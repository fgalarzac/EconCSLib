#!/usr/bin/env python3
"""Transport a complete current coverage audit from digest schema 4 to 5.

This is an administrative transport, not normal cache reuse.  A paper may
have a fully current semantic paper-coverage review whose item digests use the
immediately preceding schema-4 projection.  Schema 5 adds an explicit schema
tag to the same direct-``source_status``-excluded projection, so ordinary
freshness correctly treats the old entries as stale.  Re-running an LLM or a
Lean extraction merely to change that tag would not create new mathematical
evidence.

The bridge is deliberately narrow and fail-closed:

* every current selected source item must be represented exactly once;
* items bind through a legacy semantic digest, canonical source target digest,
  and byte-verified source-anchor identity, never through a map key or Lean
  declaration name;
* every saved review-row signature must occur exactly once in the complete v10
  statement-semantic ledger, while the current raw v10 source-record receipt
  independently pins current ``PaperInterface`` bytes and a successful fresh
  elaboration; and
* a separate immutable receipt records the old/new item identities and the
  exact artifact bytes used for the transport, while a sibling archive retains
  the complete prior schema-4 coverage sidecar.

Only the coverage sidecar's per-item digest/schema and its inventory,
review-surface, and mode aggregate pins are rewritten.  No source audit, LLM
review, signature extraction, or Lean command is run by this helper.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import re
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:  # Supports both `python scripts/...` and package imports in tests.
    from scripts import review_dashboard
    from scripts.audit_evidence_integrity import source_anchor_evidence_findings
    from scripts.source_coverage_scope import (
        DEEP_PAPER_WITH_ALL_PROSE_CLAIMS,
        LEGACY_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
        SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
        legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded,
        source_item_coverage_sha256,
    )
    from scripts.source_record_integrity import source_record_audit_receipt_error
except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
    import review_dashboard
    from audit_evidence_integrity import source_anchor_evidence_findings
    from source_coverage_scope import (
        DEEP_PAPER_WITH_ALL_PROSE_CLAIMS,
        LEGACY_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
        SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
        legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded,
        source_item_coverage_sha256,
    )
    from source_record_integrity import source_record_audit_receipt_error


PAPER_COVERAGE_SCHEMA4_TO5_REBIND_SCHEMA = 1
PAPER_COVERAGE_SCHEMA4_TO5_REBIND_ARTIFACT_KIND = (
    "paper_coverage_schema4_to5_semantic_item_rebind"
)
PAPER_COVERAGE_SCHEMA4_TO5_REBIND_POLICY_VERSION = (
    "paper-coverage-v5-schema4-to5-semantic-item-rebind-v1"
)
PAPER_COVERAGE_SCHEMA4_TO5_REBIND_BASENAME = (
    "paper_coverage_schema4_to5_rebind.json"
)
PAPER_COVERAGE_SCHEMA4_TO5_REBIND_ARCHIVE_SUFFIX = ".schema4_before_schema5_rebind"
PAPER_COVERAGE_SCHEMA4_TO5_REBIND_INTEGRITY_FIELD = (
    "paper_coverage_schema4_to5_rebind_sha256"
)
SOURCE_RECORD_V10_PROMPT_VERSION = (
    "source-record-v10-semantic-conclusion-boundary-contract"
)
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


class PaperCoverageSchema4To5RebindError(ValueError):
    """Raised when a coverage schema transport is not provably administrative."""


@dataclass(frozen=True)
class PreparedRebind:
    """A fully checked in-memory transport ready for an atomic write."""

    rebound_coverage: dict[str, object]
    receipt: dict[str, object]


def _canonical_digest(value: object) -> str:
    encoded = json.dumps(
        value, ensure_ascii=True, sort_keys=True, separators=(",", ":"), default=str
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _bytes_digest(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _valid_digest(value: object) -> str:
    candidate = str(value or "").strip().lower()
    return candidate if _SHA256_RE.fullmatch(candidate) else ""


def _json_bytes(value: object) -> bytes:
    return json.dumps(value, ensure_ascii=False, indent=2, sort_keys=True).encode("utf-8") + b"\n"


def _read_json_object(path: Path, *, label: str) -> tuple[dict[str, Any], bytes]:
    try:
        contents = path.read_bytes()
        payload = json.loads(contents)
    except (OSError, json.JSONDecodeError) as exc:
        raise PaperCoverageSchema4To5RebindError(
            f"could not read {label}: {exc}"
        ) from exc
    if not isinstance(payload, dict):
        raise PaperCoverageSchema4To5RebindError(f"{label} is not a JSON object")
    return payload, contents


def _relative_paper_path(path: Path, paper_dir: Path, *, label: str) -> str:
    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise PaperCoverageSchema4To5RebindError(
            f"{label} must remain inside the paper directory"
        ) from exc


def _paper_path(paper_dir: Path, raw_path: Path | str, *, label: str) -> Path:
    candidate = Path(raw_path)
    if candidate.is_absolute() or any(part == ".." for part in candidate.parts):
        raise PaperCoverageSchema4To5RebindError(
            f"{label} must be a paper-relative path"
        )
    try:
        resolved = (paper_dir / candidate).resolve()
        resolved.relative_to(paper_dir.resolve())
    except (OSError, RuntimeError, ValueError) as exc:
        raise PaperCoverageSchema4To5RebindError(
            f"{label} escapes the paper directory"
        ) from exc
    return resolved


def _default_prior_coverage_archive_path(coverage_path: Path) -> Path:
    """Name the preserved schema-4 sidecar beside its schema-5 successor."""

    return coverage_path.with_name(
        f"{coverage_path.stem}{PAPER_COVERAGE_SCHEMA4_TO5_REBIND_ARCHIVE_SUFFIX}"
        f"{coverage_path.suffix}"
    )


def _prior_coverage_archive_path(
    paper_dir: Path, candidate: Path | None, *, coverage_path: Path
) -> Path:
    """Resolve an API archive argument without allowing it outside the paper."""

    if candidate is None:
        archive_path = _default_prior_coverage_archive_path(coverage_path).resolve()
    elif candidate.is_absolute():
        archive_path = candidate.resolve()
    else:
        archive_path = _paper_path(
            paper_dir, candidate, label="prior schema4 coverage archive"
        )
    _relative_paper_path(
        archive_path, paper_dir, label="prior schema4 coverage archive"
    )
    return archive_path


def _repository_path(root: Path, raw_path: object, *, label: str) -> Path:
    text = str(raw_path or "").strip()
    if not text:
        raise PaperCoverageSchema4To5RebindError(f"{label} has no path")
    candidate = Path(text)
    if candidate.is_absolute() or any(part == ".." for part in candidate.parts):
        raise PaperCoverageSchema4To5RebindError(
            f"{label} must be a repository-relative path"
        )
    try:
        resolved = (root / candidate).resolve()
        resolved.relative_to(root.resolve())
    except (OSError, RuntimeError, ValueError) as exc:
        raise PaperCoverageSchema4To5RebindError(
            f"{label} escapes the repository root"
        ) from exc
    return resolved


def _required_metadata_error(
    payload: Mapping[str, object], *, label: str, paper: str, prompt_version: str
) -> str:
    if payload.get("schema") != 1:
        return f"{label} has unsupported schema"
    if str(payload.get("paper") or "").strip() != paper:
        return f"{label} belongs to another paper"
    if str(payload.get("prompt_version") or "").strip() != prompt_version:
        return f"{label} does not use the current semantic prompt"
    for field in ("validator", "validator_type", "validated_at"):
        if not str(payload.get(field) or "").strip():
            return f"{label} has no {field}"
    return ""


def _source_artifact_identity(
    statement_map: Mapping[str, object], *, paper_dir: Path
) -> tuple[str, str]:
    path = str(statement_map.get("source_artifact_path") or "").strip()
    digest = _valid_digest(statement_map.get("source_artifact_sha256"))
    if not path or not digest:
        raise PaperCoverageSchema4To5RebindError(
            "current statement map has no complete canonical source-artifact identity"
        )
    artifact = _paper_path(paper_dir, path, label="source_artifact_path")
    try:
        contents = artifact.read_bytes()
    except OSError as exc:
        raise PaperCoverageSchema4To5RebindError(
            f"could not read pinned source artifact: {exc}"
        ) from exc
    if _bytes_digest(contents) != digest:
        raise PaperCoverageSchema4To5RebindError(
            "current source artifact bytes do not match the statement-map pin"
        )
    return path, digest


def _anchor_identity(
    source_item: Mapping[str, object], *, artifact_path: str, artifact_digest: str
) -> str:
    """Return an identity for byte-pinned source evidence without map keys.

    The shared anchor validator proves that these fields are exact current
    source slices.  Keeping their path/range/quote digest here makes a later
    receipt fail closed even when a harmless-looking locator move would leave
    the broad source semantic digest unchanged.
    """

    source_location = str(source_item.get("source_location") or "").strip()
    anchors = source_item.get("source_anchor_evidence")
    if not source_location or not isinstance(anchors, list) or not anchors:
        raise PaperCoverageSchema4To5RebindError(
            "selected source item lacks byte-pinned source-anchor evidence"
        )
    records: list[dict[str, object]] = []
    for index, raw_anchor in enumerate(anchors):
        if not isinstance(raw_anchor, Mapping):
            raise PaperCoverageSchema4To5RebindError(
                f"selected source item anchor {index} is not an object"
            )
        path = str(raw_anchor.get("path") or "").strip().replace("\\", "/")
        start = raw_anchor.get("line_start")
        end = raw_anchor.get("line_end")
        quote_digest = _valid_digest(raw_anchor.get("quoted_text_sha256"))
        if (
            not path
            or not isinstance(start, int)
            or isinstance(start, bool)
            or not isinstance(end, int)
            or isinstance(end, bool)
            or not quote_digest
        ):
            raise PaperCoverageSchema4To5RebindError(
                f"selected source item anchor {index} is malformed"
            )
        records.append(
            {
                "path": path.lstrip("./"),
                "line_start": start,
                "line_end": end,
                "quoted_text_sha256": quote_digest,
            }
        )
    return _canonical_digest(
        {
            "source_artifact_path": artifact_path,
            "source_artifact_sha256": artifact_digest,
            "source_location": source_location,
            "anchors": sorted(
                records,
                key=lambda record: json.dumps(
                    record, sort_keys=True, separators=(",", ":")
                ),
            ),
        }
    )


def _source_descriptor(
    source_item: Mapping[str, object],
    *,
    mode: str,
    artifact_path: str,
    artifact_digest: str,
) -> dict[str, str]:
    """Build the map-key-free current source identity used by this bridge."""

    _target_text, target_digest = review_dashboard._source_item_coverage_statement(
        dict(source_item)
    )
    target_digest = _valid_digest(target_digest)
    legacy_digest = _valid_digest(
        legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded(
            source_item, mode
        )
    )
    current_digest = _valid_digest(source_item_coverage_sha256(source_item, mode))
    anchor_digest = _anchor_identity(
        source_item, artifact_path=artifact_path, artifact_digest=artifact_digest
    )
    if not target_digest or not legacy_digest or not current_digest:
        raise PaperCoverageSchema4To5RebindError(
            "selected source item has no complete canonical target/digest identity"
        )
    descriptor = {
        "legacy_source_item_coverage_sha256": legacy_digest,
        "current_source_item_coverage_sha256": current_digest,
        "source_target_sha256": target_digest,
        "source_anchor_identity_sha256": anchor_digest,
        "source_scope_disposition": _source_scope_disposition(source_item),
    }
    descriptor["source_identity_sha256"] = _canonical_digest(descriptor)
    return descriptor


def _source_scope_disposition(source_item: Mapping[str, object]) -> str:
    """Classify only established source-side no-proof dispositions.

    The normal lane requires an exact elaborated-signature pin.  The two
    no-proof lanes are deliberately narrower: their validity is determined by
    structured source-side evidence and byte-verified source presentation in
    the shared dashboard validator, never by a source-map key, coverage slot,
    or Lean declaration name.
    """

    item = dict(source_item)
    if review_dashboard._source_inventory_item_has_valid_user_approved_scope_exclusion(
        item
    ):
        return "explicit_user_approved_scope_exclusion"
    if review_dashboard._source_inventory_item_is_catalogued_nonformal_observation(
        item
    ):
        return "catalogued_nonformal_source_observation"
    return "requires_elaborated_review_signature"


def _legacy_inventory_digest(
    inventory: Mapping[str, Mapping[str, object]],
    *,
    mode: str,
    statement_map: Mapping[str, object],
) -> str:
    """Mirror the historic aggregate exactly, but never use it for pairing."""

    payload: dict[str, object] = {
        "mode": mode,
        "items": [
            {
                "key": key,
                "source_item_coverage_sha256": (
                    legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded(
                        item, mode
                    )
                ),
            }
            for key, item in sorted(inventory.items())
        ],
    }
    if mode == DEEP_PAPER_WITH_ALL_PROSE_CLAIMS:
        payload["source_prose_inventory_review"] = statement_map.get(
            "source_prose_inventory_review"
        )
    return _canonical_digest(payload)


def _validate_selected_source_anchors(
    *,
    paper_dir: Path,
    statement_map_path: Path,
    statement_map: Mapping[str, object],
    inventory: Mapping[str, Mapping[str, object]],
) -> None:
    """Run the cheap byte validator over exactly the current coverage surface.

    The map keys here only select current raw entries for the shared source
    byte checker.  They are deliberately absent from all subsequent
    coverage-to-source identity matching.
    """

    raw_items = statement_map.get("items")
    if not isinstance(raw_items, Mapping):
        raise PaperCoverageSchema4To5RebindError(
            "current statement map has no object-valued items ledger"
        )
    selected: dict[str, object] = {}
    for key in inventory:
        raw_item = raw_items.get(key)
        if not isinstance(raw_item, Mapping):
            raise PaperCoverageSchema4To5RebindError(
                "selected current source item is missing from the raw statement map"
            )
        selected[key] = copy.deepcopy(dict(raw_item))
    scoped = copy.deepcopy(dict(statement_map))
    scoped["items"] = selected
    scoped["source_anchor_evidence_required"] = True
    findings = source_anchor_evidence_findings(
        paper_dir, "formalized", statement_map_path, scoped
    )
    if findings:
        messages = "; ".join(sorted(str(finding.message) for finding in findings))
        raise PaperCoverageSchema4To5RebindError(
            "current selected source anchors are not byte-verified: " + messages
        )


def _validate_raw_audit(
    raw_audit: Mapping[str, object],
    *,
    paper: str,
    root: Path,
    statement_map_bytes: bytes,
    mode: str,
) -> tuple[str, str]:
    if str(raw_audit.get("paper") or "").strip() != paper:
        raise PaperCoverageSchema4To5RebindError(
            "current source-record audit belongs to another paper"
        )
    if str(raw_audit.get("prompt_version") or "").strip() != SOURCE_RECORD_V10_PROMPT_VERSION:
        raise PaperCoverageSchema4To5RebindError(
            "current source-record audit does not use the v10 semantic prompt"
        )
    if error := source_record_audit_receipt_error(raw_audit):
        raise PaperCoverageSchema4To5RebindError(
            "current source-record audit receipt is invalid: " + error
        )
    if _valid_digest(raw_audit.get("paper_statement_map_sha256")) != _bytes_digest(
        statement_map_bytes
    ):
        raise PaperCoverageSchema4To5RebindError(
            "current source-record audit is not pinned to the current statement-map bytes"
        )
    if str(raw_audit.get("source_coverage_mode") or "").strip() != mode:
        raise PaperCoverageSchema4To5RebindError(
            "current source-record audit has a different source-coverage mode"
        )
    source = raw_audit.get("review_interface_source")
    if not isinstance(source, Mapping):
        raise PaperCoverageSchema4To5RebindError(
            "current source-record audit has no PaperInterface source identity"
        )
    source_digest = _valid_digest(source.get("sha256"))
    source_path = _repository_path(
        root, source.get("path"), label="source-record review_interface_source"
    )
    try:
        current_source_digest = _bytes_digest(source_path.read_bytes())
    except OSError as exc:
        raise PaperCoverageSchema4To5RebindError(
            f"could not read current PaperInterface source: {exc}"
        ) from exc
    if not source_digest or source_digest != current_source_digest:
        raise PaperCoverageSchema4To5RebindError(
            "current PaperInterface bytes differ from the current source-record receipt"
        )
    fresh = raw_audit.get("fresh_source_elaboration")
    if not isinstance(fresh, Mapping) or fresh.get("returncode") != 0:
        raise PaperCoverageSchema4To5RebindError(
            "current source-record audit lacks a successful fresh source elaboration"
        )
    if _valid_digest(fresh.get("source_sha256")) != source_digest:
        raise PaperCoverageSchema4To5RebindError(
            "fresh source elaboration is not pinned to the reviewed PaperInterface bytes"
        )
    count = raw_audit.get("configured_review_row_count")
    if not isinstance(count, int) or isinstance(count, bool) or count <= 0:
        raise PaperCoverageSchema4To5RebindError(
            "current source-record audit has no positive configured review-row count"
        )
    raw_digest = _valid_digest(raw_audit.get("source_record_audit_sha256"))
    integrity_digest = _valid_digest(raw_audit.get("source_record_audit_integrity_sha256"))
    if not raw_digest or not integrity_digest:
        raise PaperCoverageSchema4To5RebindError(
            "current source-record audit has incomplete receipt identities"
        )
    return raw_digest, integrity_digest


def _statement_signature_index(
    statement_audit: Mapping[str, object],
    *,
    paper: str,
    configured_row_count: int,
) -> set[str]:
    error = _required_metadata_error(
        statement_audit,
        label="current statement semantic audit",
        paper=paper,
        prompt_version=review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION,
    )
    if error:
        raise PaperCoverageSchema4To5RebindError(error)
    # A statement ledger is a row-local semantic review.  Its top-level raw
    # receipt pointer records the review provenance, but an aggregate raw
    # receipt can legitimately be reissued for non-row changes (for example,
    # generated receipt fields or an explicit coverage-mode declaration).
    # Do not turn that byte-only reissue into an expensive semantic review.
    # The caller separately requires a current raw receipt whose interface
    # bytes were freshly elaborated, and every coverage pin is checked against
    # this complete ledger by signature.  The historical pointer is retained
    # in the authenticated transport receipt; it is never a pairing key.
    if not _valid_digest(statement_audit.get("source_record_audit_sha256")):
        raise PaperCoverageSchema4To5RebindError(
            "current statement semantic audit has no source-record provenance receipt"
        )
    raw_items = statement_audit.get("items")
    if not isinstance(raw_items, Mapping) or len(raw_items) != configured_row_count:
        raise PaperCoverageSchema4To5RebindError(
            "current statement semantic audit does not cover exactly the current review surface"
        )
    by_signature: set[str] = set()
    for index, raw_entry in enumerate(raw_items.values()):
        if not isinstance(raw_entry, Mapping):
            raise PaperCoverageSchema4To5RebindError(
                f"current statement semantic audit item {index} is not an object"
            )
        for field in ("validator", "validator_type", "validated_at"):
            if not str(raw_entry.get(field) or "").strip():
                raise PaperCoverageSchema4To5RebindError(
                    f"current statement semantic audit item {index} has no {field}"
                )
        if str(raw_entry.get("prompt_version") or "").strip() != review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION:
            raise PaperCoverageSchema4To5RebindError(
                f"current statement semantic audit item {index} has a stale prompt"
            )
        if not _valid_digest(raw_entry.get("lean_statement_sha256")):
            raise PaperCoverageSchema4To5RebindError(
                f"current statement semantic audit item {index} has no Lean statement digest"
            )
        signature = _valid_digest(raw_entry.get("lean_signature_sha256"))
        if not signature:
            raise PaperCoverageSchema4To5RebindError(
                f"current statement semantic audit item {index} has no elaborated signature pin"
            )
        if signature in by_signature:
            raise PaperCoverageSchema4To5RebindError(
                "current statement semantic audit has duplicate elaborated signature pins"
            )
        # The elaborated signature is the name-free binding to the reviewed
        # Lean proposition.  Do not retain the statement-ledger navigation
        # entry or any declaration spelling in the transport identity.
        by_signature.add(signature)
    return by_signature


def _validate_review_surface_audit(
    surface_audit: Mapping[str, object],
    *,
    paper: str,
    configured_row_count: int,
) -> str:
    error = _required_metadata_error(
        surface_audit,
        label="current review-surface semantic audit",
        paper=paper,
        prompt_version=review_dashboard.REQUIRED_LLM_REVIEW_SURFACE_PROMPT_VERSION,
    )
    if error:
        raise PaperCoverageSchema4To5RebindError(error)
    if str(surface_audit.get("judgment") or "").strip().lower() not in {
        "passes",
        "pass",
    }:
        raise PaperCoverageSchema4To5RebindError(
            "current review-surface semantic audit does not pass"
        )
    if surface_audit.get("review_rows") != configured_row_count:
        raise PaperCoverageSchema4To5RebindError(
            "current review-surface semantic audit has a different row count"
        )
    digest = _valid_digest(surface_audit.get("review_surface_sha256"))
    if not digest:
        raise PaperCoverageSchema4To5RebindError(
            "current review-surface semantic audit has no surface digest"
        )
    return digest


def _coverage_scope_disposition(coverage_judgment: str) -> str:
    if coverage_judgment == review_dashboard.USER_APPROVED_SCOPE_EXCLUSION:
        return "explicit_user_approved_scope_exclusion"
    if coverage_judgment in {
        "out_of_scope",
        "not_a_paper_target",
        "not_a_theorem_statement",
    }:
        return "catalogued_nonformal_source_observation"
    return "requires_elaborated_review_signature"


def _coverage_signature_pins(
    entry: Mapping[str, object], *, coverage_disposition: str
) -> list[str]:
    rows = entry.get("review_rows")
    pins = entry.get("review_row_signature_sha256")
    if coverage_disposition != "requires_elaborated_review_signature":
        if rows == [] and pins == {}:
            return []
        raise PaperCoverageSchema4To5RebindError(
            "source-side no-proof coverage disposition must have exactly empty "
            "review-row signature pins"
        )
    if (
        not isinstance(rows, list)
        or not rows
        or not all(isinstance(row, str) and row.strip() for row in rows)
        or len(set(rows)) != len(rows)
        or not isinstance(pins, Mapping)
        or set(str(key) for key in pins) != set(rows)
    ):
        raise PaperCoverageSchema4To5RebindError(
            "coverage item lacks exact review-row signature pins"
        )
    signatures = [_valid_digest(pins[row]) for row in rows]
    if not all(signatures) or len(set(signatures)) != len(signatures):
        raise PaperCoverageSchema4To5RebindError(
            "coverage item has malformed or duplicate review-row signature pins"
        )
    return sorted(signatures)


def _coverage_entry_identity(entry: Mapping[str, object], signatures: Sequence[str]) -> str:
    """Hash a coverage judgment without source or Lean navigation identifiers."""

    projected = copy.deepcopy(dict(entry))
    for field in (
        "source_item_coverage_digest_schema",
        "source_item_coverage_sha256",
        "review_rows",
        "review_row_signature_sha256",
    ):
        projected.pop(field, None)
    # A support declaration has no elaborated-signature pin in this sidecar,
    # so accepting it would reintroduce name-based routing.  The bridge stays
    # narrow and asks such a paper to obtain a dedicated transport instead.
    support = projected.pop("support_declarations", None)
    if support not in (None, [], ()):
        raise PaperCoverageSchema4To5RebindError(
            "coverage item has unpinned support declarations"
        )
    projected["review_signature_sha256s"] = list(signatures)
    return _canonical_digest(projected)


def _coverage_entries(
    coverage: Mapping[str, object],
    *,
    paper: str,
    mode: str,
    artifact_path: str,
    artifact_digest: str,
    expected_inventory_digest: str,
    expected_surface_digest: str,
    statement_signatures: set[str],
    expected_schema: int,
) -> list[dict[str, object]]:
    """Validate sidecar metadata and return name-free entry descriptors.

    The returned ``slot`` is only an in-memory serialization location used to
    preserve the sidecar's existing navigation keys during the final rewrite.
    It never enters an identity, receipt, or matching decision.
    """

    error = _required_metadata_error(
        coverage,
        label="paper coverage sidecar",
        paper=paper,
        prompt_version=review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
    )
    if error:
        raise PaperCoverageSchema4To5RebindError(error)
    if str(coverage.get("audit_kind") or "").strip() not in review_dashboard.APPROVED_PAPER_COVERAGE_AUDIT_KINDS:
        raise PaperCoverageSchema4To5RebindError(
            "paper coverage sidecar has a non-semantic audit_kind"
        )
    if coverage.get("source_grounded") is not True:
        raise PaperCoverageSchema4To5RebindError(
            "paper coverage sidecar is not source-grounded"
        )
    if coverage.get("seed_scaffold") is True:
        raise PaperCoverageSchema4To5RebindError(
            "paper coverage sidecar is a scaffold, not semantic evidence"
        )
    if str(coverage.get("source_coverage_mode") or "").strip() != mode:
        raise PaperCoverageSchema4To5RebindError(
            "paper coverage sidecar has a different source-coverage mode"
        )
    if str(coverage.get("source_artifact_path") or "").strip() != artifact_path or _valid_digest(
        coverage.get("source_artifact_sha256")
    ) != artifact_digest:
        raise PaperCoverageSchema4To5RebindError(
            "paper coverage sidecar is not pinned to the current source artifact"
        )
    if _valid_digest(coverage.get("paper_statement_inventory_sha256")) != expected_inventory_digest:
        raise PaperCoverageSchema4To5RebindError(
            "paper coverage sidecar has an unexpected source-inventory aggregate"
        )
    if _valid_digest(coverage.get("review_surface_sha256")) != expected_surface_digest:
        raise PaperCoverageSchema4To5RebindError(
            "paper coverage sidecar is not pinned to the current semantic review surface"
        )
    raw_items = coverage.get("items")
    if not isinstance(raw_items, Mapping) or not raw_items:
        raise PaperCoverageSchema4To5RebindError(
            "paper coverage sidecar has no item ledger"
        )
    entries: list[dict[str, object]] = []
    seen_identities: set[str] = set()
    for raw_slot, raw_entry in raw_items.items():
        # The slot is intentionally excluded from every identity below.
        slot = str(raw_slot)
        if not slot.strip() or not isinstance(raw_entry, Mapping):
            raise PaperCoverageSchema4To5RebindError(
                "paper coverage sidecar has an invalid item ledger entry"
            )
        entry = dict(raw_entry)
        for field in ("validator", "validator_type", "validated_at"):
            if not str(entry.get(field) or "").strip():
                raise PaperCoverageSchema4To5RebindError(
                    f"paper coverage item has no {field}"
                )
        coverage_judgment = str(entry.get("coverage") or "").strip()
        if coverage_judgment not in review_dashboard.APPROVED_PAPER_COVERAGE_JUDGMENTS:
            raise PaperCoverageSchema4To5RebindError(
                "paper coverage item has an unsupported coverage judgment"
            )
        if not str(entry.get("reason") or "").strip() or not str(
            entry.get("source_evidence") or ""
        ).strip():
            raise PaperCoverageSchema4To5RebindError(
                "paper coverage item lacks semantic reason or source evidence"
            )
        if entry.get("source_item_coverage_digest_schema") != expected_schema:
            raise PaperCoverageSchema4To5RebindError(
                "paper coverage item has an unexpected source-item digest schema"
            )
        source_digest = _valid_digest(entry.get("source_item_coverage_sha256"))
        target_digest = _valid_digest(entry.get("statement_sha256"))
        if not source_digest or not target_digest:
            raise PaperCoverageSchema4To5RebindError(
                "paper coverage item has no source-item or target-statement digest"
            )
        scope_disposition = _coverage_scope_disposition(coverage_judgment)
        signatures = _coverage_signature_pins(
            entry, coverage_disposition=scope_disposition
        )
        missing = [signature for signature in signatures if signature not in statement_signatures]
        if missing:
            raise PaperCoverageSchema4To5RebindError(
                "paper coverage item has a review signature absent from the current "
                "statement semantic audit"
            )
        identity = _coverage_entry_identity(entry, signatures)
        if identity in seen_identities:
            raise PaperCoverageSchema4To5RebindError(
                "paper coverage sidecar has duplicate name-free judgment identities"
            )
        seen_identities.add(identity)
        entries.append(
            {
                "slot": slot,
                "source_item_coverage_sha256": source_digest,
                "source_target_sha256": target_digest,
                "coverage_scope_disposition": scope_disposition,
                "review_signature_sha256s": signatures,
                "coverage_entry_semantic_sha256": identity,
            }
        )
    return entries


def _bind_entries_to_sources(
    entries: Sequence[Mapping[str, object]],
    sources: Sequence[Mapping[str, str]],
    *,
    source_digest_field: str,
) -> list[dict[str, object]]:
    """Return an exact bijection using only source semantic identities."""

    source_index: dict[tuple[str, str], list[Mapping[str, str]]] = {}
    for source in sources:
        pair = (
            str(source.get(source_digest_field) or ""),
            str(source.get("source_target_sha256") or ""),
        )
        source_index.setdefault(pair, []).append(source)
    bindings: list[dict[str, object]] = []
    used_sources: set[str] = set()
    for entry in entries:
        pair = (
            str(entry.get("source_item_coverage_sha256") or ""),
            str(entry.get("source_target_sha256") or ""),
        )
        candidates = source_index.get(pair, [])
        if len(candidates) != 1:
            raise PaperCoverageSchema4To5RebindError(
                "coverage item cannot be matched uniquely to a current semantic "
                "source target"
            )
        source = candidates[0]
        if str(entry.get("coverage_scope_disposition") or "") != str(
            source.get("source_scope_disposition") or ""
        ):
            raise PaperCoverageSchema4To5RebindError(
                "coverage no-proof disposition does not match the current "
                "source-side semantic scope evidence"
            )
        source_identity = str(source["source_identity_sha256"])
        if source_identity in used_sources:
            raise PaperCoverageSchema4To5RebindError(
                "two coverage items map to one current semantic source target"
            )
        used_sources.add(source_identity)
        binding = {
            "coverage_entry_semantic_sha256": str(
                entry["coverage_entry_semantic_sha256"]
            ),
            "review_signature_sha256s": list(entry["review_signature_sha256s"]),
            **dict(source),
        }
        binding["semantic_binding_sha256"] = _canonical_digest(binding)
        bindings.append(binding)
    if len(used_sources) != len(sources) or len(bindings) != len(sources):
        raise PaperCoverageSchema4To5RebindError(
            "paper coverage sidecar does not cover exactly every current source item"
        )
    return sorted(bindings, key=lambda binding: str(binding["source_identity_sha256"]))


def _receipt_digest(receipt: object) -> str:
    payload = copy.deepcopy(receipt)
    if isinstance(payload, dict):
        payload.pop(PAPER_COVERAGE_SCHEMA4_TO5_REBIND_INTEGRITY_FIELD, None)
    return _canonical_digest(payload)


def _artifact_record(path: Path, contents: bytes, paper_dir: Path) -> dict[str, str]:
    return {
        "path": _relative_paper_path(path, paper_dir, label="rebind artifact"),
        "bytes_sha256": _bytes_digest(contents),
    }


def prepare_paper_coverage_schema4_to5_rebind(
    *,
    paper: str,
    paper_dir: Path,
    root: Path,
    coverage: Mapping[str, object],
    coverage_bytes: bytes,
    coverage_path: Path,
    statement_map: Mapping[str, object],
    statement_map_bytes: bytes,
    statement_map_path: Path,
    raw_audit: Mapping[str, object],
    raw_audit_bytes: bytes,
    raw_audit_path: Path,
    statement_audit: Mapping[str, object],
    statement_audit_bytes: bytes,
    statement_audit_path: Path,
    review_surface_audit: Mapping[str, object],
    review_surface_audit_bytes: bytes,
    review_surface_audit_path: Path,
    prior_coverage_archive_path: Path | None = None,
) -> PreparedRebind:
    """Build a complete all-or-nothing schema-4-to-5 transport in memory."""

    if paper_dir.name != paper:
        raise PaperCoverageSchema4To5RebindError(
            "paper directory name does not match requested paper"
        )
    archive_path = _prior_coverage_archive_path(
        paper_dir, prior_coverage_archive_path, coverage_path=coverage_path
    )
    if archive_path == coverage_path.resolve():
        raise PaperCoverageSchema4To5RebindError(
            "prior schema4 coverage archive path must differ from the live coverage sidecar"
        )
    expected_map_path = (paper_dir / "audit" / "paper_statement_map.json").resolve()
    if statement_map_path.resolve() != expected_map_path:
        raise PaperCoverageSchema4To5RebindError(
            "coverage transport only accepts the current canonical statement map"
        )
    map_from_disk, map_from_disk_bytes = _read_json_object(
        statement_map_path, label="current statement map"
    )
    if _bytes_digest(map_from_disk_bytes) != _bytes_digest(statement_map_bytes) or map_from_disk != dict(statement_map):
        raise PaperCoverageSchema4To5RebindError(
            "provided statement map differs from current on-disk statement-map bytes"
        )

    full_inventory, inventory, mode, mode_error = review_dashboard.paper_coverage_inventory(
        paper_dir
    )
    del full_inventory
    if mode_error or not inventory:
        raise PaperCoverageSchema4To5RebindError(
            "current statement map has no valid nonempty coverage inventory"
            + (f": {mode_error}" if mode_error else "")
        )
    artifact_path, artifact_digest = _source_artifact_identity(
        statement_map, paper_dir=paper_dir
    )
    _validate_selected_source_anchors(
        paper_dir=paper_dir,
        statement_map_path=statement_map_path,
        statement_map=statement_map,
        inventory=inventory,
    )
    sources = [
        _source_descriptor(
            item,
            mode=mode,
            artifact_path=artifact_path,
            artifact_digest=artifact_digest,
        )
        for item in inventory.values()
    ]
    source_identities = [source["source_identity_sha256"] for source in sources]
    if len(set(source_identities)) != len(source_identities):
        raise PaperCoverageSchema4To5RebindError(
            "current source inventory has ambiguous name-free semantic identities"
        )

    raw_audit_digest, raw_integrity_digest = _validate_raw_audit(
        raw_audit,
        paper=paper,
        root=root,
        statement_map_bytes=statement_map_bytes,
        mode=mode,
    )
    configured_row_count = raw_audit.get("configured_review_row_count")
    assert isinstance(configured_row_count, int)
    statement_signatures = _statement_signature_index(
        statement_audit,
        paper=paper,
        configured_row_count=configured_row_count,
    )
    statement_audit_raw_digest = _valid_digest(
        statement_audit.get("source_record_audit_sha256")
    )
    assert statement_audit_raw_digest
    surface_digest = _validate_review_surface_audit(
        review_surface_audit,
        paper=paper,
        configured_row_count=configured_row_count,
    )
    legacy_inventory_digest = _legacy_inventory_digest(
        inventory, mode=mode, statement_map=statement_map
    )
    current_inventory_digest = review_dashboard.paper_coverage_inventory_digest(
        inventory, mode=mode, statement_map_payload=dict(statement_map)
    )
    old_entries = _coverage_entries(
        coverage,
        paper=paper,
        mode=mode,
        artifact_path=artifact_path,
        artifact_digest=artifact_digest,
        expected_inventory_digest=legacy_inventory_digest,
        expected_surface_digest=surface_digest,
        statement_signatures=statement_signatures,
        expected_schema=LEGACY_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
    )
    bindings = _bind_entries_to_sources(
        old_entries,
        sources,
        source_digest_field="legacy_source_item_coverage_sha256",
    )

    rebound_coverage = copy.deepcopy(dict(coverage))
    rebound_items = rebound_coverage.get("items")
    if not isinstance(rebound_items, dict):  # checked above; keeps type checker honest.
        raise PaperCoverageSchema4To5RebindError("paper coverage item ledger disappeared")
    by_entry_identity = {
        str(binding["coverage_entry_semantic_sha256"]): binding for binding in bindings
    }
    for entry in old_entries:
        binding = by_entry_identity[str(entry["coverage_entry_semantic_sha256"])]
        raw_entry = rebound_items[str(entry["slot"])]
        assert isinstance(raw_entry, dict)
        raw_entry["source_item_coverage_digest_schema"] = SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
        raw_entry["source_item_coverage_sha256"] = binding[
            "current_source_item_coverage_sha256"
        ]
    # These are aggregate discovery pins, not review prose.  The semantic
    # surface audit supplied the current surface digest above; no Lean work is
    # needed to copy its already-current result into this sidecar.
    rebound_coverage["paper_statement_inventory_sha256"] = current_inventory_digest
    rebound_coverage["review_surface_sha256"] = surface_digest
    rebound_coverage["source_coverage_mode"] = mode
    rebound_bytes = _json_bytes(rebound_coverage)

    receipt: dict[str, object] = {
        "schema": PAPER_COVERAGE_SCHEMA4_TO5_REBIND_SCHEMA,
        "artifact_kind": PAPER_COVERAGE_SCHEMA4_TO5_REBIND_ARTIFACT_KIND,
        "policy_version": PAPER_COVERAGE_SCHEMA4_TO5_REBIND_POLICY_VERSION,
        "paper": paper,
        "coverage_sidecar": {
            **_artifact_record(coverage_path, coverage_bytes, paper_dir),
            "rebound_bytes_sha256": _bytes_digest(rebound_bytes),
        },
        # Preserve the complete old semantic sidecar, including human review
        # prose, rather than retaining only its digest in this receipt.
        "prior_schema4_coverage_archive": _artifact_record(
            archive_path, coverage_bytes, paper_dir
        ),
        "statement_map": _artifact_record(
            statement_map_path, statement_map_bytes, paper_dir
        ),
        "raw_source_record_audit": {
            **_artifact_record(raw_audit_path, raw_audit_bytes, paper_dir),
            "source_record_audit_sha256": raw_audit_digest,
            "source_record_audit_integrity_sha256": raw_integrity_digest,
        },
        "statement_semantic_audit": {
            **_artifact_record(statement_audit_path, statement_audit_bytes, paper_dir),
            # This is immutable provenance for the already-reviewed ledger,
            # not a current-raw or semantic-pairing selector.  The current
            # receipt above independently validates the current interface and
            # fresh elaboration.
            "semantic_ledger_source_record_audit_sha256": statement_audit_raw_digest,
        },
        "review_surface_semantic_audit": _artifact_record(
            review_surface_audit_path, review_surface_audit_bytes, paper_dir
        ),
        "source_artifact": {
            "path": artifact_path,
            "sha256": artifact_digest,
        },
        "aggregate_transition": {
            "legacy_source_item_coverage_digest_schema": (
                LEGACY_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
            ),
            "current_source_item_coverage_digest_schema": (
                SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
            ),
            "prior_paper_statement_inventory_sha256": legacy_inventory_digest,
            "current_paper_statement_inventory_sha256": current_inventory_digest,
            "current_review_surface_sha256": surface_digest,
            "current_source_coverage_mode": mode,
            "current_statement_semantic_item_count": len(statement_signatures),
        },
        "item_bindings": bindings,
    }
    receipt[PAPER_COVERAGE_SCHEMA4_TO5_REBIND_INTEGRITY_FIELD] = _receipt_digest(
        receipt
    )
    return PreparedRebind(rebound_coverage=rebound_coverage, receipt=receipt)


def _receipt_artifact_error(
    receipt_record: object,
    *,
    path: Path,
    contents: bytes,
    paper_dir: Path,
    label: str,
) -> str:
    if not isinstance(receipt_record, Mapping):
        return f"{label} receipt record is not an object"
    expected = _artifact_record(path, contents, paper_dir)
    actual = {
        "path": str(receipt_record.get("path") or ""),
        "bytes_sha256": str(receipt_record.get("bytes_sha256") or "").lower(),
    }
    if actual != expected:
        return f"{label} bytes or paper-relative path differs from the receipt"
    return ""


def _prior_coverage_archive_error(
    archive_record: object,
    *,
    coverage_record: Mapping[str, object],
    coverage_path: Path,
    paper_dir: Path,
    require_on_disk: bool,
) -> str:
    """Validate that the old semantic sidecar remains available verbatim."""

    if not isinstance(archive_record, Mapping):
        return "rebind receipt has no prior schema4 coverage archive record"
    archive_relative_path = str(archive_record.get("path") or "").strip()
    archive_digest = _valid_digest(archive_record.get("bytes_sha256"))
    original_digest = _valid_digest(coverage_record.get("bytes_sha256"))
    if not archive_relative_path or not archive_digest or not original_digest:
        return "rebind receipt has incomplete prior schema4 coverage archive identity"
    try:
        archive_path = _paper_path(
            paper_dir,
            archive_relative_path,
            label="prior schema4 coverage archive receipt path",
        )
    except PaperCoverageSchema4To5RebindError as exc:
        return str(exc)
    if archive_path.resolve() == coverage_path.resolve():
        return "prior schema4 coverage archive aliases the live coverage sidecar"
    if archive_digest != original_digest:
        return "prior schema4 coverage archive does not match the original sidecar bytes"
    if not require_on_disk:
        return ""
    try:
        archived_bytes = archive_path.read_bytes()
    except OSError as exc:
        return f"could not read prior schema4 coverage archive: {exc}"
    if _bytes_digest(archived_bytes) != archive_digest:
        return "prior schema4 coverage archive bytes differ from the receipt"
    return ""


def validate_paper_coverage_schema4_to5_rebind(
    receipt: object,
    *,
    paper: str,
    paper_dir: Path,
    root: Path,
    coverage: Mapping[str, object],
    coverage_bytes: bytes,
    coverage_path: Path,
    statement_map: Mapping[str, object],
    statement_map_bytes: bytes,
    statement_map_path: Path,
    raw_audit: Mapping[str, object],
    raw_audit_bytes: bytes,
    raw_audit_path: Path,
    statement_audit: Mapping[str, object],
    statement_audit_bytes: bytes,
    statement_audit_path: Path,
    review_surface_audit: Mapping[str, object],
    review_surface_audit_bytes: bytes,
    review_surface_audit_path: Path,
    require_prior_coverage_archive: bool = True,
) -> str:
    """Validate a completed rebind against all current byte/semantic evidence.

    The original schema-4 file may have been replaced.  The receipt therefore
    stores its byte pin and the exact old semantic item identities; current
    validation proves that every resulting schema-5 sidecar entry is the same
    judgment content over the same current semantic source identity.
    """

    if not isinstance(receipt, Mapping):
        return "coverage schema4-to5 rebind receipt is not a JSON object"
    if receipt.get("schema") != PAPER_COVERAGE_SCHEMA4_TO5_REBIND_SCHEMA:
        return "coverage schema4-to5 rebind receipt has unsupported schema"
    if receipt.get("artifact_kind") != PAPER_COVERAGE_SCHEMA4_TO5_REBIND_ARTIFACT_KIND:
        return "coverage schema4-to5 rebind receipt has wrong artifact kind"
    if receipt.get("policy_version") != PAPER_COVERAGE_SCHEMA4_TO5_REBIND_POLICY_VERSION:
        return "coverage schema4-to5 rebind receipt has wrong policy version"
    if str(receipt.get("paper") or "").strip() != paper:
        return "coverage schema4-to5 rebind receipt belongs to another paper"
    supplied = _valid_digest(receipt.get(PAPER_COVERAGE_SCHEMA4_TO5_REBIND_INTEGRITY_FIELD))
    if not supplied or supplied != _receipt_digest(receipt):
        return "coverage schema4-to5 rebind receipt integrity digest is invalid"
    for record, path, contents, label in (
        (receipt.get("statement_map"), statement_map_path, statement_map_bytes, "statement map"),
        (receipt.get("raw_source_record_audit"), raw_audit_path, raw_audit_bytes, "raw source-record audit"),
        (receipt.get("statement_semantic_audit"), statement_audit_path, statement_audit_bytes, "statement semantic audit"),
        (receipt.get("review_surface_semantic_audit"), review_surface_audit_path, review_surface_audit_bytes, "review-surface semantic audit"),
    ):
        if error := _receipt_artifact_error(
            record, path=path, contents=contents, paper_dir=paper_dir, label=label
        ):
            return error
    coverage_record = receipt.get("coverage_sidecar")
    if not isinstance(coverage_record, Mapping):
        return "coverage sidecar receipt record is not an object"
    if str(coverage_record.get("path") or "") != _relative_paper_path(
        coverage_path, paper_dir, label="coverage sidecar"
    ):
        return "coverage sidecar path differs from the receipt"
    if _valid_digest(coverage_record.get("rebound_bytes_sha256")) != _bytes_digest(
        coverage_bytes
    ):
        return "rebound coverage sidecar bytes differ from the receipt"
    if error := _prior_coverage_archive_error(
        receipt.get("prior_schema4_coverage_archive"),
        coverage_record=coverage_record,
        coverage_path=coverage_path,
        paper_dir=paper_dir,
        require_on_disk=require_prior_coverage_archive,
    ):
        return error

    try:
        # Reconstruct current non-name-bearing evidence.  This deliberately
        # does not call the builder: the on-disk sidecar is schema 5 now.
        if paper_dir.name != paper:
            return "paper directory name does not match requested paper"
        expected_map_path = (paper_dir / "audit" / "paper_statement_map.json").resolve()
        if statement_map_path.resolve() != expected_map_path:
            return "receipt validation requires the canonical current statement map"
        full_inventory, inventory, mode, mode_error = review_dashboard.paper_coverage_inventory(
            paper_dir
        )
        del full_inventory
        if mode_error or not inventory:
            return "current statement map has no valid nonempty coverage inventory"
        artifact_path, artifact_digest = _source_artifact_identity(
            statement_map, paper_dir=paper_dir
        )
        _validate_selected_source_anchors(
            paper_dir=paper_dir,
            statement_map_path=statement_map_path,
            statement_map=statement_map,
            inventory=inventory,
        )
        sources = [
            _source_descriptor(
                item,
                mode=mode,
                artifact_path=artifact_path,
                artifact_digest=artifact_digest,
            )
            for item in inventory.values()
        ]
        if len({source["source_identity_sha256"] for source in sources}) != len(sources):
            return "current source inventory has ambiguous name-free semantic identities"
        raw_audit_digest, raw_integrity_digest = _validate_raw_audit(
            raw_audit,
            paper=paper,
            root=root,
            statement_map_bytes=statement_map_bytes,
            mode=mode,
        )
        configured_row_count = raw_audit.get("configured_review_row_count")
        assert isinstance(configured_row_count, int)
        statement_signatures = _statement_signature_index(
            statement_audit,
            paper=paper,
            configured_row_count=configured_row_count,
        )
        surface_digest = _validate_review_surface_audit(
            review_surface_audit,
            paper=paper,
            configured_row_count=configured_row_count,
        )
        current_inventory_digest = review_dashboard.paper_coverage_inventory_digest(
            inventory, mode=mode, statement_map_payload=dict(statement_map)
        )
        current_entries = _coverage_entries(
            coverage,
            paper=paper,
            mode=mode,
            artifact_path=artifact_path,
            artifact_digest=artifact_digest,
            expected_inventory_digest=current_inventory_digest,
            expected_surface_digest=surface_digest,
            statement_signatures=statement_signatures,
            expected_schema=SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
        )
        current_bindings = _bind_entries_to_sources(
            current_entries,
            sources,
            source_digest_field="current_source_item_coverage_sha256",
        )
    except PaperCoverageSchema4To5RebindError as exc:
        return str(exc)

    raw_record = receipt.get("raw_source_record_audit")
    if not isinstance(raw_record, Mapping) or _valid_digest(
        raw_record.get("source_record_audit_sha256")
    ) != raw_audit_digest or _valid_digest(
        raw_record.get("source_record_audit_integrity_sha256")
    ) != raw_integrity_digest:
        return "current source-record receipt identities differ from the rebind receipt"
    statement_record = receipt.get("statement_semantic_audit")
    if not isinstance(statement_record, Mapping) or _valid_digest(
        statement_record.get("semantic_ledger_source_record_audit_sha256")
    ) != _valid_digest(statement_audit.get("source_record_audit_sha256")):
        return "statement semantic-ledger provenance differs from the rebind receipt"
    aggregate = receipt.get("aggregate_transition")
    if not isinstance(aggregate, Mapping):
        return "rebind receipt has no aggregate transition"
    if (
        aggregate.get("legacy_source_item_coverage_digest_schema")
        != LEGACY_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
        or aggregate.get("current_source_item_coverage_digest_schema")
        != SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
        or _valid_digest(aggregate.get("current_paper_statement_inventory_sha256"))
        != current_inventory_digest
        or _valid_digest(aggregate.get("current_review_surface_sha256"))
        != surface_digest
        or str(aggregate.get("current_source_coverage_mode") or "") != mode
        or aggregate.get("current_statement_semantic_item_count")
        != len(statement_signatures)
    ):
        return "rebind receipt aggregate transition differs from current semantic evidence"
    source_artifact = receipt.get("source_artifact")
    if not isinstance(source_artifact, Mapping) or str(
        source_artifact.get("path") or ""
    ) != artifact_path or _valid_digest(source_artifact.get("sha256")) != artifact_digest:
        return "rebind receipt source-artifact identity differs from current source bytes"

    supplied_bindings = receipt.get("item_bindings")
    if not isinstance(supplied_bindings, list) or len(supplied_bindings) != len(
        current_bindings
    ):
        return "rebind receipt does not cover exactly the current semantic source items"
    expected_by_identity: dict[str, dict[str, object]] = {}
    for current in current_bindings:
        expected = dict(current)
        identity = str(expected["source_identity_sha256"])
        if identity in expected_by_identity:
            return "current rebind identities are ambiguous"
        expected_by_identity[identity] = expected
    seen: set[str] = set()
    for supplied_binding in supplied_bindings:
        if not isinstance(supplied_binding, Mapping):
            return "rebind receipt has a non-object item binding"
        identity = str(supplied_binding.get("source_identity_sha256") or "")
        expected = expected_by_identity.get(identity)
        if expected is None or identity in seen:
            return "rebind receipt has a missing, duplicate, or stale source binding"
        seen.add(identity)
        supplied_copy = dict(supplied_binding)
        if _valid_digest(supplied_copy.get("semantic_binding_sha256")) != _canonical_digest(
            {key: value for key, value in supplied_copy.items() if key != "semantic_binding_sha256"}
        ):
            return "rebind receipt item binding integrity is invalid"
        # Both digest projections are stored in the source descriptor.  The
        # coverage entry's mutable schema/digest fields are deliberately not
        # part of this descriptor, so a successful transport compares exactly
        # the same name-free semantic binding before and after rewriting.
        if supplied_copy != expected:
            return "rebind receipt item binding differs from current semantic evidence"
    if len(seen) != len(expected_by_identity):
        return "rebind receipt omits a current semantic source binding"
    return ""


def _atomic_write(path: Path, contents: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        dir=path.parent, prefix=f".{path.name}.", delete=False
    ) as handle:
        handle.write(contents)
        temporary = Path(handle.name)
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--coverage", type=Path, default=Path("audit/paper_coverage_llm.json"))
    parser.add_argument(
        "--archive",
        type=Path,
        help=(
            "path for the immutable schema-4 coverage-sidecar archive; defaults "
            "to an audit sibling of --coverage"
        ),
    )
    parser.add_argument("--statement-map", type=Path, default=Path("audit/paper_statement_map.json"))
    parser.add_argument("--raw-audit", type=Path, default=Path("audit/source_record_audit.json"))
    parser.add_argument("--statement-audit", type=Path, default=Path("audit/statement_match_llm.json"))
    parser.add_argument("--review-surface-audit", type=Path, default=Path("audit/review_surface_llm.json"))
    parser.add_argument(
        "--receipt",
        type=Path,
        default=Path("audit") / PAPER_COVERAGE_SCHEMA4_TO5_REBIND_BASENAME,
    )
    parser.add_argument(
        "--write",
        action="store_true",
        help="write the receipt and transformed coverage sidecar; default is a dry run",
    )
    parser.add_argument(
        "--verify",
        action="store_true",
        help="verify an existing transformed sidecar and receipt instead of building one",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    paper_dir = root / "papers" / args.paper
    try:
        if args.write and args.verify:
            raise PaperCoverageSchema4To5RebindError("--write and --verify are mutually exclusive")
        if not paper_dir.is_dir():
            raise PaperCoverageSchema4To5RebindError("paper directory does not exist")
        coverage_path = _paper_path(paper_dir, args.coverage, label="--coverage")
        archive_path = (
            _paper_path(paper_dir, args.archive, label="--archive")
            if args.archive is not None
            else _default_prior_coverage_archive_path(coverage_path)
        )
        map_path = _paper_path(paper_dir, args.statement_map, label="--statement-map")
        raw_path = _paper_path(paper_dir, args.raw_audit, label="--raw-audit")
        statement_path = _paper_path(
            paper_dir, args.statement_audit, label="--statement-audit"
        )
        surface_path = _paper_path(
            paper_dir, args.review_surface_audit, label="--review-surface-audit"
        )
        receipt_path = _paper_path(paper_dir, args.receipt, label="--receipt")
        if archive_path.resolve() in {coverage_path.resolve(), receipt_path.resolve()}:
            raise PaperCoverageSchema4To5RebindError(
                "--archive must differ from both --coverage and --receipt"
            )
        coverage, coverage_bytes = _read_json_object(coverage_path, label="coverage sidecar")
        statement_map, map_bytes = _read_json_object(map_path, label="statement map")
        raw_audit, raw_bytes = _read_json_object(raw_path, label="raw source-record audit")
        statement_audit, statement_bytes = _read_json_object(
            statement_path, label="statement semantic audit"
        )
        surface_audit, surface_bytes = _read_json_object(
            surface_path, label="review-surface semantic audit"
        )
        common = {
            "paper": args.paper,
            "paper_dir": paper_dir,
            "root": root,
            "coverage": coverage,
            "coverage_bytes": coverage_bytes,
            "coverage_path": coverage_path,
            "statement_map": statement_map,
            "statement_map_bytes": map_bytes,
            "statement_map_path": map_path,
            "raw_audit": raw_audit,
            "raw_audit_bytes": raw_bytes,
            "raw_audit_path": raw_path,
            "statement_audit": statement_audit,
            "statement_audit_bytes": statement_bytes,
            "statement_audit_path": statement_path,
            "review_surface_audit": surface_audit,
            "review_surface_audit_bytes": surface_bytes,
            "review_surface_audit_path": surface_path,
            "prior_coverage_archive_path": archive_path,
        }
        if args.verify:
            receipt, _receipt_bytes = _read_json_object(receipt_path, label="rebind receipt")
            verification_common = dict(common)
            verification_common.pop("prior_coverage_archive_path", None)
            if error := validate_paper_coverage_schema4_to5_rebind(
                receipt, **verification_common
            ):
                raise PaperCoverageSchema4To5RebindError(error)
            print(f"{args.paper}: coverage schema4-to5 rebind receipt validates")
            return 0
        prepared = prepare_paper_coverage_schema4_to5_rebind(**common)
        rebound_bytes = _json_bytes(prepared.rebound_coverage)
        receipt_bytes = _json_bytes(prepared.receipt)
        # Validate the exact bytes we are about to write before changing either
        # artifact.  This converts programming mistakes into a no-write error.
        validation_common = dict(common)
        validation_common["coverage"] = prepared.rebound_coverage
        validation_common["coverage_bytes"] = rebound_bytes
        validation_common.pop("prior_coverage_archive_path", None)
        if error := validate_paper_coverage_schema4_to5_rebind(
            prepared.receipt,
            **validation_common,
            require_prior_coverage_archive=False,
        ):
            raise PaperCoverageSchema4To5RebindError(
                "internal transformed-sidecar validation failed: " + error
            )
        if args.write:
            # The old semantic prose is retained before any replacement.  A
            # mismatching preexisting archive is never overwritten.
            if archive_path.exists():
                try:
                    archived_bytes = archive_path.read_bytes()
                except OSError as exc:
                    raise PaperCoverageSchema4To5RebindError(
                        f"could not read existing prior schema4 coverage archive: {exc}"
                    ) from exc
                if archived_bytes != coverage_bytes:
                    raise PaperCoverageSchema4To5RebindError(
                        "existing prior schema4 coverage archive has different bytes"
                    )
            else:
                _atomic_write(archive_path, coverage_bytes)
            # Write the receipt second.  If the final atomic replacement were
            # interrupted, the live sidecar remains schema 4 and cannot be
            # accepted as transformed; the old semantic evidence and receipt
            # are already preserved.
            _atomic_write(receipt_path, receipt_bytes)
            _atomic_write(coverage_path, rebound_bytes)
            print(
                f"{args.paper}: wrote schema4-to5 coverage rebind for "
                f"{len(prepared.receipt['item_bindings'])} semantic source items"
            )
        else:
            print(
                f"{args.paper}: schema4-to5 coverage rebind validates for "
                f"{len(prepared.receipt['item_bindings'])} semantic source items; "
                "rerun with --write"
            )
    except PaperCoverageSchema4To5RebindError as exc:
        print(f"{args.paper}: coverage schema4-to5 rebind refused: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
