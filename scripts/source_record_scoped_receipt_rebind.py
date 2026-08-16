#!/usr/bin/env python3
"""Fail-closed transport for a *legacy* v10 source-record judgment.

This module is deliberately not another general source-record reuse overlay.
It has one narrowly defined job: carry a response from a valid legacy v10
receipt to one exact current boundary/conclusion row when the source and Lean
obligation are demonstrably unchanged.  In particular, it cannot transport a
semantic-model or recursive-field response, cannot select by a declaration or
judgment key, and cannot make a serialized marker authoritative.

The builder emits a deterministic receipt.  The loader treats that receipt as
an instruction to replay the archived raw audit, source map, and response
sidecar; it returns an authenticated dict subclass only after that replay and
after projecting current association pins from the live raw member.  A plain
deserialized dict containing the provenance marker is therefore never an
accepted loaded item.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import importlib.util
import json
import os
import re
import sys
import tempfile
from pathlib import Path, PurePosixPath
from typing import Any, Mapping, Sequence


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:  # Supports direct execution and package imports in focused tests.
    from scripts.audit_evidence_integrity import semantic_context_requirements
    from scripts.source_coverage_scope import source_item_coverage_sha256
    from scripts.source_record_differential_revalidation import (
        SOURCE_RECORD_V10_PROMPT_VERSION,
        _raw_item_groups,
    )
    from scripts.source_record_freshness import SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    from scripts.source_record_integrity import (
        canonical_digest_payload,
        source_record_audit_receipt_error,
        source_record_item_reuse_eligible,
    )
    from scripts.source_record_target_disposition import (
        project_source_record_response_association_pins,
        semantic_association_record_digest,
        source_contract_association_record_digest,
        source_map_item_record_digest,
    )
except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
    from audit_evidence_integrity import semantic_context_requirements
    from source_coverage_scope import source_item_coverage_sha256
    from source_record_differential_revalidation import (
        SOURCE_RECORD_V10_PROMPT_VERSION,
        _raw_item_groups,
    )
    from source_record_freshness import SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    from source_record_integrity import (
        canonical_digest_payload,
        source_record_audit_receipt_error,
        source_record_item_reuse_eligible,
    )
    from source_record_target_disposition import (
        project_source_record_response_association_pins,
        semantic_association_record_digest,
        source_contract_association_record_digest,
        source_map_item_record_digest,
    )


SOURCE_RECORD_SCOPED_RECEIPT_REBIND_SCHEMA = 1
SOURCE_RECORD_SCOPED_RECEIPT_REBIND_POLICY_VERSION = (
    "source-record-v10-legacy-scoped-receipt-rebind-v1"
)
SOURCE_RECORD_SCOPED_RECEIPT_REBIND_ARTIFACT_KIND = (
    "source_record_v10_legacy_scoped_receipt_rebind"
)
SOURCE_RECORD_SCOPED_RECEIPT_REBIND_FILENAME = (
    "source_record_scoped_receipt_rebind.json"
)
SOURCE_RECORD_SCOPED_RECEIPT_REBIND_INTEGRITY_FIELD = (
    "source_record_scoped_receipt_rebind_sha256"
)
SOURCE_RECORD_SCOPED_RECEIPT_REBIND_ITEM_FIELD = (
    "source_record_scoped_receipt_rebind"
)

_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.I)
_NORMAL_SECTIONS = frozenset(
    {"boundary_input_items", "conclusion_dependency_items"}
)
_FORBIDDEN_SECTIONS = frozenset({"semantic_model_items", "recursive_field_items"})
_ASSOCIATION_FIELDS = (
    "source_contract_association",
    "semantic_contract_source_association",
    "source_statement_association",
    "semantic_contract_group",
)
_SCOPED_PIN_FIELDS = (
    "source_record_item_semantic_context_requirements_sha256",
    "source_record_item_source_proof_fidelity_records_sha256",
)
_CURRENT_ITEM_CREDENTIAL_FIELDS = frozenset(
    {
        "source_record_item_reuse_eligibility",
        "source_record_item_digest_schema",
        "source_record_item_semantic_id",
        "source_record_item_context_sha256",
        "source_record_item_sha256",
        *_SCOPED_PIN_FIELDS,
    }
)
# These fields are addresses or display-only route coordinates.  They are
# excluded from equality only after the current/raw association is separately
# checked against the correct statement-map bytes and the descriptor retains
# source-content and elaborated-signature identities.
_NAVIGATION_FIELDS = frozenset(
    {
        "row",
        "judgment_key",
        "binder",
        "lean_source_declaration",
        "effective_lean_source_declaration",
        "qualified_declaration",
        "effective_qualified_declaration",
        "reviewed_declaration_identity",
        "source_file",
        "source_location",
        "source_key",
        "source_kind",
        "source_map_item_sha256",
        "source_map_item_keys",
        "source_map_item_keys_sha256",
        "source_map_item_sha256_by_key",
        "semantic_model_judgment_key",
        "paper_statement_map_sha256",
        "association_sha256",
        "semantic_association_sha256",
        "declaration",
        "path",
        "line",
        "line_start",
        "line_end",
        "quoted_text_sha256",
    }
)
_RESPONSE_REBIND_FIELDS = frozenset(
    {
        "source_record_audit_sha256",
        "semantic_association_sha256",
        "source_contract_association_sha256",
        "source_map_item_keys",
        "source_map_item_keys_sha256",
        "source_map_item_sha256_by_key",
        "source_item_semantic_sha256",
        "source_item_semantic_sha256_by_key",
        "corrected_target_sha256_by_source_item",
        "corrected_target_sha256_by_source_semantic_sha256",
        SOURCE_RECORD_SCOPED_RECEIPT_REBIND_ITEM_FIELD,
    }
)
_LEGACY_ITEM_CREDENTIAL_FIELDS = frozenset(
    {
        "source_record_item_reuse_eligibility",
        "source_record_item_digest_schema",
        "source_record_item_semantic_id",
        "source_record_item_context_sha256",
        "source_record_item_sha256",
    }
)
_LOADED_OVERLAY_ITEM_SENTINEL = object()


class SourceRecordScopedReceiptRebindError(ValueError):
    """Raised when the legacy scoped-receipt transport is inadmissible."""


class _LoadedSourceRecordScopedReceiptRebindItem(dict[str, Any]):
    """A loader-only capability, intentionally not serializable authority."""

    __slots__ = ("_source_record_scoped_receipt_rebind_loader_token",)

    def __init__(self, value: Mapping[str, Any]) -> None:
        super().__init__(value)
        self._source_record_scoped_receipt_rebind_loader_token = (
            _LOADED_OVERLAY_ITEM_SENTINEL
        )


def _sha256(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if _SHA256_RE.fullmatch(text) else ""


def _canonical_digest(value: object) -> str:
    encoded = json.dumps(
        canonical_digest_payload(value), sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load_source_record_audit_helper() -> Any:
    """Load the generator-owned scoped-pin implementation once by path."""

    module_name = "_source_record_scoped_receipt_rebind_audit_helper"
    existing = sys.modules.get(module_name)
    if existing is not None:
        return existing
    helper_path = ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
    spec = importlib.util.spec_from_file_location(module_name, helper_path)
    if spec is None or spec.loader is None:
        raise SourceRecordScopedReceiptRebindError(
            "could not load source-record scoped-pin infrastructure"
        )
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def _payload_is_non_evidence(value: object) -> bool:
    """Reject candidate/proposal markers by payload content at every depth."""

    if isinstance(value, Mapping):
        if any(
            bool(value.get(marker))
            for marker in (
                "candidate_only",
                "not_evidence",
                "must_not_be_written_to_repository_sidecar",
                "non_evidence_scaffold",
            )
        ):
            return True
        for field in ("artifact_kind", "validator_type"):
            text = str(value.get(field) or "").strip().lower()
            if "candidate" in text or "proposal" in text:
                return True
        return any(_payload_is_non_evidence(child) for child in value.values())
    if isinstance(value, (list, tuple)):
        return any(_payload_is_non_evidence(child) for child in value)
    return False


def _has_symlink_component(path: Path) -> bool:
    """Treat a symlink anywhere in a supplied path as an alias, not evidence."""

    probe = path
    while probe != probe.parent:
        if probe.is_symlink():
            return True
        probe = probe.parent
    return probe.is_symlink()


def _canonical_paper_path(path: Path, paper_dir: Path, *, label: str) -> Path:
    """Require a real, non-symlinked canonical path inside one paper folder."""

    original = Path(path)
    if any(part in {"", ".", ".."} for part in original.parts):
        raise SourceRecordScopedReceiptRebindError(
            f"{label} must not use traversal or a path alias"
        )
    candidate = original if original.is_absolute() else paper_dir / original
    if (
        _has_symlink_component(candidate)
        or not candidate.exists()
        or not candidate.is_file()
    ):
        raise SourceRecordScopedReceiptRebindError(
            f"{label} must name an existing non-symlink file"
        )
    try:
        resolved = candidate.resolve(strict=True)
        relative = resolved.relative_to(paper_dir.resolve())
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordScopedReceiptRebindError(
            f"{label} must remain inside the paper folder"
        ) from exc
    if any(part in {"", ".", ".."} for part in relative.parts):
        raise SourceRecordScopedReceiptRebindError(f"{label} is not canonical")
    return resolved


def _relative_paper_path(path: Path, paper_dir: Path) -> str:
    canonical = _canonical_paper_path(path, paper_dir, label="artifact input path")
    return canonical.relative_to(paper_dir.resolve()).as_posix()


def _resolve_serialized_paper_path(
    value: object, paper_dir: Path, *, label: str
) -> Path:
    text = str(value or "").strip()
    pure = PurePosixPath(text)
    if (
        not text
        or pure.is_absolute()
        or any(part in {"", ".", ".."} for part in pure.parts)
    ):
        raise SourceRecordScopedReceiptRebindError(
            f"{label} must be a normalized paper-relative path"
        )
    return _canonical_paper_path(paper_dir / Path(*pure.parts), paper_dir, label=label)


def _read_json_object(path: Path, *, label: str) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise SourceRecordScopedReceiptRebindError(
            f"could not read {label}: {exc}"
        ) from exc
    if not isinstance(payload, dict):
        raise SourceRecordScopedReceiptRebindError(f"{label} is not a JSON object")
    return payload


def _exact_file_payload_error(
    path: Path, payload: Mapping[str, Any], *, label: str
) -> str:
    try:
        saved = _read_json_object(path, label=label)
    except SourceRecordScopedReceiptRebindError as exc:
        return str(exc)
    if canonical_digest_payload(saved) != canonical_digest_payload(payload):
        return f"{label} differs from its named evidence file"
    return ""


def _provenance(
    payload: Mapping[str, Any], path: Path, paper_dir: Path, *, label: str
) -> dict[str, str]:
    canonical_path = _canonical_paper_path(path, paper_dir, label=label)
    if error := _exact_file_payload_error(canonical_path, payload, label=label):
        raise SourceRecordScopedReceiptRebindError(error)
    return {
        "path": canonical_path.relative_to(paper_dir.resolve()).as_posix(),
        "file_sha256": _file_sha256(canonical_path),
    }


def _provenance_payload(
    provenance: object, paper_dir: Path, *, label: str
) -> tuple[Path, dict[str, Any]]:
    if not isinstance(provenance, Mapping):
        raise SourceRecordScopedReceiptRebindError(f"{label} provenance is missing")
    path = _resolve_serialized_paper_path(provenance.get("path"), paper_dir, label=label)
    recorded = _sha256(provenance.get("file_sha256"))
    if not recorded or _file_sha256(path) != recorded:
        raise SourceRecordScopedReceiptRebindError(
            f"{label} provenance digest does not match its file"
        )
    return path, _read_json_object(path, label=label)


def _raw_audit_error(payload: object, *, paper: str, label: str) -> str:
    if not isinstance(payload, Mapping):
        return f"{label} raw audit is not an object"
    if _payload_is_non_evidence(payload):
        return f"{label} raw audit is marked candidate/non-evidence"
    if payload.get("paper") != paper:
        return f"{label} raw audit does not record the requested paper"
    if str(payload.get("prompt_version") or "").strip() != SOURCE_RECORD_V10_PROMPT_VERSION:
        return f"{label} raw audit does not use the v10 source-record prompt"
    if (
        str(payload.get("source_record_policy_version") or "").strip()
        != SOURCE_RECORD_V10_PROMPT_VERSION
    ):
        return f"{label} raw audit does not use the v10 source-record policy"
    if not _sha256(payload.get("source_record_audit_sha256")):
        return f"{label} raw audit has no aggregate receipt"
    if error := source_record_audit_receipt_error(payload):
        return f"{label} raw audit receipt is invalid: {error}"
    lean_check = payload.get("lean_check")
    if not isinstance(lean_check, Mapping) or lean_check.get("returncode") != 0:
        return f"{label} raw audit lacks a successful Lean check"
    recursion_failures = payload.get("recursion_failure_count")
    if isinstance(recursion_failures, bool) or recursion_failures != 0:
        return f"{label} raw audit has nonzero or malformed recursion failures"
    return ""


def _source_map_error(
    statement_map: object,
    *,
    statement_map_path: Path,
    raw_audit: Mapping[str, Any],
    paper_dir: Path,
    label: str,
    allow_reconciled_raw_map_mismatch: bool = False,
) -> str:
    if not isinstance(statement_map, Mapping):
        return f"{label} statement map is not an object"
    if _payload_is_non_evidence(statement_map):
        return f"{label} statement map is marked candidate/non-evidence"
    items = statement_map.get("items")
    if not isinstance(items, Mapping):
        return f"{label} statement map has no items object"
    try:
        canonical = _canonical_paper_path(statement_map_path, paper_dir, label=f"{label} statement map")
    except SourceRecordScopedReceiptRebindError as exc:
        return str(exc)
    if error := _exact_file_payload_error(canonical, statement_map, label=f"{label} statement map"):
        return error
    expected = _sha256(raw_audit.get("paper_statement_map_sha256"))
    if not expected:
        return f"{label} raw audit has no statement-map receipt"
    if not allow_reconciled_raw_map_mismatch and _file_sha256(canonical) != expected:
        return f"{label} raw audit does not bind the supplied statement-map bytes"
    return ""


def _historical_association_snapshot_module() -> Any:
    """Load the sole exceptional historical-map witness lane lazily."""

    try:
        from scripts import (
            source_record_historical_association_snapshot_reconciliation as reconciliation,
        )
    except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
        import source_record_historical_association_snapshot_reconciliation as reconciliation
    return reconciliation


def _reconciled_prior_map(
    *,
    reconciliation_path: Path,
    paper_dir: Path,
    paper: str,
    prior_raw_path: Path,
    prior_raw: Mapping[str, Any],
) -> tuple[dict[str, Any], dict[str, Any]]:
    """Return a witness map only after its standalone reconciliation replays.

    This is intentionally the *only* exception to ordinary prior-map byte
    equality.  It does not repair an archived aggregate receipt.  Instead the
    separate loader rechecks every generated full source-map-item pin against
    one immutable witness map, and this function additionally binds that
    loaded artifact to the exact archived raw path and bytes passed here.
    """

    reconciliation = _historical_association_snapshot_module()
    canonical_reconciliation_path = _canonical_paper_path(
        reconciliation_path,
        paper_dir,
        label="historical association snapshot reconciliation",
    )
    try:
        loaded = reconciliation.load_historical_association_snapshot_reconciliation(
            paper_dir=paper_dir,
            paper=paper,
            artifact_path=canonical_reconciliation_path,
        )
    except reconciliation.SourceRecordHistoricalAssociationSnapshotReconciliationError as exc:
        raise SourceRecordScopedReceiptRebindError(
            f"historical association snapshot reconciliation is invalid: {exc}"
        ) from exc
    if not reconciliation.is_loaded_historical_association_snapshot_reconciliation(
        loaded
    ):
        raise SourceRecordScopedReceiptRebindError(
            "historical association snapshot reconciliation has no loader authority"
        )
    raw_meta = loaded.get("archived_raw_audit")
    witness_meta = loaded.get("immutable_witness_statement_map")
    if not isinstance(raw_meta, Mapping) or not isinstance(witness_meta, Mapping):
        raise SourceRecordScopedReceiptRebindError(
            "historical association snapshot reconciliation has malformed provenance"
        )
    recorded_raw_path = _resolve_serialized_paper_path(
        raw_meta.get("path"), paper_dir, label="reconciled archived raw-audit path"
    )
    canonical_prior_raw_path = _canonical_paper_path(
        prior_raw_path, paper_dir, label="prior raw audit"
    )
    if recorded_raw_path != canonical_prior_raw_path:
        raise SourceRecordScopedReceiptRebindError(
            "historical association reconciliation refers to a different archived raw audit"
        )
    if _sha256(raw_meta.get("bytes_sha256")) != _file_sha256(canonical_prior_raw_path):
        raise SourceRecordScopedReceiptRebindError(
            "historical association reconciliation raw-audit bytes differ from prior provenance"
        )
    for field, reconciliation_field in (
        ("source_record_audit_sha256", "source_record_audit_sha256"),
        ("source_record_audit_integrity_sha256", "source_record_audit_integrity_sha256"),
        ("paper_statement_map_sha256", "reported_paper_statement_map_sha256"),
    ):
        if _sha256(raw_meta.get(reconciliation_field)) != _sha256(
            prior_raw.get(field)
        ):
            raise SourceRecordScopedReceiptRebindError(
                "historical association reconciliation does not match archived raw "
                f"`{field}`"
            )
    witness_path = _resolve_serialized_paper_path(
        witness_meta.get("path"), paper_dir, label="reconciled witness statement map"
    )
    if _sha256(witness_meta.get("bytes_sha256")) != _file_sha256(witness_path):
        raise SourceRecordScopedReceiptRebindError(
            "historical association reconciliation witness-map bytes changed"
        )
    if _sha256(witness_meta.get("actual_paper_statement_map_sha256")) != _file_sha256(
        witness_path
    ):
        raise SourceRecordScopedReceiptRebindError(
            "historical association reconciliation witness-map receipt is stale"
        )
    witness_map = _read_json_object(witness_path, label="reconciled witness statement map")
    if not isinstance(witness_map.get("items"), Mapping):
        raise SourceRecordScopedReceiptRebindError(
            "historical association reconciliation witness map has no items object"
        )
    return witness_map, {
        "mode": "historical_association_snapshot_reconciliation",
        "reconciliation": _provenance(
            loaded,
            canonical_reconciliation_path,
            paper_dir,
            label="historical association snapshot reconciliation",
        ),
        "witness_statement_map": _provenance(
            witness_map,
            witness_path,
            paper_dir,
            label="reconciled witness statement map",
        ),
        "archived_reported_paper_statement_map_sha256": _sha256(
            prior_raw.get("paper_statement_map_sha256")
        ),
    }


def _prior_map_for_build(
    *,
    paper: str,
    paper_dir: Path,
    prior_raw: Mapping[str, Any],
    prior_raw_path: Path,
    prior_statement_map: Mapping[str, Any] | None,
    prior_statement_map_path: Path | None,
    prior_association_snapshot_reconciliation_path: Path | None,
) -> tuple[Mapping[str, Any], dict[str, Any]]:
    """Select either an exact archived map or the one replayed exception."""

    if prior_association_snapshot_reconciliation_path is not None:
        if prior_statement_map is not None or prior_statement_map_path is not None:
            raise SourceRecordScopedReceiptRebindError(
                "an archived statement map and association reconciliation are mutually exclusive"
            )
        witness_map, validation = _reconciled_prior_map(
            reconciliation_path=prior_association_snapshot_reconciliation_path,
            paper_dir=paper_dir,
            paper=paper,
            prior_raw_path=prior_raw_path,
            prior_raw=prior_raw,
        )
        if error := _source_map_error(
            witness_map,
            statement_map_path=_resolve_serialized_paper_path(
                validation["witness_statement_map"]["path"],
                paper_dir,
                label="reconciled witness statement map",
            ),
            raw_audit=prior_raw,
            paper_dir=paper_dir,
            label="prior reconciled witness",
            allow_reconciled_raw_map_mismatch=True,
        ):
            raise SourceRecordScopedReceiptRebindError(error)
        return witness_map, validation
    if (prior_statement_map is None) != (prior_statement_map_path is None):
        raise SourceRecordScopedReceiptRebindError(
            "prior statement map and its path must be supplied together"
        )
    if prior_statement_map is None or prior_statement_map_path is None:
        raise SourceRecordScopedReceiptRebindError(
            "an exact archived prior statement map or reconciliation is required"
        )
    if error := _source_map_error(
        prior_statement_map,
        statement_map_path=prior_statement_map_path,
        raw_audit=prior_raw,
        paper_dir=paper_dir,
        label="prior",
    ):
        raise SourceRecordScopedReceiptRebindError(error)
    return prior_statement_map, {
        "mode": "archived_exact_map",
        "statement_map": _provenance(
            prior_statement_map,
            prior_statement_map_path,
            paper_dir,
            label="prior statement map",
        ),
    }


def _prior_map_from_validation(
    validation: object,
    *,
    paper: str,
    paper_dir: Path,
    prior_raw: Mapping[str, Any],
    prior_raw_path: Path,
) -> tuple[Mapping[str, Any], Path | None, Path | None, str]:
    """Replay the stored prior-map choice for an overlay loader.

    The return shape makes the caller feed precisely the same choice back to
    ``build_source_record_scoped_receipt_rebind``: either an exact map/path,
    or no map plus the reconciliation path.  This prevents a serialized mode
    bit from selecting an unchecked exception.
    """

    if not isinstance(validation, Mapping):
        return {}, None, None, "prior statement-map validation is malformed"
    mode = str(validation.get("mode") or "").strip()
    if mode == "archived_exact_map":
        try:
            path, statement_map = _provenance_payload(
                validation.get("statement_map"), paper_dir, label="prior statement map"
            )
        except SourceRecordScopedReceiptRebindError as exc:
            return {}, None, None, str(exc)
        if error := _source_map_error(
            statement_map,
            statement_map_path=path,
            raw_audit=prior_raw,
            paper_dir=paper_dir,
            label="prior",
        ):
            return {}, None, None, error
        return statement_map, path, None, ""
    if mode == "historical_association_snapshot_reconciliation":
        reconciliation_meta = validation.get("reconciliation")
        witness_meta = validation.get("witness_statement_map")
        if not isinstance(reconciliation_meta, Mapping) or not isinstance(
            witness_meta, Mapping
        ):
            return {}, None, None, "historical association reconciliation provenance is malformed"
        try:
            reconciliation_path, _artifact = _provenance_payload(
                reconciliation_meta,
                paper_dir,
                label="historical association snapshot reconciliation",
            )
            statement_map, replayed = _reconciled_prior_map(
                reconciliation_path=reconciliation_path,
                paper_dir=paper_dir,
                paper=paper,
                prior_raw_path=prior_raw_path,
                prior_raw=prior_raw,
            )
        except SourceRecordScopedReceiptRebindError as exc:
            return {}, None, None, str(exc)
        if canonical_digest_payload(replayed) != canonical_digest_payload(validation):
            return {}, None, None, "historical association reconciliation validation does not replay"
        try:
            witness_path, witnessed = _provenance_payload(
                witness_meta,
                paper_dir,
                label="reconciled witness statement map",
            )
        except SourceRecordScopedReceiptRebindError as exc:
            return {}, None, None, str(exc)
        if canonical_digest_payload(statement_map) != canonical_digest_payload(witnessed):
            return {}, None, None, "historical association reconciliation witness map does not replay"
        return statement_map, None, reconciliation_path, ""
    return {}, None, None, "prior statement-map validation has an unsupported mode"


def _reconciled_keyless_semantic_context(
    context: list[Any], *, label: str
) -> tuple[list[dict[str, Any]], str]:
    """Remove only the source-map storage address from a replayed context.

    Historical reconciliation authenticates every source item by its complete
    map-record digest.  The raw audit's global context projection additionally
    carries ``source_item_key`` as inventory trace metadata, so a storage-key
    rename must not make otherwise identical content fail.  Retain every other
    field, including requirement index and byte-pinned anchors, and compare a
    canonical multiset rather than using a key as a selector.
    """

    projected: list[dict[str, Any]] = []
    for index, requirement in enumerate(context):
        if not isinstance(requirement, Mapping):
            return [], f"{label} semantic-context entry {index} is not an object"
        source_key = requirement.get("source_item_key")
        if not isinstance(source_key, str) or not source_key.strip():
            return (
                [],
                f"{label} semantic-context entry {index} lacks its source-item trace",
            )
        projected.append(
            {
                str(field): copy.deepcopy(value)
                for field, value in requirement.items()
                if str(field) != "source_item_key"
            }
        )
    projected.sort(key=_canonical_digest)
    return projected, ""


def _semantic_context_error(
    raw_audit: Mapping[str, Any],
    statement_map: Mapping[str, Any],
    *,
    label: str,
    allow_reconciled_storage_key_rebind: bool = False,
) -> str:
    """Check the complete raw global context against the archived/current map."""

    if "semantic_context_requirements" not in raw_audit:
        return f"{label} raw audit lacks semantic_context_requirements"
    raw_context = raw_audit.get("semantic_context_requirements")
    if not isinstance(raw_context, list):
        return f"{label} semantic_context_requirements is not a list"
    count = raw_audit.get("semantic_context_requirement_count")
    if isinstance(count, bool) or not isinstance(count, int) or count != len(raw_context):
        return f"{label} semantic-context requirement count is malformed"
    recorded = str(raw_audit.get("semantic_context_requirements_sha256") or "").strip().lower()
    expected_digest = _load_source_record_audit_helper().stable_digest(raw_context) if raw_context else ""
    if recorded != expected_digest:
        return f"{label} semantic-context requirement digest is missing or stale"
    expected_context = semantic_context_requirements(dict(statement_map))
    if allow_reconciled_storage_key_rebind:
        raw_keyless, raw_keyless_error = _reconciled_keyless_semantic_context(
            raw_context, label=label
        )
        if raw_keyless_error:
            return raw_keyless_error
        expected_keyless, expected_keyless_error = _reconciled_keyless_semantic_context(
            expected_context, label=label
        )
        if expected_keyless_error:
            return expected_keyless_error
        if canonical_digest_payload(raw_keyless) != canonical_digest_payload(
            expected_keyless
        ):
            return (
                f"{label} semantic-context payload does not match its reconciled "
                "statement map"
            )
        return ""
    if canonical_digest_payload(raw_context) != canonical_digest_payload(expected_context):
        return f"{label} semantic-context payload does not match its statement map"
    return ""


def _source_proof_fidelity_error(
    raw_audit: Mapping[str, Any], *, paper: str, label: str
) -> str:
    """Validate the global ledger shape before deriving a scoped pin from it."""

    fidelity = raw_audit.get("source_proof_fidelity")
    if not isinstance(fidelity, Mapping):
        return f"{label} raw audit lacks a source_proof_fidelity object"
    if _payload_is_non_evidence(fidelity):
        return f"{label} source_proof_fidelity is marked candidate/non-evidence"
    if fidelity.get("paper") != paper:
        return f"{label} source_proof_fidelity does not record the requested paper"
    schema = fidelity.get("schema")
    if isinstance(schema, bool) or not isinstance(schema, int) or schema < 1:
        return f"{label} source_proof_fidelity has an invalid schema"
    for collection in ("model_conventions", "checked_proof_steps", "defects"):
        records = fidelity.get(collection)
        # Older ledgers may omit a collection that no associated source-map
        # item cites.  This broad shape check must not turn that unrelated
        # absence into evidence for, or against, a row.  The item-scoped pin
        # derivation below remains strict: a referenced absent collection is
        # rejected when the exact source-map IDs are resolved.
        if records is None:
            continue
        if not isinstance(records, list):
            return f"{label} source_proof_fidelity `{collection}` is not a list"
        ids: set[str] = set()
        for index, record in enumerate(records):
            if not isinstance(record, Mapping):
                return f"{label} source_proof_fidelity `{collection}[{index}]` is not an object"
            record_id = str(record.get("id") or "").strip()
            if not record_id or record_id in ids:
                return f"{label} source_proof_fidelity `{collection}` has a missing or duplicate id"
            ids.add(record_id)
            if collection == "model_conventions":
                for field in (
                    "source_locator",
                    "classification",
                    "formal_meaning",
                    "why_needed",
                    "checked_scope",
                ):
                    if not str(record.get(field) or "").strip():
                        return (
                            f"{label} source-proof model convention `{record_id}` "
                            f"lacks `{field}`"
                        )
    scopes = fidelity.get("reviewed_proof_scopes")
    if scopes is not None and not isinstance(scopes, list):
        return f"{label} source_proof_fidelity reviewed_proof_scopes is not a list"
    return ""


def _raw_global_context_error(
    raw_audit: Mapping[str, Any],
    statement_map: Mapping[str, Any],
    *,
    paper: str,
    label: str,
    allow_reconciled_storage_key_rebind: bool = False,
) -> str:
    if error := _semantic_context_error(
        raw_audit,
        statement_map,
        label=label,
        allow_reconciled_storage_key_rebind=(
            allow_reconciled_storage_key_rebind
        ),
    ):
        return error
    return _source_proof_fidelity_error(raw_audit, paper=paper, label=label)


def _group_error(
    group: object, *, label: str, current: bool
) -> tuple[str, tuple[str, Mapping[str, Any]] | None]:
    if not isinstance(group, Mapping):
        return f"{label} judgment key has no generated group", None
    members = group.get("raw_members")
    if not isinstance(members, list) or len(members) != 1:
        return f"{label} judgment must have exactly one raw member", None
    member = members[0]
    if (
        not isinstance(member, tuple)
        or len(member) != 2
        or not isinstance(member[0], str)
        or not isinstance(member[1], Mapping)
    ):
        return f"{label} judgment has a malformed raw member", None
    section, item = member
    if section in _FORBIDDEN_SECTIONS:
        return f"{label} judgment is a forbidden {section} group", None
    if section not in _NORMAL_SECTIONS:
        return f"{label} judgment is not a boundary/conclusion group", None
    if current:
        if not source_record_item_reuse_eligible(
            item, expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA
        ):
            return f"{label} current row is not explicitly reusable at schema {SOURCE_RECORD_ITEM_DIGEST_SCHEMA}", None
        if item.get("source_record_item_digest_schema") != SOURCE_RECORD_ITEM_DIGEST_SCHEMA:
            return f"{label} current row has the wrong item-digest schema", None
        context_digest = _sha256(item.get("source_record_item_context_sha256"))
        item_digest = _sha256(item.get("source_record_item_sha256"))
        if not context_digest or context_digest != item_digest:
            return f"{label} current row has inconsistent item/context digests", None
    return "", (section, item)


def _legacy_row_error(item: Mapping[str, Any], *, label: str) -> str:
    """Require an unambiguously pre-scoped item receipt, not a partial one."""

    has_context = _SCOPED_PIN_FIELDS[0] in item
    has_fidelity = _SCOPED_PIN_FIELDS[1] in item
    if has_context != has_fidelity:
        return f"{label} legacy row is malformed partially-modern scoped metadata"
    if has_context:
        return f"{label} prior row is not visibly legacy; it already carries scoped metadata"
    present = {field for field in _LEGACY_ITEM_CREDENTIAL_FIELDS if field in item}
    if not present:
        return ""
    # A pre-schema item may have recorded only that it was *not* reusable,
    # pending a later signature revalidation.  This is a historical rejection
    # marker, never affirmative evidence: it has no digest, semantic ID, or
    # current-schema claim, and it is admitted only so a separately pinned
    # historical/raw projection can inspect the actual source and Lean data.
    if present == {"source_record_item_reuse_eligibility"}:
        eligibility = item.get("source_record_item_reuse_eligibility")
        blockers = eligibility.get("blockers") if isinstance(eligibility, Mapping) else None
        if (
            isinstance(eligibility, Mapping)
            and eligibility.get("eligible") is False
            and isinstance(blockers, list)
            and blockers
            and all(isinstance(blocker, str) and blocker.strip() for blocker in blockers)
        ):
            return ""
        return f"{label} legacy rejection marker is malformed or affirmative"
    if present != _LEGACY_ITEM_CREDENTIAL_FIELDS:
        return f"{label} legacy row carries an incomplete old item-receipt shape"
    schema = item.get("source_record_item_digest_schema")
    if isinstance(schema, bool) or not isinstance(schema, int) or schema >= SOURCE_RECORD_ITEM_DIGEST_SCHEMA:
        return f"{label} legacy row incorrectly claims a current item-digest schema"
    for field in (
        "source_record_item_semantic_id",
        "source_record_item_context_sha256",
        "source_record_item_sha256",
    ):
        if not _sha256(item.get(field)):
            return f"{label} legacy row has malformed `{field}`"
    if item.get("source_record_item_context_sha256") != item.get("source_record_item_sha256"):
        return f"{label} legacy row has inconsistent old item/context digests"
    eligibility = item.get("source_record_item_reuse_eligibility")
    if not isinstance(eligibility, Mapping) or eligibility.get("eligible") is not True:
        return f"{label} legacy row has a malformed old reuse-eligibility receipt"
    return ""


def _source_map_items(statement_map: Mapping[str, Any]) -> Mapping[str, Any]:
    raw_items = statement_map.get("items")
    return raw_items if isinstance(raw_items, Mapping) else {}


def _reconciled_source_map_items_by_full_digest(
    statement_map: Mapping[str, Any],
) -> tuple[dict[str, list[Mapping[str, Any]]], str]:
    """Index an authenticated reconciliation witness without map-key joins.

    This helper is deliberately used only after the historical-association
    reconciliation loader has replayed an immutable witness map.  A full
    source-map item digest is then the sole permitted cross-map selector: a
    storage key may have changed between the archived raw audit and its
    witness.  Duplicate full records remain ambiguous rather than letting an
    arbitrary key break the tie.
    """

    index: dict[str, list[Mapping[str, Any]]] = {}
    for source_item in _source_map_items(statement_map).values():
        if not isinstance(source_item, Mapping):
            return {}, "reconciled witness statement map has a malformed item"
        full_digest = _sha256(source_map_item_record_digest(source_item))
        if not full_digest:
            return {}, "reconciled witness statement map has an undigestible item"
        index.setdefault(full_digest, []).append(source_item)
    return index, ""


def _semantic_rebind_module() -> Any:
    """Load the established schema-1-to-2 semantic projection lazily.

    The scoped receipt has no authority to guess an old source identity.  The
    semantic-rebind module already owns the strict, name-independent
    projection from a schema-1 association to a reconciled source-map item.
    Keeping that projection in one place prevents this narrow receipt lane
    from inventing a second historical interpretation.
    """

    try:
        from scripts import source_record_semantic_rebind as semantic_rebind
    except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
        import source_record_semantic_rebind as semantic_rebind
    return semantic_rebind


def _reconciled_legacy_item_for_scoped_pins(
    item: Mapping[str, Any],
    statement_map: Mapping[str, Any],
    *,
    reconciled_map_items_by_full_digest: Mapping[str, Sequence[Mapping[str, Any]]],
    label: str,
) -> tuple[dict[str, Any] | None, str]:
    """Derive absent schema-1 source SHA pins from an authenticated witness.

    This is an in-memory projection only.  It never edits an archived raw
    audit.  Each source identity is independently resolved by its complete
    source-map-item digest after the historical reconciliation loader has
    replayed the raw/witness pair.  Storage keys and declaration spellings are
    retained only as local schema validation data and do not select a match.
    """

    semantic_rebind = _semantic_rebind_module()
    map_items = semantic_rebind._map_items(statement_map)
    projected = copy.deepcopy(dict(item))
    for field in _ASSOCIATION_FIELDS:
        association = projected.get(field)
        if association is None:
            continue
        if not isinstance(association, Mapping):
            return None, f"{label} {field} is not an object"
        identities = association.get("source_item_identities")
        if not isinstance(identities, list) or not identities:
            return None, f"{label} {field} has no source identities"
        for index, identity in enumerate(identities):
            if not isinstance(identity, dict):
                return None, f"{label} {field} source identity {index} is malformed"
            try:
                resolved = semantic_rebind._identity_from_map(
                    identity,
                    map_items=map_items,
                    map_items_by_full_digest=reconciled_map_items_by_full_digest,
                    current=False,
                    label=f"{label} {field} source identity {index}",
                )
            except semantic_rebind.SourceRecordSemanticRebindError as exc:
                return None, str(exc)
            semantic_sha = _sha256(resolved.get("source_item_semantic_sha256"))
            supplied = _sha256(identity.get("source_semantic_sha256"))
            if not semantic_sha or (supplied and supplied != semantic_sha):
                return None, f"{label} {field} has an inconsistent source semantic identity"
            identity["source_semantic_sha256"] = semantic_sha
    return projected, ""


def _reconciled_scoped_item_descriptor(
    *,
    section: str,
    item: Mapping[str, Any],
    statement_map: Mapping[str, Any],
    current: bool,
    reconciled_map_items_by_full_digest: (
        Mapping[str, Sequence[Mapping[str, Any]]] | None
    ),
) -> tuple[dict[str, Any] | None, str]:
    """Compare source/Lean obligation semantics, leaving scoped pins separate.

    The source map's *item-scoped* context and proof-fidelity records are
    regenerated and compared independently.  Their generator-issued digest
    fields must therefore not make an otherwise identical historic obligation
    look changed merely because schema 1 did not persist them.
    """

    semantic_rebind = _semantic_rebind_module()
    try:
        normalized, _route = semantic_rebind._normalized_generated_item(
            item,
            section=section,
            map_items=semantic_rebind._map_items(statement_map),
            map_items_by_full_digest=reconciled_map_items_by_full_digest,
            current=current,
        )
    except semantic_rebind.SourceRecordSemanticRebindError as exc:
        return None, str(exc)
    descriptor = copy.deepcopy(dict(normalized))
    semantic_descriptor = descriptor.get("semantic_descriptor")
    if not isinstance(semantic_descriptor, dict):
        return None, "semantic projection has no item descriptor"
    # These two values are current/legacy producer receipts, not the source or
    # Lean obligation.  The caller derives their underlying source records
    # directly and demands exact equality before a response is transported.
    semantic_descriptor.pop("scoped_semantic_context_requirements_sha256", None)
    semantic_descriptor.pop("source_proof_fidelity_records_sha256", None)
    return descriptor, ""


def _map_identity_error(
    identity: Mapping[str, Any],
    map_items: Mapping[str, Any],
    *,
    field: str,
    index: int,
    reconciled_map_items_by_full_digest: (
        Mapping[str, Sequence[Mapping[str, Any]]] | None
    ) = None,
) -> str:
    semantic_sha = _sha256(identity.get("source_semantic_sha256"))
    if not semantic_sha:
        return f"{field}.source_item_identities[{index}] lacks source semantic identity"
    source_key = str(identity.get("source_key") or "").strip()
    if not source_key:
        return f"{field}.source_item_identities[{index}] lacks a map validation address"
    full_digest = identity.get("source_map_item_sha256")
    if reconciled_map_items_by_full_digest is not None:
        # An authenticated historical reconciliation has already proved that
        # full item pins, not archived storage keys, identify its witness.
        # The raw address remains required schema shape, but is deliberately
        # absent from the cross-map semantic relation.
        resolved_full_digest = _sha256(full_digest)
        if not resolved_full_digest:
            return (
                f"{field}.source_item_identities[{index}] lacks a complete "
                "source-map item digest for reconciled lookup"
            )
        matches = reconciled_map_items_by_full_digest.get(resolved_full_digest, ())
        if len(matches) != 1:
            detail = "no" if not matches else "multiple"
            return (
                f"{field} full source-map item digest resolves to {detail} "
                "reconciled witness items"
            )
        source_item = matches[0]
    else:
        # Ordinary archived-map validation still uses its exact local address.
        source_item = map_items.get(source_key)
        if not isinstance(source_item, Mapping):
            return f"{field} source identity is absent from the statement map"
    if source_item_coverage_sha256(dict(source_item), "") != semantic_sha:
        return f"{field} source identity does not match the statement-map source content"
    if full_digest is not None and _sha256(full_digest) != source_map_item_record_digest(source_item):
        return f"{field} source identity has a stale source-map item digest"
    source_location = identity.get("source_location")
    if source_location is not None and str(source_location).strip() != str(
        source_item.get("source_location") or ""
    ).strip():
        return f"{field} source identity has a stale source-map location"
    return ""


def _association_descriptor(
    item: Mapping[str, Any],
    statement_map: Mapping[str, Any],
    *,
    label: str,
    reconciled_map_items_by_full_digest: (
        Mapping[str, Sequence[Mapping[str, Any]]] | None
    ) = None,
) -> tuple[list[dict[str, Any]], list[str], str]:
    """Validate local map routes and expose only name-free association content."""

    map_items = _source_map_items(statement_map)
    descriptors: list[dict[str, Any]] = []
    all_source_semantics: set[str] = set()
    for field in _ASSOCIATION_FIELDS:
        if field not in item:
            descriptors.append({"field": field, "state": "absent"})
            continue
        association = item.get(field)
        if association is None:
            descriptors.append({"field": field, "state": "null"})
            continue
        if not isinstance(association, Mapping):
            return [], [], f"{label} {field} is not an object"
        if _payload_is_non_evidence(association):
            return [], [], f"{label} {field} is marked candidate/non-evidence"
        raw_identities = association.get("source_item_identities")
        identities: list[dict[str, str]] = []
        if raw_identities is not None:
            if not isinstance(raw_identities, list) or not raw_identities:
                return [], [], f"{label} {field}.source_item_identities is malformed"
            seen: set[str] = set()
            for index, raw_identity in enumerate(raw_identities):
                if not isinstance(raw_identity, Mapping):
                    return [], [], f"{label} {field}.source_item_identities has a non-object entry"
                if error := _map_identity_error(
                    raw_identity,
                    map_items,
                    field=field,
                    index=index,
                    reconciled_map_items_by_full_digest=(
                        reconciled_map_items_by_full_digest
                    ),
                ):
                    return [], [], f"{label} {error}"
                semantic_sha = _sha256(raw_identity.get("source_semantic_sha256"))
                if semantic_sha in seen:
                    return [], [], f"{label} {field} has duplicate source semantic identities"
                seen.add(semantic_sha)
                all_source_semantics.add(semantic_sha)
                identities.append({"source_semantic_sha256": semantic_sha})

        signature = association.get("reviewed_elaborated_signature_identity")
        if signature is not None:
            if not isinstance(signature, Mapping):
                return [], [], f"{label} {field} has malformed elaborated signature identity"
            signature_digest = _sha256(signature.get("elaborated_signature_sha256"))
            if not signature_digest:
                return [], [], f"{label} {field} lacks an elaborated signature digest"
        else:
            signature_digest = ""

        schema = association.get("schema")
        if schema == 2:
            if not identities or not signature_digest:
                return [], [], f"{label} {field} schema-2 association lacks source/signature identity"
            expected_semantic = semantic_association_record_digest(
                [identity["source_semantic_sha256"] for identity in identities],
                signature,
            )
            if _sha256(association.get("semantic_association_sha256")) != expected_semantic:
                return [], [], f"{label} {field} has a stale semantic association digest"
        if "association_sha256" in association and _sha256(
            association.get("association_sha256")
        ) != source_contract_association_record_digest(association):
            return [], [], f"{label} {field} has a stale full association digest"

        normalized = _name_independent_projection(
            {
                str(key): value
                for key, value in association.items()
                if str(key)
                not in {
                    "source_item_identities",
                    "reviewed_elaborated_signature_identity",
                }
            }
        )
        if not isinstance(normalized, Mapping):  # Defensive; input above is a dict.
            return [], [], f"{label} {field} cannot be normalized"
        entry: dict[str, Any] = {
            "field": field,
            "association": dict(normalized),
            "source_item_semantic_identities": sorted(identities, key=lambda value: value["source_semantic_sha256"]),
        }
        if signature_digest:
            entry["elaborated_signature_sha256"] = signature_digest
        descriptors.append(entry)
    descriptors.sort(
        key=lambda value: json.dumps(value, sort_keys=True, separators=(",", ":"))
    )
    return descriptors, sorted(all_source_semantics), ""


def _name_independent_projection(value: object) -> object:
    """Keep every unknown field while removing only documented navigation data."""

    if isinstance(value, Mapping):
        return {
            str(key): _name_independent_projection(child)
            for key, child in value.items()
            if str(key).strip().lower() not in _NAVIGATION_FIELDS
        }
    if isinstance(value, list):
        return [_name_independent_projection(child) for child in value]
    if isinstance(value, tuple):
        return [_name_independent_projection(child) for child in value]
    return value


def _signature_digests(item: Mapping[str, Any], *, label: str) -> tuple[list[str], str]:
    identities: list[Mapping[str, Any]] = []
    direct = item.get("reviewed_elaborated_signature_identities")
    if direct is not None:
        if not isinstance(direct, list) or not direct:
            return [], f"{label} has malformed direct elaborated signature identities"
        identities.extend(value for value in direct if isinstance(value, Mapping))
        if len(identities) != len(direct):
            return [], f"{label} has a non-object direct elaborated signature identity"
    for field in _ASSOCIATION_FIELDS:
        association = item.get(field)
        if isinstance(association, Mapping):
            identity = association.get("reviewed_elaborated_signature_identity")
            if identity is not None:
                if not isinstance(identity, Mapping):
                    return [], f"{label} {field} has malformed elaborated signature identity"
                identities.append(identity)
    digests: set[str] = set()
    for identity in identities:
        digest = _sha256(identity.get("elaborated_signature_sha256"))
        if not digest:
            return [], f"{label} has an elaborated signature without a digest"
        digests.add(digest)
    if not digests:
        return [], f"{label} has no exact elaborated signature identity"
    return sorted(digests), ""


def _item_descriptor(
    *,
    raw_audit: Mapping[str, Any],
    section: str,
    item: Mapping[str, Any],
    statement_map: Mapping[str, Any],
    label: str,
    reconciled_map_items_by_full_digest: (
        Mapping[str, Sequence[Mapping[str, Any]]] | None
    ) = None,
) -> tuple[dict[str, Any] | None, str]:
    associations, source_semantics, association_error = _association_descriptor(
        item,
        statement_map,
        label=label,
        reconciled_map_items_by_full_digest=reconciled_map_items_by_full_digest,
    )
    if association_error:
        return None, association_error
    signatures, signature_error = _signature_digests(item, label=label)
    if signature_error:
        return None, signature_error
    # The raw item remainder is intentionally complete.  The only omitted
    # fields are navigation addresses, association containers (reintroduced
    # above as validated semantic projections), direct signature spellings,
    # and generator-issued item credentials that a visibly legacy row cannot
    # contain.  Unknown receipt fields remain equality material.
    remainder = {
        str(key): value
        for key, value in item.items()
        if str(key) not in _ASSOCIATION_FIELDS
        and str(key) not in _CURRENT_ITEM_CREDENTIAL_FIELDS
        and str(key) != "reviewed_elaborated_signature_identities"
        and str(key).strip().lower() not in _NAVIGATION_FIELDS
    }
    descriptor = {
        "schema": SOURCE_RECORD_SCOPED_RECEIPT_REBIND_SCHEMA,
        "section": section,
        "formalization_scope": _name_independent_projection(
            raw_audit.get("formalization_scope")
            if "formalization_scope" in raw_audit
            else {"state": "absent"}
        ),
        "source_item_semantic_identities": source_semantics,
        "source_association_roles": associations,
        "elaborated_signature_sha256": signatures,
        "complete_item_remainder": _name_independent_projection(remainder),
    }
    return descriptor, ""


def _derive_scoped_pins(
    item: Mapping[str, Any],
    statement_map: Mapping[str, Any],
    raw_audit: Mapping[str, Any],
    *,
    label: str,
) -> tuple[dict[str, Any] | None, dict[str, Any] | None, str]:
    helper = _load_source_record_audit_helper()
    source_map_semantic_index = helper.source_record_source_map_semantic_index(
        statement_map
    )
    context_pin, fidelity_pin, errors = helper.source_record_item_scoped_context_pins(
        dict(item),
        source_map_semantic_index=source_map_semantic_index,
        source_proof_fidelity=raw_audit.get("source_proof_fidelity"),
    )
    if errors:
        return None, None, f"{label} cannot derive scoped source pins: {'; '.join(sorted(set(errors)))}"
    return context_pin, fidelity_pin, ""


def _current_pin_field_error(
    item: Mapping[str, Any],
    context_pin: Mapping[str, Any] | None,
    fidelity_pin: Mapping[str, Any] | None,
    *,
    label: str,
) -> str:
    helper = _load_source_record_audit_helper()
    for field, pin in zip(_SCOPED_PIN_FIELDS, (context_pin, fidelity_pin)):
        if pin is None:
            if field in item:
                return f"{label} current row carries an unexpected `{field}`"
            continue
        expected = helper.stable_digest(pin)
        if _sha256(item.get(field)) != expected:
            return f"{label} current row has a missing or stale `{field}`"
    return ""


def _sidecar_error(
    sidecar: object,
    *,
    paper: str,
    prior_raw_audit: Mapping[str, Any],
    selected_keys: Sequence[str],
) -> str:
    if not isinstance(sidecar, Mapping):
        return "prior judgment sidecar is not an object"
    if _payload_is_non_evidence(sidecar):
        return "prior judgment sidecar is marked candidate/non-evidence"
    if sidecar.get("schema") != 1 or sidecar.get("paper") != paper:
        return "prior judgment sidecar has the wrong schema or paper"
    if str(sidecar.get("prompt_version") or "").strip() != SOURCE_RECORD_V10_PROMPT_VERSION:
        return "prior judgment sidecar does not use the v10 prompt"
    prior_digest = _sha256(prior_raw_audit.get("source_record_audit_sha256"))
    if _sha256(sidecar.get("source_record_audit_sha256")) != prior_digest:
        return "prior judgment sidecar is not bound to the archived raw audit"
    items = sidecar.get("items")
    if not isinstance(items, Mapping):
        return "prior judgment sidecar has no items object"
    for key in selected_keys:
        response = items.get(key)
        if not isinstance(response, Mapping):
            return f"prior judgment sidecar has no response for `{key}`"
        if SOURCE_RECORD_SCOPED_RECEIPT_REBIND_ITEM_FIELD in response:
            return f"prior response `{key}` already carries scoped-receipt transport provenance"
        if not str(response.get("classification") or "").strip():
            return f"prior response `{key}` has no classification"
        for field in ("validator", "validated_at"):
            effective = response.get(field) or sidecar.get(field)
            if not str(effective or "").strip():
                return f"prior response `{key}` has no {field}"
        response_digest = response.get("source_record_audit_sha256")
        if response_digest is not None and _sha256(response_digest) != prior_digest:
            return f"prior response `{key}` is bound to the wrong raw audit"
    return ""


def _selected_keys_error(keys: Sequence[str]) -> tuple[list[str], str]:
    if isinstance(keys, (str, bytes)):
        return [], "prior judgment keys must be a nonempty sequence, not a string"
    normalized = [str(key).strip() for key in keys]
    if not normalized or any(not key for key in normalized) or len(set(normalized)) != len(normalized):
        return [], "prior judgment keys must be nonempty and unique"
    return sorted(normalized), ""


def _group_descriptor(
    group: Mapping[str, Any],
    *,
    raw_audit: Mapping[str, Any],
    statement_map: Mapping[str, Any],
    label: str,
    current: bool,
    reconciled_map_items_by_full_digest: (
        Mapping[str, Sequence[Mapping[str, Any]]] | None
    ) = None,
) -> tuple[dict[str, Any] | None, tuple[str, Mapping[str, Any]] | None, str]:
    group_error, member = _group_error(group, label=label, current=current)
    if group_error or member is None:
        return None, None, group_error
    section, item = member
    if not current:
        if error := _legacy_row_error(item, label=label):
            return None, None, error
    descriptor, descriptor_error = _item_descriptor(
        raw_audit=raw_audit,
        section=section,
        item=item,
        statement_map=statement_map,
        label=label,
        reconciled_map_items_by_full_digest=reconciled_map_items_by_full_digest,
    )
    return descriptor, member, descriptor_error


def _normal_group_descriptors(
    raw_audit: Mapping[str, Any],
    statement_map: Mapping[str, Any],
    *,
    current: bool,
    reconciled_map_items_by_full_digest: (
        Mapping[str, Sequence[Mapping[str, Any]]] | None
    ) = None,
) -> tuple[dict[str, tuple[dict[str, Any], tuple[str, Mapping[str, Any]]]], dict[str, str]]:
    groups, group_errors = _raw_item_groups(raw_audit)
    descriptors: dict[str, tuple[dict[str, Any], tuple[str, Mapping[str, Any]]]] = {}
    errors: dict[str, str] = dict(group_errors)
    for key, group in groups.items():
        descriptor, member, error = _group_descriptor(
            group,
            raw_audit=raw_audit,
            statement_map=statement_map,
            label=("current" if current else "prior") + f" judgment `{key}`",
            current=current,
            reconciled_map_items_by_full_digest=reconciled_map_items_by_full_digest,
        )
        if error or descriptor is None or member is None:
            errors[key] = error or "could not build descriptor"
            continue
        descriptors[key] = (descriptor, member)
    return descriptors, errors


def _artifact_without_integrity(payload: Mapping[str, Any]) -> dict[str, Any]:
    return {
        str(key): value
        for key, value in payload.items()
        if str(key) != SOURCE_RECORD_SCOPED_RECEIPT_REBIND_INTEGRITY_FIELD
    }


def source_record_scoped_receipt_rebind_sha256(payload: Mapping[str, Any]) -> str:
    return _canonical_digest(_artifact_without_integrity(payload))


def source_record_scoped_receipt_rebind_overlay_path(paper_dir: Path) -> Path:
    return paper_dir / "audit" / SOURCE_RECORD_SCOPED_RECEIPT_REBIND_FILENAME


def build_source_record_scoped_receipt_rebind(
    *,
    paper: str,
    paper_dir: Path,
    prior_raw_audit: Mapping[str, Any],
    current_raw_audit: Mapping[str, Any],
    prior_sidecar: Mapping[str, Any],
    prior_raw_audit_path: Path,
    current_raw_audit_path: Path,
    prior_sidecar_path: Path,
    prior_statement_map: Mapping[str, Any] | None,
    current_statement_map: Mapping[str, Any],
    prior_statement_map_path: Path | None,
    current_statement_map_path: Path,
    prior_judgment_keys: Sequence[str],
    prior_association_snapshot_reconciliation_path: Path | None = None,
) -> dict[str, Any]:
    """Build a single-purpose transport receipt for selected legacy rows."""

    paper_dir = paper_dir.resolve()
    selected_keys, selected_error = _selected_keys_error(prior_judgment_keys)
    if selected_error:
        raise SourceRecordScopedReceiptRebindError(selected_error)
    for label, raw in (("prior", prior_raw_audit), ("current", current_raw_audit)):
        if error := _raw_audit_error(raw, paper=paper, label=label):
            raise SourceRecordScopedReceiptRebindError(error)

    canonical_current_raw = _canonical_paper_path(
        current_raw_audit_path, paper_dir, label="current raw audit"
    )
    canonical_current_map = _canonical_paper_path(
        current_statement_map_path, paper_dir, label="current statement map"
    )
    if canonical_current_raw != (paper_dir / "audit" / "source_record_audit.json").resolve():
        raise SourceRecordScopedReceiptRebindError(
            "current raw audit must be the canonical audit/source_record_audit.json"
        )
    if canonical_current_map != (paper_dir / "audit" / "paper_statement_map.json").resolve():
        raise SourceRecordScopedReceiptRebindError(
            "current statement map must be the canonical audit/paper_statement_map.json"
        )
    prior_statement_map, prior_map_validation = _prior_map_for_build(
        paper=paper,
        paper_dir=paper_dir,
        prior_raw=prior_raw_audit,
        prior_raw_path=prior_raw_audit_path,
        prior_statement_map=prior_statement_map,
        prior_statement_map_path=prior_statement_map_path,
        prior_association_snapshot_reconciliation_path=(
            prior_association_snapshot_reconciliation_path
        ),
    )
    reconciled_prior_map_items_by_full_digest: (
        Mapping[str, Sequence[Mapping[str, Any]]] | None
    ) = None
    if (
        prior_map_validation.get("mode")
        == "historical_association_snapshot_reconciliation"
    ):
        (
            reconciled_prior_map_items_by_full_digest,
            reconciled_index_error,
        ) = _reconciled_source_map_items_by_full_digest(prior_statement_map)
        if reconciled_index_error:
            raise SourceRecordScopedReceiptRebindError(reconciled_index_error)
    if error := _source_map_error(
        current_statement_map,
        statement_map_path=current_statement_map_path,
        raw_audit=current_raw_audit,
        paper_dir=paper_dir,
        label="current",
    ):
        raise SourceRecordScopedReceiptRebindError(error)
    for label, raw, statement_map, allow_reconciled_storage_key_rebind in (
        (
            "prior",
            prior_raw_audit,
            prior_statement_map,
            reconciled_prior_map_items_by_full_digest is not None,
        ),
        ("current", current_raw_audit, current_statement_map, False),
    ):
        if error := _raw_global_context_error(
            raw,
            statement_map,
            paper=paper,
            label=label,
            allow_reconciled_storage_key_rebind=(
                allow_reconciled_storage_key_rebind
            ),
        ):
            raise SourceRecordScopedReceiptRebindError(error)
    if error := _sidecar_error(
        prior_sidecar,
        paper=paper,
        prior_raw_audit=prior_raw_audit,
        selected_keys=selected_keys,
    ):
        raise SourceRecordScopedReceiptRebindError(error)

    prior_descriptors, prior_errors = _normal_group_descriptors(
        prior_raw_audit,
        prior_statement_map,
        current=False,
        reconciled_map_items_by_full_digest=(
            reconciled_prior_map_items_by_full_digest
        ),
    )
    current_descriptors, _current_errors = _normal_group_descriptors(
        current_raw_audit, current_statement_map, current=True
    )
    current_by_digest: dict[str, list[str]] = {}
    for key, (descriptor, _member) in current_descriptors.items():
        current_by_digest.setdefault(_canonical_digest(descriptor), []).append(key)
    prior_by_digest: dict[str, list[str]] = {}
    for key, (descriptor, _member) in prior_descriptors.items():
        prior_by_digest.setdefault(_canonical_digest(descriptor), []).append(key)

    items: dict[str, Any] = {}
    for prior_key in selected_keys:
        if prior_key in prior_errors or prior_key not in prior_descriptors:
            raise SourceRecordScopedReceiptRebindError(
                prior_errors.get(prior_key)
                or f"prior judgment `{prior_key}` has no eligible normal descriptor"
            )
        prior_descriptor, (_prior_section, prior_item) = prior_descriptors[prior_key]
        descriptor_sha = _canonical_digest(prior_descriptor)
        if prior_by_digest.get(descriptor_sha) != [prior_key]:
            raise SourceRecordScopedReceiptRebindError(
                f"prior descriptor for `{prior_key}` is not unique among legacy normal rows"
            )
        current_keys = sorted(current_by_digest.get(descriptor_sha, []))
        if len(current_keys) != 1:
            raise SourceRecordScopedReceiptRebindError(
                f"prior judgment `{prior_key}` does not identify exactly one current normal row"
            )
        current_key = current_keys[0]
        current_descriptor, (_current_section, current_item) = current_descriptors[current_key]
        if canonical_digest_payload(prior_descriptor) != canonical_digest_payload(
            current_descriptor
        ):
            raise SourceRecordScopedReceiptRebindError(
                f"prior/current descriptor mismatch for `{prior_key}`"
            )

        prior_context_pin, prior_fidelity_pin, pin_error = _derive_scoped_pins(
            prior_item,
            prior_statement_map,
            prior_raw_audit,
            label=f"prior judgment `{prior_key}`",
        )
        if pin_error:
            raise SourceRecordScopedReceiptRebindError(pin_error)
        current_context_pin, current_fidelity_pin, pin_error = _derive_scoped_pins(
            current_item,
            current_statement_map,
            current_raw_audit,
            label=f"current judgment `{current_key}`",
        )
        if pin_error:
            raise SourceRecordScopedReceiptRebindError(pin_error)
        if canonical_digest_payload(prior_context_pin) != canonical_digest_payload(
            current_context_pin
        ) or canonical_digest_payload(prior_fidelity_pin) != canonical_digest_payload(
            current_fidelity_pin
        ):
            raise SourceRecordScopedReceiptRebindError(
                f"prior/current scoped source pins differ for `{prior_key}`"
            )
        if error := _current_pin_field_error(
            current_item,
            current_context_pin,
            current_fidelity_pin,
            label=f"current judgment `{current_key}`",
        ):
            raise SourceRecordScopedReceiptRebindError(error)
        prior_response = prior_sidecar["items"][prior_key]
        assert isinstance(prior_response, Mapping)  # established by _sidecar_error
        items[prior_key] = {
            "schema": SOURCE_RECORD_SCOPED_RECEIPT_REBIND_SCHEMA,
            "policy_version": SOURCE_RECORD_SCOPED_RECEIPT_REBIND_POLICY_VERSION,
            "transport": "legacy_v10_scoped_receipt_rebind",
            "prior_judgment_key": prior_key,
            "current_judgment_key": current_key,
            "descriptor": prior_descriptor,
            "descriptor_sha256": descriptor_sha,
            "prior_response_sha256": _canonical_digest(prior_response),
            "derived_scoped_context_pin": copy.deepcopy(prior_context_pin),
            "derived_source_proof_fidelity_pin": copy.deepcopy(prior_fidelity_pin),
            "current_item_receipt": {
                "source_record_item_digest_schema": current_item.get(
                    "source_record_item_digest_schema"
                ),
                "source_record_item_semantic_id": current_item.get(
                    "source_record_item_semantic_id"
                ),
                "source_record_item_context_sha256": current_item.get(
                    "source_record_item_context_sha256"
                ),
                "source_record_item_sha256": current_item.get(
                    "source_record_item_sha256"
                ),
                "source_record_item_semantic_context_requirements_sha256": current_item.get(
                    _SCOPED_PIN_FIELDS[0]
                ),
                "source_record_item_source_proof_fidelity_records_sha256": current_item.get(
                    _SCOPED_PIN_FIELDS[1]
                ),
            },
        }

    artifact: dict[str, Any] = {
        "schema": SOURCE_RECORD_SCOPED_RECEIPT_REBIND_SCHEMA,
        "artifact_kind": SOURCE_RECORD_SCOPED_RECEIPT_REBIND_ARTIFACT_KIND,
        "policy_version": SOURCE_RECORD_SCOPED_RECEIPT_REBIND_POLICY_VERSION,
        "paper": paper,
        "transport": "legacy_v10_scoped_receipt_rebind",
        "prior_judgment_keys": selected_keys,
        "prior_raw_audit": _provenance(
            prior_raw_audit, prior_raw_audit_path, paper_dir, label="prior raw audit"
        ),
        "current_raw_audit_snapshot": _provenance(
            current_raw_audit,
            current_raw_audit_path,
            paper_dir,
            label="current raw audit",
        ),
        "prior_judgment_sidecar": _provenance(
            prior_sidecar,
            prior_sidecar_path,
            paper_dir,
            label="prior judgment sidecar",
        ),
        "prior_statement_map_validation": prior_map_validation,
        "current_statement_map": _provenance(
            current_statement_map,
            current_statement_map_path,
            paper_dir,
            label="current statement map",
        ),
        "items": items,
    }
    artifact[SOURCE_RECORD_SCOPED_RECEIPT_REBIND_INTEGRITY_FIELD] = (
        source_record_scoped_receipt_rebind_sha256(artifact)
    )
    return artifact


def source_record_scoped_receipt_rebind_overlay_error(
    payload: object, *, paper: str, paper_dir: Path
) -> str:
    """Replay an artifact from immutable inputs and reject any deviation."""

    if not isinstance(payload, Mapping):
        return "scoped-receipt rebind artifact is not an object"
    if _payload_is_non_evidence(payload):
        return "scoped-receipt rebind artifact is marked candidate/non-evidence"
    if (
        payload.get("schema") != SOURCE_RECORD_SCOPED_RECEIPT_REBIND_SCHEMA
        or payload.get("artifact_kind")
        != SOURCE_RECORD_SCOPED_RECEIPT_REBIND_ARTIFACT_KIND
        or payload.get("policy_version")
        != SOURCE_RECORD_SCOPED_RECEIPT_REBIND_POLICY_VERSION
        or payload.get("paper") != paper
        or payload.get("transport") != "legacy_v10_scoped_receipt_rebind"
    ):
        return "scoped-receipt rebind artifact has the wrong identity"
    recorded = _sha256(payload.get(SOURCE_RECORD_SCOPED_RECEIPT_REBIND_INTEGRITY_FIELD))
    if not recorded or recorded != source_record_scoped_receipt_rebind_sha256(payload):
        return "scoped-receipt rebind artifact integrity digest is missing or stale"
    raw_keys = payload.get("prior_judgment_keys")
    if not isinstance(raw_keys, list):
        return "scoped-receipt rebind artifact has no selected legacy keys"
    try:
        prior_raw_path, prior_raw = _provenance_payload(
            payload.get("prior_raw_audit"), paper_dir, label="prior raw audit"
        )
        current_raw_path, current_raw = _provenance_payload(
            payload.get("current_raw_audit_snapshot"),
            paper_dir,
            label="current raw audit snapshot",
        )
        prior_sidecar_path, prior_sidecar = _provenance_payload(
            payload.get("prior_judgment_sidecar"),
            paper_dir,
            label="prior judgment sidecar",
        )
        prior_map, prior_map_path, reconciliation_path, prior_map_error = (
            _prior_map_from_validation(
                payload.get("prior_statement_map_validation"),
                paper=paper,
                paper_dir=paper_dir,
                prior_raw=prior_raw,
                prior_raw_path=prior_raw_path,
            )
        )
        if prior_map_error:
            return prior_map_error
        current_map_path, current_map = _provenance_payload(
            payload.get("current_statement_map"), paper_dir, label="current statement map"
        )
        expected = build_source_record_scoped_receipt_rebind(
            paper=paper,
            paper_dir=paper_dir,
            prior_raw_audit=prior_raw,
            current_raw_audit=current_raw,
            prior_sidecar=prior_sidecar,
            prior_raw_audit_path=prior_raw_path,
            current_raw_audit_path=current_raw_path,
            prior_sidecar_path=prior_sidecar_path,
            prior_statement_map=prior_map if reconciliation_path is None else None,
            current_statement_map=current_map,
            prior_statement_map_path=prior_map_path,
            current_statement_map_path=current_map_path,
            prior_judgment_keys=raw_keys,
            prior_association_snapshot_reconciliation_path=reconciliation_path,
        )
    except SourceRecordScopedReceiptRebindError as exc:
        return str(exc)
    if canonical_digest_payload(payload) != canonical_digest_payload(expected):
        return "scoped-receipt rebind artifact does not replay from its evidence inputs"
    return ""


def _current_live_raw_error(
    current_raw_audit: Mapping[str, Any], *, paper: str, paper_dir: Path
) -> str:
    if error := _raw_audit_error(current_raw_audit, paper=paper, label="live current"):
        return error
    path = paper_dir / "audit" / "source_record_audit.json"
    try:
        canonical = _canonical_paper_path(path, paper_dir, label="live current raw audit")
    except SourceRecordScopedReceiptRebindError as exc:
        return str(exc)
    if error := _exact_file_payload_error(canonical, current_raw_audit, label="live current raw audit"):
        return error
    return ""


def _rebind_response(
    prior_response: Mapping[str, Any],
    *,
    current_raw_audit: Mapping[str, Any],
    current_members: list[tuple[str, Mapping[str, Any]]],
    current_judgment_key: str,
    statement_map: Mapping[str, Any],
    metadata: Mapping[str, Any],
) -> dict[str, Any] | None:
    """Replace only current aggregate/association credentials, then mark provenance."""

    response = copy.deepcopy(dict(prior_response))
    for field in _RESPONSE_REBIND_FIELDS:
        response.pop(field, None)
    response["source_record_audit_sha256"] = current_raw_audit[
        "source_record_audit_sha256"
    ]
    projected, error = project_source_record_response_association_pins(
        current_members,
        response,
        judgment_key=current_judgment_key,
        statement_map=statement_map,
    )
    if error or projected is None:
        return None
    projected[SOURCE_RECORD_SCOPED_RECEIPT_REBIND_ITEM_FIELD] = copy.deepcopy(
        dict(metadata)
    )
    return projected


def load_current_source_record_scoped_receipt_rebind_items(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    *,
    path: Path | None = None,
) -> dict[str, _LoadedSourceRecordScopedReceiptRebindItem]:
    """Load replayed current responses; serialized provenance alone has no power."""

    paper_dir = paper_dir.resolve()
    overlay_path = path or source_record_scoped_receipt_rebind_overlay_path(paper_dir)
    try:
        canonical_overlay = _canonical_paper_path(
            overlay_path, paper_dir, label="scoped-receipt rebind overlay"
        )
        payload = _read_json_object(canonical_overlay, label="scoped-receipt rebind overlay")
    except SourceRecordScopedReceiptRebindError:
        return {}
    if source_record_scoped_receipt_rebind_overlay_error(
        payload, paper=paper, paper_dir=paper_dir
    ):
        return {}
    if _current_live_raw_error(current_raw_audit, paper=paper, paper_dir=paper_dir):
        return {}
    try:
        prior_raw_path, prior_raw = _provenance_payload(
            payload["prior_raw_audit"], paper_dir, label="prior raw audit"
        )
        _prior_sidecar_path, prior_sidecar = _provenance_payload(
            payload["prior_judgment_sidecar"], paper_dir, label="prior judgment sidecar"
        )
        prior_map, _prior_map_path, reconciliation_path, prior_map_error = (
            _prior_map_from_validation(
                payload["prior_statement_map_validation"],
                paper=paper,
                paper_dir=paper_dir,
                prior_raw=prior_raw,
                prior_raw_path=prior_raw_path,
            )
        )
        if prior_map_error:
            return {}
        reconciled_prior_map_items_by_full_digest: (
            Mapping[str, Sequence[Mapping[str, Any]]] | None
        ) = None
        if reconciliation_path is not None:
            (
                reconciled_prior_map_items_by_full_digest,
                reconciled_index_error,
            ) = _reconciled_source_map_items_by_full_digest(prior_map)
            if reconciled_index_error:
                return {}
        current_map_path = paper_dir / "audit" / "paper_statement_map.json"
        canonical_current_map = _canonical_paper_path(
            current_map_path, paper_dir, label="live current statement map"
        )
        current_map = _read_json_object(
            canonical_current_map, label="live current statement map"
        )
        snapshot_map_path, snapshot_map = _provenance_payload(
            payload["current_statement_map"], paper_dir, label="current statement map"
        )
        if canonical_current_map != snapshot_map_path or canonical_digest_payload(
            current_map
        ) != canonical_digest_payload(snapshot_map):
            return {}
        if _source_map_error(
            current_map,
            statement_map_path=canonical_current_map,
            raw_audit=current_raw_audit,
            paper_dir=paper_dir,
            label="live current",
        ):
            return {}
        if _raw_global_context_error(
            current_raw_audit, current_map, paper=paper, label="live current"
        ):
            return {}
        prior_descriptors, prior_errors = _normal_group_descriptors(
            prior_raw,
            prior_map,
            current=False,
            reconciled_map_items_by_full_digest=(
                reconciled_prior_map_items_by_full_digest
            ),
        )
        current_descriptors, _current_errors = _normal_group_descriptors(
            current_raw_audit, current_map, current=True
        )
    except (KeyError, SourceRecordScopedReceiptRebindError):
        return {}

    current_by_digest: dict[str, list[str]] = {}
    for key, (descriptor, _member) in current_descriptors.items():
        current_by_digest.setdefault(_canonical_digest(descriptor), []).append(key)
    sidecar_items = prior_sidecar.get("items")
    artifact_items = payload.get("items")
    if not isinstance(sidecar_items, Mapping) or not isinstance(artifact_items, Mapping):
        return {}
    result: dict[str, _LoadedSourceRecordScopedReceiptRebindItem] = {}
    for prior_key, metadata in artifact_items.items():
        if not isinstance(metadata, Mapping):
            continue
        prior_key = str(prior_key)
        prior_entry = prior_descriptors.get(prior_key)
        prior_response = sidecar_items.get(prior_key)
        if prior_entry is None or prior_key in prior_errors or not isinstance(prior_response, Mapping):
            continue
        descriptor, _prior_member = prior_entry
        descriptor_digest = _canonical_digest(descriptor)
        if (
            metadata.get("schema") != SOURCE_RECORD_SCOPED_RECEIPT_REBIND_SCHEMA
            or metadata.get("policy_version")
            != SOURCE_RECORD_SCOPED_RECEIPT_REBIND_POLICY_VERSION
            or metadata.get("transport") != "legacy_v10_scoped_receipt_rebind"
            or metadata.get("prior_judgment_key") != prior_key
            or _sha256(metadata.get("descriptor_sha256")) != descriptor_digest
            or canonical_digest_payload(metadata.get("descriptor"))
            != canonical_digest_payload(descriptor)
            or _sha256(metadata.get("prior_response_sha256"))
            != _canonical_digest(prior_response)
        ):
            continue
        current_keys = sorted(current_by_digest.get(descriptor_digest, []))
        if len(current_keys) != 1:
            continue
        current_key = current_keys[0]
        if metadata.get("current_judgment_key") != current_key:
            continue
        current_descriptor, (section, current_item) = current_descriptors[current_key]
        if canonical_digest_payload(current_descriptor) != canonical_digest_payload(descriptor):
            continue
        context_pin, fidelity_pin, pin_error = _derive_scoped_pins(
            current_item,
            current_map,
            current_raw_audit,
            label=f"live current judgment `{current_key}`",
        )
        if pin_error or _current_pin_field_error(
            current_item,
            context_pin,
            fidelity_pin,
            label=f"live current judgment `{current_key}`",
        ):
            continue
        if canonical_digest_payload(metadata.get("derived_scoped_context_pin")) != canonical_digest_payload(
            context_pin
        ) or canonical_digest_payload(
            metadata.get("derived_source_proof_fidelity_pin")
        ) != canonical_digest_payload(fidelity_pin):
            continue
        expected_receipt = {
            "source_record_item_digest_schema": current_item.get(
                "source_record_item_digest_schema"
            ),
            "source_record_item_semantic_id": current_item.get("source_record_item_semantic_id"),
            "source_record_item_context_sha256": current_item.get(
                "source_record_item_context_sha256"
            ),
            "source_record_item_sha256": current_item.get("source_record_item_sha256"),
            "source_record_item_semantic_context_requirements_sha256": current_item.get(
                _SCOPED_PIN_FIELDS[0]
            ),
            "source_record_item_source_proof_fidelity_records_sha256": current_item.get(
                _SCOPED_PIN_FIELDS[1]
            ),
        }
        if canonical_digest_payload(metadata.get("current_item_receipt")) != canonical_digest_payload(
            expected_receipt
        ):
            continue
        current_groups, _errors = _raw_item_groups(current_raw_audit)
        group = current_groups.get(current_key)
        group_error, member = _group_error(
            group, label=f"live current judgment `{current_key}`", current=True
        )
        if group_error or member is None or member[0] != section:
            continue
        members = group.get("raw_members") if isinstance(group, Mapping) else None
        if not isinstance(members, list) or len(members) != 1:
            continue
        materialized = _rebind_response(
            prior_response,
            current_raw_audit=current_raw_audit,
            current_members=members,
            current_judgment_key=current_key,
            statement_map=current_map,
            metadata={
                **copy.deepcopy(dict(metadata)),
                "live_current_judgment_key": current_key,
                "live_current_descriptor_sha256": descriptor_digest,
            },
        )
        if materialized is not None:
            result[current_key] = _LoadedSourceRecordScopedReceiptRebindItem(materialized)
    return result


def is_loaded_source_record_scoped_receipt_rebind_item(value: object) -> bool:
    """Return true only for an item emitted by this process's replaying loader."""

    return bool(
        isinstance(value, _LoadedSourceRecordScopedReceiptRebindItem)
        and value._source_record_scoped_receipt_rebind_loader_token
        is _LOADED_OVERLAY_ITEM_SENTINEL
        and isinstance(value.get(SOURCE_RECORD_SCOPED_RECEIPT_REBIND_ITEM_FIELD), Mapping)
    )


def source_record_scoped_receipt_rebind_item_has_provenance(value: object) -> bool:
    """Recognize visible provenance without confusing it for loaded authority."""

    return bool(
        isinstance(value, Mapping)
        and isinstance(value.get(SOURCE_RECORD_SCOPED_RECEIPT_REBIND_ITEM_FIELD), Mapping)
    )


def copy_loaded_source_record_scoped_receipt_rebind_item(
    value: Mapping[str, Any], updates: Mapping[str, Any] | None = None
) -> dict[str, Any]:
    """Retain loader authority through an in-memory pin reprojection only."""

    copied: dict[str, Any] = dict(value)
    if updates:
        copied.update(updates)
    if is_loaded_source_record_scoped_receipt_rebind_item(value):
        return _LoadedSourceRecordScopedReceiptRebindItem(copied)
    return copied


def source_record_scoped_receipt_rebind_output_error(
    out: Path, *, paper_dir: Path
) -> str:
    """Only the dedicated overlay path is writable; ordinary evidence is reserved."""

    original = Path(out)
    if any(part in {"", ".", ".."} for part in original.parts):
        return "--out must not use traversal or a path alias"
    candidate = original if original.is_absolute() else paper_dir / original
    if _has_symlink_component(candidate):
        return "--out must not target a symlink"
    canonical = source_record_scoped_receipt_rebind_overlay_path(paper_dir).resolve()
    try:
        resolved = candidate.resolve()
    except OSError:
        return "--out cannot be resolved"
    if resolved != canonical:
        return "--out may target only audit/source_record_scoped_receipt_rebind.json"
    return ""


def _atomic_write(path: Path, contents: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        dir=path.parent,
        prefix=f".{path.name}.",
        delete=False,
        mode="w",
        encoding="utf-8",
    ) as handle:
        handle.write(contents)
        temporary = Path(handle.name)
    os.replace(temporary, path)


def _cli_paper_dir(root: Path, paper: object) -> Path:
    text = str(paper or "").strip()
    pure = PurePosixPath(text)
    if (
        not text
        or "/" in text
        or "\\" in text
        or pure.is_absolute()
        or len(pure.parts) != 1
        or pure.parts[0] in {"", ".", ".."}
    ):
        raise SourceRecordScopedReceiptRebindError(
            "--paper must be one normalized paper-directory component"
        )
    return root / "papers" / text


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Build a fail-closed, source-record-scoped transport for selected "
            "legacy v10 boundary/conclusion receipts."
        )
    )
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--prior-raw-audit", type=Path, required=True)
    parser.add_argument("--prior-sidecar", type=Path, required=True)
    prior_map_group = parser.add_mutually_exclusive_group(required=True)
    prior_map_group.add_argument("--prior-statement-map", type=Path)
    prior_map_group.add_argument(
        "--prior-association-snapshot-reconciliation",
        type=Path,
        help=(
            "Replay-only historical association witness for an archived raw "
            "whose top-level map byte receipt is known to be wrong."
        ),
    )
    parser.add_argument("--current-raw-audit", type=Path)
    parser.add_argument("--current-statement-map", type=Path)
    parser.add_argument("--judgment-key", dest="judgment_keys", action="append", required=True)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--write", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    try:
        root = args.root.resolve()
        paper_dir = _cli_paper_dir(root, args.paper)
        current_raw_path = args.current_raw_audit or paper_dir / "audit" / "source_record_audit.json"
        current_map_path = args.current_statement_map or paper_dir / "audit" / "paper_statement_map.json"
        out = args.out or source_record_scoped_receipt_rebind_overlay_path(paper_dir)
        if output_error := source_record_scoped_receipt_rebind_output_error(
            out, paper_dir=paper_dir
        ):
            raise SourceRecordScopedReceiptRebindError(output_error)
        prior_raw_path = _canonical_paper_path(
            args.prior_raw_audit, paper_dir, label="prior raw audit"
        )
        prior_sidecar_path = _canonical_paper_path(
            args.prior_sidecar, paper_dir, label="prior sidecar"
        )
        prior_map_path = (
            _canonical_paper_path(
                args.prior_statement_map, paper_dir, label="prior statement map"
            )
            if args.prior_statement_map is not None
            else None
        )
        prior_reconciliation_path = (
            _canonical_paper_path(
                args.prior_association_snapshot_reconciliation,
                paper_dir,
                label="prior association snapshot reconciliation",
            )
            if args.prior_association_snapshot_reconciliation is not None
            else None
        )
        current_raw_path = _canonical_paper_path(
            current_raw_path, paper_dir, label="current raw audit"
        )
        current_map_path = _canonical_paper_path(
            current_map_path, paper_dir, label="current statement map"
        )
        artifact = build_source_record_scoped_receipt_rebind(
            paper=str(args.paper),
            paper_dir=paper_dir,
            prior_raw_audit=_read_json_object(prior_raw_path, label="prior raw audit"),
            current_raw_audit=_read_json_object(current_raw_path, label="current raw audit"),
            prior_sidecar=_read_json_object(prior_sidecar_path, label="prior sidecar"),
            prior_raw_audit_path=prior_raw_path,
            current_raw_audit_path=current_raw_path,
            prior_sidecar_path=prior_sidecar_path,
            prior_statement_map=(
                _read_json_object(prior_map_path, label="prior statement map")
                if prior_map_path is not None
                else None
            ),
            current_statement_map=_read_json_object(current_map_path, label="current statement map"),
            prior_statement_map_path=prior_map_path,
            current_statement_map_path=current_map_path,
            prior_judgment_keys=args.judgment_keys,
            prior_association_snapshot_reconciliation_path=prior_reconciliation_path,
        )
    except SourceRecordScopedReceiptRebindError as exc:
        print(f"{args.paper}: scoped receipt rebind refused: {exc}", file=sys.stderr)
        return 1
    if args.write:
        _atomic_write(out, json.dumps(artifact, indent=2, sort_keys=True) + "\n")
        print(f"{args.paper}: wrote {out} ({len(artifact['items'])} scoped receipts)")
    else:
        print(
            f"{args.paper}: scoped receipt rebind validates "
            f"({len(artifact['items'])} scoped receipts); rerun with --write"
        )
    return 0


if __name__ == "__main__":  # pragma: no cover - exercised through CLI.
    raise SystemExit(main())
