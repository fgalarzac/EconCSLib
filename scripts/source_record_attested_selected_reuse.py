#!/usr/bin/env python3
"""Reuse a selected v10 semantic review after its historical raw receipt is gone.

This is deliberately narrower than ordinary differential revalidation.  It
handles an otherwise well-authenticated selected current-semantic attestation
whose historical raw audit JSON was not retained.  The historical selected
sidecar, its exact base sidecar, and its exact attestation remain immutable
evidence.  They are replayed on every load before a response can be reused.

The transport relation is a complete generated semantic descriptor SHA-256,
not a judgment key, declaration spelling, binder name, or function name.  A
descriptor must occur exactly once in both the authenticated historical
selected ledger and the current raw audit.  Any changed or ambiguous group is
absent from the loader output and therefore requires an ordinary current
response.
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
from pathlib import Path, PurePosixPath
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:  # Supports direct execution and package imports in focused tests.
    from scripts.source_record_differential_revalidation import (
        SOURCE_RECORD_V10_PROMPT_VERSION,
        _descriptor_index,
        _group_differential_reuse_error,
        _raw_audit_error,
        _raw_item_groups,
    )
    from scripts.source_record_integrity import canonical_digest_payload
except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
    from source_record_differential_revalidation import (
        SOURCE_RECORD_V10_PROMPT_VERSION,
        _descriptor_index,
        _group_differential_reuse_error,
        _raw_audit_error,
        _raw_item_groups,
    )
    from source_record_integrity import canonical_digest_payload


SOURCE_RECORD_ATTESTED_SELECTED_REUSE_SCHEMA = 2
SOURCE_RECORD_ATTESTED_SELECTED_REUSE_POLICY_VERSION = (
    "source-record-v10-attested-selected-semantic-descriptor-reuse-v2"
)
SOURCE_RECORD_ATTESTED_SELECTED_REUSE_ARTIFACT_KIND = (
    "source_record_v10_attested_selected_semantic_reuse"
)
SOURCE_RECORD_ATTESTED_SELECTED_REUSE_FILENAME = (
    "source_record_attested_selected_semantic_reuse.json"
)
SOURCE_RECORD_ATTESTED_SELECTED_REUSE_INTEGRITY_FIELD = (
    "source_record_attested_selected_semantic_reuse_sha256"
)
SOURCE_RECORD_ATTESTED_SELECTED_REUSE_ITEM_FIELD = (
    "source_record_attested_selected_semantic_reuse"
)
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
_LOADED_ITEM_SENTINEL = object()


class SourceRecordAttestedSelectedReuseError(ValueError):
    """Raised when historical selected-review reuse is not admissible."""


class _LoadedSourceRecordAttestedSelectedReuseItem(dict[str, Any]):
    """A JSON-invisible token proving that the reuse loader replayed evidence."""

    __slots__ = ("_source_record_attested_selected_reuse_loader_token",)

    def __init__(self, value: Mapping[str, Any]) -> None:
        super().__init__(value)
        self._source_record_attested_selected_reuse_loader_token = (
            _LOADED_ITEM_SENTINEL
        )


@dataclass(frozen=True)
class _HistoricalSelectedReplay:
    historical_raw_audit_sha256: str
    selected_descriptor_ledger: dict[str, str]
    overlay_descriptor_ledger: dict[str, str]
    responses_by_descriptor: dict[str, dict[str, Any]]
    duplicate_descriptors: frozenset[str]
    unreplayable_descriptors: dict[str, str]
    quarantined_selected_keys: dict[str, dict[str, str]]
    selected_response_semantic_ledger_sha256: str


def _canonical_digest(payload: object) -> str:
    encoded = json.dumps(
        canonical_digest_payload(payload), sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _sha256(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if _SHA256_RE.fullmatch(text) else ""


def _read_json_object_with_sha256(path: Path) -> tuple[dict[str, Any], str]:
    try:
        contents = path.read_bytes()
        payload = json.loads(contents)
    except (OSError, json.JSONDecodeError) as exc:
        raise SourceRecordAttestedSelectedReuseError(
            f"could not read JSON object at {path}: {exc}"
        ) from exc
    if not isinstance(payload, dict):
        raise SourceRecordAttestedSelectedReuseError(f"{path} is not a JSON object")
    return payload, hashlib.sha256(contents).hexdigest()


def _relative_paper_path(path: Path, paper_dir: Path) -> str:
    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordAttestedSelectedReuseError(
            f"{path} must remain inside {paper_dir}"
        ) from exc


def _resolve_paper_relative_path(value: object, paper_dir: Path, *, label: str) -> Path:
    text = str(value or "").strip()
    pure = PurePosixPath(text)
    if (
        not text
        or pure.is_absolute()
        or any(part in {"", ".", ".."} for part in pure.parts)
    ):
        raise SourceRecordAttestedSelectedReuseError(
            f"{label} must be a normalized paper-relative path"
        )
    path = (paper_dir / Path(*pure.parts)).resolve()
    try:
        normalized = path.relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordAttestedSelectedReuseError(
            f"{label} escapes the paper directory"
        ) from exc
    if normalized != text:
        raise SourceRecordAttestedSelectedReuseError(
            f"{label} is not canonical"
        )
    return path


def _current_revalidation_module() -> Any:
    """Import only after audit modules have completed their top-level imports."""

    try:
        from scripts import source_record_current_revalidation as current
    except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
        import source_record_current_revalidation as current
    return current


def _payload_is_non_evidence(payload: Mapping[str, Any]) -> bool:
    if any(
        bool(payload.get(marker))
        for marker in (
            "candidate_only",
            "not_evidence",
            "must_not_be_written_to_repository_sidecar",
            "non_evidence_scaffold",
        )
    ):
        return True
    artifact_kind = str(payload.get("artifact_kind") or "").strip().lower()
    validator_type = str(payload.get("validator_type") or "").strip().lower()
    return (
        "candidate" in artifact_kind
        or "proposal" in artifact_kind
        or "candidate" in validator_type
        or "proposal" in validator_type
    )


def _descriptor_ledger(value: object, *, label: str) -> dict[str, str]:
    """Parse a historical key ledger without using it to match current groups."""

    if not isinstance(value, Mapping):
        raise SourceRecordAttestedSelectedReuseError(
            f"{label} must be an object-valued descriptor ledger"
        )
    ledger: dict[str, str] = {}
    for raw_key, raw_digest in value.items():
        key = str(raw_key or "").strip()
        digest = _sha256(raw_digest)
        if not key or not digest or key in ledger:
            raise SourceRecordAttestedSelectedReuseError(
                f"{label} has an empty, duplicate, or malformed entry"
            )
        ledger[key] = digest
    if not ledger:
        raise SourceRecordAttestedSelectedReuseError(f"{label} is empty")
    return ledger


def _snapshot_record(
    path: Path,
    paper_dir: Path,
    *,
    logical_issued_path: Path | None = None,
) -> dict[str, str]:
    return {
        "snapshot_path": _relative_paper_path(path, paper_dir),
        "snapshot_file_sha256": _file_sha256(path),
        "logical_issued_path": _relative_paper_path(
            logical_issued_path or path, paper_dir
        ),
    }


def _snapshot_paths_from_record(
    record: object, paper_dir: Path, *, label: str
) -> tuple[Path, Path, str]:
    if not isinstance(record, Mapping):
        raise SourceRecordAttestedSelectedReuseError(f"{label} provenance is malformed")
    snapshot_path = _resolve_paper_relative_path(
        record.get("snapshot_path"), paper_dir, label=f"{label} snapshot path"
    )
    logical_path = _resolve_paper_relative_path(
        record.get("logical_issued_path"), paper_dir, label=f"{label} logical path"
    )
    file_sha256 = _sha256(record.get("snapshot_file_sha256"))
    if not file_sha256:
        raise SourceRecordAttestedSelectedReuseError(
            f"{label} has no valid snapshot-file SHA-256"
        )
    return snapshot_path, logical_path, file_sha256


def _snapshot_matches(
    path: Path,
    supplied: Mapping[str, Any],
    *,
    expected_file_sha256: str | None = None,
    label: str,
) -> tuple[dict[str, Any], str]:
    saved, saved_sha256 = _read_json_object_with_sha256(path)
    if expected_file_sha256 and saved_sha256 != expected_file_sha256:
        raise SourceRecordAttestedSelectedReuseError(
            f"{label} bytes no longer match their authenticated snapshot"
        )
    if _canonical_digest(saved) != _canonical_digest(supplied):
        raise SourceRecordAttestedSelectedReuseError(
            f"supplied {label} does not match the immutable snapshot file bytes"
        )
    return saved, saved_sha256


def _require_digest_equality(
    left: object, right: object, *, label: str
) -> str:
    left_digest = _sha256(left)
    right_digest = _sha256(right)
    if not left_digest or left_digest != right_digest:
        raise SourceRecordAttestedSelectedReuseError(label)
    return left_digest


def _historical_base_sidecar_root_error(sidecar: Mapping[str, Any]) -> str:
    """Validate global base-sidecar metadata without blessing every response.

    A selected attestation may need only a strict subset of an archived base
    ledger.  A stale, unrelated entry must not make a valid selected response
    look invalid, but it also cannot be silently accepted.  The caller checks
    every base entry actually used to reconstruct a selected response below.
    """

    if not _sha256(sidecar.get("source_record_audit_sha256")):
        return "historical base sidecar has no aggregate source-record audit digest"
    if str(sidecar.get("prompt_version") or "").strip() != (
        SOURCE_RECORD_V10_PROMPT_VERSION
    ):
        return "historical base sidecar does not use the v10 source-record prompt"
    validator = sidecar.get("validator") or sidecar.get("model")
    timestamp = sidecar.get("validated_at") or sidecar.get("timestamp")
    if not str(validator or "").strip() or not str(timestamp or "").strip():
        return "historical base sidecar lacks validator or timestamp metadata"
    return ""


def _historical_base_item_error(
    sidecar: Mapping[str, Any], item: Mapping[str, Any], *, key: str
) -> str:
    """Validate one base response that an attested selected response uses."""

    aggregate = _sha256(sidecar.get("source_record_audit_sha256"))
    if not aggregate:
        return "historical base sidecar has no aggregate source-record audit digest"
    prompt = str(item.get("prompt_version") or sidecar.get("prompt_version") or "").strip()
    item_digest = _sha256(
        item.get("source_record_audit_sha256")
        or sidecar.get("source_record_audit_sha256")
    )
    validator = item.get("validator") or sidecar.get("validator") or sidecar.get("model")
    timestamp = (
        item.get("validated_at")
        or sidecar.get("validated_at")
        or sidecar.get("timestamp")
    )
    if prompt != SOURCE_RECORD_V10_PROMPT_VERSION:
        return f"historical base judgment `{key}` does not use the v10 source-record prompt"
    if item_digest != aggregate:
        return (
            f"historical base judgment `{key}` is not bound to the base sidecar "
            "aggregate digest"
        )
    if not str(validator or "").strip() or not str(timestamp or "").strip():
        return f"historical base judgment `{key}` lacks validator or timestamp metadata"
    return ""


def _historical_selected_replay(
    selected_sidecar: Mapping[str, Any],
    selected_attestation: Mapping[str, Any],
    base_sidecar: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    selected_sidecar_path: Path,
    selected_sidecar_logical_path: Path,
    selected_attestation_path: Path,
    selected_attestation_logical_path: Path,
    base_sidecar_path: Path,
    base_sidecar_logical_path: Path,
    selected_sidecar_sha256: str,
    selected_attestation_sha256: str,
    base_sidecar_sha256: str,
) -> _HistoricalSelectedReplay:
    """Authenticate historical selected responses without a historical raw JSON.

    Historical storage keys are used only to prove that the selected sidecar is
    the exact attested transformation of the exact base sidecar.  The returned
    response map is keyed by an attested semantic descriptor digest; no later
    current-obligation matching looks at those storage keys.
    """

    current = _current_revalidation_module()
    if _payload_is_non_evidence(selected_sidecar):
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected sidecar is marked non-evidence"
        )
    if _payload_is_non_evidence(selected_attestation):
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected attestation is marked non-evidence"
        )
    if _payload_is_non_evidence(base_sidecar):
        raise SourceRecordAttestedSelectedReuseError(
            "historical base sidecar is marked non-evidence"
        )

    try:
        selected_items = current._sidecar_items(selected_sidecar, paper=paper)
        base_items = current._sidecar_items(base_sidecar, paper=paper)
    except Exception as exc:
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected/base sidecar structure is invalid: " + str(exc)
        ) from exc
    if error := current._prior_sidecar_error(selected_sidecar, selected_items):
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected sidecar is invalid: " + error
        )
    if error := _historical_base_sidecar_root_error(base_sidecar):
        raise SourceRecordAttestedSelectedReuseError(
            "historical base sidecar is invalid: " + error
        )
    if selected_sidecar.get("paper") not in {None, paper}:
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected sidecar belongs to another paper"
        )
    if str(selected_sidecar.get("prompt_version") or "").strip() != (
        SOURCE_RECORD_V10_PROMPT_VERSION
    ):
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected sidecar does not use the v10 prompt"
        )

    metadata = selected_sidecar.get(current.SELECTED_CURRENT_REVALIDATION_FIELD)
    if not isinstance(metadata, Mapping):
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected sidecar lacks selected-revalidation metadata"
        )
    if metadata.get("schema") != current.SELECTED_CURRENT_REVALIDATION_SCHEMA:
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected sidecar has an unsupported selected-revalidation schema"
        )
    if metadata.get("policy_version") != (
        current.SELECTED_CURRENT_REVALIDATION_POLICY_VERSION
    ):
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected sidecar has an unsupported selected-revalidation policy"
        )
    if str(metadata.get("current_judgment_sidecar_path") or "").strip() != (
        _relative_paper_path(selected_sidecar_logical_path, paper_dir)
    ):
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected sidecar names a different logical output path"
        )
    if str(metadata.get("attestation_path") or "").strip() != _relative_paper_path(
        selected_attestation_logical_path, paper_dir
    ):
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected sidecar names a different selected attestation"
        )
    _require_digest_equality(
        metadata.get("attestation_sha256"),
        selected_attestation_sha256,
        label="historical selected sidecar attestation bytes do not match",
    )
    if str(metadata.get("prior_judgment_sidecar_path") or "").strip() != (
        _relative_paper_path(base_sidecar_logical_path, paper_dir)
    ):
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected sidecar names a different base-sidecar snapshot"
        )
    _require_digest_equality(
        metadata.get("prior_judgment_sidecar_sha256"),
        base_sidecar_sha256,
        label="historical selected sidecar base-sidecar bytes do not match",
    )

    if selected_attestation.get("schema") != current.SELECTED_CURRENT_REVALIDATION_SCHEMA:
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected attestation has an unsupported schema"
        )
    if selected_attestation.get("artifact_kind") != (
        current.SELECTED_CURRENT_REVALIDATION_ATTESTATION_KIND
    ):
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected attestation has the wrong artifact kind"
        )
    if selected_attestation.get("policy_version") != (
        current.SELECTED_CURRENT_REVALIDATION_POLICY_VERSION
    ):
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected attestation has an unsupported policy"
        )
    if selected_attestation.get("paper") != paper:
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected attestation belongs to another paper"
        )
    if selected_attestation.get("reviewed_current_semantics") is not True:
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected attestation does not affirm current semantic review"
        )
    if str(selected_attestation.get("review_scope") or "").strip() != (
        current.SELECTED_CURRENT_REVALIDATION_SCOPE
    ):
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected attestation has the wrong review scope"
        )
    reviewer = str(selected_attestation.get("reviewer") or "").strip()
    validated_at = str(selected_attestation.get("validated_at") or "").strip()
    if not reviewer or not validated_at:
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected attestation lacks reviewer or validation time"
        )
    if str(selected_attestation.get("prior_judgment_sidecar_path") or "").strip() != (
        _relative_paper_path(base_sidecar_logical_path, paper_dir)
    ):
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected attestation names a different base-sidecar snapshot"
        )
    _require_digest_equality(
        selected_attestation.get("prior_judgment_sidecar_sha256"),
        base_sidecar_sha256,
        label="historical selected attestation base-sidecar bytes do not match",
    )
    if str(selected_attestation.get("differential_overlay_path") or "").strip() != str(
        metadata.get("differential_overlay_path") or ""
    ).strip() or not _sha256(selected_attestation.get("differential_overlay_sha256")):
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected attestation has inconsistent differential-overlay provenance"
        )
    _require_digest_equality(
        selected_attestation.get("differential_overlay_sha256"),
        metadata.get("differential_overlay_sha256"),
        label="historical selected attestation and sidecar disagree about the differential overlay",
    )

    historical_raw_digest = _require_digest_equality(
        selected_sidecar.get("source_record_audit_sha256"),
        selected_attestation.get("current_source_record_audit_sha256"),
        label="historical selected sidecar and attestation disagree about the raw receipt",
    )
    _require_digest_equality(
        metadata.get("current_source_record_audit_sha256"),
        historical_raw_digest,
        label="historical selected metadata disagrees about the raw receipt",
    )
    selected_ledger = _descriptor_ledger(
        selected_attestation.get("selected_current_group_descriptors"),
        label="historical selected attestation descriptor ledger",
    )
    overlay_ledger = _descriptor_ledger(
        selected_attestation.get("differential_overlay_current_group_descriptors"),
        label="historical selected attestation overlay descriptor ledger",
    )
    if set(selected_ledger.values()) & set(overlay_ledger.values()):
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected and differential descriptor ledgers overlap"
        )
    for payload, prefix in (
        (selected_attestation, "historical selected attestation"),
        (metadata, "historical selected metadata"),
    ):
        payload_selected = _descriptor_ledger(
            payload.get("selected_current_group_descriptors"),
            label=f"{prefix} selected descriptor ledger",
        )
        payload_overlay = _descriptor_ledger(
            payload.get("differential_overlay_current_group_descriptors"),
            label=f"{prefix} overlay descriptor ledger",
        )
        if payload_selected != selected_ledger or payload_overlay != overlay_ledger:
            raise SourceRecordAttestedSelectedReuseError(
                f"{prefix} descriptor ledgers do not match the selected attestation"
            )
        if _sha256(payload.get("selected_current_group_descriptors_sha256")) != (
            _canonical_digest(selected_ledger)
        ):
            raise SourceRecordAttestedSelectedReuseError(
                f"{prefix} selected descriptor-ledger digest is stale"
            )
        if _sha256(payload.get("differential_overlay_current_group_descriptors_sha256")) != (
            _canonical_digest(overlay_ledger)
        ):
            raise SourceRecordAttestedSelectedReuseError(
                f"{prefix} overlay descriptor-ledger digest is stale"
            )
    for field in (
        "generated_judgment_keys_sha256",
        "generated_judgment_surface_sha256",
    ):
        _require_digest_equality(
            selected_attestation.get(field),
            metadata.get(field),
            label=f"historical selected attestation and metadata disagree about {field}",
        )
    if set(selected_items) != set(selected_ledger):
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected sidecar does not exactly cover its attested descriptor ledger"
        )
    # The base snapshot is immutable and structural metadata is authenticated
    # globally above.  Its response receipts are intentionally checked only
    # for selected responses that depend on them.  This preserves a valid
    # selected subset when an unrelated historical differential item was later
    # rebound, while a stale selected response is never returned by the loader.
    unreplayable_descriptors: dict[str, str] = {}
    quarantined_selected_keys: dict[str, dict[str, str]] = {}
    for key in sorted(set(selected_ledger) & set(base_items)):
        error = _historical_base_item_error(base_sidecar, base_items[key], key=key)
        if not error:
            continue
        descriptor = selected_ledger[key]
        reason = (
            "historical selected response is quarantined because its exact base "
            "judgment is invalid: " + error
        )
        unreplayable_descriptors.setdefault(descriptor, reason)
        quarantined_selected_keys[key] = {
            "historical_selected_descriptor_sha256": descriptor,
            "reason": reason,
        }
    for key, value in selected_items.items():
        item_metadata = value.get(current.SELECTED_CURRENT_REVALIDATION_ITEM_FIELD)
        if not isinstance(item_metadata, Mapping):
            raise SourceRecordAttestedSelectedReuseError(
                f"historical selected response has no per-item attestation metadata"
            )
        if item_metadata.get("schema") != current.SELECTED_CURRENT_REVALIDATION_SCHEMA:
            raise SourceRecordAttestedSelectedReuseError(
                "historical selected response has an unsupported per-item schema"
            )
        _require_digest_equality(
            item_metadata.get("attestation_sha256"),
            selected_attestation_sha256,
            label="historical selected response is bound to different attestation bytes",
        )
        _require_digest_equality(
            item_metadata.get("current_group_semantic_descriptor_sha256"),
            selected_ledger[key],
            label="historical selected response has a different descriptor receipt",
        )
        _require_digest_equality(
            value.get("source_record_audit_sha256"),
            historical_raw_digest,
            label="historical selected response is bound to a different raw receipt",
        )
        if str(value.get("validator") or "").strip() != reviewer or str(
            value.get("validated_at") or ""
        ).strip() != validated_at:
            raise SourceRecordAttestedSelectedReuseError(
                "historical selected response reviewer metadata does not match the attestation"
            )
    try:
        expected_items = current._selected_expected_semantic_items(
            base_items, selected_attestation, selected_keys=set(selected_ledger)
        )
        actual_ledger = current._selected_semantic_judgment_ledger(selected_items)
        expected_ledger = current._selected_semantic_judgment_ledger(expected_items)
    except Exception as exc:
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected attestation amendments cannot be replayed: " + str(exc)
        ) from exc
    semantic_ledger_sha256 = _canonical_digest(actual_ledger)
    _require_digest_equality(
        metadata.get("response_semantic_ledger_sha256"),
        semantic_ledger_sha256,
        label="historical selected response semantic-ledger digest is stale",
    )
    for key, descriptor in selected_ledger.items():
        if descriptor in unreplayable_descriptors:
            continue
        if actual_ledger.get(key) == expected_ledger.get(key):
            continue
        reason = (
            "historical selected response is quarantined because its semantic "
            "judgment does not replay from the exact base sidecar plus attestation"
        )
        unreplayable_descriptors[descriptor] = reason
        quarantined_selected_keys[key] = {
            "historical_selected_descriptor_sha256": descriptor,
            "reason": reason,
        }

    descriptor_to_key: dict[str, str] = {}
    duplicate_descriptors: set[str] = set()
    for key, descriptor in selected_ledger.items():
        prior_key = descriptor_to_key.get(descriptor)
        if prior_key is not None:
            duplicate_descriptors.add(descriptor)
        else:
            descriptor_to_key[descriptor] = key
    responses_by_descriptor = {
        descriptor: copy.deepcopy(selected_items[key])
        for descriptor, key in descriptor_to_key.items()
        if descriptor not in duplicate_descriptors
        and descriptor not in unreplayable_descriptors
    }
    return _HistoricalSelectedReplay(
        historical_raw_audit_sha256=historical_raw_digest,
        selected_descriptor_ledger=selected_ledger,
        overlay_descriptor_ledger=overlay_ledger,
        responses_by_descriptor=responses_by_descriptor,
        duplicate_descriptors=frozenset(duplicate_descriptors),
        unreplayable_descriptors=unreplayable_descriptors,
        quarantined_selected_keys=quarantined_selected_keys,
        selected_response_semantic_ledger_sha256=semantic_ledger_sha256,
    )


def _current_raw_record(raw_audit: Mapping[str, Any], path: Path, paper_dir: Path) -> dict[str, str]:
    return {
        "path": _relative_paper_path(path, paper_dir),
        "file_sha256": _file_sha256(path),
        "source_record_audit_sha256": _sha256(raw_audit.get("source_record_audit_sha256")),
        "source_record_audit_integrity_sha256": _sha256(
            raw_audit.get("source_record_audit_integrity_sha256")
        ),
    }


def _current_raw_record_error(
    recorded: object, expected: Mapping[str, str]
) -> str:
    if not isinstance(recorded, Mapping):
        return "current raw-audit provenance is malformed"
    for field in (
        "path",
        "source_record_audit_sha256",
        "source_record_audit_integrity_sha256",
    ):
        if str(recorded.get(field) or "") != str(expected.get(field) or ""):
            return f"current raw-audit provenance has a different `{field}`"
    if not _sha256(recorded.get("file_sha256")):
        return "current raw-audit provenance has no valid issuance file hash"
    return ""


def _artifact_digest(payload: Mapping[str, Any]) -> str:
    stripped = {
        str(key): value
        for key, value in payload.items()
        if str(key) != SOURCE_RECORD_ATTESTED_SELECTED_REUSE_INTEGRITY_FIELD
    }
    return _canonical_digest(stripped)


def stamp_attested_selected_semantic_reuse(payload: dict[str, Any]) -> None:
    payload[SOURCE_RECORD_ATTESTED_SELECTED_REUSE_INTEGRITY_FIELD] = _artifact_digest(
        payload
    )


def attested_selected_semantic_reuse_artifact_error(
    payload: object, *, paper: str
) -> str:
    """Return a structural error before replaying immutable historical evidence."""

    if not isinstance(payload, Mapping):
        return "attested selected-reuse artifact is not an object"
    expected_fields = {
        "schema",
        "artifact_kind",
        "policy_version",
        "paper",
        "prompt_version",
        "source_record_policy_version",
        "historical_selected_sidecar",
        "historical_selected_attestation",
        "historical_base_sidecar",
        "historical_selected_current_raw_audit_sha256",
        "historical_selected_group_descriptor_ledger_sha256",
        "historical_differential_overlay_descriptor_ledger_sha256",
        "historical_generated_judgment_keys_sha256",
        "historical_generated_judgment_surface_sha256",
        "historical_selected_response_semantic_ledger_sha256",
        "current_raw_audit",
        "items",
        "manual_review_required",
        "quarantined_historical_selected_keys",
        SOURCE_RECORD_ATTESTED_SELECTED_REUSE_INTEGRITY_FIELD,
    }
    unexpected = sorted(str(key) for key in payload if str(key) not in expected_fields)
    if unexpected:
        return "attested selected-reuse artifact has unsupported fields: " + ", ".join(
            unexpected[:5]
        )
    if payload.get("schema") != SOURCE_RECORD_ATTESTED_SELECTED_REUSE_SCHEMA:
        return "attested selected-reuse artifact has an unsupported schema"
    if payload.get("artifact_kind") != SOURCE_RECORD_ATTESTED_SELECTED_REUSE_ARTIFACT_KIND:
        return "attested selected-reuse artifact has the wrong artifact kind"
    if payload.get("policy_version") != SOURCE_RECORD_ATTESTED_SELECTED_REUSE_POLICY_VERSION:
        return "attested selected-reuse artifact has an unsupported policy"
    if payload.get("paper") != paper:
        return "attested selected-reuse artifact belongs to another paper"
    if str(payload.get("prompt_version") or "").strip() != SOURCE_RECORD_V10_PROMPT_VERSION:
        return "attested selected-reuse artifact does not use the v10 prompt"
    if str(payload.get("source_record_policy_version") or "").strip() != (
        SOURCE_RECORD_V10_PROMPT_VERSION
    ):
        return "attested selected-reuse artifact does not use the v10 policy"
    if _sha256(payload.get(SOURCE_RECORD_ATTESTED_SELECTED_REUSE_INTEGRITY_FIELD)) != (
        _artifact_digest(payload)
    ):
        return "attested selected-reuse artifact integrity digest does not match"
    for field in (
        "historical_selected_sidecar",
        "historical_selected_attestation",
        "historical_base_sidecar",
        "current_raw_audit",
    ):
        if not isinstance(payload.get(field), Mapping):
            return f"attested selected-reuse artifact has malformed {field} provenance"
    for field in (
        "historical_selected_current_raw_audit_sha256",
        "historical_selected_group_descriptor_ledger_sha256",
        "historical_differential_overlay_descriptor_ledger_sha256",
        "historical_generated_judgment_keys_sha256",
        "historical_generated_judgment_surface_sha256",
        "historical_selected_response_semantic_ledger_sha256",
    ):
        if not _sha256(payload.get(field)):
            return f"attested selected-reuse artifact has no valid {field}"
    items = payload.get("items")
    manual = payload.get("manual_review_required")
    quarantined = payload.get("quarantined_historical_selected_keys")
    if (
        not isinstance(items, Mapping)
        or not isinstance(manual, Mapping)
        or not isinstance(quarantined, Mapping)
    ):
        return "attested selected-reuse artifact has malformed reusable, manual-review, or quarantine ledgers"
    if set(items) & set(manual):
        return "attested selected-reuse artifact overlaps reusable and manual descriptors"
    for raw_descriptor, value in items.items():
        descriptor = _sha256(raw_descriptor)
        if not descriptor or not isinstance(value, Mapping):
            return "attested selected-reuse artifact has a malformed reusable descriptor"
        if _sha256(value.get("historical_selected_descriptor_sha256")) != descriptor:
            return "attested selected-reuse artifact has a stale historical descriptor receipt"
        current_descriptor = value.get("current_group_semantic_descriptor")
        if not isinstance(current_descriptor, Mapping):
            return "attested selected-reuse artifact lacks a current semantic descriptor"
        if _sha256(value.get("current_group_semantic_descriptor_sha256")) != descriptor:
            return "attested selected-reuse artifact has a stale current descriptor receipt"
        if _canonical_digest(current_descriptor) != descriptor:
            return "attested selected-reuse artifact current descriptor content does not match its receipt"
    for raw_descriptor, reason in manual.items():
        if not _sha256(raw_descriptor) or not str(reason or "").strip():
            return "attested selected-reuse artifact has a malformed manual-review descriptor"
    for raw_key, value in quarantined.items():
        key = str(raw_key or "").strip()
        if not key or not isinstance(value, Mapping):
            return "attested selected-reuse artifact has a malformed quarantined selected key"
        if set(value) != {"historical_selected_descriptor_sha256", "reason"}:
            return "attested selected-reuse artifact has a malformed quarantined selected record"
        descriptor = _sha256(value.get("historical_selected_descriptor_sha256"))
        if (
            not descriptor
            or descriptor not in manual
            or descriptor in items
            or not str(value.get("reason") or "").strip()
        ):
            return "attested selected-reuse artifact has an invalid quarantined selected record"
    return ""


def attested_selected_semantic_reuse_path(paper_dir: Path) -> Path:
    return paper_dir / "audit" / SOURCE_RECORD_ATTESTED_SELECTED_REUSE_FILENAME


def build_attested_selected_semantic_reuse(
    current_raw_audit: Mapping[str, Any],
    historical_selected_sidecar: Mapping[str, Any],
    historical_selected_attestation: Mapping[str, Any],
    historical_base_sidecar: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    current_raw_audit_path: Path,
    historical_selected_sidecar_path: Path,
    historical_selected_attestation_path: Path,
    historical_base_sidecar_path: Path,
    historical_selected_sidecar_provenance_path: Path | None = None,
    historical_selected_attestation_provenance_path: Path | None = None,
    historical_base_sidecar_provenance_path: Path | None = None,
) -> dict[str, Any]:
    """Build a descriptor-only reuse overlay from immutable selected evidence.

    The historical raw audit is intentionally not an input.  Every historical
    claim is instead replayed from the selected sidecar, its attestation, and
    its base sidecar.  The historical selected-sidecar snapshot must be
    distinct from the mutable canonical sidecar so a later edit cannot erase
    the exact bytes that this artifact authenticates.
    """

    canonical_sidecar = paper_dir / "audit" / "source_record_match_llm.json"
    if historical_selected_sidecar_path.resolve() == canonical_sidecar.resolve():
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected sidecar must be archived at a path distinct from the mutable canonical sidecar"
        )
    selected_path = _resolve_paper_relative_path(
        _relative_paper_path(historical_selected_sidecar_path, paper_dir),
        paper_dir,
        label="historical selected sidecar path",
    )
    attestation_path = _resolve_paper_relative_path(
        _relative_paper_path(historical_selected_attestation_path, paper_dir),
        paper_dir,
        label="historical selected attestation path",
    )
    base_path = _resolve_paper_relative_path(
        _relative_paper_path(historical_base_sidecar_path, paper_dir),
        paper_dir,
        label="historical base sidecar path",
    )
    raw_path = _resolve_paper_relative_path(
        _relative_paper_path(current_raw_audit_path, paper_dir),
        paper_dir,
        label="current raw audit path",
    )
    selected_logical_path = historical_selected_sidecar_provenance_path or canonical_sidecar
    attestation_logical_path = (
        historical_selected_attestation_provenance_path or attestation_path
    )
    base_logical_path = historical_base_sidecar_provenance_path or base_path
    selected_logical_path = _resolve_paper_relative_path(
        _relative_paper_path(selected_logical_path, paper_dir),
        paper_dir,
        label="historical selected sidecar logical path",
    )
    attestation_logical_path = _resolve_paper_relative_path(
        _relative_paper_path(attestation_logical_path, paper_dir),
        paper_dir,
        label="historical selected attestation logical path",
    )
    base_logical_path = _resolve_paper_relative_path(
        _relative_paper_path(base_logical_path, paper_dir),
        paper_dir,
        label="historical base sidecar logical path",
    )
    saved_selected, selected_sha256 = _snapshot_matches(
        selected_path, historical_selected_sidecar, label="historical selected sidecar"
    )
    saved_attestation, attestation_sha256 = _snapshot_matches(
        attestation_path,
        historical_selected_attestation,
        label="historical selected attestation",
    )
    saved_base, base_sha256 = _snapshot_matches(
        base_path, historical_base_sidecar, label="historical base sidecar"
    )
    saved_raw, _raw_file_sha256 = _snapshot_matches(
        raw_path, current_raw_audit, label="current raw audit"
    )
    if error := _raw_audit_error(saved_raw, paper=paper, label="current"):
        raise SourceRecordAttestedSelectedReuseError(error)
    replay = _historical_selected_replay(
        saved_selected,
        saved_attestation,
        saved_base,
        paper=paper,
        paper_dir=paper_dir,
        selected_sidecar_path=selected_path,
        selected_sidecar_logical_path=selected_logical_path,
        selected_attestation_path=attestation_path,
        selected_attestation_logical_path=attestation_logical_path,
        base_sidecar_path=base_path,
        base_sidecar_logical_path=base_logical_path,
        selected_sidecar_sha256=selected_sha256,
        selected_attestation_sha256=attestation_sha256,
        base_sidecar_sha256=base_sha256,
    )
    current_groups, group_errors = _raw_item_groups(saved_raw)
    if group_errors:
        raise SourceRecordAttestedSelectedReuseError(
            "current raw audit has malformed semantic groups: "
            + ", ".join(sorted(group_errors)[:5])
        )
    current_index = _descriptor_index(current_groups)
    reusable: dict[str, dict[str, Any]] = {}
    manual: dict[str, str] = {}
    for descriptor in sorted(set(replay.selected_descriptor_ledger.values())):
        if descriptor in replay.unreplayable_descriptors:
            manual[descriptor] = replay.unreplayable_descriptors[descriptor]
            continue
        if descriptor in replay.duplicate_descriptors:
            manual[descriptor] = (
                "historical selected descriptor maps to more than one historic response; "
                "descriptor-only carry-forward is ambiguous"
            )
            continue
        candidates = current_index.get(descriptor, [])
        if len(candidates) != 1:
            manual[descriptor] = (
                "no unique current generated semantic descriptor matches the historical "
                "selected descriptor"
            )
            continue
        _current_key, current_group = candidates[0]
        if _group_differential_reuse_error(current_group):
            manual[descriptor] = (
                "the uniquely descriptor-equal current group lacks required direct "
                "semantic reuse evidence"
            )
            continue
        current_descriptor = current_group.get("descriptor")
        if (
            not isinstance(current_descriptor, Mapping)
            or _canonical_digest(current_descriptor) != descriptor
        ):
            manual[descriptor] = (
                "the current semantic descriptor cannot be authenticated exactly"
            )
            continue
        reusable[descriptor] = {
            "historical_selected_descriptor_sha256": descriptor,
            "current_group_semantic_descriptor": copy.deepcopy(dict(current_descriptor)),
            "current_group_semantic_descriptor_sha256": descriptor,
        }
    if set(reusable) | set(manual) != set(replay.selected_descriptor_ledger.values()):
        raise SourceRecordAttestedSelectedReuseError(
            "historical selected descriptor partition is incomplete"
        )
    payload: dict[str, Any] = {
        "schema": SOURCE_RECORD_ATTESTED_SELECTED_REUSE_SCHEMA,
        "artifact_kind": SOURCE_RECORD_ATTESTED_SELECTED_REUSE_ARTIFACT_KIND,
        "policy_version": SOURCE_RECORD_ATTESTED_SELECTED_REUSE_POLICY_VERSION,
        "paper": paper,
        "prompt_version": SOURCE_RECORD_V10_PROMPT_VERSION,
        "source_record_policy_version": SOURCE_RECORD_V10_PROMPT_VERSION,
        "historical_selected_sidecar": _snapshot_record(
            selected_path, paper_dir, logical_issued_path=selected_logical_path
        ),
        "historical_selected_attestation": _snapshot_record(
            attestation_path, paper_dir, logical_issued_path=attestation_logical_path
        ),
        "historical_base_sidecar": _snapshot_record(
            base_path, paper_dir, logical_issued_path=base_logical_path
        ),
        "historical_selected_current_raw_audit_sha256": replay.historical_raw_audit_sha256,
        "historical_selected_group_descriptor_ledger_sha256": _canonical_digest(
            replay.selected_descriptor_ledger
        ),
        "historical_differential_overlay_descriptor_ledger_sha256": _canonical_digest(
            replay.overlay_descriptor_ledger
        ),
        "historical_generated_judgment_keys_sha256": _sha256(
            saved_attestation.get("generated_judgment_keys_sha256")
        ),
        "historical_generated_judgment_surface_sha256": _sha256(
            saved_attestation.get("generated_judgment_surface_sha256")
        ),
        "historical_selected_response_semantic_ledger_sha256": replay.selected_response_semantic_ledger_sha256,
        "current_raw_audit": _current_raw_record(saved_raw, raw_path, paper_dir),
        "items": reusable,
        "manual_review_required": manual,
        "quarantined_historical_selected_keys": copy.deepcopy(
            replay.quarantined_selected_keys
        ),
    }
    stamp_attested_selected_semantic_reuse(payload)
    return payload


def _artifact_paths(
    payload: Mapping[str, Any], paper_dir: Path
) -> tuple[Path, Path, str, Path, Path, str, Path, Path, str, Path]:
    selected_path, selected_logical, selected_sha = _snapshot_paths_from_record(
        payload.get("historical_selected_sidecar"),
        paper_dir,
        label="historical selected sidecar",
    )
    attestation_path, attestation_logical, attestation_sha = _snapshot_paths_from_record(
        payload.get("historical_selected_attestation"),
        paper_dir,
        label="historical selected attestation",
    )
    base_path, base_logical, base_sha = _snapshot_paths_from_record(
        payload.get("historical_base_sidecar"),
        paper_dir,
        label="historical base sidecar",
    )
    raw_record = payload.get("current_raw_audit")
    if not isinstance(raw_record, Mapping):
        raise SourceRecordAttestedSelectedReuseError(
            "attested selected-reuse artifact has malformed current raw-audit provenance"
        )
    raw_path = _resolve_paper_relative_path(
        raw_record.get("path"), paper_dir, label="current raw-audit path"
    )
    return (
        selected_path,
        selected_logical,
        selected_sha,
        attestation_path,
        attestation_logical,
        attestation_sha,
        base_path,
        base_logical,
        base_sha,
        raw_path,
    )


def _normalized_expected_artifact_for_replay(
    expected: dict[str, Any], recorded: Mapping[str, Any]
) -> dict[str, Any]:
    """Allow a derived raw-audit summary refresh without weakening descriptors.

    The raw aggregate and integrity receipts, canonical raw path, and complete
    current descriptor ledger still have to match.  The issuance file hash is
    intentionally archival-only because ``--refresh-judgment-summary`` may
    rewrite a derived summary field without changing those receipts.
    """

    normalized = copy.deepcopy(expected)
    expected_raw = normalized.get("current_raw_audit")
    recorded_raw = recorded.get("current_raw_audit")
    if isinstance(expected_raw, dict) and isinstance(recorded_raw, Mapping):
        expected_raw["file_sha256"] = recorded_raw.get("file_sha256")
        # The artifact receipt commits to its issuance file hash.  Once that
        # intentionally archival-only field is normalized for a derived
        # judgment-summary rewrite, recompute the expected self-receipt too.
        # Aggregate/integrity receipts and every descriptor are still exact.
        stamp_attested_selected_semantic_reuse(normalized)
    return normalized


def load_current_attested_selected_semantic_reuse_items(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    *,
    path: Path | None = None,
) -> dict[str, dict[str, Any]]:
    """Replay authenticated selected evidence and return only exact current groups.

    A serialized item is never trusted directly.  The loader replays the
    exact immutable base sidecar, selected attestation, selected sidecar, and
    descriptor ledger, then uniquely resolves each reusable descriptor against
    the current raw semantic groups.
    """

    artifact_path = path or attested_selected_semantic_reuse_path(paper_dir)
    try:
        artifact, _artifact_file_sha256 = _read_json_object_with_sha256(artifact_path)
    except SourceRecordAttestedSelectedReuseError:
        return {}
    if attested_selected_semantic_reuse_artifact_error(artifact, paper=paper):
        return {}
    try:
        (
            selected_path,
            selected_logical_path,
            selected_sha256,
            attestation_path,
            attestation_logical_path,
            attestation_sha256,
            base_path,
            base_logical_path,
            base_sha256,
            raw_path,
        ) = _artifact_paths(artifact, paper_dir)
        saved_selected, actual_selected_sha256 = _read_json_object_with_sha256(
            selected_path
        )
        saved_attestation, actual_attestation_sha256 = _read_json_object_with_sha256(
            attestation_path
        )
        saved_base, actual_base_sha256 = _read_json_object_with_sha256(base_path)
        saved_raw, _actual_raw_file_sha256 = _read_json_object_with_sha256(raw_path)
    except SourceRecordAttestedSelectedReuseError:
        return {}
    if (
        actual_selected_sha256 != selected_sha256
        or actual_attestation_sha256 != attestation_sha256
        or actual_base_sha256 != base_sha256
        or _canonical_digest(saved_raw) != _canonical_digest(current_raw_audit)
    ):
        return {}
    if error := _raw_audit_error(saved_raw, paper=paper, label="current"):
        return {}
    expected_raw_record = _current_raw_record(saved_raw, raw_path, paper_dir)
    if _current_raw_record_error(artifact.get("current_raw_audit"), expected_raw_record):
        return {}
    try:
        expected = build_attested_selected_semantic_reuse(
            saved_raw,
            saved_selected,
            saved_attestation,
            saved_base,
            paper=paper,
            paper_dir=paper_dir,
            current_raw_audit_path=raw_path,
            historical_selected_sidecar_path=selected_path,
            historical_selected_attestation_path=attestation_path,
            historical_base_sidecar_path=base_path,
            historical_selected_sidecar_provenance_path=selected_logical_path,
            historical_selected_attestation_provenance_path=attestation_logical_path,
            historical_base_sidecar_provenance_path=base_logical_path,
        )
    except SourceRecordAttestedSelectedReuseError:
        return {}
    normalized_expected = _normalized_expected_artifact_for_replay(expected, artifact)
    if _canonical_digest(normalized_expected) != _canonical_digest(artifact):
        return {}
    try:
        replay = _historical_selected_replay(
            saved_selected,
            saved_attestation,
            saved_base,
            paper=paper,
            paper_dir=paper_dir,
            selected_sidecar_path=selected_path,
            selected_sidecar_logical_path=selected_logical_path,
            selected_attestation_path=attestation_path,
            selected_attestation_logical_path=attestation_logical_path,
            base_sidecar_path=base_path,
            base_sidecar_logical_path=base_logical_path,
            selected_sidecar_sha256=actual_selected_sha256,
            selected_attestation_sha256=actual_attestation_sha256,
            base_sidecar_sha256=actual_base_sha256,
        )
        current_groups, group_errors = _raw_item_groups(saved_raw)
        if group_errors:
            return {}
        current_index = _descriptor_index(current_groups)
        current = _current_revalidation_module()
    except (SourceRecordAttestedSelectedReuseError, Exception):
        return {}
    artifact_items = artifact.get("items")
    if not isinstance(artifact_items, Mapping):
        return {}
    out: dict[str, dict[str, Any]] = {}
    current_digest = _sha256(saved_raw.get("source_record_audit_sha256"))
    artifact_digest = _sha256(
        artifact.get(SOURCE_RECORD_ATTESTED_SELECTED_REUSE_INTEGRITY_FIELD)
    )
    for raw_descriptor, item_metadata in artifact_items.items():
        descriptor = _sha256(raw_descriptor)
        if not descriptor or not isinstance(item_metadata, Mapping):
            return {}
        current_descriptor = item_metadata.get("current_group_semantic_descriptor")
        candidates = [
            (key, group)
            for key, group in current_index.get(descriptor, [])
            if isinstance(current_descriptor, Mapping)
            and canonical_digest_payload(group.get("descriptor"))
            == canonical_digest_payload(current_descriptor)
        ]
        if len(candidates) != 1 or descriptor not in replay.responses_by_descriptor:
            return {}
        current_key, current_group = candidates[0]
        if _group_differential_reuse_error(current_group) or current_key in out:
            return {}
        value = copy.deepcopy(replay.responses_by_descriptor[descriptor])
        historical_receipt = current._historical_item_receipt(value)
        if historical_receipt:
            existing = value.get(current.PRIOR_ITEM_RECEIPT_FIELD)
            if isinstance(existing, Mapping):
                value[current.PRIOR_ITEM_RECEIPT_FIELD] = {
                    "prior": copy.deepcopy(dict(existing)),
                    "historical_selected": historical_receipt,
                }
            else:
                value[current.PRIOR_ITEM_RECEIPT_FIELD] = historical_receipt
        value.pop(current.SELECTED_CURRENT_REVALIDATION_ITEM_FIELD, None)
        value["prompt_version"] = SOURCE_RECORD_V10_PROMPT_VERSION
        value["source_record_audit_sha256"] = current_digest
        raw_members = current_group.get("raw_members")
        if not isinstance(raw_members, list):
            return {}
        pins = current._current_item_pins(raw_members)
        if pins:
            value["source_record_item_digest_schema"] = current.SOURCE_RECORD_ITEM_DIGEST_SCHEMA
            value["source_record_item_sha256s"] = pins
            value["source_record_item_sha256"] = pins[0]["source_record_item_sha256"]
        value[SOURCE_RECORD_ATTESTED_SELECTED_REUSE_ITEM_FIELD] = {
            "schema": SOURCE_RECORD_ATTESTED_SELECTED_REUSE_SCHEMA,
            "artifact_sha256": artifact_digest,
            "historical_selected_descriptor_sha256": descriptor,
            "current_group_semantic_descriptor_sha256": descriptor,
            "current_source_record_audit_sha256": current_digest,
        }
        out[current_key] = _LoadedSourceRecordAttestedSelectedReuseItem(value)
    return out


def is_loaded_source_record_attested_selected_reuse_item(value: object) -> bool:
    return bool(
        isinstance(value, _LoadedSourceRecordAttestedSelectedReuseItem)
        and value._source_record_attested_selected_reuse_loader_token
        is _LOADED_ITEM_SENTINEL
        and isinstance(value.get(SOURCE_RECORD_ATTESTED_SELECTED_REUSE_ITEM_FIELD), Mapping)
    )


def source_record_attested_selected_reuse_item_has_provenance(value: object) -> bool:
    return bool(
        isinstance(value, Mapping)
        and isinstance(value.get(SOURCE_RECORD_ATTESTED_SELECTED_REUSE_ITEM_FIELD), Mapping)
    )


def copy_loaded_source_record_attested_selected_reuse_item(
    value: Mapping[str, Any], updates: Mapping[str, Any] | None = None
) -> dict[str, Any]:
    copied: dict[str, Any] = dict(value)
    if updates is not None:
        copied.update(updates)
    if is_loaded_source_record_attested_selected_reuse_item(value):
        return _LoadedSourceRecordAttestedSelectedReuseItem(copied)
    return copied


def _atomic_write(path: Path, contents: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        dir=path.parent, prefix=f".{path.name}.", delete=False, mode="w", encoding="utf-8"
    ) as handle:
        handle.write(contents)
        temporary = Path(handle.name)
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Build a descriptor-only current reuse overlay from immutable selected "
            "v10 evidence when the historical raw receipt is unavailable."
        )
    )
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--historical-selected-sidecar", type=Path, required=True)
    parser.add_argument("--historical-selected-attestation", type=Path, required=True)
    parser.add_argument("--historical-base-sidecar", type=Path, required=True)
    parser.add_argument("--current-raw-audit", type=Path)
    parser.add_argument(
        "--historical-selected-sidecar-provenance-path",
        type=Path,
        help=(
            "logical path recorded when the selected sidecar was issued; defaults "
            "to audit/source_record_match_llm.json"
        ),
    )
    parser.add_argument(
        "--historical-selected-attestation-provenance-path", type=Path
    )
    parser.add_argument("--historical-base-sidecar-provenance-path", type=Path)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--write", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    paper_dir = root / "papers" / args.paper
    current_path = args.current_raw_audit or paper_dir / "audit" / "source_record_audit.json"
    output_path = args.out or attested_selected_semantic_reuse_path(paper_dir)
    try:
        current_raw, _current_sha = _read_json_object_with_sha256(current_path)
        selected, _selected_sha = _read_json_object_with_sha256(
            args.historical_selected_sidecar
        )
        attestation, _attestation_sha = _read_json_object_with_sha256(
            args.historical_selected_attestation
        )
        base, _base_sha = _read_json_object_with_sha256(args.historical_base_sidecar)
        payload = build_attested_selected_semantic_reuse(
            current_raw,
            selected,
            attestation,
            base,
            paper=args.paper,
            paper_dir=paper_dir,
            current_raw_audit_path=current_path,
            historical_selected_sidecar_path=args.historical_selected_sidecar,
            historical_selected_attestation_path=args.historical_selected_attestation,
            historical_base_sidecar_path=args.historical_base_sidecar,
            historical_selected_sidecar_provenance_path=(
                args.historical_selected_sidecar_provenance_path
            ),
            historical_selected_attestation_provenance_path=(
                args.historical_selected_attestation_provenance_path
            ),
            historical_base_sidecar_provenance_path=(
                args.historical_base_sidecar_provenance_path
            ),
        )
    except SourceRecordAttestedSelectedReuseError as exc:
        print(f"{args.paper}: attested selected reuse refused: {exc}", file=sys.stderr)
        return 1
    encoded = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.write:
        _atomic_write(output_path, encoded)
        print(
            f"{args.paper}: wrote attested selected semantic reuse overlay to {output_path} "
            f"({len(payload['items'])} reused; {len(payload['manual_review_required'])} manual; "
            f"{len(payload['quarantined_historical_selected_keys'])} quarantined)"
        )
    else:
        print(
            f"{args.paper}: attested selected semantic reuse validates "
            f"({len(payload['items'])} reused; {len(payload['manual_review_required'])} manual; "
            f"{len(payload['quarantined_historical_selected_keys'])} quarantined); "
            "rerun with --write"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
