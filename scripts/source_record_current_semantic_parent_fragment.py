#!/usr/bin/env python3
"""Authenticate completed reviews of aggregate-only semantic parent groups.

The source-record generator intentionally allows an item to be *aggregate
only*: it has no standalone source-content receipt suitable for narrow
item-level reuse, but it remains part of the current, integrity-stamped raw
audit.  This module provides a deliberately small transport for a reviewer to
complete such a semantic-model review before the entire paper-wide ordinary
sidecar is complete.

The persisted match relation is only the full generated raw-group descriptor
plus its ordered item-pin list (which is explicitly empty for this lane).
Neither a serialized judgment key, declaration, binder, source-map key, nor
function name selects a response.  A loader rederives the current aggregate-
only semantic-parent candidates, requires an exact unique descriptor match,
and issues a private in-memory capability only after the reviewer-authored
semantic response passes the shared v10 completeness contract.

This is not a reuse heuristic.  Every accepted record must contain actual
current reviewer content, including source and Lean evidence for every
generated semantic dimension.  It is intentionally unregistered: consumers
must opt in explicitly after confirming that doing so does not affect raw
producer identity.
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

try:  # Supports direct execution and package imports in focused tests.
    from scripts.source_record_differential_revalidation import (
        SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
        _raw_audit_error,
        _raw_item_groups,
    )
    from scripts.source_record_integrity import (
        canonical_digest_payload,
        reusable_item_metadata_error,
    )
except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
    from source_record_differential_revalidation import (
        SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
        _raw_audit_error,
        _raw_item_groups,
    )
    from source_record_integrity import (
        canonical_digest_payload,
        reusable_item_metadata_error,
    )


SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_SCHEMA = 1
SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_POLICY_VERSION = (
    "source-record-current-semantic-parent-fragment-v1"
)
SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_ARTIFACT_KIND = (
    "source_record_current_semantic_parent_fragment"
)
SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_FILENAME = (
    "source_record_current_semantic_parent_fragment.json"
)
SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_RECEIPT_FIELD = (
    "source_record_current_semantic_parent_fragment_sha256"
)
SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_ITEM_FIELD = (
    "source_record_current_semantic_parent_fragment"
)
SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_ITEM_SCHEMA = 1
SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_REVIEW_FRAGMENT_KIND = (
    "source_record_current_semantic_parent_review_fragment"
)
SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_REVIEW_TEMPLATE_KIND = (
    "source_record_current_semantic_parent_review_fragment_template"
)

_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
_LOADED_ITEM_SENTINEL = object()
_NON_EVIDENCE_MARKERS = frozenset(
    {
        "candidate_only",
        "not_evidence",
        "must_not_be_written_to_repository_sidecar",
        "non_evidence_scaffold",
        "draft",
        "is_draft",
        "proposal_only",
    }
)
_RESPONSE_TRANSPORT_FIELDS = frozenset(
    {
        "prompt_version",
        "validator",
        "model",
        "judge",
        "validated_at",
        "timestamp",
        "generated_at",
        "source_record_audit_sha256",
    }
)


class SourceRecordCurrentSemanticParentFragmentError(ValueError):
    """Raised when an aggregate-only semantic review fragment is inadmissible."""


class _LoadedSourceRecordCurrentSemanticParentFragmentItem(dict[str, Any]):
    """JSON-invisible capability issued only by this module's loader."""

    __slots__ = ("_source_record_current_semantic_parent_fragment_loader_token",)

    def __init__(self, value: Mapping[str, Any]) -> None:
        super().__init__(value)
        self._source_record_current_semantic_parent_fragment_loader_token = (
            _LOADED_ITEM_SENTINEL
        )


@dataclass(frozen=True)
class CurrentSemanticParentFragmentFrozenInputs:
    """The fixed optional receipt snapshot for one evidence transaction.

    The eventual consumer can pass this bundle after it snapshots the fixed
    paper-local path.  The loader then never observes a live appearance,
    disappearance, or mutation of the fragment during the transaction.
    """

    artifact_path: Path
    artifact_present: bool
    artifact_payload: Mapping[str, Any] | None


@dataclass(frozen=True)
class _Candidate:
    """One current aggregate-only semantic parent, addressed only in memory."""

    current_key: str
    semantic_item: Mapping[str, Any]
    group_descriptor: Mapping[str, Any]
    group_descriptor_sha256: str


def _sha256(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if _SHA256_RE.fullmatch(text) else ""


def _canonical_digest(value: object) -> str:
    encoded = json.dumps(
        canonical_digest_payload(value), sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _read_json_object(path: Path) -> tuple[dict[str, Any], bytes]:
    try:
        contents = path.read_bytes()
        payload = json.loads(contents)
    except (OSError, json.JSONDecodeError) as exc:
        raise SourceRecordCurrentSemanticParentFragmentError(
            f"could not read JSON object at {path}: {exc}"
        ) from exc
    if not isinstance(payload, dict):
        raise SourceRecordCurrentSemanticParentFragmentError(
            f"{path} is not a JSON object"
        )
    return payload, contents


def _paper_relative_path(path: Path, paper_dir: Path) -> str:
    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordCurrentSemanticParentFragmentError(
            f"{path} must remain inside {paper_dir}"
        ) from exc


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


def current_semantic_parent_fragment_artifact_path(paper_dir: Path) -> Path:
    """Return the fixed optional paper-local fragment receipt path."""

    return (
        paper_dir
        / "audit"
        / SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_FILENAME
    )


def is_loaded_source_record_current_semantic_parent_fragment_item(
    value: object,
) -> bool:
    """Whether ``value`` has this loader's private in-memory capability."""

    return bool(
        isinstance(value, _LoadedSourceRecordCurrentSemanticParentFragmentItem)
        and value._source_record_current_semantic_parent_fragment_loader_token
        is _LOADED_ITEM_SENTINEL
        and isinstance(
            value.get(SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_ITEM_FIELD),
            Mapping,
        )
    )


def source_record_current_semantic_parent_fragment_item_has_provenance(
    value: object,
) -> bool:
    """Recognize serialized provenance without treating it as authorization."""

    return bool(
        isinstance(value, Mapping)
        and isinstance(
            value.get(SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_ITEM_FIELD),
            Mapping,
        )
    )


def copy_loaded_source_record_current_semantic_parent_fragment_item(
    value: Mapping[str, Any], updates: Mapping[str, Any] | None = None
) -> dict[str, Any]:
    """Copy an authenticated response while preserving its private capability."""

    copied: dict[str, Any] = dict(value)
    if updates is not None:
        copied.update(updates)
    if is_loaded_source_record_current_semantic_parent_fragment_item(value):
        return _LoadedSourceRecordCurrentSemanticParentFragmentItem(copied)
    return copied


def _candidate_signature(
    descriptor: Mapping[str, Any], pins: Sequence[Mapping[str, Any]]
) -> str:
    """Return the exact name-free descriptor-and-ordered-pin identity."""

    return json.dumps(
        {
            "descriptor": canonical_digest_payload(descriptor),
            "ordered_current_item_pins": [
                canonical_digest_payload(pin) for pin in pins
            ],
        },
        sort_keys=True,
        separators=(",", ":"),
    )


def _aggregate_only_semantic_parent_item_error(item: object) -> str:
    """Validate the narrow raw shape that this transport is allowed to carry."""

    if not isinstance(item, Mapping):
        return "semantic parent item is not an object"
    if item.get("kind") != "semantic_model_comparison":
        return "semantic parent item is not a semantic_model_comparison"
    eligibility = item.get("source_record_item_reuse_eligibility")
    if (
        not isinstance(eligibility, Mapping)
        or eligibility.get("eligible") is not False
        or not isinstance(eligibility.get("blockers"), list)
        or not eligibility.get("blockers")
    ):
        return "semantic parent item is not explicitly aggregate-only"
    metadata_error = reusable_item_metadata_error(
        item, expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    )
    if metadata_error:
        return "semantic parent item has invalid aggregate-only metadata: " + metadata_error
    return ""


def aggregate_only_semantic_parent_candidates(
    raw_audit: Mapping[str, Any], *, paper: str
) -> tuple[list[_Candidate], str]:
    """Derive all exact aggregate-only semantic parents from current raw data.

    A group with any extra raw member is intentionally left to the ordinary
    full-group review route.  The storage key stays in memory solely to return
    the response to the generated current ledger after descriptor matching.
    """

    raw_error = _raw_audit_error(
        raw_audit, paper=paper, label="current semantic-parent fragment"
    )
    if raw_error:
        return [], raw_error
    groups, group_errors = _raw_item_groups(raw_audit)
    if group_errors:
        return [], "current raw audit has malformed generated groups"
    candidates: list[_Candidate] = []
    seen_signatures: set[str] = set()
    for current_key, group in groups.items():
        raw_members = group.get("raw_members")
        if not isinstance(raw_members, list) or len(raw_members) != 1:
            continue
        raw_member = raw_members[0]
        if (
            not isinstance(raw_member, tuple)
            or len(raw_member) != 2
            or raw_member[0] != "semantic_model_items"
            or not isinstance(raw_member[1], Mapping)
        ):
            continue
        item = raw_member[1]
        aggregate_error = _aggregate_only_semantic_parent_item_error(item)
        if aggregate_error:
            # A reusable semantic item belongs to the ordinary current route.
            # Any malformed aggregate-only metadata was already rejected by
            # ``_raw_audit_error``; either way this lane must not guess.
            continue
        descriptor = group.get("descriptor")
        descriptor_sha256 = _sha256(group.get("descriptor_sha256"))
        if (
            not isinstance(descriptor, Mapping)
            or not descriptor_sha256
            or _canonical_digest(descriptor) != descriptor_sha256
        ):
            return [], "current semantic-parent group has an invalid descriptor receipt"
        signature = _candidate_signature(descriptor, [])
        if signature in seen_signatures:
            return [], (
                "current aggregate-only semantic parents are descriptor-ambiguous; "
                "a key or name cannot choose a response"
            )
        seen_signatures.add(signature)
        candidates.append(
            _Candidate(
                current_key=str(current_key),
                semantic_item=dict(item),
                group_descriptor=dict(descriptor),
                group_descriptor_sha256=descriptor_sha256,
            )
        )
    candidates.sort(key=lambda candidate: candidate.group_descriptor_sha256)
    return candidates, ""


def _evidence_module() -> Any:
    """Load shared semantic-completeness validation only after raw helpers load."""

    try:
        from scripts import audit_evidence_integrity as evidence
    except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
        import audit_evidence_integrity as evidence
    return evidence


def _contains_non_evidence_marker(value: object) -> bool:
    if isinstance(value, Mapping):
        for raw_key, child in value.items():
            key = str(raw_key).strip()
            if key in _NON_EVIDENCE_MARKERS and bool(child):
                return True
            if key in {"artifact_kind", "validator_type", "status", "state"}:
                text = str(child or "").strip().lower()
                if any(marker in text for marker in ("candidate", "draft", "proposal")):
                    return True
            if _contains_non_evidence_marker(child):
                return True
    elif isinstance(value, (list, tuple)):
        return any(_contains_non_evidence_marker(child) for child in value)
    return False


def _reviewer_response_error(
    response: object, *, candidate: _Candidate, label: str
) -> str:
    """Require substantive reviewer content before any fragment can be current."""

    if not isinstance(response, Mapping):
        return f"{label} response is not an object"
    if _contains_non_evidence_marker(response):
        return f"{label} response is marked candidate/draft/non-evidence"
    generated = [
        str(field)
        for field in response
        if str(field) in _RESPONSE_TRANSPORT_FIELDS
        or str(field).startswith("source_record_")
    ]
    if generated:
        return (
            f"{label} response carries generated/transport fields: "
            + ", ".join(sorted(generated)[:5])
        )
    if not str(response.get("reason") or "").strip():
        return f"{label} response lacks a reason"
    if not str(response.get("source_location") or "").strip():
        return f"{label} response lacks a source_location"
    evidence = _evidence_module()
    if evidence.source_record_payload_is_non_evidence(dict(response)):
        return f"{label} response is not evidence"
    errors = evidence.semantic_model_judgment_completeness_errors(
        dict(candidate.semantic_item), dict(response)
    )
    if errors:
        return (
            f"{label} response fails the shared semantic completeness contract: "
            + "; ".join(errors)
        )
    return ""


def semantic_parent_response_semantic_sha256(response: Mapping[str, Any]) -> str:
    """Return the exact reviewer-content receipt stored in a fragment record."""

    return _canonical_digest(response)


def _review_record_error(
    record: object,
    *,
    candidates_by_signature: Mapping[str, _Candidate],
    label: str,
) -> tuple[_Candidate | None, str]:
    """Validate one self-describing review record without consulting its address."""

    required_fields = {
        "current_group_semantic_descriptor",
        "current_group_semantic_descriptor_sha256",
        "current_item_pins",
        "reviewer",
        "validated_at",
        "review_notes",
        "response",
        "response_semantic_sha256",
    }
    if not isinstance(record, Mapping) or set(record) != required_fields:
        return None, f"{label} has unsupported record fields"
    descriptor = record.get("current_group_semantic_descriptor")
    descriptor_sha256 = _sha256(record.get("current_group_semantic_descriptor_sha256"))
    if (
        not isinstance(descriptor, Mapping)
        or not descriptor_sha256
        or _canonical_digest(descriptor) != descriptor_sha256
    ):
        return None, f"{label} has an invalid current group descriptor"
    pins = record.get("current_item_pins")
    if pins != []:
        return None, f"{label} must carry the explicit empty aggregate-only pin list"
    signature = _candidate_signature(descriptor, [])
    candidate = candidates_by_signature.get(signature)
    if candidate is None:
        return None, f"{label} does not exactly match a current aggregate-only semantic parent"
    if descriptor_sha256 != candidate.group_descriptor_sha256 or (
        canonical_digest_payload(descriptor)
        != canonical_digest_payload(candidate.group_descriptor)
    ):
        return None, f"{label} descriptor does not exactly match the current raw group"
    if any(
        not str(record.get(field) or "").strip()
        for field in ("reviewer", "validated_at", "review_notes")
    ):
        return None, f"{label} lacks reviewer, validated_at, or review_notes"
    response = record.get("response")
    if error := _reviewer_response_error(response, candidate=candidate, label=label):
        return None, error
    assert isinstance(response, Mapping)
    if _sha256(record.get("response_semantic_sha256")) != (
        semantic_parent_response_semantic_sha256(response)
    ):
        return None, f"{label} response semantic receipt is invalid"
    return candidate, ""


def _candidates_by_signature(
    raw_audit: Mapping[str, Any], *, paper: str
) -> tuple[dict[str, _Candidate], str]:
    candidates, error = aggregate_only_semantic_parent_candidates(raw_audit, paper=paper)
    if error:
        return {}, error
    out: dict[str, _Candidate] = {}
    for candidate in candidates:
        signature = _candidate_signature(candidate.group_descriptor, [])
        if signature in out:
            return {}, "current aggregate-only semantic parent ledger is descriptor-ambiguous"
        out[signature] = candidate
    return out, ""


def _review_records_error(
    records: object,
    *,
    raw_audit: Mapping[str, Any],
    paper: str,
) -> tuple[list[tuple[_Candidate, Mapping[str, Any]]] | None, str]:
    """Validate a nonempty, possibly partial set of current reviewer records."""

    if not isinstance(records, list) or not records:
        return None, "semantic-parent fragment has no review records"
    candidates_by_signature, candidate_error = _candidates_by_signature(
        raw_audit, paper=paper
    )
    if candidate_error:
        return None, candidate_error
    validated: list[tuple[_Candidate, Mapping[str, Any]]] = []
    seen: set[str] = set()
    for index, record in enumerate(records, start=1):
        candidate, error = _review_record_error(
            record,
            candidates_by_signature=candidates_by_signature,
            label=f"semantic-parent review record {index}",
        )
        if error or candidate is None:
            return None, error or "semantic-parent review record is invalid"
        signature = _candidate_signature(candidate.group_descriptor, [])
        if signature in seen:
            return None, (
                "semantic-parent fragment repeats a current descriptor; a key or "
                "name cannot choose a response"
            )
        seen.add(signature)
        assert isinstance(record, Mapping)
        validated.append((candidate, record))
    return validated, ""


def _artifact_body(
    *, paper: str, raw_audit: Mapping[str, Any], records: Sequence[Mapping[str, Any]]
) -> dict[str, Any]:
    raw_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    raw_integrity = _sha256(raw_audit.get("source_record_audit_integrity_sha256"))
    if not raw_digest or not raw_integrity:
        raise SourceRecordCurrentSemanticParentFragmentError(
            "current raw audit has no aggregate/integrity receipt"
        )
    normalized_records = sorted(
        (copy.deepcopy(dict(record)) for record in records),
        key=lambda record: str(record["current_group_semantic_descriptor_sha256"]),
    )
    body = {
        "schema": SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_SCHEMA,
        "artifact_kind": SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_ARTIFACT_KIND,
        "policy_version": SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_POLICY_VERSION,
        "paper": paper,
        "current_source_record_audit_sha256": raw_digest,
        "current_source_record_audit_integrity_sha256": raw_integrity,
        "semantic_parent_reviews": normalized_records,
        "semantic_parent_review_descriptors_sha256": _canonical_digest(
            [
                record["current_group_semantic_descriptor_sha256"]
                for record in normalized_records
            ]
        ),
    }
    body[SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_RECEIPT_FIELD] = (
        _canonical_digest(body)
    )
    return body


def build_current_semantic_parent_fragment_artifact(
    *,
    paper: str,
    raw_audit: Mapping[str, Any],
    review_records: Sequence[Mapping[str, Any]],
) -> tuple[dict[str, Any] | None, str]:
    """Build an authenticated partial fragment from already-completed reviews."""

    raw_error = _raw_audit_error(
        raw_audit, paper=paper, label="current semantic-parent fragment"
    )
    if raw_error:
        return None, raw_error
    validated, error = _review_records_error(
        list(review_records), raw_audit=raw_audit, paper=paper
    )
    if error or validated is None:
        return None, error or "could not validate semantic-parent review records"
    try:
        return (
            _artifact_body(
                paper=paper,
                raw_audit=raw_audit,
                records=[record for _candidate, record in validated],
            ),
            "",
        )
    except SourceRecordCurrentSemanticParentFragmentError as exc:
        return None, str(exc)


def semantic_parent_review_fragment_template(
    raw_audit: Mapping[str, Any], *, paper: str
) -> tuple[dict[str, Any] | None, str]:
    """Create a non-evidence scaffold for every current aggregate-only parent.

    A completed subset may later be placed in a completed review fragment and
    authenticated with :func:`build_current_semantic_parent_fragment_artifact`.
    The template itself is deliberately rejected by every evidence path.
    """

    candidates, error = aggregate_only_semantic_parent_candidates(raw_audit, paper=paper)
    if error:
        return None, error
    raw_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    raw_integrity = _sha256(raw_audit.get("source_record_audit_integrity_sha256"))
    if not candidates or not raw_digest or not raw_integrity:
        return None, "current raw audit has no aggregate-only semantic-parent candidates"
    records: list[dict[str, Any]] = []
    for candidate in candidates:
        records.append(
            {
                "current_group_semantic_descriptor": copy.deepcopy(
                    dict(candidate.group_descriptor)
                ),
                "current_group_semantic_descriptor_sha256": (
                    candidate.group_descriptor_sha256
                ),
                "current_item_pins": [],
                "reviewer": "",
                "validated_at": "",
                "review_notes": "",
                "response": {},
                "response_semantic_sha256": "",
            }
        )
    return (
        {
            "schema": SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_SCHEMA,
            "artifact_kind": SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_REVIEW_TEMPLATE_KIND,
            "policy_version": SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_POLICY_VERSION,
            "completed_fragment_artifact_kind": (
                SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_REVIEW_FRAGMENT_KIND
            ),
            "paper": paper,
            "current_source_record_audit_sha256": raw_digest,
            "current_source_record_audit_integrity_sha256": raw_integrity,
            "semantic_parent_reviews": records,
            "candidate_only": True,
            "non_evidence_scaffold": True,
        },
        "",
    )


def _review_fragment_error(
    fragment: object, *, paper: str, raw_audit: Mapping[str, Any]
) -> tuple[list[tuple[_Candidate, Mapping[str, Any]]] | None, str]:
    """Validate a completed reviewer fragment before it is receipt-bound."""

    required_fields = {
        "schema",
        "artifact_kind",
        "policy_version",
        "paper",
        "current_source_record_audit_sha256",
        "current_source_record_audit_integrity_sha256",
        "semantic_parent_reviews",
    }
    if not isinstance(fragment, Mapping) or set(fragment) != required_fields:
        return None, "semantic-parent review fragment has unsupported top-level fields"
    if (
        fragment.get("schema")
        != SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_SCHEMA
        or fragment.get("artifact_kind")
        != SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_REVIEW_FRAGMENT_KIND
        or fragment.get("policy_version")
        != SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_POLICY_VERSION
        or fragment.get("paper") != paper
    ):
        return None, "semantic-parent review fragment has incompatible schema, policy, or paper"
    if _contains_non_evidence_marker(fragment):
        return None, "semantic-parent review fragment is marked candidate/draft/non-evidence"
    if _sha256(fragment.get("current_source_record_audit_sha256")) != _sha256(
        raw_audit.get("source_record_audit_sha256")
    ) or _sha256(fragment.get("current_source_record_audit_integrity_sha256")) != _sha256(
        raw_audit.get("source_record_audit_integrity_sha256")
    ):
        return None, "semantic-parent review fragment has stale current raw-audit receipts"
    return _review_records_error(
        fragment.get("semantic_parent_reviews"), raw_audit=raw_audit, paper=paper
    )


def build_current_semantic_parent_fragment_from_review_fragment(
    *, paper: str, raw_audit: Mapping[str, Any], review_fragment: Mapping[str, Any]
) -> tuple[dict[str, Any] | None, str]:
    """Bind a completed reviewer fragment to the current raw semantic surface."""

    raw_error = _raw_audit_error(
        raw_audit, paper=paper, label="current semantic-parent fragment"
    )
    if raw_error:
        return None, raw_error
    validated, error = _review_fragment_error(
        review_fragment, paper=paper, raw_audit=raw_audit
    )
    if error or validated is None:
        return None, error or "could not validate semantic-parent review fragment"
    return _artifact_body(
        paper=paper,
        raw_audit=raw_audit,
        records=[record for _candidate, record in validated],
    ), ""


def _artifact_error(
    artifact: object, *, paper: str, raw_audit: Mapping[str, Any]
) -> tuple[list[tuple[_Candidate, Mapping[str, Any]]] | None, str]:
    """Re-derive current candidates and validate every receipt-bound review."""

    required_fields = {
        "schema",
        "artifact_kind",
        "policy_version",
        "paper",
        "current_source_record_audit_sha256",
        "current_source_record_audit_integrity_sha256",
        "semantic_parent_reviews",
        "semantic_parent_review_descriptors_sha256",
        SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_RECEIPT_FIELD,
    }
    if not isinstance(artifact, Mapping) or set(artifact) != required_fields:
        return None, "semantic-parent fragment has unsupported top-level fields"
    if (
        artifact.get("schema")
        != SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_SCHEMA
        or artifact.get("artifact_kind")
        != SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_ARTIFACT_KIND
        or artifact.get("policy_version")
        != SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_POLICY_VERSION
        or artifact.get("paper") != paper
    ):
        return None, "semantic-parent fragment has incompatible schema, policy, or paper"
    if _contains_non_evidence_marker(artifact):
        return None, "semantic-parent fragment is marked candidate/draft/non-evidence"
    body = {
        str(key): copy.deepcopy(value)
        for key, value in artifact.items()
        if str(key) != SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_RECEIPT_FIELD
    }
    if _sha256(
        artifact.get(SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_RECEIPT_FIELD)
    ) != _canonical_digest(body):
        return None, "semantic-parent fragment receipt digest is invalid"
    if _sha256(artifact.get("current_source_record_audit_sha256")) != _sha256(
        raw_audit.get("source_record_audit_sha256")
    ) or _sha256(artifact.get("current_source_record_audit_integrity_sha256")) != _sha256(
        raw_audit.get("source_record_audit_integrity_sha256")
    ):
        return None, "semantic-parent fragment is stale against the current raw audit"
    validated, error = _review_records_error(
        artifact.get("semantic_parent_reviews"), raw_audit=raw_audit, paper=paper
    )
    if error or validated is None:
        return None, error or "semantic-parent fragment review records are invalid"
    expected_ledger = _canonical_digest(
        sorted(
            candidate.group_descriptor_sha256
            for candidate, _record in validated
        )
    )
    if _sha256(artifact.get("semantic_parent_review_descriptors_sha256")) != expected_ledger:
        return None, "semantic-parent fragment descriptor ledger digest is stale"
    return validated, ""


def _receipt_artifact(
    *,
    paper_dir: Path,
    frozen_inputs: CurrentSemanticParentFragmentFrozenInputs | None = None,
) -> Mapping[str, Any] | None:
    """Load the fixed optional artifact while honoring transaction snapshots."""

    path = current_semantic_parent_fragment_artifact_path(paper_dir)
    if frozen_inputs is None:
        if not path.is_file():
            return None
        artifact, _ = _read_json_object(path)
        return artifact
    try:
        same_path = frozen_inputs.artifact_path.resolve() == path.resolve()
    except (OSError, RuntimeError):
        same_path = False
    if not same_path:
        raise SourceRecordCurrentSemanticParentFragmentError(
            "frozen semantic-parent fragment path does not match the fixed authority path"
        )
    if not frozen_inputs.artifact_present:
        return None
    if not isinstance(frozen_inputs.artifact_payload, Mapping):
        raise SourceRecordCurrentSemanticParentFragmentError(
            "frozen semantic-parent fragment is malformed"
        )
    return frozen_inputs.artifact_payload


def semantic_parent_fragment_validation_error(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    *,
    frozen_inputs: CurrentSemanticParentFragmentFrozenInputs | None = None,
) -> str:
    """Explain an extant artifact error; absence remains valid legacy state."""

    try:
        artifact = _receipt_artifact(paper_dir=paper_dir, frozen_inputs=frozen_inputs)
        if artifact is None:
            return ""
        _validated, error = _artifact_error(
            artifact, paper=paper, raw_audit=current_raw_audit
        )
        return error
    except (OSError, SourceRecordCurrentSemanticParentFragmentError) as exc:
        return str(exc)
    except Exception as exc:  # noqa: BLE001 - evidence boundaries fail closed.
        return f"semantic-parent fragment replay raised {type(exc).__name__}: {exc}"


def _loaded_response(
    *, candidate: _Candidate, record: Mapping[str, Any], raw_audit: Mapping[str, Any]
) -> dict[str, Any]:
    response = copy.deepcopy(dict(record["response"]))
    response["prompt_version"] = str(raw_audit.get("prompt_version") or "")
    response["source_record_audit_sha256"] = str(
        raw_audit.get("source_record_audit_sha256") or ""
    )
    response["validator"] = str(record["reviewer"]).strip()
    response["validated_at"] = str(record["validated_at"]).strip()
    response[SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_ITEM_FIELD] = {
        "schema": SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_ITEM_SCHEMA,
        "current_group_semantic_descriptor_sha256": (
            candidate.group_descriptor_sha256
        ),
        "response_semantic_sha256": record["response_semantic_sha256"],
    }
    return _LoadedSourceRecordCurrentSemanticParentFragmentItem(response)


def load_current_source_record_current_semantic_parent_fragment_items(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    *,
    frozen_inputs: CurrentSemanticParentFragmentFrozenInputs | None = None,
) -> dict[str, dict[str, Any]]:
    """Load exact current aggregate-only semantic parent responses, or nothing."""

    try:
        artifact = _receipt_artifact(paper_dir=paper_dir, frozen_inputs=frozen_inputs)
        if artifact is None:
            return {}
        validated, error = _artifact_error(
            artifact, paper=paper, raw_audit=current_raw_audit
        )
        if error or validated is None:
            return {}
        loaded: dict[str, dict[str, Any]] = {}
        for candidate, record in validated:
            if candidate.current_key in loaded:
                return {}
            loaded[candidate.current_key] = _loaded_response(
                candidate=candidate, record=record, raw_audit=current_raw_audit
            )
        return loaded
    except (OSError, SourceRecordCurrentSemanticParentFragmentError):
        return {}
    except Exception:  # noqa: BLE001 - malformed optional evidence grants no credit.
        return {}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--raw-audit", type=Path)
    parser.add_argument(
        "--write-template",
        type=Path,
        help="write a non-evidence aggregate-only semantic-parent review scaffold",
    )
    parser.add_argument(
        "--reviews",
        type=Path,
        help="completed review-fragment JSON used to construct the receipt",
    )
    parser.add_argument("--out", type=Path)
    parser.add_argument(
        "--write",
        action="store_true",
        help="write the authenticated fragment; otherwise only validate/build it",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    paper_dir = root / "papers" / args.paper
    try:
        if not paper_dir.is_dir():
            raise SourceRecordCurrentSemanticParentFragmentError(
                f"paper directory does not exist: {paper_dir}"
            )
        canonical_raw = paper_dir / "audit" / "source_record_audit.json"
        raw_path = (args.raw_audit or canonical_raw).resolve()
        if raw_path != canonical_raw.resolve():
            raise SourceRecordCurrentSemanticParentFragmentError(
                "semantic-parent fragment only accepts the canonical current raw audit"
            )
        raw_audit, _ = _read_json_object(raw_path)
        if args.write_template is not None:
            if args.reviews is not None or args.out is not None or args.write:
                raise SourceRecordCurrentSemanticParentFragmentError(
                    "--write-template cannot be combined with receipt construction options"
                )
            template, error = semantic_parent_review_fragment_template(
                raw_audit, paper=args.paper
            )
            if error or template is None:
                raise SourceRecordCurrentSemanticParentFragmentError(
                    error or "could not construct review template"
                )
            output_path = args.write_template.resolve()
            _paper_relative_path(output_path, paper_dir)
            _atomic_write(
                output_path,
                json.dumps(template, indent=2, sort_keys=True).encode("utf-8") + b"\n",
            )
            print(
                f"{args.paper}: wrote non-evidence semantic-parent review template to "
                f"{output_path} ({len(template['semantic_parent_reviews'])} parents)"
            )
            return 0
        if args.reviews is None:
            raise SourceRecordCurrentSemanticParentFragmentError(
                "receipt construction requires --reviews"
            )
        review_path = args.reviews.resolve()
        _paper_relative_path(review_path, paper_dir)
        review_fragment, _ = _read_json_object(review_path)
        artifact, error = build_current_semantic_parent_fragment_from_review_fragment(
            paper=args.paper,
            raw_audit=raw_audit,
            review_fragment=review_fragment,
        )
        if error or artifact is None:
            raise SourceRecordCurrentSemanticParentFragmentError(
                error or "could not build semantic-parent fragment"
            )
        output_path = (
            args.out or current_semantic_parent_fragment_artifact_path(paper_dir)
        ).resolve()
        _paper_relative_path(output_path, paper_dir)
        validated, validation_error = _artifact_error(
            artifact, paper=args.paper, raw_audit=raw_audit
        )
        if validation_error or validated is None:
            raise SourceRecordCurrentSemanticParentFragmentError(
                "internal fragment validation failed: "
                + (validation_error or "unknown error")
            )
    except (OSError, SourceRecordCurrentSemanticParentFragmentError) as exc:
        print(f"{args.paper}: semantic-parent fragment refused: {exc}", file=sys.stderr)
        return 1
    contents = json.dumps(artifact, indent=2, sort_keys=True).encode("utf-8") + b"\n"
    if args.write:
        _atomic_write(output_path, contents)
        print(
            f"{args.paper}: wrote current semantic-parent fragment to {output_path} "
            f"({len(artifact['semantic_parent_reviews'])} reviewed parents)"
        )
    else:
        print(
            f"{args.paper}: current semantic-parent fragment validates "
            f"({len(artifact['semantic_parent_reviews'])} reviewed parents); rerun with --write"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
