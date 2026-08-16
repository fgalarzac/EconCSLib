#!/usr/bin/env python3
"""Selective, semantic revalidation between two current v10 raw audits.

An aggregate source-record receipt changes whenever any reviewed Lean/source
surface changes.  That is correct for the raw audit, but it must not erase a
human judgment about an unrelated generated obligation.  This module records a
strict differential overlay:

* a prior v10 raw receipt and its current judgment sidecar are archived;
* every prior/current generated judgment group is compared through a complete
  semantic descriptor with narrowly normalized presentation fields; and
* only unique, descriptor-identical groups are made current through the
  loader-authenticated overlay.  Everything else remains absent and therefore
  requires a fresh manual response in the ordinary sidecar.

The matching relation deliberately does not use a source-map key, declaration
name, binder name, or sidecar storage key.  Keys are retained only to locate a
saved response and to expose the uniquely matched current generated group.
Input/field judgments use their local source antecedent and structural surface;
they do not become stale merely because an enclosing theorem result changes.
Semantic-model judgments, which audit the advertised result itself, retain the
full expanded result surface and consequently require review after that change.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
import sys
from pathlib import Path, PurePosixPath
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:  # Supports direct execution and package imports in focused tests.
    from scripts.source_record_integrity import (
        SOURCE_RECORD_REUSABLE_ITEM_SECTIONS,
        canonical_digest_payload,
        source_record_audit_receipt_error,
        source_record_item_is_nonreusable_theorem_facing_mirror,
        source_record_raw_reusable_item_metadata_error,
        source_record_target_route_error,
    )
    from scripts.source_record_archived_source_status_projection_bridge import (
        ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_INTEGRITY_FIELD,
        ValidatedArchivedSourceStatusProjectionBridge,
        archived_source_status_association_is_rebound,
        load_archived_source_status_projection_bridge_context,
        normalized_archived_source_status_association,
        rebound_archived_source_status_response,
    )
    from scripts.source_record_target_disposition import (
        INPUT_SOURCE_CREDIT_CLASSIFICATIONS,
        STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ORIGIN,
        STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ROLE,
        STATEMENT_SOURCE_REVIEW_ASSOCIATION_ORIGIN,
        STATEMENT_SOURCE_REVIEW_ASSOCIATION_ROLE,
        SOURCE_TARGET_DISPOSITIONS,
        SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME,
        ValidatedAdministrativeProjectionRebind,
        administrative_projection_rebound_association,
        administrative_projection_rebound_response,
        load_administrative_projection_rebind_context,
        recursive_field_parent_route_record_digest,
        semantic_association_record_digest,
        statement_source_component_effective_semantic_pin,
        statement_source_review_effective_semantic_pin,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
    from source_record_integrity import (
        SOURCE_RECORD_REUSABLE_ITEM_SECTIONS,
        canonical_digest_payload,
        source_record_audit_receipt_error,
        source_record_item_is_nonreusable_theorem_facing_mirror,
        source_record_raw_reusable_item_metadata_error,
        source_record_target_route_error,
    )
    from source_record_archived_source_status_projection_bridge import (
        ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_INTEGRITY_FIELD,
        ValidatedArchivedSourceStatusProjectionBridge,
        archived_source_status_association_is_rebound,
        load_archived_source_status_projection_bridge_context,
        normalized_archived_source_status_association,
        rebound_archived_source_status_response,
    )
    from source_record_target_disposition import (
        INPUT_SOURCE_CREDIT_CLASSIFICATIONS,
        STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ORIGIN,
        STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ROLE,
        STATEMENT_SOURCE_REVIEW_ASSOCIATION_ORIGIN,
        STATEMENT_SOURCE_REVIEW_ASSOCIATION_ROLE,
        SOURCE_TARGET_DISPOSITIONS,
        SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME,
        ValidatedAdministrativeProjectionRebind,
        administrative_projection_rebound_association,
        administrative_projection_rebound_response,
        load_administrative_projection_rebind_context,
        recursive_field_parent_route_record_digest,
        semantic_association_record_digest,
        statement_source_component_effective_semantic_pin,
        statement_source_review_effective_semantic_pin,
    )


SOURCE_RECORD_V10_PROMPT_VERSION = (
    "source-record-v10-semantic-conclusion-boundary-contract"
)


def _current_revalidation_module() -> Any:
    """Load the optional current-revalidation validator only when needed.

    Evidence integrity loads the differential overlay during module import,
    while the current-revalidation tool imports that evidence gate to validate
    its source anchors.  Importing both eagerly makes correctness depend on
    Python's module import order.  The complete-reissue path is the only
    consumer of the current-revalidation validator, so defer that dependency
    until a caller actually requests a complete reissue.
    """

    try:
        from scripts import source_record_current_revalidation as current
    except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
        import source_record_current_revalidation as current
    return current


SOURCE_RECORD_ITEM_DIGEST_SCHEMA = 5
SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_SCHEMA = 1
SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_POLICY_VERSION = (
    "source-record-v10-differential-semantic-overlay-v2"
)
PRESENTATION_NORMALIZER_SCHEMA = 1
SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_FILENAME = (
    "source_record_differential_revalidation.json"
)
SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ARTIFACT_KIND = (
    "source_record_v10_differential_revalidation"
)
SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_INTEGRITY_FIELD = (
    "source_record_differential_revalidation_sha256"
)
SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD = (
    "source_record_differential_revalidation"
)
SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_HISTORY_FIELD = (
    "prior_source_record_differential_revalidations"
)
SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_FIELD = (
    "complete_reusable_section_identity"
)
SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_SCHEMA = 1
SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_MODE = (
    "all_reusable_sections_and_semantic_descriptors_exact"
)
SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_FIELD = (
    "complete_reissue_raw_group_identity"
)
SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_SCHEMA = 1
SOURCE_RECORD_COMPLETE_REISSUE_CURRENT_REVALIDATION_FIELD = (
    "prior_attested_current_revalidation"
)
SOURCE_RECORD_COMPLETE_REISSUE_CURRENT_REVALIDATION_SCHEMA = 1
SOURCE_RECORD_COMPLETE_REISSUE_AGGREGATE_DELTA_SCHEMA = 1
SOURCE_RECORD_COMPLETE_REISSUE_AGGREGATE_DELTA_POLICY = (
    "only-generated-receipt-fields-and-replicated-selected-semantic-projection-v1"
)
# A receipt reissue may regenerate its own aggregate receipts.  The only
# non-generated field allowed to differ is the selected semantic-projection
# receipt emitted by the aggregate-only receipt reprojector.  It occurs once
# in the raw payload and twice in independently checked projections.  Keep the
# paths explicit: an unknown aggregate/provenance delta must force a review.
_COMPLETE_REISSUE_GENERATED_RECEIPT_PATHS = (
    ("source_record_audit_sha256",),
    ("source_record_audit_integrity_sha256",),
)
_COMPLETE_REISSUE_SELECTED_PROJECTION_PATHS = (
    (
        "source_record_receipt_reprojection",
        "paper_statement_map_exact_default_mode_delta",
        "selected_semantic_projection_sha256",
    ),
    (
        "source_record_audit_surface",
        "source_record_receipt_reprojection",
        "paper_statement_map_exact_default_mode_delta",
        "selected_semantic_projection_sha256",
    ),
    (
        "source_record_audit_surface",
        "raw_evidence_projection",
        "source_record_receipt_reprojection",
        "paper_statement_map_exact_default_mode_delta",
        "selected_semantic_projection_sha256",
    ),
)
SEMANTIC_ASSOCIATION_REBIND_FIELD = "semantic_association_rebind"
SEMANTIC_ASSOCIATION_REBIND_SCHEMA = 1
ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FIELD = (
    "archived_source_status_projection_bridge"
)
ARCHIVED_SOURCE_STATUS_PROJECTION_NORMALIZED_DESCRIPTOR_FIELD = (
    "archived_source_status_projection_normalized_prior_group_semantic_descriptor"
)
ARCHIVED_SOURCE_STATUS_PROJECTION_NORMALIZED_DESCRIPTOR_SHA256_FIELD = (
    "archived_source_status_projection_normalized_prior_group_semantic_descriptor_sha256"
)
SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_FIELD = (
    "source_free_recursive_structural_identity"
)
SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_SCHEMA = 1
SOURCE_FREE_RECURSIVE_CONTENT_IDENTITY_SCHEMA = 1
SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_SCHEMA = 1
SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_POLICY_VERSION = (
    "source-record-v10-differential-semantic-descriptor-reuse-exclusions-v1"
)
SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_ARTIFACT_KIND = (
    "source_record_v10_differential_semantic_descriptor_reuse_exclusions"
)
SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_FIELD = (
    "semantic_descriptor_reuse_exclusions"
)
SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_REASONS_FIELD = (
    "excluded_current_group_semantic_descriptor_reasons"
)

# A differential overlay can itself be historical evidence for a selected
# current review or a replayed selected-plus-overlay composition.  Replacing
# a byte-pinned overlay silently makes that evidence unreplayable.  Keep this
# guard at the write boundary rather than broadening raw-audit freshness: it
# protects provenance without changing the audit surface or reuse semantics.
_DIFFERENTIAL_OVERLAY_PIN_MARKERS = (
    b'"differential_overlay_path"',
    b'"differential_overlay"',
)

_SHA256_RE = re.compile(r"^[0-9a-fA-F]{64}$")
_LOADED_OVERLAY_ITEM_SENTINEL = object()

# Recursive raw fields can be exact semantic matches even when they are only
# data, a derived component, or an unresolved boundary.  Those responses do
# not assert source credit and so do not need a separate source-parent route
# merely to retain their exact reviewed disposition.  This is deliberately an
# allowlist: a new response classification is source-credit-sensitive until
# the audit policy explicitly says otherwise.
_NON_SOURCE_CREDIT_RECURSIVE_CLASSIFICATIONS = frozenset(
    {
        "approved_external_boundary",
        "container_recursively_audited",
        "derived_consequence_record",
        "derived_from_visible_boundary",
        "nonpropositional_witness_data",
        "proved_from_primitives",
        "unresolved_assumed_math",
        "visible_boundary_component",
    }
)
# A classification is not the only way a response can claim source credit.
# Keep the content-bearing response fields explicit; arbitrary new fields
# remain fail-closed through the classification allowlist above rather than
# being inferred from a source-looking spelling or a function name.
_RECURSIVE_SOURCE_CREDIT_RESPONSE_FIELDS = frozenset(
    {
        "corrected_target_sha256_by_source_item",
        "corrected_target_sha256_by_source_semantic_sha256",
        "governing_source_defect_ids",
        "model_convention_ids",
        "model_convention_sha256_by_id",
        "source_target_disposition",
        "source_target_disposition_sha256",
        "source_target_match_verdict",
    }
)
# These are the generated response credentials that can bind a human response
# to a source association even when its classification spelling has not yet
# been added to the source-credit classification set.  A bare ``source_location``
# on a non-source-credit recursive response is deliberately *not* listed: it is
# a human-facing audit annotation and cannot discharge a theorem premise (the
# shared target-disposition validator only treats it as source credit together
# with a source-credit classification/association).  The fields below instead
# carry a machine-checkable source/map/convention/corrected-target claim.
_RECURSIVE_SOURCE_CREDIT_PIN_FIELDS = frozenset(
    {
        "semantic_association_sha256",
        "source_contract_association_sha256",
        "source_map_item_sha256_by_key",
        "source_map_item_keys_sha256",
        "source_target_disposition",
        "source_target_disposition_sha256",
        "source_target_match_verdict",
        "model_convention_ids",
        "model_convention_sha256_by_id",
        "governing_defect_ids",
        "governing_source_defect_ids",
        "corrected_target_sha256_by_source_item",
        "corrected_target_sha256_by_source_semantic_sha256",
        "source_item_semantic_sha256",
        "source_item_semantic_sha256_by_key",
        "source_key",
        "paper_statement_key",
    }
)


class SourceRecordDifferentialRevalidationError(ValueError):
    """Raised when a proposed v10 differential overlay is inadmissible."""


class _LoadedSourceRecordDifferentialRevalidationItem(dict[str, Any]):
    """A JSON-invisible token proving that this item passed the loader."""

    __slots__ = ("_source_record_differential_revalidation_loader_token",)

    def __init__(self, value: Mapping[str, Any]) -> None:
        super().__init__(value)
        self._source_record_differential_revalidation_loader_token = (
            _LOADED_OVERLAY_ITEM_SENTINEL
        )


# Navigation strings may help a person find the generated item, but must never
# make two obligations appear equal.  Keep unknown future fields by default so
# an audit-engine extension causes re-review until it is consciously classified.
_NAVIGATION_FIELDS = frozenset(
    {
        "row",
        "judgment_key",
        "binder",
        "reviewed_binder",
        "lean_source_declaration",
        "effective_lean_source_declaration",
        "qualified_declaration",
        "effective_qualified_declaration",
        "reviewed_declaration_identity",
        "reviewed_elaborated_signature_identities",
        "reviewed_elaborated_signature_identity",
        "paper_statement_map_sha256",
        "source_contract_association",
        "semantic_contract_source_association",
        "source_statement_association",
        "statement_source_component_association",
        "semantic_contract_group",
        "recursive_field_explicit_parent_route",
        "source_file",
        "source_location",
        "source_key",
        "source_kind",
        "source_map_item_sha256",
        "source_map_item_keys",
        "source_map_item_keys_sha256",
        "source_map_item_sha256_by_key",
        "association_sha256",
        "paired_qualified_declaration",
        "declaration",
        "local_type_head",
        "record",
        "record_aliases",
        "structure",
        "field",
        "path",
        "line",
        "names",
        "required_check",
        "semantic_context_requirements_sha256",
    }
)
_RECEIPT_ONLY_FIELDS = frozenset(
    {
        "source_record_item_reuse_eligibility",
        "source_record_item_digest_schema",
        "source_record_item_semantic_id",
        "source_record_item_context_sha256",
        "source_record_item_sha256",
        "source_record_item_semantic_context_requirements_sha256",
        "source_record_item_source_proof_fidelity_records_sha256",
    }
)
# A source-free recursive fallback may pair only the complete non-presentation
# content of a generated group. The sidecar key, record/field spelling, source
# file location, and receipt bookkeeping are navigation rather than a semantic
# matching relation. A separate full raw-group witness is still retained below
# and must remain exact once this content identity finds a unique candidate.
_SOURCE_FREE_RECURSIVE_CONTENT_OMITTED_FIELDS = (
    _NAVIGATION_FIELDS
    | _RECEIPT_ONLY_FIELDS
    | frozenset({"risk_terms"})
)
_ASSOCIATION_FIELDS = (
    "source_contract_association",
    "semantic_contract_source_association",
    "source_statement_association",
    "statement_source_component_association",
    "semantic_contract_group",
)
_ASSOCIATION_NAME_FIELDS = frozenset(
    {
        "qualified_declaration",
        "paired_qualified_declaration",
        "semantic_model_judgment_key",
        "evidence_declaration",
        "spec_declaration",
        "row",
        "source_key",
        "source_location",
        "source_kind",
        "source_map_item_sha256",
        "source_map_item_keys",
        "source_map_item_keys_sha256",
        "source_map_item_sha256_by_key",
        "association_sha256",
        "reviewed_declaration_identity",
        "reviewed_elaborated_signature_identity",
        "reviewed_elaborated_signature_identities",
    }
)


def _canonical_digest(payload: object) -> str:
    encoded = json.dumps(
        canonical_digest_payload(payload), sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _stable_provenance_path(path: Path) -> str:
    """Return the unique checkout-stable locator for repository evidence."""

    resolved = path.resolve()
    try:
        return resolved.relative_to(ROOT.resolve()).as_posix()
    except ValueError:
        raise SourceRecordDifferentialRevalidationError(
            f"source-record differential evidence must be inside the repository: {path}"
        )


def _repository_provenance_path(value: object) -> Path:
    """Resolve one serialized provenance locator without accepting aliases."""

    text = str(value or "").strip()
    if not text or text == ".":
        raise SourceRecordDifferentialRevalidationError(
            "source-record differential provenance has no path"
        )
    pure = PurePosixPath(text)
    if pure.is_absolute() or any(part in {"", ".", ".."} for part in pure.parts):
        raise SourceRecordDifferentialRevalidationError(
            "source-record differential provenance path is not normalized relative to the repository"
        )
    path = (ROOT / Path(*pure.parts)).resolve()
    try:
        normalized = path.relative_to(ROOT.resolve()).as_posix()
    except ValueError as exc:
        raise SourceRecordDifferentialRevalidationError(
            "source-record differential provenance escapes the repository"
        ) from exc
    if normalized != text:
        raise SourceRecordDifferentialRevalidationError(
            "source-record differential provenance path is not canonical"
        )
    return path


def _sha256(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if _SHA256_RE.fullmatch(text) else ""


def _reuse_exclusion_reason_ledger(
    value: object, *, label: str
) -> dict[str, str]:
    """Validate a descriptor-only reviewer exclusion ledger.

    This deliberately accepts neither generated judgment keys nor any Lean
    naming surface.  A digest identifies a complete current semantic group;
    its reason only explains why that otherwise reusable group must receive a
    fresh current review.
    """

    if not isinstance(value, Mapping):
        raise SourceRecordDifferentialRevalidationError(
            f"{label} must map semantic descriptor SHA-256 values to reasons"
        )
    reasons: dict[str, str] = {}
    for raw_digest, raw_reason in value.items():
        digest = _sha256(raw_digest)
        reason = raw_reason.strip() if isinstance(raw_reason, str) else ""
        if not digest or not reason or digest in reasons:
            raise SourceRecordDifferentialRevalidationError(
                f"{label} has an invalid, duplicate, or undocumented descriptor exclusion"
            )
        reasons[digest] = reason
    if not reasons:
        raise SourceRecordDifferentialRevalidationError(
            f"{label} has no descriptor exclusions"
        )
    return reasons


def _reuse_exclusions_artifact_error(
    payload: object,
    *,
    paper: str,
    current_raw_audit: Mapping[str, Any] | None = None,
) -> str:
    """Return whether a reviewer exclusion artifact is admissible.

    The artifact is intentionally small and fail-closed.  It has exactly one
    selector surface: a current semantic-descriptor SHA-256.  Binding it to
    the current raw receipts prevents an old exclusion decision from silently
    narrowing a later differential overlay.
    """

    if not isinstance(payload, Mapping):
        return "reuse-exclusions artifact is not an object"
    expected_fields = {
        "schema",
        "artifact_kind",
        "policy_version",
        "paper",
        "current_source_record_audit_sha256",
        "current_source_record_audit_integrity_sha256",
        SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_REASONS_FIELD,
    }
    unexpected = sorted(str(key) for key in payload if str(key) not in expected_fields)
    if unexpected:
        return "reuse-exclusions artifact has unsupported fields: " + ", ".join(
            unexpected[:5]
        )
    if payload.get("schema") != SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_SCHEMA:
        return "reuse-exclusions artifact has an unsupported schema"
    if (
        str(payload.get("artifact_kind") or "").strip()
        != SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_ARTIFACT_KIND
    ):
        return "reuse-exclusions artifact has the wrong artifact kind"
    if (
        str(payload.get("policy_version") or "").strip()
        != SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_POLICY_VERSION
    ):
        return "reuse-exclusions artifact has an unsupported policy"
    if payload.get("paper") != paper:
        return "reuse-exclusions artifact belongs to another paper"
    if not _sha256(payload.get("current_source_record_audit_sha256")):
        return "reuse-exclusions artifact lacks a current raw aggregate receipt"
    if not _sha256(payload.get("current_source_record_audit_integrity_sha256")):
        return "reuse-exclusions artifact lacks a current raw integrity receipt"
    try:
        _reuse_exclusion_reason_ledger(
            payload.get(SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_REASONS_FIELD),
            label="reuse-exclusions artifact",
        )
    except SourceRecordDifferentialRevalidationError as exc:
        return str(exc)
    if current_raw_audit is not None:
        if _sha256(payload.get("current_source_record_audit_sha256")) != _sha256(
            current_raw_audit.get("source_record_audit_sha256")
        ):
            return "reuse-exclusions artifact is not bound to the current raw aggregate receipt"
        if _sha256(payload.get("current_source_record_audit_integrity_sha256")) != _sha256(
            current_raw_audit.get("source_record_audit_integrity_sha256")
        ):
            return "reuse-exclusions artifact is not bound to the current raw integrity receipt"
    return ""


def _reuse_exclusions_record(
    payload: Mapping[str, Any], path: Path
) -> dict[str, Any]:
    """Serialize exact artifact provenance into the overlay receipt."""

    reasons = _reuse_exclusion_reason_ledger(
        payload.get(SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_REASONS_FIELD),
        label="reuse-exclusions artifact",
    )
    return {
        "path": _stable_provenance_path(path),
        "file_sha256": _file_sha256(path),
        "schema": SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_SCHEMA,
        "artifact_kind": SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_ARTIFACT_KIND,
        "policy_version": SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_POLICY_VERSION,
        "paper": str(payload.get("paper") or ""),
        "current_source_record_audit_sha256": _sha256(
            payload.get("current_source_record_audit_sha256")
        ),
        "current_source_record_audit_integrity_sha256": _sha256(
            payload.get("current_source_record_audit_integrity_sha256")
        ),
        SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_REASONS_FIELD: {
            digest: reasons[digest] for digest in sorted(reasons)
        },
    }


def _reuse_exclusions_record_error(
    value: object,
    *,
    paper: str,
    current_raw_audit: Mapping[str, Any] | None = None,
) -> str:
    """Reauthenticate a serialized descriptor-only exclusion record."""

    if not isinstance(value, Mapping):
        return "overlay reuse-exclusions provenance is not an object"
    expected_fields = {
        "path",
        "file_sha256",
        "schema",
        "artifact_kind",
        "policy_version",
        "paper",
        "current_source_record_audit_sha256",
        "current_source_record_audit_integrity_sha256",
        SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_REASONS_FIELD,
    }
    if set(value) != expected_fields:
        return "overlay reuse-exclusions provenance has an unsupported shape"
    try:
        artifact_path = _repository_provenance_path(value.get("path"))
        artifact = _read_json_object(artifact_path)
    except (OSError, SourceRecordDifferentialRevalidationError) as exc:
        return "could not read reuse-exclusions artifact: " + str(exc)
    if _file_sha256(artifact_path) != str(value.get("file_sha256") or ""):
        return "reuse-exclusions artifact bytes differ from the overlay receipt"
    if error := _reuse_exclusions_artifact_error(
        artifact, paper=paper, current_raw_audit=current_raw_audit
    ):
        return error
    expected = _reuse_exclusions_record(artifact, artifact_path)
    if canonical_digest_payload(value) != canonical_digest_payload(expected):
        return "reuse-exclusions artifact content differs from the overlay receipt"
    return ""


def _reuse_exclusions_current_group_error(
    reasons: Mapping[str, str],
    descriptor_index: Mapping[str, list[tuple[str, Mapping[str, object]]]],
) -> str:
    """Ensure each descriptor-only exclusion resolves to one current group."""

    for digest in reasons:
        if len(descriptor_index.get(digest, [])) != 1:
            return (
                "reuse-exclusions descriptor does not identify exactly one "
                "current semantic group"
            )
    return ""


def _read_json_object(path: Path) -> dict[str, Any]:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise SourceRecordDifferentialRevalidationError(
            f"could not read JSON object at {path}: {exc}"
        ) from exc
    if not isinstance(payload, dict):
        raise SourceRecordDifferentialRevalidationError(f"{path} is not a JSON object")
    return payload


def _paper_relative_overlay_reference_path(
    value: object, *, paper_dir: Path
) -> Path | None:
    """Resolve one normalized paper-local provenance path, if admissible."""

    text = value.strip() if isinstance(value, str) else ""
    pure = PurePosixPath(text)
    if (
        not text
        or pure.is_absolute()
        or any(part in {"", ".", ".."} for part in pure.parts)
    ):
        return None
    try:
        candidate = (paper_dir / Path(*pure.parts)).resolve()
        candidate.relative_to(paper_dir.resolve())
        return candidate
    except (OSError, RuntimeError, ValueError):
        return None


def _paper_local_display_path(path: Path, *, paper_dir: Path) -> str:
    """Return a stable diagnostic locator without assuming the CLI root."""

    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError):
        return str(path)


def _file_might_contain_differential_overlay_pin(path: Path) -> bool:
    """Avoid parsing ordinary large raw receipts during the write guard."""

    largest_marker = max(len(marker) for marker in _DIFFERENTIAL_OVERLAY_PIN_MARKERS)
    trailing = b""
    try:
        with path.open("rb") as handle:
            while chunk := handle.read(64 * 1024):
                searchable = trailing + chunk
                if any(marker in searchable for marker in _DIFFERENTIAL_OVERLAY_PIN_MARKERS):
                    return True
                trailing = searchable[-(largest_marker - 1) :]
    except OSError:
        return False
    return False


def _differential_overlay_pin_records(
    value: object,
    *,
    paper_dir: Path,
    json_path: str = "$",
) -> list[dict[str, str]]:
    """Find structural overlay byte pins without using artifact filenames.

    A selected/current receipt carries a logical ``differential_overlay_path``
    and its byte hash.  A historical composition carries a physical
    ``differential_overlay`` snapshot record.  These are provenance shapes,
    not theorem or declaration names.  Unknown JSON is otherwise ignored: a
    record becomes a blocker only after its path resolves to the target and
    its expected hash equals the target's live bytes.
    """

    records: list[dict[str, str]] = []
    if isinstance(value, Mapping):
        # Evidence can retain draft/template fragments inside an otherwise live
        # wrapper. A marked fragment is not provenance merely because it has a
        # structurally similar pin shape.
        if _payload_is_non_evidence(value):
            return records
        logical_path = _paper_relative_overlay_reference_path(
            value.get("differential_overlay_path"), paper_dir=paper_dir
        )
        logical_sha = _sha256(value.get("differential_overlay_sha256"))
        if logical_path is not None and logical_sha:
            records.append(
                {
                    "kind": "selected_or_composed_overlay",
                    "json_path": json_path + ".differential_overlay_path",
                    "path": str(logical_path),
                    "expected_sha256": logical_sha,
                }
            )

        physical = value.get("differential_overlay")
        if isinstance(physical, Mapping):
            physical_path = _paper_relative_overlay_reference_path(
                physical.get("path"), paper_dir=paper_dir
            )
            physical_sha = _sha256(physical.get("file_sha256"))
            if physical_path is not None and physical_sha:
                records.append(
                    {
                        "kind": "historical_composition_overlay",
                        "json_path": json_path + ".differential_overlay",
                        "path": str(physical_path),
                        "expected_sha256": physical_sha,
                    }
                )

        for raw_key, child in value.items():
            key = str(raw_key)
            records.extend(
                _differential_overlay_pin_records(
                    child,
                    paper_dir=paper_dir,
                    json_path=json_path + "." + key,
                )
            )
    elif isinstance(value, list):
        for index, child in enumerate(value):
            records.extend(
                _differential_overlay_pin_records(
                    child,
                    paper_dir=paper_dir,
                    json_path=f"{json_path}[{index}]",
                )
            )
    return records


def source_record_differential_write_pins(
    *, paper_dir: Path, output_path: Path, proposed_bytes: bytes
) -> list[dict[str, str]]:
    """Return live evidence records that would be invalidated by this write.

    The result is empty for a byte-identical rewrite, a new output file, stale
    references, or an unreferenced exploratory path.  This deliberately scans
    all paper-local JSON provenance rather than a hard-coded sidecar filename,
    so archived selected and historical-composition evidence receive the same
    protection as the current sidecar.
    """

    target = output_path.resolve()
    if not target.is_file():
        return []
    existing_sha = _file_sha256(target)
    proposed_sha = hashlib.sha256(proposed_bytes).hexdigest()
    if existing_sha == proposed_sha:
        return []

    audit_dir = paper_dir / "audit"
    if not audit_dir.is_dir():
        return []
    records: list[dict[str, str]] = []
    for path in sorted(audit_dir.rglob("*.json")):
        try:
            resolved = path.resolve()
        except OSError:
            continue
        if resolved == target or not _file_might_contain_differential_overlay_pin(path):
            continue
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError, json.JSONDecodeError):
            continue
        # A draft may intentionally retain a provenance-shaped fragment while
        # being explicitly marked unusable as evidence.  Such a file must not
        # become an ambient write blocker merely because it sits under audit/.
        # `_payload_is_non_evidence` is content-based and is also rejected by
        # every evidence consumer; do not infer this from a filename.
        if isinstance(payload, Mapping) and _payload_is_non_evidence(payload):
            continue
        for record in _differential_overlay_pin_records(
            payload, paper_dir=paper_dir.resolve()
        ):
            if (
                Path(record["path"]).resolve() == target
                and record["expected_sha256"] == existing_sha
            ):
                records.append(
                    {
                        **record,
                        "evidence_path": _paper_local_display_path(
                            path, paper_dir=paper_dir
                        ),
                    }
                )
    records.sort(
        key=lambda record: (
            record["evidence_path"],
            record["json_path"],
            record["kind"],
        )
    )
    return records


def _byte_pinned_overlay_write_error(records: list[Mapping[str, str]]) -> str:
    """Explain a blocked overwrite without exposing unbounded provenance."""

    locations = [
        f"{record.get('evidence_path', '<unknown>')}:{record.get('json_path', '$')}"
        for record in records[:3]
    ]
    suffix = "; ".join(locations)
    if len(records) > len(locations):
        suffix += f"; and {len(records) - len(locations)} more"
    return (
        "refusing to overwrite a differential overlay whose current bytes are "
        f"pinned by {len(records)} selected/current or historical-composition "
        f"evidence record(s) ({suffix}). Write an exploratory result to a "
        "different --out path, or pass --replace-byte-pinned-overlay only after "
        "deliberately relocating or reissuing the dependent evidence."
    )


def _exact_json_file_payload_error(
    path: Path, payload: Mapping[str, Any], *, label: str
) -> str:
    """Reject an in-memory candidate that differs from named evidence bytes."""

    try:
        saved = _read_json_object(path)
    except SourceRecordDifferentialRevalidationError as exc:
        return f"{label} cannot be loaded from its evidence path: {exc}"
    if canonical_digest_payload(saved) != canonical_digest_payload(payload):
        return f"{label} differs from its named evidence file bytes"
    return ""


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


def _effective(value: Mapping[str, Any], payload: Mapping[str, Any], field: str) -> Any:
    return value.get(field) or payload.get(field)


def _raw_audit_error(payload: object, *, paper: str, label: str) -> str:
    if not isinstance(payload, Mapping):
        return f"{label} raw audit is not an object"
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
        return f"{label} raw audit has no aggregate source-record receipt"
    receipt_error = source_record_audit_receipt_error(payload)
    if receipt_error:
        return f"{label} raw audit receipt is invalid: {receipt_error}"
    metadata_error = source_record_raw_reusable_item_metadata_error(
        payload, expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    )
    if metadata_error:
        return f"{label} raw audit item metadata is invalid: {metadata_error}"
    lean_check = payload.get("lean_check")
    if not isinstance(lean_check, Mapping) or lean_check.get("returncode") != 0:
        return f"{label} raw audit lacks a successful Lean check"
    if int(payload.get("recursion_failure_count") or 0) != 0:
        return f"{label} raw audit has recursion failures"
    target_route_error = source_record_target_route_error(payload)
    if target_route_error:
        return f"{label} raw audit has invalid semantic target routing: {target_route_error}"
    return ""


def _canonical_projection_sort_key(value: object) -> str:
    """Return a deterministic order key for a projected unordered inventory."""

    return json.dumps(
        canonical_digest_payload(value), sort_keys=True, separators=(",", ":")
    )


def _complete_review_alias_presentation_projection(
    value: Mapping[str, Any],
    *,
    full_result_surface: bool,
    omit_recursive_structural_coordinates: bool,
) -> object:
    """Project a complete thin-alias trace without its route spellings.

    The generated elaborated-signature and source-association receipts bind the
    actual reviewed endpoint.  Once the alias resolver has completed, the
    declaration/FQN strings, local reference spelling, and source locations
    merely explain how that endpoint was found.  Retain the ordered alias-kind
    trace, because a changed route shape still warrants a fresh review.

    Incomplete or unfamiliar routes deliberately return their raw surface:
    the current generator has no name-free identity for an unresolved target.
    """

    blocked_routes = value.get("blocked_routes")
    steps = value.get("steps")
    if (
        value.get("schema") != 1
        or value.get("complete") is not True
        or not isinstance(blocked_routes, list)
        or blocked_routes
        or not isinstance(steps, list)
        or not all(isinstance(step, Mapping) for step in steps)
    ):
        return dict(value)

    known_route_fields = {
        "schema",
        "reviewed_declaration",
        "effective_declaration",
        "alias_present",
        "complete",
        "effective_kind",
        "steps",
        "blocked_routes",
    }
    known_step_fields = {"from", "reference", "to", "target_kind", "source_file", "line"}
    projected_steps: list[dict[str, object]] = []
    for step in steps:
        assert isinstance(step, Mapping)
        extras = {
            str(key): _semantic_projection(
                raw_value,
                full_result_surface=full_result_surface,
                omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
            )
            for key, raw_value in step.items()
            if str(key) not in known_step_fields
        }
        projected_step: dict[str, object] = {
            "target_kind": step.get("target_kind"),
        }
        if extras:
            # Unknown generator fields are semantic until deliberately
            # classified, so an extension remains fail-closed by default.
            projected_step["unknown_fields"] = extras
        projected_steps.append(projected_step)

    extras = {
        str(key): _semantic_projection(
            raw_value,
            full_result_surface=full_result_surface,
            omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
        )
        for key, raw_value in value.items()
        if str(key) not in known_route_fields
    }
    projected: dict[str, object] = {
        "presentation_normalizer_schema": PRESENTATION_NORMALIZER_SCHEMA,
        "schema": value.get("schema"),
        "alias_present": value.get("alias_present"),
        "complete": value.get("complete"),
        "effective_kind": value.get("effective_kind"),
        "steps": projected_steps,
        "blocked_routes": [],
    }
    if extras:
        projected["unknown_fields"] = extras
    return projected


def _complete_proposition_alias_presentation_projection(
    value: Mapping[str, Any],
    *,
    full_result_surface: bool,
    omit_recursive_structural_coordinates: bool,
) -> object:
    """Project complete transparent proposition-alias steps without FQNs.

    ``expanded_type`` remains the reviewed proposition.  A transparent step's
    declaration/location is explanatory once that expansion is available, but
    its kind and ordered count remain part of the review surface.  Any blocked
    or malformed expansion has no equivalent canonical endpoint artifact, so
    it retains its raw presentation and cannot gain reuse from this helper.
    """

    blocked_routes = value.get("blocked_routes")
    steps = value.get("transparent_steps")
    if (
        not isinstance(blocked_routes, list)
        or blocked_routes
        or not isinstance(steps, list)
        or not all(isinstance(step, Mapping) for step in steps)
        or "expanded_type" not in value
    ):
        return dict(value)

    known_route_fields = {"expanded_type", "transparent_steps", "blocked_routes"}
    known_step_fields = {"declaration", "kind", "source_file", "line"}
    projected_steps: list[dict[str, object]] = []
    for step in steps:
        assert isinstance(step, Mapping)
        extras = {
            str(key): _semantic_projection(
                raw_value,
                full_result_surface=full_result_surface,
                omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
            )
            for key, raw_value in step.items()
            if str(key) not in known_step_fields
        }
        projected_step: dict[str, object] = {"kind": step.get("kind")}
        if extras:
            projected_step["unknown_fields"] = extras
        projected_steps.append(projected_step)

    extras = {
        str(key): _semantic_projection(
            raw_value,
            full_result_surface=full_result_surface,
            omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
        )
        for key, raw_value in value.items()
        if str(key) not in known_route_fields
    }
    projected: dict[str, object] = {
        "presentation_normalizer_schema": PRESENTATION_NORMALIZER_SCHEMA,
        "expanded_type": value.get("expanded_type"),
        "transparent_steps": projected_steps,
        "blocked_routes": [],
    }
    if extras:
        projected["unknown_fields"] = extras
    return projected


def _complete_terminal_dependency_presentation_projection(
    value: Mapping[str, Any],
    *,
    full_result_surface: bool,
    omit_recursive_structural_coordinates: bool,
) -> object:
    """Project a complete transparent term closure without declaration paths.

    A transparent dependency has existing content-bearing artifacts: its body
    digest, typed surfaces, semantic flags/fragments, and relevance status.
    Its declaration name, source location, declaration-text digest, and
    dependency-chain names are presentation/navigation data.  Do not normalize
    incomplete closures or opaque local heads: those lack a canonical local
    identity and must remain fail-closed.
    """

    definitions = value.get("transparent_definitions")
    incomplete_reasons = value.get("incomplete_reasons")
    unexpanded_heads = value.get("unexpanded_local_term_heads")
    if (
        value.get("schema") != 1
        or value.get("scan_complete") is not True
        or not isinstance(definitions, list)
        or not all(isinstance(node, Mapping) for node in definitions)
        or not isinstance(incomplete_reasons, list)
        or incomplete_reasons
        or not isinstance(unexpanded_heads, list)
        or unexpanded_heads
    ):
        return dict(value)

    known_surface_fields = {
        "schema",
        "scan_complete",
        "scan_limits",
        "incomplete_reasons",
        "terminal_result_semantic_construct_flags",
        "terminal_result_semantic_fragments",
        "transparent_definitions",
        "unexpanded_local_term_heads",
        "semantic_construct_flags",
    }
    known_node_fields = {
        "declaration",
        "kind",
        "source_file",
        "line",
        "declaration_sha256",
        "body_sha256",
        "parameter_types",
        "result_type",
        "semantic_construct_flags",
        "semantic_fragments",
        "body_surface_inspectable",
        "direct_local_dependencies",
        "dependency_chain",
        "semantic_relevant",
    }
    projected_definitions: list[dict[str, object]] = []
    for node in definitions:
        assert isinstance(node, Mapping)
        extras = {
            str(key): _semantic_projection(
                raw_value,
                full_result_surface=full_result_surface,
                omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
            )
            for key, raw_value in node.items()
            if str(key) not in known_node_fields
        }
        projected_node: dict[str, object] = {
            "kind": node.get("kind"),
            "body_sha256": node.get("body_sha256"),
            "parameter_types": _semantic_projection(
                node.get("parameter_types"),
                full_result_surface=full_result_surface,
                omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
            ),
            "result_type": _semantic_projection(
                node.get("result_type"),
                full_result_surface=full_result_surface,
                omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
            ),
            "semantic_construct_flags": _semantic_projection(
                node.get("semantic_construct_flags"),
                full_result_surface=full_result_surface,
                omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
            ),
            "semantic_fragments": _semantic_projection(
                node.get("semantic_fragments"),
                full_result_surface=full_result_surface,
                omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
            ),
            "body_surface_inspectable": node.get("body_surface_inspectable"),
            "semantic_relevant": node.get("semantic_relevant"),
        }
        if extras:
            projected_node["unknown_fields"] = extras
        projected_definitions.append(projected_node)
    projected_definitions.sort(key=_canonical_projection_sort_key)

    extras = {
        str(key): _semantic_projection(
            raw_value,
            full_result_surface=full_result_surface,
            omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
        )
        for key, raw_value in value.items()
        if str(key) not in known_surface_fields
    }
    projected: dict[str, object] = {
        "presentation_normalizer_schema": PRESENTATION_NORMALIZER_SCHEMA,
        "schema": value.get("schema"),
        "scan_complete": value.get("scan_complete"),
        "scan_limits": _semantic_projection(
            value.get("scan_limits"),
            full_result_surface=full_result_surface,
            omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
        ),
        "incomplete_reasons": [],
        "terminal_result_semantic_construct_flags": _semantic_projection(
            value.get("terminal_result_semantic_construct_flags"),
            full_result_surface=full_result_surface,
            omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
        ),
        "terminal_result_semantic_fragments": _semantic_projection(
            value.get("terminal_result_semantic_fragments"),
            full_result_surface=full_result_surface,
            omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
        ),
        "transparent_definitions": projected_definitions,
        "unexpanded_local_term_heads": [],
        "semantic_construct_flags": _semantic_projection(
            value.get("semantic_construct_flags"),
            full_result_surface=full_result_surface,
            omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
        ),
    }
    if extras:
        projected["unknown_fields"] = extras
    return projected


def _semantic_projection(
    value: object,
    *,
    full_result_surface: bool,
    omit_recursive_structural_coordinates: bool = False,
    normalize_presentation_routes: bool = False,
) -> object:
    """Project one generated obligation without receipt transport.

    Input/field dispositions need the local type/record/source surface, not an
    enclosing theorem's conclusion.  A semantic-model item is the opposite: it
    is the result-level review lane, so retain its full expanded surface.

    Alias/dependency route strings are normalized only after the caller has an
    independent semantic source or full-result endpoint identity.  Without
    that identity, their display route remains a fail-closed discriminator;
    the current generator has no canonical local binder/field atom to replace
    it.
    """

    if isinstance(value, Mapping):
        projected: dict[str, object] = {}
        for raw_key, raw_value in value.items():
            key = str(raw_key)
            normalized = key.strip().lower()
            if normalized in _NAVIGATION_FIELDS or normalized in _RECEIPT_ONLY_FIELDS:
                continue
            if (
                normalize_presentation_routes
                and normalized == "review_alias_expansion"
                and isinstance(raw_value, Mapping)
            ):
                projected[key] = _complete_review_alias_presentation_projection(
                    raw_value,
                    full_result_surface=full_result_surface,
                    omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
                )
                continue
            if (
                normalize_presentation_routes
                and normalized
                in {
                    "proposition_alias_expansion",
                    "subtype_predicate_proposition_alias_expansion",
                }
                and isinstance(raw_value, Mapping)
            ):
                projected[key] = _complete_proposition_alias_presentation_projection(
                    raw_value,
                    full_result_surface=full_result_surface,
                    omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
                )
                continue
            if (
                normalize_presentation_routes
                and normalized == "terminal_term_dependency_surface"
                and isinstance(raw_value, Mapping)
            ):
                projected[key] = _complete_terminal_dependency_presentation_projection(
                    raw_value,
                    full_result_surface=full_result_surface,
                    omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
                )
                continue
            if omit_recursive_structural_coordinates and normalized == "nested_structures":
                # Recursive field and nested-record spellings are navigation.
                # A generated direct semantic parent receipt is projected
                # separately for the only reusable recursive-field path.
                continue
            if not full_result_surface and normalized in {
                "row_result_type",
                "result_type",
                "result_type_compatibility",
                "reviewed_result_type",
            }:
                continue
            projected[key] = _semantic_projection(
                raw_value,
                full_result_surface=full_result_surface,
                omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
                normalize_presentation_routes=normalize_presentation_routes,
            )
        return projected
    if isinstance(value, list):
        return [
            _semantic_projection(
                item,
                full_result_surface=full_result_surface,
                omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
                normalize_presentation_routes=normalize_presentation_routes,
            )
            for item in value
        ]
    if isinstance(value, tuple):
        return [
            _semantic_projection(
                item,
                full_result_surface=full_result_surface,
                omit_recursive_structural_coordinates=omit_recursive_structural_coordinates,
            )
            for item in value
        ]
    return value


def _association_mappings(item: Mapping[str, Any]) -> list[tuple[str, Mapping[str, Any]]]:
    return [
        (field, association)
        for field in _ASSOCIATION_FIELDS
        if isinstance((association := item.get(field)), Mapping)
    ]


def _source_semantic_identities(item: Mapping[str, Any]) -> list[str]:
    identities: set[str] = set()
    for _field, association in _association_mappings(item):
        raw_identities = association.get("source_item_identities")
        if not isinstance(raw_identities, list):
            continue
        for raw_identity in raw_identities:
            if not isinstance(raw_identity, Mapping):
                continue
            digest = _sha256(raw_identity.get("source_semantic_sha256"))
            if digest:
                identities.add(digest)
    return sorted(identities)


def _association_semantic_digests(item: Mapping[str, Any]) -> list[str]:
    return sorted(
        {
            digest
            for _field, association in _association_mappings(item)
            if (digest := _sha256(association.get("semantic_association_sha256")))
        }
    )


def _association_role_projection(value: object) -> object:
    """Keep source-route roles while dropping route/declaration spelling."""

    if isinstance(value, Mapping):
        projected: dict[str, object] = {}
        for raw_key, raw_value in value.items():
            key = str(raw_key)
            normalized = key.strip().lower()
            if normalized in _ASSOCIATION_NAME_FIELDS:
                continue
            if normalized == "source_item_identities":
                identities: set[str] = set()
                if isinstance(raw_value, list):
                    for identity in raw_value:
                        if isinstance(identity, Mapping):
                            digest = _sha256(identity.get("source_semantic_sha256"))
                            if digest:
                                identities.add(digest)
                projected["source_item_semantic_identities"] = sorted(identities)
                continue
            if normalized == "semantic_association_sha256":
                # The full row descriptor retains this source+endpoint pin.
                # Input-local reuse instead retains source content and the
                # route role independently, so a changed theorem result does
                # not erase an unchanged antecedent review.
                continue
            projected[key] = _association_role_projection(raw_value)
        return projected
    if isinstance(value, list):
        return sorted(
            [_association_role_projection(item) for item in value],
            key=lambda item: json.dumps(item, sort_keys=True, separators=(",", ":")),
        )
    if isinstance(value, tuple):
        return _association_role_projection(list(value))
    return value


def _association_roles(item: Mapping[str, Any]) -> list[dict[str, object]]:
    return sorted(
        [
            {
                "association_field": field,
                "role": _association_role_projection(association),
            }
            for field, association in _association_mappings(item)
        ],
        key=lambda entry: json.dumps(entry, sort_keys=True, separators=(",", ":")),
    )


def _signature_digests(item: Mapping[str, Any]) -> list[str]:
    signatures: list[Mapping[str, Any]] = []
    direct = item.get("reviewed_elaborated_signature_identities")
    if isinstance(direct, list):
        signatures.extend(entry for entry in direct if isinstance(entry, Mapping))
    for _field, association in _association_mappings(item):
        identity = association.get("reviewed_elaborated_signature_identity")
        if isinstance(identity, Mapping):
            signatures.append(identity)
    return sorted(
        {
            digest
            for signature in signatures
            if (digest := _sha256(signature.get("elaborated_signature_sha256")))
        }
    )


def _recursive_field_parent_route_semantic_scope(
    item: Mapping[str, Any],
) -> dict[str, object] | None:
    """Return a name-free direct semantic parent receipt for one field.

    A recursive field cannot receive automatic differential reuse merely
    because its Lean structure, field, or nested-record spelling is stable.
    It needs a generated, locally authenticated direct parent route. This
    projection retains only source semantic identity, source-convention scope,
    semantic classification, and the checked parent association receipt. It
    never uses a record/field chain or declaration/binder spelling to identify
    a match, and performs no global parent lookup.
    """

    route = item.get("recursive_field_explicit_parent_route")
    if not isinstance(route, Mapping):
        return None
    if (
        route.get("schema") != 1
        or str(route.get("inheritance_mode") or "").strip()
        != "explicit_parent_route_and_field_scope"
    ):
        return None
    route_digest = _sha256(route.get("association_sha256"))
    if not route_digest or route_digest != recursive_field_parent_route_record_digest(route):
        return None
    # Require an actual generated route edge, but deliberately do not project
    # the edge's Lean strings into the reusable semantic identity.
    field_chain = route.get("field_chain")
    if not isinstance(field_chain, list) or not field_chain or not all(
        isinstance(link, Mapping) for link in field_chain
    ):
        return None
    field_scope = _sha256(route.get("field_scope_sha256"))
    convention = _sha256(route.get("convention_sha256"))
    if not field_scope or not convention:
        return None
    classifications = route.get("permitted_classifications")
    if not isinstance(classifications, list) or not classifications:
        return None
    classification_values = [
        str(value).strip() for value in classifications if str(value).strip()
    ]
    if (
        len(classification_values) != len(classifications)
        or len(set(classification_values)) != len(classification_values)
    ):
        return None
    identities = route.get("source_item_identities")
    if not isinstance(identities, list) or len(identities) != 1:
        return None
    identity = identities[0]
    if not isinstance(identity, Mapping):
        return None
    source_semantic = _sha256(identity.get("source_semantic_sha256"))
    if not source_semantic:
        return None
    parent_signature = route.get("parent_elaborated_signature_identity")
    parent_association = _sha256(route.get("parent_source_association_sha256"))
    if (
        not isinstance(parent_signature, Mapping)
        or not parent_association
        or parent_association
        != semantic_association_record_digest([source_semantic], parent_signature)
    ):
        return None
    parent_field = str(route.get("parent_association_field") or "").strip()
    parent_role = str(route.get("parent_source_association_role") or "").strip()
    parent_origin = str(route.get("parent_source_association_origin") or "").strip()
    if parent_field == "source_statement_association":
        if (
            parent_role != "direct_source_route"
            or parent_origin != "explicit_source_map_direct_route"
        ):
            return None
    elif parent_field == "semantic_contract_source_association":
        if parent_role not in {"direct_evidence", "transparent_spec"} or parent_origin:
            return None
    else:
        return None
    if not str(route.get("root_input_type_canonical") or "").strip():
        return None
    return {
        "schema": 1,
        "field_scope_sha256": field_scope,
        "source_item_semantic_sha256": source_semantic,
        "convention_sha256": convention,
        "permitted_classifications": sorted(classification_values),
        "parent_association_kind": parent_field,
        "parent_source_association_role": parent_role,
        "parent_source_association_origin": parent_origin,
        "parent_source_association_sha256": parent_association,
    }


_DIRECT_SOURCE_DOMAIN_PARENT_CONTRACT_SCHEMA = 1
_DIRECT_SOURCE_DOMAIN_PARENT_CONTRACTS_FIELD = (
    "recursive_field_direct_source_domain_parent_contracts"
)


def _optional_source_domain_fingerprint(value: object) -> dict[str, str] | None:
    """Return one explicit optional semantic-context/ledger fingerprint.

    A missing scoped context is materially different from a malformed one.  A
    direct source-domain contract may say that no scoped context applies, but
    it must not silently treat an unfamiliar value as absence.
    """

    text = str(value or "").strip().lower()
    if not text:
        return {"state": "absent"}
    if not _SHA256_RE.fullmatch(text):
        return None
    return {"state": "present", "sha256": text}


def _direct_source_domain_record_input_projection(value: object) -> object:
    """Project a parent record input without its human-facing binder spelling.

    The fully-qualified instantiated input type, elaborated binder atom, and
    every unknown generated field remain.  Display binders, source-text
    spellings, and record-root navigation names are deliberately excluded:
    the generated route's canonical instantiated type selects this binding.
    Retaining an unfamiliar future field keeps this route fail-closed by
    default.
    """

    if isinstance(value, Mapping):
        return {
            str(key): _direct_source_domain_record_input_projection(child)
            for key, child in value.items()
            if str(key).strip().lower()
            not in {"binder_names", "source_type_canonical", "record_roots"}
        }
    if isinstance(value, list):
        return [_direct_source_domain_record_input_projection(child) for child in value]
    if isinstance(value, tuple):
        return [_direct_source_domain_record_input_projection(child) for child in value]
    return value


def _recursive_field_direct_source_domain_parent_contract(
    item: Mapping[str, Any],
    *,
    semantic_model_items: object,
) -> dict[str, object] | None:
    """Return a name-independent direct source-domain contract for one field.

    An explicit recursive-field route proves that the field belongs to a
    source-selected model input.  The parent association's elaborated
    signature necessarily changes when a theorem conclusion changes, even
    when the model input and its source domain do not.  For a *child* review,
    compare the complete parent input-domain surface instead: source-map and
    source-content pins, all parent input domains, the exact instantiated
    record input, scoped context/ledger fingerprints, and the declared field
    scope/convention.  The parent semantic-model row still compares its full
    result surface elsewhere, so this never transports a changed direct result
    review.

    This function deliberately requires a unique current semantic-model
    parent selected by the generated association pin.  It does not look up a
    declaration, source-map key, binder, record, or field by spelling.
    """

    scope = _recursive_field_parent_route_semantic_scope(item)
    route = item.get("recursive_field_explicit_parent_route")
    if scope is None or not isinstance(route, Mapping):
        return None
    if not isinstance(semantic_model_items, list):
        return None

    raw_identities = route.get("source_item_identities")
    if not isinstance(raw_identities, list) or len(raw_identities) != 1:
        return None
    raw_identity = raw_identities[0]
    if not isinstance(raw_identity, Mapping):
        return None
    source_map_item_sha = _sha256(raw_identity.get("source_map_item_sha256"))
    source_semantic_sha = _sha256(raw_identity.get("source_semantic_sha256"))
    if not source_map_item_sha or not source_semantic_sha:
        return None

    parent_association_field = str(
        route.get("parent_association_field") or ""
    ).strip()
    parent_association_pin = _sha256(
        route.get("parent_source_association_sha256")
    )
    parent_role = str(route.get("parent_source_association_role") or "").strip()
    parent_origin = str(
        route.get("parent_source_association_origin") or ""
    ).strip()
    root_input_type = " ".join(
        str(route.get("root_input_type_canonical") or "").split()
    )
    if (
        parent_association_field not in _ASSOCIATION_FIELDS
        or not parent_association_pin
        or not parent_role
        or not root_input_type
    ):
        return None

    candidates: list[dict[str, object]] = []
    for parent in semantic_model_items:
        if not isinstance(parent, Mapping):
            continue
        if str(parent.get("kind") or "").strip() != "semantic_model_comparison":
            continue
        association = parent.get(parent_association_field)
        if not isinstance(association, Mapping):
            continue
        if _sha256(association.get("semantic_association_sha256")) != parent_association_pin:
            continue
        if association.get("schema") != 2:
            continue
        if str(association.get("role") or "").strip() != parent_role:
            continue
        if str(association.get("association_origin") or "").strip() != parent_origin:
            continue
        association_identities = association.get("source_item_identities")
        if not isinstance(association_identities, list) or len(association_identities) != 1:
            continue
        association_identity = association_identities[0]
        if not isinstance(association_identity, Mapping):
            continue
        if (
            _sha256(association_identity.get("source_map_item_sha256"))
            != source_map_item_sha
            or _sha256(association_identity.get("source_semantic_sha256"))
            != source_semantic_sha
        ):
            continue
        signature = association.get("reviewed_elaborated_signature_identity")
        if not isinstance(signature, Mapping):
            continue
        if parent_association_pin != semantic_association_record_digest(
            [source_semantic_sha], signature
        ):
            continue

        expanded_surface = parent.get("expanded_lean_surface")
        if not isinstance(expanded_surface, Mapping):
            continue
        binder_domains = expanded_surface.get("binder_domains")
        if (
            not isinstance(binder_domains, list)
            or not binder_domains
            or not all(isinstance(domain, Mapping) for domain in binder_domains)
        ):
            continue
        raw_bindings = parent.get("record_input_bindings")
        if not isinstance(raw_bindings, list):
            continue
        matching_bindings: list[Mapping[str, Any]] = []
        for binding in raw_bindings:
            if not isinstance(binding, Mapping):
                continue
            binding_type = " ".join(
                str(binding.get("fully_qualified_expanded_type_canonical") or "").split()
            )
            if binding_type == root_input_type:
                matching_bindings.append(binding)
        if len(matching_bindings) != 1:
            continue

        context_fingerprint = _optional_source_domain_fingerprint(
            parent.get("source_record_item_semantic_context_requirements_sha256")
        )
        ledger_fingerprint = _optional_source_domain_fingerprint(
            parent.get("source_record_item_source_proof_fidelity_records_sha256")
        )
        if context_fingerprint is None or ledger_fingerprint is None:
            continue
        candidates.append(
            {
                "schema": _DIRECT_SOURCE_DOMAIN_PARENT_CONTRACT_SCHEMA,
                "source_item_anchor_pins": [
                    {
                        "source_map_item_sha256": source_map_item_sha,
                        "source_semantic_sha256": source_semantic_sha,
                    }
                ],
                "parent_source_association": {
                    "field": parent_association_field,
                    "role": parent_role,
                    "origin": parent_origin,
                },
                # This is the entire proposition-input domain, deliberately
                # excluding the result surface.  It changes for a changed
                # hypothesis but not for a conclusion-only repair.
                "parent_input_domains": _semantic_projection(
                    binder_domains, full_result_surface=False
                ),
                "parent_record_input": _direct_source_domain_record_input_projection(
                    matching_bindings[0]
                ),
                "parent_semantic_context_requirements": context_fingerprint,
                "parent_source_proof_fidelity_records": ledger_fingerprint,
                "field_scope_sha256": scope["field_scope_sha256"],
                "convention_sha256": scope["convention_sha256"],
                "permitted_classifications": scope["permitted_classifications"],
            }
        )

    # Two candidates may be textually identical, but their coexistence still
    # means the raw semantic parent is not uniquely established.
    return candidates[0] if len(candidates) == 1 else None


def _recursive_field_direct_source_domain_parent_contracts(
    payload: Mapping[str, Any],
) -> dict[int, dict[str, object]]:
    """Index only uniquely authenticated direct parent contracts by raw item.

    The object identity is local in-memory bookkeeping, never a serialized or
    semantic selector.  The resulting contract itself is fully name-free and
    becomes part of the generated group descriptor below.
    """

    raw_fields = payload.get("recursive_field_items")
    semantic_model_items = payload.get("semantic_model_items")
    if not isinstance(raw_fields, list) or not isinstance(semantic_model_items, list):
        return {}
    contracts: dict[int, dict[str, object]] = {}
    for item in raw_fields:
        if not isinstance(item, Mapping):
            continue
        contract = _recursive_field_direct_source_domain_parent_contract(
            item, semantic_model_items=semantic_model_items
        )
        if contract is not None:
            contracts[id(item)] = contract
    return contracts


def source_record_differential_item_descriptor(
    item: Mapping[str, Any],
    *,
    section: str,
    recursive_field_direct_source_domain_parent_contract: Mapping[str, object]
    | None = None,
) -> dict[str, object]:
    """Return the semantic comparison descriptor for one generated item.

    This is intentionally public for focused regression tests and audit tools.
    The descriptor is an equality witness, not a key for finding a match.
    """

    full_result_surface = section == "semantic_model_items"
    source_semantic_identities = _source_semantic_identities(item)
    signature_digests = _signature_digests(item)
    # A local input with no source semantic identity has no emitted canonical
    # atom that distinguishes two equal-looking binders. Keep its route data
    # fail-closed rather than merging it merely because a presentation rename
    # erased the only available discriminator. Full result rows can also use
    # their elaborated endpoint signature as that independent identity.
    normalize_presentation_routes = bool(source_semantic_identities) or (
        full_result_surface and bool(signature_digests)
    )
    descriptor: dict[str, object] = {
        "schema": SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_SCHEMA,
        "presentation_normalizer_schema": PRESENTATION_NORMALIZER_SCHEMA,
        "comparison_scope": (
            "full_result_surface" if full_result_surface else "input_or_field_local"
        ),
        "generated_item_kind": str(item.get("kind") or "").strip(),
        "generated_obligation": _semantic_projection(
            item,
            full_result_surface=full_result_surface,
            omit_recursive_structural_coordinates=(section == "recursive_field_items"),
            normalize_presentation_routes=normalize_presentation_routes,
        ),
        "source_item_semantic_identities": source_semantic_identities,
        "source_association_roles": _association_roles(item),
        "scoped_semantic_context_requirements_sha256": _sha256(
            item.get("source_record_item_semantic_context_requirements_sha256")
        ),
        "source_proof_fidelity_records_sha256": _sha256(
            item.get("source_record_item_source_proof_fidelity_records_sha256")
        ),
    }
    if full_result_surface:
        descriptor["source_association_semantic_sha256"] = (
            _association_semantic_digests(item)
        )
        descriptor["reviewed_elaborated_signature_sha256"] = signature_digests
    if section == "recursive_field_items":
        if recursive_field_direct_source_domain_parent_contract is not None:
            descriptor["recursive_field_direct_source_domain_parent_contract"] = (
                dict(recursive_field_direct_source_domain_parent_contract)
            )
        else:
            # Preserve the older exact-parent-signature lane when a raw audit
            # lacks the stronger input-domain witness.  It remains safe, just
            # more conservative; no old field approval gains the new route by
            # resemblance.
            descriptor["recursive_field_direct_semantic_parent"] = (
                _recursive_field_parent_route_semantic_scope(item)
            )
    return descriptor


def source_record_differential_item_descriptor_sha256(
    item: Mapping[str, Any], *, section: str
) -> str:
    return _canonical_digest(source_record_differential_item_descriptor(item, section=section))


def _raw_formalization_scope_descriptor(
    payload: Mapping[str, Any],
) -> dict[str, str]:
    """Bind every differential group to the raw formalization-scope surface.

    Scope is a paper-level semantic boundary rather than an item receipt. A
    local input may look unchanged while its governing scope has changed, so a
    scope refresh must trigger narrow manual review. Preserve the distinction
    between an explicit null scope and a legacy raw audit that omits it.
    """

    if "formalization_scope" not in payload:
        return {"state": "absent"}
    scope = payload.get("formalization_scope")
    if scope is None:
        return {"state": "explicit_null"}
    return {"state": "present", "sha256": _canonical_digest(scope)}


def _raw_item_groups(
    payload: Mapping[str, Any],
) -> tuple[dict[str, dict[str, object]], dict[str, str]]:
    """Collect every response group, including aggregate-only raw members."""

    recursive_parent_contracts = (
        _recursive_field_direct_source_domain_parent_contracts(payload)
    )
    grouped: dict[str, list[tuple[str, Mapping[str, Any]]]] = {}
    errors: dict[str, str] = {}
    for section in SOURCE_RECORD_REUSABLE_ITEM_SECTIONS:
        raw_items = payload.get(section)
        if raw_items is None:
            continue
        if not isinstance(raw_items, list):
            errors[f"<section:{section}>"] = "raw audit section is not a list"
            continue
        for raw_item in raw_items:
            if not isinstance(raw_item, Mapping):
                errors[f"<section:{section}>"] = "raw audit contains a non-object item"
                continue
            if source_record_item_is_nonreusable_theorem_facing_mirror(
                section, raw_item
            ):
                continue
            key = str(raw_item.get("judgment_key") or "").strip()
            if not key:
                # Keyless generated artifacts remain tied to the raw aggregate
                # receipt.  They cannot consume a response and therefore do
                # not belong to a sidecar differential group.
                continue
            grouped.setdefault(key, []).append((section, raw_item))

    groups: dict[str, dict[str, object]] = {}
    for key, members in grouped.items():
        member_descriptors = [
            {
                "section": section,
                "descriptor": source_record_differential_item_descriptor(
                    item,
                    section=section,
                    recursive_field_direct_source_domain_parent_contract=(
                        recursive_parent_contracts.get(id(item))
                        if section == "recursive_field_items"
                        else None
                    ),
                ),
            }
            for section, item in members
        ]
        member_descriptors.sort(
            key=lambda entry: json.dumps(entry, sort_keys=True, separators=(",", ":"))
        )
        descriptor: dict[str, object] = {
            "schema": SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_SCHEMA,
            "raw_formalization_scope": _raw_formalization_scope_descriptor(payload),
            "members": member_descriptors,
        }
        groups[key] = {
            "descriptor": descriptor,
            "descriptor_sha256": _canonical_digest(descriptor),
            # Retained in memory only.  The serialized overlay carries the
            # descriptor, while a loader must inspect these generated current
            # associations before it can rebind a response provenance pin.
            "raw_members": list(members),
            "semantic_model_items": [
                dict(item)
                for section, item in members
                if section == "semantic_model_items"
            ],
            # Kept only in memory.  The descriptor contains the full
            # name-independent contract, while association-pin transport
            # needs the same derived contract to be recomputed by the loader.
            _DIRECT_SOURCE_DOMAIN_PARENT_CONTRACTS_FIELD: {
                id(item): recursive_parent_contracts[id(item)]
                for section, item in members
                if section == "recursive_field_items"
                and id(item) in recursive_parent_contracts
            },
        }
    return groups, errors


def _archived_source_status_projection_normalized_group(
    group: Mapping[str, object],
    bridge: ValidatedArchivedSourceStatusProjectionBridge,
) -> tuple[dict[str, object] | None, bool, str]:
    """Normalize only receipt-bound archived associations in one raw group.

    This is a descriptor preparation step, not a group matcher.  Each source
    association is selected by its complete raw association-record digest by
    the validated bridge; judgment keys, declaration names, and source-map
    keys never choose a candidate here.  The caller must still require a
    unique complete normalized descriptor class.
    """

    if not isinstance(bridge, ValidatedArchivedSourceStatusProjectionBridge):
        return None, False, "source-status bridge did not yield a validated context"
    raw_descriptor = group.get("descriptor")
    raw_members = group.get("raw_members")
    if not isinstance(raw_descriptor, Mapping) or not isinstance(raw_members, list):
        return None, False, "generated group has no complete raw descriptor/members"
    raw_scope = raw_descriptor.get("raw_formalization_scope")
    if not isinstance(raw_scope, Mapping):
        return None, False, "generated group has no raw formalization-scope descriptor"
    normalized_members: list[tuple[str, Mapping[str, Any]]] = []
    member_descriptors: list[dict[str, object]] = []
    changed = False
    for member in raw_members:
        if (
            not isinstance(member, tuple)
            or len(member) != 2
            or not isinstance(member[0], str)
            or not isinstance(member[1], Mapping)
        ):
            return None, False, "generated group has malformed complete raw members"
        section, raw_item = member
        item = copy.deepcopy(dict(raw_item))
        for field, association in _association_mappings(raw_item):
            if not archived_source_status_association_is_rebound(association, bridge):
                continue
            rebound = normalized_archived_source_status_association(association, bridge)
            if not isinstance(rebound, Mapping):  # defensive against future bridge APIs.
                return None, False, "source-status bridge returned a malformed association"
            item[field] = copy.deepcopy(dict(rebound))
            changed = True
        normalized_members.append((section, item))
        member_descriptors.append(
            {
                "section": section,
                "descriptor": source_record_differential_item_descriptor(
                    item, section=section
                ),
            }
        )
    member_descriptors.sort(
        key=lambda entry: json.dumps(entry, sort_keys=True, separators=(",", ":"))
    )
    descriptor: dict[str, object] = {
        "schema": SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_SCHEMA,
        "raw_formalization_scope": copy.deepcopy(dict(raw_scope)),
        "members": member_descriptors,
    }
    normalized_group = {
        "descriptor": descriptor,
        "descriptor_sha256": _canonical_digest(descriptor),
        "raw_members": normalized_members,
        "semantic_model_items": [
            dict(item)
            for section, item in normalized_members
            if section == "semantic_model_items"
        ],
    }
    return normalized_group, changed, ""


def _archived_source_status_projection_normalized_index(
    groups: Mapping[str, Mapping[str, object]],
    bridge: ValidatedArchivedSourceStatusProjectionBridge,
) -> tuple[
    dict[str, list[tuple[str, Mapping[str, object], bool]]],
    dict[str, Mapping[str, object]],
    dict[str, str],
]:
    """Index all prior groups by their bridge-normalized descriptor class.

    Unchanged groups remain in this index too.  That prevents a changed
    archived group from consuming a current descriptor that an independently
    unchanged archived group also occupies; unique pairing is checked over the
    entire normalized population rather than only a hand-picked migration set.
    """

    indexed: dict[str, list[tuple[str, Mapping[str, object], bool]]] = {}
    normalized_groups: dict[str, Mapping[str, object]] = {}
    errors: dict[str, str] = {}
    for key, group in groups.items():
        normalized, changed, error = _archived_source_status_projection_normalized_group(
            group, bridge
        )
        if error or normalized is None:
            errors[key] = error or "could not normalize archived source-status group"
            continue
        digest = _sha256(normalized.get("descriptor_sha256"))
        if not digest:
            errors[key] = "normalized archived source-status group has no descriptor digest"
            continue
        normalized_groups[key] = normalized
        indexed.setdefault(digest, []).append((key, normalized, changed))
    return indexed, normalized_groups, errors


def _complete_reissue_raw_group_identity(
    group: Mapping[str, object],
) -> tuple[dict[str, object] | None, str]:
    """Bind one strict-reissue response to its complete generated raw group.

    The group key is only a sidecar locator.  Its identity is the canonical
    multiset of every full raw member (section plus complete raw item), so a
    duplicate semantic descriptor can never be used as an interchangeable
    response target in the strict receipt-reissue path.
    """

    raw_members = group.get("raw_members")
    if not isinstance(raw_members, list) or not raw_members:
        return None, "generated group has no complete raw members"
    members: list[dict[str, object]] = []
    for member in raw_members:
        if (
            not isinstance(member, tuple)
            or len(member) != 2
            or not isinstance(member[0], str)
            or not isinstance(member[1], Mapping)
        ):
            return None, "generated group has malformed complete raw members"
        members.append({"section": member[0], "raw_item": dict(member[1])})
    return {
        "schema": SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_SCHEMA,
        "member_count": len(members),
        "canonical_sha256": _canonical_digest(members),
    }, ""


def _source_free_recursive_content_projection(value: object) -> object:
    """Project a source-free raw member without navigation or receipt noise.

    This is deliberately stricter than the semantic descriptor: it retains
    every non-presentation generated field, including recursive containment
    and expanded obligation content. It only removes names/locations used for
    navigation plus machine-generated receipt bookkeeping. It never sees a
    source association because the caller first proves the mapless lane.
    """

    if isinstance(value, Mapping):
        return {
            str(key): _source_free_recursive_content_projection(child)
            for key, child in value.items()
            if str(key) not in _SOURCE_FREE_RECURSIVE_CONTENT_OMITTED_FIELDS
        }
    if isinstance(value, list):
        return [_source_free_recursive_content_projection(child) for child in value]
    if isinstance(value, tuple):
        return [_source_free_recursive_content_projection(child) for child in value]
    return value


def _source_free_recursive_content_identity(
    group: Mapping[str, object],
) -> tuple[dict[str, object] | None, str]:
    """Return the complete name-free raw-content identity for one group."""

    raw_members = group.get("raw_members")
    if not isinstance(raw_members, list) or not raw_members:
        return None, "generated group has no complete raw members"
    members: list[dict[str, object]] = []
    for member in raw_members:
        if (
            not isinstance(member, tuple)
            or len(member) != 2
            or not isinstance(member[0], str)
            or not isinstance(member[1], Mapping)
        ):
            return None, "generated group has malformed complete raw members"
        members.append(
            {
                "section": member[0],
                "raw_item": _source_free_recursive_content_projection(member[1]),
            }
        )
    return {
        "schema": SOURCE_FREE_RECURSIVE_CONTENT_IDENTITY_SCHEMA,
        "member_count": len(members),
        "canonical_sha256": _canonical_digest(members),
    }, ""


def _source_free_recursive_content_identity_matches(
    candidates: list[tuple[str, Mapping[str, object]]],
    *,
    target: Mapping[str, object],
) -> list[tuple[str, Mapping[str, object]]]:
    """Find the unique current group with one name-free content identity.

    This is intentionally only a candidate selector for a mapless recursive
    group whose descriptor class is otherwise ambiguous.  It does not make a
    response reusable by itself: the caller still proves that the selected
    group is mapless/non-semantic and that its complete raw group is exactly
    identical to the archived one.  Count *every* current group with the
    content identity before making that decision, including one that would
    later fail the mapless lane, so source credit cannot be hidden by the
    fallback projection.
    """

    target_digest = canonical_digest_payload(target)
    matches: list[tuple[str, Mapping[str, object]]] = []
    for key, group in candidates:
        identity, error = _source_free_recursive_content_identity(group)
        if error or identity is None:
            continue
        if canonical_digest_payload(identity) == target_digest:
            matches.append((key, group))
    return matches


def _complete_reissue_raw_group_identity_error(
    recorded: object,
    *,
    prior_group: Mapping[str, object] | None = None,
    current_group: Mapping[str, object] | None = None,
) -> str:
    """Recompute one strict transport's prior/current raw-group identities."""

    if not isinstance(recorded, Mapping):
        return "complete receipt reissue item has no raw-group identity"
    if recorded.get("schema") != SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_SCHEMA:
        return "complete receipt reissue item has an unsupported raw-group identity schema"
    identities: dict[str, dict[str, object]] = {}
    for field, group in (("prior", prior_group), ("current", current_group)):
        saved = recorded.get(field)
        if not isinstance(saved, Mapping):
            return f"complete receipt reissue item lacks `{field}` raw-group identity"
        if (
            saved.get("schema") != SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_SCHEMA
            or not isinstance(saved.get("member_count"), int)
            or saved.get("member_count") < 1
            or not _sha256(saved.get("canonical_sha256"))
        ):
            return f"complete receipt reissue item has malformed `{field}` raw-group identity"
        if group is None:
            continue
        actual, actual_error = _complete_reissue_raw_group_identity(group)
        if actual_error or actual is None:
            return f"complete receipt reissue {field} raw group is invalid: {actual_error}"
        if canonical_digest_payload(saved) != canonical_digest_payload(actual):
            return f"complete receipt reissue {field} raw-group identity differs from raw audit"
        identities[field] = actual
    if len(identities) == 2 and (
        canonical_digest_payload(identities["prior"])
        != canonical_digest_payload(identities["current"])
    ):
        return "complete receipt reissue prior/current raw groups differ"
    return ""


def _complete_reissue_response_semantic_association_error(
    response: Mapping[str, Any], group: Mapping[str, object]
) -> str:
    """Verify a preserved response pin directly against an exact raw group."""

    if "semantic_association_sha256" not in response:
        return ""
    pin = _sha256(response.get("semantic_association_sha256"))
    if not pin:
        return "complete receipt reissue response semantic association pin is malformed"
    records = _group_semantic_association_rebind_records(group)
    if not any(record.get("semantic_association_sha256") == pin for record in records):
        return (
            "complete receipt reissue response semantic association pin is absent "
            "from its exact generated raw group"
        )
    return ""


def _complete_reusable_section_identity(
    payload: Mapping[str, Any],
    groups: Mapping[str, Mapping[str, object]],
) -> tuple[dict[str, object] | None, str]:
    """Bind an all-group receipt reissue to every raw reusable section.

    Ordinary differential reuse intentionally works one semantic group at a
    time.  A complete receipt reissue is stricter: it is available only when
    the complete raw reusable-item sections are unchanged as canonical JSON
    and every generated group descriptor is unchanged as a multiset.  This is
    a transport identity, not a declaration-name matching relation.
    """

    sections: dict[str, dict[str, object]] = {}
    for section in SOURCE_RECORD_REUSABLE_ITEM_SECTIONS:
        present = section in payload
        values = payload.get(section)
        if values is None:
            values = []
        if not isinstance(values, list):
            return None, f"raw audit `{section}` is not a list"
        if not all(isinstance(item, Mapping) for item in values):
            return None, f"raw audit `{section}` has a non-object item"
        sections[section] = {
            "present": present,
            "item_count": len(values),
            "canonical_sha256": _canonical_digest(values),
        }
    descriptors = []
    for group in groups.values():
        descriptor = group.get("descriptor")
        digest = _sha256(group.get("descriptor_sha256"))
        if not isinstance(descriptor, Mapping) or not digest:
            return None, "raw audit has a malformed generated semantic descriptor"
        if digest != _canonical_digest(descriptor):
            return None, "raw audit has a malformed generated semantic descriptor digest"
        descriptors.append({"sha256": digest, "descriptor": descriptor})
    descriptors.sort(
        key=lambda value: json.dumps(value, sort_keys=True, separators=(",", ":"))
    )
    return {
        "schema": SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_SCHEMA,
        "reusable_sections": sections,
        "generated_group_count": len(groups),
        "generated_descriptor_multiset_sha256": _canonical_digest(descriptors),
    }, ""


def _complete_reissue_path_label(path: tuple[str, ...]) -> str:
    return ".".join(path)


def _complete_reissue_path_value(
    payload: Mapping[str, Any], path: tuple[str, ...]
) -> tuple[bool, object]:
    current: object = payload
    for field in path:
        if not isinstance(current, Mapping) or field not in current:
            return False, None
        current = current[field]
    return True, current


def _complete_reissue_replace_path(
    payload: dict[str, Any], path: tuple[str, ...], value: object
) -> None:
    current: dict[str, Any] = payload
    for field in path[:-1]:
        next_value = current.get(field)
        if not isinstance(next_value, dict):  # Prechecked by the caller.
            raise SourceRecordDifferentialRevalidationError(
                "complete receipt reissue attempted to normalize a missing aggregate path"
            )
        current = next_value
    current[path[-1]] = value


def _complete_reissue_aggregate_metadata_identity(
    payload: Mapping[str, Any],
) -> tuple[dict[str, object] | None, str]:
    """Return a fail-closed normalized identity for receipt-only deltas.

    Full reusable-section equality cannot, by itself, prove that unrelated
    aggregate provenance remained stable.  This identity accepts only the two
    self-generated raw receipts and, when present in all three replicated
    projections, the receipt-reprojector's selected semantic-projection SHA.
    Every other serialized raw field remains in the canonical digest.
    """

    normalized = copy.deepcopy(dict(payload))
    for path in _COMPLETE_REISSUE_GENERATED_RECEIPT_PATHS:
        present, value = _complete_reissue_path_value(payload, path)
        if not present or not _sha256(value):
            return (
                None,
                "raw audit lacks a valid generated receipt at `"
                + _complete_reissue_path_label(path)
                + "`",
            )
        _complete_reissue_replace_path(
            normalized, path, "<complete-reissue-generated-receipt>"
        )

    selected_values: list[str] = []
    selected_presence: list[bool] = []
    for path in _COMPLETE_REISSUE_SELECTED_PROJECTION_PATHS:
        present, value = _complete_reissue_path_value(payload, path)
        selected_presence.append(present)
        if present:
            digest = _sha256(value)
            if not digest:
                return (
                    None,
                    "raw audit has an invalid selected semantic-projection receipt at `"
                    + _complete_reissue_path_label(path)
                    + "`",
                )
            selected_values.append(digest)
    if any(selected_presence) and not all(selected_presence):
        return (
            None,
            "raw audit has only a partial replicated selected semantic-projection receipt",
        )
    if selected_values and len(set(selected_values)) != 1:
        return (
            None,
            "raw audit's replicated selected semantic-projection receipts disagree",
        )
    for path in _COMPLETE_REISSUE_SELECTED_PROJECTION_PATHS:
        if selected_values:
            _complete_reissue_replace_path(
                normalized, path, "<complete-reissue-selected-semantic-projection>"
            )

    identity: dict[str, object] = {
        "schema": SOURCE_RECORD_COMPLETE_REISSUE_AGGREGATE_DELTA_SCHEMA,
        "policy": SOURCE_RECORD_COMPLETE_REISSUE_AGGREGATE_DELTA_POLICY,
        "generated_receipt_paths": [
            _complete_reissue_path_label(path)
            for path in _COMPLETE_REISSUE_GENERATED_RECEIPT_PATHS
        ],
        "selected_semantic_projection_path_state": (
            "replicated" if selected_values else "absent"
        ),
        "selected_semantic_projection_paths": (
            [
                _complete_reissue_path_label(path)
                for path in _COMPLETE_REISSUE_SELECTED_PROJECTION_PATHS
            ]
            if selected_values
            else []
        ),
        "normalized_payload_sha256": _canonical_digest(normalized),
    }
    if selected_values:
        identity["selected_semantic_projection_sha256"] = selected_values[0]
    return identity, ""


def _complete_reissue_aggregate_metadata_identity_error(
    value: object,
    *,
    prior_raw_audit: Mapping[str, Any],
    current_raw_audit: Mapping[str, Any],
) -> str:
    """Recompute the narrow aggregate-delta receipt for both raw audits."""

    if not isinstance(value, Mapping):
        return "complete receipt reissue has no aggregate metadata identity"
    prior_identity, prior_error = _complete_reissue_aggregate_metadata_identity(
        prior_raw_audit
    )
    current_identity, current_error = _complete_reissue_aggregate_metadata_identity(
        current_raw_audit
    )
    if prior_error or prior_identity is None:
        return "complete receipt reissue prior aggregate metadata is invalid: " + prior_error
    if current_error or current_identity is None:
        return "complete receipt reissue current aggregate metadata is invalid: " + current_error
    recorded_prior = value.get("prior")
    recorded_current = value.get("current")
    if canonical_digest_payload(recorded_prior) != canonical_digest_payload(prior_identity):
        return "complete receipt reissue prior aggregate metadata differs from archived raw"
    if canonical_digest_payload(recorded_current) != canonical_digest_payload(current_identity):
        return "complete receipt reissue current aggregate metadata differs from current raw"
    if canonical_digest_payload(prior_identity.get("normalized_payload_sha256")) != canonical_digest_payload(
        current_identity.get("normalized_payload_sha256")
    ):
        return "complete receipt reissue changed aggregate metadata outside allowed receipt paths"
    return ""


def _complete_reissue_attested_current_revalidation_record(
    *,
    paper: str,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
    candidate_sidecar: Mapping[str, Any],
    candidate_sidecar_path: Path,
    attestation_path: Path,
    replay_only: bool = False,
) -> tuple[dict[str, object] | None, str]:
    """Authenticate a candidate full-current revalidation before transport.

    Strict raw equality can carry a complete previously attested ledger, but
    cannot convert an unverified candidate sidecar into evidence.  At issuance
    this runs the current-revalidation validator's full source-target checks.
    Later loader replay rechecks exact immutable evidence and its attested
    ledger without rerunning the expensive identity-only source audit.
    """

    current_revalidation = _current_revalidation_module()
    metadata = candidate_sidecar.get(
        getattr(current_revalidation, "CURRENT_REVALIDATION_FIELD", "")
    )
    if not isinstance(metadata, Mapping):
        return None, "candidate sidecar lacks current semantic revalidation metadata"
    try:
        relative_attestation = str(metadata.get("attestation_path") or "").strip()
        relative_sidecar = str(
            metadata.get("current_judgment_sidecar_path") or ""
        ).strip()
        if not relative_attestation or not relative_sidecar:
            return None, "candidate current revalidation metadata lacks attestation or sidecar path"
        metadata_attestation = (paper_dir / relative_attestation).resolve()
        metadata_sidecar = (paper_dir / relative_sidecar).resolve()
        paper_root = paper_dir.resolve()
        metadata_attestation.relative_to(paper_root)
        metadata_sidecar.relative_to(paper_root)
        if metadata_attestation != attestation_path.resolve():
            return None, "candidate current revalidation metadata names a different attestation path"
        if metadata_sidecar != candidate_sidecar_path.resolve():
            return None, "candidate current revalidation metadata names a different sidecar path"
        if not metadata_attestation.is_file() or not metadata_sidecar.is_file():
            return None, "candidate current revalidation attestation or sidecar file is missing"
        attestation_sha256 = _file_sha256(metadata_attestation)
        if _sha256(metadata.get("attestation_sha256")) != attestation_sha256:
            return None, "candidate current revalidation attestation bytes differ from its metadata"
        errors = current_revalidation.validate_rebound_sidecar(
            raw_audit,
            candidate_sidecar,
            paper=paper,
            paper_dir=paper_dir,
            output_sidecar_path=candidate_sidecar_path,
            include_runtime_semantic_checks=not replay_only,
        )
    except (OSError, RuntimeError, ValueError) as exc:
        return None, "could not resolve candidate current revalidation evidence: " + str(exc)
    except current_revalidation.SourceRecordCurrentRevalidationError as exc:
        return None, "candidate current revalidation is invalid: " + str(exc)
    if errors:
        return None, "candidate current revalidation is invalid: " + "; ".join(errors[:3])
    return {
        "schema": SOURCE_RECORD_COMPLETE_REISSUE_CURRENT_REVALIDATION_SCHEMA,
        "candidate_sidecar": {
            "path": _stable_provenance_path(candidate_sidecar_path),
            "file_sha256": _file_sha256(candidate_sidecar_path),
        },
        "attestation": {
            "path": _stable_provenance_path(metadata_attestation),
            "file_sha256": attestation_sha256,
        },
        "archived_raw_source_record_audit_sha256": _sha256(
            raw_audit.get("source_record_audit_sha256")
        ),
    }, ""


def _complete_reissue_attested_current_revalidation_error(
    value: object,
    *,
    paper: str,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
    candidate_sidecar: Mapping[str, Any],
    candidate_sidecar_path: Path,
) -> str:
    """Recheck the exact candidate attestation binding at overlay load time."""

    if not isinstance(value, Mapping):
        return "complete receipt reissue lacks attested current-revalidation provenance"
    if value.get("schema") != SOURCE_RECORD_COMPLETE_REISSUE_CURRENT_REVALIDATION_SCHEMA:
        return "complete receipt reissue has an unsupported current-revalidation provenance schema"
    candidate_record = value.get("candidate_sidecar")
    attestation_record = value.get("attestation")
    if not isinstance(candidate_record, Mapping) or not isinstance(attestation_record, Mapping):
        return "complete receipt reissue has malformed candidate current-revalidation provenance"
    try:
        recorded_sidecar = _repository_provenance_path(candidate_record.get("path"))
        recorded_attestation = _repository_provenance_path(attestation_record.get("path"))
    except SourceRecordDifferentialRevalidationError as exc:
        return "complete receipt reissue has invalid candidate current-revalidation path: " + str(exc)
    if recorded_sidecar != candidate_sidecar_path.resolve():
        return "complete receipt reissue candidate sidecar path differs from archived sidecar"
    if not _sha256(candidate_record.get("file_sha256")) or not _sha256(
        attestation_record.get("file_sha256")
    ):
        return "complete receipt reissue has malformed candidate current-revalidation file hashes"
    try:
        if _file_sha256(recorded_sidecar) != candidate_record.get("file_sha256"):
            return "complete receipt reissue candidate sidecar bytes differ from provenance"
        if _file_sha256(recorded_attestation) != attestation_record.get("file_sha256"):
            return "complete receipt reissue candidate attestation bytes differ from provenance"
    except OSError as exc:
        return "complete receipt reissue candidate current-revalidation file is unreadable: " + str(exc)
    actual, actual_error = _complete_reissue_attested_current_revalidation_record(
        paper=paper,
        paper_dir=paper_dir,
        raw_audit=raw_audit,
        candidate_sidecar=candidate_sidecar,
        candidate_sidecar_path=candidate_sidecar_path,
        attestation_path=recorded_attestation,
        replay_only=True,
    )
    if actual_error or actual is None:
        return actual_error
    if canonical_digest_payload(value) != canonical_digest_payload(actual):
        return "complete receipt reissue candidate current-revalidation provenance differs from evidence"
    return ""


def _complete_reusable_section_identity_error(
    identity: object,
    *,
    prior_raw_audit: Mapping[str, Any],
    prior_groups: Mapping[str, Mapping[str, object]],
    current_raw_audit: Mapping[str, Any],
    current_groups: Mapping[str, Mapping[str, object]],
) -> str:
    """Verify a strict reissue receipt against both exact raw surfaces."""

    if not isinstance(identity, Mapping):
        return "complete receipt reissue has no reusable-section identity"
    if identity.get("schema") != SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_SCHEMA:
        return "complete receipt reissue has an unsupported reusable-section identity schema"
    if (
        str(identity.get("mode") or "").strip()
        != SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_MODE
    ):
        return "complete receipt reissue has the wrong reusable-section identity mode"
    prior_identity, prior_error = _complete_reusable_section_identity(
        prior_raw_audit, prior_groups
    )
    current_identity, current_error = _complete_reusable_section_identity(
        current_raw_audit, current_groups
    )
    if prior_error or prior_identity is None:
        return "complete receipt reissue prior raw identity is invalid: " + prior_error
    if current_error or current_identity is None:
        return "complete receipt reissue current raw identity is invalid: " + current_error
    recorded_prior = identity.get("prior")
    recorded_current = identity.get("current")
    if canonical_digest_payload(recorded_prior) != canonical_digest_payload(prior_identity):
        return "complete receipt reissue prior reusable-section identity differs from archived raw"
    if canonical_digest_payload(recorded_current) != canonical_digest_payload(current_identity):
        return "complete receipt reissue current reusable-section identity differs from current raw"
    if canonical_digest_payload(prior_identity) != canonical_digest_payload(current_identity):
        return "complete receipt reissue raw reusable sections or descriptor multiset changed"
    aggregate_error = _complete_reissue_aggregate_metadata_identity_error(
        identity.get("allowed_aggregate_metadata_delta"),
        prior_raw_audit=prior_raw_audit,
        current_raw_audit=current_raw_audit,
    )
    if aggregate_error:
        return aggregate_error
    return ""


def _response_classification(value: Mapping[str, object]) -> str:
    """Return the stored disposition category without interpreting its name.

    Historical sidecars have used a few equivalent ledger fields.  They are
    response metadata, not semantic matching inputs: callers have already
    established descriptor equality before this function is consulted.
    """

    return str(
        value.get("classification")
        or value.get("judgment")
        or value.get("verdict")
        or value.get("status")
        or ""
    ).strip()


def _response_field_has_value(value: Mapping[str, object], field: str) -> bool:
    """Whether one source-credit response field carries a substantive claim."""

    raw = value.get(field)
    if raw is None or raw is False:
        return False
    if isinstance(raw, str):
        return bool(raw.strip())
    if isinstance(raw, Mapping) or isinstance(raw, (list, tuple, set)):
        return bool(raw)
    return True


def _recursive_response_requires_direct_parent_route(
    response: Mapping[str, object] | None,
) -> bool:
    """Return whether exact reuse still needs a direct source-parent route.

    A direct route is mandatory for every source-credit disposition, including
    an approved source convention.  Exact descriptor reuse is safe without
    that route only for an explicit non-source-credit recursive disposition.
    An absent, malformed, or future classification therefore fails closed.
    """

    if response is None:
        # The manual-review summary does not have a current response to
        # classify.  Do not pretend a missing route is a raw-only failure;
        # the builder/loader pass the actual archived response when reuse is
        # being considered.
        return False
    classification = _response_classification(response)
    if classification in INPUT_SOURCE_CREDIT_CLASSIFICATIONS:
        return True
    disposition = str(response.get("source_target_disposition") or "").strip()
    if disposition in SOURCE_TARGET_DISPOSITIONS:
        return True
    if any(
        _response_field_has_value(response, field)
        for field in _RECURSIVE_SOURCE_CREDIT_RESPONSE_FIELDS
    ):
        return True
    return classification not in _NON_SOURCE_CREDIT_RECURSIVE_CLASSIFICATIONS


def _has_substantive_response_field(value: Mapping[str, object], field: str) -> bool:
    """Return whether one structured response credential is actually present."""

    raw = value.get(field)
    if raw is None or raw is False:
        return False
    if isinstance(raw, str):
        return bool(raw.strip())
    if isinstance(raw, Mapping) or isinstance(raw, (list, tuple, set)):
        return bool(raw)
    return True


def _source_free_recursive_member_error(item: Mapping[str, object]) -> str:
    """Reject an unrouted recursive item that carries source-credit structure.

    This is a deliberately narrow *mapless* lane.  It does not infer a source
    relation from a name or an enclosing record.  It only accepts a recursive
    item when the signed raw item itself has no association, explicit parent
    route, source semantic identity, or source-fidelity receipt.  An exact
    full raw-member identity is checked separately after the unique semantic
    descriptor pair is known.
    """

    if _association_mappings(item):
        return "unrouted non-source-credit recursive field carries a source association"
    if item.get("recursive_field_explicit_parent_route") is not None:
        return "unrouted non-source-credit recursive field carries a source parent route"
    if _source_semantic_identities(item):
        return "unrouted non-source-credit recursive field carries source semantic identities"
    if _sha256(item.get("source_record_item_source_proof_fidelity_records_sha256")):
        return "unrouted non-source-credit recursive field carries a source-proof fidelity receipt"
    return ""


def _source_free_recursive_response_error(response: Mapping[str, object]) -> str:
    """Reject machine-readable source credit on a purportedly source-free row."""

    classification = _response_classification(response)
    if classification not in _NON_SOURCE_CREDIT_RECURSIVE_CLASSIFICATIONS:
        return "recursive response is not an explicit non-source-credit disposition"
    if classification in INPUT_SOURCE_CREDIT_CLASSIFICATIONS:
        return "recursive response carries a source-credit classification"
    for field in _RECURSIVE_SOURCE_CREDIT_PIN_FIELDS:
        if _has_substantive_response_field(response, field):
            return "recursive response carries source-credit field `" + field + "`"
    return ""


def _group_has_semantic_model_obligation(group: Mapping[str, object]) -> bool:
    """Whether one response group includes an advertised model/result review."""

    raw_members = group.get("raw_members")
    return bool(
        isinstance(raw_members, list)
        and any(
            isinstance(member, tuple)
            and len(member) == 2
            and member[0] == "semantic_model_items"
            for member in raw_members
        )
    )


def _source_free_recursive_structural_identity(
    group: Mapping[str, object],
    *,
    response: Mapping[str, object] | None,
) -> tuple[dict[str, object] | None, str]:
    """Return an exact raw-member witness for the narrow mapless lane.

    ``None, ""`` means the group does not use this lane.  A response can use
    it only when it has an explicit non-source-credit classification and the
    group contains at least one recursive member with no direct parent route.
    The full raw member multiset is intentionally retained as an equality
    witness after semantic matching; it is never a selector for a current
    group.  That makes a changed recursive containment/field closure manual
    work even if its presentation-normalized descriptor is unchanged.
    """

    if response is None:
        return None, ""
    raw_members = group.get("raw_members")
    if not isinstance(raw_members, list):
        return None, "generated group has no raw members"
    uses_lane = False
    for member in raw_members:
        if (
            not isinstance(member, tuple)
            or len(member) != 2
            or not isinstance(member[0], str)
            or not isinstance(member[1], Mapping)
        ):
            return None, "generated group has malformed raw members"
        section, item = member
        if section != "recursive_field_items":
            continue
        if _recursive_field_parent_route_semantic_scope(item) is not None:
            continue
        # A malformed/partial route is still source structure and must not
        # become a mapless non-credit row merely because its semantic scope
        # could not be parsed.
        if item.get("recursive_field_explicit_parent_route") is not None:
            return None, "unrouted non-source-credit recursive field carries a malformed source parent route"
        uses_lane = True
        if error := _source_free_recursive_member_error(item):
            return None, error
    if not uses_lane:
        return None, ""
    if error := _source_free_recursive_response_error(response):
        return None, error
    identity, identity_error = _complete_reissue_raw_group_identity(group)
    if identity_error or identity is None:
        return None, "source-free recursive raw-member identity is invalid: " + identity_error
    content_identity, content_identity_error = _source_free_recursive_content_identity(
        group
    )
    if content_identity_error or content_identity is None:
        return (
            None,
            "source-free recursive content identity is invalid: "
            + content_identity_error,
        )
    return {
        "schema": SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_SCHEMA,
        "raw_group_identity": identity,
        "semantic_content_identity": content_identity,
    }, ""


def _source_free_recursive_structural_identity_error(
    recorded: object,
    *,
    group: Mapping[str, object],
    response: Mapping[str, object] | None,
) -> str:
    """Recompute one mapless recursive witness from authenticated raw data."""

    if not isinstance(recorded, Mapping):
        return "source-free recursive structural identity is not an object"
    if recorded.get("schema") != SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_SCHEMA:
        return "source-free recursive structural identity has an unsupported schema"
    if set(recorded) not in (
        {"schema", "raw_group_identity"},
        {"schema", "raw_group_identity", "semantic_content_identity"},
    ):
        return "source-free recursive structural identity has unsupported fields"
    actual, error = _source_free_recursive_structural_identity(
        group, response=response
    )
    if error:
        return error
    if actual is None:
        return "source-free recursive structural identity is attached to a non-mapless group"
    # Schema-v1 receipts issued before name-free content selection retained
    # only the strict raw witness.  They remain valid for the old unique
    # descriptor path, but cannot resolve a future descriptor collision.
    expected = (
        actual
        if "semantic_content_identity" in recorded
        else {
            "schema": actual["schema"],
            "raw_group_identity": actual["raw_group_identity"],
        }
    )
    if canonical_digest_payload(recorded) != canonical_digest_payload(expected):
        return "source-free recursive structural identity differs from authenticated raw group"
    return ""


def _group_differential_reuse_error(
    group: Mapping[str, object],
    *,
    response: Mapping[str, object] | None = None,
) -> str:
    """Return why this generated group cannot receive automatic reuse.

    Most groups are evaluated through their complete semantic descriptor. A
    recursive field claiming source credit has an additional source-fidelity
    requirement: it must carry a locally checked direct semantic parent route.
    A recursive response that explicitly makes no source-credit claim instead
    retains an exact descriptor match without inventing a route.  We never
    compose routes through another field or recover a parent by name.
    """

    raw_members = group.get("raw_members")
    if not isinstance(raw_members, list):
        return "generated group has no raw members"
    for member in raw_members:
        if (
            not isinstance(member, tuple)
            or len(member) != 2
            or not isinstance(member[0], str)
            or not isinstance(member[1], Mapping)
        ):
            return "generated group has malformed raw members"
        section, item = member
        if (
            section == "recursive_field_items"
            and _recursive_field_parent_route_semantic_scope(item) is None
            and _recursive_response_requires_direct_parent_route(response)
        ):
            return (
                "recursive field lacks a locally authenticated direct semantic "
                "parent route"
            )
    _identity, source_free_error = _source_free_recursive_structural_identity(
        group, response=response
    )
    if source_free_error:
        return source_free_error
    return ""


def _raw_audit_provenance(payload: Mapping[str, Any], path: Path) -> dict[str, str]:
    return {
        "path": _stable_provenance_path(path),
        "file_sha256": _file_sha256(path),
        "source_record_audit_sha256": _sha256(payload.get("source_record_audit_sha256")),
        "source_record_audit_integrity_sha256": _sha256(
            payload.get("source_record_audit_integrity_sha256")
        ),
    }


def _same_resolved_path(left: Path, right: Path) -> bool:
    try:
        return left.resolve() == right.resolve()
    except OSError:
        return False


def _archived_source_status_projection_bridge_context(
    *,
    bridge_path: Path,
    paper: str,
    paper_dir: Path,
    prior_raw_audit: Mapping[str, Any],
    prior_raw_audit_path: Path,
    prior_judgments: Mapping[str, Any],
    prior_judgments_path: Path,
    current_raw_audit: Mapping[str, Any],
    current_raw_audit_path: Path,
    recorded: Mapping[str, object] | None = None,
) -> tuple[ValidatedArchivedSourceStatusProjectionBridge | None, dict[str, str] | None, str]:
    """Load a bridge only when it replays the exact differential evidence.

    The bridge module authenticates its old/current source maps and fidelity
    ledgers as well as both raw receipts.  This wrapper additionally proves
    that those archived/current raw and sidecar files are the same evidence
    selected by this differential overlay.  A bridge cannot be used as a
    nearby-file waiver for another receipt.
    """

    context, receipt, evidence, error = (
        load_archived_source_status_projection_bridge_context(
            paper=paper,
            paper_dir=paper_dir,
            receipt_path=bridge_path,
        )
    )
    if error or context is None or receipt is None or evidence is None:
        return None, None, error or "could not load archived source-status bridge"
    if not isinstance(context, ValidatedArchivedSourceStatusProjectionBridge):
        return None, None, "archived source-status bridge did not yield a validated context"
    expected_evidence = {
        "prior_raw_audit": (prior_raw_audit_path, prior_raw_audit),
        "prior_judgments": (prior_judgments_path, prior_judgments),
        "current_raw_audit": (current_raw_audit_path, current_raw_audit),
    }
    for field, (expected_path, expected_payload) in expected_evidence.items():
        loaded = evidence.get(field)
        if (
            not isinstance(loaded, tuple)
            or len(loaded) != 3
            or not isinstance(loaded[0], Path)
            or not isinstance(loaded[1], Mapping)
            or not isinstance(loaded[2], bytes)
        ):
            return None, None, f"archived source-status bridge has malformed `{field}` evidence"
        actual_path, actual_payload, _actual_bytes = loaded
        if not _same_resolved_path(actual_path, expected_path):
            return None, None, f"archived source-status bridge `{field}` path differs from differential evidence"
        if canonical_digest_payload(actual_payload) != canonical_digest_payload(
            expected_payload
        ):
            return None, None, f"archived source-status bridge `{field}` content differs from differential evidence"
    try:
        bridge_record = {
            "path": _stable_provenance_path(bridge_path),
            "file_sha256": _file_sha256(bridge_path),
            "receipt_sha256": context.receipt_sha256,
        }
    except (OSError, SourceRecordDifferentialRevalidationError) as exc:
        return None, None, "could not authenticate archived source-status bridge file: " + str(exc)
    if recorded is not None and dict(recorded) != bridge_record:
        return None, None, "archived source-status bridge provenance differs from overlay"
    if _sha256(receipt.get(ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_INTEGRITY_FIELD)) != context.receipt_sha256:
        return None, None, "archived source-status bridge receipt integrity differs from its validated context"
    return context, bridge_record, ""


def _current_raw_provenance_error(
    recorded: object, expected: Mapping[str, str]
) -> str:
    """Compare the stable identity of the receiving raw audit.

    A differential overlay archives its *prior* raw audit by exact file bytes.
    The current raw audit is different: ``--refresh-judgment-summary`` is
    explicitly allowed to rewrite only derived summary fields, which changes
    the JSON file hash while leaving both independently verified raw receipts
    unchanged.  The loader has already authenticated the current file through
    ``_raw_audit_error``; this comparison therefore binds its canonical path
    and the two stable receipts, deliberately not its serialization hash.
    """

    if not isinstance(recorded, Mapping):
        return "is missing"
    for field in (
        "path",
        "source_record_audit_sha256",
        "source_record_audit_integrity_sha256",
    ):
        if str(recorded.get(field) or "") != str(expected.get(field) or ""):
            return f"has a different `{field}`"
    # The issuance file hash remains required in the serialized overlay for a
    # human audit trail, but it cannot make a permitted summary refresh stale.
    if not _sha256(recorded.get("file_sha256")):
        return "has no valid issuance `file_sha256`"
    return ""


def _semantic_association_rebind_record(
    *, section: str, field: str, association: Mapping[str, Any]
) -> dict[str, object] | None:
    """Return one source-content-validated semantic association receipt.

    The public association pin also contains the reviewed elaborated signature,
    so it correctly changes when an enclosing result changes.  A local
    boundary/field judgment may nevertheless remain semantically unchanged.
    This record separates the source semantic content and route role that must
    stay equal from that volatile signature receipt.  It never uses a source
    key, declaration, theorem name, or binder spelling to identify a match.
    """

    if association.get("schema") != 2:
        return None
    supplied_pin = _sha256(association.get("semantic_association_sha256"))
    identities = association.get("source_item_identities")
    if not supplied_pin or not isinstance(identities, list) or not identities:
        return None
    semantic_identities: list[str] = []
    for identity in identities:
        if not isinstance(identity, Mapping):
            return None
        digest = _sha256(identity.get("source_semantic_sha256"))
        if not digest:
            return None
        semantic_identities.append(digest)
    if len(set(semantic_identities)) != len(semantic_identities):
        return None
    signature = association.get("reviewed_elaborated_signature_identity")
    if not isinstance(signature, Mapping):
        return None
    # Delegate the generated-pin rule to the target-disposition module.  This
    # validates the current association rather than trusting a copied pin.
    is_statement_component = (
        str(association.get("association_origin") or "").strip()
        == STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ORIGIN
        or str(association.get("role") or "").strip()
        == STATEMENT_SOURCE_COMPONENT_ASSOCIATION_ROLE
    )
    if is_statement_component:
        expected_pin, _component_error = (
            statement_source_component_effective_semantic_pin(association)
        )
    elif (
        str(association.get("association_origin") or "").strip()
        == STATEMENT_SOURCE_REVIEW_ASSOCIATION_ORIGIN
        or str(association.get("role") or "").strip()
        == STATEMENT_SOURCE_REVIEW_ASSOCIATION_ROLE
    ):
        expected_pin, _review_error = (
            statement_source_review_effective_semantic_pin(association)
        )
    else:
        expected_pin = semantic_association_record_digest(
            semantic_identities, signature
        )
    if not expected_pin or supplied_pin != expected_pin:
        return None
    content = {
        "schema": SEMANTIC_ASSOCIATION_REBIND_SCHEMA,
        "section": section,
        "association_field": field,
        "association_schema": 2,
        "source_item_semantic_identities": sorted(semantic_identities),
        "source_association_role": _association_role_projection(association),
    }
    return {
        "content": content,
        "content_sha256": _canonical_digest(content),
        "semantic_association_sha256": supplied_pin,
    }


def _group_direct_source_domain_parent_contract(
    group: Mapping[str, object], item: Mapping[str, Any]
) -> Mapping[str, object] | None:
    """Return the in-memory contract derived for this exact raw field item."""

    contracts = group.get(_DIRECT_SOURCE_DOMAIN_PARENT_CONTRACTS_FIELD)
    if not isinstance(contracts, Mapping):
        return None
    candidate = contracts.get(id(item))
    return candidate if isinstance(candidate, Mapping) else None


def _recursive_parent_route_semantic_association_rebind_record(
    *,
    section: str,
    item: Mapping[str, Any],
    direct_source_domain_parent_contract: Mapping[str, object] | None = None,
) -> dict[str, object] | None:
    """Return one exact recursive parent-route response-pin receipt.

    A recursive response can carry the generated parent association pin even
    though the association is stored inside its parent-route receipt rather
    than in a top-level association field.  This is not an inferred route: the
    common parent-route validator authenticates the route, source semantic
    identity, convention, and parent signature before this helper exposes it.
    A legacy route retains the exact-raw-group requirement.  A newer derived
    direct-source-domain contract instead binds all source pins and the full
    parent input domain while deliberately excluding the parent conclusion;
    it may rebind a changed parent signature only after that contract remains
    byte-identical.  The direct semantic-model result row is still reviewed
    through its full descriptor, independently of this child transport.
    """

    scope = _recursive_field_parent_route_semantic_scope(item)
    if scope is None:
        return None
    parent_pin = _sha256(scope.get("parent_source_association_sha256"))
    source_semantic = _sha256(scope.get("source_item_semantic_sha256"))
    if not parent_pin or not source_semantic:
        return None
    if direct_source_domain_parent_contract is not None:
        contract = dict(direct_source_domain_parent_contract)
        if contract.get("schema") != _DIRECT_SOURCE_DOMAIN_PARENT_CONTRACT_SCHEMA:
            return None
        source_pins = contract.get("source_item_anchor_pins")
        route = item.get("recursive_field_explicit_parent_route")
        route_identities = (
            route.get("source_item_identities") if isinstance(route, Mapping) else None
        )
        if (
            not isinstance(source_pins, list)
            or len(source_pins) != 1
            or not isinstance(source_pins[0], Mapping)
            or not isinstance(route_identities, list)
            or len(route_identities) != 1
            or not isinstance(route_identities[0], Mapping)
        ):
            return None
        source_map_item_sha = _sha256(source_pins[0].get("source_map_item_sha256"))
        route_source_map_item_sha = _sha256(
            route_identities[0].get("source_map_item_sha256")
        )
        if (
            not source_map_item_sha
            or source_map_item_sha != route_source_map_item_sha
            or _sha256(source_pins[0].get("source_semantic_sha256"))
            != source_semantic
        ):
            return None
        content = {
            "schema": SEMANTIC_ASSOCIATION_REBIND_SCHEMA,
            "section": section,
            "association_field": "recursive_field_direct_source_domain_parent_contract",
            "association_schema": "recursive_parent_direct_source_domain_v1",
            "source_item_semantic_identities": [source_semantic],
            "source_association_role": contract,
        }
        return {
            "content": content,
            "content_sha256": _canonical_digest(content),
            "semantic_association_sha256": parent_pin,
        }

    route_content = dict(scope)
    route_content.pop("parent_source_association_sha256", None)
    content = {
        "schema": SEMANTIC_ASSOCIATION_REBIND_SCHEMA,
        "section": section,
        "association_field": "recursive_field_explicit_parent_route",
        "association_schema": "recursive_parent_route_v1",
        "source_item_semantic_identities": [source_semantic],
        "source_association_role": route_content,
    }
    return {
        "content": content,
        "content_sha256": _canonical_digest(content),
        "semantic_association_sha256": parent_pin,
        "requires_exact_raw_group_identity": True,
    }


def _group_semantic_association_rebind_records(
    group: Mapping[str, object],
) -> list[dict[str, object]]:
    """Collect valid generated association receipts for one response group."""

    raw_members = group.get("raw_members")
    if not isinstance(raw_members, list):
        return []
    records: list[dict[str, object]] = []
    for member in raw_members:
        if (
            not isinstance(member, tuple)
            or len(member) != 2
            or not isinstance(member[0], str)
            or not isinstance(member[1], Mapping)
        ):
            return []
        section, item = member
        for field, association in _association_mappings(item):
            record = _semantic_association_rebind_record(
                section=section, field=field, association=association
            )
            if record is not None:
                records.append(record)
        route_record = _recursive_parent_route_semantic_association_rebind_record(
            section=section,
            item=item,
            direct_source_domain_parent_contract=(
                _group_direct_source_domain_parent_contract(group, item)
                if section == "recursive_field_items"
                else None
            ),
        )
        if route_record is not None:
            records.append(route_record)
    return records


def _semantic_association_rebind_receipt(
    response: Mapping[str, Any],
    *,
    prior_group: Mapping[str, object],
    current_group: Mapping[str, object],
) -> tuple[dict[str, object] | None, str]:
    """Derive a safe current semantic-association pin for one response.

    A response without this optional provenance field needs no rebind.  If it
    does claim a pin, the old pin must be present on an authenticated prior raw
    association and each matching source-content/role record must lead to one
    unambiguous current generated pin.  A change in source content, route
    role, schema, or ambiguity is therefore manual-review debt, not a reason
    to preserve a stale response.
    """

    if "semantic_association_sha256" not in response:
        return None, ""
    prior_response_pin = _sha256(response.get("semantic_association_sha256"))
    if not prior_response_pin:
        return None, "response semantic association pin is malformed"
    prior_records = _group_semantic_association_rebind_records(prior_group)
    current_records = _group_semantic_association_rebind_records(current_group)
    matching_prior = [
        record
        for record in prior_records
        if record.get("semantic_association_sha256") == prior_response_pin
    ]
    if not matching_prior:
        return None, "response semantic association pin is not present on the archived generated group"
    requires_exact_raw_group_identity = any(
        record.get("requires_exact_raw_group_identity") is True
        for record in matching_prior
    )
    exact_raw_group_identity: dict[str, object] | None = None
    if requires_exact_raw_group_identity:
        prior_identity, prior_identity_error = _complete_reissue_raw_group_identity(
            prior_group
        )
        current_identity, current_identity_error = _complete_reissue_raw_group_identity(
            current_group
        )
        if (
            prior_identity_error
            or current_identity_error
            or prior_identity is None
            or current_identity is None
        ):
            return (
                None,
                "recursive parent-route response pin lacks a complete raw-group identity",
            )
        exact_raw_group_identity = {
            "schema": SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_SCHEMA,
            "prior": prior_identity,
            "current": current_identity,
        }
        if identity_error := _complete_reissue_raw_group_identity_error(
            exact_raw_group_identity,
            prior_group=prior_group,
            current_group=current_group,
        ):
            return None, "recursive parent-route " + identity_error
    current_by_content: dict[str, list[dict[str, object]]] = {}
    for record in current_records:
        digest = _sha256(record.get("content_sha256"))
        content = record.get("content")
        if digest and isinstance(content, Mapping) and digest == _canonical_digest(content):
            current_by_content.setdefault(digest, []).append(record)

    current_pins: set[str] = set()
    content_descriptors: dict[str, Mapping[str, object]] = {}
    for prior_record in matching_prior:
        content = prior_record.get("content")
        content_digest = _sha256(prior_record.get("content_sha256"))
        if (
            not isinstance(content, Mapping)
            or not content_digest
            or content_digest != _canonical_digest(content)
        ):
            return None, "archived generated association content is malformed"
        candidates = [
            record
            for record in current_by_content.get(content_digest, [])
            if canonical_digest_payload(record.get("content"))
            == canonical_digest_payload(content)
        ]
        if len(candidates) != 1:
            return None, "current generated association content is absent or ambiguous"
        current_pin = _sha256(candidates[0].get("semantic_association_sha256"))
        if not current_pin:
            return None, "current generated association lacks a valid semantic pin"
        current_pins.add(current_pin)
        content_descriptors[content_digest] = dict(content)
    if len(current_pins) != 1:
        return None, "one response pin would need to bind multiple current semantic associations"
    current_pin = next(iter(current_pins))
    if requires_exact_raw_group_identity and current_pin != prior_response_pin:
        return (
            None,
            "recursive parent-route response pin does not name the identical current parent association",
        )
    receipt: dict[str, object] = {
        "schema": SEMANTIC_ASSOCIATION_REBIND_SCHEMA,
        "prior_response_semantic_association_sha256": prior_response_pin,
        "current_semantic_association_sha256": current_pin,
        "association_content_descriptors": [
            {
                "content": content_descriptors[digest],
                "content_sha256": digest,
            }
            for digest in sorted(content_descriptors)
        ],
    }
    if exact_raw_group_identity is not None:
        receipt["recursive_parent_route_raw_group_identity"] = (
            exact_raw_group_identity
        )
    return receipt, ""


def _semantic_association_rebind_matches(
    recorded: object, expected: Mapping[str, object]
) -> bool:
    """Check a persisted rebind receipt without accepting an assertion alone."""

    if not isinstance(recorded, Mapping):
        return False
    if recorded.get("schema") != SEMANTIC_ASSOCIATION_REBIND_SCHEMA:
        return False
    return canonical_digest_payload(recorded) == canonical_digest_payload(expected)


def _current_group_associations_for_semantic_pin(
    group: Mapping[str, object], semantic_pin: str
) -> list[Mapping[str, object]]:
    """Return exact generated receiving associations for one response pin.

    This deliberately selects by the complete generated semantic association
    pin already authenticated by the differential receipt, not by a source
    key, theorem/declaration spelling, judgment key, or route label.  Duplicate
    copies of one byte-identical association are harmless; distinct records
    remain ambiguous and reject the reuse below.
    """

    raw_members = group.get("raw_members")
    if not isinstance(raw_members, list):
        return []
    candidates: dict[str, Mapping[str, object]] = {}
    for member in raw_members:
        if (
            not isinstance(member, tuple)
            or len(member) != 2
            or not isinstance(member[1], Mapping)
        ):
            return []
        for _field, association in _association_mappings(member[1]):
            if _sha256(association.get("semantic_association_sha256")) != semantic_pin:
                continue
            candidates.setdefault(_canonical_digest(association), association)
    return [candidates[digest] for digest in sorted(candidates)]


def _administrative_projection_rebind_loaded_response(
    response: Mapping[str, Any],
    *,
    current_group: Mapping[str, object],
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None,
) -> dict[str, Any] | None:
    """Apply one exact current association rebind to a loaded response.

    Differential reuse first validates the ordinary archived-to-current
    semantic-association receipt.  Only after that succeeds can this method
    advance its *current* response pin through a schema-4-to-schema-5 receipt.
    It cannot use an old association in the archive, a similarly named source
    item, or an arbitrary mapping shaped like a receipt.  More than one
    distinct resulting response is ambiguous and stays unavailable.
    """

    if administrative_projection_rebind is None:
        return dict(response)
    if not isinstance(
        administrative_projection_rebind, ValidatedAdministrativeProjectionRebind
    ):
        return None
    current_pin = _sha256(response.get("semantic_association_sha256"))
    if not current_pin:
        return dict(response)
    candidates = _current_group_associations_for_semantic_pin(
        current_group, current_pin
    )
    if not candidates:
        return None
    transported: dict[str, Mapping[str, object]] = {}
    for raw_association in candidates:
        effective_association = administrative_projection_rebound_association(
            raw_association, administrative_projection_rebind
        )
        effective_pin = _sha256(
            effective_association.get("semantic_association_sha256")
        )
        if not effective_pin:
            return None
        candidate = administrative_projection_rebound_response(
            response,
            raw_association,
            administrative_projection_rebind,
        )
        if _sha256(candidate.get("semantic_association_sha256")) != effective_pin:
            return None
        transported[_canonical_digest(candidate)] = candidate
    if len(transported) != 1:
        return None
    return dict(next(iter(transported.values())))


def _materialize_current_semantic_association_rebind(
    value: Mapping[str, Any],
    *,
    prior_group: Mapping[str, object],
    current_group: Mapping[str, object],
    administrative_projection_rebind: ValidatedAdministrativeProjectionRebind | None = None,
    archived_source_status_bridge: ValidatedArchivedSourceStatusProjectionBridge | None = None,
) -> dict[str, Any] | None:
    """Return a loader-only response with a checked current association pin."""

    effective_value = rebound_archived_source_status_response(
        value, archived_source_status_bridge
    )
    if effective_value is None:
        return None
    expected, error = _semantic_association_rebind_receipt(
        effective_value,
        prior_group=prior_group,
        current_group=current_group,
    )
    if error:
        return None
    metadata = effective_value.get(SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD)
    if not isinstance(metadata, Mapping):
        return None
    recorded = metadata.get(SEMANTIC_ASSOCIATION_REBIND_FIELD)
    # Legacy v1 overlays predate this receipt.  They are usable only after the
    # exact archived/current groups independently reproduce it here; a copied
    # old association pin never receives a blanket exception.
    if expected is None:
        if recorded is not None:
            return None
        return dict(effective_value)
    if recorded is not None and not _semantic_association_rebind_matches(recorded, expected):
        return None
    result = dict(effective_value)
    result["semantic_association_sha256"] = expected[
        "current_semantic_association_sha256"
    ]
    refreshed_metadata = copy.deepcopy(dict(metadata))
    refreshed_metadata[SEMANTIC_ASSOCIATION_REBIND_FIELD] = expected
    result[SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD] = refreshed_metadata
    return _administrative_projection_rebind_loaded_response(
        result,
        current_group=current_group,
        administrative_projection_rebind=administrative_projection_rebind,
    )


def _semantic_association_rebind_receipt_error(value: object) -> str:
    """Validate transport shape before the loader recomputes the receipt."""

    if not isinstance(value, Mapping):
        return "is malformed"
    if value.get("schema") != SEMANTIC_ASSOCIATION_REBIND_SCHEMA:
        return "has an unsupported schema"
    for field in (
        "prior_response_semantic_association_sha256",
        "current_semantic_association_sha256",
    ):
        if not _sha256(value.get(field)):
            return f"has no valid `{field}`"
    descriptors = value.get("association_content_descriptors")
    if not isinstance(descriptors, list) or not descriptors:
        return "has no association-content descriptors"
    seen: set[str] = set()
    for entry in descriptors:
        if not isinstance(entry, Mapping):
            return "has a non-object association-content descriptor"
        content = entry.get("content")
        digest = _sha256(entry.get("content_sha256"))
        if not isinstance(content, Mapping) or not digest or digest != _canonical_digest(content):
            return "has an invalid association-content descriptor receipt"
        if digest in seen:
            return "has duplicate association-content descriptor receipts"
        seen.add(digest)
    exact_raw_group_identity = value.get(
        "recursive_parent_route_raw_group_identity"
    )
    if exact_raw_group_identity is not None:
        if error := _complete_reissue_raw_group_identity_error(
            exact_raw_group_identity
        ):
            return "has invalid recursive parent-route raw-group identity: " + error
    return ""


def _judgment_metadata_error(
    value: Mapping[str, Any],
    payload: Mapping[str, Any],
    group: Mapping[str, object],
    *,
    prior_audit_digest: str,
) -> str:
    if _payload_is_non_evidence(value):
        return "prior judgment is marked non-evidence"
    classification = str(
        value.get("classification")
        or value.get("judgment")
        or value.get("verdict")
        or value.get("status")
        or ""
    ).strip()
    if not classification:
        return "prior judgment lacks a classification"
    if (
        str(_effective(value, payload, "prompt_version") or "").strip()
        != SOURCE_RECORD_V10_PROMPT_VERSION
    ):
        return "prior judgment does not use the v10 source-record prompt"
    policy = str(
        _effective(value, payload, "source_record_policy_version") or ""
    ).strip()
    if policy and policy != SOURCE_RECORD_V10_PROMPT_VERSION:
        return "prior judgment records a different source-record policy"
    if _sha256(_effective(value, payload, "source_record_audit_sha256")) != prior_audit_digest:
        return "prior judgment is not tied to the archived prior raw receipt"
    validator = (
        value.get("validator")
        or value.get("model")
        or value.get("judge")
        or payload.get("validator")
        or payload.get("model")
        or payload.get("judge")
    )
    timestamp = (
        value.get("validated_at")
        or value.get("timestamp")
        or value.get("generated_at")
        or payload.get("validated_at")
        or payload.get("timestamp")
        or payload.get("generated_at")
    )
    if not str(validator or "").strip() or not str(timestamp or "").strip():
        return "prior judgment lacks validator/timestamp metadata"

    for semantic_item in group.get("semantic_model_items") or []:
        if not isinstance(semantic_item, Mapping):
            return "prior semantic-model item is malformed"
        dimensions = semantic_item.get("dimensions")
        submitted = value.get("semantic_model_dimensions")
        if not isinstance(dimensions, list) or not isinstance(submitted, Mapping):
            return "prior semantic-model response is incomplete"
        for dimension in dimensions:
            if not isinstance(dimension, Mapping):
                return "prior semantic-model dimension is malformed"
            dimension_id = str(dimension.get("id") or "").strip()
            if not dimension_id or not isinstance(submitted.get(dimension_id), Mapping):
                return "prior semantic-model response is incomplete"
    return ""


def _materialize_prior_response(
    value: Mapping[str, Any], payload: Mapping[str, Any]
) -> dict[str, Any]:
    """Make inherited sidecar metadata explicit before loader authentication."""

    result = copy.deepcopy(dict(value))
    for field in (
        "prompt_version",
        "source_record_policy_version",
        "source_record_audit_sha256",
        "validator",
        "validated_at",
    ):
        if not result.get(field) and payload.get(field):
            result[field] = copy.deepcopy(payload[field])
    return result


def _descriptor_index(
    groups: Mapping[str, Mapping[str, object]]
) -> dict[str, list[tuple[str, Mapping[str, object]]]]:
    indexed: dict[str, list[tuple[str, Mapping[str, object]]]] = {}
    for key, group in groups.items():
        digest = _sha256(group.get("descriptor_sha256"))
        if digest:
            indexed.setdefault(digest, []).append((key, group))
    return indexed


def _current_reuse_exclusion_record(
    path: Path | None,
    *,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    current_descriptor_index: Mapping[
        str, list[tuple[str, Mapping[str, object]]]
    ],
) -> tuple[dict[str, str], dict[str, Any] | None]:
    """Load a reviewed descriptor-only exclusion artifact for one raw receipt."""

    if path is None:
        return {}, None
    try:
        artifact = _read_json_object(path)
    except SourceRecordDifferentialRevalidationError:
        raise
    if error := _reuse_exclusions_artifact_error(
        artifact, paper=paper, current_raw_audit=current_raw_audit
    ):
        raise SourceRecordDifferentialRevalidationError(error)
    record = _reuse_exclusions_record(artifact, path)
    if error := _reuse_exclusions_record_error(
        record, paper=paper, current_raw_audit=current_raw_audit
    ):
        raise SourceRecordDifferentialRevalidationError(error)
    reasons = _reuse_exclusion_reason_ledger(
        artifact.get(SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_REASONS_FIELD),
        label="reuse-exclusions artifact",
    )
    if error := _reuse_exclusions_current_group_error(
        reasons, current_descriptor_index
    ):
        raise SourceRecordDifferentialRevalidationError(error)
    return reasons, record


def _overlay_without_integrity(payload: Mapping[str, Any]) -> dict[str, Any]:
    return {
        str(key): value
        for key, value in payload.items()
        if str(key) != SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_INTEGRITY_FIELD
    }


def source_record_differential_revalidation_sha256(payload: Mapping[str, Any]) -> str:
    return _canonical_digest(_overlay_without_integrity(payload))


def stamp_source_record_differential_revalidation(payload: dict[str, Any]) -> None:
    payload[SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_INTEGRITY_FIELD] = (
        source_record_differential_revalidation_sha256(payload)
    )


def build_source_record_differential_revalidation(
    *,
    paper: str,
    prior_raw_audit: Mapping[str, Any],
    prior_judgments: Mapping[str, Any],
    current_raw_audit: Mapping[str, Any],
    prior_raw_audit_path: Path,
    prior_judgments_path: Path,
    current_raw_audit_path: Path,
    reuse_exclusions_path: Path | None = None,
    require_complete_reusable_section_identity: bool = False,
    prior_current_revalidation_attestation_path: Path | None = None,
    archived_source_status_projection_bridge_path: Path | None = None,
) -> dict[str, Any]:
    """Build a v10 overlay for all uniquely unchanged semantic groups.

    A changed or ambiguous group is reported in ``manual_review_required`` and
    deliberately omitted from ``items``.  This lets a reviewer write fresh
    ordinary-sidecar responses only for changed material without asserting a
    new aggregate receipt for unrelated historical judgments.  The opt-in
    ``require_complete_reusable_section_identity`` mode is stricter: every
    reusable raw section, generated descriptor, and non-receipt aggregate
    field must remain canonically identical.
    """

    for label, raw in (("prior", prior_raw_audit), ("current", current_raw_audit)):
        error = _raw_audit_error(raw, paper=paper, label=label)
        if error:
            raise SourceRecordDifferentialRevalidationError(error)
    if (
        prior_judgments.get("schema") != 1
        or prior_judgments.get("paper") != paper
        or _payload_is_non_evidence(prior_judgments)
    ):
        raise SourceRecordDifferentialRevalidationError(
            "prior source-record sidecar is not saved evidence for this paper"
        )
    if (
        str(prior_judgments.get("prompt_version") or "").strip()
        != SOURCE_RECORD_V10_PROMPT_VERSION
    ):
        raise SourceRecordDifferentialRevalidationError(
            "prior source-record sidecar does not use the v10 source-record prompt"
        )
    raw_judgments = prior_judgments.get("items") or prior_judgments.get(
        "field_judgments"
    )
    if not isinstance(raw_judgments, Mapping):
        raise SourceRecordDifferentialRevalidationError(
            "prior source-record sidecar has no item ledger"
        )
    if prior_current_revalidation_attestation_path is not None and not (
        require_complete_reusable_section_identity
    ):
        raise SourceRecordDifferentialRevalidationError(
            "a prior current-revalidation attestation is valid only for complete receipt reissue"
        )
    if archived_source_status_projection_bridge_path is not None and (
        require_complete_reusable_section_identity
    ):
        raise SourceRecordDifferentialRevalidationError(
            "an archived source-status bridge is valid only for differential descriptor reuse, not complete receipt reissue"
        )
    archived_source_status_bridge: ValidatedArchivedSourceStatusProjectionBridge | None = None
    archived_source_status_bridge_record: dict[str, str] | None = None
    if archived_source_status_projection_bridge_path is not None:
        archived_source_status_bridge, archived_source_status_bridge_record, bridge_error = (
            _archived_source_status_projection_bridge_context(
                bridge_path=archived_source_status_projection_bridge_path,
                paper=paper,
                paper_dir=ROOT / "papers" / paper,
                prior_raw_audit=prior_raw_audit,
                prior_raw_audit_path=prior_raw_audit_path,
                prior_judgments=prior_judgments,
                prior_judgments_path=prior_judgments_path,
                current_raw_audit=current_raw_audit,
                current_raw_audit_path=current_raw_audit_path,
            )
        )
        if bridge_error or archived_source_status_bridge is None or archived_source_status_bridge_record is None:
            raise SourceRecordDifferentialRevalidationError(
                "archived source-status projection bridge is invalid: " + bridge_error
            )
    attested_current_revalidation: dict[str, object] | None = None
    if require_complete_reusable_section_identity:
        for path, payload, label in (
            (prior_raw_audit_path, prior_raw_audit, "prior raw audit"),
            (current_raw_audit_path, current_raw_audit, "current raw audit"),
            (prior_judgments_path, prior_judgments, "prior judgment sidecar"),
        ):
            if file_error := _exact_json_file_payload_error(path, payload, label=label):
                raise SourceRecordDifferentialRevalidationError(file_error)
        current_revalidation_metadata = prior_judgments.get(
            "current_semantic_revalidation"
        )
        if isinstance(current_revalidation_metadata, Mapping):
            if prior_current_revalidation_attestation_path is None:
                raise SourceRecordDifferentialRevalidationError(
                    "complete receipt reissue of an attested candidate requires its exact attestation path"
                )
            attested_current_revalidation, attestation_error = (
                _complete_reissue_attested_current_revalidation_record(
                    paper=paper,
                    paper_dir=ROOT / "papers" / paper,
                    raw_audit=prior_raw_audit,
                    candidate_sidecar=prior_judgments,
                    candidate_sidecar_path=prior_judgments_path,
                    attestation_path=prior_current_revalidation_attestation_path,
                )
            )
            if attestation_error or attested_current_revalidation is None:
                raise SourceRecordDifferentialRevalidationError(
                    "complete receipt reissue candidate current revalidation is invalid: "
                    + attestation_error
                )
        elif prior_current_revalidation_attestation_path is not None:
            raise SourceRecordDifferentialRevalidationError(
                "complete receipt reissue was given a current-revalidation attestation but the candidate sidecar has no matching metadata"
            )

    prior_groups, prior_group_errors = _raw_item_groups(prior_raw_audit)
    current_groups, current_group_errors = _raw_item_groups(current_raw_audit)
    complete_reissue_identity: dict[str, object] | None = None
    if require_complete_reusable_section_identity:
        if set(raw_judgments) != set(prior_groups):
            missing = sorted(set(prior_groups) - set(raw_judgments))
            extra = sorted(set(raw_judgments) - set(prior_groups))
            raise SourceRecordDifferentialRevalidationError(
                "complete receipt reissue requires an exact candidate response ledger"
                + (f"; missing={missing[:3]}" if missing else "")
                + (f"; extra={extra[:3]}" if extra else "")
            )
        if prior_group_errors or current_group_errors:
            raise SourceRecordDifferentialRevalidationError(
                "complete receipt reissue requires generated groups without raw grouping errors"
            )
        prior_identity, prior_identity_error = _complete_reusable_section_identity(
            prior_raw_audit, prior_groups
        )
        current_identity, current_identity_error = _complete_reusable_section_identity(
            current_raw_audit, current_groups
        )
        prior_aggregate, prior_aggregate_error = (
            _complete_reissue_aggregate_metadata_identity(prior_raw_audit)
        )
        current_aggregate, current_aggregate_error = (
            _complete_reissue_aggregate_metadata_identity(current_raw_audit)
        )
        if prior_identity_error or prior_identity is None:
            raise SourceRecordDifferentialRevalidationError(
                "complete receipt reissue prior identity is invalid: "
                + prior_identity_error
            )
        if current_identity_error or current_identity is None:
            raise SourceRecordDifferentialRevalidationError(
                "complete receipt reissue current identity is invalid: "
                + current_identity_error
            )
        if prior_aggregate_error or prior_aggregate is None:
            raise SourceRecordDifferentialRevalidationError(
                "complete receipt reissue prior aggregate metadata is invalid: "
                + prior_aggregate_error
            )
        if current_aggregate_error or current_aggregate is None:
            raise SourceRecordDifferentialRevalidationError(
                "complete receipt reissue current aggregate metadata is invalid: "
                + current_aggregate_error
            )
        complete_reissue_identity = {
            "schema": SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_SCHEMA,
            "mode": SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_MODE,
            "prior": prior_identity,
            "current": current_identity,
            "allowed_aggregate_metadata_delta": {
                "prior": prior_aggregate,
                "current": current_aggregate,
            },
        }
        complete_reissue_error = _complete_reusable_section_identity_error(
            complete_reissue_identity,
            prior_raw_audit=prior_raw_audit,
            prior_groups=prior_groups,
            current_raw_audit=current_raw_audit,
            current_groups=current_groups,
        )
        if complete_reissue_error:
            raise SourceRecordDifferentialRevalidationError(complete_reissue_error)
    prior_index = _descriptor_index(prior_groups)
    current_index = _descriptor_index(current_groups)
    archived_source_status_normalized_index: dict[
        str, list[tuple[str, Mapping[str, object], bool]]
    ] = {}
    archived_source_status_normalized_groups: dict[str, Mapping[str, object]] = {}
    archived_source_status_normalized_errors: dict[str, str] = {}
    if archived_source_status_bridge is not None:
        (
            archived_source_status_normalized_index,
            archived_source_status_normalized_groups,
            archived_source_status_normalized_errors,
        ) = _archived_source_status_projection_normalized_index(
            prior_groups, archived_source_status_bridge
        )
    reuse_exclusion_reasons, reuse_exclusions_record = (
        _current_reuse_exclusion_record(
            reuse_exclusions_path,
            paper=paper,
            current_raw_audit=current_raw_audit,
            current_descriptor_index=current_index,
        )
    )
    prior_provenance = _raw_audit_provenance(prior_raw_audit, prior_raw_audit_path)
    current_provenance = _raw_audit_provenance(current_raw_audit, current_raw_audit_path)
    prior_digest = prior_provenance["source_record_audit_sha256"]

    items: dict[str, dict[str, Any]] = {}
    decisions: list[dict[str, str]] = []
    preserved_current_keys: set[str] = set()

    # Ordinary reuse matches only through a unique descriptor class.  The
    # opt-in complete-receipt path is different: it retains the same sidecar
    # storage address only after the complete prior/current raw group at that
    # address is proven identical.  It never remaps a renamed key.
    for prior_key, prior_group in sorted(prior_groups.items()):
        raw_value = raw_judgments.get(prior_key)
        if not isinstance(raw_value, Mapping):
            decisions.append(
                {
                    "prior_judgment_key": prior_key,
                    "status": "not_reused",
                    "reason": "no prior saved response for this generated group",
                }
            )
            continue
        if prior_key in prior_group_errors:
            decisions.append(
                {
                    "prior_judgment_key": prior_key,
                    "status": "not_reused",
                    "reason": "prior raw group is malformed",
                }
            )
            continue
        descriptor_sha = _sha256(prior_group.get("descriptor_sha256"))
        comparison_prior_group: Mapping[str, object] = prior_group
        comparison_descriptor_sha = descriptor_sha
        archived_source_status_bridge_used = False
        complete_group_identity: dict[str, object] | None = None
        source_free_recursive_identity: dict[str, object] | None = None
        source_free_content_fallback_used = False
        if require_complete_reusable_section_identity:
            # A key is not used as a semantic matcher here. It is a direct
            # ledger address that must still name an exact full raw group on
            # both authenticated receipts. A rename therefore fails closed.
            current_key = prior_key
            current_group = current_groups.get(current_key)
            if not isinstance(current_group, Mapping):
                decisions.append(
                    {
                        "prior_judgment_key": prior_key,
                        "status": "not_reused",
                        "reason": "complete receipt reissue current raw group is absent at the archived storage address",
                    }
                )
                continue
            prior_raw_group, prior_raw_group_error = (
                _complete_reissue_raw_group_identity(prior_group)
            )
            current_raw_group, current_raw_group_error = (
                _complete_reissue_raw_group_identity(current_group)
            )
            if prior_raw_group_error or prior_raw_group is None:
                decisions.append(
                    {
                        "prior_judgment_key": prior_key,
                        "status": "not_reused",
                        "reason": "complete receipt reissue prior raw group is invalid: "
                        + prior_raw_group_error,
                    }
                )
                continue
            if current_raw_group_error or current_raw_group is None:
                decisions.append(
                    {
                        "prior_judgment_key": prior_key,
                        "current_judgment_key": current_key,
                        "status": "not_reused",
                        "reason": "complete receipt reissue current raw group is invalid: "
                        + current_raw_group_error,
                    }
                )
                continue
            complete_group_identity = {
                "schema": SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_SCHEMA,
                "prior": prior_raw_group,
                "current": current_raw_group,
            }
            if group_identity_error := _complete_reissue_raw_group_identity_error(
                complete_group_identity,
                prior_group=prior_group,
                current_group=current_group,
            ):
                decisions.append(
                    {
                        "prior_judgment_key": prior_key,
                        "current_judgment_key": current_key,
                        "status": "not_reused",
                        "reason": group_identity_error,
                    }
                )
                continue
        else:
            if reuse_error := _group_differential_reuse_error(
                prior_group, response=raw_value
            ):
                decisions.append(
                    {
                        "prior_judgment_key": prior_key,
                        "status": "not_reused",
                        "reason": reuse_error,
                    }
                )
                continue
            prior_matches = prior_index.get(descriptor_sha, [])
            current_matches = current_index.get(descriptor_sha, [])
            if len(prior_matches) == 1 and len(current_matches) == 1:
                current_key, current_group = current_matches[0]
            else:
                # A source-free recursively audited group can have duplicate
                # semantic descriptors because a field/record spelling is
                # deliberately not semantic identity.  It may select a
                # current candidate through its complete name-free raw content
                # only when that candidate is one-to-one in the *current*
                # descriptor class.  The strict full raw-group witness below
                # still rejects any navigation or generated-content change.
                prior_source_free_candidate, prior_source_free_candidate_error = (
                    _source_free_recursive_structural_identity(
                        prior_group, response=raw_value
                    )
                )
                content_matches: list[tuple[str, Mapping[str, object]]] = []
                if (
                    not prior_source_free_candidate_error
                    and prior_source_free_candidate is not None
                ):
                    content_identity = prior_source_free_candidate.get(
                        "semantic_content_identity"
                    )
                    if isinstance(content_identity, Mapping):
                        content_matches = _source_free_recursive_content_identity_matches(
                            current_matches, target=content_identity
                        )
                if len(content_matches) == 1:
                    current_key, current_group = content_matches[0]
                    source_free_content_fallback_used = True
                else:
                    normalized_group = archived_source_status_normalized_groups.get(
                        prior_key
                    )
                    normalized_descriptor_sha = (
                        _sha256(normalized_group.get("descriptor_sha256"))
                        if isinstance(normalized_group, Mapping)
                        else ""
                    )
                    normalized_matches = (
                        archived_source_status_normalized_index.get(
                            normalized_descriptor_sha, []
                        )
                        if normalized_descriptor_sha
                        else []
                    )
                    changed_by_bridge = bool(
                        len(normalized_matches) == 1
                        and normalized_matches[0][0] == prior_key
                        and normalized_matches[0][2]
                    )
                    current_matches = current_index.get(
                        normalized_descriptor_sha, []
                    )
                    if (
                        prior_key in archived_source_status_normalized_errors
                        or not isinstance(normalized_group, Mapping)
                        or not changed_by_bridge
                        or len(normalized_matches) != 1
                        or len(current_matches) != 1
                    ):
                        decisions.append(
                            {
                                "prior_judgment_key": prior_key,
                                "status": "not_reused",
                                "reason": (
                                    "prior/current semantic descriptor is absent or ambiguous"
                                    if prior_key
                                    not in archived_source_status_normalized_errors
                                    else "archived source-status bridge could not normalize the prior semantic group"
                                ),
                            }
                        )
                        continue
                    _normalized_key, comparison_prior_group, _normalized_changed = (
                        normalized_matches[0]
                    )
                    comparison_descriptor_sha = normalized_descriptor_sha
                    current_key, current_group = current_matches[0]
                    archived_source_status_bridge_used = True
            if reuse_error := _group_differential_reuse_error(
                current_group, response=raw_value
            ):
                decisions.append(
                    {
                        "prior_judgment_key": prior_key,
                        "current_judgment_key": current_key,
                        "status": "not_reused",
                        "reason": reuse_error,
                    }
                )
                continue
            if source_free_content_fallback_used and (
                _group_has_semantic_model_obligation(prior_group)
                or _group_has_semantic_model_obligation(current_group)
            ):
                decisions.append(
                    {
                        "prior_judgment_key": prior_key,
                        "current_judgment_key": current_key,
                        "status": "not_reused",
                        "reason": "source-free recursive content fallback cannot select a semantic-model group",
                    }
                )
                continue
            prior_source_free_identity, prior_source_free_error = (
                _source_free_recursive_structural_identity(
                    comparison_prior_group, response=raw_value
                )
            )
            current_source_free_identity, current_source_free_error = (
                _source_free_recursive_structural_identity(
                    current_group, response=raw_value
                )
            )
            if prior_source_free_error or current_source_free_error:
                decisions.append(
                    {
                        "prior_judgment_key": prior_key,
                        "current_judgment_key": current_key,
                        "status": "not_reused",
                        "reason": (
                            prior_source_free_error
                            or current_source_free_error
                        ),
                    }
                )
                continue
            if (prior_source_free_identity is None) != (
                current_source_free_identity is None
            ):
                decisions.append(
                    {
                        "prior_judgment_key": prior_key,
                        "current_judgment_key": current_key,
                        "status": "not_reused",
                        "reason": "source-free recursive structural lane differs between prior and current groups",
                    }
                )
                continue
            if prior_source_free_identity is not None:
                if canonical_digest_payload(prior_source_free_identity) != canonical_digest_payload(
                    current_source_free_identity
                ):
                    decisions.append(
                        {
                            "prior_judgment_key": prior_key,
                            "current_judgment_key": current_key,
                            "status": "not_reused",
                            "reason": "source-free recursive full raw-member identity differs",
                        }
                    )
                    continue
                source_free_recursive_identity = (
                    prior_source_free_identity
                    if source_free_content_fallback_used
                    else {
                        "schema": prior_source_free_identity["schema"],
                        "raw_group_identity": prior_source_free_identity[
                            "raw_group_identity"
                        ],
                    }
                )
        if canonical_digest_payload(comparison_prior_group["descriptor"]) != canonical_digest_payload(
            current_group["descriptor"]
        ):
            decisions.append(
                {
                    "prior_judgment_key": prior_key,
                    "status": "not_reused",
                    "reason": "prior/current exact semantic descriptor differs",
                }
            )
            continue
        exclusion_reason = reuse_exclusion_reasons.get(comparison_descriptor_sha)
        if exclusion_reason is not None:
            decisions.append(
                {
                    "prior_judgment_key": prior_key,
                    "current_judgment_key": current_key,
                    "current_group_semantic_descriptor_sha256": comparison_descriptor_sha,
                    "status": "not_reused",
                    "reason": (
                        "reviewer required fresh current semantic revalidation: "
                        + exclusion_reason
                    ),
                }
            )
            continue
        judgment_error = _judgment_metadata_error(
            raw_value,
            prior_judgments,
            prior_group,
            prior_audit_digest=prior_digest,
        )
        if judgment_error:
            decisions.append(
                {
                    "prior_judgment_key": prior_key,
                    "status": "not_reused",
                    "reason": judgment_error,
                }
            )
            continue
        if current_key in items:
            # A descriptor class was unique above. This guards future changes
            # to grouping/indexing before a second response can race for one
            # current obligation.
            decisions.append(
                {
                    "prior_judgment_key": prior_key,
                    "status": "not_reused",
                    "reason": "two prior responses resolve to one current semantic group",
                }
            )
            continue
        inherited = _materialize_prior_response(raw_value, prior_judgments)
        if require_complete_reusable_section_identity:
            semantic_association_rebind = None
            rebind_error = _complete_reissue_response_semantic_association_error(
                inherited, prior_group
            ) or _complete_reissue_response_semantic_association_error(
                inherited, current_group
            )
        else:
            effective_inherited = (
                rebound_archived_source_status_response(
                    inherited, archived_source_status_bridge
                )
                if archived_source_status_bridge_used
                else inherited
            )
            if effective_inherited is None:
                semantic_association_rebind, rebind_error = (
                    None,
                    "archived source-status bridge would bind the response to multiple current semantic associations",
                )
            else:
                semantic_association_rebind, rebind_error = (
                    _semantic_association_rebind_receipt(
                        effective_inherited,
                        prior_group=comparison_prior_group,
                        current_group=current_group,
                    )
                )
        if rebind_error:
            decisions.append(
                {
                    "prior_judgment_key": prior_key,
                    "current_judgment_key": current_key,
                    "status": "not_reused",
                    "reason": rebind_error,
                }
            )
            continue
        overlay_metadata: dict[str, Any] = {
            "schema": SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_SCHEMA,
            "policy_version": SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_POLICY_VERSION,
            "prior_judgment_key": prior_key,
            "current_judgment_key": current_key,
            "prior_raw_audit": prior_provenance,
            "current_raw_audit": current_provenance,
            "prior_group_semantic_descriptor": prior_group["descriptor"],
            "prior_group_semantic_descriptor_sha256": prior_group[
                "descriptor_sha256"
            ],
            "current_group_semantic_descriptor": current_group["descriptor"],
            "current_group_semantic_descriptor_sha256": current_group[
                "descriptor_sha256"
            ],
        }
        if archived_source_status_bridge_used:
            if archived_source_status_bridge_record is None:
                raise SourceRecordDifferentialRevalidationError(
                    "archived source-status bridge reuse lacks bridge provenance"
                )
            overlay_metadata[ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FIELD] = (
                copy.deepcopy(archived_source_status_bridge_record)
            )
            overlay_metadata[
                ARCHIVED_SOURCE_STATUS_PROJECTION_NORMALIZED_DESCRIPTOR_FIELD
            ] = copy.deepcopy(comparison_prior_group["descriptor"])
            overlay_metadata[
                ARCHIVED_SOURCE_STATUS_PROJECTION_NORMALIZED_DESCRIPTOR_SHA256_FIELD
            ] = comparison_descriptor_sha
        if semantic_association_rebind is not None:
            overlay_metadata[SEMANTIC_ASSOCIATION_REBIND_FIELD] = (
                semantic_association_rebind
            )
        if complete_group_identity is not None:
            overlay_metadata[SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_FIELD] = (
                complete_group_identity
            )
        if source_free_recursive_identity is not None:
            overlay_metadata[SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_FIELD] = (
                source_free_recursive_identity
            )
        # A prior current sidecar can itself have been materialized from an
        # authenticated differential overlay.  Preserve that receipt before
        # issuing the next overlay instead of overwriting the chain.
        prior_history = inherited.get(
            SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_HISTORY_FIELD
        )
        existing_differential = inherited.get(
            SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD
        )
        if existing_differential is not None:
            if isinstance(prior_history, list):
                history = copy.deepcopy(prior_history)
            elif prior_history is None:
                history = []
            else:
                raise SourceRecordDifferentialRevalidationError(
                    "prior source-record judgment has malformed differential-revalidation history"
                )
            if not isinstance(existing_differential, Mapping):
                raise SourceRecordDifferentialRevalidationError(
                    "prior source-record judgment has malformed differential-revalidation provenance"
                )
            history.append(copy.deepcopy(dict(existing_differential)))
            inherited[SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_HISTORY_FIELD] = history
        inherited[SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD] = overlay_metadata
        items[current_key] = inherited
        preserved_current_keys.add(current_key)
        decisions.append(
            {
                "prior_judgment_key": prior_key,
                "current_judgment_key": current_key,
                "status": "reused",
                "reason": (
                    "exact complete raw-group identity"
                    if complete_group_identity is not None
                    else "unique exact semantic descriptor match"
                ),
            }
        )

    for key in sorted(set(current_group_errors)):
        decisions.append(
            {
                "current_judgment_key": key,
                "status": "manual_review_required",
                "reason": "current raw group is malformed",
            }
        )
    manual_review_required = [
        {
            "current_judgment_key": key,
            "current_group_semantic_descriptor_sha256": group["descriptor_sha256"],
            "reason": reuse_exclusion_reasons.get(
                _sha256(group.get("descriptor_sha256")),
                _group_differential_reuse_error(group)
                or "no unique archived descriptor-identical prior response",
            ),
        }
        for key, group in sorted(current_groups.items())
        if key not in preserved_current_keys
    ]
    if require_complete_reusable_section_identity and (
        manual_review_required
        or len(items) != len(current_groups)
        or set(items) != set(current_groups)
    ):
        raise SourceRecordDifferentialRevalidationError(
            "complete receipt reissue requires one authenticated reused response for every current generated group"
        )

    payload: dict[str, Any] = {
        "schema": 1,
        "artifact_kind": SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ARTIFACT_KIND,
        "revalidation_schema": SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_SCHEMA,
        "revalidation_policy_version": SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_POLICY_VERSION,
        "paper": paper,
        "prompt_version": SOURCE_RECORD_V10_PROMPT_VERSION,
        "source_record_policy_version": SOURCE_RECORD_V10_PROMPT_VERSION,
        "prior_raw_audit": prior_provenance,
        "prior_judgments": {
            "path": _stable_provenance_path(prior_judgments_path),
            "file_sha256": _file_sha256(prior_judgments_path),
            "source_record_audit_sha256": prior_digest,
        },
        "current_raw_audit": current_provenance,
        "items": items,
        "decisions": decisions,
        "manual_review_required": manual_review_required,
    }
    if reuse_exclusions_record is not None:
        payload[SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_FIELD] = (
            reuse_exclusions_record
        )
    if archived_source_status_bridge_record is not None:
        payload[ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FIELD] = (
            copy.deepcopy(archived_source_status_bridge_record)
        )
    if complete_reissue_identity is not None:
        payload[SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_FIELD] = (
            complete_reissue_identity
        )
    if attested_current_revalidation is not None:
        payload[SOURCE_RECORD_COMPLETE_REISSUE_CURRENT_REVALIDATION_FIELD] = (
            attested_current_revalidation
        )
    stamp_source_record_differential_revalidation(payload)
    return payload


def _provenance_error(value: object, expected: Mapping[str, str]) -> str:
    if not isinstance(value, Mapping):
        return "is missing"
    for field, expected_value in expected.items():
        if str(value.get(field) or "") != str(expected_value):
            return f"has a different `{field}`"
    return ""


def _archived_source_status_projection_bridge_record_shape_error(value: object) -> str:
    if not isinstance(value, Mapping):
        return "is not an object"
    try:
        _repository_provenance_path(value.get("path"))
    except SourceRecordDifferentialRevalidationError as exc:
        return "has an invalid path: " + str(exc)
    for field in ("file_sha256", "receipt_sha256"):
        if not _sha256(value.get(field)):
            return f"has no valid `{field}`"
    return ""


def _source_free_recursive_structural_identity_shape_error(value: object) -> str:
    """Check serialized mapless-recursive witness shape before raw replay."""

    if not isinstance(value, Mapping):
        return "is not an object"
    if value.get("schema") != SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_SCHEMA:
        return "has an unsupported schema"
    if set(value) not in (
        {"schema", "raw_group_identity"},
        {"schema", "raw_group_identity", "semantic_content_identity"},
    ):
        return "has unsupported fields"
    raw_identity = value.get("raw_group_identity")
    if (
        not isinstance(raw_identity, Mapping)
        or set(raw_identity) != {"schema", "member_count", "canonical_sha256"}
        or raw_identity.get("schema")
        != SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_SCHEMA
        or not isinstance(raw_identity.get("member_count"), int)
        or raw_identity.get("member_count", 0) < 1
        or not _sha256(raw_identity.get("canonical_sha256"))
    ):
        return "has an invalid raw-group identity"
    content_identity = value.get("semantic_content_identity")
    if content_identity is not None and (
        not isinstance(content_identity, Mapping)
        or set(content_identity) != {"schema", "member_count", "canonical_sha256"}
        or content_identity.get("schema")
        != SOURCE_FREE_RECURSIVE_CONTENT_IDENTITY_SCHEMA
        or not isinstance(content_identity.get("member_count"), int)
        or content_identity.get("member_count", 0) < 1
        or not _sha256(content_identity.get("canonical_sha256"))
    ):
        return "has an invalid semantic-content identity"
    return ""


def _overlay_item_error(
    key: str, value: Mapping[str, Any], payload: Mapping[str, Any]
) -> str:
    metadata = value.get(SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD)
    if not isinstance(metadata, Mapping):
        return "is missing differential-revalidation provenance"
    if metadata.get("schema") != SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_SCHEMA:
        return "has an unsupported differential-revalidation schema"
    if (
        str(metadata.get("policy_version") or "").strip()
        != SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_POLICY_VERSION
    ):
        return "has an unsupported differential-revalidation policy"
    prior_key = str(metadata.get("prior_judgment_key") or "").strip()
    current_key = str(metadata.get("current_judgment_key") or "").strip()
    if not prior_key or not current_key:
        return "does not identify prior/current generated groups"
    descriptors: list[tuple[str, str]] = []
    for prefix in ("prior", "current"):
        descriptor = metadata.get(prefix + "_group_semantic_descriptor")
        digest = _sha256(metadata.get(prefix + "_group_semantic_descriptor_sha256"))
        if not isinstance(descriptor, Mapping) or not digest:
            return f"lacks {prefix} semantic descriptor provenance"
        if digest != _canonical_digest(descriptor):
            return f"has a malformed {prefix} semantic descriptor digest"
        descriptors.append((prefix, digest))
    bridge_record = metadata.get(ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FIELD)
    if bridge_record is None:
        if descriptors[0][1] != descriptors[1][1]:
            return "records different prior/current semantic descriptors"
        if (
            ARCHIVED_SOURCE_STATUS_PROJECTION_NORMALIZED_DESCRIPTOR_FIELD in metadata
            or ARCHIVED_SOURCE_STATUS_PROJECTION_NORMALIZED_DESCRIPTOR_SHA256_FIELD
            in metadata
        ):
            return "records a normalized archived source-status descriptor without a bridge"
    else:
        if error := _archived_source_status_projection_bridge_record_shape_error(
            bridge_record
        ):
            return "has invalid archived source-status bridge provenance: " + error
        top_level_bridge = payload.get(ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FIELD)
        if not isinstance(top_level_bridge, Mapping) or dict(bridge_record) != dict(
            top_level_bridge
        ):
            return "does not bind its archived source-status bridge to the overlay"
        normalized_descriptor = metadata.get(
            ARCHIVED_SOURCE_STATUS_PROJECTION_NORMALIZED_DESCRIPTOR_FIELD
        )
        normalized_digest = _sha256(
            metadata.get(
                ARCHIVED_SOURCE_STATUS_PROJECTION_NORMALIZED_DESCRIPTOR_SHA256_FIELD
            )
        )
        if (
            not isinstance(normalized_descriptor, Mapping)
            or not normalized_digest
            or normalized_digest != _canonical_digest(normalized_descriptor)
        ):
            return "has malformed normalized archived source-status descriptor provenance"
        if (
            normalized_digest != descriptors[1][1]
            or canonical_digest_payload(normalized_descriptor)
            != canonical_digest_payload(metadata.get("current_group_semantic_descriptor"))
        ):
            return "does not make the normalized archived descriptor exactly current"
    complete_reissue = SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_FIELD in payload
    complete_group_identity = metadata.get(
        SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_FIELD
    )
    if complete_reissue:
        if error := _complete_reissue_raw_group_identity_error(complete_group_identity):
            return error
    elif complete_group_identity is not None:
        return "records a complete receipt raw-group identity outside complete receipt mode"
    source_free_recursive_identity = metadata.get(
        SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_FIELD
    )
    if source_free_recursive_identity is not None:
        if complete_reissue:
            return "records a source-free recursive structural identity inside complete receipt mode"
        if bridge_record is not None:
            return "combines source-free recursive identity with a source-status bridge"
        if error := _source_free_recursive_structural_identity_shape_error(
            source_free_recursive_identity
        ):
            return "has invalid source-free recursive structural identity: " + error
    for field in ("prior_raw_audit", "current_raw_audit"):
        error = _provenance_error(metadata.get(field), payload.get(field, {}))
        if error:
            return f"{field} {error} from the overlay receipt"
    if not str(value.get("classification") or "").strip():
        return "has no inherited classification"
    if (
        str(value.get("prompt_version") or "").strip()
        != SOURCE_RECORD_V10_PROMPT_VERSION
    ):
        return "does not retain the v10 prompt version"
    if not _sha256(value.get("source_record_audit_sha256")):
        return "does not retain prior aggregate provenance"
    if not str(value.get("validator") or "").strip() or not str(
        value.get("validated_at") or ""
    ).strip():
        return "does not retain validator/timestamp metadata"
    rebind = metadata.get(SEMANTIC_ASSOCIATION_REBIND_FIELD)
    if "semantic_association_sha256" in value:
        # v1 overlays predate the persisted receipt.  The loader admits those
        # only after recomputing it from exact archived/current raw groups;
        # new overlays persist it and must have valid transport shape here.
        if rebind is not None and (
            error := _semantic_association_rebind_receipt_error(rebind)
        ):
            return "has invalid semantic-association rebind provenance: " + error
    elif rebind is not None:
        return "records semantic-association rebind provenance without a response pin"
    history = value.get(SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_HISTORY_FIELD)
    if history is not None and (
        not isinstance(history, list)
        or not history
        or not all(isinstance(entry, Mapping) for entry in history)
    ):
        return "has malformed prior differential-revalidation history"
    return ""


def _overlay_reuse_exclusions_error(
    payload: Mapping[str, Any],
    *,
    paper: str,
    current_raw_audit: Mapping[str, Any] | None = None,
) -> str:
    """Validate an optional reviewed exclusion artifact without name matching."""

    if SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_FIELD not in payload:
        return ""
    return _reuse_exclusions_record_error(
        payload.get(SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_FIELD),
        paper=paper,
        current_raw_audit=current_raw_audit,
    )


def _complete_reissue_identity_shape_error(identity: object) -> str:
    """Check the serialized shape before the loader recomputes it from raw."""

    if not isinstance(identity, Mapping):
        return "complete receipt reissue identity is not an object"
    if identity.get("schema") != SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_SCHEMA:
        return "complete receipt reissue has an unsupported identity schema"
    if (
        str(identity.get("mode") or "").strip()
        != SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_MODE
    ):
        return "complete receipt reissue has the wrong identity mode"
    for field in ("prior", "current"):
        if not isinstance(identity.get(field), Mapping):
            return f"complete receipt reissue lacks `{field}` reusable-section identity"
    aggregate = identity.get("allowed_aggregate_metadata_delta")
    if not isinstance(aggregate, Mapping):
        return "complete receipt reissue lacks aggregate metadata identity"
    for field in ("prior", "current"):
        if not isinstance(aggregate.get(field), Mapping):
            return f"complete receipt reissue lacks `{field}` aggregate metadata identity"
    return ""


def _complete_reissue_attested_current_revalidation_shape_error(value: object) -> str:
    """Check only serialized provenance shape before raw-side revalidation."""

    if not isinstance(value, Mapping):
        return "complete receipt reissue attested current-revalidation provenance is not an object"
    if value.get("schema") != SOURCE_RECORD_COMPLETE_REISSUE_CURRENT_REVALIDATION_SCHEMA:
        return "complete receipt reissue attested current-revalidation provenance has an unsupported schema"
    for field in ("candidate_sidecar", "attestation"):
        record = value.get(field)
        if not isinstance(record, Mapping):
            return f"complete receipt reissue attested current-revalidation lacks `{field}` provenance"
        try:
            _repository_provenance_path(record.get("path"))
        except SourceRecordDifferentialRevalidationError as exc:
            return (
                "complete receipt reissue attested current-revalidation has invalid "
                f"`{field}` path: {exc}"
            )
        if not _sha256(record.get("file_sha256")):
            return (
                "complete receipt reissue attested current-revalidation has malformed "
                f"`{field}` file hash"
            )
    if not _sha256(value.get("archived_raw_source_record_audit_sha256")):
        return "complete receipt reissue attested current-revalidation has no archived raw receipt"
    return ""


def source_record_differential_revalidation_overlay_error(
    payload: object, *, paper: str
) -> str:
    """Validate serialized overlay transport before per-item current checks."""

    if not isinstance(payload, Mapping):
        return "differential revalidation overlay is not an object"
    if payload.get("schema") != 1:
        return "differential revalidation overlay lacks sidecar schema 1"
    if (
        str(payload.get("artifact_kind") or "").strip()
        != SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ARTIFACT_KIND
    ):
        return "differential revalidation overlay has the wrong artifact kind"
    if payload.get("revalidation_schema") != SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_SCHEMA:
        return "differential revalidation overlay has an unsupported schema"
    if (
        str(payload.get("revalidation_policy_version") or "").strip()
        != SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_POLICY_VERSION
    ):
        return "differential revalidation overlay has an unsupported policy"
    if payload.get("paper") != paper:
        return "differential revalidation overlay belongs to another paper"
    if (
        str(payload.get("prompt_version") or "").strip()
        != SOURCE_RECORD_V10_PROMPT_VERSION
        or str(payload.get("source_record_policy_version") or "").strip()
        != SOURCE_RECORD_V10_PROMPT_VERSION
    ):
        return "differential revalidation overlay does not record the v10 prompt family"
    if _payload_is_non_evidence(payload):
        return "differential revalidation overlay is marked non-evidence"
    integrity = _sha256(payload.get(SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_INTEGRITY_FIELD))
    if not integrity:
        return "differential revalidation overlay lacks an integrity digest"
    if integrity != source_record_differential_revalidation_sha256(payload):
        return "differential revalidation overlay integrity digest does not match"
    for field in ("prior_raw_audit", "current_raw_audit"):
        provenance = payload.get(field)
        if not isinstance(provenance, Mapping):
            return f"differential revalidation overlay lacks {field} provenance"
        try:
            _repository_provenance_path(provenance.get("path"))
        except SourceRecordDifferentialRevalidationError as exc:
            return f"differential revalidation overlay has invalid {field} path: {exc}"
        for digest_field in (
            "file_sha256",
            "source_record_audit_sha256",
            "source_record_audit_integrity_sha256",
        ):
            if not _sha256(provenance.get(digest_field)):
                return (
                    "differential revalidation overlay has malformed "
                    f"{field}.{digest_field}"
                )
    prior_judgments = payload.get("prior_judgments")
    if not isinstance(prior_judgments, Mapping) or not _sha256(
        prior_judgments.get("file_sha256")
    ):
        return "differential revalidation overlay lacks prior-sidecar provenance"
    try:
        _repository_provenance_path(prior_judgments.get("path"))
    except SourceRecordDifferentialRevalidationError as exc:
        return f"differential revalidation overlay has invalid prior-sidecar path: {exc}"
    if error := _overlay_reuse_exclusions_error(payload, paper=paper):
        return "differential revalidation overlay has invalid reuse exclusions: " + error
    if ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FIELD in payload and (
        error := _archived_source_status_projection_bridge_record_shape_error(
            payload.get(ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FIELD)
        )
    ):
        return "differential revalidation overlay has invalid archived source-status bridge: " + error
    if SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_FIELD in payload and (
        error := _complete_reissue_identity_shape_error(
            payload.get(SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_FIELD)
        )
    ):
        return "differential revalidation overlay has invalid complete receipt reissue: " + error
    if (
        SOURCE_RECORD_COMPLETE_REISSUE_CURRENT_REVALIDATION_FIELD in payload
        and SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_FIELD not in payload
    ):
        return "differential revalidation overlay records attested current revalidation outside complete receipt mode"
    if SOURCE_RECORD_COMPLETE_REISSUE_CURRENT_REVALIDATION_FIELD in payload and (
        error := _complete_reissue_attested_current_revalidation_shape_error(
            payload.get(SOURCE_RECORD_COMPLETE_REISSUE_CURRENT_REVALIDATION_FIELD)
        )
    ):
        return "differential revalidation overlay has invalid attested current revalidation: " + error
    raw_items = payload.get("items")
    if not isinstance(raw_items, Mapping):
        return "differential revalidation overlay items are not an object"
    for raw_key, raw_value in raw_items.items():
        key = str(raw_key).strip()
        if not key or not isinstance(raw_value, Mapping):
            return "differential revalidation overlay has a malformed item"
        item_error = _overlay_item_error(key, raw_value, payload)
        if item_error:
            return f"differential revalidation item `{key}` {item_error}"
    return ""


def _archived_overlay_items_error(
    payload: Mapping[str, Any],
    *,
    prior_raw_audit: Mapping[str, Any],
    prior_judgments: Mapping[str, Any],
    prior_audit_digest: str,
) -> str:
    """Reauthenticate every serialized response against archived item evidence.

    This check is deliberately stronger than the overlay's transport check.
    It reads the exact sidecar bytes named by the overlay, recovers the prior
    group from the exact raw receipt, and re-runs the same metadata/group
    checks used at overlay issuance.  The serialized inherited response must
    then be byte-for-byte equivalent as JSON content to the archived response
    after only root metadata has been materialized.  Thus a stale sidecar root
    can never cause a blanket reuse, and a copied or altered overlay response
    cannot be accepted merely because it retained a prior storage key.
    """

    raw_items = payload.get("items")
    if not isinstance(raw_items, Mapping):
        return "overlay has no item ledger"
    prior_responses = prior_judgments.get("items") or prior_judgments.get(
        "field_judgments"
    )
    if not isinstance(prior_responses, Mapping):
        return "archived sidecar has no item ledger"
    prior_groups, prior_group_errors = _raw_item_groups(prior_raw_audit)
    if not prior_groups:
        return "archived raw audit has no generated judgment groups"
    complete_reissue = SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_FIELD in payload

    for serialized_key, serialized_value in raw_items.items():
        key = str(serialized_key or "").strip()
        if not key or not isinstance(serialized_value, Mapping):
            return "overlay has a malformed serialized item"
        metadata = serialized_value.get(
            SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD
        )
        if not isinstance(metadata, Mapping):
            return f"{key}: serialized item has no differential provenance"
        prior_key = str(metadata.get("prior_judgment_key") or "").strip()
        if not prior_key:
            return f"{key}: serialized item has no prior judgment key"
        if complete_reissue and str(
            metadata.get("current_judgment_key") or ""
        ).strip() != key:
            return f"{key}: complete receipt reissue changed its raw-group storage address"
        prior_group = prior_groups.get(prior_key)
        if prior_key in prior_group_errors or not isinstance(prior_group, Mapping):
            return f"{key}: archived prior group is missing or malformed"

        recorded_descriptor = metadata.get("prior_group_semantic_descriptor")
        recorded_descriptor_sha = _sha256(
            metadata.get("prior_group_semantic_descriptor_sha256")
        )
        actual_descriptor = prior_group.get("descriptor")
        actual_descriptor_sha = _sha256(prior_group.get("descriptor_sha256"))
        if (
            not isinstance(recorded_descriptor, Mapping)
            or not recorded_descriptor_sha
            or not isinstance(actual_descriptor, Mapping)
            or not actual_descriptor_sha
            or recorded_descriptor_sha != actual_descriptor_sha
            or recorded_descriptor_sha != _canonical_digest(recorded_descriptor)
            or canonical_digest_payload(recorded_descriptor)
            != canonical_digest_payload(actual_descriptor)
        ):
            return f"{key}: serialized prior semantic descriptor no longer matches archived raw"
        if complete_reissue:
            if group_identity_error := _complete_reissue_raw_group_identity_error(
                metadata.get(SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_FIELD),
                prior_group=prior_group,
            ):
                return f"{key}: {group_identity_error}"
        archived_response = prior_responses.get(prior_key)
        if not isinstance(archived_response, Mapping):
            return f"{key}: archived sidecar has no prior response"
        elif reuse_error := _group_differential_reuse_error(
            prior_group, response=archived_response
        ):
            return f"{key}: archived prior group is not reusable: {reuse_error}"
        recorded_source_free_recursive_identity = metadata.get(
            SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_FIELD
        )
        if recorded_source_free_recursive_identity is not None:
            if identity_error := _source_free_recursive_structural_identity_error(
                recorded_source_free_recursive_identity,
                group=prior_group,
                response=archived_response,
            ):
                return (
                    f"{key}: archived prior source-free recursive structural "
                    "identity is invalid: " + identity_error
                )
        if metadata_error := _judgment_metadata_error(
            archived_response,
            prior_judgments,
            prior_group,
            prior_audit_digest=prior_audit_digest,
        ):
            return f"{key}: archived prior response is invalid: {metadata_error}"
        if complete_reissue and (
            association_error := _complete_reissue_response_semantic_association_error(
                archived_response, prior_group
            )
        ):
            return f"{key}: archived prior response is invalid: {association_error}"

        expected = _materialize_prior_response(archived_response, prior_judgments)
        observed = dict(serialized_value)
        observed.pop(SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD, None)
        # A new overlay keeps an earlier overlay receipt in an ordered history.
        # Restore the immediate prior receipt before comparing to the archived
        # response.  The current semantic descriptor is independently checked
        # above, so this is provenance preservation rather than an identity
        # heuristic based on a storage key or route name.
        history = observed.pop(SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_HISTORY_FIELD, None)
        if history is not None:
            if not isinstance(history, list) or not history:
                return f"{key}: serialized response has malformed differential history"
            restored_history = copy.deepcopy(history)
            prior_metadata = restored_history.pop()
            if not isinstance(prior_metadata, Mapping):
                return f"{key}: serialized response has malformed differential history"
            observed[SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD] = dict(
                prior_metadata
            )
            if restored_history:
                observed[SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_HISTORY_FIELD] = (
                    restored_history
                )
        if canonical_digest_payload(observed) != canonical_digest_payload(expected):
            return f"{key}: serialized response differs from the archived materialized response"
    return ""


def _load_authenticated_source_record_differential_prior_raw(
    payload: Mapping[str, Any], *, paper: str
) -> tuple[dict[str, Any] | None, str]:
    """Return exact-byte-authenticated archived raw evidence, or an error.

    A historical sidecar can have a stale *root* aggregate receipt after a
    narrow earlier update while individual responses already carry the exact
    prior receipt.  That root value is not enough to discard those individual
    judgments, nor is it enough to trust them.  Every serialized overlay item
    is therefore revalidated below against the exact archived sidecar response
    and the exact archived raw group before this function admits the archive.
    """

    prior_provenance = payload.get("prior_raw_audit")
    prior_judgments_provenance = payload.get("prior_judgments")
    if not isinstance(prior_provenance, Mapping) or not isinstance(
        prior_judgments_provenance, Mapping
    ):
        return None, "overlay archive provenance is malformed"
    try:
        prior_raw_path = _repository_provenance_path(prior_provenance.get("path"))
        prior_judgments_path = _repository_provenance_path(
            prior_judgments_provenance.get("path")
        )
        prior_raw = _read_json_object(prior_raw_path)
        prior_judgments = _read_json_object(prior_judgments_path)
        actual_prior_provenance = _raw_audit_provenance(prior_raw, prior_raw_path)
    except (OSError, SourceRecordDifferentialRevalidationError) as exc:
        return None, f"could not authenticate archived differential evidence: {exc}"
    if _raw_audit_error(prior_raw, paper=paper, label="archived prior"):
        return None, "archived prior raw audit is not an admissible v10 receipt"
    if _provenance_error(prior_provenance, actual_prior_provenance):
        return None, "archived prior raw audit bytes or receipt differ from the overlay"
    if _file_sha256(prior_judgments_path) != str(
        prior_judgments_provenance.get("file_sha256") or ""
    ):
        return None, "archived prior judgment sidecar bytes differ from the overlay"
    if (
        prior_judgments.get("schema") != 1
        or prior_judgments.get("paper") != paper
        or _payload_is_non_evidence(prior_judgments)
        or str(prior_judgments.get("prompt_version") or "").strip()
        != SOURCE_RECORD_V10_PROMPT_VERSION
    ):
        return None, "archived prior judgment sidecar is not admissible v10 evidence"
    # The overlay itself must state the exact prior receipt even if the legacy
    # sidecar root is stale.  Individual overlay candidates are checked below;
    # no name- or root-level fallback is accepted.
    if _sha256(prior_judgments_provenance.get("source_record_audit_sha256")) != _sha256(
        prior_provenance.get("source_record_audit_sha256")
    ):
        return None, "overlay prior-sidecar provenance is not tied to the archived raw receipt"
    if not _sha256(prior_judgments.get("source_record_audit_sha256")):
        return None, "archived prior judgment sidecar has no aggregate receipt"
    if error := _archived_overlay_items_error(
        payload,
        prior_raw_audit=prior_raw,
        prior_judgments=prior_judgments,
        prior_audit_digest=_sha256(prior_provenance.get("source_record_audit_sha256")),
    ):
        return None, "archived differential response is not individually authenticated: " + error
    return prior_raw, ""


def _source_record_differential_revalidation_archive_error(
    payload: Mapping[str, Any], *, paper: str
) -> str:
    """Verify the archived evidence bytes once before any response is reused."""

    _prior_raw, error = _load_authenticated_source_record_differential_prior_raw(
        payload, paper=paper
    )
    return error


def source_record_differential_revalidation_item_current(
    value: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    current_raw_audit: Mapping[str, Any],
) -> tuple[str, bool]:
    """Return the uniquely matched current key and whether this item is current."""

    if _raw_audit_error(current_raw_audit, paper=paper, label="current"):
        return "", False
    canonical_path = paper_dir / "audit" / "source_record_audit.json"
    if not canonical_path.is_file():
        return "", False
    try:
        current_provenance = _raw_audit_provenance(current_raw_audit, canonical_path)
    except (OSError, SourceRecordDifferentialRevalidationError):
        return "", False
    groups, group_errors = _raw_item_groups(current_raw_audit)
    if group_errors:
        return "", False
    return _source_record_differential_revalidation_item_current_from_groups(
        value,
        current_provenance=current_provenance,
        groups=groups,
        descriptor_index=_descriptor_index(groups),
    )


def _source_record_differential_revalidation_item_current_from_groups(
    value: Mapping[str, Any],
    *,
    current_provenance: Mapping[str, str],
    groups: Mapping[str, Mapping[str, object]],
    descriptor_index: Mapping[str, list[tuple[str, Mapping[str, object]]]],
    complete_reissue: bool = False,
    prior_groups: Mapping[str, Mapping[str, object]] | None = None,
    archived_source_status_bridge: ValidatedArchivedSourceStatusProjectionBridge | None = None,
) -> tuple[str, bool]:
    """Check one inherited response against an already-authenticated raw index.

    The public single-item helper remains useful for callers that possess only
    one response.  Batch loaders must not repeat receipt validation or rebuild
    the potentially large generated-obligation projection for every response.
    """

    metadata = value.get(SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD)
    if not isinstance(metadata, Mapping):
        return "", False
    if _current_raw_provenance_error(
        metadata.get("current_raw_audit"), current_provenance
    ):
        return "", False
    descriptor = metadata.get("current_group_semantic_descriptor")
    descriptor_sha = _sha256(metadata.get("current_group_semantic_descriptor_sha256"))
    if not isinstance(descriptor, Mapping) or not descriptor_sha:
        return "", False
    if descriptor_sha != _canonical_digest(descriptor):
        return "", False
    if complete_reissue:
        # This path deliberately does not resolve descriptor duplicates. The
        # enclosing complete-reissue receipt and the per-item raw-group
        # identity instead bind this response to the same exact raw ledger
        # address. A renamed address is rejected by the archived-side check.
        current_key = str(metadata.get("current_judgment_key") or "").strip()
        current_group = groups.get(current_key)
        if not current_key or not isinstance(current_group, Mapping):
            return "", False
        if canonical_digest_payload(current_group.get("descriptor")) != canonical_digest_payload(
            descriptor
        ):
            return "", False
        if _complete_reissue_raw_group_identity_error(
            metadata.get(SOURCE_RECORD_COMPLETE_REISSUE_GROUP_IDENTITY_FIELD),
            current_group=current_group,
        ):
            return "", False
        if _complete_reissue_response_semantic_association_error(value, current_group):
            return "", False
        return current_key, True
    bridge_record = metadata.get(ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FIELD)
    if bridge_record is not None:
        if (
            not isinstance(bridge_record, Mapping)
            or not isinstance(archived_source_status_bridge, ValidatedArchivedSourceStatusProjectionBridge)
            or prior_groups is None
        ):
            return "", False
        prior_key = str(metadata.get("prior_judgment_key") or "").strip()
        prior_group = prior_groups.get(prior_key)
        if not prior_key or not isinstance(prior_group, Mapping):
            return "", False
        normalized_prior_group, changed, normalized_error = (
            _archived_source_status_projection_normalized_group(
                prior_group, archived_source_status_bridge
            )
        )
        normalized_descriptor = metadata.get(
            ARCHIVED_SOURCE_STATUS_PROJECTION_NORMALIZED_DESCRIPTOR_FIELD
        )
        normalized_digest = _sha256(
            metadata.get(
                ARCHIVED_SOURCE_STATUS_PROJECTION_NORMALIZED_DESCRIPTOR_SHA256_FIELD
            )
        )
        if (
            normalized_error
            or normalized_prior_group is None
            or not changed
            or not isinstance(normalized_descriptor, Mapping)
            or not normalized_digest
            or normalized_digest != _canonical_digest(normalized_descriptor)
            or canonical_digest_payload(normalized_prior_group.get("descriptor"))
            != canonical_digest_payload(normalized_descriptor)
        ):
            return "", False
        candidates = [
            (key, group)
            for key, group in descriptor_index.get(descriptor_sha, [])
            if canonical_digest_payload(group.get("descriptor"))
            == canonical_digest_payload(descriptor)
        ]
        if len(candidates) != 1:
            return "", False
        current_key, current_group = candidates[0]
        if canonical_digest_payload(normalized_prior_group.get("descriptor")) != canonical_digest_payload(
            current_group.get("descriptor")
        ):
            return "", False
        if _group_differential_reuse_error(current_group, response=value):
            return "", False
        return current_key, True
    source_free_recursive_identity = metadata.get(
        SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_FIELD
    )
    descriptor_candidates = [
        (key, group)
        for key, group in descriptor_index.get(descriptor_sha, [])
        if canonical_digest_payload(group.get("descriptor"))
        == canonical_digest_payload(descriptor)
    ]
    content_identity = (
        source_free_recursive_identity.get("semantic_content_identity")
        if isinstance(source_free_recursive_identity, Mapping)
        else None
    )
    candidates = (
        _source_free_recursive_content_identity_matches(
            descriptor_candidates, target=content_identity
        )
        if isinstance(content_identity, Mapping)
        else descriptor_candidates
    )
    if len(candidates) != 1:
        return "", False
    current_key, current_group = candidates[0]
    if isinstance(content_identity, Mapping) and _group_has_semantic_model_obligation(
        current_group
    ):
        return "", False
    if _group_differential_reuse_error(current_group, response=value):
        return "", False
    if source_free_recursive_identity is not None:
        if prior_groups is None:
            return "", False
        prior_key = str(metadata.get("prior_judgment_key") or "").strip()
        prior_group = prior_groups.get(prior_key)
        if not prior_key or not isinstance(prior_group, Mapping):
            return "", False
        if isinstance(content_identity, Mapping) and _group_has_semantic_model_obligation(
            prior_group
        ):
            return "", False
        if _source_free_recursive_structural_identity_error(
            source_free_recursive_identity,
            group=prior_group,
            response=value,
        ):
            return "", False
        current_identity, current_identity_error = (
            _source_free_recursive_structural_identity(
                current_group, response=value
            )
        )
        expected_current_identity = (
            current_identity
            if isinstance(content_identity, Mapping) or current_identity is None
            else {
                "schema": current_identity["schema"],
                "raw_group_identity": current_identity["raw_group_identity"],
            }
        )
        if (
            current_identity_error
            or current_identity is None
            or canonical_digest_payload(source_free_recursive_identity)
            != canonical_digest_payload(expected_current_identity)
        ):
            return "", False
    return current_key, True


def is_loaded_source_record_differential_revalidation_item(value: object) -> bool:
    return bool(
        isinstance(value, _LoadedSourceRecordDifferentialRevalidationItem)
        and value._source_record_differential_revalidation_loader_token
        is _LOADED_OVERLAY_ITEM_SENTINEL
        and isinstance(
            value.get(SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD), Mapping
        )
    )


def source_record_differential_revalidation_item_has_provenance(value: object) -> bool:
    return bool(
        isinstance(value, Mapping)
        and isinstance(
            value.get(SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD), Mapping
        )
    )


def copy_loaded_source_record_differential_revalidation_item(
    value: Mapping[str, Any], updates: Mapping[str, Any] | None = None
) -> dict[str, Any]:
    copied: dict[str, Any] = dict(value)
    if updates is not None:
        copied.update(updates)
    if is_loaded_source_record_differential_revalidation_item(value):
        return _LoadedSourceRecordDifferentialRevalidationItem(copied)
    return copied


def source_record_differential_revalidation_overlay_path(paper_dir: Path) -> Path:
    return paper_dir / "audit" / SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_FILENAME


def _canonical_current_administrative_projection_rebind_context(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    current_raw_audit_path: Path,
) -> tuple[ValidatedAdministrativeProjectionRebind | None, str]:
    """Load only the default receipt bound to the canonical receiving raw audit.

    Differential overlays may also be checked against explicit historical raw
    files.  Do not make a canonical receipt an accidental waiver for those
    archives: automatic transport is limited to the current canonical audit.
    A caller that needs a historical transport must issue a separate
    receipt-bound workflow rather than inheriting this one by path resemblance.
    """

    canonical_raw_path = paper_dir / "audit" / "source_record_audit.json"
    try:
        if current_raw_audit_path.resolve() != canonical_raw_path.resolve():
            return None, ""
    except OSError:
        return None, ""
    receipt_path = (
        paper_dir / "audit" / SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME
    )
    if not receipt_path.exists():
        return None, ""
    statement_map_path = paper_dir / "audit" / "paper_statement_map.json"
    try:
        statement_map = _read_json_object(statement_map_path)
    except SourceRecordDifferentialRevalidationError as exc:
        return None, "could not load current source map for administrative rebind: " + str(exc)
    context, _loaded_path, error = load_administrative_projection_rebind_context(
        paper=paper,
        paper_dir=paper_dir,
        raw_audit_path=current_raw_audit_path,
        raw_audit=current_raw_audit,
        statement_map_path=statement_map_path,
        statement_map=statement_map,
        receipt_path=receipt_path,
    )
    if error:
        return None, error
    if context is not None and not isinstance(
        context, ValidatedAdministrativeProjectionRebind
    ):
        return None, "administrative projection rebind did not yield a validated context"
    return context, ""


def load_current_source_record_differential_revalidation_items(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    *,
    path: Path | None = None,
    current_raw_audit_path: Path | None = None,
    current_raw_audit_provenance_path: Path | None = None,
) -> dict[str, dict[str, Any]]:
    """Load only authenticated overlay responses still exact for current raw.

    ``current_raw_audit_path`` is normally the canonical raw-audit path.  An
    explicit path permits an immutable historical current receipt to be
    rechecked without swapping the paper's live canonical files.  When that
    archived byte copy was originally issued at a different canonical path,
    ``current_raw_audit_provenance_path`` supplies that immutable logical
    receipt path.  Both paths authenticate evidence only; semantic matching
    still uses the complete generated descriptor groups in
    ``current_raw_audit``.
    """

    overlay_path = path or source_record_differential_revalidation_overlay_path(paper_dir)
    try:
        payload = json.loads(overlay_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    if source_record_differential_revalidation_overlay_error(payload, paper=paper):
        return {}
    prior_raw_audit, archive_error = (
        _load_authenticated_source_record_differential_prior_raw(payload, paper=paper)
    )
    if archive_error or prior_raw_audit is None:
        return {}
    complete_reissue = SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_FIELD in payload
    if complete_reissue:
        try:
            prior_judgments_provenance = payload.get("prior_judgments")
            if not isinstance(prior_judgments_provenance, Mapping):
                return {}
            candidate_sidecar_path = _repository_provenance_path(
                prior_judgments_provenance.get("path")
            )
            candidate_sidecar = _read_json_object(candidate_sidecar_path)
        except (OSError, SourceRecordDifferentialRevalidationError):
            return {}
        candidate_metadata = candidate_sidecar.get("current_semantic_revalidation")
        attested_record = payload.get(
            SOURCE_RECORD_COMPLETE_REISSUE_CURRENT_REVALIDATION_FIELD
        )
        if isinstance(candidate_metadata, Mapping):
            if attested_record is None:
                return {}
            if _complete_reissue_attested_current_revalidation_error(
                attested_record,
                paper=paper,
                paper_dir=paper_dir,
                raw_audit=prior_raw_audit,
                candidate_sidecar=candidate_sidecar,
                candidate_sidecar_path=candidate_sidecar_path,
            ):
                return {}
        elif attested_record is not None:
            return {}
    raw_items = payload.get("items")
    if not isinstance(raw_items, Mapping):
        return {}
    if _raw_audit_error(current_raw_audit, paper=paper, label="current"):
        return {}
    if _overlay_reuse_exclusions_error(
        payload, paper=paper, current_raw_audit=current_raw_audit
    ):
        return {}
    receipt_path = current_raw_audit_path or (
        paper_dir / "audit" / "source_record_audit.json"
    )
    if not receipt_path.is_file():
        return {}
    try:
        # An explicit archive path is evidence, not merely a convenient file
        # location.  Refuse a caller-supplied in-memory receipt whose complete
        # JSON content differs from the archived bytes; otherwise a stale or
        # substituted archive could inherit the live mapping's provenance.
        if current_raw_audit_path is not None:
            archived_current = _read_json_object(receipt_path)
            if canonical_digest_payload(archived_current) != canonical_digest_payload(
                current_raw_audit
            ):
                return {}
        current_provenance = _raw_audit_provenance(current_raw_audit, receipt_path)
        if current_raw_audit_provenance_path is not None:
            current_provenance["path"] = _stable_provenance_path(
                current_raw_audit_provenance_path
            )
    except (OSError, SourceRecordDifferentialRevalidationError):
        return {}
    archived_source_status_bridge: ValidatedArchivedSourceStatusProjectionBridge | None = None
    if ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FIELD in payload:
        if complete_reissue:
            return {}
        bridge_record = payload.get(ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FIELD)
        if not isinstance(bridge_record, Mapping):
            return {}
        try:
            prior_raw_record = payload.get("prior_raw_audit")
            prior_sidecar_record = payload.get("prior_judgments")
            if not isinstance(prior_raw_record, Mapping) or not isinstance(
                prior_sidecar_record, Mapping
            ):
                return {}
            prior_raw_path = _repository_provenance_path(prior_raw_record.get("path"))
            prior_judgments_path = _repository_provenance_path(
                prior_sidecar_record.get("path")
            )
            prior_judgments = _read_json_object(prior_judgments_path)
            bridge_path = _repository_provenance_path(bridge_record.get("path"))
        except (OSError, SourceRecordDifferentialRevalidationError):
            return {}
        archived_source_status_bridge, _bridge_actual_record, bridge_error = (
            _archived_source_status_projection_bridge_context(
                bridge_path=bridge_path,
                paper=paper,
                paper_dir=paper_dir,
                prior_raw_audit=prior_raw_audit,
                prior_raw_audit_path=prior_raw_path,
                prior_judgments=prior_judgments,
                prior_judgments_path=prior_judgments_path,
                current_raw_audit=current_raw_audit,
                current_raw_audit_path=receipt_path,
                recorded=bridge_record,
            )
        )
        if bridge_error or archived_source_status_bridge is None:
            return {}
    administrative_projection_rebind, rebind_error = (
        _canonical_current_administrative_projection_rebind_context(
            paper_dir,
            paper,
            current_raw_audit,
            receipt_path,
        )
    )
    if rebind_error:
        return {}
    groups, group_errors = _raw_item_groups(current_raw_audit)
    if group_errors:
        return {}
    prior_groups: dict[str, dict[str, object]] | None = None
    prior_group_errors: dict[str, str] | None = None
    has_source_free_recursive_identity = any(
        isinstance(value, Mapping)
        and isinstance(
            value.get(SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD), Mapping
        )
        and value[SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD].get(
            SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_FIELD
        )
        is not None
        for value in raw_items.values()
    )
    if (
        complete_reissue
        or archived_source_status_bridge is not None
        or has_source_free_recursive_identity
    ):
        prior_groups, prior_group_errors = _raw_item_groups(prior_raw_audit)
        if prior_group_errors:
            return {}
    if complete_reissue:
        if payload.get("manual_review_required") != []:
            return {}
        if set(raw_items) != set(groups):
            return {}
        complete_reissue_error = _complete_reusable_section_identity_error(
            payload.get(SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_FIELD),
            prior_raw_audit=prior_raw_audit,
            prior_groups=prior_groups,
            current_raw_audit=current_raw_audit,
            current_groups=groups,
        )
        if complete_reissue_error:
            return {}
    descriptor_index = _descriptor_index(groups)
    if SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_FIELD in payload:
        record = payload.get(SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_FIELD)
        if not isinstance(record, Mapping):
            return {}
        try:
            reasons = _reuse_exclusion_reason_ledger(
                record.get(
                    SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_REASONS_FIELD
                ),
                label="overlay reuse-exclusions provenance",
            )
        except SourceRecordDifferentialRevalidationError:
            return {}
        if _reuse_exclusions_current_group_error(reasons, descriptor_index):
            return {}
    out: dict[str, dict[str, Any]] = {}
    for raw_value in raw_items.values():
        if not isinstance(raw_value, Mapping):
            continue
        current_key, is_current = _source_record_differential_revalidation_item_current_from_groups(
            raw_value,
            current_provenance=current_provenance,
            groups=groups,
            descriptor_index=descriptor_index,
            complete_reissue=complete_reissue,
            prior_groups=prior_groups,
            archived_source_status_bridge=archived_source_status_bridge,
        )
        if not is_current or not current_key or current_key in out:
            continue
        materialized: dict[str, Any] | None = dict(raw_value)
        metadata = raw_value.get(SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD)
        uses_archived_source_status_bridge = bool(
            isinstance(metadata, Mapping)
            and metadata.get(ARCHIVED_SOURCE_STATUS_PROJECTION_BRIDGE_FIELD) is not None
        )
        if (
            ("semantic_association_sha256" in raw_value or uses_archived_source_status_bridge)
            and not complete_reissue
        ):
            if prior_groups is None:
                prior_groups, prior_group_errors = _raw_item_groups(prior_raw_audit)
            prior_key = (
                str(metadata.get("prior_judgment_key") or "").strip()
                if isinstance(metadata, Mapping)
                else ""
            )
            prior_group = prior_groups.get(prior_key) if prior_groups else None
            current_group = groups.get(current_key)
            prior_descriptor = (
                metadata.get("prior_group_semantic_descriptor")
                if isinstance(metadata, Mapping)
                else None
            )
            if (
                not prior_key
                or prior_group_errors is None
                or prior_key in prior_group_errors
                or not isinstance(prior_group, Mapping)
                or not isinstance(current_group, Mapping)
                or not isinstance(prior_descriptor, Mapping)
                or canonical_digest_payload(prior_group.get("descriptor"))
                != canonical_digest_payload(prior_descriptor)
            ):
                continue
            effective_prior_group: Mapping[str, object] = prior_group
            if uses_archived_source_status_bridge:
                if archived_source_status_bridge is None:
                    continue
                effective_prior_group, changed, normalized_error = (
                    _archived_source_status_projection_normalized_group(
                        prior_group, archived_source_status_bridge
                    )
                )
                normalized_descriptor = (
                    metadata.get(
                        ARCHIVED_SOURCE_STATUS_PROJECTION_NORMALIZED_DESCRIPTOR_FIELD
                    )
                    if isinstance(metadata, Mapping)
                    else None
                )
                if (
                    normalized_error
                    or effective_prior_group is None
                    or not changed
                    or not isinstance(normalized_descriptor, Mapping)
                    or canonical_digest_payload(effective_prior_group.get("descriptor"))
                    != canonical_digest_payload(normalized_descriptor)
                ):
                    continue
            materialized = _materialize_current_semantic_association_rebind(
                raw_value,
                prior_group=effective_prior_group,
                current_group=current_group,
                administrative_projection_rebind=administrative_projection_rebind,
                archived_source_status_bridge=(
                    archived_source_status_bridge
                    if uses_archived_source_status_bridge
                    else None
                ),
            )
        if materialized is None:
            continue
        out[current_key] = _LoadedSourceRecordDifferentialRevalidationItem(materialized)
    if complete_reissue and set(out) != set(groups):
        return {}
    return out


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Build a semantic differential source-record v10 revalidation overlay."
    )
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--prior-raw-audit", type=Path, required=True)
    parser.add_argument("--prior-judgments", type=Path, required=True)
    parser.add_argument("--current-raw-audit", type=Path)
    parser.add_argument(
        "--reuse-exclusions",
        type=Path,
        help=(
            "reviewed descriptor-only exclusion artifact; each excluded current "
            "semantic descriptor must have a nonempty reason"
        ),
    )
    parser.add_argument(
        "--require-complete-reusable-section-identity",
        action="store_true",
        help=(
            "issue a strict receipt-reuse transport only when every reusable "
            "raw section, generated descriptor, and non-receipt aggregate field "
            "is canonically unchanged"
        ),
    )
    parser.add_argument(
        "--prior-current-revalidation-attestation",
        type=Path,
        help=(
            "exact attestation for an archived candidate sidecar that declares "
            "current semantic revalidation; required by complete receipt reissue "
            "when that candidate metadata is present"
        ),
    )
    parser.add_argument(
        "--archived-source-status-projection-bridge",
        type=Path,
        help=(
            "exact paper-local archived schema-4 direct-source-status bridge; "
            "only unique normalized descriptor pairs may consume it"
        ),
    )
    parser.add_argument(
        "--out",
        type=Path,
        help=(
            "output path; use a distinct noncanonical path for exploratory "
            "revalidation so existing byte-pinned evidence remains replayable"
        ),
    )
    parser.add_argument(
        "--replace-byte-pinned-overlay",
        action="store_true",
        help=(
            "explicitly replace an overlay whose current bytes are pinned by "
            "selected/current or historical-composition evidence; this can make "
            "that evidence unreplayable"
        ),
    )
    parser.add_argument("--write", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    paper_dir = root / "papers" / args.paper
    current_path = args.current_raw_audit or paper_dir / "audit" / "source_record_audit.json"
    output_path = args.out or source_record_differential_revalidation_overlay_path(
        paper_dir
    )
    try:
        overlay = build_source_record_differential_revalidation(
            paper=args.paper,
            prior_raw_audit=_read_json_object(args.prior_raw_audit),
            prior_judgments=_read_json_object(args.prior_judgments),
            current_raw_audit=_read_json_object(current_path),
            prior_raw_audit_path=args.prior_raw_audit,
            prior_judgments_path=args.prior_judgments,
            current_raw_audit_path=current_path,
            reuse_exclusions_path=args.reuse_exclusions,
            require_complete_reusable_section_identity=(
                args.require_complete_reusable_section_identity
            ),
            prior_current_revalidation_attestation_path=(
                args.prior_current_revalidation_attestation
            ),
            archived_source_status_projection_bridge_path=(
                args.archived_source_status_projection_bridge
            ),
        )
    except SourceRecordDifferentialRevalidationError as exc:
        print(f"{args.paper}: differential revalidation refused: {exc}", file=sys.stderr)
        return 1
    reused = len(overlay["items"])
    manual = len(overlay["manual_review_required"])
    if args.write:
        contents = (json.dumps(overlay, indent=2, sort_keys=True) + "\n").encode(
            "utf-8"
        )
        pinned_records = source_record_differential_write_pins(
            paper_dir=paper_dir,
            output_path=output_path,
            proposed_bytes=contents,
        )
        if pinned_records and not args.replace_byte_pinned_overlay:
            print(
                f"{args.paper}: differential revalidation refused: "
                + _byte_pinned_overlay_write_error(pinned_records),
                file=sys.stderr,
            )
            return 1
        if pinned_records:
            print(
                f"{args.paper}: explicitly replacing a byte-pinned differential "
                "overlay; dependent evidence will require relocation or reissue.",
                file=sys.stderr,
            )
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_bytes(contents)
        print(
            f"{args.paper}: wrote differential v10 overlay to {output_path} "
            f"({reused} reused; {manual} manual-review groups)"
        )
    else:
        print(
            f"{args.paper}: differential v10 overlay validates "
            f"({reused} reused; {manual} manual-review groups); rerun with --write"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
