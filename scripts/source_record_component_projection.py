#!/usr/bin/env python3
"""Fail-closed projection of reviewed whole-statement contracts to components.

The source-record generator deliberately emits every theorem-facing Lean
component as an audit coordinate.  That is the right default: a data-looking
binder can carry a hidden mathematical restriction.  It does, however, create
redundant review work when a *current, complete* semantic-model review has
already checked the full elaborated statement, including a plain outer carrier
binder or a direct-source result witness.

This module supplies a very narrow derived-evidence lane for those cases.  It
never infers a relation from a theorem name, binder spelling, source key, or
function name.  Instead it replays a paper-local receipt that pins:

* the current raw audit and its full generated group descriptors;
* declaration-content and elaborated-signature identities;
* one exact theorem-realization occurrence and structural type; and
* the semantic digest of a live, independently current parent response.

Only two generated component shapes are admitted:

* a non-``Prop`` header/outer-telescope data-or-container input with no
  conclusion, recursion, proof, instance, or unclassified route; and
* a ``provided_result`` type witness with an exact schema-2 direct source
  association shared by the parent semantic review.

The receipt contains no copied review prose.  On every load, the parent
response is reloaded through the ordinary current-evidence path *without this
projection lane*, checked for a complete semantic-model review and a positive
``expanded_binders_and_domain`` verdict, and compared to the saved semantic
digest.  A missing, stale, malformed, ambiguous, or incomplete parent simply
produces no derived child response.  Existing papers without the optional
receipt keep their legacy behavior exactly.
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
    from scripts import source_record_current_revalidation as CURRENT
    from scripts.configured_assumption_formalization_regularities import (
        load_configured_assumption_formalization_regularity_context,
    )
    from scripts.formalization_protocol import (
        FORMALIZATION_REVIEW_PROTOCOL_FIELD,
        formalization_review_protocol_digest,
    )
    from scripts.source_record_differential_revalidation import (
        _raw_audit_error,
        _raw_item_groups,
        source_record_differential_item_descriptor_sha256,
    )
    from scripts.source_record_integrity import canonical_digest_payload
    from scripts.source_record_target_disposition import (
        project_source_record_response_association_pins,
    )
except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
    import source_record_current_revalidation as CURRENT
    from configured_assumption_formalization_regularities import (
        load_configured_assumption_formalization_regularity_context,
    )
    from formalization_protocol import (
        FORMALIZATION_REVIEW_PROTOCOL_FIELD,
        formalization_review_protocol_digest,
    )
    from source_record_differential_revalidation import (
        _raw_audit_error,
        _raw_item_groups,
        source_record_differential_item_descriptor_sha256,
    )
    from source_record_integrity import canonical_digest_payload
    from source_record_target_disposition import (
        project_source_record_response_association_pins,
    )


SOURCE_RECORD_COMPONENT_PROJECTION_SCHEMA = 1
SOURCE_RECORD_COMPONENT_PROJECTION_POLICY_VERSION = (
    "source-record-current-component-projection-v1"
)
SOURCE_RECORD_COMPONENT_PROJECTION_ARTIFACT_KIND = (
    "source_record_current_component_projection"
)
SOURCE_RECORD_COMPONENT_PROJECTION_FILENAME = "source_record_component_projection.json"
SOURCE_RECORD_COMPONENT_PROJECTION_RECEIPT_FIELD = (
    "source_record_component_projection_sha256"
)
SOURCE_RECORD_COMPONENT_PROJECTION_ITEM_FIELD = "source_record_component_projection"
SOURCE_RECORD_COMPONENT_PROJECTION_ITEM_SCHEMA = 1
SOURCE_RECORD_COMPONENT_PROJECTION_DATA_KIND = (
    "outer_data_or_container_parent_contract"
)
SOURCE_RECORD_COMPONENT_PROJECTION_RESULT_KIND = (
    "provided_result_direct_source_parent_contract"
)
SOURCE_RECORD_COMPONENT_PARENT_CORE_SCHEMA = 1
SOURCE_RECORD_COMPONENT_PARENT_CORE_POLICY_VERSION = (
    "source-record-current-component-parent-core-v1"
)
SOURCE_RECORD_COMPONENT_PARENT_CORE_TEMPLATE_KIND = (
    "source_record_current_component_parent_core_template"
)
SOURCE_RECORD_COMPONENT_PARENT_CORE_ARTIFACT_KIND = (
    "source_record_current_component_parent_core"
)
SOURCE_RECORD_COMPONENT_PARENT_CORE_TEMPLATE_FILENAME = (
    "source_record_component_parent_core_template.json"
)
SOURCE_RECORD_COMPONENT_PARENT_CORE_FILENAME = (
    "source_record_component_parent_core.json"
)
SOURCE_RECORD_COMPONENT_PARENT_CORE_FIELD = "source_record_component_parent_core"
SOURCE_RECORD_COMPONENT_PARENT_CORE_RECEIPT_FIELD = (
    "source_record_component_parent_core_sha256"
)
SOURCE_RECORD_COMPONENT_PARENT_CORE_SCOPE = (
    "exact_raw_derived_component_projection_semantic_parents"
)

_PARENT_CORE_TEMPLATE_RECORD_FIELDS = frozenset(
    {
        "current_group_semantic_descriptor",
        "current_group_semantic_descriptor_sha256",
        "current_item_pins",
        "reviewed_current_semantics",
        "reviewer",
        "validated_at",
        "review_notes",
        "response",
    }
)
_PARENT_CORE_REVIEWER_TRANSPORT_FIELDS = frozenset(
    {
        "prompt_version",
        "validator",
        "model",
        "judge",
        "validated_at",
        "timestamp",
        "generated_at",
        "source_record_audit_sha256",
        "source_record_item_digest_schema",
        "source_record_item_sha256",
        "source_record_item_sha256s",
        "semantic_association_sha256",
        "source_contract_association_sha256",
        "source_contract_association",
        "source_statement_association",
        "semantic_contract_source_association",
        "source_target_disposition",
        "source_target_disposition_sha256",
        "corrected_target_sha256_by_source_semantic_sha256",
    }
)

_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
_LOADED_ITEM_SENTINEL = object()
_ASSOCIATION_FIELDS = (
    "source_contract_association",
    "source_statement_association",
    "semantic_contract_source_association",
)
_DIRECT_ASSOCIATION_MARKERS = frozenset(
    {"explicit_source_map_direct_route", "direct_source_route"}
)


class SourceRecordComponentProjectionError(ValueError):
    """Raised when a component-projection receipt cannot be authenticated."""


class _LoadedSourceRecordComponentProjectionItem(dict[str, Any]):
    """JSON-invisible capability issued only by the projection loader."""

    __slots__ = ("_source_record_component_projection_loader_token",)

    def __init__(self, value: Mapping[str, Any]) -> None:
        super().__init__(value)
        self._source_record_component_projection_loader_token = _LOADED_ITEM_SENTINEL


@dataclass(frozen=True)
class ComponentProjectionFrozenInputs:
    """The exact optional receipt inputs acquired by one evidence transaction.

    The projection loader has no ambient context dependency.  A context owner
    supplies this small bundle only after it has snapshotted the fixed receipt
    path and, when structurally declared by an authentic envelope, its one
    paper-local base sidecar.  In that mode the loader never probes the live
    filesystem for either authority input.
    """

    artifact_path: Path
    artifact_present: bool
    artifact_payload: Mapping[str, Any] | None
    base_sidecar_path: Path | None
    base_sidecar_payload: Mapping[str, Any] | None


@dataclass(frozen=True)
class _Candidate:
    """One raw-derived component/parent relation before parent-response replay.

    The two judgment keys are only in-memory addresses in the generated raw
    ledger.  They are never serialized as matching evidence; the persisted
    relation consists solely of content and occurrence receipts below.
    """

    child_key: str
    parent_key: str
    parent_semantic_item: Mapping[str, Any]
    structural_record: dict[str, Any]


@dataclass(frozen=True)
class _ParentCoreGroup:
    """One semantic-only current group needed by the projection parent core."""

    key: str
    semantic_item: Mapping[str, Any]
    descriptor: dict[str, Any]
    descriptor_sha256: str
    current_item_pins: list[dict[str, Any]]
    raw_members: list[tuple[str, Mapping[str, Any]]]


def _parent_core_group_signature(
    descriptor: Mapping[str, Any], pins: object
) -> str:
    """Return the exact name-free parent identity used by this transport."""

    return json.dumps(
        {
            "descriptor": canonical_digest_payload(descriptor),
            # Ordered item receipts are part of the raw group identity.
            "current_item_pins": canonical_digest_payload(pins),
        },
        sort_keys=True,
        separators=(",", ":"),
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


def component_projection_artifact_path(paper_dir: Path) -> Path:
    """Return the fixed optional paper-local projection receipt path."""

    return paper_dir / "audit" / SOURCE_RECORD_COMPONENT_PROJECTION_FILENAME


def component_parent_core_template_path(paper_dir: Path) -> Path:
    """Return the optional non-evidence template path for projection parents."""

    return paper_dir / "audit" / SOURCE_RECORD_COMPONENT_PARENT_CORE_TEMPLATE_FILENAME


def component_parent_core_artifact_path(paper_dir: Path) -> Path:
    """Return the optional current parent-core base sidecar path."""

    return paper_dir / "audit" / SOURCE_RECORD_COMPONENT_PARENT_CORE_FILENAME


def is_loaded_source_record_component_projection_item(value: object) -> bool:
    """Whether ``value`` has the private capability issued by this loader."""

    return bool(
        isinstance(value, _LoadedSourceRecordComponentProjectionItem)
        and value._source_record_component_projection_loader_token
        is _LOADED_ITEM_SENTINEL
        and isinstance(value.get(SOURCE_RECORD_COMPONENT_PROJECTION_ITEM_FIELD), Mapping)
    )


def source_record_component_projection_item_has_provenance(value: object) -> bool:
    """Recognize serialized projection provenance without trusting it."""

    return bool(
        isinstance(value, Mapping)
        and isinstance(value.get(SOURCE_RECORD_COMPONENT_PROJECTION_ITEM_FIELD), Mapping)
    )


def copy_loaded_source_record_component_projection_item(
    value: Mapping[str, Any], updates: Mapping[str, Any] | None = None
) -> dict[str, Any]:
    """Copy a loaded response while preserving its loader-only capability."""

    copied: dict[str, Any] = dict(value)
    if updates is not None:
        copied.update(updates)
    if is_loaded_source_record_component_projection_item(value):
        return _LoadedSourceRecordComponentProjectionItem(copied)
    return copied


def _read_json_object(path: Path) -> tuple[dict[str, Any], bytes]:
    try:
        contents = path.read_bytes()
        payload = json.loads(contents)
    except (OSError, json.JSONDecodeError) as exc:
        raise SourceRecordComponentProjectionError(
            f"could not read JSON object at {path}: {exc}"
        ) from exc
    if not isinstance(payload, dict):
        raise SourceRecordComponentProjectionError(f"{path} is not a JSON object")
    return payload, contents


def _normalized_paper_relative_path(value: object, paper_dir: Path, *, label: str) -> Path:
    text = str(value or "").strip()
    pure = PurePosixPath(text)
    if (
        not text
        or pure.is_absolute()
        or any(part in {"", ".", ".."} for part in pure.parts)
    ):
        raise SourceRecordComponentProjectionError(
            f"{label} must be a normalized paper-relative path"
        )
    path = (paper_dir / Path(*pure.parts)).resolve()
    try:
        normalized = path.relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordComponentProjectionError(
            f"{label} escapes the paper directory"
        ) from exc
    if normalized != text:
        raise SourceRecordComponentProjectionError(f"{label} is not canonical")
    return path


def _receipt_envelope_error(artifact: object, *, paper: str) -> str:
    """Validate only the self-authenticating receipt envelope.

    The bounded dynamic-input discovery step must not follow a path supplied
    by an arbitrary malformed JSON file.  It does not need the raw-dependent
    structural validation below, but it does require the exact policy, paper,
    and self-digest before it can nominate its one base sidecar for snapshot.
    """

    if not isinstance(artifact, Mapping):
        return "component projection receipt is not an object"
    if (
        artifact.get("schema") != SOURCE_RECORD_COMPONENT_PROJECTION_SCHEMA
        or artifact.get("artifact_kind")
        != SOURCE_RECORD_COMPONENT_PROJECTION_ARTIFACT_KIND
        or artifact.get("policy_version")
        != SOURCE_RECORD_COMPONENT_PROJECTION_POLICY_VERSION
        or artifact.get("paper") != paper
    ):
        return "component projection receipt has incompatible schema, policy, or paper"
    receipt = _sha256(artifact.get(SOURCE_RECORD_COMPONENT_PROJECTION_RECEIPT_FIELD))
    body = {
        str(key): copy.deepcopy(value)
        for key, value in artifact.items()
        if str(key) != SOURCE_RECORD_COMPONENT_PROJECTION_RECEIPT_FIELD
    }
    if not receipt or receipt != _canonical_digest(body):
        return "component projection receipt digest is invalid"
    return ""


def component_projection_declared_base_judgment_sidecar_path(
    artifact: object,
    *,
    paper_dir: Path,
    paper: str,
) -> Path | None:
    """Return the one safe dynamic sidecar path declared by an authentic envelope.

    This parser does not grant any semantic credit.  Its only purpose is to
    let :class:`EvidenceRunContext` freeze a bounded receipt-declared input
    before any loader replays it.  Full raw-derived validation remains in
    :func:`_artifact_error`.
    """

    if _receipt_envelope_error(artifact, paper=paper) or not isinstance(
        artifact, Mapping
    ):
        return None
    try:
        return _normalized_paper_relative_path(
            artifact.get("base_judgment_sidecar_path"),
            paper_dir,
            label="component projection base sidecar path",
        )
    except SourceRecordComponentProjectionError:
        return None


def _paper_relative_path(path: Path, paper_dir: Path) -> str:
    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordComponentProjectionError(
            f"{path} must remain inside {paper_dir}"
        ) from exc


def _identity_projection(item: Mapping[str, Any]) -> tuple[str, dict[str, str]] | None:
    """Return content/signature identity without declaration-name matching."""

    declaration = item.get("reviewed_declaration_identity")
    signatures = item.get("reviewed_elaborated_signature_identities")
    if not isinstance(declaration, Mapping) or not isinstance(signatures, list):
        return None
    declaration_sha256 = _sha256(declaration.get("declaration_sha256"))
    if not declaration_sha256 or len(signatures) != 1 or not isinstance(signatures[0], Mapping):
        return None
    signature_sha256 = _sha256(signatures[0].get("elaborated_signature_sha256"))
    dependency_sha256 = _sha256(signatures[0].get("semantic_dependency_sha256"))
    if not signature_sha256:
        return None
    # Some older generated rows predate a dependency receipt.  Its absence is
    # represented explicitly, while a malformed nonempty value fails closed.
    raw_dependency = signatures[0].get("semantic_dependency_sha256")
    if raw_dependency not in (None, "") and not dependency_sha256:
        return None
    return declaration_sha256, {
        "elaborated_signature_sha256": signature_sha256,
        "semantic_dependency_sha256": dependency_sha256,
    }


def _same_identity(
    left: Mapping[str, Any], right: Mapping[str, Any]
) -> tuple[str, dict[str, str]] | None:
    left_identity = _identity_projection(left)
    right_identity = _identity_projection(right)
    if left_identity is None or right_identity is None or left_identity != right_identity:
        return None
    return left_identity


def _structural_type_sha256(item: Mapping[str, Any]) -> str:
    return _sha256(item.get("structural_type_sha256"))


def _outer_occurrence_projection(item: Mapping[str, Any]) -> dict[str, Any] | None:
    """Return the complete non-name outer-telescope coordinate for a data input."""

    indices = item.get("lean_outer_binder_indices")
    if (
        item.get("input_section") != "header"
        or item.get("input_origin") != "header_binder"
        or item.get("lean_outer_binder_route") != "outer_telescope"
        or not isinstance(indices, list)
        or not indices
        or any(type(index) is not int or index < 0 for index in indices)
        or len(set(indices)) != len(indices)
    ):
        return None
    return {
        "schema": 1,
        "surface": "theorem_facing_input_items",
        "kind": "theorem_input",
        "outer_telescope_indices": list(indices),
        "outer_telescope_route": "outer_telescope",
        "input_section": "header",
        "input_origin": "header_binder",
        "recursive_projection_sort": "",
    }


def _result_occurrence_projection(item: Mapping[str, Any]) -> dict[str, Any] | None:
    path = str(item.get("elaborated_witness_path") or "").strip()
    if (
        item.get("result_occurrence_role") != "provided_result"
        or not path
        or item.get("proposition_sort") != "true"
    ):
        return None
    return {
        "schema": 1,
        "surface": "type_valued_certificate_result_items",
        "kind": "result_type_certificate",
        "outer_telescope_indices": [],
        "outer_telescope_route": "",
        "input_section": "",
        "input_origin": "",
        "recursive_projection_sort": "",
    }


def _association_semantic_pin(
    item: Mapping[str, Any],
    *,
    require_direct: bool,
) -> str | None:
    """Validate one source association using only generated content receipts.

    ``None`` means no association is present; an empty string means one was
    present but malformed.  This distinction lets a nonclaiming parent
    semantic review provide its own source-review authority while still
    rejecting any malformed asserted association.
    """

    associations = [
        value
        for field in _ASSOCIATION_FIELDS
        if isinstance((value := item.get(field)), Mapping)
    ]
    if not associations:
        return None
    if len(associations) != 1:
        return ""
    association = associations[0]
    if association.get("schema") != 2:
        return ""
    semantic_pin = _sha256(association.get("semantic_association_sha256"))
    identities = association.get("source_item_identities")
    if not semantic_pin or not isinstance(identities, list) or not identities:
        return ""
    if any(
        not isinstance(identity, Mapping)
        or not _sha256(identity.get("source_semantic_sha256"))
        for identity in identities
    ):
        return ""
    item_identity = _identity_projection(item)
    association_declaration = association.get("reviewed_declaration_identity")
    association_signature = association.get("reviewed_elaborated_signature_identity")
    if (
        item_identity is None
        or not isinstance(association_declaration, Mapping)
        or not isinstance(association_signature, Mapping)
        or _sha256(association_declaration.get("declaration_sha256"))
        != item_identity[0]
        or _sha256(association_signature.get("elaborated_signature_sha256"))
        != item_identity[1]["elaborated_signature_sha256"]
    ):
        return ""
    if require_direct:
        markers = {
            str(association.get(field) or "").strip()
            for field in (
                "association_mode",
                "association_origin",
                "role",
                "semantic_contract_member_role",
            )
        }
        if not markers & _DIRECT_ASSOCIATION_MARKERS:
            return ""
    return semantic_pin


def _theorem_realization_component(
    raw_audit: Mapping[str, Any],
    child: Mapping[str, Any],
    *,
    projection_kind: str,
    occurrence: Mapping[str, Any],
) -> Mapping[str, Any] | None:
    """Find exactly one generated occurrence using hashes and coordinates only."""

    child_identity = _identity_projection(child)
    structural = _structural_type_sha256(child)
    if child_identity is None or not structural:
        return None
    expected_section = (
        "theorem_facing_input_items"
        if projection_kind == SOURCE_RECORD_COMPONENT_PROJECTION_DATA_KIND
        else "type_valued_certificate_result_items"
    )
    expected_kind = (
        "theorem_input"
        if projection_kind == SOURCE_RECORD_COMPONENT_PROJECTION_DATA_KIND
        else "result_type_certificate"
    )
    matches: list[Mapping[str, Any]] = []
    components = raw_audit.get("theorem_realization_component_items")
    if not isinstance(components, list):
        return None
    for component in components:
        if not isinstance(component, Mapping):
            continue
        if (
            component.get("source_component_section") != expected_section
            or component.get("source_claim_component_kind") != expected_kind
            or component.get("proposition_sort") != child.get("proposition_sort")
            or _structural_type_sha256(component) != structural
            or _same_identity(component, child) is None
        ):
            continue
        component_occurrence = component.get("source_claim_component_occurrence")
        if not isinstance(component_occurrence, Mapping):
            continue
        # ``traversal_slot`` is generated occurrence identity.  It is not
        # inferable from a binder name, so only compare the shared structural
        # coordinate here and persist the complete generated occurrence below.
        if any(
            component_occurrence.get(field) != value
            for field, value in occurrence.items()
        ):
            continue
        if projection_kind == SOURCE_RECORD_COMPONENT_PROJECTION_RESULT_KIND and (
            component.get("result_occurrence_role") != "provided_result"
            or component.get("elaborated_witness_path")
            != child.get("elaborated_witness_path")
        ):
            continue
        component_sha = _sha256(component.get("source_claim_component_sha256"))
        full_occurrence = component_occurrence
        if not component_sha or not isinstance(full_occurrence.get("traversal_slot"), int):
            continue
        matches.append(component)
    return matches[0] if len(matches) == 1 else None


def _parent_semantic_candidate(
    groups: Mapping[str, Mapping[str, Any]], child: Mapping[str, Any]
) -> tuple[str, Mapping[str, Any], Mapping[str, Any]] | None:
    """Find one semantic-model parent by exact declaration/signature content."""

    matches: list[tuple[str, Mapping[str, Any], Mapping[str, Any]]] = []
    for parent_key, group in groups.items():
        raw_members = group.get("raw_members")
        if not isinstance(raw_members, list) or len(raw_members) != 1:
            continue
        member = raw_members[0]
        if (
            not isinstance(member, tuple)
            or len(member) != 2
            or member[0] != "semantic_model_items"
            or not isinstance(member[1], Mapping)
        ):
            continue
        semantic_item = member[1]
        if semantic_item.get("kind") != "semantic_model_comparison":
            continue
        if _same_identity(semantic_item, child) is None:
            continue
        matches.append((parent_key, group, semantic_item))
    return matches[0] if len(matches) == 1 else None


def _strict_data_child(child: Mapping[str, Any]) -> tuple[dict[str, Any], str] | None:
    """Recognize the sole safe data/context projection shape."""

    if (
        child.get("kind") != "theorem_facing_input"
        or child.get("proposition_sort") != "false"
        or child.get("theorem_facing_semantic_role") != "data_or_container"
        or child.get("semantic_restriction_role") != "carrier_coherence_only"
        or child.get("source_claim_component_role") != "material"
        or child.get("source_claim_component_kind") != "theorem_input"
        or str(child.get("result_relation") or "").strip()
        or child.get("semantic_restriction_candidates") not in ([], None)
        or child.get("specialized_proof_dependency_kinds") not in ([], None)
        or child.get("elaborated_result_path") not in (None, "")
    ):
        return None
    occurrence = _outer_occurrence_projection(child)
    structural = _structural_type_sha256(child)
    if occurrence is None or not structural:
        return None
    return occurrence, structural


def _strict_result_child(child: Mapping[str, Any]) -> tuple[dict[str, Any], str] | None:
    """Recognize a direct-source provided-result witness, nothing broader."""

    if (
        child.get("kind") != "type_valued_certificate_result"
        or child.get("source_claim_component_role") != "material"
        or child.get("source_claim_component_kind")
        != "elaborated_result_type_witness"
        or child.get("semantic_restriction_role") != "requires_source_or_lean_closure"
        or child.get("theorem_facing_semantic_role") != "proof_bearing"
    ):
        return None
    occurrence = _result_occurrence_projection(child)
    structural = _structural_type_sha256(child)
    direct_association = _association_semantic_pin(child, require_direct=True)
    if occurrence is None or not structural or not direct_association:
        return None
    return occurrence, structural


def _candidate_record(
    *,
    projection_kind: str,
    child_group: Mapping[str, Any],
    parent_group: Mapping[str, Any],
    child: Mapping[str, Any],
    parent_semantic_item: Mapping[str, Any],
    component: Mapping[str, Any],
    occurrence: Mapping[str, Any],
    structural_type_sha256: str,
    child_source_association_semantic_sha256: str,
    parent_source_association_semantic_sha256: str,
) -> dict[str, Any] | None:
    identity = _identity_projection(child)
    if identity is None:
        return None
    child_group_descriptor = _sha256(child_group.get("descriptor_sha256"))
    parent_group_descriptor = _sha256(parent_group.get("descriptor_sha256"))
    component_sha = _sha256(component.get("source_claim_component_sha256"))
    parent_item_descriptor = source_record_differential_item_descriptor_sha256(
        parent_semantic_item, section="semantic_model_items"
    )
    if not all(
        (
            child_group_descriptor,
            parent_group_descriptor,
            component_sha,
            parent_item_descriptor,
            structural_type_sha256,
        )
    ):
        return None
    full_occurrence = component.get("source_claim_component_occurrence")
    if not isinstance(full_occurrence, Mapping):
        return None
    if any(full_occurrence.get(field) != value for field, value in occurrence.items()):
        return None
    record = {
        "schema": SOURCE_RECORD_COMPONENT_PROJECTION_SCHEMA,
        "projection_kind": projection_kind,
        "child_current_group_descriptor_sha256": child_group_descriptor,
        "parent_current_group_descriptor_sha256": parent_group_descriptor,
        "declaration_content_sha256": identity[0],
        "elaborated_signature_identity": identity[1],
        "child_structural_type_sha256": structural_type_sha256,
        "child_component_sha256": component_sha,
        "child_component_occurrence": copy.deepcopy(dict(full_occurrence)),
        "child_component_occurrence_sha256": _canonical_digest(full_occurrence),
        "parent_semantic_item_descriptor_sha256": parent_item_descriptor,
        "child_source_association_semantic_sha256": (
            child_source_association_semantic_sha256
        ),
        "parent_source_association_semantic_sha256": (
            parent_source_association_semantic_sha256
        ),
    }
    record["projection_descriptor_sha256"] = _canonical_digest(record)
    return record


def raw_component_projection_candidates(
    raw_audit: Mapping[str, Any], *, paper: str
) -> tuple[list[_Candidate], str]:
    """Derive all strict current candidates without consulting any sidecar.

    Any incomplete/ambiguous shape is omitted, leaving its raw group in the
    ordinary manual-review surface.  This is intentionally conservative: the
    helper is a work-saving projection, never a path to classify more inputs.
    """

    raw_error = _raw_audit_error(
        raw_audit, paper=paper, label="current component-projection"
    )
    if raw_error:
        return [], raw_error
    groups, group_errors = _raw_item_groups(raw_audit)
    if group_errors:
        return [], "current raw audit has malformed generated groups"
    candidates: list[_Candidate] = []
    seen_descriptors: set[str] = set()
    for child_key, child_group in groups.items():
        raw_members = child_group.get("raw_members")
        if not isinstance(raw_members, list) or len(raw_members) != 1:
            continue
        child_member = raw_members[0]
        if (
            not isinstance(child_member, tuple)
            or len(child_member) != 2
            or not isinstance(child_member[1], Mapping)
        ):
            continue
        child_section, child = child_member
        if child_section == "theorem_facing_input_items":
            strict = _strict_data_child(child)
            projection_kind = SOURCE_RECORD_COMPONENT_PROJECTION_DATA_KIND
        elif child_section == "type_valued_certificate_result_items":
            strict = _strict_result_child(child)
            projection_kind = SOURCE_RECORD_COMPONENT_PROJECTION_RESULT_KIND
        else:
            continue
        if strict is None:
            continue
        occurrence, structural = strict
        parent = _parent_semantic_candidate(groups, child)
        if parent is None:
            continue
        parent_key, parent_group, parent_semantic_item = parent
        component = _theorem_realization_component(
            raw_audit,
            child,
            projection_kind=projection_kind,
            occurrence=occurrence,
        )
        if component is None:
            continue
        child_association = _association_semantic_pin(
            child,
            require_direct=(
                projection_kind == SOURCE_RECORD_COMPONENT_PROJECTION_RESULT_KIND
            ),
        )
        parent_association = _association_semantic_pin(
            parent_semantic_item,
            require_direct=(
                projection_kind == SOURCE_RECORD_COMPONENT_PROJECTION_RESULT_KIND
            ),
        )
        # An asserted association may not be malformed.  A data/context child
        # without one is allowed only through the complete parent review; a
        # provided result must have an exact shared direct route.
        if child_association == "" or parent_association == "":
            continue
        if projection_kind == SOURCE_RECORD_COMPONENT_PROJECTION_RESULT_KIND and (
            not child_association
            or not parent_association
            or child_association != parent_association
        ):
            continue
        if child_association and (
            not parent_association or child_association != parent_association
        ):
            continue
        record = _candidate_record(
            projection_kind=projection_kind,
            child_group=child_group,
            parent_group=parent_group,
            child=child,
            parent_semantic_item=parent_semantic_item,
            component=component,
            occurrence=occurrence,
            structural_type_sha256=structural,
            child_source_association_semantic_sha256=child_association or "",
            parent_source_association_semantic_sha256=parent_association or "",
        )
        if record is None:
            continue
        descriptor = str(record["projection_descriptor_sha256"])
        if descriptor in seen_descriptors:
            # A descriptor collision is ambiguous by construction.  Do not
            # guess a child slot from a key or a name.
            return [], "raw component projection candidates are descriptor-ambiguous"
        seen_descriptors.add(descriptor)
        candidates.append(
            _Candidate(
                child_key=child_key,
                parent_key=parent_key,
                parent_semantic_item=parent_semantic_item,
                structural_record=record,
            )
        )
    candidates.sort(key=lambda candidate: str(candidate.structural_record["projection_descriptor_sha256"]))
    return candidates, ""


def raw_component_projection_parent_groups(
    raw_audit: Mapping[str, Any], *, paper: str
) -> tuple[dict[str, _ParentCoreGroup], str]:
    """Derive the exact semantic-only parent groups needed for projection.

    This is intentionally a current-raw operation.  The generated judgment
    keys address output slots only; the returned groups are authenticated by
    their full raw descriptor and ordered item receipts, never by a declaration
    or binder name.
    """

    candidates, error = raw_component_projection_candidates(raw_audit, paper=paper)
    if error:
        return {}, error
    if not candidates:
        return {}, "current raw audit has no admissible component-projection candidates"
    groups, group_errors = _raw_item_groups(raw_audit)
    if group_errors:
        return {}, "current raw audit has malformed generated groups"
    parents: dict[str, _ParentCoreGroup] = {}
    seen_signatures: set[str] = set()
    for candidate in candidates:
        group = groups.get(candidate.parent_key)
        if not isinstance(group, Mapping):
            return {}, "component-projection parent is absent from the current raw group ledger"
        raw_members = group.get("raw_members")
        if (
            not isinstance(raw_members, list)
            or len(raw_members) != 1
            or not isinstance(raw_members[0], tuple)
            or len(raw_members[0]) != 2
            or raw_members[0][0] != "semantic_model_items"
            or not isinstance(raw_members[0][1], Mapping)
        ):
            return {}, "component-projection parent group is not semantic-only"
        semantic_item = raw_members[0][1]
        if (
            semantic_item.get("kind") != "semantic_model_comparison"
            or source_record_differential_item_descriptor_sha256(
                semantic_item, section="semantic_model_items"
            )
            != source_record_differential_item_descriptor_sha256(
                candidate.parent_semantic_item, section="semantic_model_items"
            )
        ):
            return {}, "component-projection parent does not match its current semantic raw item"
        descriptor = group.get("descriptor")
        descriptor_sha256 = _sha256(group.get("descriptor_sha256"))
        if (
            not isinstance(descriptor, Mapping)
            or not descriptor_sha256
            or _canonical_digest(descriptor) != descriptor_sha256
        ):
            return {}, "component-projection parent group has an invalid current descriptor"
        try:
            current_item_pins = CURRENT._current_item_pins(raw_members)
        except CURRENT.SourceRecordCurrentRevalidationError as exc:
            return {}, f"component-projection parent has malformed current item pins: {exc}"
        parent = _ParentCoreGroup(
            key=candidate.parent_key,
            semantic_item=semantic_item,
            descriptor=copy.deepcopy(dict(descriptor)),
            descriptor_sha256=descriptor_sha256,
            current_item_pins=copy.deepcopy(current_item_pins),
            raw_members=list(raw_members),
        )
        existing = parents.get(parent.key)
        if existing is not None and (
            existing.descriptor_sha256 != parent.descriptor_sha256
            or canonical_digest_payload(existing.descriptor)
            != canonical_digest_payload(parent.descriptor)
            or existing.current_item_pins != parent.current_item_pins
        ):
            return {}, "component-projection parent group is descriptor-ambiguous"
        signature = _parent_core_group_signature(
            parent.descriptor, parent.current_item_pins
        )
        if signature in seen_signatures and existing is None:
            return {}, (
                "component-projection parent groups are descriptor-ambiguous; "
                "a storage key or name cannot choose a parent response"
            )
        seen_signatures.add(signature)
        parents[parent.key] = parent
    return {key: parents[key] for key in sorted(parents)}, ""


def _parent_core_group_ledger(
    parents: Mapping[str, _ParentCoreGroup],
) -> list[dict[str, Any]]:
    """Render only raw-derived parent identities, not presentation names."""

    entries = [
        {
            "current_group_semantic_descriptor": copy.deepcopy(parent.descriptor),
            "current_group_semantic_descriptor_sha256": parent.descriptor_sha256,
            "current_item_pins": copy.deepcopy(parent.current_item_pins),
        }
        for parent in parents.values()
    ]
    return sorted(
        entries,
        key=lambda entry: str(entry["current_group_semantic_descriptor_sha256"]),
    )


def component_parent_core_template(
    raw_audit: Mapping[str, Any], *, paper: str
) -> dict[str, Any]:
    """Create a non-evidence review template for exact projection parents only."""

    raw_error = _raw_audit_error(
        raw_audit, paper=paper, label="current component-parent-core"
    )
    if raw_error:
        raise SourceRecordComponentProjectionError(raw_error)
    parents, error = raw_component_projection_parent_groups(raw_audit, paper=paper)
    if error:
        raise SourceRecordComponentProjectionError(error)
    raw_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    integrity_digest = _sha256(raw_audit.get("source_record_audit_integrity_sha256"))
    if not raw_digest or not integrity_digest:
        raise SourceRecordComponentProjectionError(
            "current raw audit has no aggregate/integrity receipt"
        )
    group_ledger = _parent_core_group_ledger(parents)
    # This is a list rather than a key-indexed map.  Completion is matched
    # back to the current raw ledger only through descriptor plus ordered
    # receipts; a serialized storage address never selects a parent review.
    groups = [
        {
            "current_group_semantic_descriptor": copy.deepcopy(parent.descriptor),
            "current_group_semantic_descriptor_sha256": parent.descriptor_sha256,
            "current_item_pins": copy.deepcopy(parent.current_item_pins),
            "reviewed_current_semantics": False,
            "reviewer": "",
            "validated_at": "",
            "review_notes": "",
            "response": {},
        }
        for parent in sorted(
            parents.values(), key=lambda value: value.descriptor_sha256
        )
    ]
    return {
        "schema": SOURCE_RECORD_COMPONENT_PARENT_CORE_SCHEMA,
        "artifact_kind": SOURCE_RECORD_COMPONENT_PARENT_CORE_TEMPLATE_KIND,
        "policy_version": SOURCE_RECORD_COMPONENT_PARENT_CORE_POLICY_VERSION,
        "paper": paper,
        "review_scope": SOURCE_RECORD_COMPONENT_PARENT_CORE_SCOPE,
        "current_source_record_audit_sha256": raw_digest,
        "current_source_record_audit_integrity_sha256": integrity_digest,
        "parent_group_ledger_sha256": _canonical_digest(group_ledger),
        "parent_core_groups": groups,
        "reviewed_current_semantics": False,
        "reviewer": "",
        "validated_at": "",
        "review_notes": (
            "Each listed parent requires a complete current semantic-model review. "
            "Confirm the exact descriptor and ordered current item pins before "
            "marking it reviewed; this template cannot approve child components."
        ),
        "non_evidence_scaffold": True,
        "must_not_be_written_to_repository_sidecar": True,
    }


def _semantic_response_projection(value: Mapping[str, Any]) -> dict[str, Any]:
    """Drop only transport/issuer fields from a parent response digest.

    Reviewer identity and timestamp may legitimately change when an unchanged
    review is reissued.  Every other field, including classification,
    dimensions, source locators, comparison text, and Lean evidence remains
    bound.  Unknown fields are retained by default.
    """

    administrative = {
        "validator",
        "model",
        "judge",
        "validated_at",
        "timestamp",
        "generated_at",
    }
    return {
        str(key): copy.deepcopy(content)
        for key, content in value.items()
        if not str(key).startswith("source_record_")
        and str(key) not in administrative
    }


def parent_response_semantic_sha256(value: Mapping[str, Any]) -> str:
    """Return the stable semantic receipt for a live parent response."""

    return _canonical_digest(_semantic_response_projection(value))


def _expanded_binder_verdict_is_positive(value: Mapping[str, Any]) -> bool:
    dimensions = value.get("semantic_model_dimensions")
    if not isinstance(dimensions, Mapping):
        return False
    dimension = dimensions.get("expanded_binders_and_domain")
    verdict = (
        str(dimension.get("verdict") or "").strip()
        if isinstance(dimension, Mapping)
        else ""
    )
    return verdict.startswith("matches_")


def _evidence_module() -> Any:
    """Import the main evidence layer lazily to avoid a module-import cycle."""

    try:
        from scripts import audit_evidence_integrity as evidence
    except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
        import audit_evidence_integrity as evidence
    return evidence


def _source_record_identity_context_error(
    context: object | None,
    *,
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    expected_paper_statement_map_sha256: str | None,
) -> str:
    """Recheck a neutral identity capability before a component replay uses it."""

    if context is None:
        return ""
    evidence = _evidence_module()
    expected_map_digest = (
        expected_paper_statement_map_sha256
        if isinstance(expected_paper_statement_map_sha256, str)
        else evidence.current_paper_statement_map_sha256(paper_dir)
    )
    return evidence.current_source_record_identity_context_error(
        context,
        paper_dir=paper_dir,
        paper=paper,
        current_raw_audit=current_raw_audit,
        expected_paper_statement_map_sha256=expected_map_digest,
    )


def _current_base_parent_items(
    *,
    raw_audit: Mapping[str, Any],
    base_sidecar: Mapping[str, Any],
    paper_dir: Path,
    expected_paper_statement_map_sha256: str | None = None,
    source_record_identity_context: object | None = None,
) -> dict[str, dict[str, Any]]:
    """Replay ordinary/base overlays while explicitly excluding this lane."""

    evidence = _evidence_module()
    expected_map_digest = (
        expected_paper_statement_map_sha256
        if isinstance(expected_paper_statement_map_sha256, str)
        else evidence.current_paper_statement_map_sha256(paper_dir)
    )
    return evidence.current_source_record_judgment_items(
        dict(raw_audit),
        dict(base_sidecar),
        expected_paper_statement_map_sha256=expected_map_digest,
        folder=paper_dir,
        allow_component_projection=False,
        source_record_identity_context=source_record_identity_context,
    )


def _receipt_base_sidecar(
    artifact: Mapping[str, Any],
    *,
    paper_dir: Path,
    frozen_inputs: ComponentProjectionFrozenInputs | None = None,
) -> tuple[Path, Mapping[str, Any]]:
    """Load or use the exact receipt-declared base sidecar.

    When a caller passes a frozen payload it must also pass its resolved path.
    That prevents a receipt from swapping paths after the evidence transaction
    has acquired its inputs and avoids a fallback live read in that context.
    """

    declared_path = _normalized_paper_relative_path(
        artifact.get("base_judgment_sidecar_path"),
        paper_dir,
        label="component projection base sidecar path",
    )
    if frozen_inputs is None:
        base_sidecar, _ = _read_json_object(declared_path)
        return declared_path, base_sidecar
    if frozen_inputs.base_sidecar_path is None:
        raise SourceRecordComponentProjectionError(
            "frozen component projection base sidecar has no declared path"
        )
    try:
        same_path = (
            frozen_inputs.base_sidecar_path.resolve() == declared_path.resolve()
        )
    except (OSError, RuntimeError):
        same_path = False
    if not same_path:
        raise SourceRecordComponentProjectionError(
            "frozen component projection base sidecar path does not match the receipt"
        )
    if not isinstance(frozen_inputs.base_sidecar_payload, Mapping):
        raise SourceRecordComponentProjectionError(
            "frozen component projection base sidecar is absent or malformed"
        )
    return declared_path, frozen_inputs.base_sidecar_payload


def _receipt_artifact(
    *,
    paper_dir: Path,
    frozen_inputs: ComponentProjectionFrozenInputs | None = None,
) -> Mapping[str, Any] | None:
    """Load the optional receipt, honoring a context-frozen presence state."""

    path = component_projection_artifact_path(paper_dir)
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
        raise SourceRecordComponentProjectionError(
            "frozen component projection receipt path does not match the fixed authority path"
        )
    if not frozen_inputs.artifact_present:
        return None
    if not isinstance(frozen_inputs.artifact_payload, Mapping):
        raise SourceRecordComponentProjectionError(
            "frozen component projection receipt is malformed"
        )
    return frozen_inputs.artifact_payload


def _base_parent_items_for_receipt(
    *,
    raw_audit: Mapping[str, Any],
    base_sidecar: Mapping[str, Any],
    declared_base_sidecar_path: Path,
    paper_dir: Path,
    expected_paper_statement_map_sha256: str | None,
    base_parent_items: Mapping[str, Mapping[str, Any]] | None,
    base_parent_sidecar_path: Path | None,
    source_record_identity_context: object | None = None,
) -> dict[str, dict[str, Any]]:
    """Use an already materialized base only when its sidecar identity agrees."""

    if error := component_parent_core_validation_error(
        base_sidecar,
        raw_audit,
        paper=raw_audit.get("paper") if isinstance(raw_audit.get("paper"), str) else "",
        paper_dir=paper_dir,
        sidecar_path=declared_base_sidecar_path,
    ):
        raise SourceRecordComponentProjectionError(error)
    if base_parent_items is not None and base_parent_sidecar_path is not None:
        try:
            same_path = (
                base_parent_sidecar_path.resolve()
                == declared_base_sidecar_path.resolve()
            )
        except (OSError, RuntimeError):
            same_path = False
        if same_path:
            return {
                str(key): dict(value)
                for key, value in base_parent_items.items()
                if str(key).strip() and isinstance(value, Mapping)
            }
    return _current_base_parent_items(
        raw_audit=raw_audit,
        base_sidecar=base_sidecar,
        paper_dir=paper_dir,
        expected_paper_statement_map_sha256=(
            expected_paper_statement_map_sha256
        ),
        source_record_identity_context=source_record_identity_context,
    )


def _parent_response_error(
    candidate: _Candidate,
    response: object,
) -> str:
    if not isinstance(response, Mapping):
        return "parent semantic response is absent"
    evidence = _evidence_module()
    if not evidence.semantic_model_judgment_is_complete(
        dict(candidate.parent_semantic_item), dict(response)
    ):
        return "parent semantic response is incomplete"
    if not _expanded_binder_verdict_is_positive(response):
        return "parent expanded_binders_and_domain verdict is not a positive match"
    return ""


def _parent_core_response_error(
    parent: _ParentCoreGroup, response: object, *, label: str
) -> str:
    """Validate the semantic substance shared by a core and projection."""

    if not isinstance(response, Mapping):
        return f"{label} semantic response is absent"
    evidence = _evidence_module()
    errors = evidence.semantic_model_judgment_completeness_errors(
        dict(parent.semantic_item), dict(response)
    )
    if errors:
        return f"{label} semantic response is incomplete: " + "; ".join(errors)
    if not _expanded_binder_verdict_is_positive(response):
        return f"{label} expanded_binders_and_domain verdict is not a positive match"
    return ""


def _source_scoped_analysis_pin_ledger(
    raw_members: object,
) -> tuple[dict[str, dict[str, str]], str]:
    """Derive nested analysis pins from every raw semantic dimension.

    A source-scoped semantic analysis is identified by generated schema shape:
    ``*_association`` carrying a current semantic receipt binds the response's
    corresponding ``*_analysis`` object.  This deliberately does not encode a
    list of paper-specific analysis names.
    """

    if not isinstance(raw_members, list):
        return {}, "component-parent-core raw members are not a list"
    pins: dict[str, dict[str, str]] = {}
    for index, member in enumerate(raw_members):
        if (
            not isinstance(member, tuple)
            or len(member) != 2
            or member[0] != "semantic_model_items"
            or not isinstance(member[1], Mapping)
        ):
            return {}, f"component-parent-core raw member {index} is not semantic-model data"
        raw_dimensions = member[1].get("dimensions")
        if not isinstance(raw_dimensions, list):
            return {}, f"component-parent-core raw member {index} has no dimensions"
        for dimension_index, raw_dimension in enumerate(raw_dimensions):
            if not isinstance(raw_dimension, Mapping):
                return {}, (
                    "component-parent-core semantic dimension "
                    f"{dimension_index} is not an object"
                )
            dimension = str(raw_dimension.get("id") or "").strip()
            if not dimension:
                return {}, (
                    "component-parent-core semantic dimension "
                    f"{dimension_index} has no id"
                )
            for raw_field, association in raw_dimension.items():
                field = str(raw_field).strip()
                if not field.endswith("_association") or not isinstance(
                    association, Mapping
                ):
                    continue
                raw_pin = association.get("semantic_association_sha256")
                if raw_pin in (None, ""):
                    continue
                pin = _sha256(raw_pin)
                if not pin:
                    return {}, (
                        "component-parent-core raw semantic association "
                        f"`{field}` has an invalid semantic receipt"
                    )
                analysis_field = field[: -len("_association")] + "_analysis"
                existing = pins.setdefault(dimension, {}).get(analysis_field)
                if existing is not None and existing != pin:
                    return {}, (
                        "component-parent-core raw semantic dimension has conflicting "
                        f"`{analysis_field}` receipts"
                    )
                pins[dimension][analysis_field] = pin
    return {
        dimension: dict(sorted(analyses.items()))
        for dimension, analyses in sorted(pins.items())
    }, ""


def _project_source_scoped_analysis_pins(
    raw_members: object,
    response: Mapping[str, Any],
    *,
    reject_existing: bool,
) -> tuple[dict[str, Any] | None, str]:
    """Inject exact nested raw analysis pins into a semantic response.

    The ordinary association projector already recognizes several established
    source-scoped analyses.  This narrow second pass protects the same raw
    contract for every generated ``*_association``/``*_analysis`` pair,
    including later source-scoped dimensions, without choosing by a Lean or
    source name.
    """

    pins, error = _source_scoped_analysis_pin_ledger(raw_members)
    if error:
        return None, error
    projected = copy.deepcopy(dict(response))
    if not pins:
        return projected, ""
    dimensions = projected.get("semantic_model_dimensions")
    if not isinstance(dimensions, Mapping):
        return None, "component-parent-core response has no semantic_model_dimensions object"
    copied_dimensions = copy.deepcopy(dict(dimensions))
    for dimension, analyses in pins.items():
        raw_dimension_response = copied_dimensions.get(dimension)
        if not isinstance(raw_dimension_response, Mapping):
            return None, (
                "component-parent-core response semantic dimension "
                f"`{dimension}` is not an object"
            )
        dimension_response = copy.deepcopy(dict(raw_dimension_response))
        for analysis_field, expected_pin in analyses.items():
            raw_analysis = dimension_response.get(analysis_field)
            if not isinstance(raw_analysis, Mapping):
                return None, (
                    "component-parent-core response semantic dimension "
                    f"`{dimension}` has no `{analysis_field}` object"
                )
            analysis = copy.deepcopy(dict(raw_analysis))
            supplied = analysis.get("semantic_association_sha256")
            if supplied not in (None, ""):
                if reject_existing:
                    return None, (
                        "component-parent-core reviewer response supplies "
                        f"`{dimension}.{analysis_field}.semantic_association_sha256`"
                    )
                if _sha256(supplied) != expected_pin:
                    return None, (
                        "component-parent-core generated source-scoped analysis pin "
                        f"for `{dimension}.{analysis_field}` is stale"
                    )
            else:
                analysis["semantic_association_sha256"] = expected_pin
            dimension_response[analysis_field] = analysis
        copied_dimensions[dimension] = dimension_response
    projected["semantic_model_dimensions"] = copied_dimensions
    return projected, ""


def _reviewer_generated_transport_path(value: object, *, path: str = "response") -> str:
    """Find a generated credential anywhere in reviewer-authored content."""

    if isinstance(value, Mapping):
        for raw_field, child in value.items():
            field = str(raw_field)
            child_path = f"{path}.{field}"
            if field.startswith("source_record_") or field in _PARENT_CORE_REVIEWER_TRANSPORT_FIELDS:
                return child_path
            if nested := _reviewer_generated_transport_path(child, path=child_path):
                return nested
    elif isinstance(value, (list, tuple)):
        for index, child in enumerate(value):
            if nested := _reviewer_generated_transport_path(
                child, path=f"{path}[{index}]"
            ):
                return nested
    return ""


def _parent_core_reviewer_response_error(
    parent: _ParentCoreGroup, response: object, *, label: str
) -> str:
    """Validate reviewer content before raw projection adds credentials.

    Full semantic-model completeness follows raw association projection during
    materialization.  Some generated source-scoped analyses require a nested
    association pin, which a reviewer must not write and thus cannot satisfy
    before that projection step.
    """

    if not isinstance(response, Mapping):
        return f"{label} response is not an object"
    if generated_path := _reviewer_generated_transport_path(response):
        return f"{label} response carries generated transport at `{generated_path}`"
    evidence = _evidence_module()
    if evidence.source_record_payload_is_non_evidence(dict(response)):
        return f"{label} response is marked non-evidence"
    if response.get("classification") != "semantic_model_review":
        return f"{label} response must classify as semantic_model_review"
    dimensions = response.get("semantic_model_dimensions")
    raw_dimensions = parent.semantic_item.get("dimensions")
    if not isinstance(dimensions, Mapping) or not isinstance(raw_dimensions, list):
        return f"{label} response has no semantic-model dimensions ledger"
    for raw_dimension in raw_dimensions:
        if not isinstance(raw_dimension, Mapping):
            return f"{label} current raw semantic dimension is malformed"
        dimension = str(raw_dimension.get("id") or "").strip()
        dimension_response = dimensions.get(dimension)
        if not dimension or not isinstance(dimension_response, Mapping):
            return f"{label} response lacks semantic dimension `{dimension}`"
        if not all(
            str(dimension_response.get(field) or "").strip()
            for field in ("verdict", "source_locator", "semantic_comparison", "lean_evidence")
        ):
            return f"{label} response semantic dimension `{dimension}` lacks basic review evidence"
    _projected, projection_error = _project_source_scoped_analysis_pins(
        parent.raw_members, response, reject_existing=True
    )
    return projection_error


def _parent_core_parent_index(
    raw_audit: Mapping[str, Any], *, paper: str
) -> tuple[dict[str, _ParentCoreGroup], dict[str, _ParentCoreGroup], str]:
    """Index current parents only by their raw descriptor-and-pin identity."""

    parents, error = raw_component_projection_parent_groups(raw_audit, paper=paper)
    if error:
        return {}, {}, error
    by_signature: dict[str, _ParentCoreGroup] = {}
    for parent in parents.values():
        signature = _parent_core_group_signature(
            parent.descriptor, parent.current_item_pins
        )
        if signature in by_signature:
            return {}, {}, (
                "component-parent-core parents are descriptor-ambiguous; a storage "
                "key or name cannot choose a reviewed response"
            )
        by_signature[signature] = parent
    return parents, by_signature, ""


def _completed_parent_core_template_records(
    completed: Mapping[str, Any],
    raw_audit: Mapping[str, Any],
    *,
    paper: str,
) -> tuple[list[tuple[_ParentCoreGroup, Mapping[str, Any]]] | None, str]:
    """Authenticate every completed record by descriptor and ordered receipts."""

    required_fields = {
        "schema",
        "artifact_kind",
        "policy_version",
        "paper",
        "review_scope",
        "current_source_record_audit_sha256",
        "current_source_record_audit_integrity_sha256",
        "parent_group_ledger_sha256",
        "parent_core_groups",
        "reviewed_current_semantics",
        "reviewer",
        "validated_at",
        "review_notes",
    }
    if set(completed) != required_fields:
        return None, "completed component-parent-core template has unsupported top-level fields"
    if (
        completed.get("schema") != SOURCE_RECORD_COMPONENT_PARENT_CORE_SCHEMA
        or completed.get("artifact_kind")
        != SOURCE_RECORD_COMPONENT_PARENT_CORE_TEMPLATE_KIND
        or completed.get("policy_version")
        != SOURCE_RECORD_COMPONENT_PARENT_CORE_POLICY_VERSION
        or completed.get("paper") != paper
        or completed.get("review_scope") != SOURCE_RECORD_COMPONENT_PARENT_CORE_SCOPE
    ):
        return None, "completed component-parent-core template has incompatible schema, policy, paper, or scope"
    if completed.get("reviewed_current_semantics") is not True:
        return None, "completed component-parent-core template must set reviewed_current_semantics: true"
    if any(
        not str(completed.get(field) or "").strip()
        for field in ("reviewer", "validated_at", "review_notes")
    ):
        return None, "completed component-parent-core template lacks reviewer metadata"
    raw_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    integrity_digest = _sha256(raw_audit.get("source_record_audit_integrity_sha256"))
    if (
        _sha256(completed.get("current_source_record_audit_sha256")) != raw_digest
        or _sha256(completed.get("current_source_record_audit_integrity_sha256"))
        != integrity_digest
    ):
        return None, "completed component-parent-core template is stale for the current raw audit"
    parents, by_signature, parent_error = _parent_core_parent_index(
        raw_audit, paper=paper
    )
    if parent_error:
        return None, parent_error
    if _sha256(completed.get("parent_group_ledger_sha256")) != _canonical_digest(
        _parent_core_group_ledger(parents)
    ):
        return None, "completed component-parent-core template has a stale parent ledger"
    records = completed.get("parent_core_groups")
    if not isinstance(records, list) or len(records) != len(parents):
        return None, "completed component-parent-core template does not cover every current parent exactly once"
    matched: list[tuple[_ParentCoreGroup, Mapping[str, Any]]] = []
    seen: set[str] = set()
    for index, record in enumerate(records, start=1):
        label = f"component-parent-core record {index}"
        if not isinstance(record, Mapping) or set(record) != _PARENT_CORE_TEMPLATE_RECORD_FIELDS:
            return None, f"{label} has unsupported fields"
        descriptor = record.get("current_group_semantic_descriptor")
        descriptor_sha256 = _sha256(
            record.get("current_group_semantic_descriptor_sha256")
        )
        pins = record.get("current_item_pins")
        if (
            not isinstance(descriptor, Mapping)
            or not descriptor_sha256
            or _canonical_digest(descriptor) != descriptor_sha256
            or not isinstance(pins, list)
        ):
            return None, f"{label} has malformed descriptor or current item pins"
        signature = _parent_core_group_signature(descriptor, pins)
        parent = by_signature.get(signature)
        if parent is None or signature in seen:
            return None, f"{label} does not uniquely match a current raw parent"
        if (
            descriptor_sha256 != parent.descriptor_sha256
            or canonical_digest_payload(descriptor)
            != canonical_digest_payload(parent.descriptor)
            or pins != parent.current_item_pins
        ):
            return None, f"{label} does not exactly match its current raw parent"
        if record.get("reviewed_current_semantics") is not True:
            return None, f"{label} must explicitly mark current semantics reviewed"
        if any(
            not str(record.get(field) or "").strip()
            for field in ("reviewer", "validated_at", "review_notes")
        ):
            return None, f"{label} lacks reviewer metadata"
        if error := _parent_core_reviewer_response_error(
            parent, record.get("response"), label=label
        ):
            return None, error
        seen.add(signature)
        matched.append((parent, record))
    if len(seen) != len(by_signature):
        return None, "completed component-parent-core template omits a current raw parent"
    return matched, ""


def component_parent_core_template_validation_error(
    completed_template: Mapping[str, Any],
    raw_audit: Mapping[str, Any],
    *,
    paper: str,
) -> str:
    """Return an explanatory error for a completed parent-core template."""

    _records, error = _completed_parent_core_template_records(
        completed_template, raw_audit, paper=paper
    )
    return error


def _parent_core_response_ledger(
    records: list[tuple[_ParentCoreGroup, Mapping[str, Any]]]
) -> list[dict[str, str]]:
    return sorted(
        [
            {
                "current_group_semantic_descriptor_sha256": parent.descriptor_sha256,
                "parent_response_semantic_sha256": parent_response_semantic_sha256(
                    response
                ),
            }
            for parent, response in records
        ],
        key=lambda entry: entry["current_group_semantic_descriptor_sha256"],
    )


def materialize_component_parent_core(
    raw_audit: Mapping[str, Any],
    completed_template: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    output_sidecar_path: Path,
) -> dict[str, Any]:
    """Materialize exact reviewed semantic parents into a partial base sidecar."""

    records, error = _completed_parent_core_template_records(
        completed_template, raw_audit, paper=paper
    )
    if error or records is None:
        raise SourceRecordComponentProjectionError(
            error or "could not validate component-parent-core template"
        )
    output_relative = _paper_relative_path(output_sidecar_path, paper_dir)
    raw_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    integrity_digest = _sha256(raw_audit.get("source_record_audit_integrity_sha256"))
    statement_map_path = paper_dir / "audit" / "paper_statement_map.json"
    statement_map = (
        _read_json_object(statement_map_path)[0]
        if statement_map_path.exists()
        else None
    )
    status_path = paper_dir / "status.json"
    status_payload = _read_json_object(status_path)[0] if status_path.exists() else None
    regularity_context, regularity_error = (
        load_configured_assumption_formalization_regularity_context(
            paper_dir, raw_audit, status_payload=status_payload
        )
    )
    if regularity_error:
        raise SourceRecordComponentProjectionError(
            "could not load configured-assumption regularity context: "
            + regularity_error
        )
    result_items: dict[str, dict[str, Any]] = {}
    rendered_records: list[tuple[_ParentCoreGroup, Mapping[str, Any]]] = []
    for parent, record in records:
        response, association_error = project_source_record_response_association_pins(
            parent.raw_members,
            copy.deepcopy(dict(record["response"])),
            judgment_key=parent.key,
            reject_existing=True,
            statement_map=statement_map,
            configured_assumption_formalization_regularity_context=regularity_context,
        )
        if association_error or response is None:
            raise SourceRecordComponentProjectionError(
                f"component-parent-core parent association projection failed: {association_error}"
            )
        response, scoped_analysis_error = _project_source_scoped_analysis_pins(
            parent.raw_members,
            response,
            reject_existing=False,
        )
        if scoped_analysis_error or response is None:
            raise SourceRecordComponentProjectionError(
                "component-parent-core source-scoped analysis projection failed: "
                + str(scoped_analysis_error)
            )
        rendered = dict(response)
        rendered["prompt_version"] = CURRENT.SOURCE_RECORD_V10_PROMPT_VERSION
        rendered["validator"] = str(record["reviewer"]).strip()
        rendered["validated_at"] = str(record["validated_at"]).strip()
        rendered["source_record_audit_sha256"] = raw_digest
        if parent.current_item_pins:
            rendered["source_record_item_digest_schema"] = (
                CURRENT.SOURCE_RECORD_ITEM_DIGEST_SCHEMA
            )
            rendered["source_record_item_sha256s"] = copy.deepcopy(
                parent.current_item_pins
            )
            rendered["source_record_item_sha256"] = parent.current_item_pins[0][
                "source_record_item_sha256"
            ]
        if response_error := _parent_core_response_error(
            parent, rendered, label="materialized component-parent-core parent"
        ):
            raise SourceRecordComponentProjectionError(response_error)
        if parent.key in result_items:
            raise SourceRecordComponentProjectionError(
                "component-parent-core raw parent storage address is duplicated"
            )
        result_items[parent.key] = rendered
        rendered_records.append((parent, rendered))
    parents = {parent.key: parent for parent, _record in records}
    response_ledger = _parent_core_response_ledger(rendered_records)
    metadata = {
        "schema": SOURCE_RECORD_COMPONENT_PARENT_CORE_SCHEMA,
        "artifact_kind": SOURCE_RECORD_COMPONENT_PARENT_CORE_ARTIFACT_KIND,
        "policy_version": SOURCE_RECORD_COMPONENT_PARENT_CORE_POLICY_VERSION,
        "review_scope": SOURCE_RECORD_COMPONENT_PARENT_CORE_SCOPE,
        "current_source_record_audit_sha256": raw_digest,
        "current_source_record_audit_integrity_sha256": integrity_digest,
        "parent_group_ledger_sha256": _canonical_digest(
            _parent_core_group_ledger(parents)
        ),
        "parent_response_semantic_ledger_sha256": _canonical_digest(response_ledger),
        "output_sidecar_path": output_relative,
        "template_reviewer": str(completed_template["reviewer"]).strip(),
        "template_validated_at": str(completed_template["validated_at"]).strip(),
    }
    metadata[SOURCE_RECORD_COMPONENT_PARENT_CORE_RECEIPT_FIELD] = _canonical_digest(
        metadata
    )
    return {
        "schema": 1,
        "paper": paper,
        "prompt_version": CURRENT.SOURCE_RECORD_V10_PROMPT_VERSION,
        "source_record_audit_sha256": raw_digest,
        FORMALIZATION_REVIEW_PROTOCOL_FIELD: formalization_review_protocol_digest(),
        "validator": str(completed_template["reviewer"]).strip(),
        "validated_at": str(completed_template["validated_at"]).strip(),
        "comment": (
            "Current complete semantic-model reviews for exactly the raw-derived "
            "parents of the authenticated component-projection lane. This partial "
            "sidecar does not claim paper-wide source-record coverage."
        ),
        SOURCE_RECORD_COMPONENT_PARENT_CORE_FIELD: metadata,
        "items": result_items,
    }


def component_parent_core_validation_error(
    base_sidecar: Mapping[str, Any],
    raw_audit: Mapping[str, Any],
    *,
    paper: str,
    paper_dir: Path,
    sidecar_path: Path,
) -> str:
    """Validate an optional exact parent core before projection consumes it.

    A sidecar without this marker retains the legacy ordinary-base behavior.
    The normal evidence replay remains a separate gate, so this validator does
    not turn metadata alone into current source-record credit.
    """

    metadata = base_sidecar.get(SOURCE_RECORD_COMPONENT_PARENT_CORE_FIELD)
    if metadata is None:
        return ""
    if not isinstance(metadata, Mapping):
        return "component-parent-core metadata is not an object"
    required_metadata = {
        "schema",
        "artifact_kind",
        "policy_version",
        "review_scope",
        "current_source_record_audit_sha256",
        "current_source_record_audit_integrity_sha256",
        "parent_group_ledger_sha256",
        "parent_response_semantic_ledger_sha256",
        "output_sidecar_path",
        "template_reviewer",
        "template_validated_at",
        SOURCE_RECORD_COMPONENT_PARENT_CORE_RECEIPT_FIELD,
    }
    if set(metadata) != required_metadata:
        return "component-parent-core metadata has unsupported fields"
    if (
        metadata.get("schema") != SOURCE_RECORD_COMPONENT_PARENT_CORE_SCHEMA
        or metadata.get("artifact_kind")
        != SOURCE_RECORD_COMPONENT_PARENT_CORE_ARTIFACT_KIND
        or metadata.get("policy_version")
        != SOURCE_RECORD_COMPONENT_PARENT_CORE_POLICY_VERSION
        or metadata.get("review_scope") != SOURCE_RECORD_COMPONENT_PARENT_CORE_SCOPE
    ):
        return "component-parent-core metadata has incompatible schema, policy, or scope"
    receipt = _sha256(metadata.get(SOURCE_RECORD_COMPONENT_PARENT_CORE_RECEIPT_FIELD))
    receipt_body = {
        str(key): copy.deepcopy(value)
        for key, value in metadata.items()
        if str(key) != SOURCE_RECORD_COMPONENT_PARENT_CORE_RECEIPT_FIELD
    }
    if not receipt or receipt != _canonical_digest(receipt_body):
        return "component-parent-core metadata receipt is invalid"
    raw_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    integrity_digest = _sha256(raw_audit.get("source_record_audit_integrity_sha256"))
    if (
        _sha256(metadata.get("current_source_record_audit_sha256")) != raw_digest
        or _sha256(metadata.get("current_source_record_audit_integrity_sha256"))
        != integrity_digest
        or _sha256(base_sidecar.get("source_record_audit_sha256")) != raw_digest
    ):
        return "component-parent-core is stale for the current raw audit"
    if (
        base_sidecar.get("paper") != paper
        or base_sidecar.get("prompt_version") != CURRENT.SOURCE_RECORD_V10_PROMPT_VERSION
        or base_sidecar.get(FORMALIZATION_REVIEW_PROTOCOL_FIELD)
        != formalization_review_protocol_digest()
    ):
        return "component-parent-core ordinary evidence envelope is incompatible"
    if any(
        not str(base_sidecar.get(field) or "").strip()
        for field in ("validator", "validated_at")
    ):
        return "component-parent-core ordinary evidence envelope lacks reviewer metadata"
    try:
        if _paper_relative_path(sidecar_path, paper_dir) != metadata.get(
            "output_sidecar_path"
        ):
            return "component-parent-core metadata is bound to a different sidecar path"
    except SourceRecordComponentProjectionError as exc:
        return str(exc)
    parents, _by_signature, parent_error = _parent_core_parent_index(
        raw_audit, paper=paper
    )
    if parent_error:
        return parent_error
    if _sha256(metadata.get("parent_group_ledger_sha256")) != _canonical_digest(
        _parent_core_group_ledger(parents)
    ):
        return "component-parent-core parent ledger is stale"
    items = base_sidecar.get("items")
    if not isinstance(items, Mapping) or set(items) != set(parents):
        return "component-parent-core does not contain exactly the current raw parents"
    response_ledger: list[dict[str, str]] = []
    for key, parent in parents.items():
        response = items.get(key)
        if error := _parent_core_response_error(
            parent, response, label="component-parent-core parent"
        ):
            return error
        assert isinstance(response, Mapping)
        if (
            response.get("prompt_version") != CURRENT.SOURCE_RECORD_V10_PROMPT_VERSION
            or _sha256(response.get("source_record_audit_sha256")) != raw_digest
            or not str(response.get("validator") or "").strip()
            or not str(response.get("validated_at") or "").strip()
        ):
            return "component-parent-core parent has stale ordinary evidence transport"
        if parent.current_item_pins:
            if (
                response.get("source_record_item_digest_schema")
                != CURRENT.SOURCE_RECORD_ITEM_DIGEST_SCHEMA
                or response.get("source_record_item_sha256s")
                != parent.current_item_pins
                or response.get("source_record_item_sha256")
                != parent.current_item_pins[0]["source_record_item_sha256"]
            ):
                return "component-parent-core parent has stale current item receipts"
        elif any(
            field in response
            for field in (
                "source_record_item_digest_schema",
                "source_record_item_sha256s",
                "source_record_item_sha256",
            )
        ):
            return "aggregate-only component-parent-core parent carries item receipts"
        response_ledger.append(
            {
                "current_group_semantic_descriptor_sha256": parent.descriptor_sha256,
                "parent_response_semantic_sha256": parent_response_semantic_sha256(
                    response
                ),
            }
        )
    if _sha256(metadata.get("parent_response_semantic_ledger_sha256")) != _canonical_digest(
        sorted(
            response_ledger,
            key=lambda entry: entry["current_group_semantic_descriptor_sha256"],
        )
    ):
        return "component-parent-core response ledger is stale"
    return ""


def _artifact_body(
    *,
    paper: str,
    raw_audit: Mapping[str, Any],
    base_sidecar_relative_path: str,
    records: list[dict[str, Any]],
) -> dict[str, Any]:
    raw_digest = _sha256(raw_audit.get("source_record_audit_sha256"))
    raw_integrity = _sha256(raw_audit.get("source_record_audit_integrity_sha256"))
    if not raw_digest or not raw_integrity:
        raise SourceRecordComponentProjectionError(
            "current raw audit has no aggregate/integrity receipt"
        )
    normalized_records = sorted(
        records,
        key=lambda record: str(record.get("projection_descriptor_sha256") or ""),
    )
    body = {
        "schema": SOURCE_RECORD_COMPONENT_PROJECTION_SCHEMA,
        "artifact_kind": SOURCE_RECORD_COMPONENT_PROJECTION_ARTIFACT_KIND,
        "policy_version": SOURCE_RECORD_COMPONENT_PROJECTION_POLICY_VERSION,
        "paper": paper,
        "current_source_record_audit_sha256": raw_digest,
        "current_source_record_audit_integrity_sha256": raw_integrity,
        "base_judgment_sidecar_path": base_sidecar_relative_path,
        "component_projections": normalized_records,
        "component_projection_descriptors_sha256": _canonical_digest(
            [
                record.get("projection_descriptor_sha256")
                for record in normalized_records
            ]
        ),
    }
    body[SOURCE_RECORD_COMPONENT_PROJECTION_RECEIPT_FIELD] = _canonical_digest(body)
    return body


def build_component_projection_artifact(
    *,
    paper: str,
    raw_audit: Mapping[str, Any],
    base_sidecar: Mapping[str, Any],
    base_sidecar_relative_path: str,
    paper_dir: Path,
) -> tuple[dict[str, Any] | None, str]:
    """Build a receipt only after every strict parent is live and complete."""

    candidates, error = raw_component_projection_candidates(raw_audit, paper=paper)
    if error:
        return None, error
    if not candidates:
        return None, "current raw audit has no admissible component-projection candidates"
    try:
        base_sidecar_path = _normalized_paper_relative_path(
            base_sidecar_relative_path,
            paper_dir,
            label="component projection base sidecar path",
        )
        if core_error := component_parent_core_validation_error(
            base_sidecar,
            raw_audit,
            paper=paper,
            paper_dir=paper_dir,
            sidecar_path=base_sidecar_path,
        ):
            return None, core_error
        base_items = _current_base_parent_items(
            raw_audit=raw_audit,
            base_sidecar=base_sidecar,
            paper_dir=paper_dir,
        )
    except Exception as exc:  # noqa: BLE001 - base evidence is an authority boundary.
        return None, f"could not replay base current parent judgments: {type(exc).__name__}: {exc}"
    records: list[dict[str, Any]] = []
    for candidate in candidates:
        parent_response = base_items.get(candidate.parent_key)
        if parent_error := _parent_response_error(candidate, parent_response):
            return None, (
                "component-projection parent is not admissible: " + parent_error
            )
        assert isinstance(parent_response, Mapping)
        record = copy.deepcopy(candidate.structural_record)
        record["parent_response_semantic_sha256"] = parent_response_semantic_sha256(
            parent_response
        )
        records.append(record)
    try:
        return (
            _artifact_body(
                paper=paper,
                raw_audit=raw_audit,
                base_sidecar_relative_path=base_sidecar_relative_path,
                records=records,
            ),
            "",
        )
    except SourceRecordComponentProjectionError as exc:
        return None, str(exc)


def _artifact_error(
    artifact: object,
    *,
    paper: str,
    raw_audit: Mapping[str, Any],
) -> tuple[list[tuple[_Candidate, Mapping[str, Any]]] | None, str]:
    """Re-derive and byte-check the artifact's structural candidate ledger."""

    if not isinstance(artifact, Mapping):
        return None, "component projection receipt is not an object"
    if (
        artifact.get("schema") != SOURCE_RECORD_COMPONENT_PROJECTION_SCHEMA
        or artifact.get("artifact_kind") != SOURCE_RECORD_COMPONENT_PROJECTION_ARTIFACT_KIND
        or artifact.get("policy_version")
        != SOURCE_RECORD_COMPONENT_PROJECTION_POLICY_VERSION
        or artifact.get("paper") != paper
    ):
        return None, "component projection receipt has incompatible schema, policy, or paper"
    recorded_receipt = _sha256(
        artifact.get(SOURCE_RECORD_COMPONENT_PROJECTION_RECEIPT_FIELD)
    )
    body = {
        str(key): copy.deepcopy(value)
        for key, value in artifact.items()
        if str(key) != SOURCE_RECORD_COMPONENT_PROJECTION_RECEIPT_FIELD
    }
    if not recorded_receipt or recorded_receipt != _canonical_digest(body):
        return None, "component projection receipt digest is invalid"
    if _sha256(artifact.get("current_source_record_audit_sha256")) != _sha256(
        raw_audit.get("source_record_audit_sha256")
    ) or _sha256(artifact.get("current_source_record_audit_integrity_sha256")) != _sha256(
        raw_audit.get("source_record_audit_integrity_sha256")
    ):
        return None, "component projection receipt is stale for the current raw audit"
    candidates, error = raw_component_projection_candidates(raw_audit, paper=paper)
    if error:
        return None, error
    raw_records = artifact.get("component_projections")
    if not isinstance(raw_records, list) or not raw_records:
        return None, "component projection receipt has no component records"
    entries: dict[str, Mapping[str, Any]] = {}
    for record in raw_records:
        if not isinstance(record, Mapping):
            return None, "component projection receipt has a non-object component record"
        descriptor = _sha256(record.get("projection_descriptor_sha256"))
        parent_response_sha = _sha256(record.get("parent_response_semantic_sha256"))
        if not descriptor or not parent_response_sha or descriptor in entries:
            return None, "component projection receipt has malformed or duplicate records"
        entries[descriptor] = record
    expected = {
        str(candidate.structural_record["projection_descriptor_sha256"]): candidate
        for candidate in candidates
    }
    if set(entries) != set(expected):
        return None, "component projection receipt does not cover exactly the current strict candidates"
    recorded_descriptor_ledger = artifact.get("component_projection_descriptors_sha256")
    expected_descriptor_ledger = _canonical_digest(sorted(expected))
    if _sha256(recorded_descriptor_ledger) != expected_descriptor_ledger:
        return None, "component projection descriptor ledger digest is stale"
    validated: list[tuple[_Candidate, Mapping[str, Any]]] = []
    for descriptor, candidate in expected.items():
        record = entries[descriptor]
        expected_record = candidate.structural_record
        projected = {
            str(key): copy.deepcopy(value)
            for key, value in record.items()
            if str(key) != "parent_response_semantic_sha256"
        }
        if canonical_digest_payload(projected) != canonical_digest_payload(expected_record):
            return None, "component projection structural record no longer matches current raw evidence"
        validated.append((candidate, record))
    return validated, ""


def component_projection_validation_error(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    *,
    frozen_inputs: ComponentProjectionFrozenInputs | None = None,
    base_parent_items: Mapping[str, Mapping[str, Any]] | None = None,
    base_parent_sidecar_path: Path | None = None,
    expected_paper_statement_map_sha256: str | None = None,
    source_record_identity_context: object | None = None,
) -> str:
    """Return an explanatory error for an extant receipt, or ``""`` when valid.

    A missing optional receipt is intentionally valid legacy state and returns
    ``""``.  Consumers that need to distinguish absence inspect the path.
    """

    try:
        artifact = _receipt_artifact(
            paper_dir=paper_dir,
            frozen_inputs=frozen_inputs,
        )
        if artifact is None:
            return ""
        if identity_error := _source_record_identity_context_error(
            source_record_identity_context,
            paper_dir=paper_dir,
            paper=paper,
            current_raw_audit=current_raw_audit,
            expected_paper_statement_map_sha256=(
                expected_paper_statement_map_sha256
            ),
        ):
            return "component projection identity context is invalid: " + identity_error
        validated, error = _artifact_error(
            artifact, paper=paper, raw_audit=current_raw_audit
        )
        if error or validated is None:
            return error or "component projection receipt did not validate"
        declared_base_path, base_sidecar = _receipt_base_sidecar(
            artifact,
            paper_dir=paper_dir,
            frozen_inputs=frozen_inputs,
        )
        base_items = _base_parent_items_for_receipt(
            raw_audit=current_raw_audit,
            base_sidecar=base_sidecar,
            declared_base_sidecar_path=declared_base_path,
            paper_dir=paper_dir,
            expected_paper_statement_map_sha256=(
                expected_paper_statement_map_sha256
            ),
            base_parent_items=base_parent_items,
            base_parent_sidecar_path=base_parent_sidecar_path,
            source_record_identity_context=source_record_identity_context,
        )
        for candidate, record in validated:
            parent_response = base_items.get(candidate.parent_key)
            if parent_error := _parent_response_error(candidate, parent_response):
                return "component-projection parent is not admissible: " + parent_error
            assert isinstance(parent_response, Mapping)
            if parent_response_semantic_sha256(parent_response) != _sha256(
                record.get("parent_response_semantic_sha256")
            ):
                return "component-projection parent semantic response has changed"
    except (OSError, SourceRecordComponentProjectionError) as exc:
        return str(exc)
    except Exception as exc:  # noqa: BLE001 - a loader boundary must fail closed.
        return f"component projection replay raised {type(exc).__name__}: {exc}"
    return ""


def _projected_child_response(
    *,
    parent_response: Mapping[str, Any],
    candidate: _Candidate,
    record: Mapping[str, Any],
    raw_audit: Mapping[str, Any],
) -> dict[str, Any]:
    """Construct an in-memory derived child response, never serialized evidence."""

    response = {
        str(key): copy.deepcopy(value)
        for key, value in parent_response.items()
        if not str(key).startswith("source_record_")
    }
    response["prompt_version"] = str(raw_audit.get("prompt_version") or "")
    response["source_record_audit_sha256"] = str(
        raw_audit.get("source_record_audit_sha256") or ""
    )
    response[SOURCE_RECORD_COMPONENT_PROJECTION_ITEM_FIELD] = {
        "schema": SOURCE_RECORD_COMPONENT_PROJECTION_ITEM_SCHEMA,
        "projection_kind": record.get("projection_kind"),
        "projection_descriptor_sha256": record.get("projection_descriptor_sha256"),
        "child_current_group_descriptor_sha256": record.get(
            "child_current_group_descriptor_sha256"
        ),
        "parent_current_group_descriptor_sha256": record.get(
            "parent_current_group_descriptor_sha256"
        ),
        "parent_response_semantic_sha256": record.get(
            "parent_response_semantic_sha256"
        ),
    }
    return _LoadedSourceRecordComponentProjectionItem(response)


def load_current_source_record_component_projection_items(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    *,
    frozen_inputs: ComponentProjectionFrozenInputs | None = None,
    base_parent_items: Mapping[str, Mapping[str, Any]] | None = None,
    base_parent_sidecar_path: Path | None = None,
    expected_paper_statement_map_sha256: str | None = None,
    source_record_identity_context: object | None = None,
) -> dict[str, dict[str, Any]]:
    """Load verified current projected child responses, or nothing on failure."""

    try:
        artifact = _receipt_artifact(
            paper_dir=paper_dir,
            frozen_inputs=frozen_inputs,
        )
        if artifact is None:
            return {}
        if _source_record_identity_context_error(
            source_record_identity_context,
            paper_dir=paper_dir,
            paper=paper,
            current_raw_audit=current_raw_audit,
            expected_paper_statement_map_sha256=(
                expected_paper_statement_map_sha256
            ),
        ):
            return {}
        validated, error = _artifact_error(
            artifact, paper=paper, raw_audit=current_raw_audit
        )
        if error or validated is None:
            return {}
        declared_base_path, base_sidecar = _receipt_base_sidecar(
            artifact,
            paper_dir=paper_dir,
            frozen_inputs=frozen_inputs,
        )
        base_items = _base_parent_items_for_receipt(
            raw_audit=current_raw_audit,
            base_sidecar=base_sidecar,
            declared_base_sidecar_path=declared_base_path,
            paper_dir=paper_dir,
            expected_paper_statement_map_sha256=(
                expected_paper_statement_map_sha256
            ),
            base_parent_items=base_parent_items,
            base_parent_sidecar_path=base_parent_sidecar_path,
            source_record_identity_context=source_record_identity_context,
        )
        loaded: dict[str, dict[str, Any]] = {}
        for candidate, record in validated:
            parent_response = base_items.get(candidate.parent_key)
            if _parent_response_error(candidate, parent_response):
                return {}
            assert isinstance(parent_response, Mapping)
            if parent_response_semantic_sha256(parent_response) != _sha256(
                record.get("parent_response_semantic_sha256")
            ):
                return {}
            # A base sidecar can already carry a direct current response for a
            # child.  Do not create a competing overlay; ordinary current
            # evidence is more direct and remains authoritative.
            if candidate.child_key in base_items:
                continue
            if candidate.child_key in loaded:
                return {}
            loaded[candidate.child_key] = _projected_child_response(
                parent_response=parent_response,
                candidate=candidate,
                record=record,
                raw_audit=current_raw_audit,
            )
        return loaded
    except (OSError, SourceRecordComponentProjectionError):
        return {}
    except Exception:  # noqa: BLE001 - malformed optional evidence never grants credit.
        return {}


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
    parser.add_argument("--raw-audit", type=Path)
    mode = parser.add_mutually_exclusive_group(required=True)
    # Retain the established child-projection invocation unchanged.
    mode.add_argument("--base-judgments", type=Path)
    mode.add_argument(
        "--write-parent-core-template",
        type=Path,
        help=(
            "write a non-evidence template for exactly the current raw semantic "
            "parents of component-projection candidates"
        ),
    )
    mode.add_argument(
        "--completed-parent-core-template",
        type=Path,
        help=(
            "completed parent-core template to materialize into a partial ordinary "
            "base sidecar; requires --out and --write"
        ),
    )
    parser.add_argument("--out", type=Path)
    parser.add_argument(
        "--write",
        action="store_true",
        help="write the authenticated receipt; otherwise only validate/build it",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    paper_dir = root / "papers" / args.paper
    try:
        if not paper_dir.is_dir():
            raise SourceRecordComponentProjectionError(
                f"paper directory does not exist: {paper_dir}"
            )
        canonical_raw_path = paper_dir / "audit" / "source_record_audit.json"
        raw_path = (args.raw_audit or canonical_raw_path).resolve()
        if raw_path != canonical_raw_path.resolve():
            raise SourceRecordComponentProjectionError(
                "component projection only accepts the canonical current raw audit"
            )
        raw_audit, _ = _read_json_object(raw_path)

        if args.write_parent_core_template is not None:
            if args.out is not None or args.write:
                raise SourceRecordComponentProjectionError(
                    "--write-parent-core-template uses its explicit path and cannot be combined with --out or --write"
                )
            output_path = args.write_parent_core_template.resolve()
            _paper_relative_path(output_path, paper_dir)
            template = component_parent_core_template(raw_audit, paper=args.paper)
            _atomic_write(
                output_path,
                json.dumps(template, indent=2, sort_keys=True).encode("utf-8") + b"\n",
            )
            print(
                f"{args.paper}: wrote non-evidence component-parent-core template to "
                f"{output_path} ({len(template['parent_core_groups'])} parents)"
            )
            return 0

        if args.completed_parent_core_template is not None:
            if args.out is None or not args.write:
                raise SourceRecordComponentProjectionError(
                    "--completed-parent-core-template requires explicit --out and --write"
                )
            template_path = args.completed_parent_core_template.resolve()
            _paper_relative_path(template_path, paper_dir)
            output_path = args.out.resolve()
            _paper_relative_path(output_path, paper_dir)
            if output_path == template_path:
                raise SourceRecordComponentProjectionError(
                    "component-parent-core output must differ from its completed template"
                )
            completed_template, _ = _read_json_object(template_path)
            parent_core = materialize_component_parent_core(
                raw_audit,
                completed_template,
                paper=args.paper,
                paper_dir=paper_dir,
                output_sidecar_path=output_path,
            )
            if error := component_parent_core_validation_error(
                parent_core,
                raw_audit,
                paper=args.paper,
                paper_dir=paper_dir,
                sidecar_path=output_path,
            ):
                raise SourceRecordComponentProjectionError(
                    "internal component-parent-core validation failed: " + error
                )
            _atomic_write(
                output_path,
                json.dumps(parent_core, indent=2, sort_keys=True).encode("utf-8")
                + b"\n",
            )
            print(
                f"{args.paper}: wrote current component-parent-core to {output_path} "
                f"({len(parent_core['items'])} parents)"
            )
            return 0

        assert args.base_judgments is not None  # Established by the mode group.
        base_path = args.base_judgments.resolve()
        base_relative = _paper_relative_path(base_path, paper_dir)
        output_path = (args.out or component_projection_artifact_path(paper_dir)).resolve()
        _paper_relative_path(output_path, paper_dir)
        base_sidecar, _ = _read_json_object(base_path)
        artifact, error = build_component_projection_artifact(
            paper=args.paper,
            raw_audit=raw_audit,
            base_sidecar=base_sidecar,
            base_sidecar_relative_path=base_relative,
            paper_dir=paper_dir,
        )
        if error or artifact is None:
            raise SourceRecordComponentProjectionError(error or "could not build receipt")
        # Revalidate the in-memory result before writing.  This catches an
        # implementation mistake without trusting our own constructor.
        validated, validation_error = _artifact_error(
            artifact, paper=args.paper, raw_audit=raw_audit
        )
        if validation_error or validated is None:
            raise SourceRecordComponentProjectionError(
                "internal receipt validation failed: "
                + (validation_error or "unknown error")
            )
    except (OSError, SourceRecordComponentProjectionError) as exc:
        print(
            f"{args.paper}: component projection refused: {exc}", file=sys.stderr
        )
        return 1
    contents = json.dumps(artifact, indent=2, sort_keys=True).encode("utf-8") + b"\n"
    if args.write:
        _atomic_write(output_path, contents)
        print(
            f"{args.paper}: wrote current component projection to {output_path} "
            f"({len(artifact['component_projections'])} components)"
        )
    else:
        print(
            f"{args.paper}: current component projection validates "
            f"({len(artifact['component_projections'])} components); rerun with --write"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
