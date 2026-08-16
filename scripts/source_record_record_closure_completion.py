#!/usr/bin/env python3
"""Exact, fail-closed descriptors for reviewed record-field closures.

This is deliberately a structural helper, not a matching heuristic.  It can
describe a recursive record-field closure only when the generator already
exposes one direct source-bound semantic-model parent, one declaration and
elaborated signature, one exact record-input binding, and one complete set of
material field occurrences.  Names remain navigation data: no declaration,
field, binder, source-key, or filename spelling is used to infer a route.

The manual-complement producer uses the descriptor to ask for one explicit
human closure attestation.  The theorem-realization gate independently
rebuilds it before accepting a generated child contract.  Any ambiguity or
surface change therefore removes the candidate rather than carrying a review
forward.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from typing import Any, Mapping

try:
    from scripts.source_record_integrity import canonical_digest_payload
    from scripts.source_record_target_disposition import semantic_association_record_digest
except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
    from source_record_integrity import canonical_digest_payload
    from source_record_target_disposition import semantic_association_record_digest


RECORD_FIELD_CLOSURE_COMPLETION_SCHEMA = 1
RECORD_FIELD_CLOSURE_COMPLETION_ATTESTATION_SCHEMA = 1
RECORD_FIELD_CLOSURE_COMPLETION_ATTESTATION_VERDICT = (
    "complete_generated_record_closure_matches_source"
)
RECORD_FIELD_CLOSURE_COMPLETION_ATTESTATIONS_FIELD = (
    "record_field_closure_attestations"
)
RECORD_FIELD_CLOSURE_COMPLETION_RECEIPT_FIELD = "record_field_closure_completion"
RECORD_FIELD_CLOSURE_COMPLETION_RECEIPT_SCHEMA = 1
RECORD_FIELD_CLOSURE_COMPLETION_RECEIPT_FIELDS = frozenset(
    {
        "schema",
        "closure_sha256",
        "attestation_sha256",
        "semantic_model_judgment_key",
        "component_sha256",
        "structural_type_sha256",
    }
)
RECORD_FIELD_CLOSURE_COMPLETION_ATTESTATION_FIELDS = frozenset(
    {
        "schema",
        "closure_sha256",
        "verdict",
        "source_location",
        "closure_semantics",
        "lean_evidence",
    }
)

_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_DIRECT_SOURCE_ASSOCIATION_FIELD = "source_statement_association"
_DIRECT_SOURCE_ASSOCIATION_ROLE = "direct_source_route"
_DIRECT_SOURCE_ASSOCIATION_ORIGIN = "explicit_source_map_direct_route"


def _sha256(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if _SHA256_RE.fullmatch(text) else ""


def _canonical_digest(payload: object) -> str:
    encoded = json.dumps(
        canonical_digest_payload(payload), sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _declaration_identity(value: object) -> tuple[str, str] | None:
    if not isinstance(value, Mapping):
        return None
    declaration = str(value.get("qualified_declaration") or "").strip()
    digest = _sha256(value.get("declaration_sha256"))
    return (declaration, digest) if declaration and digest else None


def _single_signature(
    value: object, *, declaration: str
) -> tuple[str, str] | None:
    if not isinstance(value, list) or len(value) != 1 or not isinstance(value[0], Mapping):
        return None
    signature_declaration = str(value[0].get("qualified_declaration") or "").strip()
    digest = _sha256(value[0].get("elaborated_signature_sha256"))
    if signature_declaration != declaration or not digest:
        return None
    return declaration, digest


def _direct_source_association(
    semantic_item: Mapping[str, Any],
    *,
    declaration_identity: tuple[str, str],
    signature_identity: tuple[str, str],
) -> Mapping[str, Any] | None:
    """Read exactly one generated direct source-map association.

    This intentionally excludes helper, inferred, paired-row, and generic
    semantic-contract routes.  A closure completion is a compression of a
    direct paper-facing model review, not a way to discover a relationship
    from a source-looking name.
    """

    association = semantic_item.get(_DIRECT_SOURCE_ASSOCIATION_FIELD)
    if not isinstance(association, Mapping):
        return None
    if (
        association.get("schema") != 2
        or str(association.get("role") or "").strip()
        != _DIRECT_SOURCE_ASSOCIATION_ROLE
        or str(association.get("association_origin") or "").strip()
        != _DIRECT_SOURCE_ASSOCIATION_ORIGIN
    ):
        return None
    if _declaration_identity(association.get("reviewed_declaration_identity")) != declaration_identity:
        return None
    signature = association.get("reviewed_elaborated_signature_identity")
    if not isinstance(signature, Mapping):
        return None
    associated_signature = (
        str(signature.get("qualified_declaration") or "").strip(),
        _sha256(signature.get("elaborated_signature_sha256")),
    )
    if associated_signature != signature_identity:
        return None
    if not _sha256(association.get("semantic_association_sha256")):
        return None
    identities = association.get("source_item_identities")
    if not isinstance(identities, list) or not identities:
        return None
    seen: set[tuple[str, str, str]] = set()
    semantic_digests: list[str] = []
    for identity in identities:
        if not isinstance(identity, Mapping):
            return None
        source_key = str(identity.get("source_key") or "").strip()
        source_location = str(identity.get("source_location") or "").strip()
        source_map_digest = _sha256(identity.get("source_map_item_sha256"))
        semantic_digest = _sha256(identity.get("source_semantic_sha256"))
        if (
            not source_key
            or not source_location
            or not source_map_digest
            or not semantic_digest
        ):
            return None
        key = (source_key, source_map_digest, semantic_digest)
        if key in seen:
            return None
        seen.add(key)
        semantic_digests.append(semantic_digest)
    expected_association_sha = semantic_association_record_digest(
        semantic_digests, signature
    )
    if _sha256(association.get("semantic_association_sha256")) != expected_association_sha:
        return None
    return association


def _declared_direct_record_roots(semantic_item: Mapping[str, Any]) -> set[str]:
    """Return roots claimed by a malformed-or-valid direct route for blocking.

    A malformed direct route must not make a different parent for the same
    root appear unique.  This only identifies a route that explicitly claims
    the generator's direct-source role/origin; it never infers a source parent
    from a semantic-model name or a record spelling.
    """

    association = semantic_item.get(_DIRECT_SOURCE_ASSOCIATION_FIELD)
    if not isinstance(association, Mapping) or (
        str(association.get("role") or "").strip()
        != _DIRECT_SOURCE_ASSOCIATION_ROLE
        or str(association.get("association_origin") or "").strip()
        != _DIRECT_SOURCE_ASSOCIATION_ORIGIN
    ):
        return set()
    bindings = semantic_item.get("record_input_bindings")
    if not isinstance(bindings, list):
        return set()
    roots: set[str] = set()
    for binding in bindings:
        parsed = _record_binding(binding)
        if parsed is not None:
            roots.add(parsed[0])
    return roots


def _record_binding(value: object) -> tuple[str, frozenset[str], str] | None:
    """Return exact root, binders, and a full binding digest."""

    if not isinstance(value, Mapping):
        return None
    roots = value.get("record_roots")
    binders = value.get("binder_names")
    if not isinstance(roots, list) or not isinstance(binders, list):
        return None
    root_values = [str(root).strip() for root in roots if str(root).strip()]
    binder_values = [str(binder).strip() for binder in binders if str(binder).strip()]
    if (
        len(root_values) != 1
        or "." not in root_values[0]
        or not binder_values
        or len(binder_values) != len(set(binder_values))
    ):
        return None
    return root_values[0], frozenset(binder_values), _canonical_digest(dict(value))


def _recursive_field_closure(
    fields: Mapping[str, Mapping[str, Any]], root: str
) -> frozenset[str] | None:
    """Follow only complete generated nested-record edges from ``root``."""

    by_structure: dict[str, set[str]] = {}
    for key, item in fields.items():
        structure = str(item.get("structure") or "").strip()
        if not key or not structure:
            return None
        by_structure.setdefault(structure, set()).add(key)

    seen: set[str] = set()
    visiting: set[str] = set()
    closure: set[str] = set()

    def visit(structure: str) -> bool:
        if structure in visiting:
            return False
        if structure in seen:
            return True
        keys = by_structure.get(structure)
        if not keys:
            return False
        visiting.add(structure)
        for key in keys:
            item = fields.get(key)
            nested = item.get("nested_structures") if item is not None else None
            if not isinstance(nested, list):
                return False
            closure.add(key)
            for raw_nested in nested:
                nested_structure = str(raw_nested or "").strip()
                # A missing generated nested structure is ambiguous here.  The
                # closure-completion route has no classification escape hatch;
                # an ordinary explicit field review remains available.
                if not nested_structure or nested_structure not in by_structure:
                    return False
                if not visit(nested_structure):
                    return False
        visiting.remove(structure)
        seen.add(structure)
        return True

    return frozenset(closure) if visit(root) else None


@dataclass(frozen=True)
class RecordFieldClosureCompletionCandidate:
    """One structurally exact direct-parent record-field closure."""

    semantic_model_judgment_key: str
    declaration_identity: tuple[str, str]
    elaborated_signature_identity: tuple[str, str]
    direct_source_association_sha256: str
    direct_source_association_record_sha256: str
    direct_source_locations: tuple[str, ...]
    record_root: str
    binder_names: frozenset[str]
    record_input_binding_sha256: str
    field_components: tuple[tuple[str, str, str, str], ...]
    closure_sha256: str

    @property
    def field_keys(self) -> frozenset[str]:
        return frozenset(field_key for field_key, _component_key, _component_sha, _type_sha in self.field_components)

    def descriptor(self) -> dict[str, Any]:
        """Return the generated template descriptor, including all closure IDs."""

        return {
            "schema": RECORD_FIELD_CLOSURE_COMPLETION_SCHEMA,
            "closure_sha256": self.closure_sha256,
            "semantic_model_judgment_key": self.semantic_model_judgment_key,
            "reviewed_declaration_identity": {
                "qualified_declaration": self.declaration_identity[0],
                "declaration_sha256": self.declaration_identity[1],
            },
            "reviewed_elaborated_signature_identity": {
                "qualified_declaration": self.elaborated_signature_identity[0],
                "elaborated_signature_sha256": self.elaborated_signature_identity[1],
            },
            "direct_source_association_sha256": self.direct_source_association_sha256,
            "direct_source_association_record_sha256": self.direct_source_association_record_sha256,
            "direct_source_locations": list(self.direct_source_locations),
            "record_root": self.record_root,
            "binder_names": sorted(self.binder_names),
            "record_input_binding_sha256": self.record_input_binding_sha256,
            "field_components": [
                {
                    "field_judgment_key": field_key,
                    "component_judgment_key": component_key,
                    "component_sha256": component_sha,
                    "structural_type_sha256": structural_type_sha,
                }
                for field_key, component_key, component_sha, structural_type_sha in self.field_components
            ],
        }


def current_record_field_closure_completion_candidates(
    raw_audit: Mapping[str, Any],
) -> tuple[RecordFieldClosureCompletionCandidate, ...]:
    """Return only unambiguous direct-parent recursive field closures.

    This is intentionally conservative.  It does not raise for a malformed
    possible route because those fields must stay on the normal manual lane;
    it simply declines to return a candidate.  A malformed global raw audit is
    separately rejected by its integrity/currentness reader before this helper
    is called by a materializer or evidence gate.
    """

    raw_fields = raw_audit.get("recursive_field_items")
    raw_components = raw_audit.get("theorem_realization_component_items")
    raw_semantic_items = raw_audit.get("semantic_model_items")
    expected_field_keys = raw_audit.get("expected_field_judgment_keys")
    if (
        not isinstance(raw_fields, list)
        or not isinstance(raw_components, list)
        or not isinstance(raw_semantic_items, list)
        or not isinstance(expected_field_keys, list)
    ):
        return ()

    expected = {str(key).strip() for key in expected_field_keys if str(key).strip()}
    fields: dict[str, Mapping[str, Any]] = {}
    for raw_field in raw_fields:
        if not isinstance(raw_field, Mapping):
            return ()
        key = str(raw_field.get("judgment_key") or "").strip()
        structural_type_sha = _sha256(raw_field.get("structural_type_sha256"))
        if not key or not structural_type_sha or key in fields:
            return ()
        fields[key] = raw_field
    if not fields or not set(fields).issubset(expected):
        return ()

    component_by_field: dict[str, tuple[str, str, str]] = {}
    ambiguous_component_fields: set[str] = set()
    for raw_component in raw_components:
        if not isinstance(raw_component, Mapping):
            return ()
        if str(raw_component.get("source_component_section") or "").strip() != "recursive_field_items":
            continue
        field_key = str(raw_component.get("source_judgment_key") or "").strip()
        component_key = str(raw_component.get("judgment_key") or "").strip()
        component_sha = _sha256(raw_component.get("source_claim_component_sha256"))
        structural_type_sha = _sha256(raw_component.get("structural_type_sha256"))
        if not field_key:
            continue
        candidate = (component_key, component_sha, structural_type_sha)
        if (
            not component_key
            or not component_sha
            or not structural_type_sha
            or field_key not in fields
            or structural_type_sha
            != _sha256(fields[field_key].get("structural_type_sha256"))
        ):
            ambiguous_component_fields.add(field_key)
            continue
        prior = component_by_field.get(field_key)
        if prior is not None:
            ambiguous_component_fields.add(field_key)
            continue
        component_by_field[field_key] = candidate

    # First collect every structurally admissible parent binding.  A root with
    # more than one such binding is ambiguous even if those rows happen to
    # share a source locator or spelling.
    provisional: list[
        tuple[
            str,
            tuple[str, str],
            tuple[str, str],
            Mapping[str, Any],
            str,
            str,
            frozenset[str],
            str,
            frozenset[str],
        ]
    ] = []
    direct_parent_counts: dict[str, int] = {}
    blocked_roots: set[str] = set()
    for raw_semantic in raw_semantic_items:
        if not isinstance(raw_semantic, Mapping):
            return ()
        declared_roots = _declared_direct_record_roots(raw_semantic)
        semantic_key = str(raw_semantic.get("judgment_key") or "").strip()
        declaration_identity = _declaration_identity(
            raw_semantic.get("reviewed_declaration_identity")
        )
        if not semantic_key or declaration_identity is None:
            blocked_roots.update(declared_roots)
            continue
        signature_identity = _single_signature(
            raw_semantic.get("reviewed_elaborated_signature_identities"),
            declaration=declaration_identity[0],
        )
        if signature_identity is None:
            blocked_roots.update(declared_roots)
            continue
        association = _direct_source_association(
            raw_semantic,
            declaration_identity=declaration_identity,
            signature_identity=signature_identity,
        )
        if association is None:
            blocked_roots.update(declared_roots)
            continue
        bindings = raw_semantic.get("record_input_bindings")
        if not isinstance(bindings, list):
            continue
        for raw_binding in bindings:
            parsed_binding = _record_binding(raw_binding)
            if parsed_binding is None:
                continue
            root, binder_names, binding_sha = parsed_binding
            direct_parent_counts[root] = direct_parent_counts.get(root, 0) + 1
            closure = _recursive_field_closure(fields, root)
            if (
                not closure
                or not closure.issubset(expected)
                or any(
                    field_key in ambiguous_component_fields
                    or field_key not in component_by_field
                    for field_key in closure
                )
            ):
                continue
            provisional.append(
                (
                    semantic_key,
                    declaration_identity,
                    signature_identity,
                    association,
                    root,
                    binding_sha,
                    binder_names,
                    closure,
                )
            )

    by_root: dict[str, list[tuple[Any, ...]]] = {}
    for candidate in provisional:
        by_root.setdefault(str(candidate[4]), []).append(candidate)

    out: list[RecordFieldClosureCompletionCandidate] = []
    for root, candidates in by_root.items():
        if (
            root in blocked_roots
            or direct_parent_counts.get(root) != 1
            or len(candidates) != 1
        ):
            continue
        (
            semantic_key,
            declaration_identity,
            signature_identity,
            association,
            _root,
            binding_sha,
            binder_names,
            closure,
        ) = candidates[0]
        field_components = tuple(
            sorted(
                (
                    field_key,
                    component_by_field[field_key][0],
                    component_by_field[field_key][1],
                    component_by_field[field_key][2],
                )
                for field_key in closure
            )
        )
        direct_source_locations = tuple(
            sorted(
                {
                    str(identity.get("source_location") or "").strip()
                    for identity in association["source_item_identities"]
                    if isinstance(identity, Mapping)
                }
            )
        )
        if not direct_source_locations or any(
            not location for location in direct_source_locations
        ):
            continue
        digest_payload = {
            "schema": RECORD_FIELD_CLOSURE_COMPLETION_SCHEMA,
            "semantic_model_judgment_key": semantic_key,
            "reviewed_declaration_identity": {
                "qualified_declaration": declaration_identity[0],
                "declaration_sha256": declaration_identity[1],
            },
            "reviewed_elaborated_signature_identity": {
                "qualified_declaration": signature_identity[0],
                "elaborated_signature_sha256": signature_identity[1],
            },
            "direct_source_association_sha256": _sha256(
                association.get("semantic_association_sha256")
            ),
            "direct_source_association_record_sha256": _canonical_digest(dict(association)),
            "direct_source_locations": list(direct_source_locations),
            "record_root": root,
            "binder_names": sorted(binder_names),
            "record_input_binding_sha256": binding_sha,
            "field_components": [
                {
                    "field_judgment_key": field_key,
                    "component_judgment_key": component_key,
                    "component_sha256": component_sha,
                    "structural_type_sha256": structural_type_sha,
                }
                for field_key, component_key, component_sha, structural_type_sha in field_components
            ],
        }
        out.append(
            RecordFieldClosureCompletionCandidate(
                semantic_model_judgment_key=semantic_key,
                declaration_identity=declaration_identity,
                elaborated_signature_identity=signature_identity,
                direct_source_association_sha256=digest_payload[
                    "direct_source_association_sha256"
                ],
                direct_source_association_record_sha256=digest_payload[
                    "direct_source_association_record_sha256"
                ],
                direct_source_locations=direct_source_locations,
                record_root=root,
                binder_names=binder_names,
                record_input_binding_sha256=binding_sha,
                field_components=field_components,
                closure_sha256=_canonical_digest(digest_payload),
            )
        )
    return tuple(sorted(out, key=lambda candidate: candidate.closure_sha256))


def candidate_descriptor_by_sha256(
    candidates: tuple[RecordFieldClosureCompletionCandidate, ...],
) -> dict[str, RecordFieldClosureCompletionCandidate]:
    """Index a current candidate set, rejecting impossible digest collisions."""

    result: dict[str, RecordFieldClosureCompletionCandidate] = {}
    for candidate in candidates:
        if candidate.closure_sha256 in result:
            return {}
        result[candidate.closure_sha256] = candidate
    return result


def closure_attestation_error(
    value: object,
    *,
    candidate: RecordFieldClosureCompletionCandidate,
) -> str:
    """Validate one explicit human attestation of an exact generated closure."""

    if not isinstance(value, Mapping):
        return "record-field closure attestation is not an object"
    if set(value) != RECORD_FIELD_CLOSURE_COMPLETION_ATTESTATION_FIELDS:
        return "record-field closure attestation has unsupported fields"
    if value.get("schema") != RECORD_FIELD_CLOSURE_COMPLETION_ATTESTATION_SCHEMA:
        return "record-field closure attestation has an unsupported schema"
    if _sha256(value.get("closure_sha256")) != candidate.closure_sha256:
        return "record-field closure attestation does not bind the current exact closure"
    if (
        str(value.get("verdict") or "").strip()
        != RECORD_FIELD_CLOSURE_COMPLETION_ATTESTATION_VERDICT
    ):
        return "record-field closure attestation has the wrong verdict"
    for field in ("source_location", "closure_semantics", "lean_evidence"):
        if not str(value.get(field) or "").strip():
            return f"record-field closure attestation lacks `{field}`"
    if str(value.get("source_location") or "").strip() not in candidate.direct_source_locations:
        return "record-field closure attestation does not cite a direct parent source location"
    return ""


def closure_attestation_sha256(value: Mapping[str, Any]) -> str:
    """Return the byte-independent identity of one reviewer attestation."""

    return _canonical_digest(dict(value))


def closure_attestation_for_candidate(
    semantic_parent_response: Mapping[str, Any],
    *,
    candidate: RecordFieldClosureCompletionCandidate,
) -> Mapping[str, Any] | None:
    """Return one valid exact parent attestation, never selecting by a name."""

    raw_attestations = semantic_parent_response.get(
        RECORD_FIELD_CLOSURE_COMPLETION_ATTESTATIONS_FIELD
    )
    if not isinstance(raw_attestations, list):
        return None
    matches = [
        value
        for value in raw_attestations
        if isinstance(value, Mapping)
        and _sha256(value.get("closure_sha256")) == candidate.closure_sha256
    ]
    if len(matches) != 1:
        return None
    return matches[0] if not closure_attestation_error(matches[0], candidate=candidate) else None


def closure_completion_receipt_error(
    value: object,
    *,
    candidate: RecordFieldClosureCompletionCandidate,
    field_key: str,
    component_key: str,
    component_sha256: str,
    structural_type_sha256: str,
    attestation_sha256: str,
) -> str:
    """Validate a materialized v10 child receipt against one exact closure."""

    if not isinstance(value, Mapping):
        return "record-field closure completion receipt is not an object"
    if set(value) != RECORD_FIELD_CLOSURE_COMPLETION_RECEIPT_FIELDS:
        return "record-field closure completion receipt has unsupported fields"
    if value.get("schema") != RECORD_FIELD_CLOSURE_COMPLETION_RECEIPT_SCHEMA:
        return "record-field closure completion receipt has an unsupported schema"
    if _sha256(value.get("closure_sha256")) != candidate.closure_sha256:
        return "record-field closure completion receipt does not bind the current exact closure"
    if _sha256(value.get("attestation_sha256")) != attestation_sha256:
        return "record-field closure completion receipt does not bind the parent attestation"
    if (
        str(value.get("semantic_model_judgment_key") or "").strip()
        != candidate.semantic_model_judgment_key
    ):
        return "record-field closure completion receipt names a different semantic parent"
    if _sha256(value.get("component_sha256")) != component_sha256:
        return "record-field closure completion receipt does not bind the current field component"
    if _sha256(value.get("structural_type_sha256")) != structural_type_sha256:
        return "record-field closure completion receipt has the wrong structural field type"
    if field_key not in candidate.field_keys or component_key not in {
        component for _field, component, _sha, _type in candidate.field_components
    }:
        return "record-field closure completion receipt is outside the current closure"
    expected_component = {
        (field, component, component_sha, type_sha)
        for field, component, component_sha, type_sha in candidate.field_components
    }
    if (field_key, component_key, component_sha256, structural_type_sha256) not in expected_component:
        return "record-field closure completion receipt does not match the generated field occurrence"
    return ""
