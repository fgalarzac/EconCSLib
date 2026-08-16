"""Authenticated source parents for reviewed Lean assumption declarations.

This module defines the generated association consumed by source-record and
conclusion-provenance checks.  It intentionally validates only immutable
semantic receipts.  Declaration names, sidecar storage keys, source-map keys,
and premise spellings remain navigation coordinates; none participates in the
effective semantic pin.

The paper-local ``assumption_match_llm.json`` sidecar opts into this lane with
an entry-local ``source_record_semantic_parent_v1`` receipt.  The source-record
generator is responsible for checking that receipt against the current Lean
declaration/signature, a complete Lean-derived semantic-component partition,
and byte-pinned current source routes before it emits the association validated
here.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Mapping
from typing import Any


SOURCE_ASSUMPTION_ASSOCIATION_FIELD = "source_assumption_association"
SOURCE_ASSUMPTION_ASSOCIATION_ORIGIN = (
    "authenticated_assumption_review_source_routes"
)
SOURCE_ASSUMPTION_ASSOCIATION_ROLE = "assumption_review_semantic_parent"
SOURCE_ASSUMPTION_REVIEW_IDENTITY_FIELD = "assumption_source_review_identity"
SOURCE_ASSUMPTION_REVIEW_IDENTITY_SCHEMA = 1
SOURCE_ASSUMPTION_SEMANTIC_PARENT_RECEIPT_FIELD = (
    "source_record_semantic_parent_v1"
)
SOURCE_ASSUMPTION_SEMANTIC_PARENT_RECEIPT_SCHEMA = 1
SOURCE_ASSUMPTION_ASSOCIATION_SCHEMA = 2
SOURCE_ASSUMPTION_LEAN_PARTITION_SCHEMA = 1
SOURCE_ASSUMPTION_OUTER_ATOM_PARTITION_MODE = "outer_assumption_atoms"
SOURCE_ASSUMPTION_TRANSPARENT_CONCLUSION_PARTITION_MODE = (
    "transparent_top_level_conjunction_components"
)
SOURCE_ASSUMPTION_TRANSPARENT_TYPE_CARRIER_PARTITION_MODE = (
    "transparent_type_carrier"
)
SOURCE_ASSUMPTION_ACCEPTED_JUDGMENTS = frozenset(
    {"paper_assumption", "paper_condition"}
)
SOURCE_ASSUMPTION_ACCEPTED_PREMISE_JUDGMENTS = frozenset(
    {
        "paper_assumption",
        "paper_condition",
        "source_text",
        "source_text_model_primitive",
        "derived_from_source_primitives",
        "human_verified_source_implicit",
    }
)

_SHA256_RE = re.compile(r"[0-9a-f]{64}")


def _canonical_digest_payload(value: object) -> object:
    if isinstance(value, Mapping):
        return {
            str(key): _canonical_digest_payload(member)
            for key, member in sorted(value.items(), key=lambda item: str(item[0]))
        }
    if isinstance(value, (list, tuple)):
        members = [_canonical_digest_payload(member) for member in value]
        return sorted(
            members,
            key=lambda member: json.dumps(
                member,
                ensure_ascii=True,
                sort_keys=True,
                separators=(",", ":"),
            ),
        )
    return value


def _stable_digest(value: object) -> str:
    encoded = json.dumps(
        _canonical_digest_payload(value),
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _ordered_digest(value: object) -> str:
    """Hash canonical JSON without treating array order as immaterial."""

    encoded = json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _signature_manifest_atom_digest(atom: object) -> str:
    """Mirror the exact, order-sensitive manifest-atom identity."""

    if not isinstance(atom, Mapping):
        return ""
    payload: dict[str, object] = {
        "ref": str(atom.get("ref") or "").strip(),
        "role": str(atom.get("role") or "").strip(),
        "canonical": atom.get("canonical"),
    }
    if payload["role"] != "conclusion":
        payload["binder_info"] = str(atom.get("binder_info") or "").strip()
    if not payload["ref"] or not payload["role"] or payload["canonical"] is None:
        return ""
    return _ordered_digest(payload)


def _component_occurrence_records(
    semantic_components: list[tuple[str, str]],
) -> list[dict[str, object]]:
    """Give a semantic component multiset reorder-independent occurrences."""

    grouped: dict[tuple[str, str], int] = {}
    for kind, semantic_sha in semantic_components:
        grouped[(kind, semantic_sha)] = grouped.get((kind, semantic_sha), 0) + 1
    records: list[dict[str, object]] = []
    for (kind, semantic_sha), multiplicity in sorted(grouped.items()):
        for occurrence_index in range(multiplicity):
            identity = {
                "schema": SOURCE_ASSUMPTION_LEAN_PARTITION_SCHEMA,
                "component_kind": kind,
                "component_semantic_sha256": semantic_sha,
                "occurrence_index": occurrence_index,
                "multiplicity": multiplicity,
            }
            records.append(
                {
                    **identity,
                    "component_occurrence_sha256": _stable_digest(identity),
                }
            )
    return records


def _finalize_lean_semantic_partition(
    *,
    mode: str,
    semantic_components: list[tuple[str, str]],
    proposition_graph_sha256: str = "",
    result_node_semantic_sha256: str = "",
) -> dict[str, object]:
    partition: dict[str, object] = {
        "schema": SOURCE_ASSUMPTION_LEAN_PARTITION_SCHEMA,
        "mode": mode,
        "components": _component_occurrence_records(semantic_components),
    }
    if proposition_graph_sha256:
        partition["proposition_graph_sha256"] = proposition_graph_sha256
    if result_node_semantic_sha256:
        partition["result_node_semantic_sha256"] = result_node_semantic_sha256
    partition["partition_sha256"] = _stable_digest(partition)
    return partition


def outer_assumption_atom_partition(
    atom_sha256s: list[str],
) -> tuple[dict[str, object] | None, str]:
    """Build the Lean partition for theorem-style outer assumption atoms."""

    atoms = [str(value or "").strip().lower() for value in atom_sha256s]
    if not atoms or any(not _SHA256_RE.fullmatch(value) for value in atoms):
        return None, "outer assumption partition has no valid Lean atoms"
    return _finalize_lean_semantic_partition(
        mode=SOURCE_ASSUMPTION_OUTER_ATOM_PARTITION_MODE,
        semantic_components=[("outer_assumption_atom", value) for value in atoms],
    ), ""


def _proposition_definition_manifest(manifest: Mapping[str, object]) -> bool:
    if (
        manifest.get("schema") != 2
        or manifest.get("declaration_kind") != "definition"
        or manifest.get("conclusion_mode") != "type_and_value"
    ):
        return False
    atoms = manifest.get("atoms")
    if not isinstance(atoms, list) or not atoms:
        return False
    result = atoms[-1]
    if not isinstance(result, Mapping) or result.get("ref") != "result":
        return False
    canonical = result.get("canonical")
    if not isinstance(canonical, Mapping) or canonical.get("tag") != "definition":
        return False
    result_type = canonical.get("type")
    if not isinstance(result_type, Mapping) or result_type.get("tag") != "sort":
        return False
    level = result_type.get("level")
    return isinstance(level, Mapping) and level.get("tag") == "zero"


def transparent_conclusion_component_partition(
    manifest: Mapping[str, object],
) -> tuple[dict[str, object] | None, str]:
    """Derive an exact top-level conjunction partition from Lean's DAG.

    Only a transparent Prop-valued definition is eligible.  The complete
    normalized proposition graph is Lean-owned structural evidence.  This
    routine peels transparent wrappers and recursively partitions conjunction
    left/right edges; every other logical subtree is one atomic component.
    Paths route traversal only and never enter component semantic identities.
    """

    if not _proposition_definition_manifest(manifest):
        return None, "reviewed declaration is not a transparent Prop-valued definition"
    try:
        from scripts.lean_signature_manifest import (
            normalize_elaborated_proposition_graph,
        )
    except ModuleNotFoundError:  # pragma: no cover - direct-script import.
        from lean_signature_manifest import normalize_elaborated_proposition_graph

    graph = normalize_elaborated_proposition_graph(
        manifest.get("elaborated_transparent_result_value_graph")
    )
    if not isinstance(graph, Mapping) or graph.get("complete") is not True:
        return None, "transparent proposition has no complete Lean proposition graph"
    graph_sha = str(graph.get("semantic_graph_sha256") or "").strip().lower()
    raw_nodes = graph.get("nodes")
    raw_edges = graph.get("edges")
    if (
        not _SHA256_RE.fullmatch(graph_sha)
        or not isinstance(raw_nodes, list)
        or not isinstance(raw_edges, list)
    ):
        return None, "transparent proposition graph has no current semantic identity"
    nodes = {
        str(node.get("path") or "").strip(): node
        for node in raw_nodes
        if isinstance(node, Mapping)
    }
    if len(nodes) != len(raw_nodes) or "result" not in nodes:
        return None, "transparent proposition graph has malformed nodes"
    edges_by_source: dict[str, dict[str, list[str]]] = {}
    for edge in raw_edges:
        if not isinstance(edge, Mapping):
            return None, "transparent proposition graph has malformed edges"
        source = str(edge.get("source") or "").strip()
        target = str(edge.get("target") or "").strip()
        role = str(edge.get("role") or "").strip()
        edges_by_source.setdefault(source, {}).setdefault(role, []).append(target)

    semantic_components: list[tuple[str, str]] = []
    active: set[str] = set()

    def visit(path: str) -> str:
        if path in active:
            return "transparent proposition component traversal encountered a cycle"
        node = nodes.get(path)
        if not isinstance(node, Mapping):
            return "transparent proposition component traversal reached a missing node"
        kind = str(node.get("kind") or "").strip()
        semantic_sha = str(node.get("semantic_sha256") or "").strip().lower()
        if not _SHA256_RE.fullmatch(semantic_sha):
            return "transparent proposition component lacks a semantic identity"
        active.add(path)
        try:
            roles = edges_by_source.get(path, {})
            if kind == "transparent_wrapper":
                expanded = roles.get("expanded_body", [])
                if len(expanded) != 1:
                    return "transparent proposition wrapper has no unique expanded body"
                return visit(expanded[0])
            if kind == "conjunction":
                left = roles.get("left", [])
                right = roles.get("right", [])
                if len(left) != 1 or len(right) != 1:
                    return "transparent proposition conjunction has incomplete Lean edges"
                left_error = visit(left[0])
                if left_error:
                    return left_error
                return visit(right[0])
            semantic_components.append((kind, semantic_sha))
            return ""
        finally:
            active.remove(path)

    traversal_error = visit("result")
    if traversal_error:
        return None, traversal_error
    if not semantic_components:
        return None, "transparent proposition partition has no logical components"
    result_sha = str(nodes["result"].get("semantic_sha256") or "").strip().lower()
    return _finalize_lean_semantic_partition(
        mode=SOURCE_ASSUMPTION_TRANSPARENT_CONCLUSION_PARTITION_MODE,
        semantic_components=semantic_components,
        proposition_graph_sha256=graph_sha,
        result_node_semantic_sha256=result_sha,
    ), ""


def transparent_type_carrier_partition(
    manifest: Mapping[str, object],
) -> tuple[dict[str, object] | None, str]:
    """Bind one transparent type-valued carrier to its complete Lean graph.

    Type-valued assumption records have no proposition connective partition.
    They are eligible only when Lean exposes an exact transparent definition
    result atom and the complete semantic/realization dependency receipt.  The
    recursively reached fields remain audited by the ordinary source-record
    closure lanes; this atom merely authenticates the carrier as their parent.
    """

    if (
        manifest.get("schema") != 2
        or manifest.get("declaration_kind") != "definition"
        or manifest.get("conclusion_mode") != "type_and_value"
        or _proposition_definition_manifest(manifest)
    ):
        return None, "reviewed declaration is not a transparent type-valued definition"
    raw_atoms = manifest.get("atoms")
    if not isinstance(raw_atoms, list) or not raw_atoms:
        return None, "transparent type carrier has no exact result atom"
    result = raw_atoms[-1]
    if (
        not isinstance(result, Mapping)
        or str(result.get("ref") or "").strip() != "result"
        or str(result.get("role") or "").strip() != "conclusion"
    ):
        return None, "transparent type carrier has no exact result atom"
    canonical = result.get("canonical")
    if not isinstance(canonical, Mapping) or canonical.get("tag") != "definition":
        return None, "type carrier result is opaque or lacks a definition value"
    result_atom_sha = _signature_manifest_atom_digest(result)
    if not _SHA256_RE.fullmatch(result_atom_sha):
        return None, "transparent type carrier result atom is malformed"
    try:
        from scripts.lean_signature_manifest import semantic_dependency_manifest
    except ModuleNotFoundError:  # pragma: no cover - direct-script import.
        from lean_signature_manifest import semantic_dependency_manifest
    dependency = semantic_dependency_manifest(manifest)
    if not isinstance(dependency, Mapping) or dependency.get("complete") is not True:
        return None, "transparent type carrier has no complete semantic dependency"
    semantic_dependency_sha = str(
        dependency.get("semantic_dependency_sha256") or ""
    ).strip().lower()
    realization_dependency_sha = str(
        dependency.get("realization_dependency_sha256") or ""
    ).strip().lower()
    if not _SHA256_RE.fullmatch(semantic_dependency_sha) or not _SHA256_RE.fullmatch(
        realization_dependency_sha
    ):
        return None, "transparent type carrier dependency identity is malformed"
    component_sha = _stable_digest(
        {
            "schema": SOURCE_ASSUMPTION_LEAN_PARTITION_SCHEMA,
            "result_atom_sha256": result_atom_sha,
            "semantic_dependency_sha256": semantic_dependency_sha,
            "realization_dependency_sha256": realization_dependency_sha,
        }
    )
    partition = _finalize_lean_semantic_partition(
        mode=SOURCE_ASSUMPTION_TRANSPARENT_TYPE_CARRIER_PARTITION_MODE,
        semantic_components=[("transparent_type_carrier", component_sha)],
    )
    partition.update(
        {
            "result_atom_sha256": result_atom_sha,
            "semantic_dependency_sha256": semantic_dependency_sha,
            "realization_dependency_sha256": realization_dependency_sha,
        }
    )
    partition_payload = dict(partition)
    partition_payload.pop("partition_sha256", None)
    partition["partition_sha256"] = _stable_digest(partition_payload)
    return partition, ""


def lean_semantic_partition_errors(partition: object) -> list[str]:
    """Validate a generated complete Lean semantic-component partition."""

    if not isinstance(partition, Mapping):
        return ["source-assumption review has no Lean semantic partition"]
    errors: list[str] = []
    if partition.get("schema") != SOURCE_ASSUMPTION_LEAN_PARTITION_SCHEMA:
        errors.append("source-assumption Lean semantic partition has invalid schema")
    mode = str(partition.get("mode") or "").strip()
    if mode not in {
        SOURCE_ASSUMPTION_OUTER_ATOM_PARTITION_MODE,
        SOURCE_ASSUMPTION_TRANSPARENT_CONCLUSION_PARTITION_MODE,
        SOURCE_ASSUMPTION_TRANSPARENT_TYPE_CARRIER_PARTITION_MODE,
    }:
        errors.append("source-assumption Lean semantic partition has invalid mode")
    if mode == SOURCE_ASSUMPTION_TRANSPARENT_CONCLUSION_PARTITION_MODE:
        for field in (
            "proposition_graph_sha256",
            "result_node_semantic_sha256",
        ):
            if not _SHA256_RE.fullmatch(
                str(partition.get(field) or "").strip().lower()
            ):
                errors.append(
                    "source-assumption transparent partition has no valid " + field
                )
    if mode == SOURCE_ASSUMPTION_TRANSPARENT_TYPE_CARRIER_PARTITION_MODE:
        for field in (
            "result_atom_sha256",
            "semantic_dependency_sha256",
            "realization_dependency_sha256",
        ):
            if not _SHA256_RE.fullmatch(
                str(partition.get(field) or "").strip().lower()
            ):
                errors.append(
                    "source-assumption type-carrier partition has no valid " + field
                )
    raw_components = partition.get("components")
    components = raw_components if isinstance(raw_components, list) else []
    occurrence_shas: set[str] = set()
    grouped_indexes: dict[tuple[str, str, int], set[int]] = {}
    for index, component in enumerate(components):
        if not isinstance(component, Mapping):
            errors.append(f"source-assumption Lean component {index} is malformed")
            continue
        kind = str(component.get("component_kind") or "").strip()
        semantic_sha = str(
            component.get("component_semantic_sha256") or ""
        ).strip().lower()
        occurrence_index = component.get("occurrence_index")
        multiplicity = component.get("multiplicity")
        occurrence_sha = str(
            component.get("component_occurrence_sha256") or ""
        ).strip().lower()
        identity = {
            "schema": SOURCE_ASSUMPTION_LEAN_PARTITION_SCHEMA,
            "component_kind": kind,
            "component_semantic_sha256": semantic_sha,
            "occurrence_index": occurrence_index,
            "multiplicity": multiplicity,
        }
        if (
            not kind
            or not _SHA256_RE.fullmatch(semantic_sha)
            or not isinstance(occurrence_index, int)
            or isinstance(occurrence_index, bool)
            or not isinstance(multiplicity, int)
            or isinstance(multiplicity, bool)
            or multiplicity < 1
            or occurrence_index < 0
            or occurrence_index >= multiplicity
            or occurrence_sha != _stable_digest(identity)
            or occurrence_sha in occurrence_shas
        ):
            errors.append(
                f"source-assumption Lean component {index} has a stale occurrence identity"
            )
            continue
        occurrence_shas.add(occurrence_sha)
        grouped_indexes.setdefault((kind, semantic_sha, multiplicity), set()).add(
            occurrence_index
        )
    if not components:
        errors.append("source-assumption Lean semantic partition has no components")
    for (_kind, _semantic_sha, multiplicity), indexes in grouped_indexes.items():
        if indexes != set(range(multiplicity)):
            errors.append(
                "source-assumption Lean semantic partition omits a repeated component occurrence"
            )
    supplied_partition_sha = str(
        partition.get("partition_sha256") or ""
    ).strip().lower()
    partition_payload = dict(partition)
    partition_payload.pop("partition_sha256", None)
    if supplied_partition_sha != _stable_digest(partition_payload):
        errors.append("source-assumption Lean semantic partition pin is stale")
    return errors


def source_assumption_premise_judgment_semantics_digest(
    receipt: Mapping[str, object],
) -> str:
    """Digest accepted judgment/source-route semantics, excluding presentation."""

    judgment = str(receipt.get("judgment") or "").strip().lower()
    reason = re.sub(r"\s+", " ", str(receipt.get("reason") or "")).strip()
    raw_routes = receipt.get("source_route_semantic_sha256s")
    routes = (
        sorted(str(value or "").strip().lower() for value in raw_routes)
        if isinstance(raw_routes, list)
        else []
    )
    if (
        judgment not in SOURCE_ASSUMPTION_ACCEPTED_PREMISE_JUDGMENTS
        or not reason
        or not routes
        or len(routes) != len(set(routes))
        or any(not _SHA256_RE.fullmatch(value) for value in routes)
    ):
        return ""
    return _stable_digest(
        {
            "schema": SOURCE_ASSUMPTION_REVIEW_IDENTITY_SCHEMA,
            "judgment": judgment,
            "reason": reason,
            "source_route_semantic_sha256s": routes,
        }
    )


def source_assumption_premise_review_digest(receipt: Mapping[str, object]) -> str:
    """Return one premise judgment's name-independent semantic identity."""

    raw_components = receipt.get("lean_component_occurrence_sha256s")
    components = (
        sorted(str(value or "").strip().lower() for value in raw_components)
        if isinstance(raw_components, list)
        else []
    )
    judgment_semantics_sha = source_assumption_premise_judgment_semantics_digest(
        receipt
    )
    if (
        not components
        or len(components) != len(set(components))
        or any(not _SHA256_RE.fullmatch(value) for value in components)
        or not _SHA256_RE.fullmatch(judgment_semantics_sha)
    ):
        return ""
    return _stable_digest(
        {
            "schema": SOURCE_ASSUMPTION_REVIEW_IDENTITY_SCHEMA,
            "lean_component_occurrence_sha256s": components,
            "premise_judgment_semantics_sha256": judgment_semantics_sha,
        }
    )


def source_assumption_alias_group_digest(receipt: Mapping[str, object]) -> str:
    """Return a name-free identity for explicitly aliased presentations."""

    raw_components = receipt.get("lean_component_occurrence_sha256s")
    components = (
        sorted(str(value or "").strip().lower() for value in raw_components)
        if isinstance(raw_components, list)
        else []
    )
    raw_members = receipt.get("members")
    members: list[dict[str, object]] = []
    if isinstance(raw_members, list):
        for raw_member in raw_members:
            if not isinstance(raw_member, Mapping):
                return ""
            review_sha = str(
                raw_member.get("premise_review_sha256") or ""
            ).strip().lower()
            count = raw_member.get("presentation_count")
            if (
                not _SHA256_RE.fullmatch(review_sha)
                or not isinstance(count, int)
                or isinstance(count, bool)
                or count < 1
            ):
                return ""
            members.append(
                {
                    "premise_review_sha256": review_sha,
                    "presentation_count": count,
                }
            )
    presentation_count = receipt.get("presentation_count")
    if (
        not components
        or len(components) != len(set(components))
        or any(not _SHA256_RE.fullmatch(value) for value in components)
        or not members
        or len(members) != len(
            {str(member["premise_review_sha256"]) for member in members}
        )
        or not isinstance(presentation_count, int)
        or isinstance(presentation_count, bool)
        or presentation_count < 2
        or presentation_count
        != sum(int(member["presentation_count"]) for member in members)
    ):
        return ""
    return _stable_digest(
        {
            "schema": SOURCE_ASSUMPTION_REVIEW_IDENTITY_SCHEMA,
            "lean_component_occurrence_sha256s": components,
            "members": members,
            "presentation_count": presentation_count,
        }
    )


def assumption_source_review_semantic_association_digest(
    review_identity: Mapping[str, object],
    source_identities: object,
    reviewed_signature_identity: object,
) -> str:
    """Bind a complete accepted assumption review without identifier names."""

    if not isinstance(source_identities, list) or not isinstance(
        reviewed_signature_identity, Mapping
    ):
        return ""
    signature_sha = str(
        reviewed_signature_identity.get("elaborated_signature_sha256") or ""
    ).strip().lower()
    source_semantic_digests = sorted(
        str(identity.get("source_semantic_sha256") or "").strip().lower()
        for identity in source_identities
        if isinstance(identity, Mapping)
    )
    review_sha = _stable_digest(dict(review_identity))
    if (
        not _SHA256_RE.fullmatch(signature_sha)
        or len(source_semantic_digests) != len(source_identities)
        or not source_semantic_digests
        or len(source_semantic_digests) != len(set(source_semantic_digests))
        or any(not _SHA256_RE.fullmatch(value) for value in source_semantic_digests)
    ):
        return ""
    return _stable_digest(
        {
            "schema": SOURCE_ASSUMPTION_ASSOCIATION_SCHEMA,
            "assumption_source_review_identity_sha256": review_sha,
            "source_item_semantic_sha256": source_semantic_digests,
            "elaborated_signature_sha256": signature_sha,
        }
    )


def _association_digest(association: Mapping[str, object]) -> str:
    payload = dict(association)
    payload.pop("association_sha256", None)
    return _stable_digest(payload)


def source_assumption_association_errors(
    association: Mapping[str, object],
) -> list[str]:
    """Validate one generated accepted-assumption semantic-parent receipt."""

    errors: list[str] = []
    if association.get("schema") != SOURCE_ASSUMPTION_ASSOCIATION_SCHEMA:
        errors.append("source-assumption association must use schema 2")
    if (
        str(association.get("association_origin") or "").strip()
        != SOURCE_ASSUMPTION_ASSOCIATION_ORIGIN
    ):
        errors.append("source-assumption association has an invalid origin")
    if (
        str(association.get("role") or "").strip()
        != SOURCE_ASSUMPTION_ASSOCIATION_ROLE
    ):
        errors.append("source-assumption association has an invalid role")

    declaration = association.get("reviewed_declaration_identity")
    signature = association.get("reviewed_elaborated_signature_identity")
    declaration_name = (
        str(declaration.get("qualified_declaration") or "").strip()
        if isinstance(declaration, Mapping)
        else ""
    )
    declaration_sha = (
        str(declaration.get("declaration_sha256") or "").strip().lower()
        if isinstance(declaration, Mapping)
        else ""
    )
    signature_name = (
        str(signature.get("qualified_declaration") or "").strip()
        if isinstance(signature, Mapping)
        else ""
    )
    signature_sha = (
        str(signature.get("elaborated_signature_sha256") or "").strip().lower()
        if isinstance(signature, Mapping)
        else ""
    )
    if (
        not declaration_name
        or not _SHA256_RE.fullmatch(declaration_sha)
        or signature_name != declaration_name
        or not _SHA256_RE.fullmatch(signature_sha)
    ):
        errors.append(
            "source-assumption association lacks an exact declaration/signature identity"
        )

    raw_source_identities = association.get("source_item_identities")
    source_identities = (
        raw_source_identities if isinstance(raw_source_identities, list) else []
    )
    source_semantic_digests: list[str] = []
    source_map_digests: dict[str, str] = {}
    for index, raw_identity in enumerate(source_identities):
        if not isinstance(raw_identity, Mapping):
            errors.append(
                f"source-assumption source_item_identities[{index}] is malformed"
            )
            continue
        source_key = str(raw_identity.get("source_key") or "").strip()
        source_location = str(raw_identity.get("source_location") or "").strip()
        source_semantic_sha = str(
            raw_identity.get("source_semantic_sha256") or ""
        ).strip().lower()
        source_map_sha = str(
            raw_identity.get("source_map_item_sha256") or ""
        ).strip().lower()
        if (
            not source_key
            or not source_location
            or not _SHA256_RE.fullmatch(source_semantic_sha)
            or not _SHA256_RE.fullmatch(source_map_sha)
        ):
            errors.append(
                f"source-assumption source_item_identities[{index}] lacks current content pins"
            )
            continue
        if source_key in source_map_digests:
            errors.append("source-assumption source identities duplicate a navigation key")
            continue
        source_map_digests[source_key] = source_map_sha
        source_semantic_digests.append(source_semantic_sha)
    if (
        not source_identities
        or len(source_semantic_digests) != len(source_identities)
        or len(source_semantic_digests) != len(set(source_semantic_digests))
    ):
        errors.append(
            "source-assumption association has no unique source semantic identities"
        )

    source_keys = association.get("source_map_item_keys")
    source_sha_by_key = association.get("source_map_item_sha256_by_key")
    if (
        not isinstance(source_keys, list)
        or sorted(str(value).strip() for value in source_keys)
        != sorted(source_map_digests)
        or not isinstance(source_sha_by_key, Mapping)
        or {
            str(key).strip(): str(value).strip().lower()
            for key, value in source_sha_by_key.items()
        }
        != source_map_digests
    ):
        errors.append(
            "source-assumption association navigation keys do not match its source identities"
        )
    if str(association.get("source_map_item_keys_sha256") or "").strip().lower() != _stable_digest(
        sorted(source_map_digests)
    ):
        errors.append("source-assumption association has a stale source-key inventory pin")

    review_identity = association.get(SOURCE_ASSUMPTION_REVIEW_IDENTITY_FIELD)
    if not isinstance(review_identity, Mapping) or review_identity.get(
        "schema"
    ) != SOURCE_ASSUMPTION_REVIEW_IDENTITY_SCHEMA:
        errors.append("source-assumption association has no review identity")
        review_identity = {}
    for field in (
        "declaration_content_sha256",
        "elaborated_signature_sha256",
        "manifest_structure_sha256",
        "semantic_dependency_sha256",
        "review_validator_identity_sha256",
        "review_protocol_sha256",
        "assumption_review_semantic_sha256",
    ):
        if not _SHA256_RE.fullmatch(
            str(review_identity.get(field) or "").strip().lower()
        ):
            errors.append("source-assumption review identity has no valid " + field)
    if str(
        review_identity.get("declaration_content_sha256") or ""
    ).strip().lower() != declaration_sha:
        errors.append("source-assumption review does not bind declaration content")
    if str(
        review_identity.get("elaborated_signature_sha256") or ""
    ).strip().lower() != signature_sha:
        errors.append("source-assumption review does not bind the elaborated signature")
    if (
        str(review_identity.get("judgment") or "").strip().lower()
        not in SOURCE_ASSUMPTION_ACCEPTED_JUDGMENTS
    ):
        errors.append("source-assumption review has no accepted source judgment")

    lean_partition = review_identity.get("lean_semantic_partition")
    errors.extend(lean_semantic_partition_errors(lean_partition))
    expected_components = (
        {
            str(component.get("component_occurrence_sha256") or "")
            .strip()
            .lower()
            for component in lean_partition.get("components", [])
            if isinstance(component, Mapping)
        }
        if isinstance(lean_partition, Mapping)
        else set()
    )
    lean_partition_sha = (
        str(lean_partition.get("partition_sha256") or "").strip().lower()
        if isinstance(lean_partition, Mapping)
        else ""
    )

    raw_premises = review_identity.get("premise_receipts")
    premise_receipts = raw_premises if isinstance(raw_premises, list) else []
    premise_route_digests: set[str] = set()
    premise_review_digests: list[str] = []
    premise_by_review_sha: dict[str, tuple[set[str], int]] = {}
    component_review_coverage: dict[str, set[str]] = {}
    for index, raw_premise in enumerate(premise_receipts):
        if not isinstance(raw_premise, Mapping):
            errors.append(f"source-assumption premise receipt {index} is malformed")
            continue
        premise_sha = str(
            raw_premise.get("premise_review_sha256") or ""
        ).strip().lower()
        expected_premise_sha = source_assumption_premise_review_digest(raw_premise)
        presentation_count = raw_premise.get("presentation_count")
        raw_components = raw_premise.get("lean_component_occurrence_sha256s")
        components = (
            {
                str(value or "").strip().lower()
                for value in raw_components
            }
            if isinstance(raw_components, list)
            else set()
        )
        if (
            not expected_premise_sha
            or premise_sha != expected_premise_sha
            or not isinstance(presentation_count, int)
            or isinstance(presentation_count, bool)
            or presentation_count < 1
            or not components
            or len(components) != len(raw_components or [])
            or not components.issubset(expected_components)
            or premise_sha in premise_by_review_sha
        ):
            errors.append(
                f"source-assumption premise receipt {index} is incomplete or stale"
            )
            continue
        premise_by_review_sha[premise_sha] = (components, presentation_count)
        for component_sha in components:
            component_review_coverage.setdefault(component_sha, set()).add(premise_sha)
        premise_review_digests.append(premise_sha)
        raw_route_digests = raw_premise.get("source_route_semantic_sha256s")
        if isinstance(raw_route_digests, list):
            premise_route_digests.update(
                str(value or "").strip().lower() for value in raw_route_digests
            )
    raw_alias_groups = review_identity.get("premise_alias_group_receipts", [])
    alias_groups = raw_alias_groups if isinstance(raw_alias_groups, list) else []
    if not isinstance(raw_alias_groups, list):
        errors.append("source-assumption alias-group inventory is malformed")
    authorized_alias_by_component: dict[str, str] = {}
    alias_group_digests: list[str] = []
    aliased_review_shas: set[str] = set()
    for index, raw_group in enumerate(alias_groups):
        if not isinstance(raw_group, Mapping):
            errors.append(f"source-assumption alias group {index} is malformed")
            continue
        supplied_group_sha = str(
            raw_group.get("alias_group_sha256") or ""
        ).strip().lower()
        expected_group_sha = source_assumption_alias_group_digest(raw_group)
        raw_group_components = raw_group.get("lean_component_occurrence_sha256s")
        group_components = (
            {
                str(value or "").strip().lower()
                for value in raw_group_components
            }
            if isinstance(raw_group_components, list)
            else set()
        )
        raw_members = raw_group.get("members")
        group_members = (
            {
                str(member.get("premise_review_sha256") or "")
                .strip()
                .lower(): member.get("presentation_count")
                for member in raw_members
                if isinstance(member, Mapping)
            }
            if isinstance(raw_members, list)
            else {}
        )
        if (
            not expected_group_sha
            or supplied_group_sha != expected_group_sha
            or not group_components.issubset(expected_components)
            or set(group_members) & aliased_review_shas
            or any(
                review_sha not in premise_by_review_sha
                or premise_by_review_sha[review_sha][0] != group_components
                or premise_by_review_sha[review_sha][1] != count
                for review_sha, count in group_members.items()
            )
            or any(
                component_review_coverage.get(component_sha, set())
                != set(group_members)
                for component_sha in group_components
            )
            or any(
                component_sha in authorized_alias_by_component
                for component_sha in group_components
            )
        ):
            errors.append(f"source-assumption alias group {index} is incomplete or stale")
            continue
        alias_group_digests.append(supplied_group_sha)
        aliased_review_shas.update(group_members)
        for component_sha in group_components:
            authorized_alias_by_component[component_sha] = supplied_group_sha

    if set(component_review_coverage) != expected_components:
        errors.append(
            "source-assumption premise receipts omit a Lean semantic component"
        )
    for component_sha in expected_components:
        covering = component_review_coverage.get(component_sha, set())
        if len(covering) == 1:
            sole = next(iter(covering))
            if premise_by_review_sha.get(sole, (set(), 0))[1] != 1 and (
                component_sha not in authorized_alias_by_component
            ):
                errors.append(
                    "source-assumption repeated premise presentation lacks an explicit alias group"
                )
        elif component_sha not in authorized_alias_by_component:
            errors.append(
                "source-assumption Lean component is duplicated without an explicit alias group"
            )
    if any(
        count != 1 and review_sha not in aliased_review_shas
        for review_sha, (_components, count) in premise_by_review_sha.items()
    ):
        errors.append(
            "source-assumption premise presentation multiplicity is unauthenticated"
        )

    raw_routes = review_identity.get("source_route_receipts")
    routes = raw_routes if isinstance(raw_routes, list) else []
    route_semantic_digests: list[str] = []
    route_parent_digests: list[str] = []
    for index, raw_route in enumerate(routes):
        if not isinstance(raw_route, Mapping):
            errors.append(f"source-assumption route receipt {index} is malformed")
            continue
        route_sha = str(
            raw_route.get("route_semantic_sha256") or ""
        ).strip().lower()
        parent_sha = str(
            raw_route.get("source_parent_semantic_sha256") or ""
        ).strip().lower()
        source_pin = raw_route.get("source_reuse_pin")
        source_pin_sha = str(
            raw_route.get("source_reuse_pin_sha256") or ""
        ).strip().lower()
        if (
            not _SHA256_RE.fullmatch(route_sha)
            or not _SHA256_RE.fullmatch(parent_sha)
            or not isinstance(source_pin, Mapping)
            or source_pin_sha != _stable_digest(dict(source_pin))
        ):
            errors.append(
                f"source-assumption route receipt {index} lacks current semantic/source pins"
            )
        route_semantic_digests.append(route_sha)
        route_parent_digests.append(parent_sha)
    route_set = set(route_semantic_digests)
    if (
        not routes
        or len(route_semantic_digests) != len(set(route_semantic_digests))
        or set(route_parent_digests) != set(source_semantic_digests)
        or (premise_receipts and premise_route_digests != route_set)
    ):
        errors.append(
            "source-assumption source routes do not exactly cover their reviewed premises and source parents"
        )

    expected_review_semantic_sha = _stable_digest(
        {
            "schema": SOURCE_ASSUMPTION_REVIEW_IDENTITY_SCHEMA,
            "judgment": str(review_identity.get("judgment") or "").strip().lower(),
            "lean_semantic_partition_sha256": lean_partition_sha,
            "premise_reviews": sorted(
                (
                    {
                        "premise_review_sha256": review_sha,
                        "presentation_count": premise_by_review_sha[review_sha][1],
                    }
                    for review_sha in premise_review_digests
                    if review_sha in premise_by_review_sha
                ),
                key=lambda value: str(value["premise_review_sha256"]),
            ),
            "premise_alias_group_sha256s": sorted(alias_group_digests),
            "source_route_semantic_sha256s": sorted(route_semantic_digests),
        }
    )
    if str(
        review_identity.get("assumption_review_semantic_sha256") or ""
    ).strip().lower() != expected_review_semantic_sha:
        errors.append("source-assumption semantic review pin is missing or stale")

    expected_pin = assumption_source_review_semantic_association_digest(
        review_identity, source_identities, signature
    )
    supplied_pin = str(
        association.get("semantic_association_sha256") or ""
    ).strip().lower()
    if not expected_pin or supplied_pin != expected_pin:
        errors.append("source-assumption semantic association pin is missing or stale")
    if str(association.get("association_sha256") or "").strip().lower() != _association_digest(
        association
    ):
        errors.append("source-assumption full association pin is missing or stale")
    return errors


def source_assumption_effective_semantic_pin(
    association: Mapping[str, object],
) -> tuple[str, str]:
    """Return the current semantic pin or a fail-closed validation error."""

    errors = source_assumption_association_errors(association)
    if errors:
        return "", "; ".join(errors)
    pin = str(association.get("semantic_association_sha256") or "").strip().lower()
    return (pin, "") if _SHA256_RE.fullmatch(pin) else (
        "",
        "source-assumption association has no effective semantic pin",
    )


def build_source_assumption_association(
    *,
    reviewed_declaration_identity: Mapping[str, object],
    reviewed_signature_identity: Mapping[str, object],
    source_item_identities: list[dict[str, object]],
    review_identity: Mapping[str, object],
) -> tuple[dict[str, Any] | None, str]:
    """Build and self-check one generator-owned association."""

    source_keys = sorted(
        str(identity.get("source_key") or "").strip()
        for identity in source_item_identities
    )
    source_sha_by_key = {
        str(identity.get("source_key") or "").strip(): str(
            identity.get("source_map_item_sha256") or ""
        ).strip().lower()
        for identity in source_item_identities
    }
    semantic_pin = assumption_source_review_semantic_association_digest(
        review_identity, source_item_identities, reviewed_signature_identity
    )
    if not semantic_pin:
        return None, "accepted assumption review cannot form a semantic pin"
    association: dict[str, Any] = {
        "schema": SOURCE_ASSUMPTION_ASSOCIATION_SCHEMA,
        "association_origin": SOURCE_ASSUMPTION_ASSOCIATION_ORIGIN,
        "role": SOURCE_ASSUMPTION_ASSOCIATION_ROLE,
        "reviewed_declaration_identity": dict(reviewed_declaration_identity),
        "reviewed_elaborated_signature_identity": dict(
            reviewed_signature_identity
        ),
        "source_item_identities": source_item_identities,
        "source_map_item_keys": source_keys,
        "source_map_item_sha256_by_key": source_sha_by_key,
        "source_map_item_keys_sha256": _stable_digest(source_keys),
        SOURCE_ASSUMPTION_REVIEW_IDENTITY_FIELD: dict(review_identity),
        "semantic_association_sha256": semantic_pin,
        "review_scope": "complete_assumption_declaration_and_premises",
        "structural_pairing": "authenticated_assumption_review_source_routes",
    }
    association["association_sha256"] = _association_digest(association)
    effective_pin, error = source_assumption_effective_semantic_pin(association)
    if error or effective_pin != semantic_pin:
        return None, error or "source-assumption semantic pin mismatch"
    return association, ""
