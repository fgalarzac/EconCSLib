#!/usr/bin/env python3
"""Rebind a v10 source-record receipt across an unselected-map change.

The normal source-record cache intentionally treats the complete source-map
semantic projection as an aggregate input.  That is the right default: a raw
audit must be regenerated whenever its selected source presentation, source
context, source route, or Lean-facing dependency changes.  It is needlessly
expensive, however, to regenerate an otherwise valid raw receipt solely
because an *unselected* inventory entry gained audit bookkeeping.

This module supplies a deliberately narrow external provenance receipt for
that case.  It does not edit generated judgments or pretend that map keys,
row names, or Lean declaration spellings establish semantic equivalence.  A
receipt is accepted only after reconstructing a content-addressed dependency
manifest from the current map and proving that it agrees with the completed
raw receipt's selected source identities and generated routing surface.

The receipt is external so the original Lean-checked raw artifact remains
byte-auditable.  A judgment-summary refresh is allowed to alter only the raw
audit's established volatile summary fields; all evidence-bearing fields,
including the old raw map provenance, remain exactly bound by this receipt.
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
from collections import Counter
from collections.abc import Mapping
from pathlib import Path
from types import ModuleType
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:  # Supports direct execution and package imports in focused tests.
    from scripts.source_coverage_scope import (
        filter_source_map_items_for_coverage,
        source_coverage_mode_from_map,
        source_record_source_item_record_sha256,
        source_record_source_item_semantic_sha256,
        source_named_result_environment_kinds_from_map,
    )
    from scripts.source_record_integrity import (
        canonical_digest_payload,
        source_record_audit_integrity_projection,
        source_record_audit_receipt_error,
        source_record_target_route_error,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
    from source_coverage_scope import (
        filter_source_map_items_for_coverage,
        source_coverage_mode_from_map,
        source_record_source_item_record_sha256,
        source_record_source_item_semantic_sha256,
        source_named_result_environment_kinds_from_map,
    )
    from source_record_integrity import (
        canonical_digest_payload,
        source_record_audit_integrity_projection,
        source_record_audit_receipt_error,
        source_record_target_route_error,
    )


SOURCE_RECORD_V10_PROMPT_VERSION = (
    "source-record-v10-semantic-conclusion-boundary-contract"
)
SELECTED_SURFACE_REBIND_SCHEMA = 1
SELECTED_SURFACE_REBIND_ARTIFACT_KIND = (
    "source_record_v10_selected_surface_provenance_rebind"
)
SELECTED_SURFACE_REBIND_POLICY_VERSION = (
    "source-record-v10-selected-content-routing-provenance-rebind-v1"
)
SELECTED_SURFACE_REBIND_BASENAME = "source_record_selected_surface_rebind.json"
SELECTED_SURFACE_REBIND_FIELD = "source_record_selected_surface_rebind"

_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
_ROUTE_FIELDS = (
    "lean_declarations",
    "proof_lean_declarations",
    "spec_lean_declarations",
    "support_lean_declarations",
    "semantic_bridge_declarations",
    "paper_equivalence_declarations",
    "source_equivalence_declarations",
    "library_bridge_declarations",
)
_ROOT_ROUTE_FIELDS = (
    "lean_declarations",
    "proof_lean_declarations",
    "support_lean_declarations",
)
_CONTRACT_ROUTE_FIELDS = ("evidence_declaration", "spec_declaration")
_RAW_REUSABLE_SECTIONS = (
    "boundary_input_items",
    "conclusion_dependency_items",
    "type_valued_certificate_result_items",
    "recursive_field_items",
    "semantic_model_items",
    "source_premise_consistency_items",
)


class SourceRecordSelectedSurfaceRebindError(ValueError):
    """Raised when a source-record provenance rebind is not admissible."""


def _canonical_digest(value: object) -> str:
    encoded = json.dumps(
        canonical_digest_payload(value), sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _bytes_sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _valid_sha256(value: object) -> str:
    candidate = str(value or "").strip().lower()
    return candidate if _SHA256_RE.fullmatch(candidate) else ""


def _same(left: object, right: object) -> bool:
    return canonical_digest_payload(left) == canonical_digest_payload(right)


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


def _read_json_object(path: Path) -> tuple[dict[str, Any], bytes]:
    try:
        contents = path.read_bytes()
        payload = json.loads(contents)
    except (OSError, json.JSONDecodeError) as exc:
        raise SourceRecordSelectedSurfaceRebindError(
            f"could not read JSON object at {path}: {exc}"
        ) from exc
    if not isinstance(payload, dict):
        raise SourceRecordSelectedSurfaceRebindError(f"{path} is not a JSON object")
    return payload, contents


def _paper_relative_path(path: Path, paper_dir: Path, *, label: str) -> str:
    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordSelectedSurfaceRebindError(
            f"{label} must remain inside the paper directory"
        ) from exc


def _paper_path(paper_dir: Path, value: Path, *, label: str) -> Path:
    candidate = value if value.is_absolute() else paper_dir / value
    try:
        resolved = candidate.resolve()
        resolved.relative_to(paper_dir.resolve())
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordSelectedSurfaceRebindError(
            f"{label} must remain inside the paper directory"
        ) from exc
    return resolved


def _source_descriptor(item: Mapping[str, Any]) -> dict[str, str]:
    """Return a content descriptor without a map key or Lean route name.

    The raw-audit item digest keeps source-claim and route metadata exact for
    this aggregate receipt, while excluding only validated refresh-only
    source-to-Spec fingerprints.  The source-semantic digest is the keyless
    source presentation identity used to join raw output to the current map.
    Neither map keys nor declaration spelling is a join key.
    """

    return {
        "source_semantic_sha256": source_record_source_item_semantic_sha256(
            dict(item), ""
        ),
        "source_map_item_sha256": source_record_source_item_record_sha256(item),
    }


def _descriptor_error(descriptor: Mapping[str, object], *, label: str) -> str:
    semantic = _valid_sha256(descriptor.get("source_semantic_sha256"))
    full = _valid_sha256(descriptor.get("source_map_item_sha256"))
    if not semantic or not full:
        return f"{label} lacks exact source semantic and full item digests"
    return ""


def _descriptor_list_error(
    descriptors: list[dict[str, str]], *, label: str
) -> str:
    if not descriptors:
        return f"{label} is empty"
    errors = [_descriptor_error(descriptor, label=label) for descriptor in descriptors]
    errors = [error for error in errors if error]
    if errors:
        return errors[0]
    semantic_counts = Counter(
        descriptor["source_semantic_sha256"] for descriptor in descriptors
    )
    duplicated = sorted(
        semantic for semantic, count in semantic_counts.items() if count != 1
    )
    if duplicated:
        return (
            f"{label} has ambiguous duplicate source-semantic identities: "
            + ", ".join(duplicated[:3])
        )
    full_counts = Counter(
        descriptor["source_map_item_sha256"] for descriptor in descriptors
    )
    duplicated_full = sorted(
        full for full, count in full_counts.items() if count != 1
    )
    if duplicated_full:
        return (
            f"{label} has ambiguous duplicate complete source-item descriptors: "
            + ", ".join(duplicated_full[:3])
        )
    return ""


def _current_selected_descriptors(
    statement_map: Mapping[str, Any],
) -> tuple[list[dict[str, str]], dict[str, Any], str]:
    raw_items = statement_map.get("items")
    if not isinstance(raw_items, Mapping):
        return [], {}, "current source map has no items object"
    mode, mode_error = source_coverage_mode_from_map(statement_map)
    if mode_error:
        return [], {}, "current source-coverage mode is invalid: " + mode_error
    try:
        selected = filter_source_map_items_for_coverage(
            raw_items,
            mode,
            declared_environment_kinds=source_named_result_environment_kinds_from_map(
                statement_map
            ),
        )
    except (AttributeError, KeyError, TypeError, ValueError) as exc:
        return [], {}, f"current source selector failed: {type(exc).__name__}: {exc}"
    descriptors = [_source_descriptor(item) for item in selected.values()]
    descriptor_error = _descriptor_list_error(
        descriptors, label="current selected source descriptors"
    )
    if descriptor_error:
        return [], {}, descriptor_error
    selector = {
        "source_coverage_mode": mode,
        "declared_environment_kinds": {
            str(key): str(value)
            for key, value in sorted(
                source_named_result_environment_kinds_from_map(statement_map).items()
            )
        },
        "selected_source_descriptors": sorted(
            descriptors, key=lambda descriptor: descriptor["source_semantic_sha256"]
        ),
    }
    return selector["selected_source_descriptors"], selector, ""


def _walk_source_identities(value: object, out: list[dict[str, str]]) -> None:
    if isinstance(value, Mapping):
        identities = value.get("source_item_identities")
        if isinstance(identities, list):
            for identity in identities:
                if not isinstance(identity, Mapping):
                    continue
                descriptor = {
                    "source_semantic_sha256": str(
                        identity.get("source_semantic_sha256") or ""
                    ).strip().lower(),
                    "source_map_item_sha256": str(
                        identity.get("source_map_item_sha256") or ""
                    ).strip().lower(),
                }
                # The source key may remain in the raw diagnostic record, but
                # it is intentionally not copied into this content identity.
                out.append(descriptor)
        for child in value.values():
            _walk_source_identities(child, out)
    elif isinstance(value, list):
        for child in value:
            _walk_source_identities(child, out)


def _raw_selected_descriptors(raw_audit: Mapping[str, Any]) -> tuple[list[dict[str, str]], str]:
    selected_keys = raw_audit.get("source_coverage_selected_source_items")
    if not isinstance(selected_keys, list) or not selected_keys:
        return [], "raw audit has no selected source presentation list"
    # The list's values are deliberately *not* used to join to the current
    # map.  It is solely a cardinality witness: every selected presentation
    # must have one content-pinned generated source association.
    if any(not isinstance(value, str) or not value.strip() for value in selected_keys):
        return [], "raw audit selected source presentation list is malformed"
    if len(set(selected_keys)) != len(selected_keys):
        return [], "raw audit selected source presentation list has duplicates"
    identities: list[dict[str, str]] = []
    for section in _RAW_REUSABLE_SECTIONS:
        _walk_source_identities(raw_audit.get(section), identities)
    unique = {
        (descriptor["source_semantic_sha256"], descriptor["source_map_item_sha256"]): descriptor
        for descriptor in identities
    }
    descriptors = sorted(
        unique.values(), key=lambda descriptor: descriptor["source_semantic_sha256"]
    )
    descriptor_error = _descriptor_list_error(
        descriptors, label="raw selected source descriptors"
    )
    if descriptor_error:
        return [], descriptor_error
    if len(descriptors) != len(selected_keys):
        return [], (
            "raw selected presentation count does not equal the count of unique "
            "content-pinned generated source identities"
        )
    return descriptors, ""


def _context_projection(requirement: Mapping[str, Any]) -> dict[str, Any]:
    """Mirror the generator's semantic-context payload without a map key."""

    projected: dict[str, Any] = {
        "kind": requirement.get("kind"),
        "source_location": requirement.get("source_location"),
        "explanation": requirement.get("explanation"),
        "source_anchor_evidence": requirement.get("source_anchor_evidence"),
    }
    # The one optional contract is part of the source semantic context only
    # when present.  Keeping unknown fields out here would be unsafe, so bind
    # them under an exact extension object instead.
    extensions = {
        str(key): value
        for key, value in requirement.items()
        if str(key)
        not in {
            "kind",
            "source_location",
            "explanation",
            "source_anchor_evidence",
        }
    }
    if extensions:
        projected["extensions"] = extensions
    return projected


def _current_context_descriptors(
    statement_map: Mapping[str, Any],
) -> tuple[list[dict[str, str]], str]:
    raw_items = statement_map.get("items")
    if not isinstance(raw_items, Mapping):
        return [], "current source map has no items object for semantic context"
    descriptors: list[dict[str, str]] = []
    for raw_item in raw_items.values():
        if not isinstance(raw_item, Mapping):
            return [], "current source map has a non-object item"
        requirements = raw_item.get("semantic_context_requirements")
        if requirements is None:
            continue
        if not isinstance(requirements, list):
            return [], "current source-map semantic_context_requirements is not a list"
        source = _source_descriptor(raw_item)
        if _descriptor_error(source, label="source semantic context descriptor"):
            return [], "current source semantic context has an invalid source descriptor"
        for requirement in requirements:
            if not isinstance(requirement, Mapping):
                return [], "current source semantic context has a non-object requirement"
            descriptors.append(
                {
                    **source,
                    "context_sha256": _canonical_digest(_context_projection(requirement)),
                }
            )
    counts = Counter(
        (
            descriptor["source_semantic_sha256"],
            descriptor["source_map_item_sha256"],
            descriptor["context_sha256"],
        )
        for descriptor in descriptors
    )
    duplicates = [key for key, count in counts.items() if count != 1]
    if duplicates:
        return [], "current semantic-context projection has duplicate content descriptors"
    return sorted(
        descriptors,
        key=lambda descriptor: (
            descriptor["source_semantic_sha256"],
            descriptor["context_sha256"],
        ),
    ), ""


def _raw_context_descriptors(
    raw_audit: Mapping[str, Any], current: list[dict[str, str]]
) -> tuple[list[dict[str, str]], str]:
    raw_contexts = raw_audit.get("semantic_context_requirements")
    if raw_contexts is None:
        raw_contexts = []
    if not isinstance(raw_contexts, list):
        return [], "raw audit semantic_context_requirements is not a list"
    by_context: dict[str, list[dict[str, str]]] = {}
    for descriptor in current:
        by_context.setdefault(descriptor["context_sha256"], []).append(descriptor)
    resolved: list[dict[str, str]] = []
    for raw_context in raw_contexts:
        if not isinstance(raw_context, Mapping):
            return [], "raw audit semantic context has a non-object entry"
        # The generator's raw projection has two navigation-only fields which
        # cannot select a current item.  Resolve instead through the literal,
        # byte-pinned context content, requiring a unique match.
        context = {
            key: value
            for key, value in raw_context.items()
            if key not in {"source_item_key", "requirement_index"}
        }
        digest = _canonical_digest(context)
        candidates = by_context.get(digest, [])
        if len(candidates) != 1:
            return [], (
                "raw semantic context does not resolve to one current source-content "
                "descriptor"
            )
        resolved.append(candidates[0])
    if len(resolved) != len(current) or not _same(resolved, current):
        return [], (
            "current all-item semantic-context projection differs from the raw "
            "generator context surface"
        )
    return current, ""


def _route_values(item: Mapping[str, Any], fields: tuple[str, ...]) -> list[dict[str, str]]:
    values: list[dict[str, str]] = []
    for field in fields:
        raw_values = item.get(field)
        if raw_values is None:
            continue
        if not isinstance(raw_values, list):
            values.append({"field": field, "value": "<malformed>"})
            continue
        for raw_value in raw_values:
            if not isinstance(raw_value, str) or not raw_value.strip():
                values.append({"field": field, "value": "<malformed>"})
            else:
                values.append({"field": field, "value": raw_value.strip()})
    contract = item.get("semantic_contract")
    if contract is not None:
        if not isinstance(contract, Mapping):
            values.append({"field": "semantic_contract", "value": "<malformed>"})
        else:
            for field in _CONTRACT_ROUTE_FIELDS:
                raw_value = contract.get(field)
                if raw_value is None:
                    continue
                if not isinstance(raw_value, str) or not raw_value.strip():
                    values.append(
                        {"field": f"semantic_contract.{field}", "value": "<malformed>"}
                    )
                else:
                    values.append(
                        {"field": f"semantic_contract.{field}", "value": raw_value.strip()}
                    )
    return sorted(values, key=lambda value: (value["field"], value["value"]))


def _route_projection(statement_map: Mapping[str, Any]) -> tuple[list[dict[str, Any]], str]:
    raw_items = statement_map.get("items")
    if not isinstance(raw_items, Mapping):
        return [], "current source map has no items object for source routes"
    projection: list[dict[str, Any]] = []
    for item in raw_items.values():
        if not isinstance(item, Mapping):
            return [], "current source map has a non-object source-route item"
        descriptor = _source_descriptor(item)
        if _descriptor_error(descriptor, label="source route descriptor"):
            return [], "current source route has an invalid source descriptor"
        routes = _route_values(item, _ROUTE_FIELDS)
        if routes:
            projection.append({**descriptor, "routes": routes})
    return sorted(
        projection, key=lambda entry: entry["source_semantic_sha256"]
    ), ""


def _normalize_source_map_routes(
    routing: Mapping[str, Any],
    statement_map: Mapping[str, Any],
    *,
    raw_descriptor_by_key: Mapping[str, dict[str, str]] | None = None,
) -> tuple[dict[str, Any], str]:
    """Normalize routing diagnostics to source content, never map keys.

    The raw audit's route rows retain a key for human navigation.  To compare
    it with a renamed current map, replace that coordinate with the current
    source descriptor.  Historical rows can only resolve through an exact raw
    generated source identity, not by searching a similarly named map entry.
    """

    items = statement_map.get("items")
    if not isinstance(items, Mapping):
        return {}, "source-route normalization requires a current items object"

    current_by_key: dict[str, dict[str, str]] = {}
    for raw_key, item in items.items():
        if not isinstance(item, Mapping):
            return {}, "source-route normalization found a non-object item"
        descriptor = _source_descriptor(item)
        if _descriptor_error(descriptor, label="source-route normalization"):
            return {}, "source-route normalization found an invalid source descriptor"
        current_by_key[str(raw_key)] = descriptor

    def normalize_route(route: object, *, historical: bool) -> tuple[dict[str, str] | None, str]:
        if not isinstance(route, Mapping):
            return None, "reachable auxiliary route is not an object"
        key = str(route.get("source_key") or "").strip()
        field = str(route.get("route_field") or "").strip()
        location = str(route.get("source_location") or "").strip()
        if not key or not field or not location:
            return None, "reachable auxiliary route is missing a navigation coordinate"
        descriptor = (
            raw_descriptor_by_key.get(key)
            if historical and raw_descriptor_by_key is not None
            else current_by_key.get(key)
        )
        if descriptor is None:
            return None, (
                "historical reachable auxiliary route has no content-pinned generated "
                "source identity"
                if historical
                else "current reachable auxiliary route has no current source descriptor"
            )
        return {
            **descriptor,
            "route_field": field,
            "source_location": location,
        }, ""

    dependencies = routing.get("reachable_paper_interface_auxiliary_dependencies")
    unresolved = routing.get("unresolved_reachable_paper_interface_auxiliaries")
    ambiguous = routing.get("ambiguous_reachable_paper_interface_auxiliary_references")
    quarantine_errors = routing.get(
        "reachable_paper_interface_auxiliary_quarantine_configuration_errors"
    )
    if not all(isinstance(value, list) for value in (dependencies, unresolved, ambiguous, quarantine_errors)):
        return {}, "reachable auxiliary routing has malformed top-level lists"

    historical = raw_descriptor_by_key is not None

    def normalize_dependency(value: object) -> tuple[dict[str, Any] | None, str]:
        if not isinstance(value, Mapping):
            return None, "reachable auxiliary dependency is not an object"
        routes = value.get("source_map_routes")
        if not isinstance(routes, list):
            return None, "reachable auxiliary dependency has no source-map route list"
        normalized_routes: list[dict[str, str]] = []
        for route in routes:
            normalized, error = normalize_route(route, historical=historical)
            if error:
                return None, error
            assert normalized is not None
            normalized_routes.append(normalized)
        # Declaration strings are current routing coordinates, not source
        # equivalence evidence.  The exact non-map fingerprint separately pins
        # their source file/Lean closure; they remain here only to prove the
        # generator's reachable dependency output did not change.
        return {
            "declaration": value.get("declaration"),
            "kind": value.get("kind"),
            "configuration": value.get("configuration"),
            "transitively_referenced_from": value.get("transitively_referenced_from"),
            "quarantined": value.get("quarantined"),
            "quarantine_source_reason": value.get("quarantine_source_reason"),
            "disposition": value.get("disposition"),
            "source_map_routes": sorted(
                normalized_routes,
                key=lambda route: (
                    route["source_semantic_sha256"],
                    route["route_field"],
                    route["source_location"],
                ),
            ),
        }, ""

    normalized_dependencies: list[dict[str, Any]] = []
    normalized_unresolved: list[dict[str, Any]] = []
    for source, target in (
        (dependencies, normalized_dependencies),
        (unresolved, normalized_unresolved),
    ):
        for value in source:
            normalized, error = normalize_dependency(value)
            if error:
                return {}, error
            assert normalized is not None
            target.append(normalized)
    return {
        "reachable_paper_interface_auxiliary_dependencies": sorted(
            normalized_dependencies,
            key=lambda value: _canonical_digest(value),
        ),
        "unresolved_reachable_paper_interface_auxiliaries": sorted(
            normalized_unresolved,
            key=lambda value: _canonical_digest(value),
        ),
        "ambiguous_reachable_paper_interface_auxiliary_references": sorted(
            copy.deepcopy(ambiguous), key=_canonical_digest
        ),
        "reachable_paper_interface_auxiliary_quarantine_configuration_errors": sorted(
            str(value) for value in quarantine_errors
        ),
    }, ""


def _raw_descriptor_by_navigation_key(raw_audit: Mapping[str, Any]) -> tuple[dict[str, dict[str, str]], str]:
    """Get navigation-to-content records only from generated raw identities."""

    by_key: dict[str, dict[str, str]] = {}

    def walk(value: object) -> None:
        if isinstance(value, Mapping):
            identities = value.get("source_item_identities")
            if isinstance(identities, list):
                for identity in identities:
                    if not isinstance(identity, Mapping):
                        continue
                    key = str(identity.get("source_key") or "").strip()
                    descriptor = {
                        "source_semantic_sha256": str(
                            identity.get("source_semantic_sha256") or ""
                        ).strip().lower(),
                        "source_map_item_sha256": str(
                            identity.get("source_map_item_sha256") or ""
                        ).strip().lower(),
                    }
                    if not key:
                        continue
                    if _descriptor_error(descriptor, label="raw route source identity"):
                        continue
                    prior = by_key.get(key)
                    if prior is None:
                        by_key[key] = descriptor
                    elif prior != descriptor:
                        by_key[key] = {}
            for child in value.values():
                walk(child)
        elif isinstance(value, list):
            for child in value:
                walk(child)

    for section in _RAW_REUSABLE_SECTIONS:
        walk(raw_audit.get(section))
    ambiguous = sorted(key for key, descriptor in by_key.items() if not descriptor)
    if ambiguous:
        return {}, "raw navigation key resolves to conflicting source-content identities"
    return by_key, ""


def _raw_routing_surface(raw_audit: Mapping[str, Any]) -> dict[str, Any]:
    return {
        key: copy.deepcopy(raw_audit.get(key, []))
        for key in (
            "reachable_paper_interface_auxiliary_dependencies",
            "unresolved_reachable_paper_interface_auxiliaries",
            "ambiguous_reachable_paper_interface_auxiliary_references",
            "reachable_paper_interface_auxiliary_quarantine_configuration_errors",
        )
    }


def _saved_direct_ledger_keys(raw_audit: Mapping[str, Any]) -> tuple[set[str], str]:
    values = raw_audit.get("statement_ledger_covered_boundary_input_keys")
    if values is None:
        values = []
    if not isinstance(values, list) or any(
        not isinstance(value, str) or not value.strip() for value in values
    ):
        return set(), "raw direct statement-ledger keys are malformed"
    normalized = {value.strip() for value in values}
    if len(normalized) != len(values):
        return set(), "raw direct statement-ledger keys have duplicates"
    precloseout = raw_audit.get("precloseout_contract_covered_boundary_input_keys")
    if precloseout not in (None, []):
        return set(), "raw audit has a precloseout ledger projection outside selected-surface reuse"
    return normalized, ""


def _non_map_fingerprint(fingerprint: Mapping[str, Any]) -> dict[str, Any]:
    return {
        str(key): copy.deepcopy(value)
        for key, value in fingerprint.items()
        if str(key) != "paper_statement_map_semantic_sha256"
    }


def _raw_audit_error(raw_audit: Mapping[str, Any], *, paper: str) -> str:
    if str(raw_audit.get("paper") or "").strip() != paper:
        return "raw audit paper does not match requested paper"
    if str(raw_audit.get("prompt_version") or "").strip() != SOURCE_RECORD_V10_PROMPT_VERSION:
        return "raw audit does not use the current v10 prompt"
    receipt_error = source_record_audit_receipt_error(raw_audit)
    if receipt_error:
        return "raw audit receipt is invalid: " + receipt_error
    target_route_error = source_record_target_route_error(raw_audit)
    if target_route_error:
        return "raw audit has invalid semantic target routing: " + target_route_error
    fingerprint = raw_audit.get("source_record_input_fingerprint")
    if not isinstance(fingerprint, Mapping) or fingerprint.get("no_lean") is not False:
        return "raw audit is not a completed no_lean=false receipt"
    if not _valid_sha256(raw_audit.get("paper_statement_map_sha256")):
        return "raw audit lacks a valid paper_statement_map_sha256"
    if not _valid_sha256(fingerprint.get("paper_statement_map_semantic_sha256")):
        return "raw audit lacks a valid semantic source-map fingerprint"
    return ""


def _current_lean_import_closure_from_raw(
    *, root: Path, paper_dir: Path, raw_audit: Mapping[str, Any]
) -> tuple[ModuleType | None, Path | None, object | None, object | None, str]:
    """Revalidate the raw Lean-owned closure without asking Lean for a graph.

    Selected-surface rebinding may carry a raw receipt across a narrowly
    checked source-map change, but it must never replace Lean's loaded-module
    closure with a Python import parser.  The provider validates the saved
    closure's repository source associations, current source bytes, Lake
    routing, build controls, and loaded external artifacts.  An import edit
    therefore fails closed before any parser-derived routing/root projection
    is reused.
    """

    module = _source_record_runtime_module()
    try:
        status_path = paper_dir / "status.json"
        interface_path = module.review_source_path(root, paper_dir, status_path)
        provider = module.WorktreeImportClosureProvider(
            root,
            eager_source_snapshot=False,
            allow_dirty_worktree_sources=True,
        )
        closure, closure_error = module.source_record_lean_import_closure_for_paper(
            root,
            paper_dir,
            provider=provider,
            saved_payload=dict(raw_audit),
            allow_live_lean_graph=False,
        )
    except (AttributeError, OSError, RuntimeError, TypeError, ValueError) as exc:
        return (
            None,
            None,
            None,
            None,
            "could not revalidate the saved Lean import closure: " + str(exc),
        )
    if closure is None:
        return (
            None,
            None,
            None,
            None,
            "saved Lean import closure is not current: "
            + (str(closure_error) or "unknown closure validation failure"),
        )
    raw_fingerprint = raw_audit.get("source_record_input_fingerprint")
    expected_closure_sha = (
        str(raw_fingerprint.get("lean_import_closure_sha256") or "").strip().lower()
        if isinstance(raw_fingerprint, Mapping)
        else ""
    )
    actual_closure_sha = str(getattr(closure, "sha256", "")).strip().lower()
    if not _valid_sha256(expected_closure_sha) or actual_closure_sha != expected_closure_sha:
        return (
            None,
            None,
            None,
            None,
            "saved Lean import closure does not match the raw input fingerprint",
        )
    return module, interface_path, closure, provider, ""


def _finalize_lean_import_closure_revalidation(
    module: ModuleType, provider: object
) -> str:
    """Check for mutation after all no-Lean rebind inputs have been read."""

    try:
        error = module.source_record_lean_import_closure_finalization_error(provider)
    except (AttributeError, OSError, RuntimeError, TypeError, ValueError) as exc:
        return "could not finalize Lean import-closure revalidation: " + str(exc)
    return str(error or "").strip()


def _canonical_lean_files_from_validated_closure(
    module: ModuleType,
    *,
    root: Path,
    interface_path: Path,
    lean_import_closure: object,
) -> tuple[list[Path], dict[Path, str], str]:
    """Load exactly the canonical review closure and its authenticated text.

    This intentionally has no diagnostic-import fallback.  A runtime helper
    missing the Lean-owned closure API is not evidence-equivalent to the raw
    generator and must request a fresh raw audit instead of recursively
    guessing imports from source text.
    """

    try:
        files = module.paper_interface_import_closure_lean_files(
            root,
            interface_path,
            lean_import_closure=lean_import_closure,
        )
        source_text_by_path = module.source_record_lean_import_closure_source_text(
            lean_import_closure
        )
    except (AttributeError, OSError, RuntimeError, TypeError, ValueError) as exc:
        return [], {}, "could not project the validated Lean import closure: " + str(exc)
    if not isinstance(files, list) or any(not isinstance(path, Path) for path in files):
        return [], {}, "validated Lean import closure returned malformed source files"
    resolved = sorted({path.resolve() for path in files})
    if interface_path.resolve() not in resolved:
        return [], {}, "validated Lean import closure omits the current review interface"
    if not isinstance(source_text_by_path, Mapping):
        return [], {}, "validated Lean import closure returned malformed source text"
    text_by_path = {
        Path(path).resolve(): str(text)
        for path, text in source_text_by_path.items()
        if isinstance(path, Path) and isinstance(text, str)
    }
    if set(text_by_path) != set(resolved):
        return [], {}, "validated Lean import closure source text is incomplete"
    return resolved, text_by_path, ""


def _raw_active_review_rows(
    raw_audit: Mapping[str, Any],
) -> tuple[dict[str, str], str]:
    """Return the raw selected row-to-declaration surface, fail closed."""

    configured = raw_audit.get("configured_review_rows")
    visible_inputs = raw_audit.get("row_visible_inputs")
    if not isinstance(configured, list) or not isinstance(visible_inputs, Mapping):
        return {}, "raw audit has no complete configured review-row ledger"
    rows: dict[str, str] = {}
    for record in configured:
        if not isinstance(record, Mapping):
            return {}, "raw configured review-row ledger is malformed"
        row = str(record.get("row") or "").strip()
        qualified = str(record.get("qualified_declaration") or "").strip()
        if not row or not qualified or "." not in qualified or row in rows:
            return {}, "raw configured review-row identity is malformed or duplicated"
        inputs = visible_inputs.get(row)
        if not isinstance(inputs, list) or any(
            not isinstance(item, Mapping) for item in inputs
        ):
            return {}, "raw configured review row has no valid visible-input entry"
        rows[row] = qualified
    if set(visible_inputs) != set(rows):
        return {}, "raw visible-input ledger does not exactly match configured review rows"
    return rows, ""


def _current_auxiliary_routing_from_validated_raw(
    *,
    module: ModuleType,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
) -> tuple[dict[str, Any], str]:
    """Reproject source routes over the raw Lean-elaborated dependency ledger.

    The saved closure pins the exact source modules from which the raw
    dependency graph was obtained.  Once the active review roots below match
    the raw ledger, re-running a text/name dependency search would be both
    redundant and unsound.  Keep the elaborated paths verbatim and recompute
    only the map-provided routes that may legitimately carry a renamed source
    inventory key.
    """

    routing = _raw_routing_surface(raw_audit)
    dependencies = routing["reachable_paper_interface_auxiliary_dependencies"]
    ambiguous = routing["ambiguous_reachable_paper_interface_auxiliary_references"]
    quarantine_errors = routing[
        "reachable_paper_interface_auxiliary_quarantine_configuration_errors"
    ]
    if not all(isinstance(value, list) for value in (dependencies, ambiguous, quarantine_errors)):
        return {}, "raw audit has a malformed reachable-auxiliary routing ledger"
    try:
        current_routes = module.explicitly_qualified_source_map_routes(paper_dir)
    except (AttributeError, OSError, RuntimeError, TypeError, ValueError) as exc:
        return {}, "could not reproject current auxiliary source routes: " + str(exc)
    if not isinstance(current_routes, Mapping):
        return {}, "current auxiliary source-route projection is malformed"

    current_dependencies: list[dict[str, Any]] = []
    for raw_dependency in dependencies:
        if not isinstance(raw_dependency, Mapping):
            return {}, "raw reachable auxiliary dependency is malformed"
        target = str(raw_dependency.get("declaration") or "").strip()
        paths = raw_dependency.get("transitively_referenced_from")
        if not target or not isinstance(paths, list):
            return {}, "raw reachable auxiliary dependency has no declaration or paths"
        routes = current_routes.get(target, [])
        if not isinstance(routes, list) or any(
            not isinstance(route, Mapping) for route in routes
        ):
            return {}, "current source-map auxiliary route is malformed"
        quarantined = raw_dependency.get("quarantined")
        quarantine_reason = raw_dependency.get("quarantine_source_reason")
        if not isinstance(quarantined, bool) or not isinstance(quarantine_reason, str):
            return {}, "raw reachable auxiliary quarantine disposition is malformed"
        if routes and quarantined:
            disposition = "conflicting_source_route_and_quarantine"
        elif routes:
            disposition = "explicit_source_map_route_or_support"
        elif quarantined and quarantine_reason:
            disposition = "explicit_quarantined_source_reason"
        elif quarantined:
            disposition = "quarantined_without_source_reason"
        else:
            disposition = "missing_source_map_route_or_quarantine"
        current = copy.deepcopy(dict(raw_dependency))
        current["source_map_routes"] = [dict(route) for route in routes]
        current["disposition"] = disposition
        current_dependencies.append(current)
    current_dependencies.sort(key=lambda item: str(item["declaration"]))
    unresolved = [
        item for item in current_dependencies
        if item["disposition"]
        not in {
            "explicit_source_map_route_or_support",
            "explicit_quarantined_source_reason",
        }
    ]
    return {
        "reachable_paper_interface_auxiliary_dependencies": current_dependencies,
        "unresolved_reachable_paper_interface_auxiliaries": unresolved,
        "ambiguous_reachable_paper_interface_auxiliary_references": copy.deepcopy(ambiguous),
        "reachable_paper_interface_auxiliary_quarantine_configuration_errors": copy.deepcopy(
            quarantine_errors
        ),
    }, ""


def _routing_and_roots_from_runtime(
    *,
    root: Path,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
    module: ModuleType,
    interface_path: Path,
    lean_import_closure: object,
) -> tuple[dict[str, Any], list[str], str]:
    """Recompute the generator's routing/root inputs without Lean execution.

    The source-record module supplies these static parsers.  Importing it is
    deferred until this function is called so its normal generator can import
    this sidecar validator without a module-initialization cycle.  Every path
    here is a parser/file-hash operation; it neither builds nor invokes Lean.
    """

    try:
        status_path = paper_dir / "status.json"
        canonical_lean_files, source_text_by_path, closure_error = (
            _canonical_lean_files_from_validated_closure(
                module,
                root=root,
                interface_path=interface_path,
                lean_import_closure=lean_import_closure,
            )
        )
        if closure_error:
            return {}, [], closure_error
        interface_text = source_text_by_path.get(interface_path.resolve())
        if interface_text is None:
            return {}, [], "validated Lean import closure has no review-interface text"
        row_namespace = module.first_declaration_namespace(
            interface_path, source_text=interface_text
        )
        configured_rows = module.parse_status_rows(status_path)
        interface_declarations = module.parse_declarations(
            interface_path, source_text=interface_text
        )
        assumptions_path = module.assumption_source_path(
            root, paper_dir, status_path, interface_path=interface_path
        )
        assumption_declarations: dict[str, str] = {}
        assumption_namespace = ""
        if assumptions_path is not None and assumptions_path.exists():
            assumption_text = source_text_by_path.get(assumptions_path.resolve())
            if assumption_text is None:
                assumption_text = assumptions_path.read_text(encoding="utf-8")
            assumption_declarations = module.parse_declarations(
                assumptions_path, source_text=assumption_text
            )
            assumption_namespace = module.first_declaration_namespace(
                assumptions_path, source_text=assumption_text
            )

        qualified_rows: dict[str, str] = {}
        configured_declarations: dict[str, str] = {}
        configured_present: list[str] = []
        for row in configured_rows:
            interface_match = module.resolve_declaration_reference(
                row, interface_declarations, preferred_namespace=row_namespace
            )
            assumption_match = module.resolve_declaration_reference(
                row,
                assumption_declarations,
                preferred_namespace=assumption_namespace,
            )
            matches = [name for name in (interface_match, assumption_match) if name]
            if len(set(matches)) != 1:
                return {}, [], "current configured review route is missing or ambiguous"
            qualified = matches[0]
            configured_present.append(row)
            qualified_rows[row] = qualified
            configured_declarations[row] = (
                interface_declarations.get(qualified)
                or assumption_declarations.get(qualified)
                or ""
            )
            if not configured_declarations[row]:
                return {}, [], "current configured review declaration source is missing"
        source_selected, _selected_map, _selection = module.source_coverage_review_rows(
            paper_dir, configured_present, qualified_rows
        )
        configured_assumption_references = set(
            module.parse_status_review_surface_names(status_path, ("assumption_names",))
        )
        configured_assumption_rows = [
            row for row in configured_present if row in configured_assumption_references
        ]
        scope_targets, scope_errors = (
            module.formalization_scope_target_declarations_for_semantic_review(status_path)
        )
        explicit_source_targets, explicit_source_target_config_errors = (
            module.explicit_source_target_declarations_for_semantic_review(status_path)
        )
        explicit_source_target_rows, explicit_source_target_selection = (
            module.explicit_source_target_review_rows(
                paper_dir,
                configured_present,
                qualified_rows,
                explicit_source_targets,
            )
        )
        row_names, semantic_selection = module.effective_source_record_review_rows(
            source_selected_rows=source_selected,
            configured_present=configured_present,
            qualified_row_refs=qualified_rows,
            configured_assumption_rows=configured_assumption_rows,
            formalization_scope_targets=scope_targets,
            explicit_source_target_rows=explicit_source_target_rows,
        )
        semantic_selection.update(explicit_source_target_selection)
        target_route_errors = (
            list(semantic_selection.get("semantic_model_scope_target_route_errors") or [])
            + list(
                semantic_selection.get(
                    "semantic_model_explicit_source_target_route_errors"
                )
                or []
            )
            + list(
                semantic_selection.get(
                    "semantic_model_explicit_source_target_effective_row_errors"
                )
                or []
            )
        )
        if scope_errors or explicit_source_target_config_errors or target_route_errors:
            return {}, [], "current semantic review target routing is invalid"
        raw_active_rows, raw_active_error = _raw_active_review_rows(raw_audit)
        current_active_rows = {
            row: qualified_rows[row]
            for row in row_names
            if row in qualified_rows
        }
        if raw_active_error or current_active_rows != raw_active_rows:
            return (
                {},
                [],
                raw_active_error
                or "current source selection differs from the raw elaborated review surface",
            )
        local_files = [
            path
            for path in canonical_lean_files
            if path == interface_path.resolve() or paper_dir.resolve() in path.parents
        ]
        lean_files = list(canonical_lean_files)
        semantic_declarations = module.parse_local_declarations(
            root,
            lean_files,
            source_text_by_path=source_text_by_path,
        )
        routing, routing_error = _current_auxiliary_routing_from_validated_raw(
            module=module,
            paper_dir=paper_dir,
            raw_audit=raw_audit,
        )
        if routing_error:
            return {}, [], routing_error
        local_source_files = {
            module.repository_relative_path(root, path) for path in local_files
        }
        structures = module.parse_structures(
            root,
            lean_files,
            source_text_by_path=source_text_by_path,
            local_declarations=semantic_declarations,
        )
        paper_local_structures = {
            name: structure
            for name, structure in structures.items()
            if structure.source_file in local_source_files
        }
        candidate_structures = module.audit_candidate_structures(
            structures, paper_local_structures
        )
        structure_aliases = module.parse_structure_aliases(
            lean_files,
            structures,
            source_text_by_path=source_text_by_path,
            local_declarations=semantic_declarations,
        )
        parameter_counts = module.structure_parameter_counts(structures)
        proposition_aliases = module.parse_proposition_aliases(semantic_declarations)
        row_records: set[str] = set()
        for row in row_names:
            qualified = qualified_rows.get(row)
            declaration = configured_declarations.get(row)
            if not qualified or not declaration:
                return {}, [], "current active review row has no exact declaration"
            surface = module.semantic_model_review_effective_surface(
                reviewed_qualified_name=qualified,
                reviewed_declaration=declaration,
                semantic_declarations=semantic_declarations,
            )
            context_namespace = (
                surface.analysis_qualified_name.rsplit(".", 1)[0]
                if "." in surface.analysis_qualified_name
                else ""
            )
            row_records.update(
                module.mentioned_structures_in_delta_expanded_scoped_inputs(
                    surface.visible_inputs,
                    candidate_structures,
                    structure_aliases,
                    proposition_aliases=proposition_aliases,
                    semantic_declarations=semantic_declarations,
                    context_namespace=context_namespace,
                    structure_parameter_counts=parameter_counts,
                )
            )
        # This is the complete root set passed to the raw generator's Lean
        # source-premise consistency phase: active-row records plus every
        # explicitly source-mapped record route.  Equality below is important;
        # subset acceptance would let a source-mapped root silently disappear.
        roots = sorted(
            row_records | module.source_mapped_record_roots(paper_dir, structures)
        )
        return routing, roots, ""
    except (OSError, ValueError, KeyError, TypeError, SourceRecordSelectedSurfaceRebindError) as exc:
        return {}, [], f"could not derive current routing/root surface: {exc}"


def _source_record_runtime_module() -> ModuleType:
    """Return the installed source-record module without assuming its name."""

    target = (ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py").resolve()
    for module in tuple(sys.modules.values()):
        if module is None:
            continue
        raw_file = getattr(module, "__file__", None)
        if raw_file is None:
            continue
        try:
            if Path(raw_file).resolve() == target:
                return module
        except (OSError, RuntimeError):
            continue
    module_name = "_source_record_audit_selected_surface_runtime"
    existing = sys.modules.get(module_name)
    if isinstance(existing, ModuleType):
        return existing
    spec = importlib.util.spec_from_file_location(module_name, target)
    if spec is None or spec.loader is None:
        raise SourceRecordSelectedSurfaceRebindError(
            "could not load the source-record static routing helpers"
        )
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


def _current_input_fingerprint(
    *,
    root: Path,
    paper_dir: Path,
    paper: str,
    raw_audit: Mapping[str, Any],
    module: ModuleType,
    lean_import_closure: object,
) -> tuple[dict[str, Any] | None, str]:
    raw_fingerprint = raw_audit.get("source_record_input_fingerprint")
    if not isinstance(raw_fingerprint, Mapping):
        return None, "raw audit has no input fingerprint"
    map_sha, semantic_map_sha = module.paper_statement_map_cache_receipts(paper_dir)
    if not _valid_sha256(map_sha) or not _valid_sha256(semantic_map_sha):
        return None, "current statement map has invalid cache receipts"
    args = argparse.Namespace(
        paper=paper,
        max_depth=raw_fingerprint.get("max_depth"),
        no_lean=bool(raw_fingerprint.get("no_lean")),
    )
    try:
        fingerprint = module.source_record_input_fingerprint(
            args,
            root,
            paper_dir,
            paper_statement_map_sha256=map_sha,
            paper_statement_map_semantic_sha256=semantic_map_sha,
            lean_import_closure=lean_import_closure,
        )
    except (OSError, ValueError, TypeError) as exc:
        return None, f"could not derive current source-record fingerprint: {exc}"
    if not isinstance(fingerprint, dict):
        return None, "could not derive current source-record fingerprint"
    return fingerprint, ""


def _current_direct_ledger_keys(
    *,
    root: Path,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
    module: ModuleType,
) -> tuple[set[str] | None, str]:
    saved, saved_error = _saved_direct_ledger_keys(raw_audit)
    if saved_error:
        return None, saved_error
    if not saved:
        return set(), ""
    try:
        current = module.current_direct_statement_ledger_covered_boundary_input_keys_without_lean(
            root, paper_dir, dict(raw_audit)
        )
    except (OSError, ValueError, TypeError) as exc:
        return None, f"could not revalidate direct statement ledger: {exc}"
    if not isinstance(current, set) or any(
        not isinstance(value, str) or not value.strip() for value in current
    ):
        return None, "current direct statement ledger is malformed"
    return {value.strip() for value in current}, ""


def _current_rebind_inputs(
    *, root: Path, paper_dir: Path, paper: str, raw_audit: Mapping[str, Any]
) -> tuple[
    dict[str, Any] | None,
    dict[str, Any] | None,
    list[str],
    set[str] | None,
    str,
]:
    """Return one mutation-checked current rebind surface, or a failure."""

    raw_error = _raw_audit_error(raw_audit, paper=paper)
    if raw_error:
        return None, None, [], None, raw_error
    _raw_selected, raw_selected_error = _raw_selected_descriptors(raw_audit)
    if raw_selected_error:
        return None, None, [], None, raw_selected_error
    (
        module,
        interface_path,
        lean_import_closure,
        closure_provider,
        closure_error,
    ) = _current_lean_import_closure_from_raw(
        root=root, paper_dir=paper_dir, raw_audit=raw_audit
    )
    if (
        closure_error
        or module is None
        or interface_path is None
        or lean_import_closure is None
        or closure_provider is None
    ):
        return None, None, [], None, closure_error or "missing current Lean import closure"
    fingerprint, fingerprint_error = _current_input_fingerprint(
        root=root,
        paper_dir=paper_dir,
        paper=paper,
        raw_audit=raw_audit,
        module=module,
        lean_import_closure=lean_import_closure,
    )
    raw_fingerprint = raw_audit.get("source_record_input_fingerprint")
    if fingerprint_error or fingerprint is None:
        return None, None, [], None, fingerprint_error or "missing current fingerprint"
    if not isinstance(raw_fingerprint, Mapping) or not _same(
        _non_map_fingerprint(raw_fingerprint), _non_map_fingerprint(fingerprint)
    ):
        return None, None, [], None, "current source-record input fingerprint differs outside map provenance"
    routing, roots, routing_error = _routing_and_roots_from_runtime(
        root=root,
        paper_dir=paper_dir,
        raw_audit=raw_audit,
        module=module,
        interface_path=interface_path,
        lean_import_closure=lean_import_closure,
    )
    if routing_error:
        return None, None, [], None, routing_error
    ledger, ledger_error = _current_direct_ledger_keys(
        root=root, paper_dir=paper_dir, raw_audit=raw_audit, module=module
    )
    if ledger_error or ledger is None:
        return None, None, [], None, ledger_error or "missing direct ledger revalidation"
    final_fingerprint, final_fingerprint_error = _current_input_fingerprint(
        root=root,
        paper_dir=paper_dir,
        paper=paper,
        raw_audit=raw_audit,
        module=module,
        lean_import_closure=lean_import_closure,
    )
    if (
        final_fingerprint_error
        or final_fingerprint is None
        or not _same(fingerprint, final_fingerprint)
    ):
        return (
            None,
            None,
            [],
            None,
            final_fingerprint_error
            or "source-record inputs changed while preparing selected-surface rebind",
        )
    finalization_error = _finalize_lean_import_closure_revalidation(
        module, closure_provider
    )
    if finalization_error:
        return None, None, [], None, finalization_error
    return fingerprint, routing, roots, ledger, ""


def _manifest(
    *,
    paper: str,
    raw_audit: Mapping[str, Any],
    statement_map: Mapping[str, Any],
    current_input_fingerprint: Mapping[str, Any],
    current_routing: Mapping[str, Any],
    current_source_premise_roots: list[str],
    current_direct_ledger_keys: set[str],
) -> tuple[dict[str, Any] | None, str]:
    raw_error = _raw_audit_error(raw_audit, paper=paper)
    if raw_error:
        return None, raw_error
    raw_fingerprint = raw_audit.get("source_record_input_fingerprint")
    assert isinstance(raw_fingerprint, Mapping)
    if not _same(
        _non_map_fingerprint(raw_fingerprint),
        _non_map_fingerprint(current_input_fingerprint),
    ):
        return None, "current source-record input fingerprint differs outside map provenance"
    raw_map_semantic = _valid_sha256(
        raw_fingerprint.get("paper_statement_map_semantic_sha256")
    )
    current_map_semantic = _valid_sha256(
        current_input_fingerprint.get("paper_statement_map_semantic_sha256")
    )
    if not raw_map_semantic or not current_map_semantic:
        return None, "source-record map semantic fingerprints are malformed"
    raw_selected, raw_selected_error = _raw_selected_descriptors(raw_audit)
    if raw_selected_error:
        return None, raw_selected_error
    current_selected, selector, selector_error = _current_selected_descriptors(statement_map)
    if selector_error:
        return None, selector_error
    if str(raw_audit.get("source_coverage_mode") or "").strip() != str(
        selector["source_coverage_mode"]
    ).strip():
        return None, "current source-coverage selector mode differs from the raw audit"
    # A raw v10 receipt does not serialize the selector's optional custom
    # environment map independently of the complete source map.  Do not
    # retroactively guess that an old map used the same custom environment
    # vocabulary.  This narrow rebind is available only for the ordinary
    # environment-free selector; a nonempty current declaration requires a
    # fresh raw audit (or a future generator receipt that pins it directly).
    if selector["declared_environment_kinds"]:
        return None, (
            "selected-surface rebind requires an environment-free source selector; "
            "custom environment classifications need a fresh raw receipt"
        )
    if not _same(raw_selected, current_selected):
        return None, (
            "selected source content differs from the raw audit's content-pinned "
            "source identities"
        )
    if any(
        raw_audit.get(field) not in (None, [], "")
        for field in (
            "source_coverage_mode_error",
            "source_coverage_route_errors",
            "source_coverage_unrouted_source_items",
        )
    ):
        return None, "raw audit has a source-selection error outside selected-surface reuse"

    current_contexts, context_error = _current_context_descriptors(statement_map)
    if context_error:
        return None, context_error
    contexts, raw_context_error = _raw_context_descriptors(raw_audit, current_contexts)
    if raw_context_error:
        return None, raw_context_error

    raw_descriptor_by_key, raw_descriptor_error = _raw_descriptor_by_navigation_key(
        raw_audit
    )
    if raw_descriptor_error:
        return None, raw_descriptor_error
    current_normalized_routing, current_routing_error = _normalize_source_map_routes(
        current_routing, statement_map
    )
    if current_routing_error:
        return None, current_routing_error
    raw_normalized_routing, raw_routing_error = _normalize_source_map_routes(
        _raw_routing_surface(raw_audit),
        statement_map,
        raw_descriptor_by_key=raw_descriptor_by_key,
    )
    if raw_routing_error:
        return None, raw_routing_error
    if not _same(raw_normalized_routing, current_normalized_routing):
        return None, "current reachable auxiliary routing differs from the raw audit"

    raw_roots = raw_audit.get("source_premise_consistency_scanned_record_roots")
    if not isinstance(raw_roots, list) or any(
        not isinstance(value, str) or not value.strip() for value in raw_roots
    ):
        return None, "raw source-premise root set is malformed"
    current_roots = sorted({value.strip() for value in current_source_premise_roots})
    if len(current_roots) != len(current_source_premise_roots):
        return None, "current source-premise root set has duplicates or malformed entries"
    if current_roots != sorted({value.strip() for value in raw_roots}):
        return None, "current complete source-premise root set differs from raw scanned roots"

    saved_direct, saved_direct_error = _saved_direct_ledger_keys(raw_audit)
    if saved_direct_error:
        return None, saved_direct_error
    if not saved_direct <= current_direct_ledger_keys:
        return None, "current direct statement ledger no longer covers every saved raw key"

    routes, routes_error = _route_projection(statement_map)
    if routes_error:
        return None, routes_error
    manifest: dict[str, Any] = {
        "schema": 1,
        "paper": paper,
        "non_map_input_fingerprint": _non_map_fingerprint(current_input_fingerprint),
        "canonical_source_artifact_identities": copy.deepcopy(
            current_input_fingerprint.get("source_artifact_identities")
        ),
        "feature_engine_identities": copy.deepcopy(
            current_input_fingerprint.get("audit_engine_identities")
        ),
        "source_coverage_selector": selector,
        "selected_source_descriptors": current_selected,
        "all_item_semantic_context_descriptors": contexts,
        "all_item_route_projection": routes,
        "reachable_auxiliary_routing": current_normalized_routing,
        "source_mapped_premise_roots": current_roots,
        "raw_scanned_premise_roots": sorted({value.strip() for value in raw_roots}),
        "saved_direct_statement_ledger_keys": sorted(saved_direct),
    }
    return manifest, ""


def _receipt_digest(receipt: Mapping[str, Any]) -> str:
    payload = {
        str(key): value
        for key, value in receipt.items()
        if str(key) != "receipt_sha256"
    }
    return _canonical_digest(payload)


def build_selected_surface_rebind(
    *,
    paper: str,
    raw_audit: Mapping[str, Any],
    raw_audit_bytes: bytes,
    raw_audit_relative_path: str,
    statement_map: Mapping[str, Any],
    statement_map_bytes: bytes,
    statement_map_relative_path: str,
    current_input_fingerprint: Mapping[str, Any],
    current_routing: Mapping[str, Any],
    current_source_premise_roots: list[str],
    current_direct_ledger_keys: set[str],
) -> tuple[dict[str, Any] | None, str]:
    """Build one exact external selected-surface provenance receipt.

    The caller supplies the current no-Lean fingerprint and generator routing
    derivations.  Keeping those inputs explicit makes this module testable and
    prevents a sidecar from silently choosing a different semantic surface.
    """

    raw_error = _raw_audit_error(raw_audit, paper=paper)
    if raw_error:
        return None, raw_error
    raw_map_sha = _valid_sha256(raw_audit.get("paper_statement_map_sha256"))
    current_map_sha = _bytes_sha256(statement_map_bytes)
    if raw_map_sha == current_map_sha:
        return None, "selected-surface rebind requires an actual current map provenance change"
    manifest, manifest_error = _manifest(
        paper=paper,
        raw_audit=raw_audit,
        statement_map=statement_map,
        current_input_fingerprint=current_input_fingerprint,
        current_routing=current_routing,
        current_source_premise_roots=current_source_premise_roots,
        current_direct_ledger_keys=current_direct_ledger_keys,
    )
    if manifest_error:
        return None, manifest_error
    assert manifest is not None
    current_map_semantic = _valid_sha256(
        current_input_fingerprint.get("paper_statement_map_semantic_sha256")
    )
    raw_fingerprint = raw_audit.get("source_record_input_fingerprint")
    assert isinstance(raw_fingerprint, Mapping)
    raw_map_semantic = _valid_sha256(
        raw_fingerprint.get("paper_statement_map_semantic_sha256")
    )
    if raw_map_semantic == current_map_semantic:
        return None, "selected-surface rebind requires a changed map semantic receipt"
    receipt: dict[str, Any] = {
        "schema": SELECTED_SURFACE_REBIND_SCHEMA,
        "artifact_kind": SELECTED_SURFACE_REBIND_ARTIFACT_KIND,
        "policy_version": SELECTED_SURFACE_REBIND_POLICY_VERSION,
        "paper": paper,
        "prompt_version": SOURCE_RECORD_V10_PROMPT_VERSION,
        "raw_audit": {
            "path": raw_audit_relative_path,
            # This is issuance provenance only. A later summary refresh may
            # rewrite its known volatile fields, so validation additionally
            # binds the nonvolatile integrity projection below.
            "issuance_file_sha256": _bytes_sha256(raw_audit_bytes),
            "nonvolatile_projection_sha256": _canonical_digest(
                source_record_audit_integrity_projection(raw_audit)
            ),
            "source_record_audit_sha256": raw_audit.get("source_record_audit_sha256"),
            "source_record_audit_integrity_sha256": raw_audit.get(
                "source_record_audit_integrity_sha256"
            ),
            "paper_statement_map_sha256": raw_map_sha,
            "paper_statement_map_semantic_sha256": raw_map_semantic,
        },
        "current_statement_map": {
            "path": statement_map_relative_path,
            "bytes_sha256": current_map_sha,
            "semantic_sha256": current_map_semantic,
        },
        "dependency_manifest": manifest,
    }
    receipt["receipt_sha256"] = _receipt_digest(receipt)
    return receipt, ""


def _normalized_expected_after_summary_refresh(
    expected: dict[str, Any], recorded: Mapping[str, Any]
) -> dict[str, Any]:
    """Retain issuance-byte provenance across an allowed summary refresh."""

    normalized = copy.deepcopy(expected)
    expected_raw = normalized.get("raw_audit")
    recorded_raw = recorded.get("raw_audit")
    if isinstance(expected_raw, dict) and isinstance(recorded_raw, Mapping):
        expected_raw["issuance_file_sha256"] = recorded_raw.get(
            "issuance_file_sha256"
        )
        # This is itself a volatile receipt field.  The nonvolatile projection
        # digest and aggregate source-record digest above remain exact, so
        # normalizing this transport checksum does not relax evidence.
        expected_raw["source_record_audit_integrity_sha256"] = recorded_raw.get(
            "source_record_audit_integrity_sha256"
        )
    normalized["receipt_sha256"] = _receipt_digest(normalized)
    return normalized


def validate_selected_surface_rebind(
    receipt: object,
    *,
    paper: str,
    raw_audit: Mapping[str, Any],
    raw_audit_bytes: bytes,
    raw_audit_relative_path: str,
    statement_map: Mapping[str, Any],
    statement_map_bytes: bytes,
    statement_map_relative_path: str,
    current_input_fingerprint: Mapping[str, Any],
    current_routing: Mapping[str, Any],
    current_source_premise_roots: list[str],
    current_direct_ledger_keys: set[str],
) -> str:
    """Return an error unless a receipt exactly reconstructs from live inputs."""

    if not isinstance(receipt, Mapping):
        return "selected-surface rebind is not a JSON object"
    supplied = copy.deepcopy(dict(receipt))
    if supplied.get("schema") != SELECTED_SURFACE_REBIND_SCHEMA:
        return "selected-surface rebind has an unsupported schema"
    if supplied.get("artifact_kind") != SELECTED_SURFACE_REBIND_ARTIFACT_KIND:
        return "selected-surface rebind has an unsupported artifact kind"
    if supplied.get("policy_version") != SELECTED_SURFACE_REBIND_POLICY_VERSION:
        return "selected-surface rebind has an unsupported policy version"
    if supplied.get("paper") != paper:
        return "selected-surface rebind paper does not match requested paper"
    if supplied.get("prompt_version") != SOURCE_RECORD_V10_PROMPT_VERSION:
        return "selected-surface rebind does not bind the current v10 prompt"
    supplied_digest = _valid_sha256(supplied.get("receipt_sha256"))
    if not supplied_digest or supplied_digest != _receipt_digest(supplied):
        return "selected-surface rebind has a stale receipt_sha256"
    expected, error = build_selected_surface_rebind(
        paper=paper,
        raw_audit=raw_audit,
        raw_audit_bytes=raw_audit_bytes,
        raw_audit_relative_path=raw_audit_relative_path,
        statement_map=statement_map,
        statement_map_bytes=statement_map_bytes,
        statement_map_relative_path=statement_map_relative_path,
        current_input_fingerprint=current_input_fingerprint,
        current_routing=current_routing,
        current_source_premise_roots=current_source_premise_roots,
        current_direct_ledger_keys=current_direct_ledger_keys,
    )
    if error:
        return "selected-surface rebind cannot be reconstructed: " + error
    assert expected is not None
    normalized = _normalized_expected_after_summary_refresh(expected, supplied)
    if supplied != normalized:
        return (
            "selected-surface rebind does not exactly match the current raw audit, "
            "source-content selection, context, routing, root, and fingerprint manifest"
        )
    return ""


def selected_surface_rebind_context(
    *,
    root: Path,
    paper: str,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
    raw_audit_path: Path | None = None,
    statement_map: Mapping[str, Any] | None = None,
    statement_map_path: Path | None = None,
    current_input_fingerprint: Mapping[str, Any] | None = None,
    receipt_path: Path | None = None,
) -> tuple[dict[str, Any] | None, Path, str]:
    """Load and reconstruct the optional current selected-surface receipt.

    Missing receipts are intentionally non-errors so existing exact cache
    behavior remains unchanged. A present receipt either reconstructs exactly
    or returns a fail-closed error.
    """

    canonical_receipt = receipt_path or (
        paper_dir / "audit" / SELECTED_SURFACE_REBIND_BASENAME
    )
    if not canonical_receipt.exists():
        return None, canonical_receipt, ""
    raw_path = raw_audit_path or paper_dir / "audit" / "source_record_audit.json"
    map_path = statement_map_path or paper_dir / "audit" / "paper_statement_map.json"
    try:
        raw_relative = _paper_relative_path(raw_path, paper_dir, label="raw audit")
        map_relative = _paper_relative_path(map_path, paper_dir, label="statement map")
        _paper_relative_path(canonical_receipt, paper_dir, label="selected-surface receipt")
        raw_bytes = raw_path.read_bytes()
        current_raw = json.loads(raw_bytes)
        map_bytes = map_path.read_bytes()
        current_map = json.loads(map_bytes)
        receipt_bytes = canonical_receipt.read_bytes()
        receipt = json.loads(receipt_bytes)
    except (OSError, json.JSONDecodeError, SourceRecordSelectedSurfaceRebindError) as exc:
        return None, canonical_receipt, "could not load selected-surface rebind inputs: " + str(exc)
    if not isinstance(current_raw, Mapping) or not isinstance(current_map, Mapping):
        return None, canonical_receipt, "selected-surface rebind inputs are not JSON objects"
    if current_raw != raw_audit:
        return None, canonical_receipt, "raw audit changed while loading selected-surface receipt"
    if statement_map is not None and current_map != statement_map:
        return None, canonical_receipt, "statement map changed while loading selected-surface receipt"
    fingerprint, routing, roots, ledger, rebind_error = _current_rebind_inputs(
        root=root, paper_dir=paper_dir, paper=paper, raw_audit=current_raw
    )
    if rebind_error or fingerprint is None or routing is None or ledger is None:
        return None, canonical_receipt, rebind_error or "missing current rebind inputs"
    if current_input_fingerprint is not None and not _same(
        current_input_fingerprint, fingerprint
    ):
        return (
            None,
            canonical_receipt,
            "caller-provided current fingerprint disagrees with the validated Lean closure",
        )
    error = validate_selected_surface_rebind(
        receipt,
        paper=paper,
        raw_audit=current_raw,
        raw_audit_bytes=raw_bytes,
        raw_audit_relative_path=raw_relative,
        statement_map=current_map,
        statement_map_bytes=map_bytes,
        statement_map_relative_path=map_relative,
        current_input_fingerprint=fingerprint,
        current_routing=routing,
        current_source_premise_roots=roots,
        current_direct_ledger_keys=ledger,
    )
    if error:
        return None, canonical_receipt, error
    return copy.deepcopy(dict(receipt)), canonical_receipt, ""


def selected_surface_rebind_error(
    *,
    root: Path,
    paper: str,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
    current_input_fingerprint: Mapping[str, Any] | None = None,
) -> str:
    """Validate an installed receipt; missing is reported distinctly to callers."""

    receipt, _path, error = selected_surface_rebind_context(
        root=root,
        paper=paper,
        paper_dir=paper_dir,
        raw_audit=raw_audit,
        current_input_fingerprint=current_input_fingerprint,
    )
    if error:
        return error
    if receipt is None:
        return "selected-surface rebind is not installed"
    return ""


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--raw-audit", type=Path)
    parser.add_argument("--statement-map", type=Path)
    parser.add_argument("--out", type=Path)
    parser.add_argument(
        "--write",
        action="store_true",
        help="write the validated receipt; otherwise validate only",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    paper_dir = root / "papers" / args.paper
    try:
        if not paper_dir.is_dir():
            raise SourceRecordSelectedSurfaceRebindError(
                f"paper directory does not exist: {paper_dir}"
            )
        raw_path = _paper_path(
            paper_dir,
            args.raw_audit or Path("audit/source_record_audit.json"),
            label="--raw-audit",
        )
        map_path = _paper_path(
            paper_dir,
            args.statement_map or Path("audit/paper_statement_map.json"),
            label="--statement-map",
        )
        output_path = _paper_path(
            paper_dir,
            args.out or Path("audit") / SELECTED_SURFACE_REBIND_BASENAME,
            label="--out",
        )
        raw_audit, raw_bytes = _read_json_object(raw_path)
        statement_map, map_bytes = _read_json_object(map_path)
        fingerprint, routing, roots, ledger, rebind_error = _current_rebind_inputs(
            root=root, paper_dir=paper_dir, paper=args.paper, raw_audit=raw_audit
        )
        if rebind_error or fingerprint is None or routing is None or ledger is None:
            raise SourceRecordSelectedSurfaceRebindError(
                rebind_error or "could not derive current selected-surface inputs"
            )
        receipt, error = build_selected_surface_rebind(
            paper=args.paper,
            raw_audit=raw_audit,
            raw_audit_bytes=raw_bytes,
            raw_audit_relative_path=_paper_relative_path(
                raw_path, paper_dir, label="raw audit"
            ),
            statement_map=statement_map,
            statement_map_bytes=map_bytes,
            statement_map_relative_path=_paper_relative_path(
                map_path, paper_dir, label="statement map"
            ),
            current_input_fingerprint=fingerprint,
            current_routing=routing,
            current_source_premise_roots=roots,
            current_direct_ledger_keys=ledger,
        )
        if error or receipt is None:
            raise SourceRecordSelectedSurfaceRebindError(error or "missing receipt")
        validation_error = validate_selected_surface_rebind(
            receipt,
            paper=args.paper,
            raw_audit=raw_audit,
            raw_audit_bytes=raw_bytes,
            raw_audit_relative_path=_paper_relative_path(
                raw_path, paper_dir, label="raw audit"
            ),
            statement_map=statement_map,
            statement_map_bytes=map_bytes,
            statement_map_relative_path=_paper_relative_path(
                map_path, paper_dir, label="statement map"
            ),
            current_input_fingerprint=fingerprint,
            current_routing=routing,
            current_source_premise_roots=roots,
            current_direct_ledger_keys=ledger,
        )
        if validation_error:
            raise SourceRecordSelectedSurfaceRebindError(
                "internal receipt validation failed: " + validation_error
            )
    except SourceRecordSelectedSurfaceRebindError as exc:
        print(
            f"{args.paper}: selected-surface provenance rebind refused: {exc}",
            file=sys.stderr,
        )
        return 1
    if args.write:
        _atomic_write(
            output_path,
            json.dumps(receipt, indent=2, sort_keys=True).encode("utf-8") + b"\n",
        )
        print(f"{args.paper}: wrote selected-surface provenance rebind to {output_path}")
    else:
        print(
            f"{args.paper}: selected-surface provenance rebind validates; rerun with --write"
        )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
