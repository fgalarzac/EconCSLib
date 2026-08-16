#!/usr/bin/env python3
"""Rebase a v1 direct-route diagnostic receipt across presentation-only map edits.

This is intentionally narrower than normal source-record reuse.  It is an
external sidecar for an already-installed v1 direct-route diagnostic rebind;
the exact v1 replay remains authoritative whenever its archived map bytes are
still current.  The sidecar is considered only when that replay fails solely
because the current map bytes changed.

The rebase never identifies a source item by a map key, Lean declaration, or
judgment key.  It reconstructs a multiset of direct/Spec source descriptors
from the archived raw surface: source content/anchor identity, source kind and
claim role, contract shape/mode, and the raw alpha-normalized obligation and
signature context.  Current map items must match that multiset uniquely after
removing only the explicit source-presentation reconciliation field.  Map and
declaration strings may locate data for validation, but are never equivalence
evidence.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
import sys
import tempfile
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:  # Supports package imports and direct execution.
    from scripts import source_record_diagnostic_rebind as V1
    from scripts.source_coverage_scope import (
        filter_source_map_items_for_coverage,
        source_coverage_mode_from_map,
        source_item_coverage_sha256,
        source_named_result_environment_kinds_from_map,
    )
    from scripts.source_record_integrity import (
        _RAW_AUDIT_VOLATILE_TOP_LEVEL_FIELDS,
        canonical_digest_payload,
        source_record_audit_receipt_error,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
    import source_record_diagnostic_rebind as V1
    from source_coverage_scope import (
        filter_source_map_items_for_coverage,
        source_coverage_mode_from_map,
        source_item_coverage_sha256,
        source_named_result_environment_kinds_from_map,
    )
    from source_record_integrity import (
        _RAW_AUDIT_VOLATILE_TOP_LEVEL_FIELDS,
        canonical_digest_payload,
        source_record_audit_receipt_error,
    )


SCHEMA = 1
ARTIFACT_KIND = "source_record_direct_route_diagnostic_rebind_map_rebase"
POLICY_VERSION = "source-record-direct-route-diagnostic-map-rebase-v1"
FILENAME = "source_record_direct_route_diagnostic_rebind_map_rebase.json"
SOURCE_PRESENTATION_RECONCILIATION_FIELD = "source_presentation_reconciliation"
_SHA256_LENGTH = 64
_V1_MAP_BYTE_ERROR = (
    "direct-route diagnostic rebind statement-map bytes do not match provenance"
)
_ROUTE_FIELDS = frozenset(
    {
        "aliases",
        "lean_declarations",
        "proof_lean_declarations",
        "support_lean_declarations",
        "spec_lean_declarations",
        "evidence_declaration",
        "spec_declaration",
        "review_rows",
        "source_routes",
    }
)
_CONTRACT_DECLARATION_FIELDS = frozenset(
    {"evidence_declaration", "spec_declaration"}
)


class DirectRouteDiagnosticRebindMapRebaseError(ValueError):
    """Raised when a v1 diagnostic receipt cannot be safely map-rebased."""


def _sha256(value: object) -> str:
    candidate = str(value or "").strip().lower()
    if len(candidate) != _SHA256_LENGTH:
        return ""
    try:
        int(candidate, 16)
    except ValueError:
        return ""
    return candidate


def _bytes_sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _digest(value: object) -> str:
    encoded = json.dumps(
        canonical_digest_payload(value), sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _same(left: object, right: object) -> bool:
    return canonical_digest_payload(left) == canonical_digest_payload(right)


def _json_object(path: Path, *, label: str) -> tuple[dict[str, Any], bytes]:
    try:
        contents = path.read_bytes()
        payload = json.loads(contents)
    except (OSError, json.JSONDecodeError) as exc:
        raise DirectRouteDiagnosticRebindMapRebaseError(
            f"could not read {label}: {exc}"
        ) from exc
    if not isinstance(payload, dict):
        raise DirectRouteDiagnosticRebindMapRebaseError(f"{label} is not a JSON object")
    return payload, contents


def _paper_path(paper_dir: Path, value: object, *, label: str) -> Path:
    text = str(value or "").strip()
    candidate = Path(text)
    if not text or candidate.is_absolute() or any(part == ".." for part in candidate.parts):
        raise DirectRouteDiagnosticRebindMapRebaseError(
            f"{label} must be a normalized paper-relative path"
        )
    try:
        resolved = (paper_dir / candidate).resolve()
        resolved.relative_to(paper_dir.resolve())
    except (OSError, RuntimeError, ValueError) as exc:
        raise DirectRouteDiagnosticRebindMapRebaseError(
            f"{label} escapes the paper directory"
        ) from exc
    return resolved


def _relative_path(path: Path, paper_dir: Path) -> str:
    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise DirectRouteDiagnosticRebindMapRebaseError(
            "artifact path must remain inside the paper directory"
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


def _nonvolatile_raw_digest(raw: Mapping[str, Any]) -> str:
    return _digest(
        {
            str(key): value
            for key, value in raw.items()
            if str(key) not in _RAW_AUDIT_VOLATILE_TOP_LEVEL_FIELDS
        }
    )


def _non_map_fingerprint(fingerprint: Mapping[str, Any]) -> dict[str, Any]:
    """Retain every expensive input except the map semantic fingerprint."""

    return {
        str(key): value
        for key, value in fingerprint.items()
        if str(key) != "paper_statement_map_semantic_sha256"
    }


def _route_shape(value: object) -> object:
    """Retain route structure while deliberately discarding identifier spelling."""

    if isinstance(value, str):
        return {"type": "string", "nonempty": bool(value.strip())}
    if isinstance(value, list):
        return {"type": "list", "items": [_route_shape(item) for item in value]}
    if isinstance(value, tuple):
        return {"type": "tuple", "items": [_route_shape(item) for item in value]}
    if isinstance(value, Mapping):
        return {
            "type": "object",
            "fields": {
                str(key): _route_shape(child)
                for key, child in sorted(value.items(), key=lambda entry: str(entry[0]))
            },
        }
    return {"type": type(value).__name__, "value": value}


def _name_independent_item_content(
    value: object,
    *,
    at_item_root: bool = False,
    in_semantic_contract: bool = False,
) -> object:
    """Project one source item, removing exactly the presentation-only core.

    The two semantic-contract declaration strings and established route fields
    are reduced to structural shapes.  Every other field, including
    ``source_status`` and unknown metadata, remains literal and therefore
    fails closed.  This is not a source-side semantic identity; it is the
    sidecar's current-content pin after a successful name-independent match.
    """

    if isinstance(value, Mapping):
        projected: dict[str, object] = {}
        for raw_key, child in sorted(value.items(), key=lambda entry: str(entry[0])):
            key = str(raw_key)
            if at_item_root and key == SOURCE_PRESENTATION_RECONCILIATION_FIELD:
                continue
            normalized = key.strip().lower()
            if normalized in _ROUTE_FIELDS or (
                in_semantic_contract and normalized in _CONTRACT_DECLARATION_FIELDS
            ):
                projected[key] = _route_shape(child)
                continue
            projected[key] = _name_independent_item_content(
                child,
                in_semantic_contract=(normalized == "semantic_contract"),
            )
        return projected
    if isinstance(value, list):
        return [
            _name_independent_item_content(item, in_semantic_contract=in_semantic_contract)
            for item in value
        ]
    if isinstance(value, tuple):
        return [
            _name_independent_item_content(item, in_semantic_contract=in_semantic_contract)
            for item in value
        ]
    return value


def _source_descriptor_from_identity(identity: Mapping[str, Any]) -> tuple[dict[str, Any] | None, str]:
    contract = identity.get("semantic_contract")
    if not isinstance(contract, Mapping):
        return None, "source identity has no semantic-contract record"
    source_semantic = _sha256(identity.get("source_semantic_sha256"))
    source_kind = str(identity.get("source_kind") or "").strip()
    source_location = str(identity.get("source_location") or "").strip()
    evidence_mode = str(contract.get("evidence_mode") or "").strip()
    semantic_shape = str(contract.get("semantic_shape") or "").strip()
    if not all((source_semantic, source_kind, source_location, evidence_mode, semantic_shape)):
        return None, "source identity lacks content/anchor/kind/contract semantics"
    # Source semantic SHA binds statement text, source anchors, kind and
    # claim-bearing role via the source-map semantic projection.  The location
    # is retained as an independent anchored-presentation pin.
    return {
        "source_semantic_sha256": source_semantic,
        "source_kind": source_kind,
        "source_location": source_location,
        "contract_roles": ["direct_evidence", "transparent_spec"],
        "evidence_mode": evidence_mode,
        "semantic_shape": semantic_shape,
    }, ""


def _current_source_descriptor(item: Mapping[str, Any]) -> tuple[dict[str, Any] | None, str]:
    contract = item.get("semantic_contract")
    if not isinstance(contract, Mapping):
        return None, "selected direct/Spec item has no semantic contract"
    schema = item.get("_semantic_contract_schema")
    # The caller attaches a validated integer schema as an implementation-only
    # local copy; it is never serialized or treated as source content.
    errors = V1.semantic_contract_validation_errors(contract, schema=schema)
    if errors:
        return None, "selected semantic contract is malformed: " + "; ".join(errors)
    evidence = str(contract.get("evidence_declaration") or "").strip()
    spec = str(contract.get("spec_declaration") or "").strip()
    if not evidence or not spec or evidence == spec:
        return None, "selected semantic contract lacks distinct direct/Spec roles"
    source_semantic = source_item_coverage_sha256(dict(item), "")
    source_kind = str(item.get("source_kind") or "").strip()
    source_location = str(item.get("source_location") or "").strip()
    evidence_mode = str(contract.get("evidence_mode") or "").strip()
    semantic_shape = str(contract.get("semantic_shape") or "").strip()
    if not all((source_semantic, source_kind, source_location, evidence_mode, semantic_shape)):
        return None, "selected direct/Spec item lacks content/anchor/kind/contract semantics"
    return {
        "source_semantic_sha256": source_semantic,
        "source_kind": source_kind,
        "source_location": source_location,
        "contract_roles": ["direct_evidence", "transparent_spec"],
        "evidence_mode": evidence_mode,
        "semantic_shape": semantic_shape,
    }, ""


def _name_free_obligation_projection(value: object) -> object:
    """Retain alpha-normalized obligation data, never navigation identifiers."""

    if isinstance(value, Mapping):
        excluded = {
            "qualified_declaration",
            "reviewed_declaration_identity",
            "reviewed_elaborated_signature_identity",
            "declaration_sha256",
            "judgment_key",
            "row",
            "paired_qualified_declaration",
            "effective_declaration",
            "reviewed_declaration",
            "dependency_chain",
        }
        return {
            str(key): _name_free_obligation_projection(child)
            for key, child in sorted(value.items(), key=lambda entry: str(entry[0]))
            if str(key) not in excluded
        }
    if isinstance(value, list):
        return [_name_free_obligation_projection(item) for item in value]
    if isinstance(value, tuple):
        return [_name_free_obligation_projection(item) for item in value]
    return value


def _signature_digests(item: Mapping[str, Any]) -> tuple[list[str] | None, str]:
    values = item.get("reviewed_elaborated_signature_identities")
    if not isinstance(values, list) or not values:
        return None, "raw semantic item has no elaborated signature identities"
    digests = []
    for value in values:
        if not isinstance(value, Mapping) or not (digest := _sha256(value.get("elaborated_signature_sha256"))):
            return None, "raw semantic item has a malformed elaborated signature identity"
        digests.append(digest)
    if len(set(digests)) != len(digests):
        return None, "raw semantic item duplicates an elaborated signature identity"
    return sorted(digests), ""


def _raw_direct_spec_obligations(
    archived_raw: Mapping[str, Any],
    expected_descriptors: Mapping[str, Mapping[str, Any]],
) -> tuple[dict[str, str] | None, str]:
    """Bind each selected source descriptor to raw alpha/signature obligations."""

    semantic_items = archived_raw.get("semantic_model_items")
    if not isinstance(semantic_items, list):
        return None, "archived raw audit has no semantic_model_items list"
    grouped: dict[str, list[dict[str, Any]]] = {key: [] for key in expected_descriptors}
    roles: dict[str, set[str]] = {key: set() for key in expected_descriptors}
    for item in semantic_items:
        if not isinstance(item, Mapping):
            return None, "archived raw audit contains a non-object semantic item"
        signatures, error = _signature_digests(item)
        if error:
            continue
        assert signatures is not None
        group = item.get("semantic_contract_group")
        association = item.get("semantic_contract_source_association")
        if isinstance(group, Mapping):
            identities = group.get("source_item_identities")
            members = group.get("member_rows")
            if not isinstance(identities, list) or not isinstance(members, list):
                return None, "raw semantic-contract group is malformed"
            member_roles = {
                str(member.get("role") or "").strip()
                for member in members
                if isinstance(member, Mapping)
            }
            if member_roles != {"direct_evidence", "transparent_spec"}:
                return None, "raw semantic-contract group does not preserve direct/Spec roles"
            obligation = {
                "kind": "semantic_contract_group",
                "roles": sorted(member_roles),
                "structural_alpha_normalized_equal": group.get(
                    "structural_alpha_normalized_equal"
                ),
                "direct_evidence_type": _name_free_obligation_projection(
                    group.get("direct_evidence_type")
                ),
                "surface_root": _name_free_obligation_projection(group.get("surface_root")),
                "expanded_lean_surface": _name_free_obligation_projection(
                    item.get("expanded_lean_surface")
                ),
                "signature_sha256": signatures,
                "context_sha256": _sha256(item.get("source_record_item_context_sha256")),
            }
            if not obligation["context_sha256"]:
                return None, "raw semantic-contract group has no current scoped context digest"
            for identity in identities:
                if not isinstance(identity, Mapping):
                    return None, "raw semantic-contract group has a malformed source identity"
                descriptor, descriptor_error = _source_descriptor_from_identity(identity)
                if descriptor_error:
                    return None, descriptor_error
                assert descriptor is not None
                descriptor_digest = _digest(descriptor)
                if descriptor_digest in grouped:
                    grouped[descriptor_digest].append(obligation)
                    roles[descriptor_digest].update(member_roles)
            continue
        if not isinstance(association, Mapping):
            continue
        role = str(association.get("role") or "").strip()
        identities = association.get("source_item_identities")
        if role not in {"direct_evidence", "transparent_spec"} or not isinstance(identities, list):
            return None, "raw direct/Spec association is malformed"
        obligation = {
            "kind": "individual_semantic_contract_association",
            "role": role,
            "expanded_lean_surface": _name_free_obligation_projection(
                item.get("expanded_lean_surface")
            ),
            "signature_sha256": signatures,
            "context_sha256": _sha256(item.get("source_record_item_context_sha256")),
        }
        if not obligation["context_sha256"]:
            return None, "raw direct/Spec association has no current scoped context digest"
        for identity in identities:
            if not isinstance(identity, Mapping):
                return None, "raw direct/Spec association has a malformed source identity"
            descriptor, descriptor_error = _source_descriptor_from_identity(identity)
            if descriptor_error:
                return None, descriptor_error
            assert descriptor is not None
            descriptor_digest = _digest(descriptor)
            if descriptor_digest in grouped:
                grouped[descriptor_digest].append(obligation)
                roles[descriptor_digest].add(role)

    result: dict[str, str] = {}
    for descriptor_digest, obligations in grouped.items():
        if not obligations or roles[descriptor_digest] != {
            "direct_evidence",
            "transparent_spec",
        }:
            return None, "archived raw audit lacks a complete direct/Spec obligation pair"
        result[descriptor_digest] = _digest(sorted(obligations, key=_digest))
    return result, ""


def _expected_v1_source_descriptors(
    raw_audit: Mapping[str, Any],
) -> tuple[dict[str, dict[str, Any]] | None, str]:
    provenance = raw_audit.get(V1.DIRECT_ROUTE_DIAGNOSTIC_REBIND_FIELD)
    if not isinstance(provenance, Mapping):
        return None, "installed raw audit has no v1 direct-route diagnostic rebind"
    records = provenance.get("removed_false_positive_diagnostics")
    if not isinstance(records, list) or not records:
        return None, "v1 diagnostic rebind has no removed direct/Spec routes"
    descriptors: dict[str, dict[str, Any]] = {}
    for record in records:
        if not isinstance(record, Mapping):
            return None, "v1 diagnostic rebind has a malformed route record"
        identity = record.get("source_identity")
        if not isinstance(identity, Mapping):
            return None, "v1 diagnostic route has no source identity"
        descriptor, error = _source_descriptor_from_identity(identity)
        if error:
            return None, error
        assert descriptor is not None
        digest = _digest(descriptor)
        if digest in descriptors:
            return None, "v1 diagnostic rebind has ambiguous duplicate source semantics"
        descriptors[digest] = descriptor
    return descriptors, ""


def _current_direct_spec_descriptors(
    statement_map: Mapping[str, Any],
) -> tuple[dict[str, dict[str, Any]] | None, str]:
    raw_items = statement_map.get("items")
    schema = statement_map.get("semantic_contract_schema")
    if not isinstance(raw_items, Mapping):
        return None, "current statement map has no items object"
    if not isinstance(schema, int) or isinstance(schema, bool) or schema not in V1.SEMANTIC_CONTRACT_SCHEMAS:
        return None, "current statement map has no supported semantic-contract schema"
    mode, mode_error = source_coverage_mode_from_map(statement_map)
    if mode_error:
        return None, "current statement map has an invalid source-coverage mode"
    selected = filter_source_map_items_for_coverage(
        raw_items,
        mode,
        declared_environment_kinds=source_named_result_environment_kinds_from_map(
            statement_map
        ),
    )
    descriptors: dict[str, dict[str, Any]] = {}
    for item in selected.values():
        if not isinstance(item, Mapping) or item.get("semantic_contract") is None:
            continue
        local = dict(item)
        local["_semantic_contract_schema"] = schema
        descriptor, error = _current_source_descriptor(local)
        if error:
            return None, error
        assert descriptor is not None
        descriptor_digest = _digest(descriptor)
        if descriptor_digest in descriptors:
            return None, "current direct/Spec source descriptors are ambiguous"
        descriptors[descriptor_digest] = {
            "source_descriptor": descriptor,
            "content_sha256": _digest(
                _name_independent_item_content(item, at_item_root=True)
            ),
        }
    if not descriptors:
        return None, "current map has no selected direct/Spec source descriptors"
    return descriptors, ""


def _archived_raw_context(
    raw_audit: Mapping[str, Any], *, paper: str, paper_dir: Path
) -> tuple[dict[str, Any] | None, str]:
    provenance = raw_audit.get(V1.DIRECT_ROUTE_DIAGNOSTIC_REBIND_FIELD)
    if not isinstance(provenance, Mapping):
        return None, "installed raw audit has no v1 diagnostic rebind"
    try:
        archived_path = _paper_path(
            paper_dir, provenance.get("prior_raw_audit_path"), label="v1 archived raw"
        )
        archived_raw, archived_bytes = _json_object(archived_path, label="v1 archived raw")
    except DirectRouteDiagnosticRebindMapRebaseError as exc:
        return None, str(exc)
    if _bytes_sha256(archived_bytes) != _sha256(
        provenance.get("prior_raw_audit_file_sha256")
    ):
        return None, "archived raw bytes do not match the installed v1 receipt"
    if str(archived_raw.get("paper") or "").strip() != paper:
        return None, "archived raw audit belongs to another paper"
    if source_record_audit_receipt_error(archived_raw):
        return None, "archived raw audit receipt is invalid"
    if _sha256(archived_raw.get("source_record_audit_sha256")) != _sha256(
        provenance.get("prior_raw_audit_sha256")
    ) or _sha256(archived_raw.get("source_record_audit_integrity_sha256")) != _sha256(
        provenance.get("prior_raw_audit_integrity_sha256")
    ):
        return None, "archived raw audit identities do not match the installed v1 receipt"
    if _sha256(archived_raw.get("paper_statement_map_sha256")) != _sha256(
        provenance.get("statement_map_sha256")
    ):
        return None, "archived raw map provenance does not match the installed v1 receipt"
    return {
        "path": _relative_path(archived_path, paper_dir),
        "bytes_sha256": _bytes_sha256(archived_bytes),
        "source_record_audit_sha256": _sha256(
            archived_raw.get("source_record_audit_sha256")
        ),
        "source_record_audit_integrity_sha256": _sha256(
            archived_raw.get("source_record_audit_integrity_sha256")
        ),
        "raw": archived_raw,
    }, ""


def _sidecar_digest(receipt: Mapping[str, Any]) -> str:
    return _digest({key: value for key, value in receipt.items() if key != "rebase_sha256"})


def _context(
    *,
    root: Path,
    paper: str,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
    raw_audit_bytes: bytes,
    raw_audit_relative_path: str,
    statement_map: Mapping[str, Any],
    statement_map_bytes: bytes,
    statement_map_relative_path: str,
    current_input_fingerprint: Mapping[str, Any],
) -> tuple[dict[str, Any] | None, str]:
    if source_record_audit_receipt_error(raw_audit):
        return None, "installed v1 raw audit receipt is invalid"
    v1_error = V1.direct_route_diagnostic_rebind_error(
        root=root, paper=paper, paper_dir=paper_dir, raw_audit=raw_audit
    )
    if v1_error != _V1_MAP_BYTE_ERROR:
        return None, (
            "v1 diagnostic replay did not fail solely because current map bytes changed: "
            + (v1_error or "v1 replay is already exact")
        )
    raw_fingerprint = raw_audit.get("source_record_input_fingerprint")
    if not isinstance(raw_fingerprint, Mapping):
        return None, "installed v1 raw audit has no input fingerprint"
    raw_map_semantic = _sha256(raw_fingerprint.get("paper_statement_map_semantic_sha256"))
    if not raw_map_semantic:
        return None, "installed v1 raw audit has no semantic map fingerprint"
    if not _same(_non_map_fingerprint(raw_fingerprint), _non_map_fingerprint(current_input_fingerprint)):
        return None, "a non-map expensive-audit input changed since the v1 raw receipt"

    expected, error = _expected_v1_source_descriptors(raw_audit)
    if error:
        return None, error
    assert expected is not None
    archived, error = _archived_raw_context(raw_audit, paper=paper, paper_dir=paper_dir)
    if error:
        return None, error
    assert archived is not None
    obligations, error = _raw_direct_spec_obligations(archived["raw"], expected)
    if error:
        return None, error
    assert obligations is not None
    current, error = _current_direct_spec_descriptors(statement_map)
    if error:
        return None, error
    assert current is not None
    if set(current) != set(expected):
        return None, "current direct/Spec source semantics do not match the archived v1 multiset"
    mode, mode_error = source_coverage_mode_from_map(statement_map)
    if mode_error or str(raw_audit.get("source_coverage_mode") or "").strip() != mode:
        return None, "current source-coverage mode differs from the archived raw audit"

    # The rebase-specific semantic identity deliberately uses only source
    # content and the raw alpha/signature obligation.  The old aggregate map
    # cache hash remains an optimization, not an equivalence test here: it
    # includes map keys and Lean route spelling.
    semantic_rows = [
        {
            "source_descriptor": expected[digest],
            "raw_alpha_signature_context_sha256": obligations[digest],
        }
        for digest in sorted(expected)
    ]
    rebase_semantic_sha = _digest(semantic_rows)
    current_rows = [
        {
            "source_descriptor": current[digest]["source_descriptor"],
            "raw_alpha_signature_context_sha256": obligations[digest],
        }
        for digest in sorted(current)
    ]
    if _digest(current_rows) != rebase_semantic_sha:
        return None, "current source/obligation semantic multiset differs from the v1 raw receipt"
    provenance = raw_audit.get(V1.DIRECT_ROUTE_DIAGNOSTIC_REBIND_FIELD)
    assert isinstance(provenance, Mapping)
    installed = {
        "path": raw_audit_relative_path,
        "source_record_audit_sha256": _sha256(raw_audit.get("source_record_audit_sha256")),
        "source_record_audit_integrity_sha256": _sha256(
            raw_audit.get("source_record_audit_integrity_sha256")
        ),
        "nonvolatile_raw_sha256": _nonvolatile_raw_digest(raw_audit),
        "v1_rebind_sha256": _sha256(provenance.get("rebind_sha256")),
    }
    if not all(installed.values()):
        return None, "installed v1 raw receipt has incomplete identities"
    return {
        "archived_raw_audit": {key: value for key, value in archived.items() if key != "raw"},
        "installed_v1_rebind": installed,
        "current_statement_map": {
            "path": statement_map_relative_path,
            "bytes_sha256": _bytes_sha256(statement_map_bytes),
            "ordinary_semantic_sha256": _sha256(
                current_input_fingerprint.get("paper_statement_map_semantic_sha256")
            ),
            "rebase_semantic_sha256": rebase_semantic_sha,
        },
        "raw_current_map_semantic_sha256": raw_map_semantic,
        "non_map_input_fingerprint_sha256": _digest(_non_map_fingerprint(raw_fingerprint)),
        "selected_direct_spec_descriptors": [
            {
                "source_descriptor_sha256": digest,
                "raw_alpha_signature_context_sha256": obligations[digest],
                "current_content_sha256": current[digest]["content_sha256"],
            }
            for digest in sorted(current)
        ],
    }, ""


def build_direct_route_diagnostic_rebind_map_rebase(
    *,
    root: Path,
    paper: str,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
    raw_audit_bytes: bytes,
    raw_audit_relative_path: str,
    statement_map: Mapping[str, Any],
    statement_map_bytes: bytes,
    statement_map_relative_path: str,
    current_input_fingerprint: Mapping[str, Any],
) -> tuple[dict[str, Any] | None, str]:
    """Construct one exact sidecar candidate without a raw/Lean scan."""

    context, error = _context(
        root=root,
        paper=paper,
        paper_dir=paper_dir,
        raw_audit=raw_audit,
        raw_audit_bytes=raw_audit_bytes,
        raw_audit_relative_path=raw_audit_relative_path,
        statement_map=statement_map,
        statement_map_bytes=statement_map_bytes,
        statement_map_relative_path=statement_map_relative_path,
        current_input_fingerprint=current_input_fingerprint,
    )
    if error:
        return None, error
    assert context is not None
    receipt: dict[str, Any] = {
        "schema": SCHEMA,
        "artifact_kind": ARTIFACT_KIND,
        "policy_version": POLICY_VERSION,
        "paper": paper,
        **context,
    }
    receipt["rebase_sha256"] = _sidecar_digest(receipt)
    return receipt, ""


def validate_direct_route_diagnostic_rebind_map_rebase(
    *,
    root: Path,
    paper: str,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
    raw_audit_bytes: bytes,
    raw_audit_relative_path: str,
    statement_map: Mapping[str, Any],
    statement_map_bytes: bytes,
    statement_map_relative_path: str,
    current_input_fingerprint: Mapping[str, Any],
    receipt: Mapping[str, Any],
) -> str:
    """Replay the sidecar as an exact, fail-closed current-map transport."""

    if (
        receipt.get("schema") != SCHEMA
        or receipt.get("artifact_kind") != ARTIFACT_KIND
        or receipt.get("policy_version") != POLICY_VERSION
        or receipt.get("paper") != paper
        or _sha256(receipt.get("rebase_sha256")) != _sidecar_digest(receipt)
    ):
        return "diagnostic map-rebase sidecar fails its identity checks"
    expected, error = build_direct_route_diagnostic_rebind_map_rebase(
        root=root,
        paper=paper,
        paper_dir=paper_dir,
        raw_audit=raw_audit,
        raw_audit_bytes=raw_audit_bytes,
        raw_audit_relative_path=raw_audit_relative_path,
        statement_map=statement_map,
        statement_map_bytes=statement_map_bytes,
        statement_map_relative_path=statement_map_relative_path,
        current_input_fingerprint=current_input_fingerprint,
    )
    if error or expected is None:
        return "diagnostic map-rebase cannot be reproduced: " + (error or "unknown error")
    if not _same(expected, receipt):
        return "diagnostic map-rebase sidecar differs from its reproducible candidate"
    return ""


def direct_route_diagnostic_rebind_current_map_error(
    *,
    root: Path,
    paper: str,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
    current_input_fingerprint: Mapping[str, Any] | None,
) -> str:
    """Validate v1 exactly, then the external sidecar only for byte mismatch."""

    if V1.DIRECT_ROUTE_DIAGNOSTIC_REBIND_FIELD not in raw_audit:
        return ""
    v1_error = V1.direct_route_diagnostic_rebind_error(
        root=root, paper=paper, paper_dir=paper_dir, raw_audit=raw_audit
    )
    if not v1_error:
        return ""
    if v1_error != _V1_MAP_BYTE_ERROR:
        return "direct-route diagnostic rebind is invalid: " + v1_error
    if not isinstance(current_input_fingerprint, Mapping):
        return "current source-record input fingerprint is unavailable for diagnostic map rebase"
    raw_path = paper_dir / "audit" / "source_record_audit.json"
    map_path = paper_dir / "audit" / "paper_statement_map.json"
    sidecar_path = paper_dir / "audit" / FILENAME
    try:
        file_raw, raw_bytes = _json_object(raw_path, label="installed v1 raw audit")
        statement_map, map_bytes = _json_object(map_path, label="current statement map")
        receipt, _receipt_bytes = _json_object(sidecar_path, label="diagnostic map-rebase sidecar")
    except DirectRouteDiagnosticRebindMapRebaseError as exc:
        return str(exc)
    if _nonvolatile_raw_digest(file_raw) != _nonvolatile_raw_digest(raw_audit):
        return "installed raw audit differs from the supplied v1 receipt outside summary fields"
    return validate_direct_route_diagnostic_rebind_map_rebase(
        root=root,
        paper=paper,
        paper_dir=paper_dir,
        raw_audit=raw_audit,
        raw_audit_bytes=raw_bytes,
        raw_audit_relative_path=_relative_path(raw_path, paper_dir),
        statement_map=statement_map,
        statement_map_bytes=map_bytes,
        statement_map_relative_path=_relative_path(map_path, paper_dir),
        current_input_fingerprint=current_input_fingerprint,
        receipt=receipt,
    )


def _current_identity_from_helper(
    *, root: Path, paper: str, raw_audit: Mapping[str, Any]
) -> tuple[dict[str, Any], str]:
    """Ask the no-Lean identity mode for exact current non-map inputs."""

    fingerprint = raw_audit.get("source_record_input_fingerprint")
    max_depth = fingerprint.get("max_depth") if isinstance(fingerprint, Mapping) else None
    if not isinstance(max_depth, int) or max_depth < 0:
        return {}, "installed raw audit has malformed max_depth"
    helper = root / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
    if not helper.is_file():
        return {}, "source-record identity helper is unavailable"
    import subprocess

    try:
        proc = subprocess.run(
            [
                sys.executable,
                str(helper),
                "--root",
                str(root),
                "--paper",
                paper,
                "--identity-only",
                "--max-depth",
                str(max_depth),
            ],
            cwd=root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=60,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return {}, f"source-record identity helper could not run: {exc}"
    if proc.returncode != 0:
        return {}, "source-record identity helper failed"
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError:
        return {}, "source-record identity helper did not emit JSON"
    fingerprint = payload.get("source_record_input_fingerprint") if isinstance(payload, Mapping) else None
    if not isinstance(fingerprint, dict):
        return {}, "source-record identity helper returned no input fingerprint"
    return fingerprint, ""


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--raw-audit", type=Path)
    parser.add_argument("--statement-map", type=Path)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--write", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = _parse_args()
    root = args.root.resolve()
    paper_dir = root / "papers" / args.paper
    try:
        if not paper_dir.is_dir():
            raise DirectRouteDiagnosticRebindMapRebaseError("paper directory does not exist")
        raw_path = _paper_path(
            paper_dir, args.raw_audit or Path("audit/source_record_audit.json"), label="--raw-audit"
        )
        map_path = _paper_path(
            paper_dir, args.statement_map or Path("audit/paper_statement_map.json"), label="--statement-map"
        )
        out_path = _paper_path(
            paper_dir, args.out or Path("audit") / FILENAME, label="--out"
        )
        raw_audit, raw_bytes = _json_object(raw_path, label="installed v1 raw audit")
        statement_map, map_bytes = _json_object(map_path, label="current statement map")
        current_fingerprint, error = _current_identity_from_helper(
            root=root, paper=args.paper, raw_audit=raw_audit
        )
        if error:
            raise DirectRouteDiagnosticRebindMapRebaseError(error)
        receipt, error = build_direct_route_diagnostic_rebind_map_rebase(
            root=root,
            paper=args.paper,
            paper_dir=paper_dir,
            raw_audit=raw_audit,
            raw_audit_bytes=raw_bytes,
            raw_audit_relative_path=_relative_path(raw_path, paper_dir),
            statement_map=statement_map,
            statement_map_bytes=map_bytes,
            statement_map_relative_path=_relative_path(map_path, paper_dir),
            current_input_fingerprint=current_fingerprint,
        )
        if error or receipt is None:
            raise DirectRouteDiagnosticRebindMapRebaseError(error or "unknown rebase error")
        validation_error = validate_direct_route_diagnostic_rebind_map_rebase(
            root=root,
            paper=args.paper,
            paper_dir=paper_dir,
            raw_audit=raw_audit,
            raw_audit_bytes=raw_bytes,
            raw_audit_relative_path=_relative_path(raw_path, paper_dir),
            statement_map=statement_map,
            statement_map_bytes=map_bytes,
            statement_map_relative_path=_relative_path(map_path, paper_dir),
            current_input_fingerprint=current_fingerprint,
            receipt=receipt,
        )
        if validation_error:
            raise DirectRouteDiagnosticRebindMapRebaseError(
                "internal rebase validation failed: " + validation_error
            )
    except DirectRouteDiagnosticRebindMapRebaseError as exc:
        print(f"{args.paper}: diagnostic map-rebase refused: {exc}", file=sys.stderr)
        return 1
    contents = json.dumps(receipt, indent=2, sort_keys=True).encode("utf-8") + b"\n"
    if args.write:
        _atomic_write(out_path, contents)
        print(f"{args.paper}: wrote diagnostic map-rebase sidecar to {out_path}")
    else:
        print(f"{args.paper}: diagnostic map-rebase validates; rerun with --write")
    return 0


if __name__ == "__main__":  # pragma: no cover - CLI entry point.
    raise SystemExit(main())
