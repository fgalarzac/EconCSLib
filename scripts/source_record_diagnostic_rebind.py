#!/usr/bin/env python3
"""Rebind one proven direct-route diagnostic false positive without a raw scan.

The source-record generator has a deliberately narrow legacy direct-route lane
alongside its direct/transparent-Spec semantic-contract lane.  A historical
bug made the former report an error for every selected item in the latter,
despite the generated semantic-model items already carrying the exact
source-contract association.  Re-running a paper's isolated Lean audit merely
to delete that false diagnostic is wasteful and needlessly invalidates
otherwise-current review evidence.

This helper is intentionally *not* a general raw-audit editor.  It accepts
only that one diagnostic shape, validates the current source map and the raw
direct/Spec associations structurally, preserves every reusable descriptor
section exactly, archives the original raw bytes, and restamps the aggregate
receipts.  It neither scans Lean/source files nor changes judgments, source
maps, theorem statements, or proof text.
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
from pathlib import Path
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:  # Supports direct execution and package imports in focused tests.
    from scripts.audit_evidence_integrity import (
        SEMANTIC_CONTRACT_SCHEMAS,
        semantic_contract_validation_errors,
    )
    from scripts.source_coverage_scope import (
        source_record_source_item_record_sha256,
        source_record_source_item_semantic_sha256,
    )
    from scripts.source_record_freshness import SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    from scripts.source_record_integrity import (
        _RAW_AUDIT_VOLATILE_TOP_LEVEL_FIELDS,
        SOURCE_RECORD_REUSABLE_ITEM_SECTIONS,
        canonical_digest_payload,
        source_record_audit_receipt_error,
        source_record_raw_reusable_item_metadata_error,
        stamp_source_record_audit_integrity,
        attach_source_record_audit_surface,
    )
except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
    from audit_evidence_integrity import (
        SEMANTIC_CONTRACT_SCHEMAS,
        semantic_contract_validation_errors,
    )
    from source_coverage_scope import (
        source_record_source_item_record_sha256,
        source_record_source_item_semantic_sha256,
    )
    from source_record_freshness import SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    from source_record_integrity import (
        _RAW_AUDIT_VOLATILE_TOP_LEVEL_FIELDS,
        SOURCE_RECORD_REUSABLE_ITEM_SECTIONS,
        canonical_digest_payload,
        source_record_audit_receipt_error,
        source_record_raw_reusable_item_metadata_error,
        stamp_source_record_audit_integrity,
        attach_source_record_audit_surface,
    )


SOURCE_RECORD_V10_PROMPT_VERSION = (
    "source-record-v10-semantic-conclusion-boundary-contract"
)
DIRECT_ROUTE_DIAGNOSTIC_REBIND_SCHEMA = 1
DIRECT_ROUTE_DIAGNOSTIC_REBIND_KIND = (
    "source_record_direct_route_diagnostic_rebind"
)
DIRECT_ROUTE_DIAGNOSTIC_REBIND_POLICY_VERSION = (
    "source-record-direct-route-contract-lane-false-positive-rebind-v1"
)
DIRECT_ROUTE_DIAGNOSTIC_REBIND_FIELD = "source_record_direct_route_diagnostic_rebind"
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
_QUALIFIED_DECLARATION_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+$"
)


class SourceRecordDiagnosticRebindError(ValueError):
    """Raised when a raw audit is outside the narrow diagnostic-only case."""


def _canonical_digest(value: object) -> str:
    encoded = json.dumps(
        canonical_digest_payload(value), sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _sha256(value: object) -> str:
    candidate = str(value or "").strip().lower()
    return candidate if _SHA256_RE.fullmatch(candidate) else ""


def _json_object(path: Path) -> tuple[dict[str, Any], bytes]:
    try:
        contents = path.read_bytes()
        payload = json.loads(contents)
    except (OSError, json.JSONDecodeError) as exc:
        raise SourceRecordDiagnosticRebindError(
            f"could not read JSON object at {path}: {exc}"
        ) from exc
    if not isinstance(payload, dict):
        raise SourceRecordDiagnosticRebindError(f"{path} is not a JSON object")
    return payload, contents


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


def _relative_path(path: Path, paper_dir: Path) -> str:
    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordDiagnosticRebindError(
            f"path must remain inside {paper_dir}"
        ) from exc


def _paper_path(paper_dir: Path, value: Path, *, label: str) -> Path:
    candidate = value if value.is_absolute() else paper_dir / value
    try:
        resolved = candidate.resolve()
        resolved.relative_to(paper_dir.resolve())
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordDiagnosticRebindError(
            f"{label} must remain inside the paper directory"
        ) from exc
    return resolved


def _source_item_identity(source_key: str, source_item: Mapping[str, Any]) -> dict[str, Any]:
    """Recompute the exact source identity recorded by semantic-contract rows."""

    contract = source_item.get("semantic_contract")
    contract = contract if isinstance(contract, Mapping) else {}
    return {
        "source_key": source_key,
        "source_location": str(source_item.get("source_location") or "").strip(),
        "source_kind": str(source_item.get("source_kind") or "").strip(),
        "source_map_item_sha256": source_record_source_item_record_sha256(
            source_item
        ),
        "source_semantic_sha256": source_record_source_item_semantic_sha256(
            dict(source_item), ""
        ),
        "semantic_contract": {
            field: str(contract.get(field) or "").strip()
            for field in (
                "evidence_declaration",
                "spec_declaration",
                "evidence_mode",
                "semantic_shape",
            )
        },
    }


def _same(value: object, expected: object) -> bool:
    return canonical_digest_payload(value) == canonical_digest_payload(expected)


def _raw_nonvolatile_projection(value: Mapping[str, Any]) -> dict[str, Any]:
    """Keep v1 replay stable across the sanctioned judgment-summary refresh."""

    return {
        str(key): child
        for key, child in value.items()
        if str(key) not in _RAW_AUDIT_VOLATILE_TOP_LEVEL_FIELDS
    }


def _error_for_source_key(source_key: str) -> str:
    return (
        f"selected source item `{source_key}` supplies semantic_contract metadata; "
        "direct-route fallback is forbidden"
    )


def _configured_declaration_records(
    raw: Mapping[str, Any],
) -> tuple[dict[str, dict[str, Any]], str]:
    values = raw.get("configured_review_rows")
    if not isinstance(values, list):
        return {}, "raw audit has no configured_review_rows list"
    by_qualified: dict[str, dict[str, Any]] = {}
    for index, value in enumerate(values):
        if not isinstance(value, dict):
            return {}, f"configured_review_rows[{index}] is not an object"
        qualified = str(value.get("qualified_declaration") or "").strip()
        declaration = str(value.get("lean_source_declaration") or "")
        if not _QUALIFIED_DECLARATION_RE.fullmatch(qualified) or not declaration:
            return {}, f"configured_review_rows[{index}] lacks an exact declaration identity"
        if qualified in by_qualified:
            return {}, f"configured_review_rows duplicates `{qualified}`"
        by_qualified[qualified] = value
    return by_qualified, ""


def _configured_identity_matches(
    identity: object,
    *,
    qualified: str,
    configured: Mapping[str, Mapping[str, Any]],
) -> bool:
    if not isinstance(identity, Mapping):
        return False
    if str(identity.get("qualified_declaration") or "").strip() != qualified:
        return False
    record = configured.get(qualified)
    if not isinstance(record, Mapping):
        return False
    expected = hashlib.sha256(
        str(record.get("lean_source_declaration") or "").encode("utf-8")
    ).hexdigest()
    return _sha256(identity.get("declaration_sha256")) == expected


def _source_identity_present(
    identities: object, expected: Mapping[str, Any]
) -> bool:
    return isinstance(identities, list) and any(
        isinstance(value, Mapping) and _same(value, expected) for value in identities
    )


def _association_signature_is_current_for(
    association: Mapping[str, Any], qualified: str
) -> bool:
    signature = association.get("reviewed_elaborated_signature_identity")
    return (
        isinstance(signature, Mapping)
        and str(signature.get("qualified_declaration") or "").strip() == qualified
        and bool(_sha256(signature.get("elaborated_signature_sha256")))
        and bool(_sha256(association.get("semantic_association_sha256")))
    )


def _raw_contract_association_support(
    raw: Mapping[str, Any],
    *,
    source_identity: Mapping[str, Any],
    evidence: str,
    spec: str,
    configured: Mapping[str, Mapping[str, Any]],
) -> tuple[list[dict[str, Any]], str]:
    """Require a raw semantic group or two individual associations for one pair."""

    semantic_items = raw.get("semantic_model_items")
    if not isinstance(semantic_items, list):
        return [], "raw audit has no semantic_model_items list"
    support: list[dict[str, Any]] = []
    individual_roles: dict[str, list[str]] = {"direct_evidence": [], "transparent_spec": []}
    for index, item in enumerate(semantic_items):
        if not isinstance(item, Mapping):
            return [], f"semantic_model_items[{index}] is not an object"
        judgment_key = str(item.get("judgment_key") or "").strip()
        group = item.get("semantic_contract_group")
        if isinstance(group, Mapping) and _source_identity_present(
            group.get("source_item_identities"), source_identity
        ):
            members = group.get("member_rows")
            if not isinstance(members, list) or len(members) != 2:
                return [], (
                    "raw semantic-contract group for the current source identity "
                    "does not contain exactly two member rows"
                )
            expected_members = {
                "direct_evidence": evidence,
                "transparent_spec": spec,
            }
            seen_roles: set[str] = set()
            for member in members:
                if not isinstance(member, Mapping):
                    return [], "raw semantic-contract group has a non-object member row"
                role = str(member.get("role") or "").strip()
                member_qualified = str(member.get("qualified_declaration") or "").strip()
                if role not in expected_members or member_qualified != expected_members[role]:
                    return [], (
                        "raw semantic-contract group does not pin the current exact "
                        "direct/Spec pair"
                    )
                if role in seen_roles or not _configured_identity_matches(
                    member.get("reviewed_declaration_identity"),
                    qualified=member_qualified,
                    configured=configured,
                ):
                    return [], (
                        "raw semantic-contract group member does not match the current "
                        "configured declaration identity"
                    )
                seen_roles.add(role)
            if seen_roles != set(expected_members):
                return [], "raw semantic-contract group is missing a direct or Spec member"
            support.append(
                {
                    "association_mode": "semantic_contract_group",
                    "semantic_judgment_keys": [judgment_key],
                }
            )
            continue

        association = item.get("semantic_contract_source_association")
        if not isinstance(association, Mapping) or not _source_identity_present(
            association.get("source_item_identities"), source_identity
        ):
            continue
        role = str(association.get("role") or "").strip()
        reviewed = association.get("reviewed_declaration_identity")
        reviewed_qualified = (
            str(reviewed.get("qualified_declaration") or "").strip()
            if isinstance(reviewed, Mapping)
            else ""
        )
        paired = str(association.get("paired_qualified_declaration") or "").strip()
        expected_reviewed = evidence if role == "direct_evidence" else spec
        expected_paired = spec if role == "direct_evidence" else evidence
        if (
            role not in individual_roles
            or reviewed_qualified != expected_reviewed
            or paired != expected_paired
            or not _configured_identity_matches(
                reviewed, qualified=expected_reviewed, configured=configured
            )
            or not _association_signature_is_current_for(association, expected_reviewed)
        ):
            return [], (
                "raw individual semantic-contract association does not pin the "
                "current exact direct/Spec pair"
            )
        individual_roles[role].append(judgment_key)

    if support:
        return support, ""
    if all(individual_roles[role] for role in individual_roles):
        return [
            {
                "association_mode": "individual_semantic_contract_associations",
                "semantic_judgment_keys": sorted(
                    individual_roles["direct_evidence"]
                    + individual_roles["transparent_spec"]
                ),
            }
        ], ""
    return [], (
        "raw semantic-model items do not contain the current source identity "
        "on both exact direct and Spec association routes"
    )


def _raw_schema5_error(raw: Mapping[str, Any], *, paper: str) -> str:
    if str(raw.get("paper") or "").strip() != paper:
        return "raw audit paper does not match the requested paper"
    if str(raw.get("prompt_version") or "").strip() != SOURCE_RECORD_V10_PROMPT_VERSION:
        return "raw audit does not use the current v10 prompt"
    if raw.get("source_record_audit_surface_schema") != 1:
        return "raw audit does not carry the current aggregate-surface schema"
    if raw.get("source_record_audit_integrity_schema") != 1:
        return "raw audit does not carry the current raw-integrity schema"
    fingerprint = raw.get("source_record_input_fingerprint")
    if not isinstance(fingerprint, Mapping) or fingerprint.get("no_lean") is not False:
        return "raw audit is not a completed no_lean=false generated receipt"
    receipt_error = source_record_audit_receipt_error(raw)
    if receipt_error:
        return "raw audit receipt is invalid before diagnostic rebind: " + receipt_error
    item_error = source_record_raw_reusable_item_metadata_error(
        raw, expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    )
    if item_error:
        return "raw audit has invalid schema-5 reusable item metadata: " + item_error
    if DIRECT_ROUTE_DIAGNOSTIC_REBIND_FIELD in raw:
        return "raw audit already carries a direct-route diagnostic rebind"
    return ""


def _mirrored_diagnostic_error(raw: Mapping[str, Any]) -> str:
    errors = raw.get("source_contract_association_errors")
    if not isinstance(errors, list) or not errors or any(
        not isinstance(error, str) or not error for error in errors
    ):
        return "raw audit has no nonempty source-contract diagnostic error list"
    if raw.get("source_contract_association_error_count") != len(errors):
        return "raw audit source-contract diagnostic count does not match its error list"
    surface = raw.get("source_record_audit_surface")
    if not isinstance(surface, Mapping):
        return "raw audit has no aggregate surface for mirrored diagnostic validation"
    if surface.get("source_contract_association_errors") != errors:
        return "aggregate surface source-contract diagnostics do not mirror the raw audit"
    if surface.get("source_contract_association_error_count") != len(errors):
        return "aggregate surface source-contract diagnostic count is stale"
    projection = surface.get("raw_evidence_projection")
    if not isinstance(projection, Mapping):
        return "aggregate surface has no raw-evidence projection"
    if projection.get("source_contract_association_errors") != errors:
        return "raw-evidence projection source-contract diagnostics are stale"
    if projection.get("source_contract_association_error_count") != len(errors):
        return "raw-evidence projection source-contract diagnostic count is stale"
    return ""


def _rebind_delta_error(
    prior: Mapping[str, Any], candidate: Mapping[str, Any]
) -> str:
    """Prove the rebind leaves every descriptor and nonreceipt surface alone."""

    for section in SOURCE_RECORD_REUSABLE_ITEM_SECTIONS:
        if prior.get(section) != candidate.get(section):
            return f"rebind changed reusable descriptor section `{section}`"

    allowed_top_level = {
        "source_contract_association_errors",
        "source_contract_association_error_count",
        "source_record_audit_sha256",
        "source_record_audit_integrity_sha256",
        "source_record_audit_surface",
        DIRECT_ROUTE_DIAGNOSTIC_REBIND_FIELD,
    }
    prior_rest = {
        key: value for key, value in prior.items() if key not in allowed_top_level
    }
    candidate_rest = {
        key: value for key, value in candidate.items() if key not in allowed_top_level
    }
    if not _same(prior_rest, candidate_rest):
        return "rebind changed a non-diagnostic, nonreceipt top-level raw field"

    prior_surface = prior.get("source_record_audit_surface")
    candidate_surface = candidate.get("source_record_audit_surface")
    if not isinstance(prior_surface, Mapping) or not isinstance(candidate_surface, Mapping):
        return "rebind has malformed aggregate surface"
    allowed_surface = {
        "source_contract_association_errors",
        "source_contract_association_error_count",
        "raw_evidence_projection",
    }
    prior_surface_rest = {
        key: value for key, value in prior_surface.items() if key not in allowed_surface
    }
    candidate_surface_rest = {
        key: value
        for key, value in candidate_surface.items()
        if key not in allowed_surface
    }
    if not _same(prior_surface_rest, candidate_surface_rest):
        return "rebind changed a non-diagnostic aggregate-surface field"

    def projection_rest(surface: Mapping[str, Any]) -> object:
        projection = surface.get("raw_evidence_projection")
        if not isinstance(projection, Mapping):
            return None
        return {
            key: value
            for key, value in projection.items()
            if key
            not in {
                "source_contract_association_errors",
                "source_contract_association_error_count",
                DIRECT_ROUTE_DIAGNOSTIC_REBIND_FIELD,
            }
        }

    if not _same(projection_rest(prior_surface), projection_rest(candidate_surface)):
        return "rebind changed a non-diagnostic raw-evidence projection field"
    return ""


def _rebind_receipt_digest(receipt: Mapping[str, Any]) -> str:
    return _canonical_digest(
        {key: value for key, value in receipt.items() if key != "rebind_sha256"}
    )


def build_direct_route_diagnostic_rebind(
    *,
    paper: str,
    raw_audit: Mapping[str, Any],
    raw_audit_bytes: bytes,
    raw_audit_reference: str,
    statement_map: Mapping[str, Any],
    statement_map_bytes: bytes,
    statement_map_reference: str,
) -> tuple[dict[str, Any] | None, str]:
    """Return one exact diagnostic-only candidate, or a fail-closed error."""

    raw = dict(raw_audit)
    if error := _raw_schema5_error(raw, paper=paper):
        return None, error
    if error := _mirrored_diagnostic_error(raw):
        return None, error
    if _sha256(raw.get("paper_statement_map_sha256")) != _sha256_bytes(
        statement_map_bytes
    ):
        return None, "current statement-map bytes do not match the raw audit map receipt"
    raw_items = statement_map.get("items")
    if not isinstance(raw_items, Mapping):
        return None, "current statement map has no items object"
    marker = statement_map.get("semantic_contract_schema")
    if (
        not isinstance(marker, int)
        or isinstance(marker, bool)
        or marker not in SEMANTIC_CONTRACT_SCHEMAS
    ):
        return None, "current statement map has no supported semantic_contract_schema"
    selected = raw.get("source_coverage_selected_source_items")
    if not isinstance(selected, list) or not selected or any(
        not isinstance(value, str) or not value.strip() for value in selected
    ):
        return None, "raw audit has no exact selected source-item set"
    selected_keys = [value.strip() for value in selected]
    if len(set(selected_keys)) != len(selected_keys):
        return None, "raw audit selected source-item set has duplicates"

    errors = raw.get("source_contract_association_errors")
    assert isinstance(errors, list)
    error_by_key: dict[str, str] = {}
    for error in errors:
        matched = re.fullmatch(
            r"selected source item `([^`]+)` supplies semantic_contract metadata; "
            r"direct-route fallback is forbidden",
            error,
        )
        if matched is None:
            return None, "raw audit has a source-contract error outside the direct-route false-positive shape"
        source_key = matched.group(1)
        if source_key in error_by_key:
            return None, "raw audit repeats a direct-route false-positive diagnostic"
        error_by_key[source_key] = error

    configured, configured_error = _configured_declaration_records(raw)
    if configured_error:
        return None, configured_error
    contract_source_keys: set[str] = set()
    route_records: list[dict[str, Any]] = []
    for source_key in selected_keys:
        source_item = raw_items.get(source_key)
        if not isinstance(source_item, Mapping):
            return None, f"current selected source item `{source_key}` is missing or malformed"
        contract = source_item.get("semantic_contract")
        if contract is None:
            continue
        contract_source_keys.add(source_key)
        if source_item.get("claim_bearing") is not True:
            return None, f"current contract source item `{source_key}` is not claim-bearing"
        if not str(source_item.get("source_location") or "").strip():
            return None, f"current contract source item `{source_key}` has no source location"
        contract_errors = semantic_contract_validation_errors(contract, schema=marker)
        if contract_errors:
            return None, (
                f"current contract source item `{source_key}` is malformed: "
                + "; ".join(contract_errors)
            )
        assert isinstance(contract, Mapping)
        evidence = str(contract.get("evidence_declaration") or "").strip()
        spec = str(contract.get("spec_declaration") or "").strip()
        if (
            not _QUALIFIED_DECLARATION_RE.fullmatch(evidence)
            or not _QUALIFIED_DECLARATION_RE.fullmatch(spec)
            or evidence == spec
        ):
            return None, (
                f"current contract source item `{source_key}` lacks two distinct exact "
                "direct/Spec declarations"
            )
        if evidence not in configured or spec not in configured:
            return None, (
                f"current contract source item `{source_key}` does not route both "
                "direct/Spec declarations to exact configured rows"
            )
        expected_identity = _source_item_identity(source_key, source_item)
        support, support_error = _raw_contract_association_support(
            raw,
            source_identity=expected_identity,
            evidence=evidence,
            spec=spec,
            configured=configured,
        )
        if support_error:
            return None, f"current contract source item `{source_key}`: {support_error}"
        route_records.append(
            {
                "source_identity": expected_identity,
                "evidence_declaration": evidence,
                "spec_declaration": spec,
                "raw_association_support": support,
                "removed_diagnostic": error_by_key.get(source_key, ""),
            }
        )

    if set(error_by_key) != contract_source_keys:
        return None, (
            "the direct-route false-positive diagnostics do not cover exactly the "
            "selected current semantic-contract source items"
        )
    if not route_records:
        return None, "no selected current semantic-contract routes were proven"

    prior_reusable_digests = {
        section: _canonical_digest(raw.get(section))
        for section in SOURCE_RECORD_REUSABLE_ITEM_SECTIONS
    }
    provenance: dict[str, Any] = {
        "schema": DIRECT_ROUTE_DIAGNOSTIC_REBIND_SCHEMA,
        "artifact_kind": DIRECT_ROUTE_DIAGNOSTIC_REBIND_KIND,
        "policy_version": DIRECT_ROUTE_DIAGNOSTIC_REBIND_POLICY_VERSION,
        "prior_raw_audit_path": raw_audit_reference,
        "prior_raw_audit_file_sha256": _sha256_bytes(raw_audit_bytes),
        "prior_raw_audit_sha256": raw.get("source_record_audit_sha256"),
        "prior_raw_audit_integrity_sha256": raw.get(
            "source_record_audit_integrity_sha256"
        ),
        "statement_map_path": statement_map_reference,
        "statement_map_file_sha256": _sha256_bytes(statement_map_bytes),
        "statement_map_sha256": raw.get("paper_statement_map_sha256"),
        "removed_false_positive_diagnostics": sorted(
            route_records,
            key=lambda record: str(
                record["source_identity"].get("source_semantic_sha256")
            ),
        ),
        "reusable_descriptor_section_sha256_before": prior_reusable_digests,
        "diagnostic_delta": {
            "source_contract_association_errors_before": sorted(errors),
            "source_contract_association_errors_after": [],
        },
    }
    provenance["rebind_sha256"] = _rebind_receipt_digest(provenance)

    candidate = copy.deepcopy(raw)
    candidate["source_contract_association_errors"] = []
    candidate["source_contract_association_error_count"] = 0
    candidate[DIRECT_ROUTE_DIAGNOSTIC_REBIND_FIELD] = provenance
    surface = copy.deepcopy(candidate.get("source_record_audit_surface"))
    if not isinstance(surface, dict):  # protected above; retain static narrowing.
        return None, "raw audit aggregate surface became malformed during rebind"
    surface["source_contract_association_errors"] = []
    surface["source_contract_association_error_count"] = 0
    # The aggregate helper replaces this snapshot after the new provenance is
    # present, so it cannot retain an old diagnostic/error mirror.
    surface.pop("raw_evidence_projection", None)
    attach_source_record_audit_surface(candidate, surface)
    stamp_source_record_audit_integrity(candidate)

    if error := _rebind_delta_error(raw, candidate):
        return None, error
    if error := source_record_audit_receipt_error(candidate):
        return None, "internal rebind receipt failure: " + error
    if error := source_record_raw_reusable_item_metadata_error(
        candidate, expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    ):
        return None, "internal rebind changed reusable item metadata: " + error
    return candidate, ""


def direct_route_diagnostic_rebind_error(
    *,
    root: Path,
    paper: str,
    paper_dir: Path,
    raw_audit: Mapping[str, Any],
) -> str:
    """Validate an installed rebind against its archived raw and current map."""

    provenance = raw_audit.get(DIRECT_ROUTE_DIAGNOSTIC_REBIND_FIELD)
    if provenance is None:
        return ""
    if not isinstance(provenance, Mapping):
        return "direct-route diagnostic rebind provenance is malformed"
    if (
        provenance.get("schema") != DIRECT_ROUTE_DIAGNOSTIC_REBIND_SCHEMA
        or provenance.get("artifact_kind") != DIRECT_ROUTE_DIAGNOSTIC_REBIND_KIND
        or provenance.get("policy_version") != DIRECT_ROUTE_DIAGNOSTIC_REBIND_POLICY_VERSION
        or _sha256(provenance.get("rebind_sha256"))
        != _rebind_receipt_digest(provenance)
    ):
        return "direct-route diagnostic rebind provenance fails its identity checks"
    prior_name = provenance.get("prior_raw_audit_path")
    map_name = provenance.get("statement_map_path")
    if not isinstance(prior_name, str) or not isinstance(map_name, str):
        return "direct-route diagnostic rebind provenance has no local artifact paths"
    try:
        prior_path = _paper_path(paper_dir, Path(prior_name), label="prior raw")
        map_path = _paper_path(paper_dir, Path(map_name), label="statement map")
        prior, prior_bytes = _json_object(prior_path)
        statement_map, statement_map_bytes = _json_object(map_path)
    except SourceRecordDiagnosticRebindError as exc:
        return str(exc)
    if _sha256_bytes(prior_bytes) != _sha256(provenance.get("prior_raw_audit_file_sha256")):
        return "direct-route diagnostic rebind archived raw bytes do not match provenance"
    if _sha256_bytes(statement_map_bytes) != _sha256(
        provenance.get("statement_map_file_sha256")
    ):
        return "direct-route diagnostic rebind statement-map bytes do not match provenance"
    expected, error = build_direct_route_diagnostic_rebind(
        paper=paper,
        raw_audit=prior,
        raw_audit_bytes=prior_bytes,
        raw_audit_reference=prior_name,
        statement_map=statement_map,
        statement_map_bytes=statement_map_bytes,
        statement_map_reference=map_name,
    )
    if error or expected is None:
        return "direct-route diagnostic rebind cannot be reproduced: " + (error or "unknown error")
    # Summary refreshes update only the explicitly volatile judgment-derived
    # fields.  They do not alter the generated audit surface or this rebind's
    # direct/Spec provenance, so replay must not invalidate them.
    if not _same(
        _raw_nonvolatile_projection(expected),
        _raw_nonvolatile_projection(raw_audit),
    ):
        return "direct-route diagnostic rebind payload differs from its reproducible candidate"
    return ""


def _parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--raw-audit", type=Path)
    parser.add_argument("--statement-map", type=Path)
    parser.add_argument("--out", type=Path)
    parser.add_argument(
        "--replace-raw",
        action="store_true",
        help="replace --raw-audit only after archiving its exact current bytes",
    )
    parser.add_argument("--archive-prior-raw-to", type=Path)
    return parser.parse_args()


def _main() -> int:
    args = _parse_args()
    root = args.root.resolve()
    paper_dir = root / "papers" / args.paper
    try:
        if not paper_dir.is_dir():
            raise SourceRecordDiagnosticRebindError("paper directory does not exist")
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
        if args.out and args.replace_raw:
            raise SourceRecordDiagnosticRebindError(
                "--out cannot be combined with --replace-raw"
            )
        if args.replace_raw:
            if args.archive_prior_raw_to is None:
                raise SourceRecordDiagnosticRebindError(
                    "--replace-raw requires --archive-prior-raw-to"
                )
            archive_path = _paper_path(
                paper_dir, args.archive_prior_raw_to, label="--archive-prior-raw-to"
            )
            if archive_path.exists():
                raise SourceRecordDiagnosticRebindError(
                    f"refusing to overwrite prior raw archive at {archive_path}"
                )
            raw_reference = _relative_path(archive_path, paper_dir)
        else:
            archive_path = None
            raw_reference = _relative_path(raw_path, paper_dir)
        raw, raw_bytes = _json_object(raw_path)
        statement_map, statement_map_bytes = _json_object(map_path)
        candidate, error = build_direct_route_diagnostic_rebind(
            paper=args.paper,
            raw_audit=raw,
            raw_audit_bytes=raw_bytes,
            raw_audit_reference=raw_reference,
            statement_map=statement_map,
            statement_map_bytes=statement_map_bytes,
            statement_map_reference=_relative_path(map_path, paper_dir),
        )
        if error or candidate is None:
            raise SourceRecordDiagnosticRebindError(error or "unknown rebind error")
        encoded = json.dumps(candidate, indent=2, sort_keys=True).encode("utf-8") + b"\n"
        if args.replace_raw:
            assert archive_path is not None
            _atomic_write(archive_path, raw_bytes)
            _atomic_write(raw_path, encoded)
            validation_error = direct_route_diagnostic_rebind_error(
                root=root,
                paper=args.paper,
                paper_dir=paper_dir,
                raw_audit=candidate,
            )
            if validation_error:
                raise SourceRecordDiagnosticRebindError(
                    "written diagnostic rebind failed self-validation: " + validation_error
                )
            print(
                f"{args.paper}: archived prior raw and wrote direct-route diagnostic rebind "
                f"for {len(candidate[DIRECT_ROUTE_DIAGNOSTIC_REBIND_FIELD]['removed_false_positive_diagnostics'])} source routes"
            )
            return 0
        if args.out:
            out = _paper_path(paper_dir, args.out, label="--out")
            _atomic_write(out, encoded)
            print(f"{args.paper}: wrote diagnostic-rebind candidate to {out}")
            return 0
        print(
            f"{args.paper}: direct-route diagnostic rebind validates for "
            f"{len(candidate[DIRECT_ROUTE_DIAGNOSTIC_REBIND_FIELD]['removed_false_positive_diagnostics'])} source routes; "
            "rerun with --replace-raw and an archive path to install it"
        )
        return 0
    except SourceRecordDiagnosticRebindError as exc:
        print(f"{args.paper}: direct-route diagnostic rebind refused: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(_main())
