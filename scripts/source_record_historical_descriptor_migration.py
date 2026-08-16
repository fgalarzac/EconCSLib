#!/usr/bin/env python3
"""One-time, fail-closed transport of an attested v10 source-record review.

This is deliberately *not* a general semantic-descriptor normalizer.  It is a
versioned historical bridge for an archived v10 raw audit whose generator
emitted a small, enumerated set of administrative representation changes.  It
may carry only non-semantic-model groups forward.  Every semantic-model group
is deliberately left to a current manual complement.

The bridge has four non-negotiable boundaries:

* both archived raw-audit byte streams and the prior reviewed sidecar are
  immutable inputs;
* a schema-1 source association is reprojected to schema 2 only after the
  current source semantic identity, exact source-contract endpoints, current
  declaration/signature pins, and semantic-association digest all validate;
* only the explicitly listed absent/``false`` defaults, no-alias receipt, and
  terminal navigation fields may be projected; and
* result/binder/model content, source content/routes, and semantic-model rows
  remain exact.  A changed semantic-model row is manual work, not reuse.

The module is an authenticated overlay.  Serialized entries have no ordinary
freshness privilege: callers must receive them through this module's loader,
which replays the historical snapshot and rechecks the current item-level
descriptor.  This keeps a harmless later aggregate-receipt refresh from
forcing a new raw scan while failing closed on any real item drift.
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
from pathlib import Path, PurePosixPath
from typing import Any, Mapping


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

try:  # Supports direct execution and package imports in focused tests.
    from scripts.source_coverage_scope import source_item_coverage_sha256
    from scripts.source_record_current_revalidation import (
        SOURCE_RECORD_V10_PROMPT_VERSION,
        _current_item_pins,
        _raw_audit_error,
        generated_judgment_keys_sha256,
        generated_judgment_surface_sha256,
    )
    from scripts.source_record_differential_revalidation import _raw_item_groups
    from scripts.source_record_freshness import SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    from scripts.source_record_integrity import (
        canonical_digest_payload,
        source_record_item_reuse_eligible,
    )
    from scripts.source_record_target_disposition import (
        semantic_association_record_digest,
        source_contract_association_record_digest,
        source_map_item_record_digest,
    )
except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
    from source_coverage_scope import source_item_coverage_sha256
    from source_record_current_revalidation import (
        SOURCE_RECORD_V10_PROMPT_VERSION,
        _current_item_pins,
        _raw_audit_error,
        generated_judgment_keys_sha256,
        generated_judgment_surface_sha256,
    )
    from source_record_differential_revalidation import _raw_item_groups
    from source_record_freshness import SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    from source_record_integrity import (
        canonical_digest_payload,
        source_record_item_reuse_eligible,
    )
    from source_record_target_disposition import (
        semantic_association_record_digest,
        source_contract_association_record_digest,
        source_map_item_record_digest,
    )


SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_SCHEMA = 1
SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_POLICY_VERSION = (
    "source-record-v10-explicit-historical-descriptor-migration-v1"
)
SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_ARTIFACT_KIND = (
    "source_record_v10_explicit_historical_descriptor_migration"
)
SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_FILENAME = (
    "source_record_historical_descriptor_migration.json"
)
SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_INTEGRITY_FIELD = (
    "source_record_historical_descriptor_migration_sha256"
)
SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_ITEM_FIELD = (
    "source_record_historical_descriptor_migration"
)
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.I)
_LEGACY_CURRENT_REVALIDATION_POLICY_VERSION = (
    "source-record-current-manual-semantic-revalidation-v3"
)
_SIDECAR_BOUND_CURRENT_REVALIDATION_POLICY_VERSION = (
    "source-record-current-manual-semantic-revalidation-v4"
)

# This is intentionally an enumeration, not a generic "missing equals false"
# rule.  A true or non-boolean value survives the projection and therefore
# fails equality with the archived descriptor.
_ABSENT_FALSE_DEFAULT_FIELDS = frozenset(
    {
        "requires_source_carrier_coherence_analysis_when_detected",
        "measure_kernel_carrier_transport_construct",
        "terminal_term_measure_kernel_carrier_transport_surface",
    }
)
_NO_ALIAS_FIELDS = frozenset(
    {
        "alias_present",
        "complete",
        "steps",
        "blocked_routes",
        "effective_declaration",
        "effective_kind",
        "reviewed_declaration",
        "schema",
        "presentation_normalizer_schema",
    }
)
_TRANSPORT_ONLY_ITEM_FIELDS = frozenset(
    {
        "source_record_item_reuse_eligibility",
        "source_record_item_digest_schema",
        "source_record_item_semantic_id",
        "source_record_item_context_sha256",
        "source_record_item_sha256",
        "source_record_item_semantic_context_requirements_sha256",
    }
)
# These prior fields were item-level copies of aggregate/current source-map
# receipts.  The bridge instead requires the archived/current raw map digest,
# the live map bytes, and the reprojected source association below.
_REPROJECTED_ITEM_FIELDS = frozenset(
    {
        "paper_statement_map_sha256",
        "semantic_context_requirements_sha256",
        "source_contract_association",
    }
)
_CURRENT_ONLY_ITEM_FIELDS = frozenset(
    {
        # Schema 1 had no elaborated route identities or scoped proof-fidelity
        # receipt.  They are not erased: `_current_row_route_receipt` below
        # pins their freshly recomputed schema-2 values into the descriptor.
        "reviewed_elaborated_signature_identities",
        "source_record_item_source_proof_fidelity_records_sha256",
    }
)
_TERMINAL_NAVIGATION_FIELDS = frozenset(
    {"declaration", "qualified_declaration", "source_file", "line"}
)

# A historical response must never acquire authority through an older overlay.
# The archived raw response remains byte-pinned in the migration receipt, but
# its previous transport wrappers are neither replayed nor composable with the
# new one-time bridge.
_ACTIVE_PRIOR_TRANSPORT_FIELDS = frozenset(
    {
        "source_record_schema4_to5_migration",
        "source_record_differential_revalidation",
        "source_record_attested_selected_semantic_reuse",
        "authenticated_evidence_composition_item",
        "source_record_historical_descriptor_migration",
        "current_selected_semantic_revalidation_item",
        "semantic_association_rebind",
    }
)

_LOADED_OVERLAY_ITEM_SENTINEL = object()


class _LoadedHistoricalDescriptorMigrationItem(dict[str, Any]):
    __slots__ = ("_source_record_historical_descriptor_migration_loader_token",)

    def __init__(self, value: Mapping[str, Any]) -> None:
        super().__init__(value)
        self._source_record_historical_descriptor_migration_loader_token = (
            _LOADED_OVERLAY_ITEM_SENTINEL
        )


class SourceRecordHistoricalDescriptorMigrationError(ValueError):
    """Raised when the one-time historical migration is not admissible."""


def _canonical_digest(value: object) -> str:
    encoded = json.dumps(
        canonical_digest_payload(value), sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _sha256(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if _SHA256_RE.fullmatch(text) else ""


def _file_sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _read_json_object(path: Path, *, label: str) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise SourceRecordHistoricalDescriptorMigrationError(
            f"could not read {label} at {path}: {exc}"
        ) from exc
    if not isinstance(value, dict):
        raise SourceRecordHistoricalDescriptorMigrationError(
            f"{label} at {path} is not a JSON object"
        )
    return value


def _relative_paper_path(path: Path, paper_dir: Path) -> str:
    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError) as exc:
        raise SourceRecordHistoricalDescriptorMigrationError(
            f"{path} must remain inside {paper_dir}"
        ) from exc


def _resolve_paper_path(value: object, paper_dir: Path, *, label: str) -> Path:
    text = str(value or "").strip()
    pure = PurePosixPath(text)
    if (
        not text
        or pure.is_absolute()
        or any(part in {"", ".", ".."} for part in pure.parts)
    ):
        raise SourceRecordHistoricalDescriptorMigrationError(
            f"{label} must be a normalized paper-relative path"
        )
    path = (paper_dir / Path(*pure.parts)).resolve()
    if _relative_paper_path(path, paper_dir) != text:
        raise SourceRecordHistoricalDescriptorMigrationError(
            f"{label} is not canonical"
        )
    return path


def _raw_provenance(raw: Mapping[str, Any], path: Path, paper_dir: Path) -> dict[str, str]:
    return {
        "path": _relative_paper_path(path, paper_dir),
        "file_sha256": _file_sha256(path),
        "source_record_audit_sha256": _sha256(raw.get("source_record_audit_sha256")),
        "source_record_audit_integrity_sha256": _sha256(
            raw.get("source_record_audit_integrity_sha256")
        ),
        "paper_statement_map_sha256": _sha256(raw.get("paper_statement_map_sha256")),
    }


def _sidecar_provenance(path: Path, paper_dir: Path) -> dict[str, str]:
    return {
        "path": _relative_paper_path(path, paper_dir),
        "file_sha256": _file_sha256(path),
    }


def _valid_raw_audit(raw: Mapping[str, Any], *, paper: str, label: str) -> str:
    error = _raw_audit_error(raw, paper=paper)
    if error:
        return f"{label} {error}"
    if not _sha256(raw.get("paper_statement_map_sha256")):
        return f"{label} raw audit lacks paper_statement_map_sha256"
    return ""


def _source_map_error(
    statement_map: Mapping[str, Any],
    *,
    statement_map_path: Path,
    expected_sha256: str,
    label: str,
) -> str:
    if _file_sha256(statement_map_path) != expected_sha256:
        return f"{label} paper statement map does not match the raw map SHA-256"
    items = statement_map.get("items")
    if not isinstance(items, Mapping):
        return f"{label} paper statement map has no items object"
    return ""


def _source_map_items(statement_map: Mapping[str, Any]) -> Mapping[str, Any]:
    raw = statement_map.get("items")
    if not isinstance(raw, Mapping):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "paper statement map has no items object"
        )
    return raw


def _is_no_alias_receipt(value: object) -> bool:
    if value is None:
        return True
    if not isinstance(value, Mapping):
        return False
    if value.get("alias_present") is not False or value.get("complete") is not True:
        return False
    if value.get("steps") != [] or value.get("blocked_routes") != []:
        return False
    return set(value).issubset(_NO_ALIAS_FIELDS)


def _current_no_alias_receipt_error(
    value: object, current_route_receipt: Mapping[str, Any]
) -> str:
    """Validate a schema-added no-alias receipt against the pinned route."""

    if value is None:
        return ""
    if not _is_no_alias_receipt(value) or not isinstance(value, Mapping):
        return "current raw review-alias receipt is not a complete no-alias receipt"
    identity = current_route_receipt.get("reviewed_declaration_identity")
    if not isinstance(identity, Mapping):  # Defensive: caller builds it first.
        return "current raw row lacks a pinned declaration identity"
    qualified = str(identity.get("qualified_declaration") or "").strip()
    if not qualified:
        return "current raw row has a malformed pinned declaration identity"
    if value.get("schema") != 1:
        return "current raw no-alias receipt has an unsupported schema"
    if str(value.get("effective_declaration") or "").strip() != qualified or str(
        value.get("reviewed_declaration") or ""
    ).strip() != qualified:
        return "current raw no-alias receipt does not equal the pinned declaration identity"
    if not str(value.get("effective_kind") or "").strip():
        return "current raw no-alias receipt lacks an effective declaration kind"
    return ""


def _normalize_explicit_defaults(value: object) -> object:
    """Project only the three documented absent/false transport defaults."""

    if isinstance(value, Mapping):
        out: dict[str, object] = {}
        for raw_key, raw_value in value.items():
            key = str(raw_key)
            if key in _ABSENT_FALSE_DEFAULT_FIELDS and raw_value is False:
                continue
            out[key] = _normalize_explicit_defaults(raw_value)
        return out
    if isinstance(value, list):
        return [_normalize_explicit_defaults(item) for item in value]
    if isinstance(value, tuple):
        return [_normalize_explicit_defaults(item) for item in value]
    return value


def _terminal_definition_projection(value: Mapping[str, Any]) -> dict[str, object]:
    """Drop navigation only after retaining every semantic/body/closure pin."""

    body_digest = _sha256(value.get("body_sha256"))
    if not body_digest:
        raise SourceRecordHistoricalDescriptorMigrationError(
            "transparent terminal definition lacks body_sha256"
        )
    flags = value.get("semantic_construct_flags")
    fragments = value.get("semantic_fragments")
    dependency_chain = value.get("dependency_chain")
    direct_dependencies = value.get("direct_local_dependencies")
    if (
        not isinstance(flags, Mapping)
        or not isinstance(fragments, list)
        or not isinstance(dependency_chain, list)
        or not dependency_chain
        or any(not isinstance(entry, str) or not entry.strip() for entry in dependency_chain)
        or not isinstance(direct_dependencies, list)
        or any(
            not isinstance(entry, str) or not entry.strip()
            for entry in direct_dependencies
        )
    ):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "transparent terminal definition lacks a complete body/closure/construct receipt"
        )
    out: dict[str, object] = {}
    for raw_key, raw_value in value.items():
        key = str(raw_key)
        if key in _TERMINAL_NAVIGATION_FIELDS:
            continue
        out[key] = _normalize_terminal_navigation(raw_value)
    # The full body and closure receipt (`dependency_chain` plus direct local
    # dependencies), opaque/unexpanded state, flags, and fragments remain in
    # `out`; do not replace them with a weaker summary.
    return out


def _normalize_terminal_navigation(value: object) -> object:
    if isinstance(value, Mapping):
        raw_definitions = value.get("transparent_definitions")
        if isinstance(raw_definitions, list):
            projected_defs: list[dict[str, object]] = []
            for definition in raw_definitions:
                if not isinstance(definition, Mapping):
                    raise SourceRecordHistoricalDescriptorMigrationError(
                        "transparent terminal definition is not an object"
                    )
                projected_defs.append(_terminal_definition_projection(definition))
            definition_digests = [_canonical_digest(item) for item in projected_defs]
            if len(set(definition_digests)) != len(definition_digests):
                raise SourceRecordHistoricalDescriptorMigrationError(
                    "transparent terminal navigation has ambiguous body/closure identities"
                )
            out: dict[str, object] = {}
            for raw_key, raw_value in value.items():
                key = str(raw_key)
                if key == "transparent_definitions":
                    out[key] = projected_defs
                else:
                    out[key] = _normalize_terminal_navigation(raw_value)
            return _normalize_explicit_defaults(out)
        return _normalize_explicit_defaults(
            {str(key): _normalize_terminal_navigation(child) for key, child in value.items()}
        )
    if isinstance(value, list):
        return [_normalize_terminal_navigation(item) for item in value]
    if isinstance(value, tuple):
        return [_normalize_terminal_navigation(item) for item in value]
    return value


def _declaration_identity_pin(value: object, *, label: str) -> dict[str, str]:
    if not isinstance(value, Mapping):
        raise SourceRecordHistoricalDescriptorMigrationError(
            f"{label} lacks a declaration identity"
        )
    qualified = str(value.get("qualified_declaration") or "").strip()
    declaration_sha256 = _sha256(value.get("declaration_sha256"))
    if not qualified or not declaration_sha256:
        raise SourceRecordHistoricalDescriptorMigrationError(
            f"{label} has a malformed declaration identity"
        )
    return {
        "qualified_declaration": qualified,
        "declaration_sha256": declaration_sha256,
    }


def _semantic_row_signature_ledger(
    raw_item: Mapping[str, Any],
    association: Mapping[str, Any],
    *,
    current: bool,
    label: str,
) -> dict[str, str]:
    """Validate every current semantic row's exact elaborated route ledger."""

    if not current:
        # Schema 1 did not emit these current Lean-route receipts.  The
        # historical bridge never treats their absence as equivalence: it
        # rechecks the schema-2 ledger below before reusing an input row.
        return {}
    raw_signatures = raw_item.get("reviewed_elaborated_signature_identities")
    if not isinstance(raw_signatures, list) or not raw_signatures:
        raise SourceRecordHistoricalDescriptorMigrationError(
            f"{label} lacks a current elaborated-signature ledger"
        )
    signature_by_qualified: dict[str, str] = {}
    for raw_signature in raw_signatures:
        if not isinstance(raw_signature, Mapping):
            raise SourceRecordHistoricalDescriptorMigrationError(
                f"{label} has a malformed elaborated-signature entry"
            )
        qualified = str(raw_signature.get("qualified_declaration") or "").strip()
        digest = _sha256(raw_signature.get("elaborated_signature_sha256"))
        if not qualified or not digest or qualified in signature_by_qualified:
            raise SourceRecordHistoricalDescriptorMigrationError(
                f"{label} has an ambiguous elaborated-signature ledger"
            )
        signature_by_qualified[qualified] = digest
    raw_identity = _declaration_identity_pin(
        raw_item.get("reviewed_declaration_identity"), label=label
    )
    if raw_identity["qualified_declaration"] not in signature_by_qualified:
        raise SourceRecordHistoricalDescriptorMigrationError(
            f"{label} omits its reviewed declaration from the signature ledger"
        )
    association_identity = _declaration_identity_pin(
        association.get("reviewed_declaration_identity"),
        label=f"{label} source association",
    )
    association_signature = association.get("reviewed_elaborated_signature_identity")
    if not isinstance(association_signature, Mapping):
        raise SourceRecordHistoricalDescriptorMigrationError(
            f"{label} source association lacks a current elaborated signature"
        )
    associated_qualified = str(
        association_signature.get("qualified_declaration") or ""
    ).strip()
    associated_digest = _sha256(
        association_signature.get("elaborated_signature_sha256")
    )
    if (
        associated_qualified != association_identity["qualified_declaration"]
        or not associated_digest
        or signature_by_qualified.get(associated_qualified) != associated_digest
    ):
        raise SourceRecordHistoricalDescriptorMigrationError(
            f"{label} source association signature is not in the semantic-row ledger"
        )
    return signature_by_qualified


def _semantic_endpoint_pair_compatible(
    direct: Mapping[str, Any], transparent: Mapping[str, Any]
) -> bool:
    """Return whether a split direct/spec pair is explicitly and uniquely linked."""

    return bool(
        direct.get("role") == "direct_evidence"
        and transparent.get("role") == "transparent_spec"
        and canonical_digest_payload(direct.get("source_contract"))
        == canonical_digest_payload(transparent.get("source_contract"))
        and canonical_digest_payload(direct.get("source_item_identities"))
        == canonical_digest_payload(transparent.get("source_item_identities"))
        and direct.get("paired_qualified_declaration")
        == transparent.get("raw_identity", {}).get("qualified_declaration")
        == transparent.get("association_identity", {}).get("qualified_declaration")
        and transparent.get("paired_qualified_declaration")
        == direct.get("raw_identity", {}).get("qualified_declaration")
        == direct.get("association_identity", {}).get("qualified_declaration")
        and direct.get("review_scope") == transparent.get("review_scope")
        and direct.get("structural_pairing") == transparent.get("structural_pairing")
    )


def _merged_signature_ledger(
    *records: Mapping[str, Any], current: bool
) -> dict[str, str]:
    merged: dict[str, str] = {}
    if not current:
        return merged
    for record in records:
        signatures = record.get("signature_by_qualified")
        if not isinstance(signatures, Mapping):
            raise SourceRecordHistoricalDescriptorMigrationError(
                "current semantic endpoint has no signature ledger"
            )
        for raw_qualified, raw_digest in signatures.items():
            qualified = str(raw_qualified or "").strip()
            digest = _sha256(raw_digest)
            if not qualified or not digest:
                raise SourceRecordHistoricalDescriptorMigrationError(
                    "current semantic endpoint has a malformed signature ledger"
                )
            existing = merged.get(qualified)
            if existing is not None and existing != digest:
                raise SourceRecordHistoricalDescriptorMigrationError(
                    "paired semantic endpoints disagree on an elaborated signature"
                )
            merged[qualified] = digest
    return merged


def _semantic_endpoint_ledger(
    raw_audit: Mapping[str, Any],
    statement_map: Mapping[str, Any],
    *,
    current: bool,
) -> dict[str, dict[str, Any]]:
    """Return exact direct/spec source-contract endpoint pairs.

    Semantic-model rows are never migrated.  They are only a current, fully
    pinned route ledger for a nonsemantic input.  A normal direct-evidence
    row may carry both endpoints in one semantic row.  If the source audit
    splits the direct and transparent-spec routes (as KR Theorem 3 does), the
    pair must be explicit, mutually paired, source-identical, and complete;
    no endpoint is inferred from one half alone.
    """

    map_items = _source_map_items(statement_map)
    values = raw_audit.get("semantic_model_items")
    if not isinstance(values, list):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "raw audit semantic_model_items is not a list"
        )
    expected_schema = 2 if current else 1
    records_by_source: dict[str, list[dict[str, Any]]] = {}
    for index, raw_item in enumerate(values):
        if not isinstance(raw_item, Mapping):
            raise SourceRecordHistoricalDescriptorMigrationError(
                "raw audit has a malformed semantic-model item"
            )
        association = raw_item.get("semantic_contract_source_association")
        if not isinstance(association, Mapping):
            association = raw_item.get("source_statement_association")
        if not isinstance(association, Mapping):
            continue
        label = f"semantic-model item {index}"
        if association.get("schema") != expected_schema:
            raise SourceRecordHistoricalDescriptorMigrationError(
                f"{label} source association is not schema {expected_schema}"
            )
        raw_identity = _declaration_identity_pin(
            raw_item.get("reviewed_declaration_identity"), label=label
        )
        association_identity = _declaration_identity_pin(
            association.get("reviewed_declaration_identity"),
            label=f"{label} source association",
        )
        signature_by_qualified = _semantic_row_signature_ledger(
            raw_item, association, current=current, label=label
        )
        identities = association.get("source_item_identities")
        if not isinstance(identities, list) or not identities:
            raise SourceRecordHistoricalDescriptorMigrationError(
                f"{label} lacks source-contract identities"
            )
        projected_identities: list[dict[str, Any]] = []
        for raw_identity_record in identities:
            if not isinstance(raw_identity_record, Mapping):
                raise SourceRecordHistoricalDescriptorMigrationError(
                    f"{label} has a malformed source identity"
                )
            source_key = str(raw_identity_record.get("source_key") or "").strip()
            source_item = map_items.get(source_key)
            if not source_key or not isinstance(source_item, Mapping):
                raise SourceRecordHistoricalDescriptorMigrationError(
                    f"{label} names a source item absent from the current map"
                )
            projected_identities.append(
                _identity_projection(
                    raw_identity_record, source_item=source_item, current=current
                )
            )
        if len({identity["source_key"] for identity in projected_identities}) != len(
            projected_identities
        ):
            raise SourceRecordHistoricalDescriptorMigrationError(
                f"{label} has duplicate source-contract identities"
            )
        projected_identities.sort(key=lambda identity: str(identity["source_key"]))
        contracts = {
            _canonical_digest(identity["semantic_contract"])
            for identity in projected_identities
        }
        if len(contracts) != 1:
            raise SourceRecordHistoricalDescriptorMigrationError(
                f"{label} combines distinct source contracts"
            )
        contract = projected_identities[0]["semantic_contract"]
        evidence = str(contract.get("evidence_declaration") or "").strip()
        spec = str(contract.get("spec_declaration") or "").strip()
        role = str(association.get("role") or "").strip()
        paired = str(association.get("paired_qualified_declaration") or "").strip()
        review_scope = str(association.get("review_scope") or "").strip()
        structural_pairing = str(association.get("structural_pairing") or "").strip()
        if not evidence or not spec or not paired or not review_scope or not structural_pairing:
            raise SourceRecordHistoricalDescriptorMigrationError(
                f"{label} lacks a complete source-contract pairing receipt"
            )
        if raw_identity["qualified_declaration"] not in {spec, evidence}:
            raise SourceRecordHistoricalDescriptorMigrationError(
                f"{label} reviewed declaration is not a source-contract endpoint"
            )
        if role == "direct_evidence":
            if (
                association_identity["qualified_declaration"] != evidence
                or paired != spec
            ):
                raise SourceRecordHistoricalDescriptorMigrationError(
                    f"{label} has a malformed direct-evidence endpoint pairing"
                )
        elif role == "transparent_spec":
            if (
                raw_identity["qualified_declaration"] != spec
                or association_identity["qualified_declaration"] != spec
                or paired != evidence
            ):
                raise SourceRecordHistoricalDescriptorMigrationError(
                    f"{label} has a malformed transparent-spec endpoint pairing"
                )
        else:
            raise SourceRecordHistoricalDescriptorMigrationError(
                f"{label} has an unsupported source-contract member role"
            )
        semantic_association_sha256 = ""
        if current:
            association_signature = association.get(
                "reviewed_elaborated_signature_identity"
            )
            semantic_association_sha256 = semantic_association_record_digest(
                [
                    identity["source_semantic_sha256"]
                    for identity in projected_identities
                ],
                association_signature,
            )
            if (
                not semantic_association_sha256
                or _sha256(association.get("semantic_association_sha256"))
                != semantic_association_sha256
            ):
                raise SourceRecordHistoricalDescriptorMigrationError(
                    f"{label} has a stale current semantic-association digest"
                )
        record = {
            "source_contract": copy.deepcopy(dict(contract)),
            "source_item_identities": copy.deepcopy(projected_identities),
            "raw_identity": raw_identity,
            "association_identity": association_identity,
            "signature_by_qualified": signature_by_qualified,
            "role": role,
            "paired_qualified_declaration": paired,
            "review_scope": review_scope,
            "structural_pairing": structural_pairing,
            "semantic_association_sha256": semantic_association_sha256,
        }
        for source_identity in projected_identities:
            records_by_source.setdefault(source_identity["source_key"], []).append(
                copy.deepcopy(record)
            )

    entries: dict[str, dict[str, Any]] = {}
    for source_key, records in records_by_source.items():
        direct_records = [
            record for record in records if record.get("role") == "direct_evidence"
        ]
        transparent_records = [
            record for record in records if record.get("role") == "transparent_spec"
        ]
        candidates: list[dict[str, Any]] = []
        used_transparent_indices: set[int] = set()
        for direct in direct_records:
            contract = direct["source_contract"]
            evidence = str(contract.get("evidence_declaration") or "").strip()
            spec = str(contract.get("spec_declaration") or "").strip()
            raw_identity = direct["raw_identity"]
            evidence_identity = direct["association_identity"]
            if raw_identity["qualified_declaration"] == spec:
                spec_identity = raw_identity
                route_records = (direct,)
            elif raw_identity["qualified_declaration"] == evidence:
                mates = [
                    (mate_index, mate)
                    for mate_index, mate in enumerate(transparent_records)
                    if _semantic_endpoint_pair_compatible(direct, mate)
                ]
                if len(mates) != 1:
                    raise SourceRecordHistoricalDescriptorMigrationError(
                        f"semantic-model source contract `{source_key}` lacks one exact paired transparent-spec endpoint"
                    )
                mate_index, mate = mates[0]
                used_transparent_indices.add(mate_index)
                spec_identity = mate["raw_identity"]
                route_records = (direct, mate)
            else:  # protected above, retained for local fail-closed clarity.
                raise SourceRecordHistoricalDescriptorMigrationError(
                    f"semantic-model source contract `{source_key}` has no direct/spec endpoint"
                )
            signatures = _merged_signature_ledger(*route_records, current=current)
            if current and (
                signatures.get(spec) is None or signatures.get(evidence) is None
            ):
                raise SourceRecordHistoricalDescriptorMigrationError(
                    f"semantic-model source contract `{source_key}` lacks a complete endpoint signature ledger"
                )
            candidates.append(
                {
                    "source_contract": copy.deepcopy(dict(contract)),
                    "source_item_identities": copy.deepcopy(
                        direct["source_item_identities"]
                    ),
                    "spec_identity": copy.deepcopy(spec_identity),
                    "evidence_identity": copy.deepcopy(evidence_identity),
                    "signature_by_qualified": signatures,
                    "semantic_association_sha256_by_role": {
                        record["role"]: record["semantic_association_sha256"]
                        for record in route_records
                        if current
                    },
                    "paired_endpoint_count": len(route_records),
                }
            )
        if len(used_transparent_indices) != len(transparent_records):
            raise SourceRecordHistoricalDescriptorMigrationError(
                f"semantic-model source contract `{source_key}` has an unpaired transparent-spec endpoint"
            )
        if len(candidates) != 1:
            raise SourceRecordHistoricalDescriptorMigrationError(
                f"semantic-model source contract `{source_key}` does not have one exact direct/spec endpoint pair"
            )
        entries[source_key] = candidates[0]
    return entries


def _identity_projection(
    raw_identity: Mapping[str, Any],
    *,
    source_item: Mapping[str, Any],
    current: bool,
) -> dict[str, Any]:
    source_key = str(raw_identity.get("source_key") or "").strip()
    source_location = str(raw_identity.get("source_location") or "").strip()
    source_kind = str(raw_identity.get("source_kind") or "").strip()
    source_map_digest = _sha256(raw_identity.get("source_map_item_sha256"))
    if not source_key or not source_location or not source_kind or not source_map_digest:
        raise SourceRecordHistoricalDescriptorMigrationError(
            "source association identity lacks an exact source key/location/kind/map digest"
        )
    if str(source_item.get("source_location") or "").strip() != source_location:
        raise SourceRecordHistoricalDescriptorMigrationError(
            f"source association `{source_key}` has a changed source location"
        )
    if str(source_item.get("source_kind") or "").strip() != source_kind:
        raise SourceRecordHistoricalDescriptorMigrationError(
            f"source association `{source_key}` has a changed source kind"
        )
    if source_map_item_record_digest(source_item) != source_map_digest:
        raise SourceRecordHistoricalDescriptorMigrationError(
            f"source association `{source_key}` has a changed source-map item digest"
        )
    contract = raw_identity.get("semantic_contract")
    if not isinstance(contract, Mapping) or canonical_digest_payload(contract) != canonical_digest_payload(
        source_item.get("semantic_contract")
    ):
        raise SourceRecordHistoricalDescriptorMigrationError(
            f"source association `{source_key}` has changed source-contract endpoints"
        )
    semantic_digest = source_item_coverage_sha256(dict(source_item), "")
    supplied = _sha256(raw_identity.get("source_semantic_sha256"))
    if current and supplied != semantic_digest:
        raise SourceRecordHistoricalDescriptorMigrationError(
            f"source association `{source_key}` has a stale source semantic identity"
        )
    if not current and supplied:
        # Schema 1 was allowed to omit this field.  If it did emit one, it must
        # already agree with the current source content rather than smuggling a
        # distinct historical source identity through the bridge.
        if supplied != semantic_digest:
            raise SourceRecordHistoricalDescriptorMigrationError(
                f"legacy source association `{source_key}` has a different source semantic identity"
            )
    return {
        "source_key": source_key,
        "source_location": source_location,
        "source_kind": source_kind,
        "source_map_item_sha256": source_map_digest,
        "source_semantic_sha256": semantic_digest,
        "semantic_contract": copy.deepcopy(dict(contract)),
    }


def _association_structure_projection(value: Mapping[str, Any]) -> dict[str, object]:
    out = copy.deepcopy(dict(value))
    for field in (
        "schema",
        "association_sha256",
        "semantic_association_sha256",
        "reviewed_declaration_identity",
        "reviewed_elaborated_signature_identity",
    ):
        out.pop(field, None)
    raw_identities = out.get("source_item_identities")
    if isinstance(raw_identities, list):
        for identity in raw_identities:
            if isinstance(identity, dict):
                identity.pop("source_semantic_sha256", None)
    return out


def _association_binding(
    item: Mapping[str, Any],
    *,
    current: bool,
    endpoint_ledger: Mapping[str, Mapping[str, Any]],
    statement_map: Mapping[str, Any],
) -> dict[str, Any] | None:
    association = item.get("source_contract_association")
    if association is None:
        return None
    if not isinstance(association, Mapping):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "source_contract_association is malformed"
        )
    expected_schema = 2 if current else 1
    if association.get("schema") != expected_schema:
        raise SourceRecordHistoricalDescriptorMigrationError(
            f"source_contract_association is not schema {expected_schema}"
        )
    if _sha256(association.get("association_sha256")) != source_contract_association_record_digest(
        association
    ):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "source_contract_association has a stale association digest"
        )
    raw_identities = association.get("source_item_identities")
    if not isinstance(raw_identities, list) or not raw_identities:
        raise SourceRecordHistoricalDescriptorMigrationError(
            "source_contract_association lacks source identities"
        )
    map_items = _source_map_items(statement_map)
    identities: list[dict[str, Any]] = []
    for raw_identity in raw_identities:
        if not isinstance(raw_identity, Mapping):
            raise SourceRecordHistoricalDescriptorMigrationError(
                "source_contract_association contains a malformed source identity"
            )
        source_key = str(raw_identity.get("source_key") or "").strip()
        source_item = map_items.get(source_key)
        if not isinstance(source_item, Mapping):
            raise SourceRecordHistoricalDescriptorMigrationError(
                f"source association `{source_key}` is absent from the current map"
            )
        identity = _identity_projection(
            raw_identity, source_item=source_item, current=current
        )
        endpoint = endpoint_ledger.get(source_key)
        if endpoint is None:
            raise SourceRecordHistoricalDescriptorMigrationError(
                f"source association `{source_key}` has no semantic endpoint ledger"
            )
        if canonical_digest_payload(identity["semantic_contract"]) != canonical_digest_payload(
            endpoint.get("source_contract")
        ):
            raise SourceRecordHistoricalDescriptorMigrationError(
                f"source association `{source_key}` has a different semantic contract"
            )
        identities.append(identity)
    if len({identity["source_key"] for identity in identities}) != len(identities):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "source_contract_association duplicates a source identity"
        )
    identities.sort(key=lambda identity: str(identity["source_key"]))

    reviewed = association.get("reviewed_declaration_identity")
    if not isinstance(reviewed, Mapping):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "source_contract_association lacks reviewed declaration identity"
        )
    qualified = str(reviewed.get("qualified_declaration") or "").strip()
    declaration_sha = _sha256(reviewed.get("declaration_sha256"))
    if not qualified or not declaration_sha:
        raise SourceRecordHistoricalDescriptorMigrationError(
            "source_contract_association has a malformed declaration pin"
        )
    if len(identities) != 1:
        # The migration intentionally does not invent an endpoint pairing for
        # a multi-source group.  Such a group needs a current review.
        raise SourceRecordHistoricalDescriptorMigrationError(
            "source_contract_association has multiple source endpoints"
        )
    endpoint = endpoint_ledger[identities[0]["source_key"]]
    evidence_identity = endpoint.get("evidence_identity")
    spec_identity = endpoint.get("spec_identity")
    if not isinstance(evidence_identity, Mapping) or not isinstance(spec_identity, Mapping):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "semantic endpoint ledger is malformed"
        )
    endpoint_by_qualified = {
        str(evidence_identity.get("qualified_declaration") or "").strip(): evidence_identity,
        str(spec_identity.get("qualified_declaration") or "").strip(): spec_identity,
    }
    expected_identity = endpoint_by_qualified.get(qualified)
    if not isinstance(expected_identity, Mapping) or _sha256(
        expected_identity.get("declaration_sha256")
    ) != declaration_sha:
        raise SourceRecordHistoricalDescriptorMigrationError(
            "source_contract_association declaration pin is not a current source-contract endpoint"
        )

    role = str(
        association.get("semantic_contract_member_role") or association.get("role") or ""
    ).strip()
    mode = str(association.get("association_mode") or "").strip()
    semantic_key = str(association.get("semantic_model_judgment_key") or "").strip()
    if not role or not mode or not semantic_key:
        raise SourceRecordHistoricalDescriptorMigrationError(
            "source_contract_association lacks role/mode/semantic-group route"
        )

    signature: dict[str, str] | None = None
    if current:
        raw_signature = association.get("reviewed_elaborated_signature_identity")
        if not isinstance(raw_signature, Mapping):
            raise SourceRecordHistoricalDescriptorMigrationError(
                "schema-2 source association lacks elaborated signature pin"
            )
        signature_qualified = str(raw_signature.get("qualified_declaration") or "").strip()
        signature_digest = _sha256(raw_signature.get("elaborated_signature_sha256"))
        expected_signature = endpoint.get("signature_by_qualified", {}).get(qualified)
        if (
            signature_qualified != qualified
            or not signature_digest
            or signature_digest != expected_signature
        ):
            raise SourceRecordHistoricalDescriptorMigrationError(
                "schema-2 source association has a stale declaration/signature pin"
            )
        signature = {
            "qualified_declaration": qualified,
            "elaborated_signature_sha256": signature_digest,
        }
        expected_semantic_association = semantic_association_record_digest(
            [identity["source_semantic_sha256"] for identity in identities], signature
        )
        if not expected_semantic_association or _sha256(
            association.get("semantic_association_sha256")
        ) != expected_semantic_association:
            raise SourceRecordHistoricalDescriptorMigrationError(
                "schema-2 source association has a stale semantic association digest"
            )
    return {
        "association_mode": mode,
        "semantic_contract_member_role": role,
        "semantic_model_judgment_key": semantic_key,
        "route_structure": _association_structure_projection(association),
        "source_item_identities": identities,
        "reviewed_declaration_identity": {
            "qualified_declaration": qualified,
            "declaration_sha256": declaration_sha,
        },
        **({"reviewed_elaborated_signature_identity": signature} if signature else {}),
    }


def _reprojected_association_descriptor(
    prior_item: Mapping[str, Any],
    current_item: Mapping[str, Any],
    *,
    prior_endpoints: Mapping[str, Mapping[str, Any]],
    current_endpoints: Mapping[str, Mapping[str, Any]],
    statement_map: Mapping[str, Any],
) -> dict[str, Any] | None:
    prior = _association_binding(
        prior_item,
        current=False,
        endpoint_ledger=prior_endpoints,
        statement_map=statement_map,
    )
    current = _association_binding(
        current_item,
        current=True,
        endpoint_ledger=current_endpoints,
        statement_map=statement_map,
    )
    if prior is None or current is None:
        if prior is current:
            return None
        raise SourceRecordHistoricalDescriptorMigrationError(
            "source-contract association was added or removed"
        )
    source_key = prior["source_item_identities"][0]["source_key"]
    prior_endpoint = prior_endpoints.get(source_key)
    current_endpoint = current_endpoints.get(source_key)
    if not isinstance(prior_endpoint, Mapping) or not isinstance(current_endpoint, Mapping):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "source-contract endpoint ledger is incomplete"
        )
    # The proof declaration may change while repairing its derivation.  The
    # `Spec` statement is the source-facing contract and must remain byte-pinned.
    if canonical_digest_payload(prior_endpoint.get("spec_identity")) != canonical_digest_payload(
        current_endpoint.get("spec_identity")
    ):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "source-contract Spec declaration changed"
        )
    if canonical_digest_payload(prior["route_structure"]) != canonical_digest_payload(
        current["route_structure"]
    ):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "source-contract route structure changed"
        )
    if (
        prior["association_mode"] != current["association_mode"]
        or prior["semantic_contract_member_role"]
        != current["semantic_contract_member_role"]
        or prior["semantic_model_judgment_key"] != current["semantic_model_judgment_key"]
        or canonical_digest_payload(prior["source_item_identities"])
        != canonical_digest_payload(current["source_item_identities"])
    ):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "source-contract association changed beyond schema-1-to-2 reprojection"
        )
    signature = current.get("reviewed_elaborated_signature_identity")
    if not isinstance(signature, Mapping):  # defensive; enforced above.
        raise SourceRecordHistoricalDescriptorMigrationError(
            "reprojected source association lacks current signature"
        )
    return {
        "schema": 2,
        "association_mode": current["association_mode"],
        "semantic_contract_member_role": current["semantic_contract_member_role"],
        "semantic_model_judgment_key": current["semantic_model_judgment_key"],
        "route_structure": current["route_structure"],
        "source_item_identities": current["source_item_identities"],
        "reviewed_declaration_identity": current["reviewed_declaration_identity"],
        "reviewed_elaborated_signature_identity": signature,
        "semantic_association_sha256": semantic_association_record_digest(
            [identity["source_semantic_sha256"] for identity in current["source_item_identities"]],
            signature,
        ),
        "source_facing_spec_identity": current_endpoint["spec_identity"],
        "prior_proof_declaration_identity": prior["reviewed_declaration_identity"],
    }


_EXACT_ROW_TEXT_FIELDS = (
    "lean_source_declaration",
    "expanded_input_type",
    "result_relation",
    "proposition_alias_expansion",
    "subtype_predicate_proposition_alias_expansion",
)


def _exact_row_text_error(
    prior_item: Mapping[str, Any], current_item: Mapping[str, Any]
) -> str:
    """Return a reason unless full declaration and expanded relations match."""

    for field in _EXACT_ROW_TEXT_FIELDS:
        if canonical_digest_payload(prior_item.get(field)) != canonical_digest_payload(
            current_item.get(field)
        ):
            return f"raw `{field}` changed"
    for field in ("lean_source_declaration",):
        value = current_item.get(field)
        if not isinstance(value, str) or not value.strip():
            return f"current raw `{field}` is missing"
    return ""


def _effective_route_receipt_projection(
    prior_item: Mapping[str, Any],
    current_item: Mapping[str, Any],
    current_route_receipt: Mapping[str, Any],
) -> tuple[str, bool]:
    """Validate the sole schema-1-to-2 effective-route addition.

    The archived producer emitted a full ``lean_source_declaration`` but no
    separate effective-route receipt. The current producer adds redundant
    effective text and declaration fields. They are projectable only when the
    current text is byte-identical to the exact source declaration and its
    declaration equals the already pinned current route. A populated archived
    effective receipt is ordinary source content and must match exactly.
    """

    prior_source = prior_item.get("lean_source_declaration")
    current_source = current_item.get("lean_source_declaration")
    if not isinstance(prior_source, str) or not prior_source.strip():
        return "prior raw `lean_source_declaration` is missing", False
    if not isinstance(current_source, str) or not current_source.strip():
        return "current raw `lean_source_declaration` is missing", False
    if canonical_digest_payload(prior_source) != canonical_digest_payload(current_source):
        return "raw `lean_source_declaration` changed", False

    prior_effective = prior_item.get("effective_lean_source_declaration")
    prior_qualified = prior_item.get("effective_qualified_declaration")
    current_effective = current_item.get("effective_lean_source_declaration")
    current_qualified = current_item.get("effective_qualified_declaration")
    identity = current_route_receipt.get("reviewed_declaration_identity")
    if not isinstance(identity, Mapping):  # Defensive: caller pins this first.
        return "current raw row lacks a pinned declaration identity", False
    pinned_qualified = str(identity.get("qualified_declaration") or "").strip()
    if not pinned_qualified:
        return "current raw row has a malformed pinned declaration identity", False

    if prior_effective is None and prior_qualified is None:
        if not isinstance(current_effective, str) or not current_effective.strip():
            return "current raw `effective_lean_source_declaration` is missing", False
        if current_effective != current_source:
            return (
                "current raw `effective_lean_source_declaration` is not byte-identical "
                "to `lean_source_declaration`",
                False,
            )
        if str(current_qualified or "").strip() != pinned_qualified:
            return (
                "current raw `effective_qualified_declaration` does not equal "
                "the pinned declaration identity",
                False,
            )
        return "", True

    if prior_effective is None or prior_qualified is None:
        return "prior raw effective-route receipt is incomplete", False
    if canonical_digest_payload(prior_effective) != canonical_digest_payload(
        current_effective
    ):
        return "raw `effective_lean_source_declaration` changed", False
    if canonical_digest_payload(prior_qualified) != canonical_digest_payload(
        current_qualified
    ):
        return "raw `effective_qualified_declaration` changed", False
    if str(current_qualified or "").strip() != pinned_qualified:
        return (
            "current raw `effective_qualified_declaration` does not equal "
            "the pinned declaration identity",
            False,
        )
    return "", False


def _current_row_route_receipt(item: Mapping[str, Any]) -> dict[str, Any]:
    """Recompute the exact current declaration, signature, and fidelity pins.

    This applies even before a source association is inspected, so a mapless
    row cannot bypass the Lean-route validation.  It still needs nonempty
    group pins to migrate, which rejects the current source-free recursive
    rows without relying on their field or declaration names.
    """

    identity = _declaration_identity_pin(
        item.get("reviewed_declaration_identity"), label="current raw row"
    )
    effective_qualified = str(item.get("effective_qualified_declaration") or "").strip()
    if effective_qualified != identity["qualified_declaration"]:
        raise SourceRecordHistoricalDescriptorMigrationError(
            "current raw row effective declaration does not match its declaration identity"
        )
    raw_signatures = item.get("reviewed_elaborated_signature_identities")
    if not isinstance(raw_signatures, list) or not raw_signatures:
        raise SourceRecordHistoricalDescriptorMigrationError(
            "current raw row lacks exact elaborated-signature identities"
        )
    signatures: list[dict[str, str]] = []
    seen_qualified: set[str] = set()
    for raw_signature in raw_signatures:
        if not isinstance(raw_signature, Mapping):
            raise SourceRecordHistoricalDescriptorMigrationError(
                "current raw row has a malformed elaborated-signature identity"
            )
        qualified = str(raw_signature.get("qualified_declaration") or "").strip()
        digest = _sha256(raw_signature.get("elaborated_signature_sha256"))
        if not qualified or not digest or qualified in seen_qualified:
            raise SourceRecordHistoricalDescriptorMigrationError(
                "current raw row has an ambiguous elaborated-signature ledger"
            )
        seen_qualified.add(qualified)
        signatures.append(
            {
                "qualified_declaration": qualified,
                "elaborated_signature_sha256": digest,
            }
        )
    if identity["qualified_declaration"] not in seen_qualified:
        raise SourceRecordHistoricalDescriptorMigrationError(
            "current raw row signature ledger omits its reviewed declaration"
        )
    if not source_record_item_reuse_eligible(
        item, expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    ):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "current raw row is not independently item-reuse eligible"
        )
    current_context = _sha256(
        item.get("source_record_item_semantic_context_requirements_sha256")
    )
    if (
        item.get("source_record_item_semantic_context_requirements_sha256") is not None
        and not current_context
    ):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "current raw row has a malformed semantic-context receipt"
        )
    current_fidelity = _sha256(
        item.get("source_record_item_source_proof_fidelity_records_sha256")
    )
    if (
        item.get("source_record_item_source_proof_fidelity_records_sha256") is not None
        and not current_fidelity
    ):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "current raw row has a malformed source-proof-fidelity receipt"
        )
    return {
        "reviewed_declaration_identity": identity,
        "reviewed_elaborated_signature_identities": sorted(
            signatures, key=lambda signature: signature["qualified_declaration"]
        ),
        "source_record_item_reuse_eligibility": copy.deepcopy(
            dict(item["source_record_item_reuse_eligibility"])
        ),
        "source_record_item_semantic_context_requirements_sha256": current_context,
        "source_record_item_source_proof_fidelity_records_sha256": current_fidelity,
    }


def _item_projection(
    item: Mapping[str, Any],
    *,
    association_descriptor: Mapping[str, Any] | None,
    current_route_receipt: Mapping[str, Any],
    omit_legacy_effective_route_receipt: bool,
) -> dict[str, object]:
    """Preserve all non-administrative input content exactly."""

    out: dict[str, object] = {}
    for raw_key, raw_value in item.items():
        key = str(raw_key)
        if (
            key in _TRANSPORT_ONLY_ITEM_FIELDS
            or key in _REPROJECTED_ITEM_FIELDS
            or key in _CURRENT_ONLY_ITEM_FIELDS
            or (
                omit_legacy_effective_route_receipt
                and key
                in {
                    "effective_lean_source_declaration",
                    "effective_qualified_declaration",
                }
            )
        ):
            continue
        if key == "review_alias_expansion":
            if not _is_no_alias_receipt(raw_value):
                out[key] = _normalize_terminal_navigation(raw_value)
            continue
        out[key] = _normalize_terminal_navigation(raw_value)
    if association_descriptor is not None:
        out["source_contract_association_reprojected"] = copy.deepcopy(
            dict(association_descriptor)
        )
    out["current_row_route_receipt"] = copy.deepcopy(dict(current_route_receipt))
    return _normalize_explicit_defaults(out)


def _group_descriptor(
    prior_group: Mapping[str, Any],
    current_group: Mapping[str, Any],
    *,
    prior_endpoints: Mapping[str, Mapping[str, Any]],
    current_endpoints: Mapping[str, Mapping[str, Any]],
    statement_map: Mapping[str, Any],
) -> dict[str, Any]:
    prior_members = prior_group.get("raw_members")
    current_members = current_group.get("raw_members")
    if not isinstance(prior_members, list) or not isinstance(current_members, list):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "generated group lacks complete raw members"
        )
    if len(prior_members) != len(current_members):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "generated group member count changed"
        )
    members: list[dict[str, Any]] = []
    for prior_member, current_member in zip(prior_members, current_members):
        if (
            not isinstance(prior_member, tuple)
            or not isinstance(current_member, tuple)
            or len(prior_member) != 2
            or len(current_member) != 2
        ):
            raise SourceRecordHistoricalDescriptorMigrationError(
                "generated group has malformed raw members"
            )
        prior_section, prior_item = prior_member
        current_section, current_item = current_member
        if prior_section != current_section or not isinstance(prior_item, Mapping) or not isinstance(current_item, Mapping):
            raise SourceRecordHistoricalDescriptorMigrationError(
                "generated group section or member shape changed"
            )
        if prior_section == "semantic_model_items":
            raise SourceRecordHistoricalDescriptorMigrationError(
                "semantic-model rows require a current manual review"
            )
        if prior_section == "recursive_field_items":
            raise SourceRecordHistoricalDescriptorMigrationError(
                "recursive-field rows are never transported by this historical migration"
            )
        current_route_receipt = _current_row_route_receipt(current_item)
        if error := _current_no_alias_receipt_error(
            current_item.get("review_alias_expansion"), current_route_receipt
        ):
            raise SourceRecordHistoricalDescriptorMigrationError(error)
        if error := _exact_row_text_error(prior_item, current_item):
            raise SourceRecordHistoricalDescriptorMigrationError(error)
        (
            effective_route_error,
            omit_legacy_effective_route_receipt,
        ) = _effective_route_receipt_projection(
            prior_item, current_item, current_route_receipt
        )
        if effective_route_error:
            raise SourceRecordHistoricalDescriptorMigrationError(effective_route_error)
        association = _reprojected_association_descriptor(
            prior_item,
            current_item,
            prior_endpoints=prior_endpoints,
            current_endpoints=current_endpoints,
            statement_map=statement_map,
        )
        if association is not None:
            association_identity = association.get("reviewed_declaration_identity")
            if canonical_digest_payload(association_identity) != canonical_digest_payload(
                current_route_receipt["reviewed_declaration_identity"]
            ):
                raise SourceRecordHistoricalDescriptorMigrationError(
                    "current raw row declaration identity does not equal its source-contract endpoint"
                )
            association_signature = association.get(
                "reviewed_elaborated_signature_identity"
            )
            if not isinstance(association_signature, Mapping) or association_signature not in (
                current_route_receipt["reviewed_elaborated_signature_identities"]
            ):
                raise SourceRecordHistoricalDescriptorMigrationError(
                    "current raw row signature ledger does not contain its source-contract endpoint"
                )
        prior_projection = _item_projection(
            prior_item,
            association_descriptor=association,
            current_route_receipt=current_route_receipt,
            omit_legacy_effective_route_receipt=omit_legacy_effective_route_receipt,
        )
        current_projection = _item_projection(
            current_item,
            association_descriptor=association,
            current_route_receipt=current_route_receipt,
            omit_legacy_effective_route_receipt=omit_legacy_effective_route_receipt,
        )
        if canonical_digest_payload(prior_projection) != canonical_digest_payload(
            current_projection
        ):
            raise SourceRecordHistoricalDescriptorMigrationError(
                "generated input/result/binder/source content differs after the explicit projection"
            )
        members.append(
            {
                "section": prior_section,
                "item": prior_projection,
            }
        )
    prior_scope = prior_group.get("raw_formalization_scope")
    current_scope = current_group.get("raw_formalization_scope")
    if canonical_digest_payload(prior_scope) != canonical_digest_payload(current_scope):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "raw formalization scope changed"
        )
    return {
        "schema": SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_SCHEMA,
        "raw_formalization_scope": copy.deepcopy(prior_scope),
        "members": members,
    }


def _group_source_keys(group: Mapping[str, Any]) -> set[str]:
    """Return explicitly attached source keys; never infer one from names."""

    raw_members = group.get("raw_members")
    if not isinstance(raw_members, list):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "generated group lacks raw members while reading source associations"
        )
    keys: set[str] = set()
    for _section, item in raw_members:
        if not isinstance(item, Mapping):
            raise SourceRecordHistoricalDescriptorMigrationError(
                "generated group has a malformed source-associated member"
            )
        association = item.get("source_contract_association")
        if association is None:
            continue
        if not isinstance(association, Mapping):
            raise SourceRecordHistoricalDescriptorMigrationError(
                "generated group has a malformed source-contract association"
            )
        identities = association.get("source_item_identities")
        if not isinstance(identities, list):
            raise SourceRecordHistoricalDescriptorMigrationError(
                "generated group source-contract association lacks source identities"
            )
        for identity in identities:
            if not isinstance(identity, Mapping):
                raise SourceRecordHistoricalDescriptorMigrationError(
                    "generated group source-contract identity is malformed"
                )
            source_key = str(identity.get("source_key") or "").strip()
            if not source_key:
                raise SourceRecordHistoricalDescriptorMigrationError(
                    "generated group source-contract identity lacks a source key"
                )
            keys.add(source_key)
    return keys


def _group_has_section(group: Mapping[str, Any], section_name: str) -> bool:
    raw_members = group.get("raw_members")
    return bool(
        isinstance(raw_members, list)
        and any(
            isinstance(member, tuple)
            and len(member) == 2
            and member[0] == section_name
            for member in raw_members
        )
    )


def _source_association_set_drift_error(
    prior_group: Mapping[str, Any], current_group: Mapping[str, Any]
) -> str:
    """Return a source-route drift reason without inferring names or parents."""

    prior_keys = _group_source_keys(prior_group)
    current_keys = _group_source_keys(current_group)
    if prior_keys == current_keys:
        return ""
    removed = sorted(prior_keys - current_keys)
    added = sorted(current_keys - prior_keys)
    pieces: list[str] = []
    if removed:
        pieces.append("removed=" + ", ".join(removed))
    if added:
        pieces.append("added=" + ", ".join(added))
    return "source-contract association source identities changed (" + "; ".join(pieces) + ")"


def source_record_historical_descriptor_migration_group_descriptor(
    prior_group: Mapping[str, Any],
    current_group: Mapping[str, Any],
    *,
    prior_raw_audit: Mapping[str, Any],
    current_raw_audit: Mapping[str, Any],
    statement_map: Mapping[str, Any],
) -> dict[str, Any]:
    """Public, fail-closed descriptor for one archived/current nonsemantic group."""

    return _group_descriptor(
        prior_group,
        current_group,
        prior_endpoints=_semantic_endpoint_ledger(
            prior_raw_audit, statement_map, current=False
        ),
        current_endpoints=_semantic_endpoint_ledger(
            current_raw_audit, statement_map, current=True
        ),
        statement_map=statement_map,
    )


def _prior_judgment_error(
    key: str,
    value: object,
    sidecar: Mapping[str, Any],
    *,
    prior_raw_digest: str,
) -> str:
    if not isinstance(value, Mapping):
        return "prior sidecar has no object-valued judgment"
    active_transport = sorted(
        field for field in _ACTIVE_PRIOR_TRANSPORT_FIELDS if field in value
    )
    if active_transport:
        return (
            "prior judgment carries active historical transport metadata: "
            + ", ".join(active_transport)
        )
    if str(value.get("prompt_version") or sidecar.get("prompt_version") or "").strip() != (
        SOURCE_RECORD_V10_PROMPT_VERSION
    ):
        return "prior judgment does not use v10"
    if _sha256(
        value.get("source_record_audit_sha256")
        or sidecar.get("source_record_audit_sha256")
    ) != prior_raw_digest:
        return "prior judgment is not bound to the archived prior raw audit"
    validator = value.get("validator") or sidecar.get("validator") or sidecar.get("model")
    timestamp = (
        value.get("validated_at")
        or value.get("timestamp")
        or sidecar.get("validated_at")
        or sidecar.get("timestamp")
    )
    if not str(validator or "").strip() or not str(timestamp or "").strip():
        return "prior judgment lacks validator/timestamp metadata"
    return ""


def _prior_attestation_error(
    sidecar: Mapping[str, Any],
    attestation: Mapping[str, Any],
    *,
    paper: str,
    prior_raw_audit: Mapping[str, Any],
    prior_raw_digest: str,
    sidecar_path: Path,
    attestation_path: Path,
    paper_dir: Path,
) -> str:
    try:
        groups = _snapshot_groups(prior_raw_audit, label="prior")
    except SourceRecordHistoricalDescriptorMigrationError as exc:
        return str(exc)
    raw_items = sidecar.get("items")
    if not isinstance(raw_items, Mapping) or set(str(key) for key in raw_items) != set(
        groups
    ):
        return "prior sidecar does not cover exactly the archived generated judgment ledger"
    expected_keys_sha256 = generated_judgment_keys_sha256(prior_raw_audit)
    expected_surface_sha256 = generated_judgment_surface_sha256(prior_raw_audit)
    expected_sidecar_path = _relative_paper_path(sidecar_path, paper_dir)
    expected_sidecar_sha256 = _file_sha256(sidecar_path)
    metadata = sidecar.get("current_semantic_revalidation")
    if not isinstance(metadata, Mapping):
        return "prior sidecar lacks the archived current-semantic-revalidation receipt"
    if (
        metadata.get("schema") != 1
        or str(metadata.get("policy_version") or "").strip()
        != _LEGACY_CURRENT_REVALIDATION_POLICY_VERSION
        or _sha256(metadata.get("current_source_record_audit_sha256"))
        != prior_raw_digest
        or _sha256(metadata.get("generated_judgment_keys_sha256"))
        != expected_keys_sha256
        or _sha256(metadata.get("generated_judgment_surface_sha256"))
        != expected_surface_sha256
        or str(metadata.get("review_scope") or "").strip()
        != "all_current_generated_judgment_keys"
    ):
        return "prior sidecar has an invalid current-semantic-revalidation receipt"
    if (
        str(metadata.get("current_judgment_sidecar_path") or "").strip()
        != expected_sidecar_path
    ):
        return "prior sidecar current-semantic-revalidation receipt names a different sidecar"
    if (
        attestation.get("schema") != 1
        or attestation.get("artifact_kind")
        != "source_record_current_semantic_revalidation_attestation"
        or str(attestation.get("policy_version") or "").strip()
        != _SIDECAR_BOUND_CURRENT_REVALIDATION_POLICY_VERSION
        or attestation.get("paper") != paper
        or attestation.get("reviewed_current_semantics") is not True
        or _sha256(attestation.get("current_source_record_audit_sha256"))
        != prior_raw_digest
        or _sha256(attestation.get("generated_judgment_keys_sha256"))
        != expected_keys_sha256
        or _sha256(attestation.get("generated_judgment_surface_sha256"))
        != expected_surface_sha256
        or str(attestation.get("review_scope") or "").strip()
        != "all_current_generated_judgment_keys"
        or str(attestation.get("scope") or "").strip()
        != "all_current_semantic_model_judgment_groups"
        or attestation.get("semantic_model_group_count")
        != sum(
            1
            for group in groups.values()
            if isinstance(group.get("raw_members"), list)
            and any(section == "semantic_model_items" for section, _ in group["raw_members"])
        )
        or str(attestation.get("current_judgment_sidecar_path") or "").strip()
        != expected_sidecar_path
        or _sha256(attestation.get("current_judgment_sidecar_sha256"))
        != expected_sidecar_sha256
        or str(attestation.get("reviewer") or "").strip() == ""
        or str(attestation.get("validated_at") or "").strip() == ""
        or str(attestation.get("review_notes") or "").strip() == ""
        or attestation.get("non_evidence_scaffold") is True
        or attestation.get("must_not_be_written_to_repository_sidecar") is True
    ):
        return "prior current semantic attestation is invalid"
    legacy_path_text = str(
        attestation.get("legacy_current_semantic_attestation_path") or ""
    ).strip()
    try:
        legacy_path = _resolve_paper_path(
            legacy_path_text,
            paper_dir,
            label="sidecar-bound attestation legacy attestation path",
        )
        legacy_attestation = _read_json_object(
            legacy_path, label="legacy current semantic attestation"
        )
    except SourceRecordHistoricalDescriptorMigrationError as exc:
        return str(exc)
    if (
        _sha256(attestation.get("legacy_current_semantic_attestation_sha256"))
        != _file_sha256(legacy_path)
        or str(metadata.get("attestation_path") or "").strip() != legacy_path_text
        or _sha256(metadata.get("attestation_sha256")) != _file_sha256(legacy_path)
        or legacy_attestation.get("schema") != 1
        or legacy_attestation.get("artifact_kind")
        != "source_record_current_semantic_revalidation_attestation"
        or str(legacy_attestation.get("policy_version") or "").strip()
        != _LEGACY_CURRENT_REVALIDATION_POLICY_VERSION
        or legacy_attestation.get("paper") != paper
        or legacy_attestation.get("reviewed_current_semantics") is not True
        or _sha256(legacy_attestation.get("current_source_record_audit_sha256"))
        != prior_raw_digest
        or _sha256(legacy_attestation.get("generated_judgment_keys_sha256"))
        != expected_keys_sha256
        or _sha256(legacy_attestation.get("generated_judgment_surface_sha256"))
        != expected_surface_sha256
        or str(legacy_attestation.get("review_scope") or "").strip()
        != "all_current_generated_judgment_keys"
        or str(legacy_attestation.get("reviewer") or "").strip() == ""
        or str(legacy_attestation.get("validated_at") or "").strip() == ""
        or str(legacy_attestation.get("review_notes") or "").strip() == ""
        or legacy_attestation.get("non_evidence_scaffold") is True
        or legacy_attestation.get("must_not_be_written_to_repository_sidecar") is True
    ):
        return "sidecar-bound attestation has an invalid legacy semantic-review ancestry"
    return ""


def _snapshot_groups(
    raw: Mapping[str, Any], *, label: str
) -> dict[str, dict[str, Any]]:
    groups, errors = _raw_item_groups(raw)
    if errors:
        raise SourceRecordHistoricalDescriptorMigrationError(
            f"{label} raw audit has malformed semantic groups: "
            + ", ".join(sorted(errors)[:5])
        )
    return groups


def _current_group_pins(group: Mapping[str, Any]) -> list[dict[str, Any]]:
    raw_members = group.get("raw_members")
    if not isinstance(raw_members, list):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "current group lacks raw members for current item pins"
        )
    try:
        pins = _current_item_pins(raw_members)
    except Exception as exc:  # pragma: no cover - shared helper already tests details.
        raise SourceRecordHistoricalDescriptorMigrationError(
            f"current group has malformed item pins: {exc}"
        ) from exc
    if not pins:
        raise SourceRecordHistoricalDescriptorMigrationError(
            "current group has no complete independently reusable item pin"
        )
    return pins


def _artifact_without_integrity(payload: Mapping[str, Any]) -> dict[str, Any]:
    return {
        str(key): value
        for key, value in payload.items()
        if str(key) != SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_INTEGRITY_FIELD
    }


def source_record_historical_descriptor_migration_sha256(payload: Mapping[str, Any]) -> str:
    return _canonical_digest(_artifact_without_integrity(payload))


def stamp_source_record_historical_descriptor_migration(payload: dict[str, Any]) -> None:
    payload[SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_INTEGRITY_FIELD] = (
        source_record_historical_descriptor_migration_sha256(payload)
    )


def build_source_record_historical_descriptor_migration(
    *,
    paper: str,
    paper_dir: Path,
    prior_raw_audit: Mapping[str, Any],
    current_raw_audit: Mapping[str, Any],
    prior_judgments: Mapping[str, Any],
    prior_attestation: Mapping[str, Any],
    prior_raw_audit_path: Path,
    current_raw_audit_path: Path,
    prior_judgments_path: Path,
    prior_attestation_path: Path,
    statement_map: Mapping[str, Any],
) -> dict[str, Any]:
    """Build the one-time overlay and record every accepted/excluded group."""

    for label, raw in (("prior", prior_raw_audit), ("current", current_raw_audit)):
        if error := _valid_raw_audit(raw, paper=paper, label=label):
            raise SourceRecordHistoricalDescriptorMigrationError(error)
    prior_map_sha = _sha256(prior_raw_audit.get("paper_statement_map_sha256"))
    current_map_sha = _sha256(current_raw_audit.get("paper_statement_map_sha256"))
    if prior_map_sha != current_map_sha:
        raise SourceRecordHistoricalDescriptorMigrationError(
            "prior/current raw audits bind different paper statement maps"
        )
    if error := _source_map_error(
        statement_map,
        statement_map_path=paper_dir / "audit" / "paper_statement_map.json",
        expected_sha256=current_map_sha,
        label="current",
    ):
        raise SourceRecordHistoricalDescriptorMigrationError(error)
    if (
        prior_judgments.get("schema") != 1
        or prior_judgments.get("paper") != paper
        or _sha256(prior_judgments.get("source_record_audit_sha256"))
        != _sha256(prior_raw_audit.get("source_record_audit_sha256"))
    ):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "prior judgment sidecar is not bound to the archived prior raw audit"
        )
    if error := _prior_attestation_error(
        prior_judgments,
        prior_attestation,
        paper=paper,
        prior_raw_audit=prior_raw_audit,
        prior_raw_digest=_sha256(prior_raw_audit.get("source_record_audit_sha256")),
        sidecar_path=prior_judgments_path,
        attestation_path=prior_attestation_path,
        paper_dir=paper_dir,
    ):
        raise SourceRecordHistoricalDescriptorMigrationError(error)
    raw_judgments = prior_judgments.get("items")
    if not isinstance(raw_judgments, Mapping):
        raise SourceRecordHistoricalDescriptorMigrationError(
            "prior judgment sidecar has no items object"
        )

    prior_groups = _snapshot_groups(prior_raw_audit, label="prior")
    current_groups = _snapshot_groups(current_raw_audit, label="current")
    prior_endpoints = _semantic_endpoint_ledger(
        prior_raw_audit, statement_map, current=False
    )
    current_endpoints = _semantic_endpoint_ledger(
        current_raw_audit, statement_map, current=True
    )
    # A changed or vanished source route is not an error in the current raw
    # audit.  It is simply fresh review work.  In particular, Equation F.1
    # deliberately lost a former formula association; that cannot invalidate
    # unrelated historical review credit, nor can it be silently carried.
    changed_source_endpoint_keys: set[str] = set()
    changed_evidence_source_keys: set[str] = set()
    for source_key in sorted(set(prior_endpoints) | set(current_endpoints)):
        prior_endpoint = prior_endpoints.get(source_key)
        current_endpoint = current_endpoints.get(source_key)
        if not isinstance(prior_endpoint, Mapping) or not isinstance(
            current_endpoint, Mapping
        ):
            changed_source_endpoint_keys.add(source_key)
            continue
        if (
            canonical_digest_payload(prior_endpoint.get("source_contract"))
            != canonical_digest_payload(current_endpoint.get("source_contract"))
            or canonical_digest_payload(prior_endpoint.get("spec_identity"))
            != canonical_digest_payload(current_endpoint.get("spec_identity"))
        ):
            changed_source_endpoint_keys.add(source_key)
            continue
        if canonical_digest_payload(prior_endpoint.get("evidence_identity")) != canonical_digest_payload(
            current_endpoint.get("evidence_identity")
        ):
            changed_evidence_source_keys.add(source_key)

    changed_source_endpoint_keys.update(changed_evidence_source_keys)

    current_descriptors: dict[str, dict[str, Any]] = {}
    current_group_pins: dict[str, list[dict[str, Any]]] = {}
    current_descriptor_errors: dict[str, str] = {}
    for key, group in current_groups.items():
        if _group_has_section(group, "semantic_model_items") or _group_has_section(
            group, "recursive_field_items"
        ):
            continue
        prior_group = prior_groups.get(key)
        if prior_group is None:
            continue
        try:
            if error := _source_association_set_drift_error(prior_group, group):
                raise SourceRecordHistoricalDescriptorMigrationError(error)
            source_keys = _group_source_keys(group)
            if source_keys & changed_source_endpoint_keys:
                raise SourceRecordHistoricalDescriptorMigrationError(
                    "source-contract endpoint changed for source endpoint(s): "
                    + ", ".join(sorted(source_keys & changed_source_endpoint_keys))
                )
            current_group_pins[key] = _current_group_pins(group)
            current_descriptors[key] = _group_descriptor(
                prior_group,
                group,
                prior_endpoints=prior_endpoints,
                current_endpoints=current_endpoints,
                statement_map=statement_map,
            )
        except SourceRecordHistoricalDescriptorMigrationError as exc:
            current_descriptor_errors[key] = str(exc)

    def matching_current_descriptor_keys(
        prior_group: Mapping[str, Any], descriptor: Mapping[str, Any]
    ) -> list[str]:
        """Find every current key matching one prior descriptor, fail closed.

        This is intentionally cross-key rather than an index over only keys
        present in both receipts.  A newly generated current group with an
        otherwise identical descriptor makes the archived key ambiguous and
        therefore ineligible for transport.
        """

        expected = _canonical_digest(descriptor)
        matches: list[str] = []
        for candidate_key, candidate_group in current_groups.items():
            if _group_has_section(candidate_group, "semantic_model_items") or _group_has_section(
                candidate_group, "recursive_field_items"
            ):
                continue
            try:
                if _source_association_set_drift_error(prior_group, candidate_group):
                    continue
                candidate_sources = _group_source_keys(candidate_group)
                if candidate_sources & changed_source_endpoint_keys:
                    continue
                _current_group_pins(candidate_group)
                candidate_descriptor = _group_descriptor(
                    prior_group,
                    candidate_group,
                    prior_endpoints=prior_endpoints,
                    current_endpoints=current_endpoints,
                    statement_map=statement_map,
                )
            except SourceRecordHistoricalDescriptorMigrationError:
                continue
            if _canonical_digest(candidate_descriptor) == expected:
                matches.append(candidate_key)
        return sorted(matches)

    prior_raw_digest = _sha256(prior_raw_audit.get("source_record_audit_sha256"))
    current_raw_provenance = _raw_provenance(
        current_raw_audit, current_raw_audit_path, paper_dir
    )
    prior_raw_provenance = _raw_provenance(prior_raw_audit, prior_raw_audit_path, paper_dir)
    items: dict[str, dict[str, Any]] = {}
    decisions: list[dict[str, str]] = []
    for key in sorted(set(prior_groups) | set(current_groups) | {str(k) for k in raw_judgments}):
        prior_group = prior_groups.get(key)
        current_group = current_groups.get(key)
        if prior_group is None:
            decisions.append(
                {
                    "judgment_key": key,
                    "status": "not_migrated",
                    "reason": "no archived prior generated group for this exact key",
                }
            )
            continue
        if current_group is None:
            decisions.append(
                {
                    "judgment_key": key,
                    "status": "not_migrated",
                    "reason": "no current generated group for this archived key",
                }
            )
            continue
        if _group_has_section(current_group, "semantic_model_items"):
            decisions.append(
                {
                    "judgment_key": key,
                    "status": "manual_current_review_required",
                    "reason": "semantic-model rows are never normalized by this historical migration",
                }
            )
            continue
        if _group_has_section(current_group, "recursive_field_items"):
            decisions.append(
                {
                    "judgment_key": key,
                    "status": "manual_current_review_required",
                    "reason": "recursive-field rows are never transported by this historical migration",
                }
            )
            continue
        try:
            if error := _source_association_set_drift_error(prior_group, current_group):
                decisions.append(
                    {
                        "judgment_key": key,
                        "status": "manual_current_review_required",
                        "reason": error,
                    }
                )
                continue
            changed_sources = sorted(
                _group_source_keys(current_group) & changed_source_endpoint_keys
            )
        except SourceRecordHistoricalDescriptorMigrationError as exc:
            decisions.append(
                {"judgment_key": key, "status": "not_migrated", "reason": str(exc)}
            )
            continue
        if changed_sources:
            decisions.append(
                {
                    "judgment_key": key,
                    "status": "manual_current_review_required",
                    "reason": "source-contract endpoint or direct evidence body changed for source endpoint(s): "
                    + ", ".join(changed_sources),
                }
            )
            continue
        raw_judgment = raw_judgments.get(key)
        if error := _prior_judgment_error(
            key, raw_judgment, prior_judgments, prior_raw_digest=prior_raw_digest
        ):
            decisions.append(
                {"judgment_key": key, "status": "not_migrated", "reason": error}
            )
            continue
        descriptor = current_descriptors.get(key)
        if descriptor is None:
            decisions.append(
                {
                    "judgment_key": key,
                    "status": "not_migrated",
                    "reason": current_descriptor_errors.get(
                        key, "no admissible current normalized descriptor"
                    ),
                }
            )
            continue
        digest = _canonical_digest(descriptor)
        candidates = matching_current_descriptor_keys(prior_group, descriptor)
        if candidates != [key]:
            decisions.append(
                {
                    "judgment_key": key,
                    "status": "not_migrated",
                    "reason": "normalized descriptor does not identify one exact current key",
                }
            )
            continue
        current_pins = current_group_pins.get(key)
        if not current_pins:
            decisions.append(
                {
                    "judgment_key": key,
                    "status": "manual_current_review_required",
                    "reason": current_descriptor_errors.get(
                        key,
                        "current group has no complete independently reusable item pin",
                    ),
                }
            )
            continue
        migrated = copy.deepcopy(dict(raw_judgment))
        for field in list(migrated):
            if field.startswith("source_record_item_"):
                migrated.pop(field)
            elif field in _ACTIVE_PRIOR_TRANSPORT_FIELDS:
                migrated.pop(field)
        migrated["prompt_version"] = SOURCE_RECORD_V10_PROMPT_VERSION
        migrated["source_record_policy_version"] = SOURCE_RECORD_V10_PROMPT_VERSION
        migrated["source_record_audit_sha256"] = current_raw_provenance[
            "source_record_audit_sha256"
        ]
        migrated["source_record_item_digest_schema"] = SOURCE_RECORD_ITEM_DIGEST_SCHEMA
        migrated["source_record_item_sha256s"] = copy.deepcopy(current_pins)
        migrated["source_record_item_sha256"] = (
            current_pins[0]["source_record_item_sha256"] if current_pins else ""
        )
        migrated[SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_ITEM_FIELD] = {
            "schema": SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_SCHEMA,
            "policy_version": SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_POLICY_VERSION,
            "prior_judgment_key": key,
            "current_judgment_key": key,
            "prior_response_sha256": _canonical_digest(raw_judgment),
            "prior_normalized_descriptor": descriptor,
            "prior_normalized_descriptor_sha256": digest,
            "current_normalized_descriptor": descriptor,
            "current_normalized_descriptor_sha256": digest,
            "prior_raw_audit": prior_raw_provenance,
            "current_raw_audit_snapshot": current_raw_provenance,
        }
        items[key] = migrated
        decisions.append(
            {
                "judgment_key": key,
                "status": "migrated",
                "reason": "one exact current normalized descriptor after the explicit historical projection",
            }
        )

    payload: dict[str, Any] = {
        "schema": SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_SCHEMA,
        "artifact_kind": SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_ARTIFACT_KIND,
        "policy_version": SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_POLICY_VERSION,
        "paper": paper,
        "prompt_version": SOURCE_RECORD_V10_PROMPT_VERSION,
        "source_record_policy_version": SOURCE_RECORD_V10_PROMPT_VERSION,
        "prior_raw_audit": prior_raw_provenance,
        "current_raw_audit_snapshot": current_raw_provenance,
        "prior_judgments": _sidecar_provenance(prior_judgments_path, paper_dir),
        "prior_current_semantic_attestation": _sidecar_provenance(
            prior_attestation_path, paper_dir
        ),
        "paper_statement_map": {
            "path": "audit/paper_statement_map.json",
            "file_sha256": _file_sha256(paper_dir / "audit" / "paper_statement_map.json"),
            "paper_statement_map_sha256": current_map_sha,
        },
        "items": items,
        "decisions": decisions,
    }
    stamp_source_record_historical_descriptor_migration(payload)
    return payload


def _snapshot_provenance_error(
    value: object,
    *,
    paper_dir: Path,
    label: str,
) -> tuple[dict[str, Any] | None, str]:
    if not isinstance(value, Mapping):
        return None, f"{label} provenance is malformed"
    try:
        path = _resolve_paper_path(value.get("path"), paper_dir, label=f"{label} path")
        raw = _read_json_object(path, label=label)
    except SourceRecordHistoricalDescriptorMigrationError as exc:
        return None, str(exc)
    if _sha256(value.get("file_sha256")) != _file_sha256(path):
        return None, f"{label} bytes no longer match the archived file hash"
    for field in (
        "source_record_audit_sha256",
        "source_record_audit_integrity_sha256",
        "paper_statement_map_sha256",
    ):
        if _sha256(value.get(field)) != _sha256(raw.get(field)):
            return None, f"{label} has a different `{field}`"
    return raw, ""


def _simple_file_provenance_error(
    value: object, *, paper_dir: Path, label: str
) -> tuple[Path | None, str]:
    if not isinstance(value, Mapping):
        return None, f"{label} provenance is malformed"
    try:
        path = _resolve_paper_path(value.get("path"), paper_dir, label=f"{label} path")
    except SourceRecordHistoricalDescriptorMigrationError as exc:
        return None, str(exc)
    if _sha256(value.get("file_sha256")) != _file_sha256(path):
        return None, f"{label} bytes no longer match the archived file hash"
    return path, ""


def source_record_historical_descriptor_migration_overlay_error(
    payload: object, *, paper: str, paper_dir: Path
) -> str:
    """Validate the immutable snapshot relation before any current reuse."""

    if not isinstance(payload, Mapping):
        return "historical descriptor migration overlay is not an object"
    expected_fields = {
        "schema",
        "artifact_kind",
        "policy_version",
        "paper",
        "prompt_version",
        "source_record_policy_version",
        "prior_raw_audit",
        "current_raw_audit_snapshot",
        "prior_judgments",
        "prior_current_semantic_attestation",
        "paper_statement_map",
        "items",
        "decisions",
        SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_INTEGRITY_FIELD,
    }
    unknown = sorted(str(key) for key in payload if str(key) not in expected_fields)
    if unknown:
        return "historical descriptor migration overlay has unsupported fields: " + ", ".join(
            unknown[:5]
        )
    if (
        payload.get("schema") != SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_SCHEMA
        or payload.get("artifact_kind")
        != SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_ARTIFACT_KIND
        or payload.get("policy_version")
        != SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_POLICY_VERSION
        or payload.get("paper") != paper
        or str(payload.get("prompt_version") or "").strip()
        != SOURCE_RECORD_V10_PROMPT_VERSION
        or str(payload.get("source_record_policy_version") or "").strip()
        != SOURCE_RECORD_V10_PROMPT_VERSION
    ):
        return "historical descriptor migration overlay has an invalid identity or policy"
    if _sha256(payload.get(SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_INTEGRITY_FIELD)) != (
        source_record_historical_descriptor_migration_sha256(payload)
    ):
        return "historical descriptor migration overlay integrity digest does not match"
    prior_raw, error = _snapshot_provenance_error(
        payload.get("prior_raw_audit"), paper_dir=paper_dir, label="prior raw audit"
    )
    if error or prior_raw is None:
        return error
    current_snapshot, error = _snapshot_provenance_error(
        payload.get("current_raw_audit_snapshot"),
        paper_dir=paper_dir,
        label="current raw audit snapshot",
    )
    if error or current_snapshot is None:
        return error
    prior_path, error = _simple_file_provenance_error(
        payload.get("prior_judgments"), paper_dir=paper_dir, label="prior judgments"
    )
    if error or prior_path is None:
        return error
    attestation_path, error = _simple_file_provenance_error(
        payload.get("prior_current_semantic_attestation"),
        paper_dir=paper_dir,
        label="prior current semantic attestation",
    )
    if error or attestation_path is None:
        return error
    statement_map_meta = payload.get("paper_statement_map")
    if not isinstance(statement_map_meta, Mapping):
        return "historical descriptor migration overlay has malformed paper statement map provenance"
    try:
        map_path = _resolve_paper_path(
            statement_map_meta.get("path"), paper_dir, label="paper statement map path"
        )
        statement_map = _read_json_object(map_path, label="paper statement map")
    except SourceRecordHistoricalDescriptorMigrationError as exc:
        return str(exc)
    if _sha256(statement_map_meta.get("file_sha256")) != _file_sha256(map_path):
        return "historical descriptor migration overlay paper statement map bytes changed"
    if _sha256(statement_map_meta.get("paper_statement_map_sha256")) != _file_sha256(map_path):
        return "historical descriptor migration overlay paper statement map digest is stale"
    try:
        prior_judgments = _read_json_object(prior_path, label="prior judgments")
        prior_attestation = _read_json_object(
            attestation_path, label="prior current semantic attestation"
        )
        rebuilt = build_source_record_historical_descriptor_migration(
            paper=paper,
            paper_dir=paper_dir,
            prior_raw_audit=prior_raw,
            current_raw_audit=current_snapshot,
            prior_judgments=prior_judgments,
            prior_attestation=prior_attestation,
            prior_raw_audit_path=_resolve_paper_path(
                payload["prior_raw_audit"].get("path"), paper_dir, label="prior raw audit path"
            ),
            current_raw_audit_path=_resolve_paper_path(
                payload["current_raw_audit_snapshot"].get("path"),
                paper_dir,
                label="current raw audit snapshot path",
            ),
            prior_judgments_path=prior_path,
            prior_attestation_path=attestation_path,
            statement_map=statement_map,
        )
    except SourceRecordHistoricalDescriptorMigrationError as exc:
        return f"historical descriptor migration replay failed: {exc}"
    if canonical_digest_payload(rebuilt) != canonical_digest_payload(payload):
        return "historical descriptor migration overlay does not replay from its archived snapshots"
    return ""


def _current_item_from_group(
    historical_value: Mapping[str, Any],
    current_group: Mapping[str, Any],
    *,
    current_raw_digest: str,
) -> dict[str, Any]:
    copied = copy.deepcopy(dict(historical_value))
    copied["source_record_audit_sha256"] = current_raw_digest
    pins = _current_group_pins(current_group)
    copied["source_record_item_digest_schema"] = SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    copied["source_record_item_sha256s"] = copy.deepcopy(pins)
    copied["source_record_item_sha256"] = (
        pins[0]["source_record_item_sha256"] if pins else ""
    )
    return copied


def _migration_item_current(
    key: str,
    value: Mapping[str, Any],
    *,
    current_raw_audit: Mapping[str, Any],
    snapshot_prior_raw: Mapping[str, Any],
    snapshot_current_raw: Mapping[str, Any],
    statement_map: Mapping[str, Any],
    snapshot_prior_groups: Mapping[str, Mapping[str, Any]] | None = None,
    snapshot_current_groups: Mapping[str, Mapping[str, Any]] | None = None,
    live_current_groups: Mapping[str, Mapping[str, Any]] | None = None,
    prior_endpoint_ledger: Mapping[str, Mapping[str, Any]] | None = None,
    snapshot_current_endpoint_ledger: Mapping[str, Mapping[str, Any]] | None = None,
    live_current_endpoint_ledger: Mapping[str, Mapping[str, Any]] | None = None,
) -> bool:
    metadata = value.get(SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_ITEM_FIELD)
    if not isinstance(metadata, Mapping):
        return False
    if (
        metadata.get("schema") != SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_SCHEMA
        or metadata.get("policy_version")
        != SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_POLICY_VERSION
        or str(metadata.get("prior_judgment_key") or "").strip() != key
        or str(metadata.get("current_judgment_key") or "").strip() != key
    ):
        return False
    try:
        prior_groups = snapshot_prior_groups or _snapshot_groups(
            snapshot_prior_raw, label="prior"
        )
        snapshot_groups = snapshot_current_groups or _snapshot_groups(
            snapshot_current_raw, label="current"
        )
        live_groups = live_current_groups or _snapshot_groups(
            current_raw_audit, label="current"
        )
        prior_endpoints = prior_endpoint_ledger or _semantic_endpoint_ledger(
            snapshot_prior_raw, statement_map, current=False
        )
        snapshot_endpoints = (
            snapshot_current_endpoint_ledger
            or _semantic_endpoint_ledger(
                snapshot_current_raw, statement_map, current=True
            )
        )
        live_endpoints = live_current_endpoint_ledger or _semantic_endpoint_ledger(
            current_raw_audit, statement_map, current=True
        )
    except SourceRecordHistoricalDescriptorMigrationError:
        return False
    prior_group = prior_groups.get(key)
    snapshot_group = snapshot_groups.get(key)
    live_group = live_groups.get(key)
    if prior_group is None or snapshot_group is None or live_group is None:
        return False
    try:
        snapshot_descriptor = _group_descriptor(
            prior_group,
            snapshot_group,
            prior_endpoints=prior_endpoints,
            current_endpoints=snapshot_endpoints,
            statement_map=statement_map,
        )
        live_descriptor = _group_descriptor(
            prior_group,
            live_group,
            prior_endpoints=prior_endpoints,
            current_endpoints=live_endpoints,
            statement_map=statement_map,
        )
    except SourceRecordHistoricalDescriptorMigrationError:
        return False
    stored = metadata.get("current_normalized_descriptor")
    stored_digest = _sha256(metadata.get("current_normalized_descriptor_sha256"))
    if (
        not isinstance(stored, Mapping)
        or not stored_digest
        or _canonical_digest(stored) != stored_digest
        or canonical_digest_payload(stored) != canonical_digest_payload(snapshot_descriptor)
        or canonical_digest_payload(stored) != canonical_digest_payload(live_descriptor)
    ):
        return False
    return True


def source_record_historical_descriptor_migration_overlay_path(paper_dir: Path) -> Path:
    return paper_dir / "audit" / SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_FILENAME


def _semantic_rebind_module() -> Any:
    """Load the schema-2 item-level transport lazily.

    The evidence gate imports this legacy bridge lazily, while the schema-2
    transport calls the evidence gate's folder-aware raw identity validator.
    Deferring this import keeps that authentication cycle explicit rather than
    relying on module import order.
    """

    try:
        from scripts import source_record_semantic_rebind as semantic_rebind
    except ModuleNotFoundError:  # pragma: no cover - direct-script fallback.
        import source_record_semantic_rebind as semantic_rebind
    return semantic_rebind


def load_current_source_record_historical_descriptor_migration_items(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    *,
    path: Path | None = None,
    include_semantic_rebind: bool = True,
    semantic_rebind_identity_context: object | None = None,
) -> dict[str, dict[str, Any]]:
    """Load only historical items whose exact current descriptor still replays."""

    # Schema 2 is a separate, stronger authenticated sidecar transport.  It
    # has its own artifact path and validates live folder inputs before it
    # returns a private loader token.  Keep schema 1 below as a legacy bridge;
    # neither artifact can be smuggled through the ordinary sidecar path.
    semantic_items: dict[str, dict[str, Any]] = {}
    if include_semantic_rebind and path is None:
        try:
            semantic = _semantic_rebind_module()
            if semantic_rebind_identity_context is None:
                semantic_items = semantic.load_current_source_record_semantic_rebind_items(
                    paper_dir, paper, current_raw_audit
                )
            else:
                semantic_items = semantic.load_current_source_record_semantic_rebind_items(
                    paper_dir,
                    paper,
                    current_raw_audit,
                    identity_context=semantic_rebind_identity_context,
                )
        except Exception:  # noqa: BLE001 - an overlay failure is non-evidence.
            semantic_items = {}

    migration_path = path or source_record_historical_descriptor_migration_overlay_path(
        paper_dir
    )
    try:
        payload = json.loads(migration_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return semantic_items
    if source_record_historical_descriptor_migration_overlay_error(
        payload, paper=paper, paper_dir=paper_dir
    ):
        return semantic_items
    try:
        prior_path = _resolve_paper_path(
            payload["prior_raw_audit"].get("path"), paper_dir, label="prior raw audit path"
        )
        snapshot_path = _resolve_paper_path(
            payload["current_raw_audit_snapshot"].get("path"),
            paper_dir,
            label="current raw audit snapshot path",
        )
        map_path = _resolve_paper_path(
            payload["paper_statement_map"].get("path"),
            paper_dir,
            label="paper statement map path",
        )
        prior_raw = _read_json_object(prior_path, label="prior raw audit")
        snapshot_current = _read_json_object(snapshot_path, label="current raw audit snapshot")
        statement_map = _read_json_object(map_path, label="paper statement map")
        if _valid_raw_audit(current_raw_audit, paper=paper, label="current"):
            return semantic_items
        if _sha256(current_raw_audit.get("paper_statement_map_sha256")) != _sha256(
            snapshot_current.get("paper_statement_map_sha256")
        ):
            return semantic_items
        prior_groups = _snapshot_groups(prior_raw, label="prior")
        snapshot_groups = _snapshot_groups(snapshot_current, label="current")
        current_groups = _snapshot_groups(current_raw_audit, label="current")
        prior_endpoints = _semantic_endpoint_ledger(
            prior_raw, statement_map, current=False
        )
        snapshot_endpoints = _semantic_endpoint_ledger(
            snapshot_current, statement_map, current=True
        )
        current_endpoints = _semantic_endpoint_ledger(
            current_raw_audit, statement_map, current=True
        )
    except SourceRecordHistoricalDescriptorMigrationError:
        return semantic_items
    raw_items = payload.get("items")
    if not isinstance(raw_items, Mapping):
        return semantic_items
    current_digest = _sha256(current_raw_audit.get("source_record_audit_sha256"))
    out: dict[str, dict[str, Any]] = {}
    for raw_key, value in raw_items.items():
        key = str(raw_key).strip()
        if not key or not isinstance(value, Mapping):
            continue
        group = current_groups.get(key)
        if group is None:
            continue
        if not _migration_item_current(
            key,
            value,
            current_raw_audit=current_raw_audit,
            snapshot_prior_raw=prior_raw,
            snapshot_current_raw=snapshot_current,
            statement_map=statement_map,
            snapshot_prior_groups=prior_groups,
            snapshot_current_groups=snapshot_groups,
            live_current_groups=current_groups,
            prior_endpoint_ledger=prior_endpoints,
            snapshot_current_endpoint_ledger=snapshot_endpoints,
            live_current_endpoint_ledger=current_endpoints,
        ):
            continue
        out[key] = _LoadedHistoricalDescriptorMigrationItem(
            _current_item_from_group(value, group, current_raw_digest=current_digest)
        )
    # The schema-2 transport is stronger for a collision because it authenticates
    # the live raw/map and a full name-independent descriptor.  Do not however
    # let its nonempty subset hide unrelated valid schema-1 migration entries.
    # The merge is by current storage address only after each loader has
    # independently authenticated its semantic relation.
    return {**out, **semantic_items}


def is_loaded_source_record_historical_descriptor_migration_item(value: object) -> bool:
    try:
        if _semantic_rebind_module().is_loaded_source_record_semantic_rebind_item(value):
            return True
    except Exception:  # noqa: BLE001 - a forged or unavailable overlay is false.
        pass
    return bool(
        isinstance(value, _LoadedHistoricalDescriptorMigrationItem)
        and value._source_record_historical_descriptor_migration_loader_token
        is _LOADED_OVERLAY_ITEM_SENTINEL
        and isinstance(
            value.get(SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_ITEM_FIELD), Mapping
        )
    )


def source_record_historical_descriptor_migration_item_has_provenance(value: object) -> bool:
    try:
        if _semantic_rebind_module().source_record_semantic_rebind_item_has_provenance(
            value
        ):
            return True
    except Exception:  # noqa: BLE001 - preserve the legacy fail-closed path.
        pass
    return bool(
        isinstance(value, Mapping)
        and isinstance(
            value.get(SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_ITEM_FIELD), Mapping
        )
    )


def copy_loaded_source_record_historical_descriptor_migration_item(
    value: Mapping[str, Any], updates: Mapping[str, Any] | None = None
) -> dict[str, Any]:
    try:
        semantic = _semantic_rebind_module()
        if semantic.is_loaded_source_record_semantic_rebind_item(value):
            return semantic.copy_loaded_source_record_semantic_rebind_item(value, updates)
    except Exception:  # noqa: BLE001 - only a private token may take this path.
        pass
    copied: dict[str, Any] = dict(value)
    if updates:
        copied.update(updates)
    if is_loaded_source_record_historical_descriptor_migration_item(value):
        return _LoadedHistoricalDescriptorMigrationItem(copied)
    return copied


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
    try:
        os.replace(temporary, path)
    finally:
        if temporary.exists():
            temporary.unlink()


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description=(
            "Build the one-time explicit historical v10 descriptor-migration overlay "
            "without running a raw source or Lean audit."
        )
    )
    parser.add_argument("--root", type=Path, default=ROOT)
    parser.add_argument("--paper", required=True)
    parser.add_argument("--prior-raw-audit", type=Path, required=True)
    parser.add_argument("--current-raw-audit", type=Path)
    parser.add_argument("--prior-judgments", type=Path, required=True)
    parser.add_argument("--prior-attestation", type=Path, required=True)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--write", action="store_true")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    root = args.root.resolve()
    paper_dir = root / "papers" / args.paper
    current_path = args.current_raw_audit or paper_dir / "audit" / "source_record_audit.json"
    out = args.out or source_record_historical_descriptor_migration_overlay_path(paper_dir)
    try:
        for path, label in (
            (args.prior_raw_audit, "--prior-raw-audit"),
            (current_path, "--current-raw-audit"),
            (args.prior_judgments, "--prior-judgments"),
            (args.prior_attestation, "--prior-attestation"),
            (out, "--out"),
        ):
            _relative_paper_path(path, paper_dir)
        prior_raw = _read_json_object(args.prior_raw_audit, label="prior raw audit")
        current_raw = _read_json_object(current_path, label="current raw audit")
        prior_judgments = _read_json_object(args.prior_judgments, label="prior judgments")
        prior_attestation = _read_json_object(args.prior_attestation, label="prior attestation")
        statement_map = _read_json_object(
            paper_dir / "audit" / "paper_statement_map.json", label="paper statement map"
        )
        payload = build_source_record_historical_descriptor_migration(
            paper=args.paper,
            paper_dir=paper_dir,
            prior_raw_audit=prior_raw,
            current_raw_audit=current_raw,
            prior_judgments=prior_judgments,
            prior_attestation=prior_attestation,
            prior_raw_audit_path=args.prior_raw_audit,
            current_raw_audit_path=current_path,
            prior_judgments_path=args.prior_judgments,
            prior_attestation_path=args.prior_attestation,
            statement_map=statement_map,
        )
    except SourceRecordHistoricalDescriptorMigrationError as exc:
        print(f"{args.paper}: historical descriptor migration refused: {exc}", file=sys.stderr)
        return 1
    migrated = sum(1 for item in payload["decisions"] if item["status"] == "migrated")
    manual = sum(
        1
        for item in payload["decisions"]
        if item["status"] == "manual_current_review_required"
    )
    if args.write:
        _atomic_write(out, json.dumps(payload, indent=2, sort_keys=True) + "\n")
        print(f"{args.paper}: wrote {out} ({migrated} migrated, {manual} manual)")
    else:
        print(
            f"{args.paper}: historical descriptor migration validates "
            f"({migrated} migrated, {manual} manual); rerun with --write"
        )
    return 0


if __name__ == "__main__":  # pragma: no cover - exercised through CLI.
    raise SystemExit(main())
