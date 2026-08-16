#!/usr/bin/env python3
"""One-time, fail-closed migration of source-record v4 judgments to v5.

Schema 4 item receipts omitted portions of an item's expanded Lean surface.
They must therefore never be treated as ordinary schema-5 receipts.  This
module supports a deliberately narrow bridge: a saved v4 judgment can be
re-expressed as a v5 judgment only after a deterministic comparison of the
saved raw v4 item group with a current raw v5 item group.

The bridge is intentionally an overlay rather than a mutation of the normal
judgment sidecar.  It has three useful properties:

* it preserves the original, independently receipt-checked raw audit and
  judgment provenance;
* it compares a full, name-independent semantic descriptor, including the
  expanded obligation, source association/content, elaborated Lean surface,
  scoped context, and proof-fidelity records; and
* it permits no key remap.  A migrated item remains usable only under the
  exact generated judgment key that existed in both raw audits.

The normal schema-5 reuse path is deliberately outside this module.  It may
continue to use its existing unique semantic-ID rename handling; this one-time
schema bridge may not.
"""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from typing import Any, Mapping

try:  # Supports direct execution and package imports in repository scripts.
    from source_record_freshness import SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    from source_record_integrity import (
        SOURCE_RECORD_REUSABLE_ITEM_SECTIONS,
        canonical_digest_payload,
        source_record_audit_receipt_error,
        source_record_item_reuse_eligible,
        source_record_item_is_nonreusable_theorem_facing_mirror,
        source_record_raw_reusable_item_metadata_error,
    )
except ModuleNotFoundError:  # pragma: no cover - exercised by package imports.
    from scripts.source_record_freshness import SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    from scripts.source_record_integrity import (
        SOURCE_RECORD_REUSABLE_ITEM_SECTIONS,
        canonical_digest_payload,
        source_record_audit_receipt_error,
        source_record_item_reuse_eligible,
        source_record_item_is_nonreusable_theorem_facing_mirror,
        source_record_raw_reusable_item_metadata_error,
    )


SOURCE_RECORD_SCHEMA4_ITEM_DIGEST_SCHEMA = 4
SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_SCHEMA = 1
SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_POLICY_VERSION = (
    "source-record-schema4-to5-direct-key-semantic-overlay-v1"
)
SOURCE_RECORD_V10_PROMPT_VERSION = (
    "source-record-v10-semantic-conclusion-boundary-contract"
)
SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_FILENAME = (
    "source_record_schema4_to5_migration.json"
)
SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_ARTIFACT_KIND = (
    "source_record_schema4_to5_judgment_migration"
)
SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_INTEGRITY_FIELD = (
    "source_record_schema4_to5_migration_sha256"
)
SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_ITEM_FIELD = (
    "source_record_schema4_to5_migration"
)
_SHA256_RE = re.compile(r"^[0-9a-fA-F]{64}$")

# The migration overlay is ordinary JSON on disk.  Its special currentness
# path must therefore be authenticated in memory, rather than by a JSON field
# an arbitrary direct Python caller could forge.  The token lives only on the
# private dict subclass; ``json.dumps`` sees the normal mapping contents and
# never serializes the token.
_LOADED_OVERLAY_ITEM_SENTINEL = object()


class _LoadedSourceRecordSchema4To5MigrationItem(dict[str, Any]):
    __slots__ = ("_source_record_schema4_to5_loader_token",)

    def __init__(self, value: Mapping[str, Any]) -> None:
        super().__init__(value)
        self._source_record_schema4_to5_loader_token = (
            _LOADED_OVERLAY_ITEM_SENTINEL
        )


# This is a frozen migration descriptor rather than an alias for the ordinary
# schema-5 item digest projection.  The ordinary projection may evolve with
# the current audit engine; changing that implementation must not silently
# widen this one-time bridge.  New item fields are retained by default.
_MIGRATION_NAVIGATION_FIELDS = frozenset(
    {
        "row",
        "judgment_key",
        "binder",
        "lean_source_declaration",
        "effective_lean_source_declaration",
        "qualified_declaration",
        "effective_qualified_declaration",
        "reviewed_declaration_identity",
        "reviewed_elaborated_signature_identities",
        "paper_statement_map_sha256",
        "source_contract_association",
        "semantic_contract_source_association",
        "source_statement_association",
        "semantic_contract_group",
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
# These are generated receipt transport fields, not part of the underlying
# mathematical obligation.  Keep this deliberately explicit: a future
# `source_record_item_*` field is semantic by default and must therefore
# change the schema4-to5 descriptor unless it is consciously added here.
_MIGRATION_RECEIPT_ONLY_FIELDS = frozenset(
    {
        "source_record_item_reuse_eligibility",
        "source_record_item_digest_schema",
        "source_record_item_semantic_id",
        "source_record_item_context_sha256",
        "source_record_item_sha256",
        # These two remain separately represented in the descriptor below so
        # their absence/presence and values cannot be hidden as receipt churn.
        "source_record_item_semantic_context_requirements_sha256",
        "source_record_item_source_proof_fidelity_records_sha256",
    }
)
_MIGRATION_ASSOCIATION_FIELDS = (
    "source_contract_association",
    "semantic_contract_source_association",
    "source_statement_association",
    "semantic_contract_group",
)
_ROUTE_SCOPE_REFERENCE_FIELDS = frozenset(
    {
        "qualified_declaration",
        "paired_qualified_declaration",
        "semantic_model_judgment_key",
        "evidence_declaration",
        "spec_declaration",
        "row",
    }
)
_ROUTE_SCOPE_IGNORED_FIELDS = frozenset(
    {
        "source_key",
        "source_location",
        "source_kind",
        "source_map_item_sha256",
        "source_map_item_keys",
        "source_map_item_keys_sha256",
        "source_map_item_sha256_by_key",
        "association_sha256",
        "semantic_association_sha256",
        "source_item_semantic_sha256",
    }
)


class SourceRecordSchema4To5MigrationError(ValueError):
    """Raised when a requested migration input is not an admissible receipt."""


def _stable_digest(payload: object) -> str:
    encoded = json.dumps(
        canonical_digest_payload(payload), sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _valid_sha256(value: object) -> str:
    digest = str(value or "").strip().lower()
    return digest if _SHA256_RE.fullmatch(digest) else ""


def _migration_projection(value: object) -> object:
    """Keep the full generated obligation while dropping only navigation data."""

    if isinstance(value, Mapping):
        projected: dict[str, object] = {}
        for raw_key, raw_value in value.items():
            key = str(raw_key)
            normalized = key.strip().lower()
            if (
                normalized in _MIGRATION_NAVIGATION_FIELDS
                or normalized in _MIGRATION_RECEIPT_ONLY_FIELDS
            ):
                continue
            projected[key] = _migration_projection(raw_value)
        return projected
    if isinstance(value, list):
        return [_migration_projection(item) for item in value]
    if isinstance(value, tuple):
        return [_migration_projection(item) for item in value]
    return value


def _association_mappings(item: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    return [
        association
        for field in _MIGRATION_ASSOCIATION_FIELDS
        if isinstance((association := item.get(field)), Mapping)
    ]


def _source_semantic_identities(item: Mapping[str, Any]) -> list[dict[str, str]]:
    identities: set[str] = set()
    for association in _association_mappings(item):
        raw_identities = association.get("source_item_identities")
        if not isinstance(raw_identities, list):
            continue
        for raw_identity in raw_identities:
            if not isinstance(raw_identity, Mapping):
                continue
            digest = _valid_sha256(raw_identity.get("source_semantic_sha256"))
            if digest:
                identities.add(digest)
    return [{"source_semantic_sha256": digest} for digest in sorted(identities)]


def _association_semantic_digests(item: Mapping[str, Any]) -> list[str]:
    return sorted(
        {
            digest
            for association in _association_mappings(item)
            if (digest := _valid_sha256(association.get("semantic_association_sha256")))
        }
    )


def _route_identity_digest(value: object) -> str:
    """Pin an exact configured route without exposing its spelling as a match key."""

    text = str(value or "").strip()
    return _stable_digest({"route_identity": text}) if text else ""


def _route_scope_projection(value: object) -> object:
    """Normalize association/group semantics while removing presentation names.

    ``semantic_association_sha256`` intentionally binds source content and the
    current elaborated endpoint, not the route's *role*.  A direct source
    route, a support route, and two members of a direct/Spec pair therefore
    need an additional descriptor.  Fully-qualified route strings are hashed
    only to pin a pair/group relationship; no caller uses them to discover or
    remap a judgment key.
    """

    if isinstance(value, Mapping):
        projected: dict[str, object] = {}
        for raw_key, raw_value in value.items():
            key = str(raw_key)
            normalized = key.strip().lower()
            if normalized in _ROUTE_SCOPE_IGNORED_FIELDS:
                continue
            if normalized == "source_item_identities":
                identities: set[str] = set()
                if isinstance(raw_value, list):
                    for identity in raw_value:
                        if isinstance(identity, Mapping):
                            digest = _valid_sha256(
                                identity.get("source_semantic_sha256")
                            )
                            if digest:
                                identities.add(digest)
                projected["source_item_semantic_identities"] = sorted(identities)
                continue
            if normalized in _ROUTE_SCOPE_REFERENCE_FIELDS:
                projected[key + "_route_identity_sha256"] = _route_identity_digest(
                    raw_value
                )
                continue
            if normalized == "reviewed_declaration_identity" and isinstance(
                raw_value, Mapping
            ):
                projected[key] = {
                    "declaration_sha256": _valid_sha256(
                        raw_value.get("declaration_sha256")
                    ),
                    "route_identity_sha256": _route_identity_digest(
                        raw_value.get("qualified_declaration")
                    ),
                }
                continue
            if normalized == "reviewed_elaborated_signature_identity" and isinstance(
                raw_value, Mapping
            ):
                projected[key] = {
                    "elaborated_signature_sha256": _valid_sha256(
                        raw_value.get("elaborated_signature_sha256")
                    ),
                    "route_identity_sha256": _route_identity_digest(
                        raw_value.get("qualified_declaration")
                    ),
                }
                continue
            projected[key] = _route_scope_projection(raw_value)
        return projected
    if isinstance(value, list):
        return sorted(
            [_route_scope_projection(item) for item in value],
            key=lambda item: json.dumps(item, sort_keys=True, separators=(",", ":")),
        )
    if isinstance(value, tuple):
        return _route_scope_projection(list(value))
    return value


def _association_route_scopes(item: Mapping[str, Any]) -> list[dict[str, object]]:
    """Return field-distinguished direct/support/contract-pair route semantics."""

    scopes: list[dict[str, object]] = []
    for field in _MIGRATION_ASSOCIATION_FIELDS:
        raw_scope = item.get(field)
        if isinstance(raw_scope, Mapping):
            scopes.append(
                {
                    "association_field": field,
                    "scope": _route_scope_projection(raw_scope),
                }
            )
    return sorted(
        scopes,
        key=lambda scope: json.dumps(scope, sort_keys=True, separators=(",", ":")),
    )


def _declaration_source_digests(item: Mapping[str, Any]) -> list[str]:
    identities: list[Mapping[str, Any]] = []
    direct = item.get("reviewed_declaration_identity")
    if isinstance(direct, Mapping):
        identities.append(direct)
    for association in _association_mappings(item):
        identity = association.get("reviewed_declaration_identity")
        if isinstance(identity, Mapping):
            identities.append(identity)
    return sorted(
        {
            digest
            for identity in identities
            if (digest := _valid_sha256(identity.get("declaration_sha256")))
        }
    )


def _elaborated_signature_digests(item: Mapping[str, Any]) -> list[str]:
    signatures: list[Mapping[str, Any]] = []
    direct = item.get("reviewed_elaborated_signature_identities")
    if isinstance(direct, list):
        signatures.extend(entry for entry in direct if isinstance(entry, Mapping))
    for association in _association_mappings(item):
        identity = association.get("reviewed_elaborated_signature_identity")
        if isinstance(identity, Mapping):
            signatures.append(identity)
    return sorted(
        {
            digest
            for signature in signatures
            if (digest := _valid_sha256(signature.get("elaborated_signature_sha256")))
        }
    )


def source_record_schema4_to5_item_descriptor(
    item: Mapping[str, Any],
) -> dict[str, object]:
    """Return the migration's complete, name-independent item descriptor.

    The descriptor deliberately separates source and Lean provenance from the
    generated obligation projection.  The association and elaborated values
    are retained as digest-only identities: declaration spelling or a
    source-map key cannot establish equality, while changed source bytes,
    source association, Lean declaration text, elaborated type, context, or
    proof-fidelity record cannot be hidden as navigation churn.
    """

    return {
        "schema": SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_SCHEMA,
        "generated_obligation": _migration_projection(item),
        "source_item_semantic_identities": _source_semantic_identities(item),
        "source_association_semantic_sha256": _association_semantic_digests(item),
        "source_association_route_scope": _association_route_scopes(item),
        "reviewed_declaration_source_sha256": _declaration_source_digests(item),
        "reviewed_elaborated_signature_sha256": _elaborated_signature_digests(item),
        # An absent scoped pin means the generator found no scoped condition
        # for this item.  A newly introduced pin is therefore a descriptor
        # change, not a cosmetic schema upgrade.
        "scoped_semantic_context_requirements_sha256": _valid_sha256(
            item.get("source_record_item_semantic_context_requirements_sha256")
        ),
        "source_proof_fidelity_records_sha256": _valid_sha256(
            item.get("source_record_item_source_proof_fidelity_records_sha256")
        ),
    }


def source_record_schema4_to5_item_descriptor_sha256(item: Mapping[str, Any]) -> str:
    return _stable_digest(source_record_schema4_to5_item_descriptor(item))


def _raw_item_groups(
    payload: Mapping[str, Any],
    *,
    expected_item_digest_schema: int,
) -> tuple[dict[str, dict[str, object]], dict[str, str]]:
    """Build complete reusable item groups keyed by exact judgment key.

    A single source-record response may cover a boundary view and a richer
    conclusion-dependency view.  The bridge therefore compares a multiset of
    descriptors, not merely one scalar digest selected by a key.  Any
    aggregate-only/malformed item makes that key non-migratable rather than
    allowing the remaining, weaker view to stand in for it.
    """

    raw_groups: dict[str, list[dict[str, Any]]] = {}
    for section in SOURCE_RECORD_REUSABLE_ITEM_SECTIONS:
        raw_items = payload.get(section)
        if not isinstance(raw_items, list):
            continue
        for raw_item in raw_items:
            if not isinstance(raw_item, Mapping):
                continue
            if source_record_item_is_nonreusable_theorem_facing_mirror(
                section, raw_item
            ):
                continue
            key = str(raw_item.get("judgment_key") or "").strip()
            if not key:
                continue
            raw_groups.setdefault(key, []).append(dict(raw_item))

    groups: dict[str, dict[str, object]] = {}
    errors: dict[str, str] = {}
    for key, raw_items in raw_groups.items():
        members: list[dict[str, object]] = []
        for item in raw_items:
            if not source_record_item_reuse_eligible(
                item, expected_item_digest_schema=expected_item_digest_schema
            ):
                errors[key] = (
                    "raw audit contains an aggregate-only or malformed generated item"
                )
                break
            kind = str(item.get("kind") or "").strip()
            digest = _valid_sha256(item.get("source_record_item_sha256"))
            if not kind or not digest:
                errors[key] = "raw audit item lacks a kind or item receipt"
                break
            descriptor = source_record_schema4_to5_item_descriptor(item)
            members.append(
                {
                    "kind": kind,
                    "descriptor": descriptor,
                    "descriptor_sha256": _stable_digest(descriptor),
                    "source_record_item_digest_schema": expected_item_digest_schema,
                    "source_record_item_sha256": digest,
                }
            )
        if key in errors:
            continue
        ordered_members = sorted(
            members,
            key=lambda member: json.dumps(member, sort_keys=True, separators=(",", ":")),
        )
        descriptor = {
            "schema": SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_SCHEMA,
            "items": [
                {
                    "kind": member["kind"],
                    "descriptor": member["descriptor"],
                }
                for member in ordered_members
            ],
        }
        pin_tuples = [
            (
                str(member["kind"]),
                int(member["source_record_item_digest_schema"]),
                str(member["source_record_item_sha256"]),
            )
            for member in ordered_members
        ]
        # Schema 4 exposed an incomplete item receipt.  Two generated
        # obligations can therefore collide on the same old `(kind, digest)`
        # pair even when their complete semantic descriptors differ.  A set
        # projection would erase that multiplicity and let one sidecar pin
        # stand in for both.  Reject the entire exact-key group before any
        # later pin comparison can collapse it.
        if (
            expected_item_digest_schema == SOURCE_RECORD_SCHEMA4_ITEM_DIGEST_SCHEMA
            and len(set(pin_tuples)) != len(pin_tuples)
        ):
            errors[key] = (
                "raw audit contains duplicate schema-4 (kind, item digest) "
                "members for one exact judgment key"
            )
            continue
        pins = sorted(set(pin_tuples))
        digests = {
            str(member["source_record_item_sha256"]) for member in ordered_members
        }
        groups[key] = {
            "descriptor": descriptor,
            "descriptor_sha256": _stable_digest(descriptor),
            # Preserve raw multiplicity separately from the normalized pin
            # list.  A legacy scalar receipt may represent exactly one raw
            # obligation, never merely one de-duplicated `(kind, digest)` pin.
            "raw_reusable_member_count": len(ordered_members),
            "item_pins": [
                {
                    "kind": kind,
                    "source_record_item_digest_schema": schema,
                    "source_record_item_sha256": digest,
                }
                for kind, schema, digest in pins
            ],
            # A scalar receipt is safe only for one raw generated obligation.
            # A multi-view key must carry its complete exact pin list even if
            # all views happened to share one digest.
            "scalar_item_digest": (
                next(iter(digests)) if len(ordered_members) == 1 else ""
            ),
        }
    return groups, errors


def _valid_pin_set(
    raw_pins: object,
    *,
    expected_item_digest_schema: int,
) -> list[dict[str, object]] | None:
    if not isinstance(raw_pins, list) or not raw_pins:
        return None
    pins: set[tuple[str, int, str]] = set()
    for raw_pin in raw_pins:
        if not isinstance(raw_pin, Mapping):
            return None
        kind = str(raw_pin.get("kind") or "").strip()
        schema = raw_pin.get("source_record_item_digest_schema")
        digest = _valid_sha256(raw_pin.get("source_record_item_sha256"))
        if not kind or schema != expected_item_digest_schema or not digest:
            return None
        pins.add((kind, schema, digest))
    if len(pins) != len(raw_pins):
        return None
    return [
        {
            "kind": kind,
            "source_record_item_digest_schema": schema,
            "source_record_item_sha256": digest,
        }
        for kind, schema, digest in sorted(pins)
    ]


def _raw_audit_provenance(
    payload: Mapping[str, Any], path: Path) -> dict[str, str]:
    return {
        "path": str(path),
        "file_sha256": _sha256_file(path),
        "source_record_audit_sha256": _valid_sha256(
            payload.get("source_record_audit_sha256")
        ),
        "source_record_audit_integrity_sha256": _valid_sha256(
            payload.get("source_record_audit_integrity_sha256")
        ),
    }


def _effective_item_value(
    value: Mapping[str, Any], payload: Mapping[str, Any], field: str
) -> object:
    return value.get(field) or payload.get(field)


def _valid_judgment_metadata(
    value: Mapping[str, Any], payload: Mapping[str, Any]) -> bool:
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
    return bool(validator and timestamp)


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


def _raw_audit_input_error(
    payload: object,
    *,
    paper: str,
    expected_item_digest_schema: int,
    label: str,
) -> str:
    if not isinstance(payload, Mapping):
        return f"{label} raw audit is not an object"
    if payload.get("paper") != paper:
        return f"{label} raw audit does not record the exact requested paper"
    if str(payload.get("prompt_version") or "").strip() != SOURCE_RECORD_V10_PROMPT_VERSION:
        return f"{label} raw audit does not use the current v10 prompt family"
    policy = str(payload.get("source_record_policy_version") or "").strip()
    if policy != SOURCE_RECORD_V10_PROMPT_VERSION:
        return f"{label} raw audit does not record the current v10 policy version"
    receipt_error = source_record_audit_receipt_error(payload)
    if receipt_error:
        return f"{label} raw audit receipt is invalid: {receipt_error}"
    metadata_error = source_record_raw_reusable_item_metadata_error(
        payload, expected_item_digest_schema=expected_item_digest_schema
    )
    if metadata_error:
        return f"{label} raw audit item metadata is invalid: {metadata_error}"
    return ""


def _migration_payload_without_integrity(payload: Mapping[str, Any]) -> dict[str, Any]:
    return {
        str(key): value
        for key, value in payload.items()
        if str(key) != SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_INTEGRITY_FIELD
    }


def source_record_schema4_to5_migration_sha256(payload: Mapping[str, Any]) -> str:
    return _stable_digest(_migration_payload_without_integrity(payload))


def stamp_source_record_schema4_to5_migration(payload: dict[str, Any]) -> None:
    payload[SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_INTEGRITY_FIELD] = (
        source_record_schema4_to5_migration_sha256(payload)
    )


def _migration_item_metadata_error(
    key: str,
    value: Mapping[str, Any],
    top_level: Mapping[str, Any],
) -> str:
    migration = value.get(SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_ITEM_FIELD)
    if not isinstance(migration, Mapping):
        return "is missing migration provenance"
    if migration.get("schema") != SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_SCHEMA:
        return "has an unsupported migration provenance schema"
    if (
        str(migration.get("migration_policy_version") or "").strip()
        != SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_POLICY_VERSION
    ):
        return "has an unsupported migration policy"
    if (
        migration.get("from_item_digest_schema")
        != SOURCE_RECORD_SCHEMA4_ITEM_DIGEST_SCHEMA
        or migration.get("to_item_digest_schema") != SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    ):
        return "has an invalid migration item-digest schema transition"
    if (
        str(migration.get("prior_judgment_key") or "").strip() != key
        or str(migration.get("current_judgment_key") or "").strip() != key
    ):
        return "does not retain its exact direct judgment key"
    if str(value.get("prompt_version") or "").strip() != SOURCE_RECORD_V10_PROMPT_VERSION:
        return "does not carry the current v10 prompt version"
    if value.get("source_record_item_digest_schema") != SOURCE_RECORD_ITEM_DIGEST_SCHEMA:
        return "does not carry a schema-5 item digest declaration"

    prior_descriptor = migration.get("prior_item_semantic_descriptor")
    current_descriptor = migration.get("current_item_semantic_descriptor")
    if not isinstance(prior_descriptor, Mapping) or not isinstance(current_descriptor, Mapping):
        return "lacks complete prior/current semantic descriptors"
    prior_descriptor_digest = _valid_sha256(
        migration.get("prior_item_semantic_descriptor_sha256")
    )
    current_descriptor_digest = _valid_sha256(
        migration.get("current_item_semantic_descriptor_sha256")
    )
    if not prior_descriptor_digest or not current_descriptor_digest:
        return "lacks descriptor SHA-256 provenance"
    if (
        prior_descriptor_digest != _stable_digest(prior_descriptor)
        or current_descriptor_digest != _stable_digest(current_descriptor)
    ):
        return "has a descriptor SHA-256 mismatch"
    if canonical_digest_payload(prior_descriptor) != canonical_digest_payload(
        current_descriptor
    ):
        return "records nonidentical prior/current semantic descriptors"

    for audit_field in ("prior_raw_audit", "current_raw_audit"):
        provenance = migration.get(audit_field)
        if not isinstance(provenance, Mapping):
            return f"lacks {audit_field} provenance"
        for digest_field in (
            "file_sha256",
            "source_record_audit_sha256",
            "source_record_audit_integrity_sha256",
        ):
            if not _valid_sha256(provenance.get(digest_field)):
                return f"has malformed {audit_field}.{digest_field}"
    for audit_field in ("prior_raw_audit", "current_raw_audit"):
        top_provenance = top_level.get(audit_field)
        item_provenance = migration.get(audit_field)
        if not isinstance(top_provenance, Mapping):
            return f"has no top-level {audit_field} provenance"
        if not isinstance(item_provenance, Mapping) or canonical_digest_payload(
            item_provenance
        ) != canonical_digest_payload(top_provenance):
            return f"has item {audit_field} provenance that differs from the overlay"
    return ""


def source_record_schema4_to5_migration_overlay_error(
    payload: object,
    *,
    paper: str,
) -> str:
    """Validate overlay transport/provenance, leaving item freshness per-item.

    This intentionally does not compare every item to a current raw audit.
    One changed item must not invalidate a still-correct migration receipt for
    unrelated direct keys; callers use ``..._migration_item_current`` below
    for that per-item fail-closed check.
    """

    if not isinstance(payload, Mapping):
        return "schema4-to5 migration overlay is not an object"
    if payload.get("schema") != 1:
        return "schema4-to5 migration overlay lacks sidecar schema 1"
    if (
        str(payload.get("artifact_kind") or "").strip()
        != SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_ARTIFACT_KIND
    ):
        return "schema4-to5 migration overlay has the wrong artifact kind"
    if payload.get("migration_schema") != SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_SCHEMA:
        return "schema4-to5 migration overlay has an unsupported migration schema"
    if (
        str(payload.get("migration_policy_version") or "").strip()
        != SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_POLICY_VERSION
    ):
        return "schema4-to5 migration overlay has an unsupported migration policy"
    if payload.get("paper") != paper:
        return "schema4-to5 migration overlay belongs to a different paper"
    if (
        str(payload.get("prompt_version") or "").strip()
        != SOURCE_RECORD_V10_PROMPT_VERSION
        or str(payload.get("source_record_policy_version") or "").strip()
        != SOURCE_RECORD_V10_PROMPT_VERSION
    ):
        return "schema4-to5 migration overlay does not record the current v10 prompt family"
    if (
        payload.get("from_item_digest_schema")
        != SOURCE_RECORD_SCHEMA4_ITEM_DIGEST_SCHEMA
        or payload.get("to_item_digest_schema") != SOURCE_RECORD_ITEM_DIGEST_SCHEMA
    ):
        return "schema4-to5 migration overlay has an invalid schema transition"
    if _payload_is_non_evidence(payload):
        return "schema4-to5 migration overlay is marked non-evidence"
    recorded_digest = _valid_sha256(
        payload.get(SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_INTEGRITY_FIELD)
    )
    if not recorded_digest:
        return "schema4-to5 migration overlay lacks its integrity digest"
    if recorded_digest != source_record_schema4_to5_migration_sha256(payload):
        return "schema4-to5 migration overlay integrity digest does not match"
    for audit_field in ("prior_raw_audit", "current_raw_audit"):
        provenance = payload.get(audit_field)
        if not isinstance(provenance, Mapping):
            return f"schema4-to5 migration overlay lacks {audit_field} provenance"
        for digest_field in (
            "file_sha256",
            "source_record_audit_sha256",
            "source_record_audit_integrity_sha256",
        ):
            if not _valid_sha256(provenance.get(digest_field)):
                return (
                    "schema4-to5 migration overlay has malformed "
                    f"{audit_field}.{digest_field}"
                )
    prior_judgments = payload.get("prior_judgments")
    if not isinstance(prior_judgments, Mapping) or not _valid_sha256(
        prior_judgments.get("file_sha256")
    ):
        return "schema4-to5 migration overlay lacks prior judgment-file provenance"
    raw_items = payload.get("items")
    if not isinstance(raw_items, Mapping):
        return "schema4-to5 migration overlay items are not an object"
    for raw_key, raw_value in raw_items.items():
        key = str(raw_key).strip()
        if not key or not isinstance(raw_value, Mapping):
            return "schema4-to5 migration overlay has a malformed item"
        item_error = _migration_item_metadata_error(key, raw_value, payload)
        if item_error:
            return f"schema4-to5 migration overlay item `{key}` {item_error}"
    return ""


def _judgment_matches_prior_group(
    key: str,
    value: Mapping[str, Any],
    payload: Mapping[str, Any],
    group: Mapping[str, object],
    *,
    prior_audit_digest: str,
) -> str:
    """Return why an old sidecar entry cannot be promoted, or ``''``."""

    if _payload_is_non_evidence(value):
        return "prior judgment is marked non-evidence"
    if (
        str(_effective_item_value(value, payload, "prompt_version") or "").strip()
        != SOURCE_RECORD_V10_PROMPT_VERSION
    ):
        return "prior judgment does not use the current v10 prompt family"
    policy = str(
        _effective_item_value(value, payload, "source_record_policy_version") or ""
    ).strip()
    if policy and policy != SOURCE_RECORD_V10_PROMPT_VERSION:
        return "prior judgment records a different source-record policy version"
    if (
        _valid_sha256(
            _effective_item_value(value, payload, "source_record_audit_sha256")
        )
        != prior_audit_digest
    ):
        return "prior judgment is not tied to the saved prior raw audit"
    if not _valid_judgment_metadata(value, payload):
        return "prior judgment lacks validator/timestamp metadata"

    expected_pins = group.get("item_pins")
    if not isinstance(expected_pins, list) or not expected_pins:
        return "prior raw item group has no reusable receipt pins"
    raw_judgment_pins = value.get("source_record_item_sha256s")
    judgment_pins = _valid_pin_set(
        raw_judgment_pins,
        expected_item_digest_schema=SOURCE_RECORD_SCHEMA4_ITEM_DIGEST_SCHEMA,
    )
    if judgment_pins == expected_pins:
        return ""
    # A bare scalar v4 receipt may be retained only when the prior raw group
    # had exactly one reusable member.  This is deliberately a raw member
    # count, not the size of a de-duplicated pin set: schema 4 collisions can
    # otherwise let one scalar appear to cover two distinct obligations.
    if raw_judgment_pins is None and group.get("raw_reusable_member_count") == 1:
        scalar_schema = value.get("source_record_item_digest_schema")
        scalar_digest = _valid_sha256(value.get("source_record_item_sha256"))
        expected_scalar = _valid_sha256(group.get("scalar_item_digest"))
        if (
            scalar_schema == SOURCE_RECORD_SCHEMA4_ITEM_DIGEST_SCHEMA
            and scalar_digest
            and scalar_digest == expected_scalar
        ):
            return ""
    # A scalar v4 digest cannot establish that the reviewer saw every
    # generated view for a multi-member key. In particular, schema 4 could
    # collide for distinct expanded premises, so any other legacy sidecar
    # without the complete schema-4 pin list is intentionally not bridgeable.
    return "prior judgment does not pin the complete prior schema-4 item group"


def build_source_record_schema4_to5_migration(
    *,
    paper: str,
    prior_raw_audit: Mapping[str, Any],
    prior_judgments: Mapping[str, Any],
    current_raw_audit: Mapping[str, Any],
    prior_raw_audit_path: Path,
    prior_judgments_path: Path,
    current_raw_audit_path: Path,
) -> dict[str, Any]:
    """Build a deterministic direct-key migration overlay.

    Invalid top-level input fails the command.  Differences between individual
    old/current keys are recorded in ``decisions`` and omitted from ``items``;
    they do not suppress reuse for an unrelated key with an identical complete
    descriptor.
    """

    prior_error = _raw_audit_input_error(
        prior_raw_audit,
        paper=paper,
        expected_item_digest_schema=SOURCE_RECORD_SCHEMA4_ITEM_DIGEST_SCHEMA,
        label="prior",
    )
    if prior_error:
        raise SourceRecordSchema4To5MigrationError(prior_error)
    current_error = _raw_audit_input_error(
        current_raw_audit,
        paper=paper,
        expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
        label="current",
    )
    if current_error:
        raise SourceRecordSchema4To5MigrationError(current_error)
    if (
        prior_judgments.get("schema") != 1
        or prior_judgments.get("paper") != paper
        or _payload_is_non_evidence(prior_judgments)
    ):
        raise SourceRecordSchema4To5MigrationError(
            "prior source-record judgment sidecar is not saved evidence for this paper"
        )
    if (
        str(prior_judgments.get("prompt_version") or "").strip()
        != SOURCE_RECORD_V10_PROMPT_VERSION
    ):
        raise SourceRecordSchema4To5MigrationError(
            "prior source-record judgment sidecar does not use the current v10 prompt family"
        )
    prior_policy = str(
        prior_judgments.get("source_record_policy_version") or ""
    ).strip()
    if prior_policy and prior_policy != SOURCE_RECORD_V10_PROMPT_VERSION:
        raise SourceRecordSchema4To5MigrationError(
            "prior source-record judgment sidecar records a different policy version"
        )
    raw_judgments = prior_judgments.get("items") or prior_judgments.get(
        "field_judgments"
    )
    if not isinstance(raw_judgments, Mapping):
        raise SourceRecordSchema4To5MigrationError(
            "prior source-record judgment sidecar has no item object"
        )

    prior_groups, prior_group_errors = _raw_item_groups(
        prior_raw_audit,
        expected_item_digest_schema=SOURCE_RECORD_SCHEMA4_ITEM_DIGEST_SCHEMA,
    )
    current_groups, current_group_errors = _raw_item_groups(
        current_raw_audit,
        expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
    )
    prior_provenance = _raw_audit_provenance(prior_raw_audit, prior_raw_audit_path)
    current_provenance = _raw_audit_provenance(
        current_raw_audit, current_raw_audit_path
    )
    prior_audit_digest = prior_provenance["source_record_audit_sha256"]

    decisions: list[dict[str, str]] = []
    migrated_items: dict[str, dict[str, Any]] = {}
    considered_keys = {
        str(key).strip() for key in raw_judgments if str(key).strip()
    } | set(prior_groups) | set(prior_group_errors) | set(current_groups) | set(
        current_group_errors
    )
    for key in sorted(considered_keys):
        raw_value = raw_judgments.get(key)
        if not isinstance(raw_value, Mapping):
            decisions.append(
                {
                    "judgment_key": key,
                    "status": "not_migrated",
                    "reason": "no prior saved judgment item for this exact key",
                }
            )
            continue
        if key in prior_group_errors:
            decisions.append(
                {
                    "judgment_key": key,
                    "status": "not_migrated",
                    "reason": "prior " + prior_group_errors[key],
                }
            )
            continue
        prior_group = prior_groups.get(key)
        if prior_group is None:
            decisions.append(
                {
                    "judgment_key": key,
                    "status": "not_migrated",
                    "reason": "prior raw audit has no generated item for this exact key",
                }
            )
            continue
        if key in current_group_errors:
            decisions.append(
                {
                    "judgment_key": key,
                    "status": "not_migrated",
                    "reason": "current " + current_group_errors[key],
                }
            )
            continue
        current_group = current_groups.get(key)
        if current_group is None:
            decisions.append(
                {
                    "judgment_key": key,
                    "status": "not_migrated",
                    "reason": "current raw audit has no generated item for this exact key; key remap is forbidden",
                }
            )
            continue
        prior_judgment_error = _judgment_matches_prior_group(
            key,
            raw_value,
            prior_judgments,
            prior_group,
            prior_audit_digest=prior_audit_digest,
        )
        if prior_judgment_error:
            decisions.append(
                {
                    "judgment_key": key,
                    "status": "not_migrated",
                    "reason": prior_judgment_error,
                }
            )
            continue
        if canonical_digest_payload(prior_group["descriptor"]) != canonical_digest_payload(
            current_group["descriptor"]
        ):
            decisions.append(
                {
                    "judgment_key": key,
                    "status": "not_migrated",
                    "reason": "prior/current full semantic descriptor differs",
                }
            )
            continue

        migrated = dict(raw_value)
        migrated.pop("source_record_item_sha256s", None)
        migrated.update(
            {
                "prompt_version": SOURCE_RECORD_V10_PROMPT_VERSION,
                "source_record_policy_version": SOURCE_RECORD_V10_PROMPT_VERSION,
                "source_record_audit_sha256": current_provenance[
                    "source_record_audit_sha256"
                ],
                "source_record_item_digest_schema": SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
                "source_record_item_sha256": str(
                    current_group.get("scalar_item_digest") or ""
                ),
                "source_record_item_sha256s": current_group["item_pins"],
                SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_ITEM_FIELD: {
                    "schema": SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_SCHEMA,
                    "migration_policy_version": SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_POLICY_VERSION,
                    "from_item_digest_schema": SOURCE_RECORD_SCHEMA4_ITEM_DIGEST_SCHEMA,
                    "to_item_digest_schema": SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
                    "prior_judgment_key": key,
                    "current_judgment_key": key,
                    "prior_raw_audit": prior_provenance,
                    "current_raw_audit": current_provenance,
                    "prior_item_semantic_descriptor": prior_group["descriptor"],
                    "prior_item_semantic_descriptor_sha256": prior_group[
                        "descriptor_sha256"
                    ],
                    "current_item_semantic_descriptor": current_group["descriptor"],
                    "current_item_semantic_descriptor_sha256": current_group[
                        "descriptor_sha256"
                    ],
                },
            }
        )
        migrated_items[key] = migrated
        decisions.append(
            {
                "judgment_key": key,
                "status": "migrated",
                "reason": "exact direct key and full semantic descriptor match",
            }
        )

    payload: dict[str, Any] = {
        "schema": 1,
        "artifact_kind": SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_ARTIFACT_KIND,
        "migration_schema": SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_SCHEMA,
        "migration_policy_version": SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_POLICY_VERSION,
        "paper": paper,
        "prompt_version": SOURCE_RECORD_V10_PROMPT_VERSION,
        "source_record_policy_version": SOURCE_RECORD_V10_PROMPT_VERSION,
        "from_item_digest_schema": SOURCE_RECORD_SCHEMA4_ITEM_DIGEST_SCHEMA,
        "to_item_digest_schema": SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
        "prior_raw_audit": prior_provenance,
        "prior_judgments": {
            "path": str(prior_judgments_path),
            "file_sha256": _sha256_file(prior_judgments_path),
        },
        "current_raw_audit": current_provenance,
        "items": migrated_items,
        "decisions": decisions,
    }
    stamp_source_record_schema4_to5_migration(payload)
    return payload


def source_record_schema4_to5_migration_item_current(
    key: str,
    value: Mapping[str, Any],
    *,
    paper: str,
    current_raw_audit: Mapping[str, Any],
) -> bool:
    """Return whether one loaded overlay item still matches the current raw item.

    This recomputes the current complete descriptor.  It intentionally ignores
    a changed aggregate receipt when every item-specific source/Lean/context
    obligation is unchanged, but any change in a field retained by the
    descriptor rejects that one key.
    """

    migration = value.get(SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_ITEM_FIELD)
    if not isinstance(migration, Mapping):
        return False
    if (
        str(migration.get("prior_judgment_key") or "").strip() != key
        or str(migration.get("current_judgment_key") or "").strip() != key
    ):
        return False
    current_error = _raw_audit_input_error(
        current_raw_audit,
        paper=paper,
        expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
        label="current",
    )
    if current_error:
        return False
    groups, group_errors = _raw_item_groups(
        current_raw_audit,
        expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
    )
    if key in group_errors:
        return False
    group = groups.get(key)
    if group is None:
        return False
    stored_descriptor = migration.get("current_item_semantic_descriptor")
    stored_descriptor_digest = _valid_sha256(
        migration.get("current_item_semantic_descriptor_sha256")
    )
    if not isinstance(stored_descriptor, Mapping) or not stored_descriptor_digest:
        return False
    if stored_descriptor_digest != _stable_digest(stored_descriptor):
        return False
    if canonical_digest_payload(stored_descriptor) != canonical_digest_payload(
        group["descriptor"]
    ):
        return False
    stored_pins = _valid_pin_set(
        value.get("source_record_item_sha256s"),
        expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
    )
    if stored_pins != group.get("item_pins"):
        return False
    stored_scalar = _valid_sha256(value.get("source_record_item_sha256"))
    expected_scalar = str(group.get("scalar_item_digest") or "").strip()
    if expected_scalar:
        if stored_scalar != expected_scalar:
            return False
    elif stored_scalar:
        return False
    return True


def is_loaded_source_record_schema4_to5_migration_item(value: object) -> bool:
    """Return whether ``value`` came from a validated migration overlay loader."""

    return bool(
        isinstance(value, _LoadedSourceRecordSchema4To5MigrationItem)
        and value._source_record_schema4_to5_loader_token
        is _LOADED_OVERLAY_ITEM_SENTINEL
        and isinstance(
            value.get(SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_ITEM_FIELD), Mapping
        )
    )


def source_record_schema4_to5_migration_item_has_provenance(value: object) -> bool:
    """Return whether a value claims migration provenance, loaded or not.

    A serialized overlay item is not ordinary schema-5 sidecar evidence.  The
    consumers use this distinction to reject a copied JSON object unless this
    module's loader supplied the private in-memory token above.
    """

    return bool(
        isinstance(value, Mapping)
        and isinstance(
            value.get(SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_ITEM_FIELD), Mapping
        )
    )


def copy_loaded_source_record_schema4_to5_migration_item(
    value: Mapping[str, Any],
    updates: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Copy a loader-authenticated item while retaining its private token.

    This is for in-memory normalization only.  The returned subclass has no
    token field in its mapping contents, so serializing it cannot produce a
    forgeable JSON marker.
    """

    copied: dict[str, Any] = dict(value)
    if updates is not None:
        copied.update(updates)
    if is_loaded_source_record_schema4_to5_migration_item(value):
        return _LoadedSourceRecordSchema4To5MigrationItem(copied)
    return copied


def source_record_schema4_to5_migration_overlay_path(paper_dir: Path) -> Path:
    return paper_dir / "audit" / SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_FILENAME


def load_current_source_record_schema4_to5_migration_items(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    *,
    path: Path | None = None,
) -> dict[str, dict[str, Any]]:
    """Load only overlay entries that remain current for this raw audit.

    The returned entries are marked in memory so callers can bypass ordinary
    scalar/rename handling.  The marker is not serialized into the overlay and
    thus cannot make a normal sidecar entry use migration semantics.
    """

    migration_path = path or source_record_schema4_to5_migration_overlay_path(paper_dir)
    try:
        payload = json.loads(migration_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    if source_record_schema4_to5_migration_overlay_error(payload, paper=paper):
        return {}
    raw_items = payload.get("items")
    if not isinstance(raw_items, Mapping):  # defensive, covered above.
        return {}
    out: dict[str, dict[str, Any]] = {}
    for raw_key, raw_value in raw_items.items():
        key = str(raw_key).strip()
        if not key or not isinstance(raw_value, Mapping):
            continue
        if not source_record_schema4_to5_migration_item_current(
            key, raw_value, paper=paper, current_raw_audit=current_raw_audit
        ):
            continue
        out[key] = _LoadedSourceRecordSchema4To5MigrationItem(raw_value)
    return out
