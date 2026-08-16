#!/usr/bin/env python3
"""Deterministic integrity receipts for generated source-record audits.

The aggregate ``source_record_audit_sha256`` binds the generator's semantic
surface.  This module additionally binds the *serialized raw audit payload*
that later gates read.  Without that second receipt, a cache or a fast
evidence-only invocation could accept a hand-edited raw item merely because an
old aggregate digest still has the shape of a SHA-256 string.

This is deliberately a content-integrity check, not a signature scheme.  It
detects accidental or unreviewed mutation of a generated artifact while the
existing input fingerprint continues to establish that the artifact belongs to
the current repository inputs.
"""

from __future__ import annotations

import hashlib
import json
import re
from copy import deepcopy
from typing import Any, Mapping


SOURCE_RECORD_AUDIT_INTEGRITY_SCHEMA = 1
SOURCE_RECORD_AUDIT_INTEGRITY_DIGEST_FIELD = "source_record_audit_integrity_sha256"
SOURCE_RECORD_AUDIT_INTEGRITY_SCHEMA_FIELD = "source_record_audit_integrity_schema"
SOURCE_RECORD_AUDIT_SURFACE_SCHEMA = 1
SOURCE_RECORD_AUDIT_SURFACE_FIELD = "source_record_audit_surface"
SOURCE_RECORD_AUDIT_SURFACE_SCHEMA_FIELD = "source_record_audit_surface_schema"
SOURCE_RECORD_AUDIT_SURFACE_PROJECTION_FIELD = "raw_evidence_projection"
SHA256_RE = re.compile(r"^[0-9a-fA-F]{64}$")

# These sections are the generator-owned item surfaces whose narrow digests
# may be reused by a judgment sidecar.  Keep the list here rather than in each
# consumer: an item-level receipt is meaningful only under one shared
# eligibility contract, regardless of whether the consumer is the cache, the
# fast evidence gate, repository hygiene, or conclusion provenance.
SOURCE_RECORD_REUSABLE_ITEM_SECTIONS = (
    "boundary_input_items",
    "theorem_facing_input_items",
    "conclusion_dependency_items",
    "type_valued_certificate_result_items",
    "recursive_field_items",
    "semantic_model_items",
    "source_premise_consistency_items",
)
THEOREM_FACING_INPUT_MIRROR_REUSE_BLOCKER = (
    "canonical theorem-facing mirror of an existing reusable input"
)
SOURCE_RECORD_ITEM_REUSE_ELIGIBILITY_FIELD = "source_record_item_reuse_eligibility"
SOURCE_RECORD_ITEM_REUSE_METADATA_FIELDS = frozenset(
    {
        "source_record_item_digest_schema",
        "source_record_item_semantic_id",
        "source_record_item_context_sha256",
        "source_record_item_sha256",
        "source_record_item_semantic_context_requirements_sha256",
        "source_record_item_source_proof_fidelity_records_sha256",
    }
)

# These generator-owned routing errors make a raw receipt unsuitable for any
# current/rebound evidence.  Keep this small shared predicate outside the
# evidence gate so current revalidation and differential reuse reject the same
# malformed target selection without importing a higher-level audit module.
SOURCE_RECORD_TARGET_ROUTE_ERROR_FIELDS = (
    "semantic_model_scope_target_route_errors",
    "semantic_model_explicit_source_target_route_errors",
    "semantic_model_explicit_source_target_effective_row_errors",
    "semantic_model_explicit_source_target_generated_item_errors",
    "semantic_model_target_route_errors",
)


def source_record_target_route_error(payload: Mapping[str, Any]) -> str:
    """Return a current target-selection error recorded in a raw receipt."""

    for field in SOURCE_RECORD_TARGET_ROUTE_ERROR_FIELDS:
        value = payload.get(field)
        if value in (None, [], {}, ""):
            continue
        if isinstance(value, list):
            detail = "; ".join(str(error) for error in value[:3])
        else:
            detail = str(value)
        return f"generated `{field}` is nonempty: {detail}"
    return ""


def source_record_item_is_nonreusable_theorem_facing_mirror(
    section: object, item: object
) -> bool:
    """Return whether an item is a non-credit duplicate canonical input view.

    The canonical theorem-facing ledger is part of raw integrity and generic
    semantic closure, but a mirror of an existing reusable boundary/conclusion
    judgment must not alter that judgment's differential or migration group.
    Only this exact generated blocker receives that treatment; ordinary
    aggregate-only items remain visible to group builders and continue to
    prevent inappropriate item-level reuse.
    """

    if section != "theorem_facing_input_items" or not isinstance(item, Mapping):
        return False
    eligibility = item.get(SOURCE_RECORD_ITEM_REUSE_ELIGIBILITY_FIELD)
    if not isinstance(eligibility, Mapping) or eligibility.get("eligible") is not False:
        return False
    blockers = eligibility.get("blockers")
    return isinstance(blockers, list) and (
        THEOREM_FACING_INPUT_MIRROR_REUSE_BLOCKER in blockers
    )

# These are presentation/summary views derived after the evidence-producing
# scan. A ``--refresh-judgment-summary`` operation may update them, including
# re-rendering the judge prompt, without regenerating the Lean-checked raw
# surface, so they intentionally do not participate in the raw receipt.
_RAW_AUDIT_VOLATILE_TOP_LEVEL_FIELDS = frozenset(
    {
        SOURCE_RECORD_AUDIT_INTEGRITY_DIGEST_FIELD,
        "llm_judge_prompt",
        "current_source_record_judgment_count",
        "resolved_conclusion_dependency_count",
        "resolved_conclusion_dependency_items",
        "unresolved_conclusion_dependency_count",
        "unresolved_conclusion_dependency_items",
    }
)

# The aggregate semantic digest must be independently recomputable from the
# serialized evidence-bearing payload.  These are the only transport fields it
# omits: its own digest/surface receipts and post-scan presentation/summary
# fields that an explicit refresh is allowed to update without a Lean scan.
_RAW_EVIDENCE_PROJECTION_VOLATILE_TOP_LEVEL_FIELDS = frozenset(
    {
        "source_record_audit_sha256",
        SOURCE_RECORD_AUDIT_INTEGRITY_SCHEMA_FIELD,
        SOURCE_RECORD_AUDIT_INTEGRITY_DIGEST_FIELD,
        SOURCE_RECORD_AUDIT_SURFACE_SCHEMA_FIELD,
        SOURCE_RECORD_AUDIT_SURFACE_FIELD,
        "llm_judge_prompt",
        "current_source_record_judgment_count",
        "resolved_conclusion_dependency_count",
        "resolved_conclusion_dependency_items",
        "unresolved_conclusion_dependency_count",
        "unresolved_conclusion_dependency_items",
    }
)


def canonical_digest_payload(payload: object) -> object:
    """Return an order-insensitive JSON-safe digest representation.

    Source-record discovery traversals are not semantic order.  Sorting lists
    recursively makes the receipt stable across equivalent traversal order
    while retaining every serialized content field.
    """

    if isinstance(payload, Mapping):
        return {
            str(key): canonical_digest_payload(value)
            for key, value in sorted(payload.items(), key=lambda entry: str(entry[0]))
        }
    if isinstance(payload, list):
        canonical_items = [canonical_digest_payload(item) for item in payload]
        return sorted(
            canonical_items,
            key=lambda item: json.dumps(item, sort_keys=True, separators=(",", ":")),
        )
    if isinstance(payload, tuple):
        return canonical_digest_payload(list(payload))
    return payload


def source_record_audit_integrity_projection(
    payload: Mapping[str, Any],
) -> dict[str, Any]:
    """Return the complete raw audit surface excluding judgment-derived views."""

    return {
        str(key): value
        for key, value in payload.items()
        if str(key) not in _RAW_AUDIT_VOLATILE_TOP_LEVEL_FIELDS
    }


def source_record_raw_evidence_projection(
    payload: Mapping[str, Any],
) -> dict[str, Any]:
    """Return every serialized raw field that can affect evidence decisions.

    This projection is deliberately broader than the old in-memory audit
    object.  It includes the input fingerprint, generated items, route errors,
    elaboration results, and source context, so a downstream gate never trusts
    an unbound top-level mirror of the generator surface.
    """

    return {
        str(key): value
        for key, value in payload.items()
        if str(key) not in _RAW_EVIDENCE_PROJECTION_VOLATILE_TOP_LEVEL_FIELDS
    }


def source_record_audit_surface_sha256(surface: Mapping[str, Any]) -> str:
    """Match the generator's aggregate semantic digest convention exactly.

    Item-level digests are intentionally volatile inside the aggregate
    semantic surface: they are narrower reusable receipts, while this digest
    binds the full generated obligation graph and its raw-evidence projection.
    """

    def canonical_surface(value: object) -> object:
        if isinstance(value, Mapping):
            return {
                str(key): canonical_surface(child)
                for key, child in sorted(value.items(), key=lambda entry: str(entry[0]))
                if str(key) != "source_record_item_sha256"
            }
        if isinstance(value, list):
            items = [canonical_surface(item) for item in value]
            return sorted(
                items,
                key=lambda item: json.dumps(item, sort_keys=True, separators=(",", ":")),
            )
        if isinstance(value, tuple):
            return canonical_surface(list(value))
        return value

    encoded = json.dumps(
        canonical_surface(surface), sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def attach_source_record_audit_surface(
    payload: dict[str, Any],
    surface: dict[str, Any],
) -> str:
    """Bind a complete raw-evidence projection into a generator audit surface.

    The returned digest is the authoritative ``source_record_audit_sha256``.
    It is computed after all Lean-facing output has been assembled, but before
    the raw receipt is stamped.  Callers must not edit the payload afterward.
    """

    # Keep an independent snapshot.  A shallow projection would share nested
    # item objects with ``payload`` in memory, allowing a caller to mutate both
    # sides of the comparison before serializing either one.
    surface[SOURCE_RECORD_AUDIT_SURFACE_PROJECTION_FIELD] = deepcopy(
        source_record_raw_evidence_projection(payload)
    )
    aggregate_digest = source_record_audit_surface_sha256(surface)
    payload["source_record_audit_sha256"] = aggregate_digest
    payload[SOURCE_RECORD_AUDIT_SURFACE_SCHEMA_FIELD] = (
        SOURCE_RECORD_AUDIT_SURFACE_SCHEMA
    )
    payload[SOURCE_RECORD_AUDIT_SURFACE_FIELD] = surface
    return aggregate_digest


def stamp_source_record_audit_receipts(
    payload: dict[str, Any],
    surface: dict[str, Any] | None = None,
) -> str:
    """Attach both aggregate and raw receipts to a completed audit payload.

    ``surface`` carries generator-owned semantic material in addition to the
    complete raw-evidence snapshot.  Callers that have no additional semantic
    fields may use an empty surface; the raw-evidence projection still makes
    the aggregate digest independently recomputable.
    """

    aggregate_digest = attach_source_record_audit_surface(
        payload, {} if surface is None else surface
    )
    stamp_source_record_audit_integrity(payload)
    return aggregate_digest


def source_record_audit_surface_error(payload: object) -> str:
    """Return an aggregate semantic-surface integrity error, if any."""

    if not isinstance(payload, Mapping):
        return "source-record audit payload is not an object"
    if payload.get(SOURCE_RECORD_AUDIT_SURFACE_SCHEMA_FIELD) != (
        SOURCE_RECORD_AUDIT_SURFACE_SCHEMA
    ):
        return (
            "source-record audit lacks the current recomputable aggregate-surface "
            f"schema {SOURCE_RECORD_AUDIT_SURFACE_SCHEMA}"
        )
    surface = payload.get(SOURCE_RECORD_AUDIT_SURFACE_FIELD)
    if not isinstance(surface, Mapping):
        return "source-record audit aggregate surface is missing or malformed"
    recorded_projection = surface.get(SOURCE_RECORD_AUDIT_SURFACE_PROJECTION_FIELD)
    if not isinstance(recorded_projection, Mapping):
        return "source-record audit aggregate surface lacks its raw-evidence projection"
    # Older authenticated surfaces may retain fields that were subsequently
    # classified as presentation-only.  Apply today's explicit volatile-field
    # projection to both sides: this preserves those historical receipts while
    # still rejecting every unknown added, removed, or changed evidence field.
    normalized_recorded_projection = source_record_raw_evidence_projection(
        recorded_projection
    )
    if canonical_digest_payload(
        normalized_recorded_projection
    ) != canonical_digest_payload(source_record_raw_evidence_projection(payload)):
        return (
            "source-record audit aggregate surface does not match its serialized "
            "raw-evidence projection"
        )
    recorded_digest = str(payload.get("source_record_audit_sha256") or "").strip()
    if not SHA256_RE.fullmatch(recorded_digest):
        return "source_record_audit_sha256 is missing or malformed"
    expected_digest = source_record_audit_surface_sha256(surface)
    if recorded_digest.lower() != expected_digest:
        return (
            "source_record_audit_sha256 does not match the recomputable generated "
            "aggregate surface"
        )
    return ""


def source_record_audit_receipt_error(payload: object) -> str:
    """Validate both the aggregate semantic surface and raw serialization receipt."""

    surface_error = source_record_audit_surface_error(payload)
    if surface_error:
        return surface_error
    return source_record_audit_integrity_error(payload)


def source_record_audit_integrity_sha256(payload: Mapping[str, Any]) -> str:
    """Hash the current raw source-record surface deterministically."""

    encoded = json.dumps(
        canonical_digest_payload(source_record_audit_integrity_projection(payload)),
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _source_record_legacy_prompt_integrity_sha256(
    payload: Mapping[str, Any],
) -> str:
    """Recompute the pre-prompt-refresh raw receipt exactly.

    Before prompt rendering was classified as presentation-only, the raw
    integrity receipt authenticated ``llm_judge_prompt`` as well.  That older
    projection is strictly broader than the current one, so accepting its
    exact digest cannot hide evidence drift; it only keeps an immutable older
    receipt readable after prompt text became refreshable.
    """

    projection = dict(source_record_audit_integrity_projection(payload))
    if "llm_judge_prompt" in payload:
        projection["llm_judge_prompt"] = payload["llm_judge_prompt"]
    encoded = json.dumps(
        canonical_digest_payload(projection),
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def stamp_source_record_audit_integrity(payload: dict[str, Any]) -> None:
    """Attach the current schema and receipt after a full raw audit is built."""

    payload[SOURCE_RECORD_AUDIT_INTEGRITY_SCHEMA_FIELD] = (
        SOURCE_RECORD_AUDIT_INTEGRITY_SCHEMA
    )
    payload[SOURCE_RECORD_AUDIT_INTEGRITY_DIGEST_FIELD] = (
        source_record_audit_integrity_sha256(payload)
    )


def source_record_audit_integrity_error(payload: object) -> str:
    """Return a fail-closed raw-audit receipt error, if any."""

    if not isinstance(payload, Mapping):
        return "source-record audit payload is not an object"
    if payload.get(SOURCE_RECORD_AUDIT_INTEGRITY_SCHEMA_FIELD) != (
        SOURCE_RECORD_AUDIT_INTEGRITY_SCHEMA
    ):
        return (
            "source-record audit lacks the current raw-integrity schema "
            f"{SOURCE_RECORD_AUDIT_INTEGRITY_SCHEMA}"
        )
    recorded = str(
        payload.get(SOURCE_RECORD_AUDIT_INTEGRITY_DIGEST_FIELD) or ""
    ).strip().lower()
    if not SHA256_RE.fullmatch(recorded):
        return "source-record audit raw-integrity digest is missing or malformed"
    expected = source_record_audit_integrity_sha256(payload)
    if recorded != expected and recorded != (
        _source_record_legacy_prompt_integrity_sha256(payload)
    ):
        return "source-record audit raw-integrity digest does not match its serialized surface"
    return ""


def elaborated_review_signature_identities_error(item: Mapping[str, Any]) -> str:
    """Validate optional generated exact Lean-route identity metadata.

    A route identity may be present on an aggregate-only item so downstream
    audits can project a current semantic review surface by FQN, source bytes,
    and elaborated signature.  It is not a reusable source-record item digest:
    callers must still require an explicit ``eligible: true`` declaration
    before accepting narrow sidecar freshness.
    """

    signatures = item.get("reviewed_elaborated_signature_identities")
    if signatures is None:
        return ""
    if not isinstance(signatures, list) or not signatures:
        return "has malformed exact elaborated review-route signature identities"
    identities: set[tuple[str, str]] = set()
    for signature in signatures:
        if not isinstance(signature, Mapping):
            return "has a non-object elaborated review-route signature identity"
        declaration = str(signature.get("qualified_declaration") or "").strip()
        digest = str(signature.get("elaborated_signature_sha256") or "").strip()
        if not declaration or "." not in declaration:
            return "has an incomplete elaborated review-route declaration identity"
        if not SHA256_RE.fullmatch(digest):
            return "has an elaborated review-route signature without a SHA-256 digest"
        identity = (declaration, digest.lower())
        if identity in identities:
            return "has duplicate elaborated review-route signature identities"
        identities.add(identity)
    return ""


def reusable_item_metadata_error(
    item: object,
    *,
    expected_item_digest_schema: int,
) -> str:
    """Validate identity material for a raw item that claims narrow reuse.

    Aggregate-only items are intentionally allowed: they explicitly carry an
    ineligible reuse declaration and are covered by the complete raw receipt.
    A reusable item, by contrast, must show its source-independent semantic
    identity, scoped context identity, and exact elaborated Lean-route
    signatures.  Aggregate-only items may retain a well-formed exact Lean-route
    signature for semantic-surface projection, but it never enables item-level
    judgment reuse. These values are generated metadata, never reviewer input.
    """

    if not isinstance(item, Mapping):
        return "is not an object"
    eligibility = item.get(SOURCE_RECORD_ITEM_REUSE_ELIGIBILITY_FIELD)
    if not isinstance(eligibility, Mapping):
        # A raw item with *any* generated item receipt must state whether it is
        # reusable.  Otherwise a legacy-looking digest could be consumed as a
        # narrow freshness proof even though no generator has established the
        # source/context/signature prerequisites for it.
        generated_metadata = [
            str(field)
            for field in item
            if str(field).startswith("source_record_item_")
            or str(field) == "reviewed_elaborated_signature_identities"
        ]
        if generated_metadata:
            return "has generated item metadata but no reuse-eligibility declaration"
        return ""
    eligible = eligibility.get("eligible")
    blockers = eligibility.get("blockers")
    if not isinstance(eligible, bool) or not isinstance(blockers, list) or any(
        not isinstance(blocker, str) or not blocker.strip() for blocker in blockers
    ):
        return "has malformed generated reuse-eligibility metadata"
    if not eligible:
        if not blockers:
            return "claims aggregate-only freshness without an item-reuse blocker"
        signature_error = elaborated_review_signature_identities_error(item)
        if signature_error:
            return signature_error
        # Aggregate-only items are covered by the full raw-audit receipt.  They
        # must not retain a scalar item-digest receipt that another consumer
        # could mistake for independently reusable evidence. A validated exact
        # Lean-route signature is deliberately allowed above: it identifies a
        # generated declaration but cannot satisfy any narrow-reuse predicate.
        # Check every source_record_item_* transport field, not merely today's
        # known digest fields, so future generator metadata fails closed by
        # default.
        retained_metadata = [
            str(field)
            for field in item
            if (
                str(field).startswith("source_record_item_")
                and str(field) != SOURCE_RECORD_ITEM_REUSE_ELIGIBILITY_FIELD
            )
        ]
        if retained_metadata:
            return (
                "claims aggregate-only freshness while retaining item-level "
                "metadata: "
                + ", ".join(sorted(retained_metadata))
            )
        return ""
    if blockers:
        return "claims reusable item freshness while listing reuse blockers"
    if item.get("source_record_item_digest_schema") != expected_item_digest_schema:
        return "claims reusable item freshness without the current item-digest schema"
    for field in (
        "source_record_item_semantic_id",
        "source_record_item_context_sha256",
        "source_record_item_sha256",
    ):
        if not SHA256_RE.fullmatch(str(item.get(field) or "").strip()):
            return f"claims reusable item freshness without a SHA-256 `{field}`"
    signature_error = elaborated_review_signature_identities_error(item)
    if signature_error:
        return signature_error
    signatures = item.get("reviewed_elaborated_signature_identities")
    if not isinstance(signatures, list) or not signatures:  # defensive narrowing
        return (
            "claims reusable item freshness without exact elaborated review-route "
            "signature identities"
        )
    return ""


def source_record_item_reuse_eligible(
    item: object,
    *,
    expected_item_digest_schema: int,
) -> bool:
    """Return whether an item may supply a narrow reusable digest.

    This deliberately requires an explicit generated ``eligible: true``
    declaration.  Missing metadata, an aggregate-only declaration, and a
    malformed reusable declaration all fall back to the full aggregate audit
    receipt; none can be treated as item-local freshness by a downstream
    collector.
    """

    if not isinstance(item, Mapping):
        return False
    eligibility = item.get(SOURCE_RECORD_ITEM_REUSE_ELIGIBILITY_FIELD)
    return bool(
        isinstance(eligibility, Mapping)
        and eligibility.get("eligible") is True
        and not reusable_item_metadata_error(
            item,
            expected_item_digest_schema=expected_item_digest_schema,
        )
    )


def source_record_raw_reusable_item_metadata_error(
    payload: object,
    *,
    expected_item_digest_schema: int,
) -> str:
    """Validate all generated raw item metadata before cache or gate reuse.

    A payload can be receipt-valid yet still contain a malformed
    aggregate-only item if an actor restamps every affected receipt.  This
    structural check rejects that state before any cache reuses the artifact.
    It does not require every optional section to be present so it remains a
    narrow validator of the item-reuse contract rather than a version parser.
    """

    if not isinstance(payload, Mapping):
        return "source-record audit payload is not an object"
    for section in SOURCE_RECORD_REUSABLE_ITEM_SECTIONS:
        raw_items = payload.get(section)
        if raw_items is None:
            continue
        if not isinstance(raw_items, list):
            return f"generated `{section}` is not a list"
        for index, item in enumerate(raw_items):
            item_error = reusable_item_metadata_error(
                item,
                expected_item_digest_schema=expected_item_digest_schema,
            )
            if item_error:
                return f"generated `{section}[{index}]` {item_error}"
    return ""
