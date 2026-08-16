#!/usr/bin/env python3
"""Validate explicit semantic compatibility for raw-producer provenance.

The source-record fingerprint keeps exact producer code identities for forensic
provenance and for a fail-closed implementation-change acknowledgement.  Those
identities are not themselves the semantic audit surface: a registered engine
transition may change implementation while leaving every non-producer input
and every active, feature-scoped producer contract unchanged.

This module admits that narrow reuse only through append-only grants in the
formalization-engine ledger.  It never discovers compatibility from a paper
name, Lean declaration, function name, or a coincidental code hash.
"""

from __future__ import annotations

import copy
import re
from typing import Any, Mapping


RAW_PRODUCER_COMPATIBILITY_SCHEMA = 1
RAW_PRODUCER_COMPATIBILITY_INVARIANT = (
    "same-nonproducer-source-record-fingerprint-v1"
)
RAW_PRODUCER_IDENTITY_SCHEMA = 1
RAW_PRODUCER_IDENTITY_FIELDS = frozenset({"path", "sha256", "status"})
RAW_PRODUCER_FINGERPRINT_FIELDS = frozenset(
    {"raw_producer_code_identity_schema", "raw_producer_code_identities"}
)
RAW_PRODUCER_COMPATIBILITY_FIELD = "raw_producer_compatibility"
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")


def _identity_set(
    value: object,
    *,
    field: str,
) -> tuple[tuple[str, str, str], ...] | None:
    """Normalize one complete producer-provenance identity set."""

    if not isinstance(value, list) or not value:
        return None
    records: list[tuple[str, str, str]] = []
    paths: set[str] = set()
    for index, raw_identity in enumerate(value):
        if not isinstance(raw_identity, Mapping) or set(raw_identity) != RAW_PRODUCER_IDENTITY_FIELDS:
            return None
        path = raw_identity.get("path")
        sha256 = raw_identity.get("sha256")
        status = raw_identity.get("status")
        if (
            not isinstance(path, str)
            or not path.strip()
            or not isinstance(sha256, str)
            or not SHA256_RE.fullmatch(sha256.strip().lower())
            or status != "present"
        ):
            return None
        normalized_path = path.strip()
        if normalized_path in paths:
            return None
        paths.add(normalized_path)
        records.append((normalized_path, sha256.strip().lower(), "present"))
    return tuple(sorted(records))


def raw_producer_identity_set(value: object) -> tuple[tuple[str, str, str], ...] | None:
    """Return a validated normalized producer identity set, if complete."""

    return _identity_set(value, field="raw producer identities")


def fingerprint_without_raw_producer_provenance(
    value: object,
) -> dict[str, Any] | None:
    """Project a schema-10 fingerprint onto semantic non-producer inputs.

    A complete producer provenance field is required before this projection can
    authorize a compatibility grant.  Older schemas retain their separate
    migration paths and cannot enter this mechanism.
    """

    if not isinstance(value, Mapping) or value.get("schema") != 10:
        return None
    if value.get("raw_producer_code_identity_schema") != RAW_PRODUCER_IDENTITY_SCHEMA:
        return None
    if raw_producer_identity_set(value.get("raw_producer_code_identities")) is None:
        return None
    projection = copy.deepcopy(dict(value))
    for field in RAW_PRODUCER_FINGERPRINT_FIELDS:
        projection.pop(field, None)
    return projection


def raw_producer_compatibility_grant_error(value: object) -> str:
    """Return a structural error for one append-only compatibility grant."""

    if not isinstance(value, Mapping):
        return "raw-producer compatibility grant is not an object"
    expected_fields = {
        "schema",
        "invariant",
        "predecessor_raw_producer_code_identity_sets",
        "successor_raw_producer_code_identities",
    }
    if set(value) != expected_fields:
        return "raw-producer compatibility grant fields are malformed"
    if value.get("schema") != RAW_PRODUCER_COMPATIBILITY_SCHEMA:
        return "raw-producer compatibility grant has an unsupported schema"
    if value.get("invariant") != RAW_PRODUCER_COMPATIBILITY_INVARIANT:
        return "raw-producer compatibility grant has an unsupported invariant"
    predecessors = value.get("predecessor_raw_producer_code_identity_sets")
    if not isinstance(predecessors, list) or not predecessors:
        return "raw-producer compatibility grant has no predecessor identity sets"
    normalized_predecessors: set[tuple[tuple[str, str, str], ...]] = set()
    for index, predecessor in enumerate(predecessors):
        normalized = _identity_set(
            predecessor,
            field=f"raw-producer compatibility predecessor[{index}]",
        )
        if normalized is None:
            return (
                "raw-producer compatibility grant has a malformed predecessor "
                f"identity set at index {index}"
            )
        if normalized in normalized_predecessors:
            return "raw-producer compatibility grant repeats a predecessor identity set"
        normalized_predecessors.add(normalized)
    successor = _identity_set(
        value.get("successor_raw_producer_code_identities"),
        field="raw-producer compatibility successor",
    )
    if successor is None:
        return "raw-producer compatibility grant has a malformed successor identity set"
    if successor in normalized_predecessors:
        return "raw-producer compatibility successor duplicates a predecessor"
    return ""


def raw_producer_compatibility_grants_from_ledger(
    ledger: object,
) -> tuple[
    dict[tuple[tuple[str, str, str], ...], set[tuple[tuple[str, str, str], ...]]],
    tuple[tuple[str, str, str], ...] | None,
    str,
]:
    """Return the explicit provenance graph and current endpoint from a ledger.

    Each edge is permitted only on a `review_compatible` revision.  The latest
    grant is the current raw-producer implementation attestation; if there is
    no such grant, exact raw code identity remains the only accepted route.
    """

    if not isinstance(ledger, Mapping):
        return {}, None, "formalization-engine ledger is not an object"
    revisions = ledger.get("revisions")
    if not isinstance(revisions, list):
        return {}, None, "formalization-engine ledger has no revision list"
    graph: dict[
        tuple[tuple[str, str, str], ...], set[tuple[tuple[str, str, str], ...]]
    ] = {}
    current_endpoint: tuple[tuple[str, str, str], ...] | None = None
    for index, raw_revision in enumerate(revisions, start=1):
        if not isinstance(raw_revision, Mapping):
            return {}, None, f"formalization-engine revision {index} is malformed"
        # A review-semantic transition starts a new provenance era. A later
        # implementation grant may not transitively carry a raw receipt across
        # a changed canonical review protocol, even if an incidental
        # non-producer projection happened to coincide.
        if raw_revision.get("relation_to_previous") == "review_semantics_changed":
            graph = {}
            current_endpoint = None
        grant = raw_revision.get(RAW_PRODUCER_COMPATIBILITY_FIELD)
        if grant is None:
            continue
        if raw_revision.get("relation_to_previous") != "review_compatible":
            return {}, None, (
                "raw-producer compatibility grant appears on a non-compatible "
                f"engine revision {index}"
            )
        error = raw_producer_compatibility_grant_error(grant)
        if error:
            return {}, None, f"engine revision {index}: {error}"
        assert isinstance(grant, Mapping)
        successor = _identity_set(
            grant.get("successor_raw_producer_code_identities"),
            field="raw-producer compatibility successor",
        )
        assert successor is not None
        predecessors = grant.get("predecessor_raw_producer_code_identity_sets")
        assert isinstance(predecessors, list)
        for predecessor in predecessors:
            normalized = _identity_set(
                predecessor,
                field="raw-producer compatibility predecessor",
            )
            assert normalized is not None
            graph.setdefault(normalized, set()).add(successor)
        current_endpoint = successor
    return graph, current_endpoint, ""


def source_record_fingerprint_matches_with_raw_producer_compatibility(
    stored: object,
    current: object,
    *,
    ledger: object,
) -> bool:
    """Return exact or explicitly granted semantic fingerprint compatibility.

    Compatibility never projects away a map/source/Lean/toolchain/feature
    difference.  It removes only the two producer-provenance fields after both
    sides validate, then requires an explicit chain from the stored exact code
    identity to the current ledger-attested implementation identity.
    """

    if (
        isinstance(stored, Mapping)
        and isinstance(current, Mapping)
        and dict(stored) == dict(current)
    ):
        return True
    stored_projection = fingerprint_without_raw_producer_provenance(stored)
    current_projection = fingerprint_without_raw_producer_provenance(current)
    if stored_projection is None or current_projection is None:
        return False
    stored_identities = raw_producer_identity_set(
        stored.get("raw_producer_code_identities")
    )
    current_identities = raw_producer_identity_set(
        current.get("raw_producer_code_identities")
    )
    assert stored_identities is not None and current_identities is not None
    graph, current_endpoint, ledger_error = raw_producer_compatibility_grants_from_ledger(
        ledger
    )
    if ledger_error:
        return False
    # A ledger with grants must attest the actual current producer identity.
    # Otherwise an implementation edit cannot inherit an older grant.
    if current_endpoint is not None and current_identities != current_endpoint:
        return False
    if stored_projection != current_projection:
        return False
    if stored_identities == current_identities:
        return True
    if current_endpoint is None:
        return False
    pending = [stored_identities]
    seen: set[tuple[tuple[str, str, str], ...]] = set()
    while pending:
        identity_set = pending.pop()
        if identity_set in seen:
            continue
        seen.add(identity_set)
        for successor in graph.get(identity_set, set()):
            if successor == current_identities:
                return True
            pending.append(successor)
    return False
