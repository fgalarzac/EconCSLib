#!/usr/bin/env python3
"""Decide whether a closeout needs the optional v11 realization lane.

One centrally pinned Git tree identifies papers that already received a
completed legacy-v10 closeout.  A paper absent from that tree is new and must
complete v11.  A material repair of a legacy paper instead receives current,
item-level v10 evidence; requiring a synthetic atom-to-Spec migration merely
because the repair changed a theorem route duplicates that review without
making the v10 judgment stronger.  Explicit v11 switches in the current status
or source map still take precedence at the caller.

This module intentionally reads already-generated closeout artifacts.  It does
not run Lean and does not make a semantic judgment.  The ordinary closeout
gates remain responsible for proving that current v10 artifacts are valid.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
from dataclasses import dataclass
from functools import lru_cache
from pathlib import Path
from typing import Any, Callable, Mapping

try:
    from formalization_protocol import (
        IMMUTABLE_MATERIAL_IDENTITY_MANIFEST_AUTHORITY,
        IMMUTABLE_V10_MATERIAL_IDENTITY_SCHEMA,
        TRUSTED_GIT_TREE_AUTHORITY,
        formalization_review_protocol_digest,
        load_formalization_protocol,
    )
    from source_coverage_scope import (
        NAMED_THEORETICAL_SOURCE_KINDS,
        THEOREM_REALIZATION_NONCLAIM_STATUSES,
        THEOREM_REALIZATION_SOURCE_KINDS,
        filter_source_map_items_for_coverage,
        filter_source_map_items_for_proof_obligations,
        source_item_has_explicit_corrected_obligation,
        source_coverage_mode_from_map,
        source_item_coverage_sha256,
        source_named_result_environment_kinds_from_map,
    )
except ModuleNotFoundError:  # pragma: no cover - module-style imports.
    from scripts.formalization_protocol import (
        IMMUTABLE_MATERIAL_IDENTITY_MANIFEST_AUTHORITY,
        IMMUTABLE_V10_MATERIAL_IDENTITY_SCHEMA,
        TRUSTED_GIT_TREE_AUTHORITY,
        formalization_review_protocol_digest,
        load_formalization_protocol,
    )
    from scripts.source_coverage_scope import (
        NAMED_THEORETICAL_SOURCE_KINDS,
        THEOREM_REALIZATION_NONCLAIM_STATUSES,
        THEOREM_REALIZATION_SOURCE_KINDS,
        filter_source_map_items_for_coverage,
        filter_source_map_items_for_proof_obligations,
        source_item_has_explicit_corrected_obligation,
        source_coverage_mode_from_map,
        source_item_coverage_sha256,
        source_named_result_environment_kinds_from_map,
    )


MATERIAL_IDENTITY_SCHEMA = 1
PORTABLE_MATERIAL_IDENTITY_SCHEMA = IMMUTABLE_V10_MATERIAL_IDENTITY_SCHEMA
SUPPORTED_MATERIAL_IDENTITY_SCHEMAS = frozenset(
    {MATERIAL_IDENTITY_SCHEMA, PORTABLE_MATERIAL_IDENTITY_SCHEMA}
)
CLOSEOUT_STATUSES = frozenset({"formalized", "formalized with caveat"})
SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)

STATUS_PATH = "status.json"
STATEMENT_MAP_PATH = "audit/paper_statement_map.json"
STATEMENT_REVIEW_PATH = "audit/statement_match_llm.json"
SOURCE_RECORD_PATH = "audit/source_record_audit.json"
SOURCE_PROOF_FIDELITY_PATH = "audit/source_proof_fidelity.json"
MATERIAL_ARTIFACT_PATHS = (
    STATUS_PATH,
    STATEMENT_MAP_PATH,
    STATEMENT_REVIEW_PATH,
    SOURCE_RECORD_PATH,
    SOURCE_PROOF_FIDELITY_PATH,
)


@dataclass(frozen=True)
class TheoremRealizationReissueRequirement:
    required: bool
    reason: str
    current_material_identity_sha256: str = ""
    baseline_material_identity_sha256: str = ""


@dataclass(frozen=True)
class MaterialCloseoutIdentityRecord:
    """Name-independent identity and compact inspectable component receipts."""

    schema: int
    lookup_identity_sha256: str
    material_identity_sha256: str
    component_sha256s: Mapping[str, str]


GitBlobReader = Callable[[str, str], bytes | None]
BaselineAncestorVerifier = Callable[[str, str], bool]


def _stable_digest(value: object) -> str:
    encoded = json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
        default=str,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _digest(value: object) -> str:
    text = str(value or "").strip().lower()
    return text if SHA256_RE.fullmatch(text) else ""


def _json_object(raw: bytes | None) -> dict[str, Any] | None:
    if raw is None:
        return None
    try:
        value = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError):
        return None
    return value if isinstance(value, dict) else None


def _current_artifacts(folder: Path) -> dict[str, bytes | None]:
    artifacts: dict[str, bytes | None] = {}
    for relative in MATERIAL_ARTIFACT_PATHS:
        try:
            artifacts[relative] = (folder / relative).read_bytes()
        except OSError:
            artifacts[relative] = None
    return artifacts


@lru_cache(maxsize=1024)
def _trusted_git_blob(root: str, commit: str, object_path: str) -> bytes | None:
    """Read one immutable baseline blob once per process."""

    try:
        result = subprocess.run(
            ["git", "-C", root, "show", f"{commit}:{object_path}"],
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
            env={**os.environ, "GIT_NO_REPLACE_OBJECTS": "1"},
            check=False,
            timeout=10,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    return result.stdout if result.returncode == 0 else None


def _git_blob_reader(root: Path, paper_relative: str) -> GitBlobReader:
    def read(commit: str, relative: str) -> bytes | None:
        return _trusted_git_blob(
            str(root), commit, f"papers/{paper_relative}/{relative}"
        )

    return read


@lru_cache(maxsize=16)
def _trusted_baseline_is_ancestor(
    root: str, commit: str, trusted_ref: str
) -> bool:
    """Require the pinned tree to belong to the trusted private main line."""

    try:
        result = subprocess.run(
            [
                "git",
                "-C",
                root,
                "merge-base",
                "--is-ancestor",
                commit,
                trusted_ref,
            ],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            env={**os.environ, "GIT_NO_REPLACE_OBJECTS": "1"},
            check=False,
            timeout=10,
        )
    except (OSError, subprocess.SubprocessError):
        return False
    return result.returncode == 0


def _selected_source_item_digests(
    statement_map: Mapping[str, Any],
    source_proof_fidelity: Mapping[str, Any] | None,
    *,
    resolver: _LedgerSemanticResolver | None = None,
) -> tuple[list[str] | None, str]:
    mode, mode_error = source_coverage_mode_from_map(dict(statement_map))
    if mode_error:
        return None, mode_error
    raw_items = statement_map.get("items")
    if not isinstance(raw_items, dict):
        return None, "paper statement map has no items object"
    selected = filter_source_map_items_for_coverage(
        raw_items,
        mode,
        declared_environment_kinds=source_named_result_environment_kinds_from_map(
            statement_map
        ),
    )
    # Some established v10 inventories predate the explicit normal/deep mode
    # selector.  They remain a trusted baseline only by retaining every source
    # item, never by treating an empty selection as evidence.  A current map
    # that adds/removes/changes one of those items therefore still reissues.
    if not selected:
        selected = {
            str(key): value
            for key, value in raw_items.items()
            if isinstance(value, dict)
        }
    digests: list[str] = []
    resolver = resolver or _LedgerSemanticResolver(source_proof_fidelity)
    for item in selected.values():
        projected, projection_error = _source_item_transition_projection(
            item, resolver
        )
        if projection_error:
            return None, projection_error
        digest = source_item_coverage_sha256(
            projected, mode
        )
        if not _digest(digest):
            return None, "selected source item has no semantic content digest"
        digests.append(digest.lower())
    if not digests:
        return None, "paper statement map selects no named-theory source items"
    # Map keys and source/Lean declaration names are navigation only.  Keep a
    # sorted multiset so duplicate source presentations remain visible.
    return sorted(digests), ""


def _statement_review_identity(
    statement_review: Mapping[str, Any],
) -> tuple[list[dict[str, str]] | None, str]:
    raw_items = statement_review.get("items")
    if not isinstance(raw_items, dict) or not raw_items:
        return None, "statement review has no item judgments"
    identities: list[dict[str, str]] = []
    for raw_item in raw_items.values():
        if not isinstance(raw_item, Mapping):
            return None, "statement review contains a malformed item judgment"
        signature = _digest(raw_item.get("lean_signature_sha256"))
        paper_statement = _digest(raw_item.get("paper_statement_sha256"))
        if not signature or not paper_statement:
            return None, "statement review item lacks a semantic statement identity"
        identities.append(
            {
                "lean_signature_sha256": signature,
                "paper_statement_sha256": paper_statement,
            }
        )
    return sorted(
        identities,
        key=lambda value: (
            value["paper_statement_sha256"],
            value["lean_signature_sha256"],
        ),
    ), ""


def _theorem_realization_source_item_identities(
    statement_map: Mapping[str, Any],
    source_proof_fidelity: Mapping[str, Any] | None,
    *,
    resolver: _LedgerSemanticResolver,
) -> tuple[dict[str, str] | None, str]:
    """Return source-first v11 items keyed only for route lookup.

    The returned keys are never hashed.  They only join a source map to the
    reviewer-authored source-route cards below.  Definitions and model
    vocabulary remain ordinary audit obligations, but do not acquire an
    artificial theorem-realization requirement merely because they have a
    paper-facing Lean wrapper.
    """

    mode, mode_error = source_coverage_mode_from_map(dict(statement_map))
    if mode_error:
        return None, mode_error
    raw_items = statement_map.get("items")
    if not isinstance(raw_items, dict):
        return None, "paper statement map has no items object"
    selected = filter_source_map_items_for_proof_obligations(
        raw_items,
        mode,
        declared_environment_kinds=source_named_result_environment_kinds_from_map(
            statement_map
        ),
    )
    identities: dict[str, str] = {}
    for raw_key, item in selected.items():
        source_kind = str(item.get("source_kind") or "").strip().lower()
        source_status = str(item.get("source_status") or "").strip().lower()
        corrected = source_item_has_explicit_corrected_obligation(item)
        if (
            source_status in THEOREM_REALIZATION_NONCLAIM_STATUSES
            and not corrected
        ):
            continue
        if not corrected and source_kind not in THEOREM_REALIZATION_SOURCE_KINDS:
            # Unknown claim-bearing categories remain an ordinary source-map
            # validation error.  Known definitions, assumptions, and models
            # are intentionally not theorem-Spec obligations.
            if (
                item.get("claim_bearing") is True
                and source_kind not in NAMED_THEORETICAL_SOURCE_KINDS
            ):
                return None, (
                    "selected claim-bearing source item has no recognized "
                    "presentation kind for theorem-realization scope"
                )
            continue
        projected, projection_error = _source_item_transition_projection(
            item, resolver
        )
        if projection_error:
            return None, projection_error
        digest = source_item_coverage_sha256(projected, mode)
        if not _digest(digest):
            return None, "theorem-realization source item has no semantic digest"
        identities[str(raw_key)] = digest.lower()
    return identities, ""


def _theorem_realization_route_cards(
    statement_review: Mapping[str, Any],
    source_item_identities: Mapping[str, str],
) -> tuple[list[dict[str, str]] | None, bool, str]:
    """Return route-bound theorem identities when every source item is covered.

    Source-map keys and review-item names are navigation only.  A route card
    retains their semantic endpoints, including the review's relation label,
    so a cross-item route swap cannot preserve the transition identity.
    """

    if not source_item_identities:
        return [], True, ""
    raw_items = statement_review.get("items")
    if not isinstance(raw_items, dict) or not raw_items:
        return None, False, "statement review has no item judgments"
    cards: list[dict[str, str]] = []
    covered: set[str] = set()
    for raw_item in raw_items.values():
        if not isinstance(raw_item, Mapping):
            return None, False, "statement review contains a malformed item judgment"
        paper_statement = _digest(raw_item.get("paper_statement_sha256"))
        lean_signature = _digest(raw_item.get("lean_signature_sha256"))
        raw_routes = raw_item.get("source_routes")
        if not isinstance(raw_routes, list):
            continue
        for raw_route in raw_routes:
            if not isinstance(raw_route, Mapping):
                continue
            source_item = str(raw_route.get("source_item") or "").strip()
            source_digest = source_item_identities.get(source_item)
            if not source_digest:
                continue
            source_statement = _digest(raw_route.get("source_statement_sha256"))
            semantic_relation = str(
                raw_route.get("semantic_relation") or ""
            ).strip()
            if not (
                source_statement
                and paper_statement
                and lean_signature
                and semantic_relation
            ):
                continue
            covered.add(source_item)
            cards.append(
                {
                    "source_item_semantic_sha256": source_digest,
                    "source_statement_sha256": source_statement,
                    "paper_statement_sha256": paper_statement,
                    "lean_signature_sha256": lean_signature,
                    "semantic_relation": semantic_relation,
                }
            )
    if set(source_item_identities) - covered:
        return [], False, ""
    # Duplicate generated/review cards are administrative.  Source-presentation
    # multiplicity remains in the separately retained source-item digest bag.
    unique_cards = {
        _stable_digest(card): card
        for card in cards
    }
    return sorted(unique_cards.values(), key=_stable_digest), True, ""


def _theorem_realization_transition_components(
    artifacts: Mapping[str, bytes | None],
) -> tuple[dict[str, object] | None, str]:
    """Project only semantics that determine an automatic v11 reissue.

    This deliberately omits the broad generated raw source-record identity.
    Raw receipt currentness remains a mandatory ordinary evidence gate; it is
    not itself proof that a paper theorem's source-to-Lean realization changed.
    """

    status = _json_object(artifacts.get(STATUS_PATH))
    statement_map = _json_object(artifacts.get(STATEMENT_MAP_PATH))
    statement_review = _json_object(artifacts.get(STATEMENT_REVIEW_PATH))
    source_record = _json_object(artifacts.get(SOURCE_RECORD_PATH))
    source_proof_fidelity = _json_object(
        artifacts.get(SOURCE_PROOF_FIDELITY_PATH)
    )
    if status is None:
        return None, "status.json is missing or malformed"
    if statement_map is None:
        return None, "paper statement map is missing or malformed"
    if statement_review is None:
        return None, "statement review is missing or malformed"
    if source_record is None:
        return None, "source record is missing or malformed"

    semantic_ledger: dict[str, Any] = dict(source_proof_fidelity or {})
    raw_corrections = status.get("governing_corrections")
    correction_references: dict[str, tuple[str, bool]] = {}
    if isinstance(raw_corrections, list) and raw_corrections:
        semantic_ledger["governing_corrections"] = raw_corrections
        correction_references = {
            "correction_id": ("governing_corrections", False),
            "correction_ids": ("governing_corrections", True),
        }
    ledger_resolver = _LedgerSemanticResolver(
        semantic_ledger,
        reference_fields=correction_references,
    )
    source_items, error = _theorem_realization_source_item_identities(
        statement_map,
        source_proof_fidelity,
        resolver=ledger_resolver,
    )
    if source_items is None:
        return None, error
    statements, error = _statement_review_identity(statement_review)
    if statements is None:
        return None, error
    route_cards, route_complete, error = _theorem_realization_route_cards(
        statement_review, source_items
    )
    if route_cards is None:
        return None, error
    formalization_scope, error = _formalization_scope_identity(
        status, source_record, ledger_resolver
    )
    if error:
        return None, error
    governing_corrections, error = _governing_corrections_identity(
        status, ledger_resolver
    )
    if governing_corrections is None:
        return None, error
    return {
        "theorem_source_item_semantic_sha256s": sorted(source_items.values()),
        "full_statement_semantic_identities": statements,
        "route_statement_cards": route_cards,
        "route_statement_cards_complete": route_complete,
        "formalization_scope_semantic_identity": formalization_scope,
        "governing_correction_semantic_sha256s": governing_corrections,
    }, ""


def _theorem_realization_transition_identity(
    components: Mapping[str, object],
    *,
    use_route_cards: bool,
) -> str:
    """Hash one narrow v11-transition surface without navigation names."""

    statement_identity: object
    if use_route_cards:
        statement_identity = {
            "mode": "complete_source_route_cards",
            "cards": components["route_statement_cards"],
        }
    else:
        statement_identity = {
            "mode": "conservative_full_statement_review",
            "identities": components["full_statement_semantic_identities"],
        }
    return _stable_digest(
        {
            "schema": 1,
            "theorem_source_item_semantic_sha256s": components[
                "theorem_source_item_semantic_sha256s"
            ],
            "statement_realization_identity": statement_identity,
            "formalization_scope_semantic_identity": components[
                "formalization_scope_semantic_identity"
            ],
            "governing_correction_semantic_sha256s": components[
                "governing_correction_semantic_sha256s"
            ],
        }
    )


_SOURCE_IDENTITY_FIELDS = frozenset(
    {
        "source_semantic_sha256",
        "source_claim_atom_semantic_sha256",
        "source_claim_component_sha256",
    }
)
_ELABORATED_STATEMENT_IDENTITY_FIELDS = frozenset(
    {
        "elaborated_signature_sha256",
        "semantic_dependency_sha256",
    }
)
_SEMANTIC_SURFACE_FIELDS = frozenset(
    {
        "alpha_normalized_type",
        "binder_domains",
        "binder_type",
        "body_sha256",
        "expanded_lean_surface",
        "expanded_binder_type",
        "expanded_field_type",
        "expanded_input_type",
        "expanded_type",
        "field_type",
        "input_type",
        "parameter_types",
        "proposition_alias_expansion",
        "record_field_types",
        "record_parameter_types",
        "result_bridges",
        "result_type",
        "row_result_type",
        "terminal_result",
        "terminal_term_dependency_surface",
        "transparent_definitions",
        "type",
    }
)
_SEMANTIC_NAVIGATION_FIELDS = frozenset(
    {
        "binder",
        "declaration",
        "effective_qualified_declaration",
        "field",
        "judgment_key",
        "line",
        "local_type_head",
        "names",
        "parameter",
        "path",
        "qualified_declaration",
        "record",
        "row",
        "source_file",
        "source_key",
        "source_location",
        "structure",
    }
)


def _collect_digest_fields(
    value: object, fields: frozenset[str], output: list[str]
) -> None:
    if isinstance(value, Mapping):
        for raw_key, raw_value in value.items():
            key = str(raw_key)
            if key in fields:
                digest = _digest(raw_value)
                if digest:
                    output.append(digest)
            _collect_digest_fields(raw_value, fields, output)
    elif isinstance(value, list):
        for item in value:
            _collect_digest_fields(item, fields, output)


def _semantic_surface_projection(value: object) -> object:
    """Project generated model/type content without route or binder names."""

    if isinstance(value, Mapping):
        projected: dict[str, object] = {}
        for raw_key, raw_value in value.items():
            key = str(raw_key)
            if key in _SEMANTIC_NAVIGATION_FIELDS:
                continue
            if key in _SEMANTIC_SURFACE_FIELDS:
                projected[key] = _semantic_surface_projection(raw_value)
        return projected
    if isinstance(value, list):
        return [_semantic_surface_projection(item) for item in value]
    return value


_SOURCE_AUDIT_ONLY_ITEM_FIELDS = frozenset(
    {
        "audit_note",
        "coverage_note",
        "coverage_notes",
        "draft_notes",
        "lean_status",
        "notes",
        "source_kind_validated_at",
        "source_kind_validator",
    }
)

_LEDGER_REFERENCE_FIELDS: dict[str, tuple[str, bool]] = {
    "model_convention_ids": ("model_conventions", True),
    "source_defect_id": ("defects", False),
    "source_defect_ids": ("defects", True),
    "governing_defect_ids": ("defects", True),
    "checked_proof_step_ids": ("checked_proof_steps", True),
    "deep_audit_observation_ids": ("deep_audit_observations", True),
}
_LEDGER_NAVIGATION_OR_REVIEW_FIELDS = frozenset(
    {
        "id",
        "correction_id",
        "source_locator",
        "affected_source_locators",
        "source_anchor",
        "corrected_clause_anchor",
        "resolution_evidence",
        "model_evidence",
        "repair_handoff",
        "approval_reference",
        "approved_at",
        "recorded_at",
        # These explain why/where a record was checked. They are valuable
        # human evidence, but neither changes its formal meaning nor the
        # source-item association that this transition identity pins.
        "why_needed",
        "checked_scope",
    }
)


class _LedgerSemanticResolver:
    """Resolve mutable ledger IDs to name-independent record content."""

    def __init__(
        self,
        fidelity: Mapping[str, Any] | None,
        *,
        reference_fields: Mapping[str, tuple[str, bool]] | None = None,
    ) -> None:
        self.fidelity = fidelity
        self.reference_fields = {
            **_LEDGER_REFERENCE_FIELDS,
            **dict(reference_fields or {}),
        }
        self._indexes: dict[str, tuple[dict[str, Mapping[str, Any]] | None, str]] = {}
        self._digests: dict[tuple[str, str], tuple[str, str]] = {}

    def _index(
        self, collection: str
    ) -> tuple[dict[str, Mapping[str, Any]] | None, str]:
        cached = self._indexes.get(collection)
        if cached is not None:
            return cached
        if self.fidelity is None:
            result = (None, f"referenced {collection} have no fidelity ledger")
            self._indexes[collection] = result
            return result
        raw_records = self.fidelity.get(collection)
        if not isinstance(raw_records, list):
            result = (None, f"referenced {collection} have no fidelity ledger")
            self._indexes[collection] = result
            return result
        records: dict[str, Mapping[str, Any]] = {}
        for raw_record in raw_records:
            if not isinstance(raw_record, Mapping):
                continue
            record_id = str(raw_record.get("id") or "").strip()
            if not record_id:
                continue
            if record_id in records:
                result = (None, f"source-proof fidelity duplicates a {collection} id")
                self._indexes[collection] = result
                return result
            records[record_id] = raw_record
        result = (records, "")
        self._indexes[collection] = result
        return result

    def record_digest(
        self, collection: str, record_id: str, stack: tuple[tuple[str, str], ...] = ()
    ) -> tuple[str, str]:
        key = (collection, record_id)
        cached = self._digests.get(key)
        if cached is not None:
            return cached
        if key in stack:
            return "", "source-proof fidelity record references form a cycle"
        records, error = self._index(collection)
        if records is None:
            return "", error
        record = records.get(record_id)
        if record is None:
            return "", f"missing {collection} record {record_id}"
        projected, error = self.project(
            record, ledger_record=True, stack=stack + (key,)
        )
        if error:
            return "", error
        if projected in ({}, [], None, ""):
            return "", f"{collection} record {record_id} has no semantic content"
        result = (_stable_digest({"collection": collection, "record": projected}), "")
        self._digests[key] = result
        return result

    def project(
        self,
        value: object,
        *,
        ledger_record: bool,
        stack: tuple[tuple[str, str], ...] = (),
    ) -> tuple[object, str]:
        if isinstance(value, Mapping):
            projected: dict[str, object] = {}
            for raw_key, raw_value in value.items():
                key = str(raw_key)
                if key == "id":
                    continue
                reference = self.reference_fields.get(key)
                if reference is not None:
                    collection, multiple = reference
                    if multiple:
                        if not isinstance(raw_value, list):
                            return {}, f"{key} must be a list of ledger record IDs"
                        ids = [str(item).strip() for item in raw_value]
                    else:
                        ids = [str(raw_value).strip()]
                    if any(not item for item in ids):
                        return {}, f"{key} contains an empty ledger record ID"
                    digests: list[str] = []
                    for record_id in ids:
                        digest, error = self.record_digest(
                            collection, record_id, stack
                        )
                        if error:
                            return {}, error
                        digests.append(digest)
                    # Reference order and record spelling are navigation. The
                    # association at this exact semantic field remains pinned.
                    projected[key] = sorted(digests) if multiple else digests[0]
                    continue
                if ledger_record and key in _LEDGER_NAVIGATION_OR_REVIEW_FIELDS:
                    continue
                child, error = self.project(
                    raw_value, ledger_record=ledger_record, stack=stack
                )
                if error:
                    return {}, error
                projected[key] = child
            return projected, ""
        if isinstance(value, list):
            projected_items: list[object] = []
            for item in value:
                child, error = self.project(
                    item, ledger_record=ledger_record, stack=stack
                )
                if error:
                    return [], error
                projected_items.append(child)
            return projected_items, ""
        return value, ""


def _source_item_transition_projection(
    value: object, resolver: _LedgerSemanticResolver
) -> tuple[object, str]:
    """Drop bookkeeping and replace ledger names with semantic records."""

    if isinstance(value, Mapping):
        stripped = {
            str(key): raw_value
            for key, raw_value in value.items()
            if str(key) not in _SOURCE_AUDIT_ONLY_ITEM_FIELDS
        }
        return resolver.project(stripped, ledger_record=False)
    return resolver.project(value, ledger_record=False)


_SOURCE_RECORD_ITEM_SECTIONS = (
    "boundary_input_items",
    "conclusion_dependency_items",
    "recursive_field_items",
    "semantic_model_items",
    "type_valued_certificate_result_items",
)


def _source_record_item_relationship(
    section: str, raw_item: Mapping[str, Any]
) -> dict[str, object]:
    """Return one generated row with its semantic endpoints still attached."""

    source_digests: list[str] = []
    statement_digests: list[str] = []
    _collect_digest_fields(raw_item, _SOURCE_IDENTITY_FIELDS, source_digests)
    _collect_digest_fields(
        raw_item, _ELABORATED_STATEMENT_IDENTITY_FIELDS, statement_digests
    )
    surface = {
        key: _semantic_surface_projection(raw_item[key])
        for key in _SEMANTIC_SURFACE_FIELDS
        if key in raw_item
    }
    return {
        "generated_item_kind": section,
        # Repeated generated copies of the same endpoint are administrative.
        # Multiplicity of source claims remains owned by the statement-map bag.
        "source_semantic_sha256s": sorted(set(source_digests)),
        "elaborated_statement_sha256s": sorted(set(statement_digests)),
        "semantic_surface": surface,
    }


def _source_record_identity(
    source_record: Mapping[str, Any],
) -> tuple[dict[str, object] | None, str]:
    source_digests: list[str] = []
    semantic_surfaces: list[object] = []
    item_relationships: list[dict[str, object]] = []
    saw_section = False
    for section in _SOURCE_RECORD_ITEM_SECTIONS:
        raw_items = source_record.get(section)
        if raw_items is None:
            continue
        if not isinstance(raw_items, list):
            return None, f"source record {section} is not a list"
        saw_section = True
        for raw_item in raw_items:
            if not isinstance(raw_item, Mapping):
                return None, f"source record {section} contains a malformed item"
            _collect_digest_fields(raw_item, _SOURCE_IDENTITY_FIELDS, source_digests)
            surface = {
                key: _semantic_surface_projection(raw_item[key])
                for key in _SEMANTIC_SURFACE_FIELDS
                if key in raw_item
            }
            if surface:
                semantic_surfaces.append(surface)
            item_relationships.append(
                _source_record_item_relationship(section, raw_item)
            )
    if not saw_section:
        return None, "source record has no generated semantic item sections"
    # Source-free items can exist, but a completed source-routed paper must
    # expose at least its elaborated statement identities.
    return {
        "source_semantic_sha256s": sorted(source_digests),
        # The statement ledger above owns the name-independent theorem type.
        # Older v10 source records did not always repeat that signature, so the
        # aggregate surface remains independently available for those records.
        "semantic_surfaces": sorted(
            semantic_surfaces, key=lambda value: _stable_digest(value)
        ),
        # Do not flatten source, statement, and model endpoints into independent
        # bags.  Their generated per-row association is material even when a
        # cross-row swap preserves every aggregate multiset above.
        "semantic_item_relationships": sorted(
            item_relationships, key=lambda value: _stable_digest(value)
        ),
    }, ""


_VALIDATOR_CONTRACT_EXACT_FIELDS = frozenset(
    {
        "schema",
        "prompt_version",
        "source_record_policy_version",
        "validator_engine_sha256",
        "validator_protocol_sha256",
        "audit_engine_sha256",
        "audit_protocol_sha256",
        "formalization_protocol_sha256",
    }
)


def _validator_contract_field(key: str) -> bool:
    """Return whether a field identifies an audit schema/engine, not a person."""

    return (
        key in _VALIDATOR_CONTRACT_EXACT_FIELDS
        or key.endswith("_schema")
        or key.endswith("_prompt_version")
        or key.endswith("_policy_version")
        or (
            key.endswith("_sha256")
            and any(token in key for token in ("validator", "protocol", "engine"))
        )
    )


def _validator_contract_projection(value: object) -> object:
    """Keep only machine-verifiable validator/protocol identity fields."""

    if isinstance(value, Mapping):
        projected: dict[str, object] = {}
        for raw_key, raw_value in value.items():
            key = str(raw_key)
            if _validator_contract_field(key):
                projected[key] = _validator_contract_projection(raw_value)
            elif key == "v10_audit_state" and isinstance(raw_value, Mapping):
                nested = _validator_contract_projection(raw_value)
                if nested:
                    projected[key] = nested
        return projected
    if isinstance(value, list):
        return [_validator_contract_projection(item) for item in value]
    return value


def _audit_authority_identity(
    artifacts: Mapping[str, bytes | None],
    protocol: Mapping[str, Any] | None,
) -> tuple[dict[str, object] | None, str]:
    sidecars: dict[str, object] = {}
    for relative in MATERIAL_ARTIFACT_PATHS:
        payload = _json_object(artifacts.get(relative))
        if payload is None:
            if relative == SOURCE_PROOF_FIDELITY_PATH:
                continue
            return None, f"{relative} is missing or malformed"
        projected = _validator_contract_projection(payload)
        if projected:
            sidecars[relative] = projected
    try:
        protocol_sha256 = formalization_review_protocol_digest(protocol)
    except (TypeError, ValueError) as exc:
        return None, f"material audit protocol identity is unavailable: {exc}"
    return {
        "formalization_material_protocol_sha256": protocol_sha256,
        "artifact_validator_contracts": sidecars,
    }, ""


_DEPENDENCY_CONTEXT_IDENTITY_LIST_FIELDS = (
    "lean_dependency_identities",
    "toolchain_identities",
    "source_artifact_identities",
    "audit_engine_identities",
    "raw_producer_code_identities",
)


def _content_identity_bag(
    value: object, field: str
) -> tuple[list[dict[str, object]] | None, str]:
    if not isinstance(value, list):
        return None, f"source-record input fingerprint {field} is not a list"
    identities: list[dict[str, object]] = []
    for raw_item in value:
        if not isinstance(raw_item, Mapping):
            return None, f"source-record input fingerprint {field} is malformed"
        identity = {
            str(key): raw_value
            for key, raw_value in raw_item.items()
            # File/declaration spelling locates an identity but does not define it.
            if str(key) not in {"path", "name", "label", "declaration"}
        }
        for key, raw_value in identity.items():
            if key.endswith("_sha256") or key == "sha256":
                digest = str(raw_value or "").strip().lower()
                if digest and not _digest(digest):
                    return None, (
                        f"source-record input fingerprint {field} has an invalid digest"
                    )
        if not identity or (
            set(identity) <= {"sha256", "status"}
            and not str(identity.get("sha256") or "").strip()
            and identity.get("status") != "missing"
        ):
            return None, f"source-record input fingerprint {field} lacks content identity"
        identities.append(identity)
    return sorted(identities, key=_stable_digest), ""


def _lean_owned_dependency_and_artifact_context(
    source_record: Mapping[str, Any],
) -> tuple[dict[str, object], str]:
    """Project current closure/toolchain receipts without depending on paths."""

    fingerprint = source_record.get("source_record_input_fingerprint")
    if fingerprint is None:
        return {"available": False}, ""
    if not isinstance(fingerprint, Mapping):
        return {}, "source_record_input_fingerprint is not an object"
    projected: dict[str, object] = {"available": True}
    for field in _DEPENDENCY_CONTEXT_IDENTITY_LIST_FIELDS:
        if field not in fingerprint:
            continue
        identities, error = _content_identity_bag(fingerprint[field], field)
        if identities is None:
            return {}, error
        projected[field] = identities
    for field in (
        "schema",
        "source_record_item_digest_schema",
        "source_record_policy_version",
        "implementation_sha256",
        "paper_statement_map_semantic_sha256",
    ):
        if field in fingerprint:
            projected[field] = fingerprint[field]
    return projected, ""


_RESULT_DECLARATION_NAVIGATION_FIELDS = frozenset(
    {
        "qualified_declaration",
        "effective_qualified_declaration",
        "reviewed_declaration",
        "effective_declaration",
    }
)


def _collect_navigation_strings(
    value: object, fields: frozenset[str], output: list[str]
) -> None:
    """Collect exact route coordinates for lookup, never for hashed output."""

    if isinstance(value, Mapping):
        for raw_key, raw_value in value.items():
            key = str(raw_key)
            if key in fields:
                if isinstance(raw_value, str) and raw_value.strip():
                    output.append(raw_value.strip())
                elif isinstance(raw_value, list):
                    output.extend(
                        item.strip()
                        for item in raw_value
                        if isinstance(item, str) and item.strip()
                    )
            _collect_navigation_strings(raw_value, fields, output)
    elif isinstance(value, list):
        for item in value:
            _collect_navigation_strings(item, fields, output)


class _GeneratedTargetSemanticResolver:
    """Resolve status declaration routes to generated name-free semantics."""

    def __init__(self, source_record: Mapping[str, Any]) -> None:
        self.result_targets: dict[str, set[str]] = {}
        self.model_targets: dict[str, set[str]] = {}
        for section in _SOURCE_RECORD_ITEM_SECTIONS:
            raw_items = source_record.get(section)
            if not isinstance(raw_items, list):
                continue
            for raw_item in raw_items:
                if not isinstance(raw_item, Mapping):
                    continue
                relationship = _source_record_item_relationship(section, raw_item)
                statements = relationship["elaborated_statement_sha256s"]
                if statements:
                    result_identity = _stable_digest(
                        {"elaborated_statement_sha256s": statements}
                    )
                    declarations: list[str] = []
                    _collect_navigation_strings(
                        raw_item,
                        _RESULT_DECLARATION_NAVIGATION_FIELDS,
                        declarations,
                    )
                    for declaration in declarations:
                        self.result_targets.setdefault(declaration, set()).add(
                            result_identity
                        )

                surface = relationship["semantic_surface"]
                if not surface:
                    continue
                model_identity = _stable_digest(
                    {
                        "generated_item_kind": section,
                        "semantic_surface": surface,
                    }
                )
                model_roots: list[str] = []
                _collect_navigation_strings(
                    raw_item, frozenset({"record_roots"}), model_roots
                )
                for model_root in model_roots:
                    self.model_targets.setdefault(model_root, set()).add(
                        model_identity
                    )

    @staticmethod
    def _resolve_many(
        raw_values: object,
        index: Mapping[str, set[str]],
        label: str,
    ) -> tuple[list[list[str]] | None, str]:
        values = [raw_values] if isinstance(raw_values, str) else raw_values
        if not isinstance(values, list) or not values:
            return None, f"formalization_scope {label} must be nonempty"
        resolved: list[list[str]] = []
        for raw_value in values:
            value = str(raw_value or "").strip()
            endpoints = index.get(value)
            if not value or not endpoints:
                return None, f"formalization_scope {label} has an unresolved semantic target"
            resolved.append(sorted(endpoints))
        return sorted(resolved, key=_stable_digest), ""

    def resolve_results(self, values: object) -> tuple[list[list[str]] | None, str]:
        return self._resolve_many(
            values, self.result_targets, "target_result_declarations"
        )

    def resolve_models(self, values: object) -> tuple[list[list[str]] | None, str]:
        return self._resolve_many(values, self.model_targets, "model_spec_declarations")


_STATUS_NAVIGATION_FIELDS = frozenset(
    {
        "scope_id",
        "artifact_path",
        "path",
        "recorded_at",
    }
)


def _formalization_scope_identity(
    status: Mapping[str, Any],
    source_record: Mapping[str, Any],
    ledger_resolver: _LedgerSemanticResolver,
) -> tuple[object, str]:
    """Project material scope/correction targets without hashing their names."""

    raw_scope = status.get("formalization_scope")
    if raw_scope is None:
        return None, ""
    if not isinstance(raw_scope, Mapping):
        return None, "formalization_scope is not an object"
    # The trusted v10 baseline predates the explicit authority pair and its
    # closeout gate interpreted joint omission as whole-paper authority. Treat
    # the later explicit spelling of that same effective role as migration,
    # not a mathematical scope change. Current malformed scopes still fail the
    # ordinary evidence gate independently of this transition comparison.
    effective_scope = dict(raw_scope)
    if (
        "scope_role" not in effective_scope
        and "whole_paper_closeout_claimed" not in effective_scope
    ):
        effective_scope["scope_role"] = "whole_paper_closeout"
        effective_scope["whole_paper_closeout_claimed"] = True
    targets = _GeneratedTargetSemanticResolver(source_record)

    def project(value: object) -> tuple[object, str]:
        if isinstance(value, Mapping):
            projected: dict[str, object] = {}
            for raw_key, raw_value in value.items():
                key = str(raw_key)
                if key in _STATUS_NAVIGATION_FIELDS:
                    continue
                if key == "correction_ids":
                    if not isinstance(raw_value, list) or not raw_value:
                        return {}, "formalization_scope correction_ids must be nonempty"
                    corrections: list[str] = []
                    for raw_id in raw_value:
                        correction_id = str(raw_id or "").strip()
                        correction_digest, error = ledger_resolver.record_digest(
                            "governing_corrections", correction_id
                        )
                        if error:
                            return {}, error
                        corrections.append(correction_digest)
                    projected["governing_correction_semantic_sha256s"] = sorted(
                        corrections
                    )
                    continue
                if key == "target_result_declarations":
                    resolved, error = targets.resolve_results(raw_value)
                    if error:
                        return {}, error
                    projected["target_result_semantic_identities"] = resolved or []
                    continue
                if key in {"model_spec_declaration", "model_spec_declarations"}:
                    resolved, error = targets.resolve_models(raw_value)
                    if error:
                        return {}, error
                    projected["model_spec_semantic_identities"] = resolved or []
                    continue
                if key == "target_model_spec_declarations":
                    if not isinstance(raw_value, Mapping) or not raw_value:
                        return {}, "formalization_scope target_model_spec_declarations is malformed"
                    associations: list[dict[str, object]] = []
                    for raw_result, raw_model in raw_value.items():
                        result, result_error = targets.resolve_results(str(raw_result))
                        model, model_error = targets.resolve_models(raw_model)
                        if result_error or model_error:
                            return {}, result_error or model_error
                        associations.append(
                            {
                                "target_result_semantic_identities": result or [],
                                "model_spec_semantic_identities": model or [],
                            }
                        )
                    projected["target_model_semantic_associations"] = sorted(
                        associations, key=_stable_digest
                    )
                    continue
                child, error = project(raw_value)
                if error:
                    return {}, error
                projected[key] = child
            return projected, ""
        if isinstance(value, list):
            items: list[object] = []
            for raw_item in value:
                child, error = project(raw_item)
                if error:
                    return [], error
                items.append(child)
            return sorted(items, key=_stable_digest), ""
        return value, ""

    return project(effective_scope)


def _governing_corrections_identity(
    status: Mapping[str, Any], resolver: _LedgerSemanticResolver
) -> tuple[list[str] | None, str]:
    raw_corrections = status.get("governing_corrections")
    if raw_corrections is None:
        return [], ""
    if not isinstance(raw_corrections, list) or not raw_corrections:
        return None, "governing_corrections is not a nonempty record list"
    identities: list[str] = []
    for raw_record in raw_corrections:
        if not isinstance(raw_record, Mapping):
            return None, "governing_corrections contains a malformed record"
        record_id = str(raw_record.get("id") or "").strip()
        identity, error = resolver.record_digest("governing_corrections", record_id)
        if error:
            return None, error
        identities.append(identity)
    return sorted(identities), ""


def _material_closeout_semantic_payload(
    artifacts: Mapping[str, bytes | None],
) -> tuple[dict[str, object] | None, str]:
    """Return the name-free mathematical projection shared by both schemas."""

    status = _json_object(artifacts.get(STATUS_PATH))
    statement_map = _json_object(artifacts.get(STATEMENT_MAP_PATH))
    statement_review = _json_object(artifacts.get(STATEMENT_REVIEW_PATH))
    source_record = _json_object(artifacts.get(SOURCE_RECORD_PATH))
    source_proof_fidelity = _json_object(
        artifacts.get(SOURCE_PROOF_FIDELITY_PATH)
    )
    if status is None:
        return None, "status.json is missing or malformed"
    if statement_map is None:
        return None, "paper statement map is missing or malformed"
    if statement_review is None:
        return None, "statement review is missing or malformed"
    if source_record is None:
        return None, "source record is missing or malformed"

    semantic_ledger: dict[str, Any] = dict(source_proof_fidelity or {})
    raw_corrections = status.get("governing_corrections")
    correction_references: dict[str, tuple[str, bool]] = {}
    if isinstance(raw_corrections, list) and raw_corrections:
        semantic_ledger["governing_corrections"] = raw_corrections
        correction_references = {
            "correction_id": ("governing_corrections", False),
            "correction_ids": ("governing_corrections", True),
        }
    ledger_resolver = _LedgerSemanticResolver(
        semantic_ledger,
        reference_fields=correction_references,
    )
    source_items, error = _selected_source_item_digests(
        statement_map,
        source_proof_fidelity,
        resolver=ledger_resolver,
    )
    if source_items is None:
        return None, error
    statements, error = _statement_review_identity(statement_review)
    if statements is None:
        return None, error
    source_record_identity, error = _source_record_identity(source_record)
    if source_record_identity is None:
        return None, error
    formalization_scope, error = _formalization_scope_identity(
        status, source_record, ledger_resolver
    )
    if error:
        return None, error
    governing_corrections, error = _governing_corrections_identity(
        status, ledger_resolver
    )
    if governing_corrections is None:
        return None, error
    return {
        "selected_source_item_semantic_sha256s": source_items,
        "statement_semantic_identities": statements,
        "source_record_semantic_identity": source_record_identity,
        "formalization_scope_semantic_identity": formalization_scope,
        "governing_correction_semantic_sha256s": governing_corrections,
        # Status labels, review configuration, and free-form closeout prose are
        # administration. Scope and correction targets above are mathematical:
        # IDs and declaration spellings are resolved to generated semantics.
    }, ""


def _material_closeout_identity_record_uncached(
    artifacts: Mapping[str, bytes | None],
    *,
    schema: int,
    protocol: Mapping[str, Any] | None,
) -> tuple[MaterialCloseoutIdentityRecord | None, str]:
    if schema not in SUPPORTED_MATERIAL_IDENTITY_SCHEMAS:
        return None, f"material closeout identity schema {schema} is unsupported"
    semantic_payload, error = _material_closeout_semantic_payload(artifacts)
    if semantic_payload is None:
        return None, error

    payload: dict[str, object] = {
        "schema": schema,
        **semantic_payload,
    }
    if schema == PORTABLE_MATERIAL_IDENTITY_SCHEMA:
        source_record = _json_object(artifacts.get(SOURCE_RECORD_PATH))
        if source_record is None:
            return None, "source record is missing or malformed"
        dependency_context, dependency_error = (
            _lean_owned_dependency_and_artifact_context(source_record)
        )
        if dependency_error:
            return None, dependency_error
        payload["lean_owned_dependency_and_artifact_context"] = dependency_context
        audit_authority, authority_error = _audit_authority_identity(
            artifacts, protocol
        )
        if audit_authority is None:
            return None, authority_error
        payload["audit_authority_identity"] = audit_authority

    component_sha256s = {
        key: _stable_digest({"component": key, "value": value})
        for key, value in payload.items()
        if key != "schema"
    }
    lookup_identity = _stable_digest(
        {
            "schema": 1,
            "selected_source_items_component_sha256": component_sha256s[
                "selected_source_item_semantic_sha256s"
            ],
        }
    )
    material_identity = (
        _stable_digest(payload)
        if schema == MATERIAL_IDENTITY_SCHEMA
        else _stable_digest(
            {"schema": schema, "component_sha256s": component_sha256s}
        )
    )
    return MaterialCloseoutIdentityRecord(
        schema=schema,
        lookup_identity_sha256=lookup_identity,
        material_identity_sha256=material_identity,
        component_sha256s=component_sha256s,
    ), ""


_MATERIAL_IDENTITY_CACHE: dict[
    tuple[tuple[str, str], ...], tuple[MaterialCloseoutIdentityRecord | None, str]
] = {}


def material_closeout_identity_record(
    artifacts: Mapping[str, bytes | None],
    *,
    schema: int = MATERIAL_IDENTITY_SCHEMA,
    protocol: Mapping[str, Any] | None = None,
) -> tuple[MaterialCloseoutIdentityRecord | None, str]:
    """Return a compact semantic record without retaining raw audit payloads."""

    protocol_identity = ""
    if schema == PORTABLE_MATERIAL_IDENTITY_SCHEMA:
        try:
            protocol_identity = formalization_review_protocol_digest(protocol)
        except (TypeError, ValueError) as exc:
            return None, f"material audit protocol identity is unavailable: {exc}"
    cache_key = (
        ("<schema>", str(schema)),
        ("<protocol>", protocol_identity),
        *(
            (
                relative,
                hashlib.sha256(raw).hexdigest()
                if isinstance(raw, bytes)
                else "<missing>",
            )
            for relative in MATERIAL_ARTIFACT_PATHS
            for raw in (artifacts.get(relative),)
        ),
    )
    cached = _MATERIAL_IDENTITY_CACHE.get(cache_key)
    if cached is not None:
        return cached
    result = _material_closeout_identity_record_uncached(
        artifacts, schema=schema, protocol=protocol
    )
    if len(_MATERIAL_IDENTITY_CACHE) >= 128 and _MATERIAL_IDENTITY_CACHE:
        _MATERIAL_IDENTITY_CACHE.pop(next(iter(_MATERIAL_IDENTITY_CACHE)))
    _MATERIAL_IDENTITY_CACHE[cache_key] = result
    return result


def material_closeout_identity(
    artifacts: Mapping[str, bytes | None],
    *,
    schema: int = MATERIAL_IDENTITY_SCHEMA,
    protocol: Mapping[str, Any] | None = None,
) -> tuple[str, str]:
    """Return a content-addressed transition identity without repeat parsing."""

    record, error = material_closeout_identity_record(
        artifacts, schema=schema, protocol=protocol
    )
    return (record.material_identity_sha256, "") if record is not None else ("", error)


ArtifactSnapshot = tuple[tuple[str, tuple[int, int, int, int, int] | None], ...]
_CURRENT_IDENTITY_CACHE: dict[
    tuple[str, int, str], tuple[ArtifactSnapshot, tuple[str, str]]
] = {}
_BASELINE_IDENTITY_CACHE: dict[
    tuple[str, str, str], tuple[str, str, str]
] = {}


def _artifact_snapshot(folder: Path) -> ArtifactSnapshot:
    snapshot: list[tuple[str, tuple[int, int, int, int, int] | None]] = []
    for relative in MATERIAL_ARTIFACT_PATHS:
        try:
            stat = (folder / relative).stat()
            identity = (
                stat.st_dev,
                stat.st_ino,
                stat.st_size,
                stat.st_mtime_ns,
                stat.st_ctime_ns,
            )
        except OSError:
            identity = None
        snapshot.append((relative, identity))
    return tuple(snapshot)


def _current_artifacts_consistently(
    folder: Path,
) -> tuple[dict[str, bytes | None] | None, str]:
    """Read all transition inputs from one stable filesystem snapshot."""

    for _attempt in range(2):
        before = _artifact_snapshot(folder)
        artifacts = _current_artifacts(folder)
        after = _artifact_snapshot(folder)
        if before == after:
            return artifacts, ""
    return None, "material closeout artifacts changed while they were read"


def _current_material_identity(
    folder: Path,
    *,
    schema: int = MATERIAL_IDENTITY_SCHEMA,
    protocol: Mapping[str, Any] | None = None,
) -> tuple[str, str]:
    """Reuse a current identity until one of its five inputs changes."""

    protocol_identity = (
        formalization_review_protocol_digest(protocol)
        if schema == PORTABLE_MATERIAL_IDENTITY_SCHEMA
        else ""
    )
    folder_key = (str(folder), schema, protocol_identity)
    for _attempt in range(2):
        before = _artifact_snapshot(folder)
        cached = _CURRENT_IDENTITY_CACHE.get(folder_key)
        if cached is not None and cached[0] == before:
            return cached[1]
        artifacts = _current_artifacts(folder)
        after = _artifact_snapshot(folder)
        if before != after:
            continue
        result = material_closeout_identity(
            artifacts, schema=schema, protocol=protocol
        )
        if len(_CURRENT_IDENTITY_CACHE) >= 64 and folder_key not in _CURRENT_IDENTITY_CACHE:
            _CURRENT_IDENTITY_CACHE.pop(next(iter(_CURRENT_IDENTITY_CACHE)))
        _CURRENT_IDENTITY_CACHE[folder_key] = (after, result)
        return result
    return "", "material closeout artifacts changed while they were read"


def current_material_closeout_identity_record(
    folder: Path,
    *,
    schema: int,
    protocol: Mapping[str, Any] | None,
) -> tuple[MaterialCloseoutIdentityRecord | None, str]:
    """Read one folder consistently and return its portable material record."""

    for _attempt in range(2):
        before = _artifact_snapshot(folder)
        artifacts = _current_artifacts(folder)
        after = _artifact_snapshot(folder)
        if before != after:
            continue
        return material_closeout_identity_record(
            artifacts, schema=schema, protocol=protocol
        )
    return None, "material closeout artifacts changed while they were read"


def _baseline_material_identity(
    reader: GitBlobReader,
    commit: str,
    *,
    cache_key: tuple[str, str, str] | None,
) -> tuple[str, str, str]:
    """Return baseline status/identity/error without rehashing immutable blobs."""

    if cache_key is not None:
        cached = _BASELINE_IDENTITY_CACHE.get(cache_key)
        if cached is not None:
            return cached
    artifacts = {
        relative: reader(commit, relative) for relative in MATERIAL_ARTIFACT_PATHS
    }
    status = _json_object(artifacts.get(STATUS_PATH))
    status_value = (
        str(status.get("status") or "").strip().lower()
        if status is not None
        else ""
    )
    identity, error = material_closeout_identity(artifacts)
    result = (status_value, identity, error)
    if cache_key is not None:
        if len(_BASELINE_IDENTITY_CACHE) >= 128:
            _BASELINE_IDENTITY_CACHE.pop(next(iter(_BASELINE_IDENTITY_CACHE)))
        _BASELINE_IDENTITY_CACHE[cache_key] = result
    return result


def _baseline_configuration(
    protocol: Mapping[str, Any] | None = None,
) -> tuple[str, dict[str, Any] | None, str]:
    payload = dict(protocol) if isinstance(protocol, Mapping) else load_formalization_protocol()
    versions = payload.get("audit_versions")
    realization = versions.get("theorem_realization") if isinstance(versions, Mapping) else None
    baseline = (
        realization.get("legacy_v10_transition_baseline")
        if isinstance(realization, Mapping)
        else None
    )
    if not isinstance(baseline, Mapping):
        return "", None, "protocol has no trusted legacy-v10 transition baseline"
    authority = str(baseline.get("authority") or "").strip()
    if authority == IMMUTABLE_MATERIAL_IDENTITY_MANIFEST_AUTHORITY:
        manifest_path = str(baseline.get("manifest_path") or "").strip()
        manifest_sha256 = _digest(baseline.get("manifest_sha256"))
        if not manifest_path or not manifest_sha256:
            return authority, None, "protocol transition manifest coordinates are malformed"
        if baseline.get("material_identity_schema") != PORTABLE_MATERIAL_IDENTITY_SCHEMA:
            return authority, None, "protocol transition material-identity schema is unsupported"
        return authority, dict(baseline), ""
    if authority != TRUSTED_GIT_TREE_AUTHORITY:
        return authority, None, "protocol transition baseline authority is unsupported"
    commit = str(baseline.get("git_commit") or "").strip().lower()
    trusted_ref = str(baseline.get("trusted_ref") or "").strip()
    schema = baseline.get("material_identity_schema")
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        return authority, None, "protocol transition baseline commit is malformed"
    if trusted_ref != "refs/remotes/origin/main":
        return authority, None, "protocol transition trusted ref is unsupported"
    if schema != MATERIAL_IDENTITY_SCHEMA:
        return authority, None, "protocol transition material-identity schema is unsupported"
    return authority, dict(baseline), ""


def theorem_realization_reissue_requirement(
    root: Path,
    folder: Path,
    status_payload: Mapping[str, Any],
    *,
    git_blob_reader: GitBlobReader | None = None,
    baseline_ancestor_verifier: BaselineAncestorVerifier | None = None,
    protocol: Mapping[str, Any] | None = None,
) -> TheoremRealizationReissueRequirement:
    """Return the automatic v11 requirement for one current closeout.

    Only papers absent from the trusted legacy-v10 closeout baseline receive an
    automatic v11 requirement.  A legacy paper's changed source/model/target
    surface remains subject to the ordinary current-v10 semantic and source
    record gates, rather than being relabelled as v11 or forced through a
    migration solely because it changed.  Explicit v11 requests are handled by
    the caller and can only strengthen this result.
    """

    status = str(status_payload.get("status") or "").strip().lower()
    if status not in CLOSEOUT_STATUSES:
        return TheoremRealizationReissueRequirement(False, "not a closeout status")

    authority, baseline, config_error = _baseline_configuration(protocol)
    if config_error:
        return TheoremRealizationReissueRequirement(True, config_error)

    root = root.resolve()
    folder = folder.resolve()
    try:
        paper_relative = str(folder.relative_to(root / "papers"))
    except ValueError:
        return TheoremRealizationReissueRequirement(
            True, "paper folder is outside the trusted repository papers tree"
        )
    if not paper_relative or "/" in paper_relative or "\\" in paper_relative:
        return TheoremRealizationReissueRequirement(
            True, "paper folder is not one direct repository paper folder"
        )

    if authority == IMMUTABLE_MATERIAL_IDENTITY_MANIFEST_AUTHORITY:
        try:
            from legacy_v10_trust_ledger import evaluate_trust_ledger_entry
        except ModuleNotFoundError:  # pragma: no cover - module-style imports.
            from scripts.legacy_v10_trust_ledger import evaluate_trust_ledger_entry

        evaluation = evaluate_trust_ledger_entry(
            root=root,
            folder=folder,
            baseline=baseline or {},
            protocol=protocol,
        )
        # A matched immutable entry identifies an already closed v10 paper.
        # Its material identity may legitimately differ after a source-faithful
        # repair; fresh v10 evidence owns that change.  A missing/ambiguous
        # entry or unavailable current identity still fails closed as a new or
        # unverifiable candidate.
        if evaluation.required and not evaluation.baseline_material_identity_sha256:
            return TheoremRealizationReissueRequirement(
                True,
                evaluation.reason,
                current_material_identity_sha256=(
                    evaluation.current_material_identity_sha256
                ),
                baseline_material_identity_sha256=(
                    evaluation.baseline_material_identity_sha256
                ),
            )
        return TheoremRealizationReissueRequirement(
            False,
            "paper has a trusted legacy-v10 closeout; any material repair requires "
            "current item-level v10 source and Lean evidence; the ordinary current "
            "raw-evidence gate remains mandatory, while v11 remains an explicit upgrade",
            current_material_identity_sha256=(
                evaluation.current_material_identity_sha256
            ),
            baseline_material_identity_sha256=(
                evaluation.baseline_material_identity_sha256
            ),
        )

    if baseline is None:
        return TheoremRealizationReissueRequirement(
            True, "protocol has no trusted legacy-v10 transition baseline"
        )
    commit = str(baseline["git_commit"])
    trusted_ref = str(baseline["trusted_ref"])

    baseline_is_ancestor = (
        baseline_ancestor_verifier(commit, trusted_ref)
        if baseline_ancestor_verifier is not None
        else _trusted_baseline_is_ancestor(str(root), commit, trusted_ref)
    )
    if not baseline_is_ancestor:
        return TheoremRealizationReissueRequirement(
            True,
            "trusted legacy-v10 baseline is not an ancestor of private origin/main",
        )

    reader = git_blob_reader or _git_blob_reader(root, paper_relative)
    baseline_status_value, baseline_identity, baseline_error = (
        _baseline_material_identity(
            reader,
            commit,
            cache_key=(str(root), commit, paper_relative)
            if git_blob_reader is None
            else None,
        )
    )
    if baseline_status_value not in CLOSEOUT_STATUSES:
        return TheoremRealizationReissueRequirement(
            True,
            "paper had no completed closeout in the trusted legacy-v10 baseline",
        )

    if baseline_error:
        return TheoremRealizationReissueRequirement(
            True, "trusted legacy-v10 baseline is incomplete: " + baseline_error
        )
    current_identity, current_error = _current_material_identity(folder)
    if current_error:
        # The current closeout is still rejected by its ordinary v10 evidence
        # gates.  That malformed candidate does not become a synthetic v11
        # migration solely because this advisory transition probe cannot read
        # every material artifact.
        return TheoremRealizationReissueRequirement(
            False,
            "paper has a trusted legacy-v10 closeout; current material identity is "
            "unavailable and must be repaired by the ordinary v10 evidence gates",
            baseline_material_identity_sha256=baseline_identity,
        )
    return TheoremRealizationReissueRequirement(
        False,
        "paper has a trusted legacy-v10 closeout; any material repair requires "
        "current item-level v10 source and Lean evidence; the ordinary current "
        "raw-evidence gate remains mandatory, while v11 remains an explicit upgrade",
        current_material_identity_sha256=current_identity,
        baseline_material_identity_sha256=baseline_identity,
    )
