#!/usr/bin/env python3
"""Fast, fail-closed checks for paper-audit evidence integrity.

This complements ``audit_repository.py``.  It deliberately avoids Lean builds so
it can run on every push and pull request.  The checks target evidence failures
that can otherwise make a semantic audit look green: placeholder source
locations, divergent duplicate sidecars, unsupported status promotion, missing
source-artifact hashes, non-independent audit lanes, and untraceable human-review
counts.
"""

from __future__ import annotations

import argparse
import copy
from contextlib import contextmanager
import fcntl
import hashlib
import json
import os
import re
import shlex
import subprocess
import sys
import tarfile
import threading
import time
from collections import Counter
from dataclasses import asdict, dataclass, field as dataclass_field
from pathlib import Path
from types import MappingProxyType
from typing import Any, Iterable, Mapping, MutableMapping


def _register_supported_import_aliases() -> None:
    """Keep every supported import path at one evidence-context issuer.

    Several source-record transport lanes import this module lazily so they can
    validate an in-process ``EvidenceRunContext`` capability.  The supported
    entrypoint/module identities are ``__main__`` (direct CLI),
    ``scripts.audit_evidence_integrity`` (package import), and
    ``audit_evidence_integrity`` (top-level import from ``scripts``).  Publish
    whichever supported origin loaded first under both module aliases before a
    lazy lane can load.  A pre-existing distinct issuer is an unsupported
    hybrid invocation and fails closed rather than silently mixing opaque
    capabilities.
    """

    if __name__ not in {
        "__main__",
        "scripts.audit_evidence_integrity",
        "audit_evidence_integrity",
    }:
        return
    module = sys.modules.get(__name__)
    if module is None:  # pragma: no cover - Python registers an executing module.
        raise RuntimeError("evidence issuer has no executing module")
    for alias in ("scripts.audit_evidence_integrity", "audit_evidence_integrity"):
        existing = sys.modules.get(alias)
        if existing is not None and existing is not module:
            raise RuntimeError(
                "evidence issuer cannot share an interpreter with "
                f"a distinct `{alias}` issuer"
            )
        sys.modules[alias] = module
    # ``from scripts import audit_evidence_integrity`` may return an already
    # bound parent-package attribute without consulting the alias above.  Check
    # and bind that second import cache explicitly so a stale attribute cannot
    # bypass the exact module/class identity used by opaque contexts.
    parent = sys.modules.get("scripts")
    if parent is not None:
        missing = object()
        existing_child = getattr(parent, "audit_evidence_integrity", missing)
        if existing_child is not missing and existing_child is not module:
            raise RuntimeError(
                "evidence issuer cannot share an interpreter with a distinct "
                "`scripts.audit_evidence_integrity` package attribute"
            )
        try:
            setattr(parent, "audit_evidence_integrity", module)
        except (AttributeError, TypeError) as exc:
            raise RuntimeError(
                "evidence issuer cannot bind the `scripts.audit_evidence_integrity` "
                "package attribute"
            ) from exc


_register_supported_import_aliases()


try:
    from scripts.source_model_process_obligations import (
        caller_supplied_derived_process_basis,  # noqa: F401 - public compatibility export.
        caller_supplied_model_construction_basis,  # noqa: F401 - public compatibility export.
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_model_process_obligations import (
        caller_supplied_derived_process_basis,  # noqa: F401 - public compatibility export.
        caller_supplied_model_construction_basis,  # noqa: F401 - public compatibility export.
    )

try:
    from scripts.source_record_projection_contract import semantic_model_subanalysis_errors
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_record_projection_contract import semantic_model_subanalysis_errors

try:
    from scripts.source_coverage_scope import (
        DEEP_ONLY_SOURCE_KINDS,
        NAMED_THEORETICAL_STATEMENTS,
        THEOREM_REALIZATION_NONCLAIM_STATUSES,
        THEOREM_REALIZATION_SOURCE_KINDS,
        deep_source_coverage_attestation_error,
        filter_source_map_items_for_coverage,
        filter_source_map_items_for_proof_obligations,
        source_index_byte_pinned_anchor_item_ids,
        source_prose_definition_inventory_errors,
        source_prose_definition_replaced_named_presentation_spans,
        source_vocabulary_definition_binding_item_ids,
        source_named_result_environment_kinds_from_map,
        source_presentation_aliases,
        SOURCE_PRESENTATION_ALIAS_EXPLICIT_RENUMBERED_RESTATEMENT,
        SOURCE_PRESENTATION_ALIAS_LABEL_RELATION_FIELD,
        SOURCE_PRESENTATION_ALIAS_RENUMBERED_EVIDENCE_FIELD,
        source_coverage_mode_from_map,
        source_coverage_mode_migration_error,
        source_named_presentation_in_coverage_scope,
        source_item_in_coverage_scope,
        source_item_coverage_sha256,
        source_map_cache_semantic_sha256,
        source_map_structural_errors,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_coverage_scope import (
        DEEP_ONLY_SOURCE_KINDS,
        NAMED_THEORETICAL_STATEMENTS,
        THEOREM_REALIZATION_NONCLAIM_STATUSES,
        THEOREM_REALIZATION_SOURCE_KINDS,
        deep_source_coverage_attestation_error,
        filter_source_map_items_for_coverage,
        filter_source_map_items_for_proof_obligations,
        source_index_byte_pinned_anchor_item_ids,
        source_prose_definition_inventory_errors,
        source_prose_definition_replaced_named_presentation_spans,
        source_vocabulary_definition_binding_item_ids,
        source_named_result_environment_kinds_from_map,
        source_presentation_aliases,
        SOURCE_PRESENTATION_ALIAS_EXPLICIT_RENUMBERED_RESTATEMENT,
        SOURCE_PRESENTATION_ALIAS_LABEL_RELATION_FIELD,
        SOURCE_PRESENTATION_ALIAS_RENUMBERED_EVIDENCE_FIELD,
        source_coverage_mode_from_map,
        source_coverage_mode_migration_error,
        source_named_presentation_in_coverage_scope,
        source_item_in_coverage_scope,
        source_item_coverage_sha256,
        source_map_cache_semantic_sha256,
        source_map_structural_errors,
    )

try:
    from scripts.source_artifact_companion import source_text_companion_validation_issues
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_artifact_companion import source_text_companion_validation_issues

try:
    from scripts.source_archive_surface import source_archive_surface_validation_issues
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_archive_surface import source_archive_surface_validation_issues

try:
    from scripts.source_record_freshness import (
        SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
        source_record_item_judgment_current,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_record_freshness import (
        SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
        source_record_item_judgment_current,
    )

try:
    from scripts.source_record_integrity import canonical_digest_payload
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_record_integrity import canonical_digest_payload

try:
    from scripts.check_formalization_engine_revision import (
        EngineRevisionError,
        validated_runtime_raw_producer_compatibility_ledger,
    )
    from scripts.source_record_raw_producer_compatibility import (
        fingerprint_without_raw_producer_provenance,
        source_record_fingerprint_matches_with_raw_producer_compatibility,
    )
except ModuleNotFoundError:  # pragma: no cover - direct-script imports.
    from check_formalization_engine_revision import (
        EngineRevisionError,
        validated_runtime_raw_producer_compatibility_ledger,
    )
    from source_record_raw_producer_compatibility import (
        fingerprint_without_raw_producer_provenance,
        source_record_fingerprint_matches_with_raw_producer_compatibility,
    )

try:
    from scripts.formalization_protocol import (
        formalization_judgment_review_protocol_is_current,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from formalization_protocol import (
        formalization_judgment_review_protocol_is_current,
    )

try:
    from scripts.source_record_integrity import (
        SOURCE_RECORD_REUSABLE_ITEM_SECTIONS,
        reusable_item_metadata_error,
        source_record_audit_receipt_error,
        source_record_item_reuse_eligible,
        source_record_target_route_error,
        source_record_raw_reusable_item_metadata_error as _raw_item_metadata_error,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_record_integrity import (
        SOURCE_RECORD_REUSABLE_ITEM_SECTIONS,
        reusable_item_metadata_error,
        source_record_audit_receipt_error,
        source_record_item_reuse_eligible,
        source_record_target_route_error,
        source_record_raw_reusable_item_metadata_error as _raw_item_metadata_error,
    )

try:
    from scripts.source_record_partial_to_formalized_transition import (
        validate_source_record_partial_to_formalized_transition,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_record_partial_to_formalized_transition import (
        validate_source_record_partial_to_formalized_transition,
    )

try:
    from scripts.source_record_selected_surface_rebind import selected_surface_rebind_context
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_record_selected_surface_rebind import selected_surface_rebind_context

try:
    from scripts.source_record_schema4_to5_migration import (
        copy_loaded_source_record_schema4_to5_migration_item,
        is_loaded_source_record_schema4_to5_migration_item,
        load_current_source_record_schema4_to5_migration_items,
        source_record_schema4_to5_migration_item_has_provenance,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_record_schema4_to5_migration import (
        copy_loaded_source_record_schema4_to5_migration_item,
        is_loaded_source_record_schema4_to5_migration_item,
        load_current_source_record_schema4_to5_migration_items,
        source_record_schema4_to5_migration_item_has_provenance,
    )

try:
    from scripts.source_record_differential_revalidation import (
        _raw_item_groups as source_record_raw_item_groups,
        copy_loaded_source_record_differential_revalidation_item,
        is_loaded_source_record_differential_revalidation_item,
        load_current_source_record_differential_revalidation_items,
        source_record_differential_revalidation_item_has_provenance,
    )
except ModuleNotFoundError:  # pragma: no cover - supports direct-script imports.
    from source_record_differential_revalidation import (
        _raw_item_groups as source_record_raw_item_groups,
        copy_loaded_source_record_differential_revalidation_item,
        is_loaded_source_record_differential_revalidation_item,
        load_current_source_record_differential_revalidation_items,
        source_record_differential_revalidation_item_has_provenance,
    )

try:
    from scripts.source_record_attested_selected_reuse import (
        copy_loaded_source_record_attested_selected_reuse_item,
        is_loaded_source_record_attested_selected_reuse_item,
        load_current_attested_selected_semantic_reuse_items,
        source_record_attested_selected_reuse_item_has_provenance,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_record_attested_selected_reuse import (
        copy_loaded_source_record_attested_selected_reuse_item,
        is_loaded_source_record_attested_selected_reuse_item,
        load_current_attested_selected_semantic_reuse_items,
        source_record_attested_selected_reuse_item_has_provenance,
    )

try:
    from scripts.source_record_target_disposition import (
        SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME,
        load_administrative_projection_rebind_context,
        model_convention_semantic_digest,
        project_source_record_response_association_pins,
        recursive_field_target_disposition_errors,
        semantic_target_disposition_errors,
        source_input_target_disposition_errors,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_record_target_disposition import (
        SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME,
        load_administrative_projection_rebind_context,
        model_convention_semantic_digest,
        project_source_record_response_association_pins,
        recursive_field_target_disposition_errors,
        semantic_target_disposition_errors,
        source_input_target_disposition_errors,
    )

try:
    from scripts.source_record_auxiliary_routing_supplement import (
        ValidatedAuxiliaryRoutingContext,
        current_auxiliary_routing_context,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_record_auxiliary_routing_supplement import (
        ValidatedAuxiliaryRoutingContext,
        current_auxiliary_routing_context,
    )

try:
    from scripts.configured_assumption_formalization_regularities import (
        CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_FILE,
        ConfiguredAssumptionFormalizationRegularityContext,
        load_configured_assumption_formalization_regularity_context,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from configured_assumption_formalization_regularities import (
        CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_FILE,
        ConfiguredAssumptionFormalizationRegularityContext,
        load_configured_assumption_formalization_regularity_context,
    )

try:
    from scripts.source_named_result_index import (
        OPEN_NAMED_PRESENTATION_KIND,
        SOURCE_PRESENTATION_RECONCILIATION_FIELD,
        UNCLASSIFIED_NAMED_PRESENTATION_KIND,
        extract_named_result_presentations,
        named_result_presentations_sha256,
        reconcile_named_result_presentations,
        source_presentation_reconciliation_errors,
        uncovered_named_result_presentations,
    )
except ModuleNotFoundError:  # pragma: no cover - supports module-style imports.
    from source_named_result_index import (
        OPEN_NAMED_PRESENTATION_KIND,
        SOURCE_PRESENTATION_RECONCILIATION_FIELD,
        UNCLASSIFIED_NAMED_PRESENTATION_KIND,
        extract_named_result_presentations,
        named_result_presentations_sha256,
        reconcile_named_result_presentations,
        source_presentation_reconciliation_errors,
        uncovered_named_result_presentations,
    )

try:
    from scripts.tomllib_compat import tomllib
except ModuleNotFoundError:  # Direct ``python scripts/...`` execution.
    from tomllib_compat import tomllib


ROOT = Path(
    os.environ.get("ECONCSLIB_REPO_ROOT", Path(__file__).resolve().parents[1])
).resolve()
PAPERS = ROOT / "papers"
AUDIT_CONFIG = PAPERS / "audit_config.json"
LAKEFILE = ROOT / "lakefile.toml"

_UNSET = object()

CLOSEOUT_STATUSES = {
    "formalized",
    "formalized with caveat",
    "partially formalized",
    "conditional",
}
FULL_CLOSEOUT_STATUSES = {
    "formalized",
    "formalized with caveat",
}
REPOSITORY_VISIBILITIES = frozenset({"public", "private_only"})
PLAIN_FORMALIZED = "formalized"
AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE = "author_approved_corrected_model"
WHOLE_PAPER_CLOSEOUT_SCOPE_ROLE = "whole_paper_closeout"
COMPONENT_LEVEL_EVIDENCE_ONLY_SCOPE_ROLE = "component_level_evidence_only"
CORRECTED_MODEL_SCOPE_ROLES = {
    WHOLE_PAPER_CLOSEOUT_SCOPE_ROLE,
    COMPONENT_LEVEL_EVIDENCE_ONLY_SCOPE_ROLE,
}
# Schema 2 contracts predate the probability-semantics dimensions below.  They
# remain auditable as historical evidence, while all newly created corrected
# model contracts must use schema 3 and cover the expanded set.
CORRECTED_MODEL_LEGACY_CONTRACT_SCHEMA = 2
CORRECTED_MODEL_CONTRACT_SCHEMA = 3
CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION = (
    "source-record-v10-semantic-conclusion-boundary-contract"
)
CORRECTED_MODEL_LEGACY_SEMANTIC_DIMENSIONS = {
    "expanded_binders_and_domain",
    "carrier_and_domain",
    "probability_support_endpoints",
    "joint_law_and_state_evolution",
    "extended_rate_codomain",
}
CORRECTED_MODEL_SEMANTIC_DIMENSIONS = {
    *CORRECTED_MODEL_LEGACY_SEMANTIC_DIMENSIONS,
    "conditioning_and_calibration_semantics",
    "expectation_definedness",
    "null_cell_totalization_and_partition_scope",
}
CORRECTED_MODEL_GOVERNING_DISPOSITIONS = {
    "repaired_in_governing_proof",
    "replaced_by_authorized_correction",
}
CORRECTED_MODEL_CONCLUSION_RELATIONS = {
    "same",
    "restricted_domain",
    "corrected_codomain",
    "replaced",
}
CORRECTED_MODEL_SEMANTIC_DISPOSITIONS = {
    "literal_source_formula",
    "literal_source_condition",
    "author_approved_correction",
    "author_approved_additional_assumption",
    "derived_checked_bridge",
    "archival_diagnostic",
}
CORRECTED_MODEL_ASSUMPTION_DISPOSITIONS = {
    "literal_source_condition",
    "author_approved_correction",
    "author_approved_additional_assumption",
}
CORRECTED_MODEL_DIMENSION_VERDICTS = {
    "matches_literal_source",
    "author_approved_correction",
    "archival_diagnostic",
    "not_applicable",
}
CORRECTED_MODEL_SOURCE_LOCATOR_RE = re.compile(
    r"(?:\b[\w./-]+\.(?:tex|txt|md|pdf):\d+|"
    r"\b(?:Appendix|Theorem|Lemma|Proposition|Corollary|Definition|Equation|Section)\s+)",
    re.I,
)
SEMANTIC_MODEL_REVIEW_CLASSIFICATION = "semantic_model_review"
SEMANTIC_MODEL_REVIEW_VERDICTS = {
    "matches_source_model",
    "matches_literal_source",
    "matches_approved_source_convention",
    "matches_approved_corrected_target",
    "not_applicable",
    "mismatch_or_open",
    "documented_partial_boundary",
}
SEMANTIC_MODEL_REVIEW_SCHEMA = 2
SEMANTIC_MODEL_REVIEW_DIMENSIONS = {
    "expanded_binders_and_domain",
    "carrier_and_domain",
    "probability_support_endpoints",
    "joint_law_and_state_evolution",
    "conditioning_and_calibration_semantics",
    "expectation_definedness",
    "null_cell_totalization_and_partition_scope",
    "extended_rate_codomain",
}
# These are not part of the universal schema-2 review checklist.  They are
# source-context-triggered extensions emitted only for a specific generated
# row, with their own source/signature association and response validator.
# Keeping them out of ``SEMANTIC_MODEL_REVIEW_DIMENSIONS`` avoids turning a
# repair for one source model into a new obligatory review dimension for every
# unrelated paper.
SOURCE_SCOPED_SEMANTIC_MODEL_DIMENSIONS = {
    "conditioning_information",
    "source_equality_partition",
    "source_model_derivation",
    "strategic_observation_totality",
}
SEMANTIC_MODEL_BRIDGE_DIMENSIONS = {
    "probability_support_endpoints",
    "joint_law_and_state_evolution",
    "conditioning_and_calibration_semantics",
    "expectation_definedness",
    "null_cell_totalization_and_partition_scope",
    "extended_rate_codomain",
}


def semantic_model_item_dimension_ids_error(raw_dimensions: object) -> str:
    """Validate one generated row's base and source-scoped dimensions.

    Every row has the fixed schema-2 base checklist.  A source-pinned
    generator may append a narrowly validated dimension, but arbitrary extras
    cannot be smuggled into the audit surface.  This is intentionally driven
    by generated context metadata rather than a declaration, binder, or map
    key.
    """

    if not isinstance(raw_dimensions, list) or not all(
        isinstance(dimension, dict) for dimension in raw_dimensions
    ):
        return "semantic dimensions must be a list of objects"
    dimension_ids = [
        str(dimension.get("id") or "").strip() for dimension in raw_dimensions
    ]
    if not dimension_ids or any(not dimension for dimension in dimension_ids):
        return "semantic dimensions must have nonempty ids"
    if len(dimension_ids) != len(set(dimension_ids)):
        return "semantic dimensions must not duplicate an id"
    dimension_id_set = set(dimension_ids)
    if not SEMANTIC_MODEL_REVIEW_DIMENSIONS.issubset(dimension_id_set):
        return "semantic dimensions omit a required schema-2 base dimension"
    extensions = dimension_id_set - SEMANTIC_MODEL_REVIEW_DIMENSIONS
    if not extensions.issubset(SOURCE_SCOPED_SEMANTIC_MODEL_DIMENSIONS):
        return "semantic dimensions contain an unsupported non-base extension"
    for dimension in raw_dimensions:
        if (
            str(dimension.get("id") or "").strip()
            == "source_equality_partition"
            and dimension.get("requires_source_equality_partition_analysis") is not True
        ):
            return (
                "source_equality_partition must be an explicitly generated "
                "source-pinned equality-partition obligation"
            )
        if (
            str(dimension.get("id") or "").strip()
            == "strategic_observation_totality"
            and dimension.get("requires_strategic_observation_totality_analysis")
            is not True
        ):
            return (
                "strategic_observation_totality must be an explicitly generated "
                "source-pinned game-observation totality obligation"
            )
        if (
            str(dimension.get("id") or "").strip()
            == "conditioning_information"
            and dimension.get("requires_conditioning_information_analysis") is not True
        ):
            return (
                "conditioning_information must be an explicitly generated "
                "source-pinned conditioning-information obligation"
            )
        if (
            str(dimension.get("id") or "").strip()
            == "source_model_derivation"
            and dimension.get("requires_source_model_derivation_analysis") is not True
        ):
            return (
                "source_model_derivation must be an explicitly generated "
                "source-pinned model-derivation obligation"
            )
    return ""
# A source-first closeout is not allowed to rely indefinitely on a legacy
# statement/coverage surface once it has both a curated source inventory and a
# canonical source-proof ledger.  These fields describe evidence artifacts and
# review schemas only; Lean declaration names are intentionally not inputs.
V10_STATEMENT_REVIEW_ARTIFACT_FIELDS = (
    "lean_to_tex_file",
    "match_judgment_file",
    "review_surface_audit_file",
)
V10_PAPER_COVERAGE_ARTIFACT_FIELDS = ("paper_coverage_audit_file",)
V10_SOURCE_RECORD_ARTIFACT_FIELDS = (
    "source_record_audit_file",
    "source_record_judgment_file",
)

AUDIT_SIDECARS = (
    "assumption_match_llm.json",
    "defect_support_match_llm.json",
    "lean_to_tex_llm.json",
    # v11 direct semantic-review artifacts are first-class closeout inputs.
    # Freeze them with the transaction so a validator cannot combine a current
    # source map with a packet cache or prerequisite/library ledger written
    # midway through the same audit.
    "human_review_packet_lean_cache.json",
    "library_semantic_review.json",
    "paper_coverage_llm.json",
    "paper_semantic_prerequisites.json",
    "paper_statement_map.json",
    "review_surface_llm.json",
    "source_record_audit.json",
    "source_record_match_llm.json",
    "source_proof_fidelity.json",
    "statement_match_llm.json",
    "v11_raw_source_spec_screening.json",
)
INDEPENDENT_LANES = (
    "assumption_match_llm.json",
    "defect_support_match_llm.json",
    "lean_to_tex_llm.json",
    "paper_coverage_llm.json",
    "review_surface_llm.json",
    "source_record_match_llm.json",
    "statement_match_llm.json",
)
SOURCE_RECORD_OPTIONAL_AUTHORITY_SIDECARS = (
    "source_record_attested_selected_semantic_reuse.json",
    "source_record_auxiliary_routing_supplement.json",
    "source_record_differential_revalidation.json",
    "source_record_historical_descriptor_migration.json",
    # Schema-2 historical semantic transport is loaded indirectly through the
    # historical-descriptor lane.  It is still an authority artifact and must
    # be frozen (including explicit absence) for the whole evidence run.
    "source_record_semantic_rebind.json",
    "source_record_schema4_to5_migration.json",
    "source_record_scoped_receipt_rebind.json",
    # A narrow consumer-side structural replay is authority only when its
    # fixed receipt and, for transparent-Spec pairs, manifest authority are
    # both frozen with the raw audit transaction.
    "source_record_semantic_contract_revalidation.json",
    "lean_signature_manifest_cache_authority.json",
)

PLACEHOLDER_SOURCE_RE = re.compile(
    r"\b(?:tbd|todo|unknown|not recorded|not available)\b|"
    r"exact source location (?:to be )?refined|"
    r"paper-facing review target|"
    r"paper source location recorded by group-level|"
    r"source location recorded by group-level|"
    r"exact premise is the Lean audit-premise key",
    re.I,
)
NAME_ONLY_REASON_RE = re.compile(
    r"exactly matches current dashboard row name|"
    r"exact source-key|"
    r"\bname[-_ ]?match(?:ed|es|ing)?\b|"
    r"\bmatched by name\b",
    re.I,
)
VACUOUS_ASSUMPTION_RE = re.compile(
    r"^\s*(?:(?:noncomputable|private|protected)\s+)*"
    r"(?:def|abbrev)\s+([A-Za-z_][A-Za-z0-9_']*)\b"
    r"(?:(?!^\s*(?:def|abbrev|theorem|lemma|structure|class|inductive)\b).)*?"
    r":\s*Prop\s*:=\s*True\b",
    re.M | re.S,
)
SHA256_RE = re.compile(r"^[0-9a-fA-F]{64}$")
SOURCE_PROOF_DEFECT_ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9._-]*$")
CORRECTED_SOURCE_STATEMENT_STATUS = "corrected_source_statement"
CORRECTED_TARGET_SCHEMA = 1

# A strict source-record identity replay rehashes every external Lean artifact
# in the saved Lean-owned import closure, once before and once after its own
# TOCTOU boundary.  Coordinate only with fresh raw scans, which use the same
# repository-wide advisory lock while compiling and publishing new evidence.
# The evidence gate takes a nonblocking shared lock: it never treats a busy
# source-record scan as current evidence, and it avoids an opaque I/O fight.
SOURCE_RECORD_AUDIT_LOCK_RELATIVE_PATH = Path(".lake") / "source-record-audit.lock"
# This replays a whole Lean-owned closure and can hash thousands of external
# artifacts twice.  Match the repository's established generous-but-bounded
# paper-closeout limit rather than treating an I/O-heavy valid receipt like the
# short `lake env` discovery command used inside fresh generation.
SOURCE_RECORD_IDENTITY_HELPER_TIMEOUT_SECONDS = 600
SOURCE_RECORD_IDENTITY_PROGRESS_HEARTBEAT_SECONDS = 15.0
CORRECTED_TARGET_COVERAGE = "covered_corrected_target"
CORRECTED_TARGET_ROUTE_KIND = "approved_corrected_target"
CORRECTED_TARGET_ROUTE_RELATION = "proves_approved_corrected_target"
CORRECTED_TARGET_APPROVAL_KINDS = {
    "explicit_user_instruction",
    "documented_source_correction",
    "documented_author_correction",
}
APPROVED_CORRECTED_TARGET_MATCH = "matches_approved_corrected_target"
PAPER_COVERAGE_ROW_SIGNATURE_PROMPT_VERSION = (
    "paper-coverage-v6-verbatim-source-anchor-proof-row-signature-pins"
)
DIRECT_PAPER_COVERAGE_JUDGMENTS = {
    "covered",
    "covered_by_rows",
    "conditional_boundary",
    "covered_with_boundary",
    CORRECTED_TARGET_COVERAGE,
}
LEGACY_SOURCE_DIGEST_KEYS = {
    "source_file_sha256",
    "source_pdf_sha256",
    "source_tex_sha256",
    "source_text_sha256",
}
SOURCE_PROOF_FIDELITY_REVIEW_STATUSES = {
    "not_started",
    "reviewed_no_defects",
    "defects_recorded",
}
SOURCE_PROOF_FIDELITY_SCHEMAS = {1, 2}
SOURCE_PROOF_FIDELITY_SCOPE_OUTCOMES = {"no_defect", "defect_recorded"}
SOURCE_PROOF_FIDELITY_DEFECT_KINDS = {
    "algebra_or_sign",
    "inequality_direction",
    "quantifier_or_uniformity",
    "domain_or_endpoint",
    "index_or_integrality",
    "event_or_measure",
    "normalization_or_scaling",
    "logical_dependency",
    "model_semantics",
    "other",
}
SOURCE_PROOF_FIDELITY_STATEMENT_IMPACTS = {
    "proof_only",
    "source_statement",
    "uncertain",
}
SOURCE_PROOF_FIDELITY_STATUS_IMPACTS = {
    "formalized_note",
    "formalized_with_caveat",
    "partially_formalized",
}
SOURCE_PROOF_FIDELITY_RESOLUTIONS = {
    "repaired_in_lean",
    "open_proof_obligation",
    "corrected_source_statement",
    "resolved_in_current_source",
    "user_approved_scope_exclusion",
}
DEEP_AUDIT_OBSERVATION_LINK_FIELD = "deep_audit_observation_ids"
DEEP_AUDIT_OBSERVATION_NORMAL_SCOPE_DISPOSITION = (
    "unnumbered_prose_outside_named_theory"
)
DEEP_AUDIT_OBSERVATION_REQUIRED_FIELDS = (
    "id",
    "source_locator",
    "affected_source_locators",
    "source_claim",
    "finding",
    "repair_handoff",
    "normal_scope_disposition",
)
SOURCE_PROOF_MODEL_CONVENTION_REQUIRED_FIELDS = (
    "id",
    "source_locator",
    "classification",
    "formal_meaning",
    "why_needed",
    "checked_scope",
)
SOURCE_PROOF_CHECKED_STEP_REQUIRED_FIELDS = (
    "id",
    "source_locator",
    "source_step",
    "checked_conclusion",
    "scope",
)
# A theorem source item can contain several independently advertised claims.
# These atoms are source-first semantic inventory entries: their Lean route is
# checked only as an auditable endpoint, never used as evidence that an atom
# was present in the source.
SOURCE_CLAIM_ATOMS_SCHEMA_KEY = "source_claim_atoms_schema"
SOURCE_CLAIM_ATOMS_SCHEMA = 1
SOURCE_CLAIM_ATOMS_KEY = "source_claim_atoms"
# ``source_quote_sha256`` is intentionally optional in the general atom
# inventory.  Existing v10 maps may use source atoms as a source-first routing
# aid without opting into the v11 theorem-realization credential.  Once a map
# opts into source-Spec correspondence, however, it becomes mandatory and is
# checked against the exact current canonical source slice.
SOURCE_CLAIM_ATOM_REQUIRED_FIELDS = frozenset(
    {"id", "source_locator", "semantic_claim", "reviewed_lean_route"}
)
SOURCE_CLAIM_ATOM_SOURCE_QUOTE_SHA256_FIELD = "source_quote_sha256"
SOURCE_CLAIM_ATOM_FIELDS = frozenset(
    set(SOURCE_CLAIM_ATOM_REQUIRED_FIELDS)
    | {SOURCE_CLAIM_ATOM_SOURCE_QUOTE_SHA256_FIELD}
)
SOURCE_CLAIM_ATOM_ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.:-]*$")
SOURCE_CLAIM_ATOM_THEOREM_LIKE_KINDS = (
    THEOREM_REALIZATION_SOURCE_KINDS - {"example"}
)
# V11 scopes its theorem-realization obligation from the independently curated
# source inventory, not from a paper-authored ``claim_bearing`` switch.  The
# latter is a receipt field once an item is in scope, never permission to omit
# a named source result.  Examples may contain a source-presented mathematical
# conclusion and are included when the normal named-theory inventory retains
# them.  Explicit defect/support-only entries are handled by their dedicated
# source-fidelity lanes and cannot masquerade as proved source claims.
SOURCE_SPEC_CORRESPONDENCE_SOURCE_KINDS = THEOREM_REALIZATION_SOURCE_KINDS
SOURCE_SPEC_CORRESPONDENCE_NONCLAIM_STATUSES = (
    THEOREM_REALIZATION_NONCLAIM_STATUSES
)
# The realization correspondence is deliberately independent of the legacy
# semantic-contract schemas.  It is a new closeout lane: old maps stay
# readable, while a map that opts in must bind every individually source-pinned
# claim atom to an elaborated Spec component and account for every material
# closure node.  Neither a source-item key nor a theorem name is an identity in
# this protocol.
SOURCE_SPEC_CORRESPONDENCE_SCHEMA_KEY = "source_spec_correspondence_schema"
SOURCE_SPEC_CORRESPONDENCE_SCHEMA = 1
SOURCE_SPEC_CORRESPONDENCE_KEY = "source_spec_correspondence"
SOURCE_SPEC_CORRESPONDENCE_FIELDS = frozenset(
    {
        "schema",
        "source_atoms_sha256",
        "spec_closure_sha256",
        "spec_surface_sha256",
        "closure_environment_sha256",
        "item_identity_sha256",
        "source_atom_bindings",
        "closure_node_dispositions",
    }
)
SOURCE_SPEC_ATOM_BINDING_FIELDS = frozenset(
    {
        "source_atom_sha256",
        "spec_component_sha256s",
        "semantic_bridge",
        "overlap_justification",
    }
)
SOURCE_SPEC_NODE_DISPOSITION_FIELDS = frozenset(
    {
        "closure_component_sha256",
        "source_atom_sha256",
        "semantic_basis",
        "pinned_declaration_identity_sha256",
    }
)
SOURCE_SPEC_SEMANTIC_BASIS_FIELDS = frozenset(
    {"artifact_path", "artifact_sha256", "source_locator", "semantic_statement"}
)
SEMANTIC_CONTRACT_SCHEMA = 1
# Schema 1 remains the historical exact-proposition contract.  Schema 2 adds
# one source-model shape with its own source-pinned clauses and generated
# review obligation; accepting it must not make existing schema-1 maps stale.
SEMANTIC_CONTRACT_SCHEMA_2 = 2
SEMANTIC_CONTRACT_SCHEMAS = {
    SEMANTIC_CONTRACT_SCHEMA,
    SEMANTIC_CONTRACT_SCHEMA_2,
}


def schema_version_is_exact(value: object, expected: int) -> bool:
    """Return true only for the exact non-Boolean integer schema marker.

    Python's ``bool`` is an ``int`` subclass, so bare equality and set
    membership would otherwise let JSON ``true`` activate schema 1.  Every
    schema marker is an explicit protocol version, never a truthy flag.
    """

    return type(value) is int and value == expected


def schema_version_is_supported(value: object, supported: Iterable[int]) -> bool:
    """Return whether a non-Boolean integer is one supported schema version."""

    return type(value) is int and value in supported


# ``definitionally_realizes`` is for source *definitions*, which are semantic
# review targets rather than propositions asserted to hold.  Its evidence is
# an exact Lean-checked equivalence between the independently written Spec and
# the paper-local definition; it is not a proof of the definition as a fact.
SEMANTIC_CONTRACT_EVIDENCE_MODES = {
    "proves",
    "refutes",
    "definitionally_realizes",
}
SOURCE_CORE_PROJECTION_CLASSIFICATION = "literal_source_core"
CHECKED_STRENGTHENING_CLASSIFICATION = (
    "checked_strengthening_not_literal_source_coverage"
)
# Schema 1 can Lean-check only exact proposition proof/refutation. Specialized
# shapes need role-bearing fields and dedicated Meta checks before a label can
# count as semantic evidence.
SEMANTIC_CONTRACT_SHAPES = {"plain"}
CONDITIONAL_PROBABILITY_COMPOSITION_SEMANTIC_SHAPE = (
    "conditional_probability_composition"
)
SEMANTIC_CONTRACT_SCHEMA_2_SHAPES = {
    *SEMANTIC_CONTRACT_SHAPES,
    CONDITIONAL_PROBABILITY_COMPOSITION_SEMANTIC_SHAPE,
}
CONDITIONAL_PROBABILITY_COMPOSITION_FIELD = "conditional_probability_composition"
CONDITIONAL_PROBABILITY_COMPOSITION_CLAUSES = (
    "selector_law",
    "conditional_outcome_law",
    "composed_objective_or_expectation",
)
CONDITIONAL_PROBABILITY_COMPOSITION_CLAUSE_FIELDS = {
    "source_location",
    "source_anchor_evidence",
    "semantic_statement",
}
# A semantic-surface contract is deliberately separate from a semantic proof
# contract.  The latter checks that one Lean theorem proves one specification;
# the former makes the source-facing signature itself auditable.  In
# particular, source coverage cannot rest only on a theorem's suggestive name
# or on a bundled predicate whose contents have not been exposed on the
# PaperInterface surface.
# Schema 1 is the original lexical declaration-surface guard.  Schema 2 adds
# an optional high-assurance lane whose formula requirements are checked
# against Lean's elaborated *conclusion* rather than against arbitrary source
# text.  Schema 3 is the result-only, exact-primitive contract used for new
# high-risk rows: it deliberately has no lexical term or structural-token
# fields, because those can otherwise be satisfied by a premise or a familiar
# helper name.
SEMANTIC_SURFACE_LEGACY_SCHEMA = 1
SEMANTIC_SURFACE_SCHEMA = 2
SEMANTIC_SURFACE_RESULT_SCHEMA = 3
SEMANTIC_SURFACE_SCHEMAS = {
    SEMANTIC_SURFACE_LEGACY_SCHEMA,
    SEMANTIC_SURFACE_SCHEMA,
    SEMANTIC_SURFACE_RESULT_SCHEMA,
}
SEMANTIC_SURFACE_STRUCTURAL_TOKENS = {
    "∀",
    "∃",
    "∧",
    "∨",
    "↔",
    "→",
    "=",
    "≠",
    "<",
    "≤",
    ">",
    "≥",
    "/",
    "if",
    "match",
    "∫",
    "∑",
}
SEMANTIC_SURFACE_V1_FIELDS = {
    "schema",
    "required_structural_tokens",
    "required_terms",
    "forbidden_opaque_terms",
}
SEMANTIC_SURFACE_CONCLUSION_COMPONENT_FIELDS = {
    "selector",
    "relation",
    "left_operand",
    "required_semantic_features",
    "required_constant_suffixes",
    "min_matches",
}
SEMANTIC_SURFACE_CONCLUSION_SELECTORS = {
    "rightmost_top_level_conjunct",
    "any_result_component",
}
SEMANTIC_SURFACE_CONCLUSION_RELATIONS = {"eq", "iff", "lt", "le"}
SEMANTIC_SURFACE_CONCLUSION_LEFT_OPERANDS = {"zero"}
# These are mathematical operator categories, not declaration-route labels.
# Their exact canonical Lean constants are interpreted by audit_repository.py
# after elaboration.
SEMANTIC_SURFACE_CONCLUSION_FEATURES = {
    "addition",
    "conditional",
    "division",
    "exponential",
    "integral",
    "multiplication",
    "subtraction",
    "sum",
}
SEMANTIC_SURFACE_V2_FIELDS = (
    SEMANTIC_SURFACE_V1_FIELDS | {"required_conclusion_components"}
)
# Schema 3 is intentionally compact.  Every requirement is evaluated against
# the elaborated result atom by audit_repository.py; no declaration, binder,
# proof, or source-text spelling is evidence.
SEMANTIC_SURFACE_RESULT_FEATURES = {
    "addition",
    "conditional",
    "continuous",
    "density",
    "density_coercion",
    "division",
    "differentiable",
    "exponential",
    "finite_sum",
    "finite_cardinality",
    "finite_nonempty",
    "integral",
    "measure_map",
    "measure_comp_prod",
    "measure_pi",
    "measure_product",
    "multiplication",
    "measure_dirac",
    "pmf_map",
    "pmf_to_measure",
    "power",
    "subtraction",
    "tendsto",
}
SEMANTIC_SURFACE_RESULT_CAPTURE_FEATURES = {
    *SEMANTIC_SURFACE_RESULT_FEATURES,
    # This is structural: it captures the argument of an exact PMF-to-measure
    # operation rather than recognizing an implementation helper by its name.
    "pmf_law",
}
SEMANTIC_SURFACE_RESULT_PATTERN_FIELDS = {
    "id",
    "relation",
    "all_features",
    "minimum_feature_counts",
    "canonical_sha256",
    "operand_patterns",
    "require_distinct_operands",
    "guard_patterns",
    "quantifier_shape",
    "capture",
    "equality_alias_capture",
    "allow_leaf_reuse",
    "requires_captures",
    "requires_equality_aliases",
    "min_matches",
}
SEMANTIC_SURFACE_RESULT_OPERAND_PATTERN_FIELDS = {
    "side",
    "all_features",
    "minimum_feature_counts",
    "requires_captures",
    "requires_equality_aliases",
}
SEMANTIC_SURFACE_RESULT_OPERAND_SIDES = {"left", "right", "argument"}
SEMANTIC_SURFACE_RESULT_GUARD_PATTERN_FIELDS = {
    "relation",
    "all_features",
    "minimum_feature_counts",
    "canonical_sha256",
}
SEMANTIC_SURFACE_RESULT_QUANTIFIER_FIELDS = {"forall", "exists"}
SEMANTIC_SURFACE_ASSUMPTION_PATTERN_FIELDS = {
    "id",
    "relation",
    "all_features",
    "minimum_feature_counts",
    "min_matches",
}
SEMANTIC_SURFACE_RESULT_RELATIONS = {"any", "eq", "iff", "lt", "le", "not"}
SEMANTIC_SURFACE_RESULT_CAPTURE_FIELDS = {
    "feature",
    "as",
    "distinct_from",
    "mode",
}
SEMANTIC_SURFACE_RESULT_CAPTURE_MODES = {"root", "opposite_relation_operand"}
# A directional equality bridge.  ``alias_side`` selects the Eq operand that
# must recur verbatim in a later asserted result leaf; the opposite operand
# must expose exactly one ``construction_feature`` subtree.  This is
# structural evidence only: it never follows equality rewrites or names.
SEMANTIC_SURFACE_RESULT_EQUALITY_ALIAS_CAPTURE_FIELDS = {
    "alias_side",
    "construction_feature",
    "as",
}
SEMANTIC_SURFACE_V3_FIELDS = {
    "schema",
    "outer_binder_sha256",
    "required_result_patterns",
    "required_assumption_patterns",
}
SOURCE_PROOF_LOCATOR_RE = re.compile(
    r"(?:"
    r"\b(?:page|p\.?)\s*\d+|"
    r"\b(?:appendix|section|theorem|lemma|proposition|corollary|definition|"
    r"equation|claim|proof)\s+(?:[A-Z]?\d[\w.()/-]*|[A-Z](?:\.\d+)*)|"
    r"\b[\w./-]+\.(?:tex|txt|md|pdf):\d+"
    r")",
    re.I,
)
SOURCE_FILE_LINE_RE = re.compile(
    r"(?P<path>[A-Za-z0-9_./-]+\.(?:tex|txt|md|pdf)):"
    r"(?P<start>\d+)(?:-(?P<end>\d+))?",
    re.I,
)
TEXT_SOURCE_SUFFIXES = {".tex", ".txt", ".md"}
SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY = "source_anchor_evidence_required"
SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY = "source_named_result_inventory_review"
SOURCE_NAMED_RESULT_INVENTORY_REVIEW_SCHEMA = 1
NON_NAMED_COMPUTATIONAL_ILLUSTRATION = "non_named_computational_illustration"
# This is deliberately a source-scope disposition rather than a statement-map
# key convention.  It is only available when the exact quoted source text says
# that an observation remains unresolved; it cannot classify an ordinary
# mathematical claim as non-claim-bearing.
SOURCE_DECLARED_OPEN_NONRESULT_OBSERVATION = (
    "source_declared_open_nonresult_observation"
)
SOURCE_DECLARED_OPEN_NONRESULT_RE = re.compile(
    r"""
    (?ix)
    (?:
        \b(?:remains?|is)\s+(?:an\s+)?open\s+(?:question|problem|issue|case)\b
      | \b(?:we|the\s+(?:paper|work|article))\s+(?:leave|do\s+not\s+(?:resolve|settle|know))
        (?:(?![.!?;\n]).){0,120}?\bopen\b
      | \b(?:open\s+(?:question|problem|issue)|future\s+work)\b
      | \bconjecture\b
      | \b(?:it\s+is\s+not\s+known|remains?\s+unresolved)\b
    )
    """,
    re.IGNORECASE | re.VERBOSE,
)
# A source-declared open observation may describe an unresolved formula, but it
# cannot also carry a positive result in the same anchored excerpt.  This is
# intentionally source-language only; map keys and Lean declaration spelling
# are not inputs.
SOURCE_POSITIVE_RESULT_PRESENTATION_RE = re.compile(
    r"""
    (?ix)
    (?:
        \b(?:we|this\s+(?:paper|work|article)|our\s+(?:main\s+)?(?:result|analysis))\b
        (?:(?![.!?;\n]).){0,100}?
        \b(?:prove|show|establish|demonstrate|derive|obtain|give|provide|guarantee|ensure)\b
      | \b(?:theorem|lemma|proposition|corollary|claim)\b
        (?:(?![.!?;\n]).){0,100}?
        \b(?:proves?|shows?|establishes?|demonstrates?|guarantees?|asserts?)\b
    )
    """,
    re.IGNORECASE | re.VERBOSE,
)
USER_APPROVED_SCOPE_EXCLUSION = "user_approved_scope_exclusion"
USER_APPROVED_SCOPE_EXCLUSION_SCHEMA = 1
USER_APPROVED_SCOPE_EXCLUSION_APPROVAL_KIND = "explicit_user_instruction"
USER_APPROVED_SCOPE_EXCLUSION_TIMESTAMP_RE = re.compile(
    r"^\d{4}-\d{2}-\d{2}(?:[T ][0-2]\d:[0-5]\d(?::[0-5]\d(?:\.\d+)?)?(?:Z|[+-][0-2]\d:[0-5]\d)?)?$"
)
SOURCE_ANCHOR_EVIDENCE_FIELDS = {
    "path",
    "line_start",
    "line_end",
    "quoted_text",
    "quoted_text_sha256",
}
# Source-map context is deliberately a source-text-only lane.  It exposes a
# convention or domain restriction that matters when reviewing the expanded
# Lean surface, but it is never a proof route or a substitute for a theorem
# statement/contract.  Keep the schema small enough that a Lean declaration or
# function name cannot be smuggled in as purported semantic evidence.
SEMANTIC_CONTEXT_REQUIREMENTS_KEY = "semantic_context_requirements"
SEMANTIC_CONTEXT_REQUIREMENT_FIELDS = {
    "semantic_role",
    "kind",
    "source_location",
    "explanation",
    "source_anchor_evidence",
}
SEMANTIC_CONTEXT_ROLES = frozenset(
    {
        "definition",
        "model",
        "model_construction",
        "scope",
        "prior_result",
        "stated_antecedent",
    }
)
SEMANTIC_CONTEXT_REQUIREMENT_KIND_RE = re.compile(
    r"^[a-z][a-z0-9_]*(?:[.-][a-z][a-z0-9_]*)*$"
)
# A source can define a type/class partition *by* equality of a source feature
# vector.  That is stronger than the common one-way implementation condition
# that equal labels have equal features.  This opt-in source context makes the
# two logical directions independently auditable without treating a record,
# field, binder, or declaration spelling as evidence.
EQUALITY_DEFINED_PARTITION_CONTEXT_KIND = "equality_defined_partition"
EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD = "equality_partition_contract"
EQUALITY_DEFINED_PARTITION_CONTRACT_SCHEMA = 1
EQUALITY_DEFINED_PARTITION_RELATION = "feature_equality_iff_class_equality"
EQUALITY_DEFINED_PARTITION_REQUIRED_DIRECTIONS = {
    "feature_equality_implies_class_equality",
    "class_equality_implies_feature_equality",
}
EQUALITY_DEFINED_PARTITION_CONTRACT_FIELDS = {
    "schema",
    "relation",
    "feature_description",
    "class_description",
    "required_directions",
}

# A game-theoretic source statement can quantify a best response over every
# feasible action while evaluating some actions through a posterior,
# conditional expectation, or other observation-contingent value.  Such a
# value is not automatically defined on an observation branch of probability
# zero.  This opt-in source context makes the totality question an explicit,
# source-pinned review obligation.  It is deliberately selected only by the
# source-map context and its byte-verified quote, never by a Lean theorem,
# predicate, field, binder, or function name.
STRATEGIC_OBSERVATION_TOTALITY_CONTEXT_KIND = "strategic_observation_totality"
STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD = (
    "strategic_observation_totality_contract"
)
# Schema 2 safely represents one conditionalization mode. Schema 3 preserves
# that form while allowing one source route to use several distinct modes, for
# example a positive selected event together with an a.e. posterior kernel.
STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONTRACT_SCHEMA = 2
STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMA = 3
STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMAS = {
    STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONTRACT_SCHEMA,
    STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMA,
}
STRATEGIC_OBSERVATION_TOTALITY_ACTION_SCOPES = {
    "all_feasible_actions",
    "source_defined_restricted_action_domain",
}
STRATEGIC_OBSERVATION_TOTALITY_VALUE_KINDS = {
    "conditional_expectation_or_posterior",
    "observation_contingent_payoff_or_belief",
}
# A conditional value can be taken on the entire source population, a source
# subgroup/access event, or an already conditioned/restricted population.  A
# source map must say which semantic carrier is being selected; an arbitrary
# Lean measure restriction is not source credit merely because it gives a
# convenient conditional-expectation route.
STRATEGIC_OBSERVATION_TOTALITY_CONDITIONING_POPULATION_SCOPES = {
    "entire_source_population",
    "source_defined_subpopulation_or_access_event",
    "source_defined_conditioned_or_restricted_population",
}
# Sequential games must make the selected event's history explicit.  The
# single-action value is intentionally available for static games, but it is a
# source-semantic declaration rather than an inference from local names.
STRATEGIC_OBSERVATION_TOTALITY_SELECTED_EVENT_HISTORY_SCOPES = {
    "single_action_without_prior_strategic_history",
    "source_defined_sequential_action_history",
    "source_defined_pre_action_state_or_history",
}
# These modes determine how a conditional value is meaningful.  In
# particular, an RCD/disintegration only supplies a version on an a.e. base;
# it cannot silently support a pointwise fibre claim.
STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES = {
    "positive_measurable_event",
    "source_totalized_pointwise_observation_branch",
    "ae_regular_conditional_distribution_or_disintegration",
}
STRATEGIC_OBSERVATION_TOTALITY_REQUIRED_CHECKS = {
    "equilibrium_action_domain",
    "observation_branch_domain",
    "zero_probability_observation_branches",
    "conditional_value_totality",
    "offpath_completion_or_infeasibility",
    "conditioning_population_carrier",
    "sequential_action_history_in_selected_event",
    "action_observation_event_measurability",
    "ae_fibre_or_base_scope",
}
STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_BASE_FIELDS = {
    "schema",
    "equilibrium_action_scope",
    "action_description",
    "observation_description",
    "conditional_value_kind",
    "conditional_value_description",
    "conditioning_population_scope",
    "conditioning_population_description",
    "selected_event_history_scope",
    "selected_event_history_description",
    "selected_event_description",
    "required_checks",
}
STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONDITIONALIZATION_SCOPE_FIELD = (
    "conditionalization_scope"
)
STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES_FIELD = (
    "conditionalization_scopes"
)
STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELDS_BY_SCHEMA = {
    STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONTRACT_SCHEMA: {
        *STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_BASE_FIELDS,
        STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONDITIONALIZATION_SCOPE_FIELD,
    },
    STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMA: {
        *STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_BASE_FIELDS,
        STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES_FIELD,
    },
}

# A conditional expectation, posterior/PBO belief, or regular conditional law
# can look source-faithful while conditioning on a strictly coarser Lean
# observation or on an unselected population.  This opt-in context records the
# source conditioning information as semantic component/stage identifiers,
# rather than trying to infer it from a theorem, function, field, or binder
# name.  The observed-component list may be empty for conditioning on the
# trivial sigma-algebra; its presence still distinguishes that case from an
# omitted contract. The source-record response then has to account for the
# corresponding Lean observation, selection stages, law population, and
# a.e./pointwise scope.
CONDITIONING_INFORMATION_CONTEXT_KIND = "conditioning_information"
CONDITIONING_INFORMATION_CONTRACT_FIELD = "conditioning_information_contract"
CONDITIONING_INFORMATION_CONTRACT_SCHEMA = 1
CONDITIONING_INFORMATION_VALUE_KINDS = {
    "conditional_expectation",
    "bayesian_or_pbo_belief",
    "conditional_law",
}
CONDITIONING_INFORMATION_LAW_POPULATIONS = {
    "raw_unselected_source_law",
    "selected_by_source_actions",
    "source_restricted_nonaction_population",
}
CONDITIONING_INFORMATION_CONDITIONALIZATION_SCOPES = {
    "positive_measurable_event",
    "pointwise_totalized_observation",
    "ae_regular_conditional_distribution_or_disintegration",
}
CONDITIONING_INFORMATION_COMPONENT_FIELDS = {"id", "description"}
CONDITIONING_INFORMATION_STAGE_FIELDS = {"id", "description"}
CONDITIONING_INFORMATION_SEMANTIC_ID_RE = re.compile(
    r"^[a-z][a-z0-9_]*(?:[.-][a-z][a-z0-9_]*)*$"
)
CONDITIONING_INFORMATION_CONTRACT_FIELDS = {
    "schema",
    "conditional_value_kind",
    "source_observed_components",
    "source_action_selection_stages",
    "source_law_population",
    "conditionalization_scopes",
}

# A source model may state primitive laws/recurrences while the Lean-facing
# theorem takes a record that already contains the material process, execution,
# cycle, or conditional-law consequence.  This opt-in source context records
# the primitive basis and conclusion that must be connected by a checked Lean
# derivation. It is keyed only by byte-pinned source content and the generated
# semantic association, not by a Lean record, field, theorem, or function name.
SOURCE_MODEL_DERIVATION_CONTEXT_KIND = "source_model_derivation"
SOURCE_MODEL_DERIVATION_CONTRACT_FIELD = "source_model_derivation_contract"
SOURCE_MODEL_DERIVATION_CONTRACT_SCHEMA = 2
SOURCE_MODEL_DERIVATION_COMPONENT_FIELDS = {
    "id",
    "description",
    "source_location",
    "source_anchor_evidence",
}
SOURCE_MODEL_DERIVATION_CONCLUSION_FIELDS = {
    "description",
    "source_location",
    "source_anchor_evidence",
}
SOURCE_MODEL_DERIVATION_CONTRACT_FIELDS = {
    "schema",
    "source_primitive_components",
    "derived_conclusion",
}


def _conditioning_information_semantic_entries_errors(
    value: object,
    *,
    field: str,
    entry_fields: set[str],
    require_nonempty: bool,
) -> list[str]:
    """Validate source-semantic component/stage entries without Lean names."""

    if not isinstance(value, list):
        return [f"{field} must be a list"]
    if require_nonempty and not value:
        return [f"{field} must be a nonempty list"]
    errors: list[str] = []
    ids: list[str] = []
    for index, entry in enumerate(value):
        prefix = f"{field}[{index}]"
        if not isinstance(entry, dict):
            errors.append(f"{prefix} must be an object")
            continue
        unexpected = sorted(set(entry) - entry_fields)
        if unexpected:
            errors.append(
                f"{prefix} has unsupported field(s): " + ", ".join(unexpected)
            )
        identifier = entry.get("id")
        if not isinstance(identifier, str) or not CONDITIONING_INFORMATION_SEMANTIC_ID_RE.fullmatch(
            identifier.strip()
        ):
            errors.append(
                f"{prefix}.id must be a lowercase source-semantic identifier"
            )
        else:
            ids.append(identifier.strip())
        description = entry.get("description")
        if not isinstance(description, str) or not description.strip():
            errors.append(
                f"{prefix}.description must be a nonempty source-semantic description"
            )
    if len(ids) != len(set(ids)):
        errors.append(f"{field} must not duplicate a semantic id")
    return errors


def conditioning_information_context_contract_errors(
    requirement: object,
) -> list[str]:
    """Validate source conditioning information before a direct match is credited.

    The contract is deliberately source-side only.  A generated review response
    has to state the Lean-side components and compare them component-by-component
    against this byte-pinned source contract; a raw law, selected law, and RCD
    scope are not interchangeable merely because a posterior helper has a
    familiar name.
    """

    if not isinstance(requirement, dict):
        return ["must be an object"]
    contract = requirement.get(CONDITIONING_INFORMATION_CONTRACT_FIELD)
    if not isinstance(contract, dict):
        return [f"{CONDITIONING_INFORMATION_CONTRACT_FIELD} must be an object"]
    errors: list[str] = []
    unexpected = sorted(set(contract) - CONDITIONING_INFORMATION_CONTRACT_FIELDS)
    if unexpected:
        errors.append(
            f"{CONDITIONING_INFORMATION_CONTRACT_FIELD} has unsupported field(s): "
            + ", ".join(unexpected)
        )
    if not schema_version_is_exact(
        contract.get("schema"), CONDITIONING_INFORMATION_CONTRACT_SCHEMA
    ):
        errors.append(
            f"{CONDITIONING_INFORMATION_CONTRACT_FIELD}.schema must be "
            f"{CONDITIONING_INFORMATION_CONTRACT_SCHEMA}"
        )
    value_kind = str(contract.get("conditional_value_kind") or "").strip()
    if value_kind not in CONDITIONING_INFORMATION_VALUE_KINDS:
        errors.append(
            f"{CONDITIONING_INFORMATION_CONTRACT_FIELD}.conditional_value_kind "
            "must identify a conditional expectation, Bayesian/PBO belief, or "
            "conditional law"
        )
    errors.extend(
        _conditioning_information_semantic_entries_errors(
            contract.get("source_observed_components"),
            field=(
                f"{CONDITIONING_INFORMATION_CONTRACT_FIELD}."
                "source_observed_components"
            ),
            entry_fields=CONDITIONING_INFORMATION_COMPONENT_FIELDS,
            require_nonempty=False,
        )
    )
    errors.extend(
        _conditioning_information_semantic_entries_errors(
            contract.get("source_action_selection_stages"),
            field=(
                f"{CONDITIONING_INFORMATION_CONTRACT_FIELD}."
                "source_action_selection_stages"
            ),
            entry_fields=CONDITIONING_INFORMATION_STAGE_FIELDS,
            require_nonempty=False,
        )
    )
    law_population = str(contract.get("source_law_population") or "").strip()
    if law_population not in CONDITIONING_INFORMATION_LAW_POPULATIONS:
        errors.append(
            f"{CONDITIONING_INFORMATION_CONTRACT_FIELD}.source_law_population "
            "must say whether the source law is raw/unselected, selected by source "
            "actions, or restricted by a nonaction source population"
        )
    stages = contract.get("source_action_selection_stages")
    has_stages = isinstance(stages, list) and bool(stages)
    if law_population == "raw_unselected_source_law" and has_stages:
        errors.append(
            f"{CONDITIONING_INFORMATION_CONTRACT_FIELD} cannot list action-selection "
            "stages for a raw_unselected_source_law"
        )
    if law_population == "selected_by_source_actions" and not has_stages:
        errors.append(
            f"{CONDITIONING_INFORMATION_CONTRACT_FIELD} must list ordered "
            "source_action_selection_stages for a selected_by_source_actions law"
        )
    raw_scopes = contract.get("conditionalization_scopes")
    scopes = (
        [scope.strip() for scope in raw_scopes]
        if isinstance(raw_scopes, list) and all(isinstance(scope, str) for scope in raw_scopes)
        else []
    )
    if (
        not scopes
        or len(scopes) != len(raw_scopes)
        or len(set(scopes)) != len(scopes)
        or any(
            scope not in CONDITIONING_INFORMATION_CONDITIONALIZATION_SCOPES
            for scope in scopes
        )
    ):
        errors.append(
            f"{CONDITIONING_INFORMATION_CONTRACT_FIELD}.conditionalization_scopes "
            "must be a nonempty duplicate-free list of positive-event, pointwise "
            "totalized, or a.e. RCD/disintegration scopes"
        )
    return errors


def _source_model_derivation_component_anchor_errors(
    entry: dict[str, Any],
    *,
    field: str,
) -> list[str]:
    """Require one independently byte-pinned source basis component.

    The later canonical-source pass verifies the line slice and digest. This
    shape pass rejects the easier failure mode first: treating a broad parent
    context quote as evidence for a separately claimed primitive or conclusion.
    """

    errors: list[str] = []
    location = entry.get("source_location")
    matches = list(SOURCE_FILE_LINE_RE.finditer(location)) if isinstance(location, str) else []
    if not isinstance(location, str) or not location.strip() or len(matches) != 1:
        errors.append(
            f"{field}.source_location must contain exactly one source anchor for "
            "this primitive or derived conclusion"
        )
    raw_anchors = entry.get("source_anchor_evidence")
    if not isinstance(raw_anchors, list) or not raw_anchors:
        errors.append(
            f"{field}.source_anchor_evidence must be a nonempty byte-pinned "
            "source-anchor list for this primitive or derived conclusion"
        )
    else:
        for index, raw_anchor in enumerate(raw_anchors):
            prefix = f"{field}.source_anchor_evidence[{index}]"
            if not isinstance(raw_anchor, dict):
                errors.append(f"{prefix} must be an object")
                continue
            missing = sorted(SOURCE_ANCHOR_EVIDENCE_FIELDS - set(raw_anchor))
            if missing:
                errors.append(
                    f"{prefix} is missing required field(s): " + ", ".join(missing)
                )
    return errors


def source_model_derivation_context_contract_errors(
    requirement: object,
) -> list[str]:
    """Validate an opt-in source primitive-to-consequence contract.

    The contract deliberately lives on the source side. Every primitive and
    the derived conclusion carries its own byte-pinned source anchor, rather
    than relying on one broadly relevant parent quote. A later generated
    semantic-model row has to account for every primitive and can receive a
    direct-match verdict only through a checked derivation, rather than by
    accepting the consequence as record data.
    """

    if not isinstance(requirement, dict):
        return ["must be an object"]
    contract = requirement.get(SOURCE_MODEL_DERIVATION_CONTRACT_FIELD)
    if not isinstance(contract, dict):
        return [f"{SOURCE_MODEL_DERIVATION_CONTRACT_FIELD} must be an object"]
    errors: list[str] = []
    unexpected = sorted(set(contract) - SOURCE_MODEL_DERIVATION_CONTRACT_FIELDS)
    if unexpected:
        errors.append(
            f"{SOURCE_MODEL_DERIVATION_CONTRACT_FIELD} has unsupported field(s): "
            + ", ".join(unexpected)
        )
    if not schema_version_is_exact(
        contract.get("schema"), SOURCE_MODEL_DERIVATION_CONTRACT_SCHEMA
    ):
        errors.append(
            f"{SOURCE_MODEL_DERIVATION_CONTRACT_FIELD}.schema must be "
            f"{SOURCE_MODEL_DERIVATION_CONTRACT_SCHEMA}"
        )
    primitive_field = (
        f"{SOURCE_MODEL_DERIVATION_CONTRACT_FIELD}.source_primitive_components"
    )
    raw_primitives = contract.get("source_primitive_components")
    errors.extend(
        _conditioning_information_semantic_entries_errors(
            raw_primitives,
            field=primitive_field,
            entry_fields=SOURCE_MODEL_DERIVATION_COMPONENT_FIELDS,
            require_nonempty=True,
        )
    )
    if isinstance(raw_primitives, list):
        for index, primitive in enumerate(raw_primitives):
            if not isinstance(primitive, dict):
                continue
            errors.extend(
                _source_model_derivation_component_anchor_errors(
                    primitive,
                    field=f"{primitive_field}[{index}]",
                )
            )
    derived = contract.get("derived_conclusion")
    if not isinstance(derived, dict):
        errors.append(
            f"{SOURCE_MODEL_DERIVATION_CONTRACT_FIELD}.derived_conclusion "
            "must be an object"
        )
    else:
        unexpected_derived = sorted(
            set(derived) - SOURCE_MODEL_DERIVATION_CONCLUSION_FIELDS
        )
        if unexpected_derived:
            errors.append(
                f"{SOURCE_MODEL_DERIVATION_CONTRACT_FIELD}.derived_conclusion "
                "has unsupported field(s): "
                + ", ".join(unexpected_derived)
            )
        description = derived.get("description")
        if not isinstance(description, str) or not description.strip():
            errors.append(
                f"{SOURCE_MODEL_DERIVATION_CONTRACT_FIELD}.derived_conclusion."
                "description must be a nonempty source-semantic description"
            )
        errors.extend(
            _source_model_derivation_component_anchor_errors(
                derived,
                field=(
                    f"{SOURCE_MODEL_DERIVATION_CONTRACT_FIELD}.derived_conclusion"
                ),
            )
        )
    return errors


def equality_defined_partition_context_contract_errors(
    requirement: object,
) -> list[str]:
    """Validate the source-only exact-partition context payload.

    This validates metadata declared by the source-map author, not a Lean
    route.  The exact source quote is checked by the normal context-anchor
    lane.  Requiring both directions here prevents a map from asking only
    whether a formalization has the easier within-class agreement direction.
    """

    if not isinstance(requirement, dict):
        return ["must be an object"]
    contract = requirement.get(EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD)
    if not isinstance(contract, dict):
        return [
            f"{EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD} must be an object"
        ]
    errors: list[str] = []
    unexpected = sorted(
        set(contract) - EQUALITY_DEFINED_PARTITION_CONTRACT_FIELDS
    )
    if unexpected:
        errors.append(
            f"{EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD} has unsupported field(s): "
            + ", ".join(unexpected)
        )
    if not schema_version_is_exact(
        contract.get("schema"), EQUALITY_DEFINED_PARTITION_CONTRACT_SCHEMA
    ):
        errors.append(
            f"{EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD}.schema must be "
            f"{EQUALITY_DEFINED_PARTITION_CONTRACT_SCHEMA}"
        )
    if contract.get("relation") != EQUALITY_DEFINED_PARTITION_RELATION:
        errors.append(
            f"{EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD}.relation must be "
            f"`{EQUALITY_DEFINED_PARTITION_RELATION}`"
        )
    for field in ("feature_description", "class_description"):
        if not isinstance(contract.get(field), str) or not str(
            contract.get(field) or ""
        ).strip():
            errors.append(
                f"{EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD}.{field} "
                "must be a nonempty source-semantic description"
            )
    directions = contract.get("required_directions")
    if not isinstance(directions, list):
        errors.append(
            f"{EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD}.required_directions "
            "must be a list containing both equality directions"
        )
    else:
        normalized = [
            direction.strip()
            for direction in directions
            if isinstance(direction, str) and direction.strip()
        ]
        if (
            len(normalized) != len(directions)
            or len(set(normalized)) != len(normalized)
            or set(normalized) != EQUALITY_DEFINED_PARTITION_REQUIRED_DIRECTIONS
        ):
            errors.append(
                f"{EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD}.required_directions "
                "must contain exactly `feature_equality_implies_class_equality` "
                "and `class_equality_implies_feature_equality`"
            )
    return errors


def strategic_observation_totality_context_contract_errors(
    requirement: object,
) -> list[str]:
    """Validate a source-pinned game-observation totality requirement.

    The schema records only the source semantics that make an off-path review
    necessary.  It does not assert that the source is safe: the generated
    semantic-model response must separately establish totality, infeasibility,
    or an explicitly restricted equilibrium domain.
    """

    if not isinstance(requirement, dict):
        return ["must be an object"]
    contract = requirement.get(STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD)
    if not isinstance(contract, dict):
        return [
            f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD} must be an object"
        ]
    errors: list[str] = []
    schema = contract.get("schema")
    schema_is_supported = (
        isinstance(schema, int)
        and not isinstance(schema, bool)
        and schema in STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMAS
    )
    allowed_fields = STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELDS_BY_SCHEMA.get(
        schema if schema_is_supported else None,
        set().union(*STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELDS_BY_SCHEMA.values()),
    )
    unexpected = sorted(set(contract) - allowed_fields)
    if unexpected:
        errors.append(
            f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD} has unsupported field(s): "
            + ", ".join(unexpected)
        )
    if not schema_is_supported:
        errors.append(
            f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD}.schema must be "
            f"{STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONTRACT_SCHEMA} or "
            f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMA}"
        )
    action_scope = str(contract.get("equilibrium_action_scope") or "").strip()
    if action_scope not in STRATEGIC_OBSERVATION_TOTALITY_ACTION_SCOPES:
        errors.append(
            f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD}.equilibrium_action_scope "
            "must state whether the source quantifies all feasible actions or a "
            "source-defined restricted action domain"
        )
    value_kind = str(contract.get("conditional_value_kind") or "").strip()
    if value_kind not in STRATEGIC_OBSERVATION_TOTALITY_VALUE_KINDS:
        errors.append(
            f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD}.conditional_value_kind "
            "must identify a conditional/posterior or observation-contingent value"
        )
    conditioning_population_scope = str(
        contract.get("conditioning_population_scope") or ""
    ).strip()
    if (
        conditioning_population_scope
        not in STRATEGIC_OBSERVATION_TOTALITY_CONDITIONING_POPULATION_SCOPES
    ):
        errors.append(
            f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD}."
            "conditioning_population_scope must identify whether the conditional "
            "value is taken on the whole source population, a source subgroup/access "
            "event, or a source-conditioned/restricted population"
        )
    selected_event_history_scope = str(
        contract.get("selected_event_history_scope") or ""
    ).strip()
    if (
        selected_event_history_scope
        not in STRATEGIC_OBSERVATION_TOTALITY_SELECTED_EVENT_HISTORY_SCOPES
    ):
        errors.append(
            f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD}."
            "selected_event_history_scope must state whether the selected event has "
            "no prior strategic history, source-defined sequential action history, or "
            "a source-defined pre-action state/history"
        )
    if schema == STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONTRACT_SCHEMA:
        conditionalization_scope = str(
            contract.get(
                STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONDITIONALIZATION_SCOPE_FIELD
            )
            or ""
        ).strip()
        if (
            conditionalization_scope
            not in STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES
        ):
            errors.append(
                f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD}."
                f"{STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONDITIONALIZATION_SCOPE_FIELD} "
                "must identify a positive measurable event, a source-totalized "
                "pointwise branch, or an a.e. regular conditional "
                "distribution/disintegration"
            )
    elif schema == STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMA:
        raw_scopes = contract.get(
            STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES_FIELD
        )
        scopes = (
            [scope.strip() for scope in raw_scopes]
            if isinstance(raw_scopes, list)
            and all(isinstance(scope, str) for scope in raw_scopes)
            else []
        )
        if (
            not scopes
            or len(scopes) != len(raw_scopes)
            or len(set(scopes)) != len(scopes)
            or any(
                scope not in STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES
                for scope in scopes
            )
        ):
            errors.append(
                f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD}."
                f"{STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES_FIELD} "
                "must be a nonempty duplicate-free list of positive measurable-event, "
                "source-totalized pointwise-branch, or a.e. regular-conditional "
                "distribution/disintegration scopes"
            )
    for field in (
        "action_description",
        "observation_description",
        "conditional_value_description",
        "conditioning_population_description",
        "selected_event_history_description",
        "selected_event_description",
    ):
        if not isinstance(contract.get(field), str) or not str(
            contract.get(field) or ""
        ).strip():
            errors.append(
                f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD}.{field} "
                "must be a nonempty source-semantic description"
            )
    raw_checks = contract.get("required_checks")
    if not isinstance(raw_checks, list):
        errors.append(
            f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD}.required_checks "
            "must list every totality check"
        )
    else:
        checks = [
            check.strip()
            for check in raw_checks
            if isinstance(check, str) and check.strip()
        ]
        if (
            len(checks) != len(raw_checks)
            or len(set(checks)) != len(checks)
            or set(checks) != STRATEGIC_OBSERVATION_TOTALITY_REQUIRED_CHECKS
        ):
            errors.append(
                f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD}.required_checks "
                "must contain every equilibrium-domain, observation-branch, "
                "zero-probability, conditional-value, and off-path check exactly once"
            )
    return errors


@dataclass(frozen=True)
class Finding:
    severity: str
    paper: str
    path: str
    message: str

    def format(self) -> str:
        return f"[{self.severity}] {self.paper} {self.path}: {self.message}"


def _immutable_json_error(*_args: object, **_kwargs: object) -> None:
    raise TypeError("evidence run snapshots are immutable")


class _FrozenJSONDict(dict[str, Any]):
    """A ``dict``-compatible recursive read view for legacy validators."""

    __setitem__ = _immutable_json_error
    __delitem__ = _immutable_json_error
    clear = _immutable_json_error
    pop = _immutable_json_error
    popitem = _immutable_json_error
    setdefault = _immutable_json_error
    update = _immutable_json_error
    __ior__ = _immutable_json_error

    def __copy__(self) -> dict[str, Any]:
        return dict(self)

    def __deepcopy__(self, memo: dict[int, Any]) -> dict[str, Any]:
        return copy.deepcopy(dict(self), memo)


class _FrozenJSONList(list[Any]):
    """A ``list``-compatible recursive read view for legacy validators."""

    __setitem__ = _immutable_json_error
    __delitem__ = _immutable_json_error
    append = _immutable_json_error
    clear = _immutable_json_error
    extend = _immutable_json_error
    insert = _immutable_json_error
    pop = _immutable_json_error
    remove = _immutable_json_error
    reverse = _immutable_json_error
    sort = _immutable_json_error
    __iadd__ = _immutable_json_error
    __imul__ = _immutable_json_error

    def __copy__(self) -> list[Any]:
        return list(self)

    def __deepcopy__(self, memo: dict[int, Any]) -> list[Any]:
        return copy.deepcopy(list(self), memo)


_FROZEN_DICT_SUBCLASS_BY_BASE: dict[type[Any], type[dict[str, Any]]] = {}


def _frozen_dict_subclass(base: type[Any]) -> type[dict[str, Any]]:
    """Preserve private loader-token subclasses while disabling mutation."""

    if base is dict or base is _FrozenJSONDict:
        return _FrozenJSONDict
    cached = _FROZEN_DICT_SUBCLASS_BY_BASE.get(base)
    if cached is not None:
        return cached
    attributes = {
        "__slots__": (),
        "__setitem__": _immutable_json_error,
        "__delitem__": _immutable_json_error,
        "clear": _immutable_json_error,
        "pop": _immutable_json_error,
        "popitem": _immutable_json_error,
        "setdefault": _immutable_json_error,
        "update": _immutable_json_error,
        "__ior__": _immutable_json_error,
        "__copy__": _FrozenJSONDict.__copy__,
        "__deepcopy__": _FrozenJSONDict.__deepcopy__,
        "__module__": __name__,
    }
    frozen = type(f"_Frozen{base.__name__}", (base,), attributes)
    _FROZEN_DICT_SUBCLASS_BY_BASE[base] = frozen
    return frozen


def _freeze_json(value: Any, *, preserve_dict_subclasses: bool = False) -> Any:
    if isinstance(value, dict):
        frozen_type = (
            _frozen_dict_subclass(type(value))
            if preserve_dict_subclasses
            else _FrozenJSONDict
        )
        return frozen_type(
            {
                str(key): _freeze_json(
                    item,
                    preserve_dict_subclasses=preserve_dict_subclasses,
                )
                for key, item in value.items()
            }
        )
    if isinstance(value, list):
        return _FrozenJSONList(
            _freeze_json(
                item,
                preserve_dict_subclasses=preserve_dict_subclasses,
            )
            for item in value
        )
    return value


@dataclass(frozen=True)
class EvidenceJSONSnapshot:
    """One exact JSON input as read for a paper evidence transaction."""

    path: Path
    sha256: str | None
    payload: dict[str, Any] | None
    raw_bytes: bytes | None = None


class _EvidenceRunContextIssuerBinding:
    """Object-identity binding that does not survive ``dataclasses.replace``."""

    __slots__ = (
        "context",
        "primary_closeout_source_record_judgment_receipt",
    )

    def __init__(self) -> None:
        self.context: EvidenceRunContext | None = None
        # This is an in-memory, single-transaction capability.  It is issued
        # only by the consolidated closeout owner after its primary gate has
        # completed without errors; no JSON sidecar can manufacture it.
        self.primary_closeout_source_record_judgment_receipt: (
            _PrimaryCloseoutSourceRecordJudgmentReceipt | None
        ) = None


@dataclass(frozen=True)
class EvidenceRunContext:
    """Immutable, content-bound results shared by one paper evidence run.

    The context is deliberately run scoped.  It is neither persisted nor kept
    in a module cache: every authorization result is derived from the exact
    input snapshots below and the watched repository state recorded for this
    transaction.
    """

    folder: Path
    status: str
    audit_config_snapshot: EvidenceJSONSnapshot
    status_snapshot: EvidenceJSONSnapshot
    audit_snapshot: EvidenceJSONSnapshot
    match_snapshot: EvidenceJSONSnapshot
    statement_map_snapshot: EvidenceJSONSnapshot
    source_proof_fidelity_snapshot: EvidenceJSONSnapshot | None
    sidecar_snapshots: tuple[EvidenceJSONSnapshot, ...]
    audit_path_error: str
    match_path_error: str
    source_proof_fidelity_path_error: str
    source_record_identity_error: str
    semantic_contract_revalidation: Any | None
    semantic_contract_revalidation_error: str
    corrected_scope_findings: tuple[Finding, ...]
    corrected_scope_current: bool
    corrected_model_field_items: Mapping[str, dict[str, Any]]
    administrative_projection_rebind: Any | None
    administrative_projection_rebind_path: Path | None
    administrative_projection_rebind_error: str
    configured_assumption_regularity_context: (
        ConfiguredAssumptionFormalizationRegularityContext | None
    )
    configured_assumption_regularity_context_error: str
    current_source_record_judgments: Mapping[str, dict[str, Any]]
    auxiliary_routing_context: ValidatedAuxiliaryRoutingContext | None
    auxiliary_routing_context_error: str
    watched_input_digest: str
    # Runtime-only capability for nested current-overlay replays.  It is not
    # serialized, compared as evidence, or accepted from a sidecar.
    source_record_identity_context: object | None = dataclass_field(
        default=None,
        repr=False,
        compare=False,
    )
    _issuer_token: object | None = None

    @property
    def issued_by_builder(self) -> bool:
        """Whether the exact snapshot builder issued this transaction."""

        binding = self._issuer_token
        return (
            isinstance(binding, _EvidenceRunContextIssuerBinding)
            and binding.context is self
        )

    @property
    def status_payload(self) -> dict[str, Any]:
        return self.status_snapshot.payload or {}

    @property
    def audit_payload(self) -> dict[str, Any] | None:
        return self.audit_snapshot.payload

    @property
    def match_payload(self) -> dict[str, Any]:
        return self.match_snapshot.payload or {}

    @property
    def statement_map(self) -> dict[str, Any] | None:
        return self.statement_map_snapshot.payload

    @property
    def paper_statement_map_sha256(self) -> str:
        return self.statement_map_snapshot.sha256 or ""

    @property
    def source_proof_fidelity(self) -> dict[str, Any] | None:
        snapshot = self.source_proof_fidelity_snapshot
        return snapshot.payload if snapshot is not None else None

    @property
    def input_snapshots(self) -> tuple[EvidenceJSONSnapshot, ...]:
        snapshots = (
            self.audit_config_snapshot,
            self.status_snapshot,
            self.audit_snapshot,
            self.match_snapshot,
            self.statement_map_snapshot,
        )
        if self.source_proof_fidelity_snapshot is not None:
            snapshots += (self.source_proof_fidelity_snapshot,)
        return snapshots + self.sidecar_snapshots

    def json_snapshot(self, path: Path) -> EvidenceJSONSnapshot | None:
        """Return the exact builder-read snapshot for ``path``, if watched."""

        try:
            target = path.resolve()
        except (OSError, RuntimeError):
            return None
        for snapshot in self.input_snapshots:
            try:
                if snapshot.path.resolve() == target:
                    return snapshot
            except (OSError, RuntimeError):
                continue
        return None

    def json_payload(self, path: Path) -> dict[str, Any] | None:
        """Return only the parsed object acquired by this transaction."""

        snapshot = self.json_snapshot(path)
        return snapshot.payload if snapshot is not None else None

    def file_bytes_override(self) -> Mapping[Path, bytes | None]:
        """Return every acquired input as an immutable absolute-path byte map."""

        return MappingProxyType(
            {
                snapshot.path.resolve(): snapshot.raw_bytes
                for snapshot in self.input_snapshots
            }
        )

    def canonical_sidecar_path(self, basename: str) -> Path:
        """Resolve the canonical sidecar from the transaction's initial state."""

        organized = self.folder / "audit" / basename
        organized_snapshot = self.json_snapshot(organized)
        if organized_snapshot is not None and organized_snapshot.sha256 is not None:
            return organized
        return self.folder / basename


class _PrimaryCloseoutSourceRecordJudgmentReceipt:
    """Opaque proof that the primary closeout gate covered source judgments.

    The receipt deliberately stores object identities rather than serialized
    key lists.  It can only validate against the exact builder-issued evidence
    transaction that minted it, and it evaporates when the process exits.
    """

    __slots__ = (
        "context",
        "status_snapshot",
        "audit_snapshot",
        "match_snapshot",
        "statement_map_snapshot",
    )

    def __init__(self, context: EvidenceRunContext) -> None:
        self.context = context
        self.status_snapshot = context.status_snapshot
        self.audit_snapshot = context.audit_snapshot
        self.match_snapshot = context.match_snapshot
        self.statement_map_snapshot = context.statement_map_snapshot


def _issue_primary_closeout_source_record_judgment_receipt(
    context: object,
) -> bool:
    """Publish one exact primary-gate pass to deferred evidence integrity.

    This is intentionally an internal, non-CLI bridge.  Its only production
    caller is the consolidated closeout owner, after the primary paper gate
    has returned without an error.  The capability is bound to the builder's
    object-identity issuer rather than a caller-supplied Boolean, source key,
    or persisted marker.
    """

    if not isinstance(context, EvidenceRunContext) or not context.issued_by_builder:
        return False
    binding = context._issuer_token
    if (
        not isinstance(binding, _EvidenceRunContextIssuerBinding)
        or binding.context is not context
    ):
        return False
    binding.primary_closeout_source_record_judgment_receipt = (
        _PrimaryCloseoutSourceRecordJudgmentReceipt(context)
    )
    return True


def _has_current_primary_closeout_source_record_judgment_receipt(
    context: object,
) -> bool:
    """Accept only the exact in-process primary-gate receipt for ``context``."""

    if not isinstance(context, EvidenceRunContext) or not context.issued_by_builder:
        return False
    binding = context._issuer_token
    if (
        not isinstance(binding, _EvidenceRunContextIssuerBinding)
        or binding.context is not context
    ):
        return False
    receipt = binding.primary_closeout_source_record_judgment_receipt
    return bool(
        isinstance(receipt, _PrimaryCloseoutSourceRecordJudgmentReceipt)
        and receipt.context is context
        and receipt.status_snapshot is context.status_snapshot
        and receipt.audit_snapshot is context.audit_snapshot
        and receipt.match_snapshot is context.match_snapshot
        and receipt.statement_map_snapshot is context.statement_map_snapshot
    )


EVIDENCE_DIAGNOSTIC_CONTEXTS = "evidence_contexts_built"
EVIDENCE_DIAGNOSTIC_WATCH_DIGESTS = "watched_input_digests"
EVIDENCE_DIAGNOSTIC_IDENTITY_VALIDATIONS = "source_record_identity_validations"
EVIDENCE_DIAGNOSTIC_CURRENT_JUDGMENTS = "current_judgment_materializations"
EVIDENCE_DIAGNOSTIC_CORRECTED_SCOPE = "corrected_scope_evaluations"
EVIDENCE_DIAGNOSTIC_INPUT_MUTATIONS = "watched_input_mutations"


def _increment_diagnostic(
    diagnostics: MutableMapping[str, int] | None, key: str
) -> None:
    if diagnostics is not None:
        diagnostics[key] = diagnostics.get(key, 0) + 1


def unique_findings(findings: Iterable[Finding]) -> list[Finding]:
    """Preserve order while collapsing equivalent conclusions from audit lanes."""
    seen: set[tuple[str, str, str, str]] = set()
    unique: list[Finding] = []
    for finding in findings:
        key = (finding.severity, finding.paper, finding.path, finding.message)
        if key not in seen:
            seen.add(key)
            unique.append(finding)
    return unique


def load_json(path: Path) -> dict[str, Any] | None:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return payload if isinstance(payload, dict) else None


def _path_content_sha256(path: Path) -> str | None:
    """Return only a file's exact byte digest; never parse it."""

    try:
        return hashlib.sha256(path.read_bytes()).hexdigest()
    except OSError:
        return None


def _load_json_snapshot(path: Path) -> EvidenceJSONSnapshot:
    """Read and hash a JSON input once without canonicalizing its bytes."""

    try:
        raw = path.read_bytes()
    except OSError:
        return EvidenceJSONSnapshot(
            path=path, sha256=None, payload=None, raw_bytes=None
        )
    digest = hashlib.sha256(raw).hexdigest()
    try:
        payload = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError):
        payload = None
    return EvidenceJSONSnapshot(
        path=path,
        sha256=digest,
        payload=_freeze_json(payload) if isinstance(payload, dict) else None,
        raw_bytes=raw,
    )


def _exact_file_bytes(
    path: Path,
    file_bytes_override: Mapping[Path, bytes | None] | None,
) -> bytes:
    """Read one file, or require it from an exact frozen-input mapping."""

    if file_bytes_override is None:
        return path.read_bytes()
    resolved = path.resolve()
    if resolved not in file_bytes_override:
        raise RuntimeError(f"frozen input bundle omits {resolved}")
    raw = file_bytes_override[resolved]
    if raw is None:
        raise FileNotFoundError(resolved)
    if not isinstance(raw, bytes):
        raise RuntimeError(f"frozen input bundle has non-byte content for {resolved}")
    return raw


def paper_dirs(
    paper_filter: str | None = None,
    *,
    public_complete: bool = False,
) -> list[Path]:
    folders = sorted(
        path.parent
        for path in PAPERS.glob("*/status.json")
        if path.parent.name != "TEMPLATE"
    )
    if public_complete:
        selected: list[Path] = []
        for folder in folders:
            status, payload = paper_status(folder)
            if "repository_visibility" not in payload:
                raise ValueError(
                    f"{rel(folder / 'status.json')}: public release requires an "
                    "explicit repository_visibility (`public` or `private_only`)"
                )
            raw_visibility = payload.get("repository_visibility")
            if not isinstance(raw_visibility, str):
                visibility = ""
            else:
                visibility = raw_visibility.strip().lower()
            if visibility not in REPOSITORY_VISIBILITIES:
                expected = ", ".join(sorted(REPOSITORY_VISIBILITIES))
                raise ValueError(
                    f"{rel(folder / 'status.json')}: repository_visibility must be "
                    f"one of {expected}, got {raw_visibility!r}"
                )
            if visibility == "public" and status in FULL_CLOSEOUT_STATUSES:
                selected.append(folder)
        folders = selected
    if paper_filter is not None:
        folders = [folder for folder in folders if folder.name == paper_filter]
    return folders


def paper_status(folder: Path) -> tuple[str, dict[str, Any]]:
    payload = load_json(folder / "status.json") or {}
    return str(payload.get("status") or "").strip().lower(), payload


def finding_severity(status: str) -> str:
    return "ERROR" if status in CLOSEOUT_STATUSES else "WARN"


def source_record_judgment_freshness_severity(status: str) -> str:
    return "ERROR" if status in FULL_CLOSEOUT_STATUSES else "WARN"


def rel(path: Path) -> str:
    try:
        return str(path.relative_to(ROOT))
    except ValueError:
        return str(path)


def canonical_sidecar(folder: Path, basename: str) -> Path:
    organized = folder / "audit" / basename
    return organized if organized.exists() else folder / basename


def transaction_sidecar(
    folder: Path,
    basename: str,
    context: EvidenceRunContext | None = None,
) -> Path:
    """Resolve a sidecar from the initial transaction state when available."""

    if context is not None and context.folder == folder.resolve():
        return context.canonical_sidecar_path(basename)
    return canonical_sidecar(folder, basename)


def transaction_json(
    path: Path,
    context: EvidenceRunContext | None = None,
) -> dict[str, Any] | None:
    """Load JSON once per transaction, falling back only in standalone mode."""

    return context.json_payload(path) if context is not None else load_json(path)


def walk_values(value: Any, prefix: tuple[str, ...] = ()) -> Iterable[tuple[tuple[str, ...], Any]]:
    if isinstance(value, dict):
        for key, item in value.items():
            item_prefix = prefix + (str(key),)
            yield item_prefix, item
            yield from walk_values(item, item_prefix)
    elif isinstance(value, list):
        for index, item in enumerate(value):
            item_prefix = prefix + (str(index),)
            yield item_prefix, item
            yield from walk_values(item, item_prefix)


def sidecar_has_items(payload: dict[str, Any]) -> bool:
    for key in ("items", "judgments"):
        value = payload.get(key)
        if isinstance(value, dict) and value:
            return True
        if isinstance(value, list) and value:
            return True
    return "judgment" in payload


def validators(payload: dict[str, Any]) -> set[str]:
    out: set[str] = set()
    for path, value in walk_values(payload):
        if path and path[-1] in {
            "validator",
            "model",
            "judge",
            "agent",
            "generator",
            "translator",
            "producer",
        }:
            text = str(value or "").strip()
            if text:
                out.add(text)
    return out


def identities_for_keys(payload: dict[str, Any], keys: set[str]) -> set[str]:
    """Collect free-form producer attestations for explicit workflow roles."""

    identities: set[str] = set()
    for path, value in walk_values(payload):
        if path and path[-1] in keys:
            identity = str(value or "").strip()
            if identity:
                identities.add(identity)
    return identities


def legacy_source_digest_locations(payload: dict[str, Any]) -> list[str]:
    """Return legacy digest fields that cannot identify bytes to verify."""

    locations: list[str] = []
    for path, _value in walk_values(payload):
        if path and path[-1] in LEGACY_SOURCE_DIGEST_KEYS:
            locations.append(".".join(path))
        elif path and path[-1] == "source_artifact_sha256" and len(path) != 1:
            locations.append(".".join(path))
    return sorted(set(locations))


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def canonical_json_payload(payload: Any) -> Any:
    """Canonicalize JSON data exactly like the source-record scope helper."""

    if isinstance(payload, dict):
        return {
            key: canonical_json_payload(value)
            for key, value in sorted(payload.items())
        }
    if isinstance(payload, list):
        return sorted(
            (canonical_json_payload(value) for value in payload),
            key=lambda value: json.dumps(value, sort_keys=True, separators=(",", ":")),
        )
    return payload


def canonical_json_digest(payload: Any) -> str:
    """Hash JSON data after recursively sorting maps and correction lists.

    Corrected-model approval is about the content of every recorded correction,
    not about the incidental order in which the status file lists them.
    """

    encoded = json.dumps(
        canonical_json_payload(payload), sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def canonical_governing_corrections(
    status_payload: dict[str, Any],
) -> list[dict[str, Any]] | None:
    """Return every governing correction in a stable, content-complete order."""

    raw_corrections = status_payload.get("governing_corrections")
    if not isinstance(raw_corrections, list) or not raw_corrections:
        return None
    corrections: list[dict[str, Any]] = []
    seen_ids: set[str] = set()
    for correction in raw_corrections:
        if not isinstance(correction, dict):
            return None
        correction_id = str(correction.get("id") or "").strip()
        if not correction_id or correction_id in seen_ids:
            return None
        seen_ids.add(correction_id)
        corrections.append(canonical_json_payload(correction))
    return sorted(
        corrections,
        key=lambda correction: json.dumps(correction, sort_keys=True, separators=(",", ":")),
    )


def governing_corrections_sha256(status_payload: dict[str, Any]) -> str | None:
    """Return the current full-content governing-correction digest."""

    corrections = canonical_governing_corrections(status_payload)
    return canonical_json_digest(corrections) if corrections is not None else None


def author_approved_corrected_scope(
    status_payload: dict[str, Any] | None,
) -> dict[str, Any] | None:
    """Return the explicit corrected target, never inferred from a status word."""

    if not isinstance(status_payload, dict):
        return None
    scope = status_payload.get("formalization_scope")
    if not isinstance(scope, dict):
        return None
    if str(scope.get("kind") or "").strip() != AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE:
        return None
    return scope


def corrected_model_scope_role(scope: object) -> tuple[str | None, str]:
    """Return one explicit corrected-scope role without a status-name fallback.

    Both fields are mandatory.  Corrected-target metadata may grant a
    whole-paper waiver only when that authority is explicitly declared; old or
    partially migrated records fail closed instead of inheriting it.
    """

    if not isinstance(scope, dict):
        return None, "formalization_scope must be an object"
    raw_role = scope.get("scope_role")
    raw_claim = scope.get("whole_paper_closeout_claimed")
    if raw_role is None and raw_claim is None:
        return (
            None,
            "formalization_scope must explicitly declare scope_role and "
            "whole_paper_closeout_claimed",
        )
    if not isinstance(raw_role, str) or not raw_role.strip():
        return None, "formalization_scope.scope_role must be a nonempty string"
    role = raw_role.strip()
    if role not in CORRECTED_MODEL_SCOPE_ROLES:
        return (
            None,
            "formalization_scope.scope_role must be one of: "
            + ", ".join(sorted(CORRECTED_MODEL_SCOPE_ROLES)),
        )
    if not isinstance(raw_claim, bool):
        return (
            None,
            "formalization_scope.whole_paper_closeout_claimed must be Boolean "
            "when scope_role is declared",
        )
    expected_claim = role == WHOLE_PAPER_CLOSEOUT_SCOPE_ROLE
    if raw_claim is not expected_claim:
        return (
            None,
            "formalization_scope.scope_role `"
            + role
            + "` conflicts with whole_paper_closeout_claimed="
            + str(raw_claim).lower(),
        )
    return role, ""


def _paper_local_artifact_path(folder: Path, raw_path: object) -> Path | None:
    """Resolve a declared paper-local artifact without permitting path escape."""

    if not isinstance(raw_path, str) or not raw_path.strip():
        return None
    candidate = Path(raw_path.strip())
    if candidate.is_absolute():
        return None
    resolved_folder = folder.resolve()
    resolved = (folder / candidate).resolve()
    try:
        resolved.relative_to(resolved_folder)
    except ValueError:
        return None
    return resolved


def _nonempty_string_list(value: object) -> list[str] | None:
    if not isinstance(value, list):
        return None
    items = [str(item).strip() for item in value if isinstance(item, str) and item.strip()]
    if len(items) != len(value) or not items or len(set(items)) != len(items):
        return None
    return sorted(items)


def _is_fully_qualified_lean_identity(value: str) -> bool:
    """Return whether one value is a non-short Lean declaration identity.

    The generator resolves these names independently.  This structural check
    only prevents a new multi-model scope from using a display label, a short
    type tail, or a comma-separated pseudo-list as a governing model root.
    """

    return bool(re.fullmatch(r"[^\s.]+(?:\.[^\s.]+)+", value))


@dataclass(frozen=True)
class CorrectedModelScopeModelBindings:
    """Normalized governing-model roots for one corrected formalization scope.

    Legacy scopes carry one scalar model and implicitly map every target to
    it.  New scopes make the target-to-model relationship explicit so a
    schedule-specific theorem cannot silently inherit a companion model.
    """

    model_spec_declarations: tuple[str, ...]
    target_model_spec_declarations: dict[str, str]
    uses_legacy_scalar: bool


def corrected_model_scope_model_bindings(
    scope: object,
    *,
    target_result_declarations: object | None = None,
) -> tuple[CorrectedModelScopeModelBindings | None, list[str]]:
    """Normalize legacy or explicit multi-model corrected-scope metadata.

    New metadata must provide both ``model_spec_declarations`` and an exact
    ``target_model_spec_declarations`` map.  A legacy scalar remains accepted
    unchanged and is normalized by mapping every declared target to it.
    """

    if not isinstance(scope, dict):
        return None, ["must be an object"]
    raw_targets = (
        scope.get("target_result_declarations")
        if target_result_declarations is None
        else target_result_declarations
    )
    targets = _nonempty_string_list(raw_targets)
    if targets is None:
        return None, ["requires unique nonempty target_result_declarations"]

    has_multi_fields = (
        "model_spec_declarations" in scope
        or "target_model_spec_declarations" in scope
    )
    raw_scalar = scope.get("model_spec_declaration")
    scalar = raw_scalar.strip() if isinstance(raw_scalar, str) else ""
    if not has_multi_fields:
        if not scalar:
            return None, ["requires a nonempty governing model_spec_declaration"]
        return (
            CorrectedModelScopeModelBindings(
                model_spec_declarations=(scalar,),
                target_model_spec_declarations={target: scalar for target in targets},
                uses_legacy_scalar=True,
            ),
            [],
        )

    errors: list[str] = []
    if raw_scalar is not None:
        errors.append(
            "must not combine legacy model_spec_declaration with multi-model metadata"
        )
    models = _nonempty_string_list(scope.get("model_spec_declarations"))
    if models is None:
        errors.append("requires unique nonempty model_spec_declarations")
        models = []
    elif any(not _is_fully_qualified_lean_identity(model) for model in models):
        errors.append("model_spec_declarations must contain fully qualified Lean identities")

    raw_target_models = scope.get("target_model_spec_declarations")
    target_models: dict[str, str] = {}
    if not isinstance(raw_target_models, dict):
        errors.append("requires target_model_spec_declarations object")
    else:
        for raw_target, raw_model in raw_target_models.items():
            if not isinstance(raw_target, str) or not raw_target.strip():
                errors.append(
                    "target_model_spec_declarations has a nonempty-string target key requirement"
                )
                continue
            if not isinstance(raw_model, str) or not raw_model.strip():
                errors.append(
                    "target_model_spec_declarations has a nonempty-string model value requirement"
                )
                continue
            target = raw_target.strip()
            model = raw_model.strip()
            if target in target_models:
                errors.append(
                    "target_model_spec_declarations has duplicate normalized target keys"
                )
                continue
            target_models[target] = model
        if set(target_models) != set(targets):
            errors.append(
                "target_model_spec_declarations must map exactly every target_result_declaration"
            )
        for target, model in target_models.items():
            if not _is_fully_qualified_lean_identity(target):
                errors.append(
                    "target_model_spec_declarations target keys must be fully qualified Lean identities"
                )
            if not _is_fully_qualified_lean_identity(model):
                errors.append(
                    "target_model_spec_declarations values must be fully qualified Lean identities"
                )
            elif model not in models:
                errors.append(
                    "target_model_spec_declarations values must be declared model_spec_declarations"
                )
    if errors:
        return None, errors
    return (
        CorrectedModelScopeModelBindings(
            model_spec_declarations=tuple(models),
            target_model_spec_declarations={
                target: target_models[target] for target in sorted(target_models)
            },
            uses_legacy_scalar=False,
        ),
        [],
    )


def corrected_model_scope_model_metadata(
    bindings: CorrectedModelScopeModelBindings,
) -> dict[str, object]:
    """Return the canonical persisted shape for normalized model bindings."""

    if bindings.uses_legacy_scalar:
        return {"model_spec_declaration": bindings.model_spec_declarations[0]}
    return {
        "model_spec_declarations": list(bindings.model_spec_declarations),
        "target_model_spec_declarations": {
            target: bindings.target_model_spec_declarations[target]
            for target in sorted(bindings.target_model_spec_declarations)
        },
    }


def corrected_model_contract_dimensions(schema: object) -> set[str] | None:
    """Return the dimension set pinned by one corrected-model contract schema.

    Schema 2 is a historical record format.  It is intentionally not upgraded
    in place: doing so would make old evidence appear to have reviewed new
    probability semantics.  New schema-3 contracts must review all eight
    dimensions.
    """

    if schema_version_is_exact(schema, CORRECTED_MODEL_LEGACY_CONTRACT_SCHEMA):
        return CORRECTED_MODEL_LEGACY_SEMANTIC_DIMENSIONS
    if schema_version_is_exact(schema, CORRECTED_MODEL_CONTRACT_SCHEMA):
        return CORRECTED_MODEL_SEMANTIC_DIMENSIONS
    return None


def corrected_model_raw_item_freshness_mode(
    item: object,
) -> tuple[str | None, str]:
    """Classify a raw corrected-model item by its generated freshness mode.

    An item-level digest is valid only when the generator explicitly marked the
    item reusable.  Conversely, an explicitly non-reusable item may be covered
    only by the contract's current aggregate source-record audit pin.  This
    keeps an absent source identity from becoming a name-based synthetic item
    key while still requiring a complete fresh audit of its semantic surface.
    """

    if not isinstance(item, dict):
        return None, "must be an object"
    eligibility = item.get("source_record_item_reuse_eligibility")
    if not isinstance(eligibility, dict):
        return None, "requires generated source_record_item_reuse_eligibility"
    eligible = eligibility.get("eligible")
    blockers = eligibility.get("blockers")
    if not isinstance(eligible, bool) or not isinstance(blockers, list) or any(
        not isinstance(blocker, str) or not blocker.strip() for blocker in blockers
    ):
        return None, "has malformed source_record_item_reuse_eligibility"

    digest = str(item.get("source_record_item_sha256") or "").strip()
    metadata_error = reusable_item_metadata_error(
        item,
        expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
    )
    if metadata_error:
        return None, metadata_error
    if eligible:
        if blockers:
            return None, "is reusable but lists item-reuse blockers"
        if not SHA256_RE.fullmatch(digest):  # defensive: helper already checks this
            return None, "is reusable but lacks a SHA-256 item digest"
        return "item", ""

    if not blockers:
        return None, "is aggregate-only but has no item-reuse blocker"
    generated_item_fields = (
        "source_record_item_digest_schema",
        "source_record_item_semantic_id",
        "source_record_item_context_sha256",
        "source_record_item_sha256",
    )
    if any(item.get(field) not in (None, "", []) for field in generated_item_fields):
        return None, "is aggregate-only but retains item-level digest metadata"
    return "aggregate", ""


def corrected_model_mapping_freshness_error(
    mapping: object,
    item: object,
) -> str:
    """Return an exact/aggregate freshness error for one contract mapping."""

    if not isinstance(mapping, dict):
        return "must be an object"
    mode, item_error = corrected_model_raw_item_freshness_mode(item)
    if item_error:
        return f"references a raw item that {item_error}"
    mapped_digest_value = mapping.get("source_record_item_sha256")
    if mapped_digest_value is None:
        mapped_digest = ""
    elif isinstance(mapped_digest_value, str):
        mapped_digest = mapped_digest_value.strip()
    else:
        return "has a non-string source_record_item_sha256"
    aggregate_only = mapping.get("aggregate_audit_freshness_only")
    if mode == "item":
        if aggregate_only not in (None, False):
            return "claims aggregate-only freshness for a reusable raw item"
        raw_digest = str(item.get("source_record_item_sha256") or "").strip()
        if mapped_digest != raw_digest:
            return "is not pinned to the current expanded-item digest"
        return ""
    if aggregate_only is not True:
        return "must set aggregate_audit_freshness_only for a non-reusable raw item"
    if mapped_digest:
        return "must not retain an item digest for aggregate-only freshness"
    return ""


def corrected_model_transitively_reachable_field_items(
    audit_payload: object,
    *,
    model_spec_declaration: object | None = None,
    model_spec_declarations: object | None = None,
    target_model_spec_declarations: object | None = None,
    target_result_declarations: object,
) -> tuple[dict[str, dict[str, Any]], list[str]]:
    """Return exact field items reached through mapped corrected model records.

    The raw recursive-field collection is de-duplicated by declaration, so a
    nested field can be stored under its immediate record root rather than the
    top-level corrected-model path.  The generated semantic item's
    ``record_field_types`` retains that transitive graph.  This helper joins
    the two generated surfaces using complete declaration identities: it never
    guesses from suffixes, field spelling, or a record-name convention.

    Every path rooted at each target's declared governing model must have a
    structurally complete chain whose nodes are generated recursive-field
    items. A malformed, cross-mapped, or incomplete graph yields errors,
    rather than silently treating a nested record as covered by another
    target's model.
    """

    errors: list[str] = []
    if isinstance(target_result_declarations, tuple):
        target_result_declarations = list(target_result_declarations)
    scope_metadata: dict[str, object] = {
        "target_result_declarations": target_result_declarations,
    }
    if model_spec_declarations is not None or target_model_spec_declarations is not None:
        if model_spec_declaration is not None:
            scope_metadata["model_spec_declaration"] = model_spec_declaration
        scope_metadata["model_spec_declarations"] = model_spec_declarations
        scope_metadata["target_model_spec_declarations"] = (
            target_model_spec_declarations
        )
    else:
        scope_metadata["model_spec_declaration"] = model_spec_declaration
    model_bindings, model_binding_errors = corrected_model_scope_model_bindings(
        scope_metadata,
        target_result_declarations=target_result_declarations,
    )
    if model_binding_errors or model_bindings is None:
        return {}, [
            "governing model metadata " + error
            for error in model_binding_errors
        ]
    targets = sorted(model_bindings.target_model_spec_declarations)
    if not isinstance(audit_payload, dict):
        return {}, ["source-record audit payload must be an object"]

    raw_field_items = audit_payload.get("recursive_field_items")
    if not isinstance(raw_field_items, list):
        return {}, ["source-record audit requires a recursive_field_items list"]
    field_items: dict[str, dict[str, Any]] = {}
    field_paths: dict[str, tuple[str, ...]] = {}
    for index, raw_item in enumerate(raw_field_items):
        if not isinstance(raw_item, dict):
            errors.append(f"recursive_field_items[{index}] must be an object")
            continue
        key = str(raw_item.get("judgment_key") or "").strip()
        raw_path = str(raw_item.get("path") or "").strip()
        path_segments = tuple(segment.strip() for segment in raw_path.split(" -> "))
        if not key or key in field_items:
            errors.append(
                f"recursive_field_items[{index}] has a missing or duplicate judgment_key"
            )
            continue
        if (
            len(path_segments) < 2
            or any(not segment for segment in path_segments)
            or path_segments[-1] != key
        ):
            errors.append(
                f"recursive_field_items[{index}] lacks a structural path ending in its exact declaration"
            )
            continue
        field_items[key] = raw_item
        field_paths[key] = path_segments

    raw_semantic_items = audit_payload.get("semantic_model_items")
    if not isinstance(raw_semantic_items, list):
        return {}, errors + ["source-record audit requires a semantic_model_items list"]
    semantic_items_by_declaration: dict[str, dict[str, Any]] = {}
    for index, raw_item in enumerate(raw_semantic_items):
        if not isinstance(raw_item, dict):
            errors.append(f"semantic_model_items[{index}] must be an object")
            continue
        declaration = str(raw_item.get("qualified_declaration") or "").strip()
        if not declaration or declaration in semantic_items_by_declaration:
            errors.append(
                f"semantic_model_items[{index}] has a missing or duplicate fully qualified declaration"
            )
            continue
        semantic_items_by_declaration[declaration] = raw_item

    reachable: dict[str, dict[str, Any]] = {}
    for target in targets:
        model_spec = model_bindings.target_model_spec_declarations[target]
        model_prefix = f"{model_spec} ->"
        semantic_item = semantic_items_by_declaration.get(target)
        if semantic_item is None:
            errors.append(
                "corrected target `"
                + target
                + "` has no generated semantic-model item for its structural field graph"
            )
            continue
        surface = semantic_item.get("expanded_lean_surface")
        if not isinstance(surface, dict):
            errors.append(
                "corrected target `"
                + target
                + "` lacks an expanded_lean_surface for structural field reachability"
            )
            continue
        raw_paths = surface.get("record_field_types")
        if not isinstance(raw_paths, list):
            errors.append(
                "corrected target `"
                + target
                + "` lacks generated record_field_types for structural field reachability"
            )
            continue
        rooted_paths = 0
        for path_index, raw_path_item in enumerate(raw_paths):
            if not isinstance(raw_path_item, dict):
                errors.append(
                    f"corrected target `{target}` record_field_types[{path_index}] must be an object"
                )
                continue
            raw_path = str(raw_path_item.get("path") or "").strip()
            if not raw_path.startswith(model_prefix):
                continue
            rooted_paths += 1
            segments = tuple(segment.strip() for segment in raw_path.split(" -> "))
            if (
                len(segments) < 2
                or segments[0] != model_spec
                or any(not segment for segment in segments)
            ):
                errors.append(
                    f"corrected target `{target}` has malformed generated model-field path `{raw_path}`"
                )
                continue
            terminal = segments[-1]
            terminal_item = field_items.get(terminal)
            if terminal_item is None:
                errors.append(
                    "corrected target `"
                    + target
                    + "` generated model-field path terminates at `"
                    + terminal
                    + "`, which has no exact recursive-field item"
                )
                continue
            # Every intermediate edge must name a generated field declaration.
            # This is what makes the route transitive structural evidence rather
            # than a string prefix that happens to begin with the model name.
            missing_intermediate = [
                segment for segment in segments[1:-1] if segment not in field_items
            ]
            if missing_intermediate:
                errors.append(
                    "corrected target `"
                    + target
                    + "` generated model-field path has no exact recursive-field item for "
                    + ", ".join(sorted(set(missing_intermediate)))
                )
                continue
            terminal_field_path = field_paths.get(terminal, ())
            if len(terminal_field_path) < 2 or terminal_field_path[-1] != terminal:
                errors.append(
                    "corrected target `"
                    + target
                    + "` terminal field `"
                    + terminal
                    + "` has no structurally valid recursive-field path"
                )
                continue
            reachable[terminal] = terminal_item
        if rooted_paths == 0:
            errors.append(
                "corrected target `"
                + target
                + "` has no generated record-field path rooted at its mapped governing model `"
                + model_spec
                + "`"
            )
    return reachable, errors


def component_corrected_scope_findings(
    folder: Path,
    status: str,
    raw_scope: dict[str, Any],
    status_payload: dict[str, Any],
) -> list[Finding]:
    """Validate an approved component boundary without granting source credit.

    A component scope records exactly what the user approved, but it is not a
    substitute for the ordinary source-map, fidelity-ledger, source-record, or
    closeout checks.  In particular, it deliberately does not validate a
    semantic contract or return a value that any waiver path can consume.
    """

    findings: list[Finding] = []
    path = rel(folder / "status.json")

    def add(message: str) -> None:
        findings.append(Finding("ERROR", folder.name, path, message))

    if status in FULL_CLOSEOUT_STATUSES:
        add(
            "component_level_evidence_only formalization_scope cannot support "
            f"full-closeout status `{status}`"
        )
    if raw_scope.get("whole_paper_closeout_claimed") is not False:
        add(
            "component_level_evidence_only formalization_scope must set "
            "whole_paper_closeout_claimed to false"
        )
    if str(raw_scope.get("kind") or "").strip() != AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE:
        add(
            "component-level formalization_scope.kind must be "
            f"`{AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE}`"
        )
    if not str(raw_scope.get("scope_id") or "").strip():
        add("component-level formalization_scope requires a nonempty scope_id")
    if raw_scope.get("archival_equivalence_claimed") is not False:
        add(
            "component-level formalization_scope must set "
            "archival_equivalence_claimed to false"
        )
    _model_bindings, model_binding_errors = corrected_model_scope_model_bindings(
        raw_scope
    )
    for error in model_binding_errors:
        add("component-level formalization_scope " + error)

    approval = raw_scope.get("approval")
    if not isinstance(approval, dict):
        add("component-level formalization_scope requires approval metadata")
    else:
        approval_path = _paper_local_artifact_path(folder, approval.get("artifact_path"))
        approval_digest = str(approval.get("artifact_sha256") or "").strip().lower()
        if not str(approval.get("recorded_at") or "").strip():
            add("component corrected-target approval requires recorded_at")
        if not str(approval.get("statement") or "").strip():
            add("component corrected-target approval requires a precise statement")
        if approval_path is None or not approval_path.is_file():
            add("component corrected-target approval artifact_path must name an existing paper-local file")
        elif not SHA256_RE.fullmatch(approval_digest) or sha256_file(approval_path) != approval_digest:
            add("component corrected-target approval artifact_sha256 is stale or malformed")

    base_archive = raw_scope.get("base_archive")
    if not isinstance(base_archive, dict):
        add("component-level formalization_scope requires base_archive metadata")
    else:
        archive_path = _paper_local_artifact_path(folder, base_archive.get("path"))
        archive_digest = str(base_archive.get("sha256") or "").strip().lower()
        if archive_path is None or not archive_path.is_file():
            add("component corrected-target base_archive.path must name an existing paper-local archive")
        elif not SHA256_RE.fullmatch(archive_digest) or sha256_file(archive_path) != archive_digest:
            add("component corrected-target base_archive.sha256 is stale or malformed")

    correction_ids = _nonempty_string_list(raw_scope.get("correction_ids"))
    if correction_ids is None:
        add("component-level formalization_scope requires unique nonempty correction_ids")
    else:
        governing = {
            str(item.get("id") or "").strip()
            for item in status_payload.get("governing_corrections") or []
            if isinstance(item, dict) and str(item.get("id") or "").strip()
        }
        if not set(correction_ids).issubset(governing):
            add(
                "component-level formalization_scope.correction_ids must cite declared "
                "governing_corrections"
            )
    return findings


def _corrected_model_scope_contract_findings(
    folder: Path,
    status: str,
    status_payload: dict[str, Any],
    *,
    audit_payload_override: object = _UNSET,
    prevalidated_source_record_identity_error: object = _UNSET,
    validated_field_items_out: MutableMapping[str, dict[str, Any]] | None = None,
    artifact_snapshots_override: (
        Mapping[Path, EvidenceJSONSnapshot] | None
    ) = None,
) -> list[Finding]:
    """Validate an author-approved corrected target as a separate source scope.

    This is deliberately not a waiver for a stale source audit.  It requires a
    pinned author-approved correction artifact, a current structural
    source-record digest, complete semantic-dimension coverage, and a mapping
    for each expanded field of the corrected model record.  The archived TeX
    remains pinned as a distinct baseline and may not be claimed equivalent.
    """

    raw_scope = status_payload.get("formalization_scope")
    if raw_scope is None:
        return []
    severity = finding_severity(status)
    if not isinstance(raw_scope, dict):
        return [
            Finding(
                severity,
                folder.name,
                rel(folder / "status.json"),
                "formalization_scope must be an object when declared",
            )
        ]
    scope_role, scope_role_error = corrected_model_scope_role(raw_scope)
    if scope_role_error:
        return [
            Finding(severity, folder.name, rel(folder / "status.json"), scope_role_error)
        ]
    # This branch is intentionally before the legacy whole-paper contract.
    # Component metadata, even malformed beyond the role pair, must never fall
    # through to a waiver-capable path.
    if scope_role == COMPONENT_LEVEL_EVIDENCE_ONLY_SCOPE_ROLE:
        return component_corrected_scope_findings(
            folder, status, raw_scope, status_payload
        )
    kind = str(raw_scope.get("kind") or "").strip()
    if kind != AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE:
        return [
            Finding(
                severity,
                folder.name,
                rel(folder / "status.json"),
                "formalization_scope.kind must be "
                f"`{AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE}` when a corrected target is declared",
            )
        ]
    if scope_role != WHOLE_PAPER_CLOSEOUT_SCOPE_ROLE:
        return [
            Finding(
                severity,
                folder.name,
                rel(folder / "status.json"),
                "formalization_scope has no waiver-capable whole-paper role",
            )
        ]

    findings: list[Finding] = []

    def artifact_snapshot(path: Path | None) -> EvidenceJSONSnapshot | None:
        if path is None or artifact_snapshots_override is None:
            return None
        try:
            return artifact_snapshots_override.get(path.resolve())
        except (OSError, RuntimeError):
            return None

    def artifact_digest(path: Path | None) -> str | None:
        if artifact_snapshots_override is None:
            if path is None or not path.exists():
                return None
            try:
                return sha256_file(path)
            except OSError:
                return None
        snapshot = artifact_snapshot(path)
        return snapshot.sha256 if snapshot is not None else None

    def add(message: str) -> None:
        findings.append(
            Finding(severity, folder.name, rel(folder / "status.json"), message)
        )

    scope_id = str(raw_scope.get("scope_id") or "").strip()
    if not scope_id:
        add("author-approved corrected formalization_scope requires a nonempty scope_id")
    if raw_scope.get("archival_equivalence_claimed") is not False:
        add(
            "author-approved corrected formalization_scope must set "
            "archival_equivalence_claimed to false"
        )
    targets = _nonempty_string_list(raw_scope.get("target_result_declarations"))
    if targets is None:
        add(
            "author-approved corrected formalization_scope requires unique nonempty "
            "target_result_declarations"
        )
        targets = []
    scope_model_bindings, scope_model_binding_errors = (
        corrected_model_scope_model_bindings(
            raw_scope,
            target_result_declarations=targets,
        )
    )
    for error in scope_model_binding_errors:
        add("author-approved corrected formalization_scope " + error)
    correction_ids = _nonempty_string_list(raw_scope.get("correction_ids"))
    if correction_ids is None:
        add(
            "author-approved corrected formalization_scope requires unique nonempty correction_ids"
        )
        correction_ids = []

    approval = raw_scope.get("approval")
    if not isinstance(approval, dict):
        add("author-approved corrected formalization_scope requires approval metadata")
        approval = {}
    approval_path = _paper_local_artifact_path(folder, approval.get("artifact_path"))
    approval_digest = str(approval.get("artifact_sha256") or "").strip().lower()
    if not str(approval.get("recorded_at") or "").strip():
        add("corrected-model approval requires recorded_at")
    if not str(approval.get("statement") or "").strip():
        add("corrected-model approval requires a precise statement")
    approval_actual_digest = artifact_digest(approval_path)
    if approval_path is None or approval_actual_digest is None:
        add("corrected-model approval artifact_path must name an existing paper-local file")
    if not SHA256_RE.fullmatch(approval_digest):
        add("corrected-model approval artifact_sha256 must be a SHA-256 digest")
    elif approval_actual_digest is not None and approval_actual_digest != approval_digest:
        add("corrected-model approval artifact_sha256 does not match its tracked artifact")

    base_archive = raw_scope.get("base_archive")
    if not isinstance(base_archive, dict):
        add("author-approved corrected formalization_scope requires base_archive metadata")
        base_archive = {}
    archive_path = _paper_local_artifact_path(folder, base_archive.get("path"))
    archive_digest = str(base_archive.get("sha256") or "").strip().lower()
    archive_actual_digest = artifact_digest(archive_path)
    if archive_path is None or archive_actual_digest is None:
        add("corrected-model base_archive.path must name an existing paper-local archive")
    if not SHA256_RE.fullmatch(archive_digest):
        add("corrected-model base_archive.sha256 must be a SHA-256 digest")
    elif archive_actual_digest is not None and archive_actual_digest != archive_digest:
        add("corrected-model base_archive.sha256 does not match its pinned archive")

    corrections = status_payload.get("governing_corrections")
    if not isinstance(corrections, list):
        add("corrected-model status requires a governing_corrections list")
        corrections = []
    correction_by_id: dict[str, dict[str, Any]] = {}
    for index, correction in enumerate(corrections):
        if not isinstance(correction, dict):
            add(f"governing_corrections[{index}] must be an object")
            continue
        correction_id = str(correction.get("id") or "").strip()
        if not correction_id or correction_id in correction_by_id:
            add(f"governing_corrections[{index}] has a missing or duplicate id")
            continue
        correction_by_id[correction_id] = correction
        for key in ("clause", "source_anchor", "relation", "model_evidence"):
            if not str(correction.get(key) or "").strip():
                add(f"governing correction `{correction_id}` requires {key}")
        if correction.get("does_not_claim_archive_derivation") is not True:
            add(
                f"governing correction `{correction_id}` must explicitly reject an archive-derivation claim"
            )
    if correction_ids and set(correction_ids) != set(correction_by_id):
        add(
            "formalization_scope.correction_ids must exactly match governing_corrections ids"
        )
    correction_digest = governing_corrections_sha256(status_payload)
    if correction_digest is None:
        add("corrected-model status has no canonicalizable governing_corrections content")

    contract_ref = raw_scope.get("semantic_contract")
    if not isinstance(contract_ref, dict):
        add("author-approved corrected formalization_scope requires semantic_contract metadata")
        return findings
    contract_path = _paper_local_artifact_path(folder, contract_ref.get("path"))
    contract_digest = str(contract_ref.get("sha256") or "").strip().lower()
    contract_snapshot = artifact_snapshot(contract_path)
    contract_actual_digest = artifact_digest(contract_path)
    if contract_path is None or contract_actual_digest is None:
        add("corrected-model semantic_contract.path must name an existing paper-local file")
        return findings
    if not SHA256_RE.fullmatch(contract_digest):
        add("corrected-model semantic_contract.sha256 must be a SHA-256 digest")
        return findings
    if contract_actual_digest != contract_digest:
        add("corrected-model semantic_contract.sha256 does not match its tracked artifact")
        return findings
    contract = (
        contract_snapshot.payload
        if contract_snapshot is not None
        else load_json(contract_path)
    )
    if not isinstance(contract, dict):
        add("corrected-model semantic contract must be valid JSON")
        return findings
    contract_dimension_set = corrected_model_contract_dimensions(contract.get("schema"))
    if contract_dimension_set is None:
        add("corrected-model semantic contract has an unsupported schema")
        # Continue with the current shape only to provide useful diagnostics
        # for the remaining fields. The unsupported-schema finding is already
        # fail-closed.
        contract_dimension_set = CORRECTED_MODEL_SEMANTIC_DIMENSIONS
    expected_contract_values = {
        "scope_id": scope_id,
        "approval_artifact_sha256": approval_digest,
        "base_archive_sha256": archive_digest,
    }
    for key, expected in expected_contract_values.items():
        if str(contract.get(key) or "").strip().lower() != str(expected).strip().lower():
            add(f"corrected-model semantic contract `{key}` does not match formalization_scope")
    if _nonempty_string_list(contract.get("target_result_declarations")) != targets:
        add("corrected-model semantic contract target_result_declarations do not match scope")
    contract_model_bindings, contract_model_binding_errors = (
        corrected_model_scope_model_bindings(
            contract,
            target_result_declarations=targets,
        )
    )
    for error in contract_model_binding_errors:
        add("corrected-model semantic contract " + error)
    if (
        scope_model_bindings is not None
        and contract_model_bindings is not None
        and scope_model_bindings != contract_model_bindings
    ):
        add(
            "corrected-model semantic contract governing model bindings do not match "
            "formalization_scope"
        )
    if _nonempty_string_list(contract.get("correction_ids")) != correction_ids:
        add("corrected-model semantic contract correction_ids do not match scope")
    contract_correction_digest = str(
        contract.get("governing_corrections_sha256") or ""
    ).strip()
    if not SHA256_RE.fullmatch(contract_correction_digest) or contract_correction_digest != str(
        correction_digest or ""
    ):
        add(
            "corrected-model semantic contract governing_corrections_sha256 does not match "
            "the complete current correction content"
        )
    if contract.get("archival_equivalence_claimed") is not False:
        add("corrected-model semantic contract must set archival_equivalence_claimed to false")
    dimensions = contract.get("semantic_dimensions")
    if not isinstance(dimensions, list) or set(dimensions) != contract_dimension_set:
        add("corrected-model semantic contract must cover every semantic-model dimension")

    audit_path, audit_path_error = source_record_review_sidecar_path(
        folder,
        status_payload,
        config_field="source_record_audit_file",
        default_basename="source_record_audit.json",
    )
    if audit_path_error:
        add(audit_path_error)
        return findings
    assert audit_path is not None
    audit_payload = (
        load_json(audit_path)
        if audit_payload_override is _UNSET
        else audit_payload_override
    )
    if not isinstance(audit_payload, dict):
        add("corrected-model formalization requires a current source-record audit payload")
        return findings
    if prevalidated_source_record_identity_error is _UNSET:
        audit_identity_error = source_record_audit_identity_error(
            audit_payload,
            expected_paper_statement_map_sha256=current_paper_statement_map_sha256(
                folder
            ),
            folder=folder,
        )
    else:
        audit_identity_error = str(prevalidated_source_record_identity_error)
    if audit_identity_error:
        add(
            "corrected-model formalization requires a current generated source-record "
            "audit: "
            + audit_identity_error
        )
    expected_import_module = f"{folder.name}.PaperInterface"
    if str(audit_payload.get("prompt_version") or "").strip() != (
        CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
    ):
        add("corrected-model formalization requires the current source-record prompt version")
    if str(audit_payload.get("import_module") or "").strip() != expected_import_module:
        add(
            "corrected-model formalization requires a source-record audit generated from "
            f"`{expected_import_module}`"
        )
    audit_scope = audit_payload.get("formalization_scope")
    if not isinstance(audit_scope, dict):
        add("source-record audit is missing the corrected formalization-scope context")
        return findings
    expected_scope_values = {
        "kind": AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE,
        "scope_id": scope_id,
        "approval_artifact_sha256": approval_digest,
        "base_archive_sha256": archive_digest,
    }
    for key, expected in expected_scope_values.items():
        if str(audit_scope.get(key) or "").strip().lower() != str(expected).strip().lower():
            add(f"source-record audit corrected scope `{key}` is stale or mismatched")
    if _nonempty_string_list(audit_scope.get("target_result_declarations")) != targets:
        add("source-record audit corrected scope target declarations are stale or mismatched")
    audit_model_bindings, audit_model_binding_errors = (
        corrected_model_scope_model_bindings(
            audit_scope,
            target_result_declarations=targets,
        )
    )
    for error in audit_model_binding_errors:
        add("source-record audit corrected scope " + error)
    if (
        scope_model_bindings is not None
        and audit_model_bindings is not None
        and scope_model_bindings != audit_model_bindings
    ):
        add(
            "source-record audit corrected scope governing model bindings are stale "
            "or mismatched"
        )
    if _nonempty_string_list(audit_scope.get("correction_ids")) != correction_ids:
        add("source-record audit corrected scope correction ids are stale or mismatched")
    if str(audit_scope.get("governing_corrections_sha256") or "").strip() != str(
        correction_digest or ""
    ):
        add(
            "source-record audit corrected scope governing-correction content is stale or mismatched"
        )
    if audit_scope.get("archival_equivalence_claimed") is not False:
        add("source-record audit corrected scope must not claim archival equivalence")

    audit_digest = str(audit_payload.get("source_record_audit_sha256") or "").strip()
    audit_integrity_digest = str(
        audit_payload.get("source_record_audit_integrity_sha256") or ""
    ).strip()
    audit_scope_digest = str(audit_scope.get("scope_sha256") or "").strip()
    if not SHA256_RE.fullmatch(audit_digest):
        add("corrected-model source-record audit requires a SHA-256 audit digest")
    if not SHA256_RE.fullmatch(audit_integrity_digest):
        add(
            "corrected-model source-record audit requires a SHA-256 raw-integrity receipt"
        )
    if not SHA256_RE.fullmatch(audit_scope_digest):
        add("corrected-model source-record audit requires a SHA-256 formalization-scope digest")
    if str(contract.get("source_record_audit_sha256") or "").strip() != audit_digest:
        add("corrected-model semantic contract is stale for the current source-record audit digest")
    if str(contract.get("source_record_audit_integrity_sha256") or "").strip() != audit_integrity_digest:
        add(
            "corrected-model semantic contract is stale for the current source-record raw-integrity receipt"
        )
    if str(contract.get("source_record_scope_sha256") or "").strip() != str(
        audit_scope_digest
    ).strip():
        add("corrected-model semantic contract is stale for the current formalization-scope digest")

    expected_semantic_keys = {
        str(key).strip()
        for key in audit_payload.get("expected_semantic_model_judgment_keys") or []
        if str(key).strip()
    }
    semantic_items_by_key: dict[str, dict[str, Any]] = {}
    semantic_items_by_qualified: dict[str, dict[str, Any]] = {}
    raw_semantic_items = audit_payload.get("semantic_model_items")
    if not isinstance(raw_semantic_items, list) or not raw_semantic_items:
        add("corrected-model formalization requires generated semantic_model_items")
        raw_semantic_items = []
    for index, item in enumerate(raw_semantic_items):
        if not isinstance(item, dict):
            add(f"semantic_model_items[{index}] must be an object")
            continue
        key = str(item.get("judgment_key") or "").strip()
        qualified = str(item.get("qualified_declaration") or "").strip()
        freshness_mode, freshness_error = corrected_model_raw_item_freshness_mode(
            item
        )
        if not key or not qualified:
            add(
                f"semantic_model_items[{index}] requires judgment_key and "
                "qualified_declaration"
            )
            continue
        if freshness_error or freshness_mode is None:
            add(
                f"semantic_model_items[{index}] has invalid generated freshness metadata: "
                + (freshness_error or "unknown freshness mode")
            )
            continue
        if key in semantic_items_by_key or qualified in semantic_items_by_qualified:
            add(
                f"semantic_model_items[{index}] has a duplicate key or qualified declaration"
            )
            continue
        semantic_items_by_key[key] = item
        semantic_items_by_qualified[qualified] = item
    if expected_semantic_keys != set(semantic_items_by_key):
        add(
            "corrected-model source-record audit must expose exactly one current "
            "semantic item for every expected semantic-model key"
        )
    available_local_declarations = {
        str(declaration).strip()
        for declaration in audit_payload.get("available_local_lean_declarations") or []
        if str(declaration).strip()
    }
    if not available_local_declarations:
        add(
            "corrected-model source-record audit requires available_local_lean_declarations "
            "for bridge identity validation"
        )

    review_surface = status_payload.get("review_surface")
    included_rows: set[str] = set()
    assumption_rows: set[str] = set()
    if isinstance(review_surface, dict):
        raw_included_rows = review_surface.get("include_names")
        if isinstance(raw_included_rows, list):
            included_rows = {
                name.strip()
                for name in raw_included_rows
                if isinstance(name, str) and name.strip()
            }
        raw_assumption_rows = review_surface.get("assumption_names")
        if isinstance(raw_assumption_rows, list):
            assumption_rows = {
                name.strip()
                for name in raw_assumption_rows
                if isinstance(name, str) and name.strip()
            }

    semantic_mapping_by_key: dict[str, dict[str, Any]] = {}
    semantic_item_mappings = contract.get("semantic_item_mappings")
    if not isinstance(semantic_item_mappings, list) or not semantic_item_mappings:
        add("corrected-model semantic contract requires semantic_item_mappings")
    else:
        mapped_semantic_keys: set[str] = set()
        for index, mapping in enumerate(semantic_item_mappings):
            if not isinstance(mapping, dict):
                add(f"semantic_item_mappings[{index}] must be an object")
                continue
            key = str(mapping.get("source_record_item_key") or "").strip()
            item = semantic_items_by_key.get(key)
            if not key or key in mapped_semantic_keys:
                add(
                    f"semantic_item_mappings[{index}] has a missing or duplicate source-record key"
                )
                continue
            mapped_semantic_keys.add(key)
            semantic_mapping_by_key[key] = mapping
            if item is None:
                add(
                    f"semantic_item_mappings[{index}] references a semantic item absent from "
                    "the current source-record audit"
                )
                continue
            freshness_error = corrected_model_mapping_freshness_error(mapping, item)
            if freshness_error:
                add(f"semantic_item_mappings[{index}] {freshness_error}")
            if str(mapping.get("qualified_declaration") or "").strip() != str(
                item.get("qualified_declaration") or ""
            ).strip():
                add(
                    f"semantic_item_mappings[{index}] does not name the generated fully "
                    "qualified declaration"
                )
            disposition = str(mapping.get("disposition") or "").strip()
            if disposition not in CORRECTED_MODEL_SEMANTIC_DISPOSITIONS:
                add(f"semantic_item_mappings[{index}] has an unsupported disposition")
            if disposition in {
                "author_approved_correction",
                "author_approved_additional_assumption",
            }:
                if str(mapping.get("approval_artifact_path") or "").strip() != str(
                    approval.get("artifact_path") or ""
                ).strip() or str(mapping.get("approval_artifact_sha256") or "").strip().lower() != approval_digest:
                    add(
                        f"semantic_item_mappings[{index}] must pin the current author-approval artifact"
                    )
            mapped_corrections = _nonempty_string_list(mapping.get("correction_ids"))
            if mapped_corrections is None or not set(mapped_corrections).issubset(
                set(correction_ids)
            ):
                add(
                    f"semantic_item_mappings[{index}] must cite declared correction_ids"
                )
            for required_key in ("source_anchor", "semantic_comparison", "lean_evidence"):
                value = str(mapping.get(required_key) or "").strip()
                if not value:
                    add(f"semantic_item_mappings[{index}] requires {required_key}")
                elif required_key == "source_anchor" and not CORRECTED_MODEL_SOURCE_LOCATOR_RE.search(value):
                    add(
                        f"semantic_item_mappings[{index}] source_anchor needs an exact "
                        "source or approval-artifact locator"
                    )
                elif required_key == "source_anchor":
                    for error in corrected_model_anchor_errors(folder, value):
                        add(f"semantic_item_mappings[{index}] {error}")
            dimensions = item.get("dimensions")
            responses = mapping.get("dimensions")
            expected_dimensions = {
                str(dimension.get("id") or "").strip()
                for dimension in (dimensions if isinstance(dimensions, list) else [])
                if isinstance(dimension, dict) and str(dimension.get("id") or "").strip()
            }
            if not expected_dimensions or not isinstance(responses, dict) or set(responses) != expected_dimensions:
                add(
                    f"semantic_item_mappings[{index}] must answer exactly every generated "
                    "semantic dimension"
                )
                continue
            for raw_dimension in dimensions if isinstance(dimensions, list) else []:
                if not isinstance(raw_dimension, dict):
                    continue
                dimension = str(raw_dimension.get("id") or "").strip()
                response = responses.get(dimension)
                if not isinstance(response, dict):
                    continue
                verdict = str(response.get("verdict") or "").strip()
                if verdict not in CORRECTED_MODEL_DIMENSION_VERDICTS:
                    add(
                        f"semantic_item_mappings[{index}].dimensions.{dimension} has an "
                        "unsupported verdict"
                    )
                detected = raw_dimension.get("detected_from_expanded_surface") is True
                if detected and verdict == "not_applicable":
                    add(
                        f"semantic_item_mappings[{index}].dimensions.{dimension} cannot mark "
                        "a generated semantic boundary not_applicable"
                    )
                for required_key in ("source_locator", "semantic_comparison", "lean_evidence"):
                    value = str(response.get(required_key) or "").strip()
                    if not value:
                        add(
                            f"semantic_item_mappings[{index}].dimensions.{dimension} requires "
                            f"{required_key}"
                        )
                    elif required_key == "source_locator" and not CORRECTED_MODEL_SOURCE_LOCATOR_RE.search(value):
                        add(
                            f"semantic_item_mappings[{index}].dimensions.{dimension} source_locator "
                            "needs an exact source or approval-artifact locator"
                        )
                    elif required_key == "source_locator":
                        for error in corrected_model_anchor_errors(folder, value):
                            add(
                                f"semantic_item_mappings[{index}].dimensions.{dimension} {error}"
                            )
                if detected and raw_dimension.get("requires_checked_bridge_when_detected") is True:
                    bridges = _nonempty_string_list(
                        response.get("checked_bridge_declarations")
                    )
                    if bridges is None or not all(
                        bridge in available_local_declarations for bridge in bridges
                    ):
                        add(
                            f"semantic_item_mappings[{index}].dimensions.{dimension} needs fully "
                            "qualified checked_bridge_declarations from the current local Lean closure"
                        )
        if mapped_semantic_keys != set(semantic_items_by_key):
            add(
                "semantic_item_mappings must cover exactly every generated semantic-model item"
            )

    target_mappings = contract.get("target_result_mappings")
    if not isinstance(target_mappings, list) or not target_mappings:
        add("corrected-model semantic contract requires target_result_mappings")
    else:
        mapped_targets: set[str] = set()
        for index, mapping in enumerate(target_mappings):
            if not isinstance(mapping, dict):
                add(f"target_result_mappings[{index}] must be an object")
                continue
            target = str(mapping.get("target_declaration") or "").strip()
            item = semantic_items_by_qualified.get(target)
            if not target or target in mapped_targets:
                add(f"target_result_mappings[{index}] has a missing or duplicate target_declaration")
                continue
            mapped_targets.add(target)
            if item is None:
                add(
                    f"target_result_mappings[{index}] does not match a generated fully "
                    "qualified PaperInterface semantic item"
                )
                continue
            row = str(item.get("row") or "").strip()
            if row not in included_rows:
                add(
                    f"target_result_mappings[{index}] targets a declaration that is not "
                    "an included PaperInterface review row"
                )
            if str(mapping.get("source_record_item_key") or "").strip() != str(
                item.get("judgment_key") or ""
            ).strip():
                add(
                    f"target_result_mappings[{index}] does not name the current expanded item"
                )
            freshness_error = corrected_model_mapping_freshness_error(mapping, item)
            if freshness_error:
                add(f"target_result_mappings[{index}] {freshness_error}")
            expected_model_spec = (
                scope_model_bindings.target_model_spec_declarations.get(target)
                if scope_model_bindings is not None
                else None
            )
            declared_model_spec = str(
                mapping.get("model_spec_declaration") or ""
            ).strip()
            if expected_model_spec is None:
                add(
                    f"target_result_mappings[{index}] has no validated target-to-model "
                    "scope binding"
                )
            elif (
                declared_model_spec != expected_model_spec
                and not (
                    not declared_model_spec
                    and scope_model_bindings is not None
                    and scope_model_bindings.uses_legacy_scalar
                )
            ):
                add(
                    f"target_result_mappings[{index}] must name its exact mapped "
                    "governing model_spec_declaration"
                )
            surface = item.get("expanded_lean_surface")
            roots = (
                {
                    str(root).strip()
                    for root in surface.get("record_roots") or []
                    if str(root).strip()
                }
                if isinstance(surface, dict)
                else set()
            )
            if expected_model_spec is not None and expected_model_spec not in roots:
                add(
                    f"target_result_mappings[{index}] target does not consume the exact "
                    "governing model record mapped to it in its expanded Lean surface"
                )
            mapped_corrections = _nonempty_string_list(mapping.get("correction_ids"))
            if mapped_corrections is None or not set(mapped_corrections).issubset(
                set(correction_ids)
            ):
                add(f"target_result_mappings[{index}] must cite declared correction_ids")
            for required_key in ("source_anchor", "semantic_comparison", "lean_evidence"):
                value = str(mapping.get(required_key) or "").strip()
                if not value:
                    add(f"target_result_mappings[{index}] requires {required_key}")
                elif required_key == "source_anchor" and not CORRECTED_MODEL_SOURCE_LOCATOR_RE.search(value):
                    add(
                        f"target_result_mappings[{index}] source_anchor needs an exact source "
                        "or approval-artifact locator"
                    )
                elif required_key == "source_anchor":
                    for error in corrected_model_anchor_errors(folder, value):
                        add(f"target_result_mappings[{index}] {error}")
            if str(mapping.get("approval_artifact_path") or "").strip() != str(
                approval.get("artifact_path") or ""
            ).strip() or str(mapping.get("approval_artifact_sha256") or "").strip().lower() != approval_digest:
                add(
                    f"target_result_mappings[{index}] must pin the current author-approval artifact"
                )
        if mapped_targets != set(targets):
            add(
                "target_result_mappings must cover exactly the corrected target_result_declarations"
            )

    expected_assumption_declarations = {
        str(item.get("qualified_declaration") or "").strip()
        for item in semantic_items_by_key.values()
        if str(item.get("row") or "").strip() in assumption_rows
        and str(item.get("qualified_declaration") or "").strip()
    }
    if assumption_rows and len(expected_assumption_declarations) != len(assumption_rows):
        add(
            "every explicit corrected-model assumption must have a generated fully qualified semantic item"
        )
    assumption_mappings = contract.get("assumption_mappings")
    if assumption_rows and (not isinstance(assumption_mappings, list) or not assumption_mappings):
        add("corrected-model semantic contract requires assumption_mappings")
    elif isinstance(assumption_mappings, list):
        mapped_assumptions: set[str] = set()
        for index, mapping in enumerate(assumption_mappings):
            if not isinstance(mapping, dict):
                add(f"assumption_mappings[{index}] must be an object")
                continue
            declaration = str(mapping.get("assumption_declaration") or "").strip()
            item = semantic_items_by_qualified.get(declaration)
            if not declaration or declaration in mapped_assumptions:
                add(f"assumption_mappings[{index}] has a missing or duplicate assumption_declaration")
                continue
            mapped_assumptions.add(declaration)
            if item is None or str(item.get("row") or "").strip() not in assumption_rows:
                add(
                    f"assumption_mappings[{index}] does not identify a configured explicit assumption"
                )
                continue
            if str(mapping.get("source_record_item_key") or "").strip() != str(
                item.get("judgment_key") or ""
            ).strip():
                add(
                    f"assumption_mappings[{index}] does not name the current expanded item"
                )
            freshness_error = corrected_model_mapping_freshness_error(mapping, item)
            if freshness_error:
                add(f"assumption_mappings[{index}] {freshness_error}")
            item_key = str(item.get("judgment_key") or "").strip()
            if item_key not in semantic_mapping_by_key:
                add(
                    f"assumption_mappings[{index}] lacks the required detailed semantic-item mapping"
                )
            disposition = str(mapping.get("disposition") or "").strip()
            if disposition not in CORRECTED_MODEL_ASSUMPTION_DISPOSITIONS:
                add(f"assumption_mappings[{index}] has an unsupported disposition")
            mapped_corrections = _nonempty_string_list(mapping.get("correction_ids"))
            if mapped_corrections is None or not set(mapped_corrections).issubset(
                set(correction_ids)
            ):
                add(f"assumption_mappings[{index}] must cite declared correction_ids")
            for required_key in ("source_anchor", "semantic_comparison", "lean_evidence"):
                value = str(mapping.get(required_key) or "").strip()
                if not value:
                    add(f"assumption_mappings[{index}] requires {required_key}")
                elif required_key == "source_anchor" and not CORRECTED_MODEL_SOURCE_LOCATOR_RE.search(value):
                    add(
                        f"assumption_mappings[{index}] source_anchor needs an exact source "
                        "or approval-artifact locator"
                    )
                elif required_key == "source_anchor":
                    for error in corrected_model_anchor_errors(folder, value):
                        add(f"assumption_mappings[{index}] {error}")
            if disposition in {
                "author_approved_correction",
                "author_approved_additional_assumption",
            }:
                if str(mapping.get("approval_artifact_path") or "").strip() != str(
                    approval.get("artifact_path") or ""
                ).strip() or str(mapping.get("approval_artifact_sha256") or "").strip().lower() != approval_digest:
                    add(
                        f"assumption_mappings[{index}] must pin the current author-approval artifact"
                    )
        if mapped_assumptions != expected_assumption_declarations:
            add(
                "assumption_mappings must cover exactly every configured explicit assumption"
            )
    contract_semantic_keys = _nonempty_string_list(contract.get("semantic_item_keys"))
    if contract_semantic_keys is None or set(contract_semantic_keys) != expected_semantic_keys:
        add(
            "corrected-model semantic contract must enumerate exactly the current expanded semantic-model rows"
        )
    groups = contract.get("semantic_review_groups")
    if not isinstance(groups, list) or not groups:
        add("corrected-model semantic contract requires semantic_review_groups")
    else:
        covered: set[str] = set()
        duplicate_coverage: set[str] = set()
        for index, group in enumerate(groups):
            if not isinstance(group, dict):
                add(f"semantic_review_groups[{index}] must be an object")
                continue
            group_keys = _nonempty_string_list(group.get("item_keys"))
            if group_keys is None:
                add(f"semantic_review_groups[{index}] requires unique nonempty item_keys")
                continue
            for key in group_keys:
                if key in covered:
                    duplicate_coverage.add(key)
                covered.add(key)
            group_corrections = _nonempty_string_list(group.get("correction_ids"))
            if group_corrections is None or not set(group_corrections).issubset(set(correction_ids)):
                add(f"semantic_review_groups[{index}] must cite declared correction_ids")
            responses = group.get("dimensions")
            if not isinstance(responses, dict) or set(responses) != contract_dimension_set:
                add(f"semantic_review_groups[{index}] must cover every semantic dimension")
                continue
            for dimension, response in responses.items():
                if not isinstance(response, dict) or not all(
                    str(response.get(key) or "").strip()
                    for key in ("disposition", "rationale", "lean_evidence")
                ):
                    add(
                        f"semantic_review_groups[{index}].dimensions.{dimension} requires "
                        "disposition, rationale, and lean_evidence"
                    )
        if covered != expected_semantic_keys:
            add("semantic_review_groups must cover each current semantic-model row exactly once")
        if duplicate_coverage:
            add("semantic_review_groups duplicate semantic-model row coverage")

    if scope_model_bindings is None:
        field_items: dict[str, dict[str, Any]] = {}
        field_graph_errors = ["cannot resolve validated governing model bindings"]
    else:
        field_items, field_graph_errors = corrected_model_transitively_reachable_field_items(
            audit_payload,
            target_result_declarations=targets,
            **corrected_model_scope_model_metadata(scope_model_bindings),
        )
    for error in field_graph_errors:
        add("corrected-model structural field graph " + error)
    reachable_model_field_keys = set(field_items)
    mappings = contract.get("model_field_mappings")
    if not isinstance(mappings, list) or not mappings:
        add("corrected-model semantic contract requires model_field_mappings")
    else:
        mapped_keys: set[str] = set()
        for index, mapping in enumerate(mappings):
            if not isinstance(mapping, dict):
                add(f"model_field_mappings[{index}] must be an object")
                continue
            key = str(mapping.get("source_record_item_key") or "").strip()
            correction_id = str(mapping.get("correction_id") or "").strip()
            if not key or key in mapped_keys:
                add(f"model_field_mappings[{index}] has a missing or duplicate source-record key")
                continue
            mapped_keys.add(key)
            if key not in field_items:
                add(
                    f"model_field_mappings[{index}] references a field absent from the "
                    "current transitive governing-model field graph"
                )
            else:
                freshness_error = corrected_model_mapping_freshness_error(
                    mapping, field_items[key]
                )
                if freshness_error:
                    add(f"model_field_mappings[{index}] {freshness_error}")
            if correction_id not in correction_by_id:
                add(f"model_field_mappings[{index}] cites an undeclared correction_id")
            for required_key in ("semantic_role", "rationale", "lean_evidence"):
                if not str(mapping.get(required_key) or "").strip():
                    add(f"model_field_mappings[{index}] requires {required_key}")
        if mapped_keys != reachable_model_field_keys:
            add(
                "model_field_mappings must cover exactly every expanded corrected-model "
                "field reachable from the governing model record"
            )
    if not findings and validated_field_items_out is not None:
        validated_field_items_out.clear()
        validated_field_items_out.update(field_items)
    return findings


def corrected_model_scope_contract_findings(
    folder: Path,
    status: str,
    status_payload: dict[str, Any],
) -> list[Finding]:
    """Validate corrected scope without accepting prevalidated caller evidence."""

    return _corrected_model_scope_contract_findings(folder, status, status_payload)


def author_approved_corrected_scope_contract_is_current(
    folder: Path, status_payload: dict[str, Any]
) -> bool:
    """Whether a waiver-capable whole-paper contract is current.

    Component-only receipts are useful evidence, but intentionally return
    ``False`` here so no caller can use them to exempt source obligations.
    """

    scope = author_approved_corrected_scope(status_payload)
    if scope is None:
        return False
    scope_role, scope_role_error = corrected_model_scope_role(scope)
    if scope_role_error or scope_role != WHOLE_PAPER_CLOSEOUT_SCOPE_ROLE:
        return False

    return not (
        corrected_model_scope_contract_findings(
            folder, str(status_payload.get("status") or ""), status_payload
        )
    )


def current_author_approved_corrected_model_field_items(
    folder: Path, status_payload: dict[str, Any]
) -> dict[str, dict[str, Any]] | None:
    """Return the exact current transitive governing-model field graph.

    Consumers that need to exempt a nested corrected-model input must use this
    helper rather than reconstructing reachability from declaration spelling.
    ``None`` means that either no corrected scope is active, its full semantic
    contract is stale/invalid, or the checked contract no longer maps every
    structurally reachable field with the required freshness receipt.
    """

    if not author_approved_corrected_scope_contract_is_current(folder, status_payload):
        return None
    scope = author_approved_corrected_scope(status_payload)
    if scope is None:
        return None
    targets = _nonempty_string_list(scope.get("target_result_declarations"))
    contract_ref = scope.get("semantic_contract")
    if targets is None or not isinstance(contract_ref, dict):
        return None
    model_bindings, model_binding_errors = corrected_model_scope_model_bindings(
        scope,
        target_result_declarations=targets,
    )
    if model_binding_errors or model_bindings is None:
        return None
    contract_path = _paper_local_artifact_path(folder, contract_ref.get("path"))
    contract = load_json(contract_path) if contract_path is not None else None
    if not isinstance(contract, dict):
        return None
    audit_path, audit_path_error = source_record_review_sidecar_path(
        folder,
        status_payload,
        config_field="source_record_audit_file",
        default_basename="source_record_audit.json",
    )
    if audit_path_error or audit_path is None:
        return None
    audit_payload = load_json(audit_path)
    if not isinstance(audit_payload, dict):
        return None
    field_items, graph_errors = corrected_model_transitively_reachable_field_items(
        audit_payload,
        target_result_declarations=targets,
        **corrected_model_scope_model_metadata(model_bindings),
    )
    if graph_errors or not field_items:
        return None
    raw_mappings = contract.get("model_field_mappings")
    if not isinstance(raw_mappings, list):
        return None
    mapped_keys: set[str] = set()
    for mapping in raw_mappings:
        if not isinstance(mapping, dict):
            return None
        key = str(mapping.get("source_record_item_key") or "").strip()
        item = field_items.get(key)
        if (
            not key
            or item is None
            or key in mapped_keys
            or corrected_model_mapping_freshness_error(mapping, item)
        ):
            return None
        mapped_keys.add(key)
    if mapped_keys != set(field_items):
        return None
    return field_items


def source_artifact_pin_findings(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
    *,
    require_source_bytes: bool = True,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[Finding]:
    """Validate the canonical source pin against paper-local artifact bytes."""

    severity = finding_severity(status)

    def companion_findings() -> list[Finding]:
        """Check an opted-in companion even when canonical bytes are absent.

        Structural checkouts may intentionally omit licensed source artifacts.
        That only relaxes findings explicitly caused by missing bytes; it must
        not bypass the companion's schema, path-safety, or page-map checks.
        """

        companion_issues = source_text_companion_validation_issues(
            folder,
            payload,
            repository_root=ROOT,
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        )
        return [
            Finding(
                severity if not issue.missing_bytes or require_source_bytes else "WARN",
                folder.name,
                rel(manifest_path),
                f"source_text_companion: {issue.message}",
            )
            for issue in companion_issues
        ]

    def archive_surface_findings() -> list[Finding]:
        """Validate an opted-in archive-derived text surface independently.

        A public structural checkout can omit the archive and the derived text,
        but it cannot hide malformed paths, schema, member identities, or a
        claimed digest that does not reconstruct from private source bytes.
        """

        archive_issues = source_archive_surface_validation_issues(
            folder,
            payload,
            repository_root=ROOT,
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        )
        return [
            Finding(
                severity if not issue.missing_bytes or require_source_bytes else "WARN",
                folder.name,
                rel(manifest_path),
                f"source_archive_surface: {issue.message}",
            )
            for issue in archive_issues
        ]

    raw_path = payload.get("source_artifact_path")
    raw_digest = payload.get("source_artifact_sha256")
    source_path = raw_path.strip() if isinstance(raw_path, str) else ""
    expected_digest = raw_digest.strip() if isinstance(raw_digest, str) else ""
    legacy_locations = legacy_source_digest_locations(payload)

    if not source_path or not expected_digest:
        missing = []
        if not source_path:
            missing.append("source_artifact_path")
        if not expected_digest:
            missing.append("source_artifact_sha256")
        legacy_note = ""
        if legacy_locations:
            legacy_note = (
                "; legacy/unscoped digest field(s) cannot pin verifiable bytes: "
                + ", ".join(legacy_locations)
            )
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                "source statement inventory lacks the top-level canonical source pin; "
                f"missing {', '.join(missing)}{legacy_note}",
            ),
            *companion_findings(),
            *archive_surface_findings(),
        ]

    if not SHA256_RE.fullmatch(expected_digest):
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                "source_artifact_sha256 must be exactly 64 hexadecimal characters",
            ),
            *companion_findings(),
            *archive_surface_findings(),
        ]

    relative_path = Path(source_path)
    if relative_path.is_absolute():
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                "source_artifact_path must be relative to the paper folder or repository root",
            ),
            *companion_findings(),
            *archive_surface_findings(),
        ]

    # Prefer portable paper-relative paths.  Repository-relative `papers/...`
    # paths are accepted, but both forms must resolve inside this paper folder.
    anchor = ROOT if relative_path.parts[:1] == ("papers",) else folder
    try:
        paper_root = folder.resolve()
        artifact_path = (anchor / relative_path).resolve()
        artifact_path.relative_to(paper_root)
    except (OSError, RuntimeError, ValueError):
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                "source_artifact_path escapes the paper folder",
            ),
            *companion_findings(),
            *archive_surface_findings(),
        ]

    frozen_artifact_present = None
    if file_bytes_override is not None:
        if artifact_path not in file_bytes_override:
            return [
                Finding(
                    severity,
                    folder.name,
                    rel(manifest_path),
                    f"frozen input bundle omits source_artifact_path: {source_path}",
                ),
                *companion_findings(),
                *archive_surface_findings(),
            ]
        frozen_artifact_present = file_bytes_override[artifact_path] is not None
    if (
        frozen_artifact_present is False
        or (file_bytes_override is None and not artifact_path.exists())
    ):
        return [
            Finding(
                severity if require_source_bytes else "WARN",
                folder.name,
                rel(manifest_path),
                (
                    f"source_artifact_path does not exist: {source_path}"
                    if require_source_bytes
                    else (
                        "source bytes are not provisioned in this structural checkout: "
                        f"{source_path}; the recorded SHA-256 is not release certification"
                    )
                ),
            ),
            *companion_findings(),
            *archive_surface_findings(),
        ]
    if file_bytes_override is None and not artifact_path.is_file():
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                f"source_artifact_path is not a regular file: {source_path}",
            ),
            *companion_findings(),
            *archive_surface_findings(),
        ]

    try:
        actual_digest = (
            hashlib.sha256(
                _exact_file_bytes(artifact_path, file_bytes_override)
            ).hexdigest()
            if file_bytes_override is not None
            else sha256_file(artifact_path)
        )
    except (OSError, RuntimeError) as error:
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                f"cannot read source_artifact_path `{source_path}`: {error}",
            ),
            *companion_findings(),
            *archive_surface_findings(),
        ]
    if actual_digest != expected_digest.lower():
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                "source artifact SHA-256 mismatch: "
                f"manifest has {expected_digest.lower()}, file has {actual_digest}",
            ),
            *companion_findings(),
            *archive_surface_findings(),
        ]
    return [*companion_findings(), *archive_surface_findings()]


def resolve_paper_source_path(folder: Path, raw_path: object) -> tuple[Path | None, str]:
    """Resolve a paper-local or repository-relative source path safely."""

    if not isinstance(raw_path, str) or not raw_path.strip():
        return None, "path must be a nonempty string"
    relative_path = Path(raw_path.strip())
    if relative_path.is_absolute():
        return None, "path must be relative to the paper folder or repository root"
    anchor = ROOT if relative_path.parts[:1] == ("papers",) else folder
    try:
        candidate = (anchor / relative_path).resolve()
        candidate.relative_to(folder.resolve())
    except (OSError, RuntimeError, ValueError):
        return None, "path escapes the paper folder"
    return candidate, ""


def normalized_source_text(raw: bytes) -> str:
    """Return the canonical text view used by source line anchors.

    The artifact's raw SHA-256 remains the source pin.  Line-oriented evidence
    intentionally normalizes only line endings, so a source extracted on a
    CRLF host has the same quoted line slices as the LF version.
    """

    return raw.decode("utf-8").replace("\r\n", "\n").replace("\r", "\n")


def normalized_source_lines(text: str) -> list[str]:
    """Split canonical source text into one-based logical lines.

    A terminating newline ends the final content line rather than adding a
    synthetic empty line.  Empty lines that are actually present in the source
    remain part of the line inventory.
    """

    if not text:
        return []
    lines = text.split("\n")
    if text.endswith("\n"):
        lines.pop()
    return lines


def normalized_source_line_excerpt(
    lines: list[str], line_start: int, line_end: int
) -> str | None:
    """Return the canonical no-terminal-newline slice, or ``None`` if invalid."""

    if line_start < 1 or line_end < line_start or line_end > len(lines):
        return None
    return "\n".join(lines[line_start - 1 : line_end])


def source_anchor_evidence_nodes(
    value: object, path: str = "$") -> Iterable[tuple[str, dict[str, Any]]]:
    """Yield every structured source-location declaration in an inventory.

    This deliberately follows JSON structure, not row keys or Lean declaration
    names. Nested component-level anchors therefore receive the same evidence
    requirement as top-level statement-map rows when a paper opts in.
    ``semantic_context_requirements`` are validated by their dedicated,
    always-on source-only lane below so they cannot be skipped when a map has
    not opted into global anchor evidence.
    """

    if isinstance(value, dict):
        if "source_location" in value:
            yield path, value
        for key, child in value.items():
            if key in {
                "source_anchor_evidence",
                SEMANTIC_CONTEXT_REQUIREMENTS_KEY,
            }:
                continue
            yield from source_anchor_evidence_nodes(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from source_anchor_evidence_nodes(child, f"{path}[{index}]")


def scoped_computational_observation_nodes(
    value: object, path: str = "$"
) -> Iterable[tuple[str, dict[str, Any]]]:
    """Yield explicit computational-exception rows without using their keys.

    A byte-pinned quote is mandatory for this narrow scope exemption even when a
    paper has not elected to require quote evidence for its entire source map.
    Traverse the JSON structure instead of recognizing map keys or Lean names so
    a renamed item cannot escape the same source-evidence requirement.
    """

    if isinstance(value, dict):
        if (
            str(value.get("source_scope_classification") or "").strip().lower()
            == NON_NAMED_COMPUTATIONAL_ILLUSTRATION
        ):
            yield path, value
        for key, child in value.items():
            if key == "source_anchor_evidence":
                continue
            yield from scoped_computational_observation_nodes(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from scoped_computational_observation_nodes(child, f"{path}[{index}]")


def user_approved_scope_exclusion_nodes(
    value: object, path: str = "$"
) -> Iterable[tuple[str, dict[str, Any]]]:
    """Yield source-map items carrying explicit user-scope metadata.

    The approval does not make a source claim non-claim-bearing.  It only
    creates a separately auditable scope disposition, so its exact source
    location needs the same byte-pinned quote evidence as any other exception.
    This structural traversal never consults map keys or Lean names.
    """

    if isinstance(value, dict):
        if USER_APPROVED_SCOPE_EXCLUSION in value:
            yield path, value
        for key, child in value.items():
            if key == "source_anchor_evidence":
                continue
            yield from user_approved_scope_exclusion_nodes(child, f"{path}.{key}")
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from user_approved_scope_exclusion_nodes(child, f"{path}[{index}]")


def semantic_context_requirement_nodes(
    payload: dict[str, Any],
) -> Iterable[tuple[str, str, int, object]]:
    """Yield declared source-map semantic context without inspecting Lean names.

    A context requirement belongs to a source inventory item, but it is not an
    additional result and cannot receive proof or coverage credit. The source
    item key is returned only as a stable inventory trace; callers must compare
    the literal context kind, explanation, and byte-pinned source excerpt with
    expanded Lean semantics rather than treating the key as mathematical
    evidence.
    """

    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        return
    for raw_key, raw_item in raw_items.items():
        if not isinstance(raw_item, dict):
            continue
        if SEMANTIC_CONTEXT_REQUIREMENTS_KEY not in raw_item:
            continue
        raw_requirements = raw_item.get(SEMANTIC_CONTEXT_REQUIREMENTS_KEY)
        if not isinstance(raw_requirements, list):
            continue
        source_key = str(raw_key)
        for index, requirement in enumerate(raw_requirements):
            yield (
                f"$.items.{source_key}.{SEMANTIC_CONTEXT_REQUIREMENTS_KEY}[{index}]",
                source_key,
                index,
                requirement,
            )


def semantic_context_requirements(payload: dict[str, Any]) -> list[dict[str, Any]]:
    """Project declared source context into a deterministic audit-only payload.

    This projection intentionally carries no Lean declaration, proof route, or
    coverage disposition. It preserves the exact byte-pinned source anchor so
    the source-record judge can use the context semantically without being able
    to mistake a declaration/function name for evidence.
    """

    items: list[dict[str, Any]] = []
    for _path, source_key, index, raw_requirement in semantic_context_requirement_nodes(
        payload
    ):
        if not isinstance(raw_requirement, dict):
            continue
        item = {
            "source_item_key": source_key,
            "requirement_index": index,
            "source_anchor_evidence": raw_requirement.get(
                "source_anchor_evidence"
            ),
        }
        # Do not synthesize absent legacy fields.  That keeps historical
        # projections byte-stable while letting a role-only v11 context be an
        # explicitly source-text-only object.
        for field in ("kind", "source_location", "explanation"):
            if field in raw_requirement:
                item[field] = raw_requirement.get(field)
        # The bounded role is part of the v11 semantic input contract.  Keep
        # it out of legacy projections when absent so historical raw receipts
        # remain replayable until that paper enters the v11 re-audit lane.
        if "semantic_role" in raw_requirement:
            item["semantic_role"] = raw_requirement.get("semantic_role")
        # Preserve source-scoped contracts in the judge-visible projection.
        # Do not add absent/null fields to ordinary contexts: those existing
        # v10 context digests must remain byte-for-byte stable.
        if (
            raw_requirement.get("kind")
            == EQUALITY_DEFINED_PARTITION_CONTEXT_KIND
        ):
            item[EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD] = raw_requirement.get(
                EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD
            )
        if (
            raw_requirement.get("kind")
            == STRATEGIC_OBSERVATION_TOTALITY_CONTEXT_KIND
        ):
            item[STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD] = (
                raw_requirement.get(STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD)
            )
        if raw_requirement.get("kind") == CONDITIONING_INFORMATION_CONTEXT_KIND:
            item[CONDITIONING_INFORMATION_CONTRACT_FIELD] = raw_requirement.get(
                CONDITIONING_INFORMATION_CONTRACT_FIELD
            )
        if raw_requirement.get("kind") == SOURCE_MODEL_DERIVATION_CONTEXT_KIND:
            item[SOURCE_MODEL_DERIVATION_CONTRACT_FIELD] = raw_requirement.get(
                SOURCE_MODEL_DERIVATION_CONTRACT_FIELD
            )
        items.append(item)
    return sorted(
        items,
        key=lambda item: (
            str(item.get("source_item_key") or ""),
            int(item.get("requirement_index") or 0),
        ),
    )


def semantic_context_requirement_shape_findings(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
) -> list[Finding]:
    """Validate the source-only context schema before quote checking.

    The requirement is intentionally not attached to a Lean endpoint. Its only
    job is to force a reviewer to account for a source convention/domain fact
    that could otherwise be silently assumed in a formal statement.
    """

    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        return []
    severity = finding_severity(status)
    findings: list[Finding] = []

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(manifest_path), message))

    for raw_key, raw_item in raw_items.items():
        if not isinstance(raw_item, dict):
            continue
        if SEMANTIC_CONTEXT_REQUIREMENTS_KEY not in raw_item:
            continue
        node_path = f"items.{raw_key}.{SEMANTIC_CONTEXT_REQUIREMENTS_KEY}"
        requirements = raw_item.get(SEMANTIC_CONTEXT_REQUIREMENTS_KEY)
        if not isinstance(requirements, list) or not requirements:
            add(f"{node_path} must be a nonempty list")
            continue
        for index, requirement in enumerate(requirements):
            requirement_path = f"{node_path}[{index}]"
            if not isinstance(requirement, dict):
                add(f"{requirement_path} must be an object")
                continue
            kind = requirement.get("kind")
            semantic_role = requirement.get("semantic_role")
            allowed_fields = set(SEMANTIC_CONTEXT_REQUIREMENT_FIELDS)
            if kind == EQUALITY_DEFINED_PARTITION_CONTEXT_KIND:
                allowed_fields.add(EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD)
            if kind == STRATEGIC_OBSERVATION_TOTALITY_CONTEXT_KIND:
                allowed_fields.add(STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD)
            if kind == CONDITIONING_INFORMATION_CONTEXT_KIND:
                allowed_fields.add(CONDITIONING_INFORMATION_CONTRACT_FIELD)
            if kind == SOURCE_MODEL_DERIVATION_CONTEXT_KIND:
                allowed_fields.add(SOURCE_MODEL_DERIVATION_CONTRACT_FIELD)
            unexpected = sorted(
                set(requirement) - allowed_fields
            )
            if unexpected:
                add(
                    f"{requirement_path} has unsupported field(s): "
                    + ", ".join(unexpected)
                )
            required_fields = ["source_anchor_evidence"]
            # Pre-v11 maps used a curator-facing `kind`/location/explanation
            # triple.  Preserve that narrow compatibility lane, but whenever
            # a bounded `semantic_role` is supplied it is the authority for
            # what the raw-source statement judge may use as context.
            if semantic_role is None:
                required_fields.extend(["kind", "source_location", "explanation"])
            for field in required_fields:
                if field not in requirement:
                    add(f"{requirement_path} is missing required field `{field}`")
            if semantic_role is not None:
                if not isinstance(semantic_role, str) or semantic_role.strip() not in SEMANTIC_CONTEXT_ROLES:
                    add(
                        f"{requirement_path}.semantic_role must be one of: "
                        + ", ".join(sorted(SEMANTIC_CONTEXT_ROLES))
                    )
            # If legacy curation fields are present, retain their validation;
            # role-only v11 context instead relies exclusively on the pinned
            # source quotes and its bounded semantic role.
            uses_legacy_curation = semantic_role is None or any(
                field in requirement for field in ("kind", "source_location", "explanation")
            )
            if uses_legacy_curation:
                if not isinstance(kind, str) or not kind.strip():
                    add(f"{requirement_path}.kind must be a nonempty semantic identifier")
                elif not SEMANTIC_CONTEXT_REQUIREMENT_KIND_RE.fullmatch(kind.strip()):
                    add(
                        f"{requirement_path}.kind must use lowercase semantic identifier "
                        "syntax (letters, digits, `_`, `.`, or `-`)"
                    )
                location = requirement.get("source_location")
                if not isinstance(location, str) or not location.strip():
                    add(f"{requirement_path}.source_location must be a nonempty string")
                elif not list(SOURCE_FILE_LINE_RE.finditer(location)):
                    add(
                        f"{requirement_path}.source_location must include one or more "
                        "file:line anchors into the canonical pinned source artifact"
                    )
                explanation = requirement.get("explanation")
                if not isinstance(explanation, str) or not explanation.strip():
                    add(f"{requirement_path}.explanation must be a nonempty semantic explanation")
            anchors = requirement.get("source_anchor_evidence")
            if not isinstance(anchors, list) or not anchors:
                add(
                    f"{requirement_path}.source_anchor_evidence must be a nonempty "
                    "byte-pinned source-anchor list"
                )
            if kind == EQUALITY_DEFINED_PARTITION_CONTEXT_KIND:
                for error in equality_defined_partition_context_contract_errors(
                    requirement
                ):
                    add(f"{requirement_path}.{error}")
            elif kind == STRATEGIC_OBSERVATION_TOTALITY_CONTEXT_KIND:
                for error in strategic_observation_totality_context_contract_errors(
                    requirement
                ):
                    add(f"{requirement_path}.{error}")
            elif kind == CONDITIONING_INFORMATION_CONTEXT_KIND:
                for error in conditioning_information_context_contract_errors(
                    requirement
                ):
                    add(f"{requirement_path}.{error}")
            elif kind == SOURCE_MODEL_DERIVATION_CONTEXT_KIND:
                for error in source_model_derivation_context_contract_errors(
                    requirement
                ):
                    add(f"{requirement_path}.{error}")
            elif EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD in requirement:
                add(
                    f"{requirement_path}.{EQUALITY_DEFINED_PARTITION_CONTRACT_FIELD} "
                    f"is allowed only with kind `{EQUALITY_DEFINED_PARTITION_CONTEXT_KIND}`"
                )
            elif STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD in requirement:
                add(
                    f"{requirement_path}.{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_FIELD} "
                    "is allowed only with kind "
                    f"`{STRATEGIC_OBSERVATION_TOTALITY_CONTEXT_KIND}`"
                )
            elif CONDITIONING_INFORMATION_CONTRACT_FIELD in requirement:
                add(
                    f"{requirement_path}.{CONDITIONING_INFORMATION_CONTRACT_FIELD} "
                    "is allowed only with kind "
                    f"`{CONDITIONING_INFORMATION_CONTEXT_KIND}`"
                )
            elif SOURCE_MODEL_DERIVATION_CONTRACT_FIELD in requirement:
                add(
                    f"{requirement_path}.{SOURCE_MODEL_DERIVATION_CONTRACT_FIELD} "
                    "is allowed only with kind "
                    f"`{SOURCE_MODEL_DERIVATION_CONTEXT_KIND}`"
                )
    return findings


def semantic_context_requirement_anchor_findings(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
    *,
    require_source_bytes: bool = True,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[Finding]:
    """Byte-validate every declared semantic context requirement.

    The synthetic map limits the ordinary quote validator to these source-only
    requirements. It neither looks at, nor gives credit for, any source-map
    Lean route. A malformed requirement is handled by the shape validator so
    this helper can keep its diagnostics focused on exact canonical source
    bytes and line ranges.
    """

    context_items: dict[str, dict[str, Any]] = {}
    raw_items = payload.get("items")
    if isinstance(raw_items, dict):
        for raw_key, raw_item in raw_items.items():
            if not isinstance(raw_item, dict):
                continue
            if SEMANTIC_CONTEXT_REQUIREMENTS_KEY not in raw_item:
                continue
            # Use a neutral synthetic container so the ordinary quote walker
            # visits the requirement entries while its normal traversal keeps
            # this separately validated lane out of global-anchor diagnostics.
            # Role-only v11 context deliberately has no curator paraphrase or
            # independent location string.  Derive a validation-only locator
            # from the context's own declared anchor coordinates so the shared
            # anchor validator still checks exact current source bytes; this
            # does not add any source text or semantic content.
            raw_contexts = raw_item.get(SEMANTIC_CONTEXT_REQUIREMENTS_KEY)
            normalized_contexts: list[object] = []
            if isinstance(raw_contexts, list):
                for raw_context in raw_contexts:
                    if not isinstance(raw_context, dict):
                        normalized_contexts.append(raw_context)
                        continue
                    context = dict(raw_context)
                    if (
                        context.get("semantic_role") is not None
                        and not str(context.get("source_location") or "").strip()
                    ):
                        anchors = context.get("source_anchor_evidence")
                        locators: list[str] = []
                        if isinstance(anchors, list):
                            for anchor in anchors:
                                if not isinstance(anchor, dict):
                                    continue
                                path = str(anchor.get("path") or "").strip()
                                start = anchor.get("line_start")
                                end = anchor.get("line_end")
                                if path and isinstance(start, int) and isinstance(end, int):
                                    suffix = str(start) if start == end else f"{start}-{end}"
                                    locators.append(f"{path}:{suffix}")
                        if locators:
                            context["source_location"] = "; ".join(locators)
                    normalized_contexts.append(context)
            context_items[str(raw_key)] = {
                "context_entries": normalized_contexts
            }
    if not context_items:
        return []
    isolated_payload = {
        "source_artifact_path": payload.get("source_artifact_path"),
        "source_artifact_sha256": payload.get("source_artifact_sha256"),
        SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY: True,
        "items": context_items,
    }
    return source_anchor_evidence_findings(
        folder,
        status,
        manifest_path,
        isolated_payload,
        require_source_bytes=require_source_bytes,
        file_bytes_override=file_bytes_override,
    )


def semantic_context_requirement_findings(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
    *,
    require_source_bytes: bool = True,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[Finding]:
    """Return schema and exact-source evidence failures for context requirements."""

    shape_findings = semantic_context_requirement_shape_findings(
        folder, status, manifest_path, payload
    )
    if shape_findings:
        return shape_findings
    return semantic_context_requirement_anchor_findings(
        folder,
        status,
        manifest_path,
        payload,
        require_source_bytes=require_source_bytes,
        file_bytes_override=file_bytes_override,
    )


def source_anchor_evidence_findings(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
    *,
    require_source_bytes: bool = True,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[Finding]:
    """Validate required source excerpts against the canonical pinned artifact.

    A map opts in with top-level ``source_anchor_evidence_required: true`` to
    require evidence for every structured ``source_location``. Independently,
    every ``non_named_computational_illustration`` scope exemption and every
    ``user_approved_scope_exclusion`` record always needs evidence, even when
    the map does not opt in globally. Each required node
    needs one
    ``source_anchor_evidence`` object per declared ``file:line[-line]`` anchor:

    ``{"path", "line_start", "line_end", "quoted_text", "quoted_text_sha256"}``

    Evidence paths must resolve to the top-level pinned artifact, the quote's
    UTF-8 SHA-256 must be current, and the quote must equal the exact canonical
    line slice.  The raw artifact SHA-256 is checked first, tying this content
    evidence to the byte-pinned source rather than to a declaration name.
    """

    raw_required = payload.get(SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY, False)
    severity = finding_severity(status)
    if raw_required is not False and raw_required is not True:
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                f"{SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY} must be boolean true when present",
            )
        ]

    all_location_nodes = list(source_anchor_evidence_nodes(payload))
    scoped_nodes = list(scoped_computational_observation_nodes(payload))
    scoped_nodes.extend(user_approved_scope_exclusion_nodes(payload))
    # A malformed attempt to combine the two lanes should still be diagnosed by
    # their dedicated validators, not duplicate every quote-evidence finding.
    unique_scoped_nodes: list[tuple[str, dict[str, Any]]] = []
    seen_scoped_paths: set[str] = set()
    for node_path, node in scoped_nodes:
        if node_path not in seen_scoped_paths:
            seen_scoped_paths.add(node_path)
            unique_scoped_nodes.append((node_path, node))
    scoped_nodes = unique_scoped_nodes
    required_nodes = all_location_nodes if raw_required is True else scoped_nodes
    if not required_nodes and raw_required is False:
        return []

    pin_findings = source_artifact_pin_findings(
        folder,
        status,
        manifest_path,
        payload,
        require_source_bytes=require_source_bytes,
        file_bytes_override=file_bytes_override,
    )
    if pin_findings:
        # A source quote cannot certify anything until the artifact it quotes is
        # itself byte-verified.  Returning the pin finding avoids a second,
        # misleading content diagnosis for an untrusted file.
        return pin_findings

    artifact_path, artifact_path_error = resolve_paper_source_path(
        folder, payload.get("source_artifact_path")
    )
    if artifact_path is None:
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                "cannot resolve canonical source artifact for source-anchor evidence: "
                + artifact_path_error,
            )
        ]
    try:
        source_bytes = _exact_file_bytes(artifact_path, file_bytes_override)
        source_text = normalized_source_text(source_bytes)
    except UnicodeDecodeError:
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                "source-anchor evidence requires a UTF-8 text canonical source artifact",
            )
        ]
    except (OSError, RuntimeError) as error:
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                f"cannot read canonical source artifact for source-anchor evidence: {error}",
            )
        ]

    expected_digest = str(payload.get("source_artifact_sha256") or "").strip().lower()
    actual_digest = hashlib.sha256(source_bytes).hexdigest()
    if actual_digest != expected_digest:
        return [
            Finding(
                severity,
                folder.name,
                rel(manifest_path),
                "source artifact changed after pin validation; cannot certify source-anchor evidence",
            )
        ]

    source_lines = normalized_source_lines(source_text)
    findings: list[Finding] = []

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(manifest_path), message))

    # An explicit, valid scope exclusion can leave no ordinary source rows.
    # It remains independently validated below in the raw-map lane; demanding
    # a synthetic in-scope locator here would turn an approved exclusion into
    # a false source-evidence failure.
    if not required_nodes:
        return findings

    for node_path, node in required_nodes:
        raw_location = node.get("source_location")
        if not isinstance(raw_location, str) or not raw_location.strip():
            add(f"{node_path}.source_location must be a nonempty string")
            continue
        location_matches = list(SOURCE_FILE_LINE_RE.finditer(raw_location))
        if not location_matches:
            add(
                f"{node_path}.source_location must include one or more file:line anchors "
                "when source-anchor evidence is required"
            )
            continue

        expected_anchors: Counter[tuple[str, int, int]] = Counter()
        for match in location_matches:
            raw_anchor_path = match.group("path")
            candidate, path_error = resolve_paper_source_path(folder, raw_anchor_path)
            start = int(match.group("start"))
            end = int(match.group("end") or start)
            if candidate is None:
                add(
                    f"{node_path}.source_location anchor `{raw_anchor_path}:{start}-{end}` "
                    f"{path_error}"
                )
                continue
            if candidate != artifact_path:
                add(
                    f"{node_path}.source_location anchor `{raw_anchor_path}:{start}-{end}` "
                    "does not identify the canonical pinned source artifact"
                )
                continue
            if normalized_source_line_excerpt(source_lines, start, end) is None:
                add(
                    f"{node_path}.source_location anchor `{raw_anchor_path}:{start}-{end}` "
                    f"is outside the {len(source_lines)}-line canonical source artifact"
                )
                continue
            expected_anchors[(str(artifact_path), start, end)] += 1

        raw_evidence = node.get("source_anchor_evidence")
        if not isinstance(raw_evidence, list) or not raw_evidence:
            add(
                f"{node_path}.source_anchor_evidence must be a nonempty list with one "
                "byte-verified quote for every declared source anchor"
            )
            continue

        actual_anchors: Counter[tuple[str, int, int]] = Counter()
        for index, raw_entry in enumerate(raw_evidence):
            entry_path = f"{node_path}.source_anchor_evidence[{index}]"
            if not isinstance(raw_entry, dict):
                add(f"{entry_path} must be an object")
                continue
            missing = sorted(
                field for field in SOURCE_ANCHOR_EVIDENCE_FIELDS if field not in raw_entry
            )
            if missing:
                add(f"{entry_path} is missing required field(s): {', '.join(missing)}")
                continue

            candidate, path_error = resolve_paper_source_path(folder, raw_entry.get("path"))
            line_start = raw_entry.get("line_start")
            line_end = raw_entry.get("line_end")
            valid_lines = (
                isinstance(line_start, int)
                and not isinstance(line_start, bool)
                and isinstance(line_end, int)
                and not isinstance(line_end, bool)
            )
            if candidate is None:
                add(f"{entry_path}.path {path_error}")
            elif candidate != artifact_path:
                add(
                    f"{entry_path}.path must identify the canonical pinned source artifact"
                )
            if not valid_lines:
                add(f"{entry_path}.line_start and line_end must be integers")
            elif normalized_source_line_excerpt(source_lines, line_start, line_end) is None:
                add(
                    f"{entry_path}.line_start/line_end is outside the "
                    f"{len(source_lines)}-line canonical source artifact"
                )

            raw_quote = raw_entry.get("quoted_text")
            raw_quote_digest = raw_entry.get("quoted_text_sha256")
            if not isinstance(raw_quote, str):
                add(f"{entry_path}.quoted_text must be a string")
                quote = None
            else:
                quote = raw_quote.replace("\r\n", "\n").replace("\r", "\n")
                if not quote:
                    add(f"{entry_path}.quoted_text must not be empty")
            if not isinstance(raw_quote_digest, str) or not SHA256_RE.fullmatch(
                raw_quote_digest.strip()
            ):
                add(f"{entry_path}.quoted_text_sha256 must be 64 hexadecimal characters")
            elif quote is not None and hashlib.sha256(quote.encode("utf-8")).hexdigest() != raw_quote_digest.strip().lower():
                add(
                    f"{entry_path}.quoted_text_sha256 does not match the normalized quoted_text bytes"
                )

            excerpt = (
                normalized_source_line_excerpt(source_lines, line_start, line_end)
                if valid_lines
                else None
            )
            if quote is not None and excerpt is not None and quote != excerpt:
                add(
                    f"{entry_path}.quoted_text does not equal the exact normalized source "
                    "line slice"
                )
            if candidate == artifact_path and valid_lines and excerpt is not None:
                actual_anchors[(str(artifact_path), line_start, line_end)] += 1

        missing_anchors = expected_anchors - actual_anchors
        extra_anchors = actual_anchors - expected_anchors
        if missing_anchors:
            rendered = ", ".join(
                f"{start}-{end}" for (_, start, end), count in sorted(missing_anchors.items()) for _ in range(count)
            )
            add(
                f"{node_path}.source_anchor_evidence is missing declared source anchor "
                f"line range(s): {rendered}"
            )
        if extra_anchors:
            rendered = ", ".join(
                f"{start}-{end}" for (_, start, end), count in sorted(extra_anchors.items()) for _ in range(count)
            )
            add(
                f"{node_path}.source_anchor_evidence has undeclared or duplicate source "
                f"anchor line range(s): {rendered}"
            )
    return findings


def check_duplicate_sidecars(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    differing: list[str] = []
    identical: list[str] = []
    for basename in AUDIT_SIDECARS:
        legacy = folder / basename
        organized = folder / "audit" / basename
        if context is not None:
            legacy_snapshot = context.json_snapshot(legacy)
            organized_snapshot = context.json_snapshot(organized)
            legacy_digest = (
                legacy_snapshot.sha256 if legacy_snapshot is not None else None
            )
            organized_digest = (
                organized_snapshot.sha256 if organized_snapshot is not None else None
            )
            if legacy_digest is None or organized_digest is None:
                continue
            same_bytes = legacy_digest == organized_digest
        else:
            if not legacy.exists() or not organized.exists():
                continue
            same_bytes = legacy.read_bytes() == organized.read_bytes()
        if same_bytes:
            identical.append(basename)
        else:
            differing.append(basename)

    findings: list[Finding] = []
    if differing:
        findings.append(
            Finding(
                finding_severity(status),
                folder.name,
                rel(folder / "audit"),
                "legacy-root and canonical audit sidecars diverge: " + ", ".join(differing),
            )
        )
    if identical:
        findings.append(
            Finding(
                "WARN",
                folder.name,
                rel(folder / "audit"),
                "byte-identical legacy sidecars still duplicate the canonical audit copy: "
                + ", ".join(identical),
            )
        )
    return findings


def historical_statement_manifest_replay_evidence_findings(
    folder: Path,
    _status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Run the no-Lean persisted-artifact gate only when a sidecar uses it.

    Ordinary papers never pay for this replay check.  A transported statement
    receipt, however, is evidence only while its historical carrier/authority,
    archive, current source-record closure, and static Git/current-file recipe
    can all be reopened from their byte-pinned retrieval coordinates.
    """

    try:
        try:
            from scripts import statement_receipt_reissue as reissue
        except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
            import statement_receipt_reissue as reissue
    except Exception as exc:  # pragma: no cover - import boundary is fail-closed.
        return [
            Finding(
                "ERROR",
                folder.name,
                rel(folder / "audit" / "statement_match_llm.json"),
                "historical statement-manifest replay integrity gate is unavailable: "
                f"{type(exc).__name__}",
            )
        ]
    match_path = transaction_sidecar(folder, "statement_match_llm.json", context)
    match_payload = transaction_json(match_path, context)
    items = match_payload.get("items") if isinstance(match_payload, Mapping) else None
    if not isinstance(items, Mapping) or not any(
        isinstance(entry, Mapping)
        and reissue.HISTORICAL_REPLAY_PROVENANCE_FIELD in entry
        for entry in items.values()
    ):
        return []
    try:
        errors = reissue.historical_manifest_replay_persisted_evidence_errors(folder)
    except Exception as exc:  # noqa: BLE001 - evidence-gate exceptions fail closed.
        errors = [f"static replay validator raised {type(exc).__name__}"]
    return [
        Finding(
            "ERROR",
            folder.name,
            rel(match_path),
            "historical statement-manifest replay integrity failure: " + error,
        )
        for error in errors
    ]


def check_placeholder_evidence(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    findings: list[Finding] = []
    for basename in AUDIT_SIDECARS:
        path = transaction_sidecar(folder, basename, context)
        payload = transaction_json(path, context)
        if payload is None:
            continue
        placeholders: list[str] = []
        name_only: list[str] = []
        for key_path, value in walk_values(payload):
            if not key_path or not isinstance(value, str):
                continue
            leaf = key_path[-1]
            dotted = ".".join(key_path)
            if leaf in {"source_location", "source_evidence", "source_note", "source_status"}:
                if PLACEHOLDER_SOURCE_RE.search(value):
                    placeholders.append(dotted)
            if leaf == "reason" and NAME_ONLY_REASON_RE.search(value):
                name_only.append(dotted)
        if placeholders:
            findings.append(
                Finding(
                    finding_severity(status),
                    folder.name,
                    rel(path),
                    f"{len(placeholders)} placeholder/generic source-provenance value(s): "
                    + ", ".join(placeholders[:5])
                    + ("; ..." if len(placeholders) > 5 else ""),
                )
            )
        if name_only:
            findings.append(
                Finding(
                    finding_severity(status),
                    folder.name,
                    rel(path),
                    f"{len(name_only)} coverage reason(s) use name matching as semantic evidence: "
                    + ", ".join(name_only[:5])
                    + ("; ..." if len(name_only) > 5 else ""),
                )
            )
    return findings


def coverage_row_signature_pin_findings(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Check the structural half of v6 direct-coverage signature binding.

    This fast integrity audit intentionally does not run Lean.  It ensures that
    a v6 direct source-to-row claim records one syntactically valid signature
    pin for exactly each named row.  ``review_dashboard.py`` recomputes the
    current normalized elaborated manifest and rejects a stale pin, so neither
    check treats row names or source routes as semantic evidence.
    """

    path = transaction_sidecar(folder, "paper_coverage_llm.json", context)
    payload = transaction_json(path, context)
    if not isinstance(payload, dict):
        return []
    if (
        str(payload.get("prompt_version") or "").strip()
        != PAPER_COVERAGE_ROW_SIGNATURE_PROMPT_VERSION
    ):
        return []

    malformed: list[str] = []
    for source_key, item in item_entries(payload):
        coverage = str(
            item.get("coverage")
            or item.get("judgment")
            or item.get("verdict")
            or item.get("status")
            or ""
        ).strip().lower().replace("-", "_")
        coverage = re.sub(r"\s+", "_", coverage)
        if coverage in {"match", "matches", "yes", "true", "represented", "present"}:
            coverage = "covered"
        elif coverage in {
            "conditional",
            "visible_premise_boundary",
            "covered_conditionally",
            "additional_assumption",
            "covered_with_additional_assumption",
        }:
            coverage = "conditional_boundary"
        if coverage not in DIRECT_PAPER_COVERAGE_JUDGMENTS:
            continue
        raw_rows = item.get("review_rows")
        if isinstance(raw_rows, list):
            rows = [str(row).strip() for row in raw_rows if str(row).strip()]
        elif raw_rows is None:
            rows = []
        else:
            rows = [
                value.strip()
                for value in str(raw_rows).split(",")
                if value.strip()
            ]
        # A no-row direct verdict is separately rejected by the coverage audit.
        if not rows:
            continue
        raw_pins = item.get("review_row_signature_sha256")
        if not isinstance(raw_pins, dict):
            malformed.append(
                f"{source_key}: missing review_row_signature_sha256 object"
            )
            continue
        pins = {
            str(name).strip(): value
            for name, value in raw_pins.items()
            if str(name).strip()
        }
        if len(set(rows)) != len(rows):
            malformed.append(f"{source_key}: duplicate review_rows entry")
        if set(pins) != set(rows):
            malformed.append(
                f"{source_key}: review_row_signature_sha256 keys do not exactly match review_rows"
            )
        for row in sorted(set(rows)):
            digest = pins.get(row)
            if not isinstance(digest, str) or not SHA256_RE.fullmatch(digest.strip()):
                malformed.append(
                    f"{source_key} -> {row}: missing or malformed Lean signature digest"
                )
    if not malformed:
        return []
    return [
        Finding(
            finding_severity(status),
            folder.name,
            rel(path),
            f"{len(malformed)} v5 direct-coverage row-signature pin error(s): "
            + "; ".join(malformed[:4])
            + ("; ..." if len(malformed) > 4 else ""),
        )
    ]


def corrected_target_coverage_findings(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Reject coverage that launders a corrected target into ordinary proof credit.

    This fast lane does not inspect Lean. It binds a source-to-row coverage
    verdict to the archival and corrected record hashes before the dashboard
    performs its fuller semantic and elaborated-signature review.
    """

    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    map_payload = transaction_json(map_path, context)
    if not isinstance(map_payload, dict):
        return []
    map_items = map_payload.get("items")
    if not isinstance(map_items, dict):
        return []
    presentation_aliases, _alias_errors = source_presentation_aliases(map_items)
    corrected_items = {
        str(key).strip(): item
        for key, item in map_items.items()
        if isinstance(item, dict)
        and str(key).strip() not in presentation_aliases
        and str(item.get("coverage_status") or "").strip().lower()
        == CORRECTED_SOURCE_STATEMENT_STATUS
    }
    if not corrected_items:
        return []
    coverage_path = transaction_sidecar(folder, "paper_coverage_llm.json", context)
    coverage_payload = transaction_json(coverage_path, context)
    if not isinstance(coverage_payload, dict):
        return []
    raw_items = coverage_payload.get("items")
    if not isinstance(raw_items, dict):
        return []

    malformed: list[str] = []
    for key, target_item in corrected_items.items():
        raw_coverage = raw_items.get(key)
        if not isinstance(raw_coverage, dict):
            continue
        primary_declaration = corrected_target_primary_declaration(target_item)
        if primary_declaration is None:
            malformed.append(
                f"{key}: source map has no sole corrected-target endpoint in lean_declarations"
            )
            continue
        coverage = re.sub(
            r"\s+",
            "_",
            str(raw_coverage.get("coverage") or "").strip().lower().replace("-", "_"),
        )
        if coverage != CORRECTED_TARGET_COVERAGE:
            malformed.append(
                f"{key}: corrected source item uses `{coverage or 'missing'}` instead of `{CORRECTED_TARGET_COVERAGE}`"
            )
            continue
        target = target_item.get("corrected_target")
        if not isinstance(target, dict):
            # Map validation provides the primary structural diagnosis.
            continue
        target_statement = re.sub(
            r"\s+", " ", str(target.get("statement") or "").strip()
        )
        archival_statement = re.sub(
            r"\s+", " ", str(target_item.get("statement") or "").strip()
        )
        expected_target_digest = hashlib.sha256(target_statement.encode("utf-8")).hexdigest()
        expected_archival_digest = hashlib.sha256(
            archival_statement.encode("utf-8")
        ).hexdigest()
        if str(raw_coverage.get("target_kind") or "").strip().lower() != CORRECTED_TARGET_ROUTE_KIND:
            malformed.append(f"{key}: missing target_kind approved_corrected_target")
        raw_rows = raw_coverage.get("review_rows")
        if isinstance(raw_rows, list):
            review_rows = [str(row).strip() for row in raw_rows if str(row).strip()]
        elif raw_rows is None:
            review_rows = []
        else:
            review_rows = [
                value.strip() for value in str(raw_rows).split(",") if value.strip()
            ]
        if not corrected_target_coverage_rows_match_primary(
            primary_declaration,
            review_rows,
            map_items,
            folder.name,
        ):
            malformed.append(
                f"{key}: covered_corrected_target must link exactly the sole "
                "corrected-target endpoint in lean_declarations"
            )
        if str(raw_coverage.get("statement_sha256") or "").strip().lower() != expected_target_digest:
            malformed.append(f"{key}: stale corrected target statement digest")
        if str(raw_coverage.get("archival_statement_sha256") or "").strip().lower() != expected_archival_digest:
            malformed.append(f"{key}: stale archival statement digest")
        if str(raw_coverage.get("corrected_target_sha256") or "").strip().lower() != corrected_target_record_digest(target):
            malformed.append(f"{key}: stale corrected-target record digest")
        governing = target.get("governing_defect_ids")
        recorded_governing = raw_coverage.get("governing_defect_ids")
        if (
            not isinstance(governing, list)
            or not isinstance(recorded_governing, list)
            or [str(value).strip() for value in recorded_governing]
            != [str(value).strip() for value in governing]
        ):
            malformed.append(
                f"{key}: governing source-statement defect ids do not match corrected target"
            )
        if raw_coverage.get("archival_equivalence_claimed") is not False:
            malformed.append(
                f"{key}: coverage must set archival_equivalence_claimed to false"
            )
    for key, raw_coverage in raw_items.items():
        if (
            not isinstance(raw_coverage, dict)
            or str(key).strip() in corrected_items
            or str(key).strip() in presentation_aliases
        ):
            continue
        coverage = re.sub(
            r"\s+",
            "_",
            str(raw_coverage.get("coverage") or "").strip().lower().replace("-", "_"),
        )
        if coverage == CORRECTED_TARGET_COVERAGE:
            malformed.append(
                f"{str(key).strip() or '<unnamed>'}: corrected-target coverage has no corrected source-map item"
            )
    if not malformed:
        return []
    return [
        Finding(
            finding_severity(status),
            folder.name,
            rel(coverage_path),
            f"{len(malformed)} corrected-target coverage pin error(s): "
            + "; ".join(malformed[:4])
            + ("; ..." if len(malformed) > 4 else ""),
        )
    ]


def item_values(payload: dict[str, Any]) -> list[dict[str, Any]]:
    raw = payload.get("items") or payload.get("judgments") or {}
    if isinstance(raw, dict):
        return [item for item in raw.values() if isinstance(item, dict)]
    if isinstance(raw, list):
        return [item for item in raw if isinstance(item, dict)]
    return []


def item_entries(payload: dict[str, Any]) -> list[tuple[str, dict[str, Any]]]:
    raw = payload.get("items") or payload.get("judgments") or {}
    if isinstance(raw, dict):
        return [
            (str(key), item)
            for key, item in raw.items()
            if isinstance(item, dict)
        ]
    if isinstance(raw, list):
        return [
            (str(index), item)
            for index, item in enumerate(raw)
            if isinstance(item, dict)
        ]
    return []


def formalized_note_rows(payload: dict[str, Any]) -> set[str]:
    raw = payload.get("formalized_note_rows")
    if raw is None:
        raw = payload.get("formalized_note_boundary_rows")
    if not isinstance(raw, list):
        return set()
    return {str(item).strip() for item in raw if str(item).strip()}


def is_formalized_note_boundary(
    row_key: str, item: dict[str, Any], note_rows: set[str]
) -> bool:
    status_impact = str(
        item.get("status_impact")
        or item.get("status_alignment")
        or item.get("boundary_status_impact")
        or ""
    ).strip()
    return status_impact == "formalized_note" or row_key in note_rows


NONWAIVABLE_FORMALIZED_NOTE_ASSUMPTION_JUDGMENTS = {
    "documented_additional_assumption",
    "partial_boundary",
    "not_paper_assumption",
}


def formalized_note_waives_assumption_judgment(
    row_key: str, item: dict[str, Any], note_rows: set[str]
) -> bool:
    """Return whether a note may retain this assumption-provenance judgment.

    A source correction or explicit source convention can be documented as a
    note when the advertised endpoint is actually proved.  A non-source
    assumption, an open partial boundary, or an assumption added to the paper
    cannot be converted into that note merely by listing its row in
    ``formalized_note_rows``.
    """

    judgment = str(item.get("judgment") or "").strip().lower()
    return (
        judgment not in NONWAIVABLE_FORMALIZED_NOTE_ASSUMPTION_JUDGMENTS
        and is_formalized_note_boundary(row_key, item, note_rows)
    )


def configured_assumption_review_rows(
    folder: Path, *, context: EvidenceRunContext | None = None
) -> set[str] | None:
    """Return the explicitly selected assumption-review rows, when available.

    ``assumption_match_llm.json`` is a current review artifact, not an archive
    of every historical premise a paper has ever exposed.  A status file with
    an explicit ``assumption_names`` list therefore defines the active rows
    whose provenance judgments can affect closeout.  This is only a routing
    control: it does not accept any mathematical claim based on a row name.

    Keep the legacy fail-closed behavior when the configuration is absent or
    malformed.  In that situation the gate cannot establish an active scope,
    so every serialized judgment remains relevant rather than being silently
    discarded.
    """

    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, Mapping):
        return None
    raw_rows = review_surface.get("assumption_names")
    if not isinstance(raw_rows, list):
        return None
    if any(not isinstance(row, str) or not row.strip() for row in raw_rows):
        return None
    return {row.strip() for row in raw_rows}


def assumption_sidecar_entry_review_rows(
    row_key: str, item: Mapping[str, Any]
) -> set[str]:
    """Return explicit navigation coordinates declared by one sidecar entry.

    Schema-1 sidecars historically used their object key as the configured
    row identifier.  Newer entries may additionally carry an exact reviewed
    declaration field.  These coordinates select an already-configured audit
    row only; they never serve as source or semantic-match evidence.
    """

    rows = {str(row_key).strip()} if str(row_key).strip() else set()
    for field in (
        "assumption_declaration",
        "qualified_declaration",
        "reviewed_declaration",
    ):
        value = item.get(field)
        if isinstance(value, str) and value.strip():
            rows.add(value.strip())
    return rows


def active_assumption_sidecar_entries(
    folder: Path,
    payload: dict[str, Any],
    *,
    context: EvidenceRunContext | None = None,
) -> list[tuple[str, dict[str, Any]]]:
    """Filter provenance rows to the current explicit assumption surface.

    An empty configured set deliberately returns no active entries.  This
    prevents an archived, retired boundary in the canonical sidecar from
    demoting a paper after its proof is completed.  The source-record and
    Lean-premise gates remain responsible for detecting any currently exposed
    premise that was omitted from the configured surface.
    """

    entries = item_entries(payload)
    configured_rows = configured_assumption_review_rows(folder, context=context)
    if configured_rows is None:
        return entries
    return [
        (row_key, item)
        for row_key, item in entries
        if assumption_sidecar_entry_review_rows(row_key, item).intersection(
            configured_rows
        )
    ]


def author_approved_corrected_assumption_rows(
    folder: Path, *, context: EvidenceRunContext | None = None
) -> set[str]:
    """Return current assumption rows explicitly approved by a corrected scope.

    An author-approved corrected-model scope may legitimately add or repair a
    premise while retaining a full-closeout status.  Source-backed conditions
    in that same current contract are also safe when a provenance reviewer
    conservatively labels their composite predicate as additional.  The
    exception is narrow: it uses the current generated source-record row and
    the current semantic contract's exact assumption declaration, never a
    short declaration name or a source-looking predicate name.  Partial and
    unreviewed assumptions remain nonwaivable.
    """

    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    corrected_scope_current = (
        context.corrected_scope_current
        if context is not None
        else author_approved_corrected_scope_contract_is_current(
            folder, status_payload
        )
    )
    if not corrected_scope_current:
        return set()
    scope = author_approved_corrected_scope(status_payload)
    if scope is None:
        return set()
    approval = scope.get("approval")
    if not isinstance(approval, dict):
        return set()
    approval_path = str(approval.get("artifact_path") or "").strip()
    approval_digest = str(approval.get("artifact_sha256") or "").strip().lower()
    contract_ref = scope.get("semantic_contract")
    if not isinstance(contract_ref, dict):
        return set()
    contract_path = _paper_local_artifact_path(folder, contract_ref.get("path"))
    contract = (
        transaction_json(contract_path, context)
        if contract_path is not None
        else None
    )
    audit_payload = (
        context.audit_payload
        if context is not None
        else load_json(canonical_sidecar(folder, "source_record_audit.json"))
    )
    if not isinstance(contract, dict) or not isinstance(audit_payload, dict):
        return set()

    rows_by_declaration = {
        str(item.get("qualified_declaration") or "").strip(): str(
            item.get("row") or ""
        ).strip()
        for item in audit_payload.get("semantic_model_items") or []
        if isinstance(item, dict)
        and str(item.get("qualified_declaration") or "").strip()
        and str(item.get("row") or "").strip()
    }
    approved_rows: set[str] = set()
    for mapping in contract.get("assumption_mappings") or []:
        if not isinstance(mapping, dict):
            continue
        if str(mapping.get("disposition") or "").strip() not in {
            "literal_source_condition",
            "author_approved_correction",
            "author_approved_additional_assumption",
        }:
            continue
        disposition = str(mapping.get("disposition") or "").strip()
        if disposition != "literal_source_condition" and (
            str(mapping.get("approval_artifact_path") or "").strip()
            != approval_path
            or str(mapping.get("approval_artifact_sha256") or "").strip().lower()
            != approval_digest
        ):
            continue
        row = rows_by_declaration.get(
            str(mapping.get("assumption_declaration") or "").strip()
        )
        if row:
            approved_rows.add(row)
    return approved_rows


def check_full_closeout_assumption_alignment(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Keep non-source and partial assumptions out of either full status."""

    if status not in FULL_CLOSEOUT_STATUSES:
        return []
    assumption_path = transaction_sidecar(
        folder, "assumption_match_llm.json", context
    )
    assumptions = transaction_json(assumption_path, context) or {}
    assumption_note_rows = formalized_note_rows(assumptions)
    corrected_scope_rows = author_approved_corrected_assumption_rows(
        folder, context=context
    )
    non_source_assumptions = [
        item
        for key, item in active_assumption_sidecar_entries(
            folder, assumptions, context=context
        )
        if str(item.get("judgment") or "").strip().lower()
        in {
            "documented_additional_assumption",
            "documented_caveat",
            "not_paper_assumption",
            "partial_boundary",
        }
        and not formalized_note_waives_assumption_judgment(
            key, item, assumption_note_rows
        )
        and not (
            key in corrected_scope_rows
            and str(item.get("judgment") or "").strip().lower()
            in {"documented_additional_assumption", "documented_caveat"}
        )
    ]
    if not non_source_assumptions:
        return []
    label = (
        "plain `formalized`"
        if status == PLAIN_FORMALIZED
        else f"full-closeout status `{status}`"
    )
    return [
        Finding(
            "ERROR",
            folder.name,
            rel(assumption_path),
            f"{label} conflicts with {len(non_source_assumptions)} "
            "non-source/caveat assumption judgment(s)",
        )
    ]


def check_status_alignment(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    if status not in FULL_CLOSEOUT_STATUSES:
        return []

    findings = check_full_closeout_assumption_alignment(
        folder, status, context=context
    )
    if status != PLAIN_FORMALIZED:
        return findings

    # The v11 direct lane replaces the historical aggregate statement and
    # coverage sidecars with one raw-source-to-transparent-Spec screen per
    # current source claim.  Do not let an explicitly superseded v10
    # ``formalized note`` (which recorded an old presentation boundary) change
    # the mathematical status after the current v11 gate has independently
    # checked the same source surface.  The v11 validators run later in this
    # transaction and fail closed if their raw-source screens, paper-local
    # prerequisites, or material-library checks are absent or stale.
    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    source_map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    source_map = transaction_json(source_map_path, context)
    if isinstance(source_map, dict) and raw_source_spec_screening_requested(
        status_payload, source_map, folder=folder
    ):
        return findings

    coverage_path = transaction_sidecar(folder, "paper_coverage_llm.json", context)
    coverage = transaction_json(coverage_path, context) or {}
    coverage_note_rows = formalized_note_rows(coverage)
    conditional_coverage: list[dict[str, Any]] = []
    for key, item in item_entries(coverage):
        coverage_status = str(
            item.get("coverage") or item.get("judgment") or ""
        ).strip().lower()
        if coverage_status not in {
            "conditional_boundary",
            "visible_premise_boundary",
            "covered_with_boundary",
            "partially_covered",
            "missing",
        }:
            continue
        if not is_formalized_note_boundary(key, item, coverage_note_rows):
            conditional_coverage.append(item)
            continue
        note_error = approved_source_convention_formalized_note_error(
            folder, item, context=context
        )
        if note_error:
            findings.append(
                Finding(
                    "ERROR",
                    folder.name,
                    rel(coverage_path),
                    f"formalized-note coverage row `{key}` is not a current approved "
                    f"source-convention receipt: {note_error}",
                )
            )
            conditional_coverage.append(item)
        elif coverage_status != "covered_with_boundary":
            findings.append(
                Finding(
                    "ERROR",
                    folder.name,
                    rel(coverage_path),
                    f"formalized-note coverage row `{key}` must be "
                    "`covered_with_boundary`, not a partial or missing result",
                )
            )
            conditional_coverage.append(item)
    if conditional_coverage:
        findings.append(
            Finding(
                "ERROR",
                folder.name,
                rel(coverage_path),
                f"plain `formalized` status conflicts with {len(conditional_coverage)} visible-premise/partial coverage row(s)",
            )
        )

    statement_path = transaction_sidecar(folder, "statement_match_llm.json", context)
    statement = transaction_json(statement_path, context) or {}
    statement_note_rows = formalized_note_rows(statement)
    conditional_statements: list[dict[str, Any]] = []
    for key, item in item_entries(statement):
        if (
            str(item.get("judgment") or "").strip().lower() != "mismatch"
            or str(item.get("resolution") or "").strip().lower()
            not in {"conditional_boundary", "visible_premise_boundary"}
        ):
            continue
        if not is_formalized_note_boundary(key, item, statement_note_rows):
            conditional_statements.append(item)
            continue
        note_error = approved_source_convention_formalized_note_error(
            folder, item, context=context
        )
        if note_error:
            findings.append(
                Finding(
                    "ERROR",
                    folder.name,
                    rel(statement_path),
                    f"formalized-note statement row `{key}` is not a current approved "
                    f"source-convention receipt: {note_error}",
                )
            )
            conditional_statements.append(item)
    if conditional_statements:
        findings.append(
            Finding(
                "ERROR",
                folder.name,
                rel(statement_path),
                f"plain `formalized` status conflicts with {len(conditional_statements)} accepted statement mismatch(es)",
            )
        )

    return findings


def user_approved_scope_exclusion_map_findings(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
    *,
    require_source_bytes: bool = True,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[Finding]:
    """Fail closed on malformed user-approved exclusions in a source map."""

    findings: list[Finding] = []
    severity = finding_severity(status)

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(manifest_path), message))

    for node_path, node in user_approved_scope_exclusion_nodes(payload):
        if node.get("claim_bearing") is not True:
            add(
                f"{node_path}.user_approved_scope_exclusion must keep the source "
                "assertion claim_bearing: true"
            )
        if str(node.get("source_scope_classification") or "").strip():
            add(
                f"{node_path}.user_approved_scope_exclusion cannot coexist with "
                "source_scope_classification"
            )
        try:
            dashboard = _source_scope_dashboard_module()
            scoped_item = _semantic_contract_scope_item_context(payload, node)
            scope_error = dashboard._source_inventory_item_user_approved_scope_exclusion_error(
                scoped_item
            )
        except (ModuleNotFoundError, AttributeError) as error:
            scope_error = (
                "cannot load source-only unnumbered-prose scope validator: "
                f"{error}"
            )
        if scope_error:
            add(f"{node_path}.{scope_error}")
        for error in user_approved_scope_exclusion_errors(
            folder,
            node.get(USER_APPROVED_SCOPE_EXCLUSION),
            expected_source_locator=node.get("source_location"),
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        ):
            add(f"{node_path}.{error}")
    return findings


def source_map_scope_integrity_findings(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: object,
) -> list[Finding]:
    """Fail closed on raw source-map shape and presentation smuggling.

    Coverage selection is deliberately *not* a parsing or integrity boundary.
    A source item cannot escape review by being made non-object, given an
    unknown presentation kind, or classified as prose despite its own visible
    named-theory presentation.  This lane therefore traverses the raw map
    before normal/deep selection, and never consults map keys or Lean route
    names to decide whether an item is a source claim.
    """

    severity = finding_severity(status)
    findings: list[Finding] = []

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(manifest_path), message))

    if not isinstance(payload, dict):
        add("source statement inventory must be a JSON object")
        return findings
    for error in source_map_structural_errors(
        payload.get("items"),
        declared_environment_kinds=source_named_result_environment_kinds_from_map(
            payload
        ),
    ):
        add(error)
    return findings


def source_coverage_mode_findings(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: object,
) -> tuple[str, list[Finding]]:
    """Return the selected mode plus configuration/closeout findings.

    Legacy discovery may use the normal default, but every closeout status has
    to record its source scope explicitly.  That prevents an old map from
    silently changing meaning when scope policy evolves.
    """

    mode, mode_error = source_coverage_mode_from_map(payload)
    migration_error = source_coverage_mode_migration_error(
        payload, require_explicit=status in CLOSEOUT_STATUSES
    )
    deep_error = deep_source_coverage_attestation_error(payload, mode)
    messages = [message for message in (mode_error, migration_error, deep_error) if message]
    # ``migration_error`` includes malformed/invalid mode diagnostics from
    # the authoritative helper, so do not duplicate the same message.
    unique_messages = list(dict.fromkeys(messages))
    severity = finding_severity(status)
    findings = [
        Finding(severity, folder.name, rel(manifest_path), message)
        for message in unique_messages
    ]
    return mode, findings


def scoped_source_map_payload(
    payload: dict[str, Any],
    mode: str,
    *,
    folder: Path | None = None,
    repository_root: Path | None = None,
) -> tuple[dict[str, Any], dict[str, dict[str, Any]]]:
    """Project per-item source obligations to the active coverage surface.

    Top-level source-artifact data is preserved, while only source items in
    the configured ordinary/deep surface (plus explicit correction/exception
    rows) remain for quote and exact-contract validators. When current paper
    bytes are available, exact source-index/anchor reconciliation contributes
    an additional semantic selector without replacing the legacy row selector.
    Raw-map integrity must be checked separately with
    ``source_map_scope_integrity_findings``.
    """

    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        return dict(payload), {}
    indexed_item_ids = (
        source_index_byte_pinned_anchor_item_ids(
            folder,
            payload,
            mode,
            repository_root=repository_root,
        )
        if folder is not None
        else set()
    )
    selected = filter_source_map_items_for_proof_obligations(
        raw_items,
        mode,
        declared_environment_kinds=source_named_result_environment_kinds_from_map(
            payload
        ),
        additional_selected_item_ids=indexed_item_ids,
    )
    for raw_key, raw_item in raw_items.items():
        if not isinstance(raw_item, dict) or not str(raw_key).strip():
            continue
        # A nonempty source-defect route is an explicit proof-fidelity
        # obligation, even when its source presentation is outside ordinary
        # named-theory coverage.  Retain it for evidence integrity so a
        # `repaired_in_lean` ledger entry cannot be made to look unrouted by
        # classifying its source presentation as a formula, figure, or other
        # nonordinary display.  This does not alter the paper-facing coverage
        # selector, which remains owned by source_coverage_scope.
        raw_defect_ids = raw_item.get("source_defect_ids")
        has_defect_routing_obligation = (
            bool(raw_defect_ids)
            if isinstance(raw_defect_ids, list)
            else raw_defect_ids is not None
        )
        if has_defect_routing_obligation:
            selected[str(raw_key)] = raw_item
    scoped_payload = dict(payload)
    scoped_payload["items"] = selected
    return scoped_payload, selected


def source_named_result_inventory_review_errors(
    payload: object,
    *,
    require_explicit: bool,
    presentation_digest: str | None = None,
) -> list[str]:
    """Validate the source-pinned receipt for named-result discovery.

    The receipt is a curator's completeness attestation, not a Lean route or a
    theorem proof.  Its only role is to make the boundary of the ordinary
    named-theory inventory explicit, including source formats with custom TeX
    environments that a generic extractor cannot recognize on its own.
    """

    if not isinstance(payload, dict):
        return ["named-result inventory requires a readable paper_statement_map.json"]
    review = payload.get(SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY)
    if review is None and not require_explicit:
        return []
    if not isinstance(review, dict):
        return [
            "source-coverage closeout requires "
            f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY} with a source-pinned complete: true attestation"
        ]
    errors: list[str] = []
    if not schema_version_is_exact(
        review.get("schema"), SOURCE_NAMED_RESULT_INVENTORY_REVIEW_SCHEMA
    ):
        errors.append(
            f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY}.schema must be "
            f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_SCHEMA}"
        )
    if review.get("complete") is not True:
        errors.append(
            f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY}.complete must be true"
        )
    for field in ("validator", "method"):
        if not isinstance(review.get(field), str) or not review[field].strip():
            errors.append(f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY}.{field} is required")
    validated_at = str(review.get("validated_at") or "").strip()
    if not USER_APPROVED_SCOPE_EXCLUSION_TIMESTAMP_RE.fullmatch(validated_at):
        errors.append(
            f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY}.validated_at must be an ISO-like timestamp"
        )
    expected_source_digest = str(payload.get("source_artifact_sha256") or "").strip().lower()
    recorded_source_digest = str(review.get("source_artifact_sha256") or "").strip().lower()
    if not SHA256_RE.fullmatch(expected_source_digest):
        errors.append(
            "named-result inventory requires a canonical source_artifact_sha256"
        )
    elif recorded_source_digest != expected_source_digest:
        errors.append(
            f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY} must pin the current source_artifact_sha256"
        )
    if presentation_digest is not None:
        recorded_presentation_digest = str(
            review.get("discovered_named_result_sha256") or ""
        ).strip().lower()
        if not SHA256_RE.fullmatch(recorded_presentation_digest):
            errors.append(
                f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY}.discovered_named_result_sha256 is required"
            )
        elif recorded_presentation_digest != presentation_digest:
            errors.append(
                f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY}.discovered_named_result_sha256 "
                "does not match the current source-only named-result index"
            )
    return errors


def source_named_result_presentation_kinds(
    payload: object,
) -> tuple[object | None, object | None]:
    """Return explicit source-presentation classification tables from the receipt.

    The table is deliberately attached to the source-pinned inventory receipt,
    rather than to a Lean route or a source-map item.  They are only needed
    when a document class, macro package, or PDF transcript uses visible
    theorem-like presentations that cannot be classified from canonical text
    alone.  The source-only extractor performs value-level validation.
    """

    if not isinstance(payload, dict):
        return None, None
    review = payload.get(SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY)
    if not isinstance(review, dict):
        return None, None
    return review.get("environment_kinds"), review.get("heading_kinds")


_RENUMBERED_RESTATEMENT_TEXT_RE = re.compile(
    r"\bre(?:state|stated|statement)\b", re.IGNORECASE
)


def renumbered_presentation_alias_evidence_error(
    relation: object,
    *,
    folder: Path,
    artifact_path: Path,
    source_lines: list[str],
    alias_label: str,
    canonical_label: str,
) -> str:
    """Validate source content that expressly relates two differently labelled results.

    A map key, a Lean declaration, or two superficially similar statements do
    not establish that different visible labels designate one result. The
    narrow exception exists only where the current source itself says it is
    restating the two independently discovered presentations.
    """

    if not isinstance(relation, dict):
        return "has no readable repeated-presentation relation metadata"
    evidence = relation.get(SOURCE_PRESENTATION_ALIAS_RENUMBERED_EVIDENCE_FIELD)
    if not isinstance(evidence, dict):
        return "has no byte-pinned source relation evidence"

    required = {
        "path",
        "line_start",
        "line_end",
        "quoted_text",
        "quoted_text_sha256",
    }
    missing = sorted(required - set(evidence))
    if missing:
        return "source relation evidence is missing " + ", ".join(missing)

    candidate, path_error = resolve_paper_source_path(folder, evidence.get("path"))
    if candidate is None or candidate != artifact_path:
        return "source relation evidence does not identify the current pinned source artifact" + (
            f" ({path_error})" if path_error else ""
        )
    line_start = evidence.get("line_start")
    line_end = evidence.get("line_end")
    if (
        not isinstance(line_start, int)
        or isinstance(line_start, bool)
        or not isinstance(line_end, int)
        or isinstance(line_end, bool)
    ):
        return "source relation evidence has non-integer line bounds"
    expected = normalized_source_line_excerpt(source_lines, line_start, line_end)
    if expected is None:
        return "source relation evidence has out-of-range line bounds"
    quote = evidence.get("quoted_text")
    digest = evidence.get("quoted_text_sha256")
    if not isinstance(quote, str) or not quote:
        return "source relation evidence has no quoted source text"
    normalized_quote = quote.replace("\r\n", "\n").replace("\r", "\n")
    if normalized_quote != expected:
        return "source relation evidence is not the exact current source excerpt"
    if (
        not isinstance(digest, str)
        or not SHA256_RE.fullmatch(digest.strip())
        or hashlib.sha256(normalized_quote.encode("utf-8")).hexdigest()
        != digest.strip().lower()
    ):
        return "source relation evidence has an invalid current quote digest"
    if not _RENUMBERED_RESTATEMENT_TEXT_RE.search(normalized_quote):
        return "source relation evidence does not materially state a restatement"

    def mentions_visible_label(label: str) -> bool:
        return bool(
            re.search(
                r"(?<![A-Za-z0-9])" + re.escape(label) + r"(?![A-Za-z0-9])",
                normalized_quote,
                flags=re.IGNORECASE,
            )
        )

    if not mentions_visible_label(alias_label) or not mentions_visible_label(
        canonical_label
    ):
        return (
            "source relation evidence must name both independently discovered visible labels"
        )
    return ""


def source_named_result_inventory_findings(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
    *,
    require_source_bytes: bool = True,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[Finding]:
    """Reconcile independently discovered named source results to map spans.

    This is intentionally a source-only completeness check.  It does not read
    source-map keys, ``source_kind``, Lean declarations, or review-row names to
    decide whether a source result exists.  The selector is used only after a
    result is discovered, so a deep-only map row cannot absorb a named theorem
    outside the ordinary coverage surface.
    """

    # A named-result receipt certifies the *complete* ordinary source surface.
    # A partially formalized or conditional paper can still use this validator
    # when it has supplied a receipt, but must not be treated as having made
    # that full-closeout claim merely by publishing an intermediate status.
    require_receipt = status in FULL_CLOSEOUT_STATUSES
    review_present = SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY in payload
    if not require_receipt and not review_present:
        return []

    severity = finding_severity(status)
    findings: list[Finding] = []

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(manifest_path), message))

    def add_receipt_errors(presentation_digest: str | None = None) -> None:
        for error in source_named_result_inventory_review_errors(
            payload,
            require_explicit=require_receipt,
            presentation_digest=presentation_digest,
        ):
            add(error)

    if require_receipt and payload.get(SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY) is not True:
        add(
            "named-result inventory closeout requires "
            f"{SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY}: true so source-span coverage is byte-verified"
        )

    pin_findings = source_artifact_pin_findings(
        folder,
        status,
        manifest_path,
        payload,
        require_source_bytes=require_source_bytes,
        file_bytes_override=file_bytes_override,
    )
    if pin_findings:
        # Without current source bytes there is no source-only presentation
        # digest to validate.  Still report the basic receipt contract once,
        # rather than duplicating it before and after the failed read.
        add_receipt_errors()
        return findings + pin_findings

    artifact_path, artifact_path_error = resolve_paper_source_path(
        folder, payload.get("source_artifact_path")
    )
    if artifact_path is None:
        add(
            "cannot resolve canonical source artifact for named-result inventory: "
            + artifact_path_error
        )
        add_receipt_errors()
        return findings
    if artifact_path.suffix.lower() not in TEXT_SOURCE_SUFFIXES:
        add(
            "named-result inventory reconciliation requires a UTF-8 text or TeX canonical "
            "source artifact, not only a binary/PDF pin"
        )
        add_receipt_errors()
        return findings
    try:
        source_text = normalized_source_text(
            _exact_file_bytes(artifact_path, file_bytes_override)
        )
    except UnicodeDecodeError:
        add(
            "named-result inventory reconciliation requires a UTF-8 text or TeX canonical source artifact"
        )
        add_receipt_errors()
        return findings
    except (OSError, RuntimeError) as error:
        add(f"cannot read canonical source artifact for named-result inventory: {error}")
        add_receipt_errors()
        return findings

    prose_definition_ids, prose_definition_errors = (
        source_vocabulary_definition_binding_item_ids(
            folder,
            payload,
            repository_root=ROOT,
            file_bytes_override=file_bytes_override,
        )
    )
    for error in prose_definition_errors:
        add("source prose-definition inventory: " + error)

    source_format = "tex" if artifact_path.suffix.lower() == ".tex" else "text"
    environment_kinds, heading_kinds = source_named_result_presentation_kinds(payload)
    try:
        presentations = extract_named_result_presentations(
            source_text,
            source_format=source_format,
            environment_kinds=environment_kinds,
            heading_kinds=heading_kinds,
        )
    except ValueError as error:
        add(
            f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY} presentation classification is invalid: {error}"
        )
        add_receipt_errors()
        return findings
    source_coverage_mode, _mode_error = source_coverage_mode_from_map(payload)
    replaced_definition_spans = source_prose_definition_replaced_named_presentation_spans(
        folder,
        payload,
        presentations,
        repository_root=ROOT,
        file_bytes_override=file_bytes_override,
    )
    # The receipt covers the semantic source surface selected by the active
    # policy, not every mechanically recognized display. In normal mode this
    # omits standalone Formula/Equation/Algorithm presentations;
    # unclassified named presentations remain included so they still block a
    # closeout until the source receipt classifies them.
    receipt_presentations = [
        presentation
        for presentation in presentations
        if source_named_presentation_in_coverage_scope(
            presentation.kind, source_coverage_mode
        )
        and not (
            presentation.kind == "definition"
            and (presentation.line_start, presentation.line_end)
            in replaced_definition_spans
        )
    ]
    presentation_digest = named_result_presentations_sha256(receipt_presentations)
    add_receipt_errors(presentation_digest)

    for presentation in presentations:
        if presentation.kind != UNCLASSIFIED_NAMED_PRESENTATION_KIND:
            continue
        add(
            "independent source named-result index found an unclassified named "
            f"presentation `{presentation.label}` at "
            f"{payload.get('source_artifact_path')}:{presentation.line_start}-{presentation.line_end}; "
            "classify its visible source environment or heading in "
            f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY}.environment_kinds or "
            f"{SOURCE_NAMED_RESULT_INVENTORY_REVIEW_KEY}.heading_kinds before closeout"
        )

    scoped_payload, _scoped_items = scoped_source_map_payload(
        payload,
        source_coverage_mode,
        folder=folder,
        repository_root=ROOT,
    )
    # ``scoped_payload`` retains legacy and explicit obligation rows for their
    # own validators. The source-heading coverage decision below is stricter:
    # it can use only rows independently reconciled to current bytes through
    # exact anchors, never a legacy source_kind/text selector or source_location.
    del scoped_payload
    raw_items = payload.get("items")
    if isinstance(raw_items, dict):
        for raw_item in raw_items.values():
            for error in source_presentation_reconciliation_errors(
                raw_item,
                presentations,
                source_text=source_text,
                source_path=str(payload.get("source_artifact_path") or ""),
            ):
                add(error)
    strict_items = (
        {
            # Keep only exact anchors for the second reconciliation. This
            # prevents a broad source_location or any map metadata from
            # absorbing a different result after strict selection.
            item_id: {
                "source_anchor_evidence": raw_items[item_id].get(
                    "source_anchor_evidence"
                ),
                **(
                    {
                        SOURCE_PRESENTATION_RECONCILIATION_FIELD: raw_items[
                            item_id
                        ].get(SOURCE_PRESENTATION_RECONCILIATION_FIELD)
                    }
                    if SOURCE_PRESENTATION_RECONCILIATION_FIELD in raw_items[item_id]
                    else {}
                ),
            }
            for item_id in source_index_byte_pinned_anchor_item_ids(
                folder,
                payload,
                source_coverage_mode,
                repository_root=ROOT,
            )
            if isinstance(raw_items, dict) and isinstance(raw_items.get(item_id), dict)
        }
        if isinstance(raw_items, dict)
        else {}
    )
    in_scope_presentations = [
        presentation
        for presentation in presentations
        if source_named_presentation_in_coverage_scope(
            presentation.kind, source_coverage_mode
        )
        and not (
            presentation.kind == "definition"
            and (presentation.line_start, presentation.line_end)
            in replaced_definition_spans
        )
        and presentation.kind
        not in {
            UNCLASSIFIED_NAMED_PRESENTATION_KIND,
            OPEN_NAMED_PRESENTATION_KIND,
        }
    ]
    reconciliations = reconcile_named_result_presentations(
        in_scope_presentations,
        strict_items,
        source_text=source_text,
        source_path=str(payload.get("source_artifact_path") or ""),
    )
    presentations_by_item: dict[str, set[tuple[str, int, int]]] = {}
    presentation_details_by_item: dict[
        str, set[tuple[str, str, int, int, str]]
    ] = {}
    for reconciliation in reconciliations:
        presentation = reconciliation.presentation
        presentation_identity = (
            presentation.kind,
            presentation.line_start,
            presentation.line_end,
        )
        presentation_details = (
            presentation.kind,
            presentation.label,
            presentation.line_start,
            presentation.line_end,
            presentation.presentation,
        )
        for match in reconciliation.matches:
            presentations_by_item.setdefault(match.item_id, set()).add(
                presentation_identity
            )
            presentation_details_by_item.setdefault(match.item_id, set()).add(
                presentation_details
            )
    for item_id, matched_presentations in sorted(presentations_by_item.items()):
        if len(matched_presentations) > 1:
            add(
                "in-scope source-map item `"
                + item_id
                + "` spans multiple independent discovered named results; split it into "
                "one tightly anchored source item per named presentation"
            )
    # A proof appendix may visibly restate an earlier numbered theorem.  The
    # source-only alias relation keeps both independently discovered spans in
    # the inventory, while requiring byte-pinned evidence that they present
    # the same visible source result.  The human semantic basis in the map
    # covers hypotheses/scope/conclusion; this check verifies that it is tied
    # to two distinct current source presentations rather than a map or Lean
    # naming convention.
    presentation_aliases, _presentation_alias_errors = source_presentation_aliases(
        raw_items
    )
    for alias_item, canonical_item in sorted(presentation_aliases.items()):
        alias_presentations = presentation_details_by_item.get(alias_item, set())
        canonical_presentations = presentation_details_by_item.get(
            canonical_item, set()
        )
        if len(alias_presentations) != 1 or len(canonical_presentations) != 1:
            add(
                "repeated-source-presentation alias `"
                + alias_item
                + "` and canonical item `"
                + canonical_item
                + "` must each have exactly one byte-pinned in-scope source presentation"
            )
            continue
        alias_presentation = next(iter(alias_presentations))
        canonical_presentation = next(iter(canonical_presentations))
        if alias_presentation[0] != canonical_presentation[0]:
            add(
                "repeated-source-presentation alias `"
                + alias_item
                + "` does not preserve the canonical visible source result kind"
            )
        elif alias_presentation[1] != canonical_presentation[1]:
            alias_map_item = raw_items.get(alias_item)
            relation = (
                alias_map_item.get("source_presentation_alias")
                if isinstance(alias_map_item, dict)
                else None
            )
            label_relation = (
                relation.get(SOURCE_PRESENTATION_ALIAS_LABEL_RELATION_FIELD)
                if isinstance(relation, dict)
                else None
            )
            if (
                label_relation
                != SOURCE_PRESENTATION_ALIAS_EXPLICIT_RENUMBERED_RESTATEMENT
            ):
                add(
                    "repeated-source-presentation alias `"
                    + alias_item
                    + "` does not preserve the canonical visible source result label; "
                    "a differently labelled presentation requires explicit current source "
                    "renumbered-restatement evidence"
                )
            else:
                relation_error = renumbered_presentation_alias_evidence_error(
                    relation,
                    folder=folder,
                    artifact_path=artifact_path,
                    source_lines=normalized_source_lines(source_text),
                    alias_label=alias_presentation[1],
                    canonical_label=canonical_presentation[1],
                )
                if relation_error:
                    add(
                        "repeated-source-presentation alias `"
                        + alias_item
                        + "` has invalid explicit renumbered-restatement evidence: "
                        + relation_error
                    )
        if alias_presentation[2:4] == canonical_presentation[2:4]:
            add(
                "repeated-source-presentation alias `"
                + alias_item
                + "` must anchor a distinct source presentation from canonical item `"
                + canonical_item
                + "`"
            )
    for presentation in uncovered_named_result_presentations(reconciliations):
        add(
            "independent source named-result index found an uncovered "
            f"{presentation.kind} presentation `{presentation.label}` at "
            f"{payload.get('source_artifact_path')}:{presentation.line_start}-{presentation.line_end}; "
            "add an in-scope source-map item anchored to this source span"
        )

    # A named conjecture/open question is not a theorem-proof target, but it
    # is still part of the source inventory.  Reconcile it to the raw map so
    # normal named-theory scope cannot silently erase it, then require an
    # explicit source-declared-open disposition and an exact anchor.
    all_items = raw_items if isinstance(raw_items, dict) else {}
    open_presentations = [
        presentation
        for presentation in presentations
        if presentation.kind == OPEN_NAMED_PRESENTATION_KIND
    ]
    open_reconciliations = reconcile_named_result_presentations(
        open_presentations,
        all_items,
        source_text=source_text,
        source_path=str(payload.get("source_artifact_path") or ""),
    )
    for reconciliation in open_reconciliations:
        presentation = reconciliation.presentation
        if not reconciliation.matches:
            add(
                "independent source named-result index found an uncatalogued named "
                f"open presentation `{presentation.label}` at "
                f"{payload.get('source_artifact_path')}:{presentation.line_start}-{presentation.line_end}; "
                "add a byte-pinned source-map item with the explicit source-declared-open disposition"
            )
            continue
        valid_open_disposition = False
        for match in reconciliation.matches:
            raw_item = all_items.get(match.item_id)
            if not isinstance(raw_item, dict):
                continue
            has_exact_anchor = any(
                evidence.startswith("source_anchor_evidence[")
                for evidence in match.evidence
            )
            if (
                has_exact_anchor
                and str(raw_item.get("source_kind") or "").strip().lower()
                == "open_problem"
                and raw_item.get("claim_bearing") is False
                and str(raw_item.get("source_scope_classification") or "")
                .strip()
                .lower()
                == SOURCE_DECLARED_OPEN_NONRESULT_OBSERVATION
                and str(raw_item.get("coverage_status") or "").strip().lower()
                == "source_declared_open"
                and str(raw_item.get("protocol_role") or "").strip().lower()
                == "source_declared_open"
                and str(raw_item.get("scope_reason") or "").strip()
                and str(raw_item.get("source_evidence") or "").strip()
            ):
                valid_open_disposition = True
                break
        if not valid_open_disposition:
            add(
                "named open presentation `"
                + presentation.label
                + "` must be anchored by a source-map item with source_kind "
                "`open_problem`, claim_bearing: false, "
                "source_scope_classification: "
                "`source_declared_open_nonresult_observation`, and "
                "coverage_status/protocol_role: `source_declared_open` with source-facing reason/evidence"
            )
    return findings


def check_source_manifest(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    file_bytes_override = (
        context.file_bytes_override() if context is not None else None
    )
    path = transaction_sidecar(folder, "paper_statement_map.json", context)
    payload = transaction_json(path, context)
    if payload is None:
        return [
            Finding(
                finding_severity(status),
                folder.name,
                rel(path),
                "source statement inventory is missing or invalid; add "
                "audit/paper_statement_map.json with top-level "
                "source_artifact_path and source_artifact_sha256",
            )
        ]
    if not isinstance(payload, dict):
        return source_map_scope_integrity_findings(folder, status, path, payload)

    findings = source_map_scope_integrity_findings(folder, status, path, payload)
    source_coverage_mode, mode_findings = source_coverage_mode_findings(
        folder, status, path, payload
    )
    findings.extend(mode_findings)
    pin_findings = source_artifact_pin_findings(
        folder,
        status,
        path,
        payload,
        require_source_bytes=require_source_bytes,
        file_bytes_override=file_bytes_override,
    )
    if pin_findings:
        return findings + pin_findings
    findings.extend(
        source_named_result_inventory_findings(
            folder,
            status,
            path,
            payload,
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        )
    )
    scoped_payload, _coverage_items = scoped_source_map_payload(
        payload,
        source_coverage_mode,
        folder=folder,
        repository_root=ROOT,
    )
    findings.extend(
        source_anchor_evidence_findings(
            folder,
            status,
            path,
            scoped_payload,
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        )
    )
    findings.extend(
        semantic_context_requirement_findings(
            folder,
            status,
            path,
            # Source-only context records govern how every selected Lean
            # statement is interpreted.  They are not themselves claim
            # coverage rows, so normal named-theory scoping must not make an
            # invalid convention/domain anchor disappear from the manifest
            # gate merely because its host item is otherwise out of scope.
            payload,
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        )
    )
    findings.extend(
        user_approved_scope_exclusion_map_findings(
            folder,
            status,
            path,
            # Exclusions are deliberately removed from the ordinary coverage
            # projection.  Their authorization and exact source pin must
            # nevertheless be checked on the raw map, or a malformed
            # exclusion could disappear before its dedicated validator runs.
            payload,
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        )
    )
    # Corrected targets are explicit governing-source repairs and retain their
    # all-map validation lane even under ordinary named-theory coverage.
    findings.extend(
        corrected_source_statement_map_findings(
            folder,
            status,
            payload,
            context=context,
        )
    )
    findings.extend(
        semantic_surface_inventory_findings(
            folder,
            status,
            scoped_payload,
            context=context,
        )
    )
    return findings


def source_claim_atoms_validation_errors(
    raw_atoms: object,
    *,
    require_source_quote: bool = False,
) -> list[str]:
    """Validate source-first theorem-clause atoms without trusting Lean names.

    The atom text is deliberately independent of the source-map item key and
    of the Lean declaration spelling.  ``reviewed_lean_route`` is retained
    only as a route for the repository audit to resolve against the configured
    review surface.  It cannot by itself establish that a source clause was
    inventoried or that its mathematical content was reviewed.  A
    ``source_quote_sha256`` is accepted for all maps, but is required only by
    the strict source-Spec realization lane; legacy atom maps must not become
    malformed merely because they predate that credential.
    """

    if not isinstance(raw_atoms, list) or not raw_atoms:
        return ["source_claim_atoms must be a nonempty list"]

    errors: list[str] = []
    seen_ids: set[str] = set()
    for index, raw_atom in enumerate(raw_atoms):
        prefix = f"source_claim_atoms[{index}]"
        if not isinstance(raw_atom, dict):
            errors.append(f"{prefix} must be an object")
            continue
        unexpected = sorted(set(raw_atom) - SOURCE_CLAIM_ATOM_FIELDS)
        if unexpected:
            errors.append(
                f"{prefix} has unsupported field(s): " + ", ".join(unexpected)
            )
        missing = sorted(SOURCE_CLAIM_ATOM_REQUIRED_FIELDS - set(raw_atom))
        if missing:
            errors.append(
                f"{prefix} is missing required field(s): " + ", ".join(missing)
            )

        atom_id = raw_atom.get("id")
        if not isinstance(atom_id, str) or not SOURCE_CLAIM_ATOM_ID_RE.fullmatch(
            atom_id.strip()
        ):
            errors.append(
                f"{prefix}.id must use a nonempty stable atom identifier"
            )
        elif atom_id.strip() in seen_ids:
            errors.append(f"{prefix}.id duplicates `{atom_id.strip()}`")
        else:
            seen_ids.add(atom_id.strip())

        locator = raw_atom.get("source_locator")
        matches = (
            list(SOURCE_FILE_LINE_RE.finditer(locator))
            if isinstance(locator, str)
            else []
        )
        if not isinstance(locator, str) or not locator.strip():
            errors.append(f"{prefix}.source_locator must be a nonempty string")
        elif len(matches) != 1:
            errors.append(
                f"{prefix}.source_locator must contain exactly one file:line source span"
            )

        semantic_claim = raw_atom.get("semantic_claim")
        if not meaningful_semantic_text(semantic_claim):
            errors.append(
                f"{prefix}.semantic_claim must contain a substantive source-facing claim"
            )

        route = raw_atom.get("reviewed_lean_route")
        if not isinstance(route, str) or not route.strip():
            errors.append(
                f"{prefix}.reviewed_lean_route must be a nonempty string"
            )
        elif isinstance(semantic_claim, str) and semantic_claim.strip() in {
            route.strip(),
            route.strip().rsplit(".", 1)[-1],
        }:
            errors.append(
                f"{prefix}.semantic_claim cannot be a Lean route/name in place of source semantics"
            )

        quote_digest = raw_atom.get(SOURCE_CLAIM_ATOM_SOURCE_QUOTE_SHA256_FIELD)
        if quote_digest is None and require_source_quote:
            errors.append(
                f"{prefix}.{SOURCE_CLAIM_ATOM_SOURCE_QUOTE_SHA256_FIELD} is required "
                "for source-spec correspondence"
            )
        elif quote_digest is not None and (
            not isinstance(quote_digest, str)
            or not SHA256_RE.fullmatch(quote_digest.strip())
        ):
            errors.append(
                f"{prefix}.{SOURCE_CLAIM_ATOM_SOURCE_QUOTE_SHA256_FIELD} "
                "must be a SHA-256 digest when present"
            )
    return errors


def source_claim_atom_semantic_sha256(raw_atom: object) -> str:
    """Return one name-free, source-first atom identity.

    Atom identifiers and reviewed Lean routes are navigation metadata.  They
    deliberately do not participate here: renaming either must not make a
    different source clause appear.  The source locator and source-facing
    mathematical claim are the base content.  When supplied, the exact quoted
    source-slice digest is also content: strict correspondence cannot retain a
    reusable atom identity after the anchored source text changed.
    """

    if not isinstance(raw_atom, dict):
        return ""
    locator = raw_atom.get("source_locator")
    claim = raw_atom.get("semantic_claim")
    if not isinstance(locator, str) or not locator.strip():
        return ""
    if not meaningful_semantic_text(claim):
        return ""
    identity: dict[str, str] = {
        "source_locator": locator.strip(),
        "semantic_claim": str(claim).strip(),
    }
    quote_digest = raw_atom.get(SOURCE_CLAIM_ATOM_SOURCE_QUOTE_SHA256_FIELD)
    if quote_digest is not None:
        if not isinstance(quote_digest, str) or not SHA256_RE.fullmatch(
            quote_digest.strip()
        ):
            return ""
        identity[SOURCE_CLAIM_ATOM_SOURCE_QUOTE_SHA256_FIELD] = (
            quote_digest.strip().lower()
        )
    return canonical_json_digest(identity)


def source_claim_atoms_semantic_sha256(raw_atoms: object) -> str:
    """Hash the complete individually anchored source-claim atom inventory.

    A duplicate content identity is deliberately ambiguous in the realization
    correspondence: one source anchor cannot silently discharge two claimed
    clauses merely because their row IDs differ.  Callers receive ``""`` and
    report a shape error instead of choosing by list position or item key.
    """

    if source_claim_atoms_validation_errors(raw_atoms):
        return ""
    assert isinstance(raw_atoms, list)
    atoms = [source_claim_atom_semantic_sha256(atom) for atom in raw_atoms]
    if not atoms or any(not SHA256_RE.fullmatch(atom) for atom in atoms):
        return ""
    if len(set(atoms)) != len(atoms):
        return ""
    return canonical_json_digest(
        {"schema": SOURCE_CLAIM_ATOMS_SCHEMA, "source_atoms": sorted(atoms)}
    )


def _source_claim_atoms_current_quote_binding_errors(
    folder: Path,
    raw_atoms: object,
    *,
    source_artifact_path: object,
    source_artifact_sha256: object,
) -> list[str]:
    """Verify strict atom receipts against the current canonical source bytes.

    This intentionally derives the expected quote from the locator's exact
    ``file:line[-line]`` range.  It never accepts supplied prose as the quote,
    so changing an atom's paraphrase, identifier, or Lean route cannot mask a
    stale source slice.  The raw artifact digest is checked first; the stored
    quote digest then binds one semantic atom to the current normalized line
    excerpt of that already byte-pinned artifact.

    Shape errors (missing locator / digest, malformed ranges) belong to
    :func:`source_claim_atoms_validation_errors`; this helper avoids repeating
    them and only resolves atom fields that are syntactically usable.
    """

    artifact_path, artifact_path_error = resolve_paper_source_path(
        folder, source_artifact_path
    )
    if artifact_path is None:
        return [
            "cannot resolve the canonical source artifact for source-claim atom "
            "quote validation: "
            + artifact_path_error
        ]
    if not artifact_path.is_file():
        return [
            "canonical source artifact is not a readable regular file for "
            "source-claim atom quote validation"
        ]

    expected_artifact_digest = str(source_artifact_sha256 or "").strip().lower()
    if not SHA256_RE.fullmatch(expected_artifact_digest):
        return [
            "source_artifact_sha256 must be a SHA-256 digest before source-claim "
            "atom quote validation"
        ]
    try:
        source_bytes = artifact_path.read_bytes()
    except OSError as error:
        return [
            "cannot read canonical source artifact for source-claim atom quote "
            f"validation: {error}"
        ]
    actual_artifact_digest = hashlib.sha256(source_bytes).hexdigest()
    if actual_artifact_digest != expected_artifact_digest:
        return [
            "source_artifact_sha256 does not match the current canonical source "
            "artifact; source-claim atom quotes are stale"
        ]
    try:
        source_lines = normalized_source_lines(normalized_source_text(source_bytes))
    except UnicodeDecodeError:
        return [
            "canonical source artifact must be UTF-8 text for exact source-claim "
            "atom quote validation"
        ]

    if not isinstance(raw_atoms, list):
        return []

    errors: list[str] = []
    for index, raw_atom in enumerate(raw_atoms):
        if not isinstance(raw_atom, dict):
            continue
        prefix = f"source_claim_atoms[{index}]"
        locator = raw_atom.get("source_locator")
        matches = (
            list(SOURCE_FILE_LINE_RE.finditer(locator))
            if isinstance(locator, str)
            else []
        )
        if len(matches) != 1:
            continue
        quote_digest = raw_atom.get(SOURCE_CLAIM_ATOM_SOURCE_QUOTE_SHA256_FIELD)
        if not isinstance(quote_digest, str) or not SHA256_RE.fullmatch(
            quote_digest.strip()
        ):
            continue

        match = matches[0]
        candidate, path_error = resolve_paper_source_path(folder, match.group("path"))
        start = int(match.group("start"))
        end = int(match.group("end") or start)
        if candidate is None:
            errors.append(
                f"{prefix}.source_locator source span `{match.group('path')}:"
                f"{start}-{end}` {path_error}"
            )
            continue
        if candidate != artifact_path:
            errors.append(
                f"{prefix}.source_locator must identify the canonical pinned source "
                "artifact for source-spec correspondence"
            )
            continue
        quote = normalized_source_line_excerpt(source_lines, start, end)
        if quote is None:
            errors.append(
                f"{prefix}.source_locator line range {start}-{end} is outside the "
                "current canonical source artifact"
            )
            continue
        current_quote_digest = hashlib.sha256(quote.encode("utf-8")).hexdigest()
        if quote_digest.strip().lower() != current_quote_digest:
            errors.append(
                f"{prefix}.{SOURCE_CLAIM_ATOM_SOURCE_QUOTE_SHA256_FIELD} does not "
                "match the exact current canonical source line slice"
            )
    return errors


def _source_spec_semantic_basis_validation_errors(raw_basis: object) -> list[str]:
    """Validate an explicit, pinned supplemental semantic basis shape.

    This is intentionally not a route taxonomy.  A basis can document a
    correction, an additional assumption, or an external primitive, but it
    always has to expose the exact semantic statement and a version-pinned
    artifact/anchor.  It never receives credit merely because a caller calls
    it a convention, data object, or derivation.
    """

    if not isinstance(raw_basis, dict):
        return ["semantic_basis must be an object"]
    errors: list[str] = []
    unexpected = sorted(set(raw_basis) - SOURCE_SPEC_SEMANTIC_BASIS_FIELDS)
    if unexpected:
        errors.append("semantic_basis has unsupported field(s): " + ", ".join(unexpected))
    missing = sorted(SOURCE_SPEC_SEMANTIC_BASIS_FIELDS - set(raw_basis))
    if missing:
        errors.append("semantic_basis is missing required field(s): " + ", ".join(missing))
    artifact_path = raw_basis.get("artifact_path")
    if not isinstance(artifact_path, str) or not artifact_path.strip():
        errors.append("semantic_basis.artifact_path must be a nonempty paper-local path")
    artifact_sha = raw_basis.get("artifact_sha256")
    if not isinstance(artifact_sha, str) or not SHA256_RE.fullmatch(artifact_sha.strip()):
        errors.append("semantic_basis.artifact_sha256 must be a SHA-256 digest")
    locator = raw_basis.get("source_locator")
    if not isinstance(locator, str) or len(list(SOURCE_FILE_LINE_RE.finditer(locator))) != 1:
        errors.append("semantic_basis.source_locator must contain exactly one file:line anchor")
    if not meaningful_semantic_text(raw_basis.get("semantic_statement")):
        errors.append("semantic_basis.semantic_statement must be substantive source-facing text")
    return errors


def _source_spec_correspondence_identity_payload(
    raw_contract: object,
    raw_correspondence: object,
) -> dict[str, Any] | None:
    """Project a correspondence record to its name-free item reuse identity."""

    if not isinstance(raw_contract, dict) or not isinstance(raw_correspondence, dict):
        return None
    required = SOURCE_SPEC_CORRESPONDENCE_FIELDS - {"item_identity_sha256"}
    if not required.issubset(raw_correspondence):
        return None
    return {
        "schema": raw_correspondence.get("schema"),
        "source_atoms_sha256": raw_correspondence.get("source_atoms_sha256"),
        "spec_closure_sha256": raw_correspondence.get("spec_closure_sha256"),
        "spec_surface_sha256": raw_correspondence.get("spec_surface_sha256"),
        "closure_environment_sha256": raw_correspondence.get(
            "closure_environment_sha256"
        ),
        "source_atom_bindings": raw_correspondence.get("source_atom_bindings"),
        "closure_node_dispositions": raw_correspondence.get(
            "closure_node_dispositions"
        ),
        # The exact theorem-to-Spec check is rerun by Lean Meta.  These two
        # source-contract semantics, unlike declaration spellings, describe
        # the result relationship retained in a reusable item identity.
        "evidence_mode": raw_contract.get("evidence_mode"),
        "semantic_shape": raw_contract.get("semantic_shape"),
    }


def source_spec_correspondence_item_identity_sha256(
    raw_contract: object,
    raw_correspondence: object,
) -> str:
    """Return the exact structural reuse identity for one realization record."""

    payload = _source_spec_correspondence_identity_payload(
        raw_contract, raw_correspondence
    )
    return canonical_json_digest(payload) if payload is not None else ""


def source_spec_correspondence_validation_errors(
    raw_correspondence: object,
    *,
    raw_atoms: object,
    raw_contract: object,
) -> list[str]:
    """Validate the static, atom-level realization correspondence record.

    Lean later verifies that the supplied component hashes actually occur in
    the current elaborated `Spec` closure.  This fast validator intentionally
    checks only content-addressed structure and source atom completeness; it
    never grants credit from a source item key, a declaration name, a data
    classification, or free-form convention prose.
    """

    if not isinstance(raw_correspondence, dict):
        return ["source_spec_correspondence must be an object"]
    errors: list[str] = []
    unexpected = sorted(set(raw_correspondence) - SOURCE_SPEC_CORRESPONDENCE_FIELDS)
    if unexpected:
        errors.append(
            "source_spec_correspondence has unsupported field(s): "
            + ", ".join(unexpected)
        )
    missing = sorted(SOURCE_SPEC_CORRESPONDENCE_FIELDS - set(raw_correspondence))
    if missing:
        errors.append(
            "source_spec_correspondence is missing required field(s): "
            + ", ".join(missing)
        )
    if not schema_version_is_exact(
        raw_correspondence.get("schema"), SOURCE_SPEC_CORRESPONDENCE_SCHEMA
    ):
        errors.append(
            "source_spec_correspondence.schema must be "
            + str(SOURCE_SPEC_CORRESPONDENCE_SCHEMA)
        )
    for field in (
        "source_atoms_sha256",
        "spec_closure_sha256",
        "spec_surface_sha256",
        "closure_environment_sha256",
        "item_identity_sha256",
    ):
        value = raw_correspondence.get(field)
        if not isinstance(value, str) or not SHA256_RE.fullmatch(value.strip()):
            errors.append(f"source_spec_correspondence.{field} must be a SHA-256 digest")

    # A record in this validator is itself the strict realization
    # correspondence.  Its atom identities must therefore contain the exact
    # source-slice receipt, not merely a line locator plus an audited
    # paraphrase.  The inventory pass below verifies those digest bytes against
    # the current canonical artifact.
    atom_errors = source_claim_atoms_validation_errors(
        raw_atoms, require_source_quote=True
    )
    if atom_errors:
        errors.extend("source_claim_atoms " + error for error in atom_errors)
        atom_hashes: set[str] = set()
        atoms_digest = ""
    else:
        assert isinstance(raw_atoms, list)
        atom_hashes = {
            source_claim_atom_semantic_sha256(atom) for atom in raw_atoms
        }
        atoms_digest = source_claim_atoms_semantic_sha256(raw_atoms)
        if not atoms_digest:
            errors.append(
                "source_claim_atoms have duplicate or noncanonical semantic identities; "
                "split or distinguish the source clauses before binding them"
            )
        elif str(raw_correspondence.get("source_atoms_sha256") or "").strip().lower() != atoms_digest:
            errors.append(
                "source_spec_correspondence.source_atoms_sha256 does not match the "
                "current individually anchored source_claim_atoms content"
            )

    bindings = raw_correspondence.get("source_atom_bindings")
    seen_atoms: set[str] = set()
    component_to_bindings: dict[str, list[dict[str, Any]]] = {}
    if not isinstance(bindings, list) or not bindings:
        errors.append("source_spec_correspondence.source_atom_bindings must be a nonempty list")
    else:
        for index, raw_binding in enumerate(bindings):
            prefix = f"source_spec_correspondence.source_atom_bindings[{index}]"
            if not isinstance(raw_binding, dict):
                errors.append(f"{prefix} must be an object")
                continue
            unexpected_binding = sorted(
                set(raw_binding) - SOURCE_SPEC_ATOM_BINDING_FIELDS
            )
            if unexpected_binding:
                errors.append(
                    f"{prefix} has unsupported field(s): "
                    + ", ".join(unexpected_binding)
                )
            missing_binding = sorted(
                SOURCE_SPEC_ATOM_BINDING_FIELDS - {"overlap_justification"} - set(raw_binding)
            )
            if missing_binding:
                errors.append(
                    f"{prefix} is missing required field(s): "
                    + ", ".join(missing_binding)
                )
            atom_hash = str(raw_binding.get("source_atom_sha256") or "").strip().lower()
            if not SHA256_RE.fullmatch(atom_hash):
                errors.append(f"{prefix}.source_atom_sha256 must be a SHA-256 digest")
            elif atom_hash not in atom_hashes:
                errors.append(
                    f"{prefix}.source_atom_sha256 does not identify a current source claim atom"
                )
            elif atom_hash in seen_atoms:
                errors.append(
                    f"{prefix}.source_atom_sha256 duplicates a source atom; each atom has one repair handoff row"
                )
            else:
                seen_atoms.add(atom_hash)

            raw_components = raw_binding.get("spec_component_sha256s")
            if (
                not isinstance(raw_components, list)
                or not raw_components
                or any(
                    not isinstance(component, str)
                    or not SHA256_RE.fullmatch(component.strip())
                    for component in raw_components
                )
                or len({str(component).strip().lower() for component in raw_components})
                != len(raw_components)
            ):
                errors.append(
                    f"{prefix}.spec_component_sha256s must be a nonempty list of unique SHA-256 digests"
                )
            else:
                for component in raw_components:
                    component_to_bindings.setdefault(
                        str(component).strip().lower(), []
                    ).append(raw_binding)
            if not meaningful_semantic_text(raw_binding.get("semantic_bridge")):
                errors.append(
                    f"{prefix}.semantic_bridge must explain the source-clause to Spec-component correspondence"
                )

    if atom_hashes and seen_atoms != atom_hashes:
        missing_atoms = sorted(atom_hashes - seen_atoms)
        extra_atoms = sorted(seen_atoms - atom_hashes)
        detail: list[str] = []
        if missing_atoms:
            detail.append("missing " + ", ".join(missing_atoms[:3]))
        if extra_atoms:
            detail.append("unknown " + ", ".join(extra_atoms[:3]))
        errors.append(
            "source_spec_correspondence.source_atom_bindings must cover every current "
            "source claim atom exactly once" + (": " + "; ".join(detail) if detail else "")
        )
    for component, component_bindings in component_to_bindings.items():
        if len(component_bindings) <= 1:
            continue
        if any(
            not meaningful_semantic_text(binding.get("overlap_justification"))
            for binding in component_bindings
        ):
            errors.append(
                "source_spec_correspondence source atoms overlap on Spec component `"
                + component
                + "` without an explicit substantive overlap_justification on every row"
            )

    dispositions = raw_correspondence.get("closure_node_dispositions")
    if not isinstance(dispositions, list):
        errors.append("source_spec_correspondence.closure_node_dispositions must be a list")
    else:
        seen_components: set[str] = set()
        for index, raw_disposition in enumerate(dispositions):
            prefix = f"source_spec_correspondence.closure_node_dispositions[{index}]"
            if not isinstance(raw_disposition, dict):
                errors.append(f"{prefix} must be an object")
                continue
            unexpected_disposition = sorted(
                set(raw_disposition) - SOURCE_SPEC_NODE_DISPOSITION_FIELDS
            )
            if unexpected_disposition:
                errors.append(
                    f"{prefix} has unsupported field(s): "
                    + ", ".join(unexpected_disposition)
                )
            component = str(raw_disposition.get("closure_component_sha256") or "").strip().lower()
            if not SHA256_RE.fullmatch(component):
                errors.append(f"{prefix}.closure_component_sha256 must be a SHA-256 digest")
            elif component in seen_components:
                errors.append(
                    f"{prefix}.closure_component_sha256 duplicates a material closure node disposition"
                )
            else:
                seen_components.add(component)
            atom_hash = raw_disposition.get("source_atom_sha256")
            if atom_hash is not None:
                atom_text = str(atom_hash).strip().lower()
                if not SHA256_RE.fullmatch(atom_text) or atom_text not in atom_hashes:
                    errors.append(
                        f"{prefix}.source_atom_sha256 must identify a current source claim atom"
                    )
            basis = raw_disposition.get("semantic_basis")
            if atom_hash is None and basis is None:
                errors.append(
                    f"{prefix} needs a current source_atom_sha256 or an explicit pinned semantic_basis"
                )
            if basis is not None:
                errors.extend(
                    f"{prefix}." + error
                    for error in _source_spec_semantic_basis_validation_errors(basis)
                )
            node_pin = raw_disposition.get("pinned_declaration_identity_sha256")
            if node_pin is not None and (
                not isinstance(node_pin, str)
                or not SHA256_RE.fullmatch(node_pin.strip())
            ):
                errors.append(
                    f"{prefix}.pinned_declaration_identity_sha256 must be a SHA-256 digest when present"
                )

    expected_identity = source_spec_correspondence_item_identity_sha256(
        raw_contract, raw_correspondence
    )
    recorded_identity = str(raw_correspondence.get("item_identity_sha256") or "").strip().lower()
    if expected_identity and recorded_identity != expected_identity:
        errors.append(
            "source_spec_correspondence.item_identity_sha256 does not match the current "
            "atom-level source/Spec realization record"
        )
    return errors


def _source_map_proof_obligation_items(
    folder: Path,
    payload: object,
) -> tuple[dict[str, dict[str, Any]], str]:
    """Project one map onto its name-independent direct-proof obligations."""

    if not isinstance(payload, dict):
        return {}, ""
    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        return {}, ""
    mode, mode_error = source_coverage_mode_from_map(payload)
    source_index_ids = source_index_byte_pinned_anchor_item_ids(
        folder,
        payload,
        mode,
        repository_root=ROOT,
    )
    return (
        filter_source_map_items_for_proof_obligations(
            raw_items,
            mode,
            declared_environment_kinds=source_named_result_environment_kinds_from_map(
                payload
            ),
            additional_selected_item_ids=source_index_ids,
        ),
        mode_error,
    )


def source_claim_atom_inventory_findings(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Validate the opt-in atom inventory before resolving any Lean route.

    Older source maps have no atom schema and remain valid.  A new map opts in
    at its top level; every theorem-like presentation selected by the active
    semantic coverage mode (plus an explicit corrected target) then needs an
    atom for each source clause.  The independent source review must establish
    atom completeness from the pinned source statement; this mechanical pass
    verifies that no declared atom loses its source span or semantic text
    before the full repository pass validates its Lean route.
    """

    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    payload = transaction_json(map_path, context)
    if not isinstance(payload, dict):
        return []
    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        return []

    proof_obligation_items, _mode_error = _source_map_proof_obligation_items(
        folder, payload
    )
    presentation_aliases, _alias_errors = source_presentation_aliases(raw_items)
    atom_obligation_items = {
        source_key: raw_item
        for source_key, raw_item in proof_obligation_items.items()
        if source_key not in presentation_aliases
        and str(raw_item.get("source_kind") or "").strip().lower()
        in SOURCE_CLAIM_ATOM_THEOREM_LIKE_KINDS
        and str(raw_item.get("source_status") or "").strip().lower()
        not in SOURCE_SPEC_CORRESPONDENCE_NONCLAIM_STATUSES
    }

    marker_present = SOURCE_CLAIM_ATOMS_SCHEMA_KEY in payload
    atoms_present = any(
        SOURCE_CLAIM_ATOMS_KEY in raw_item
        for raw_item in atom_obligation_items.values()
    )
    if not marker_present and not atoms_present:
        return []

    severity = finding_severity(status)
    findings: list[Finding] = []
    file_bytes_override = (
        context.file_bytes_override() if context is not None else None
    )

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(map_path), message))

    if not marker_present:
        add(
            f"{SOURCE_CLAIM_ATOMS_SCHEMA_KEY} is required when an item uses "
            f"{SOURCE_CLAIM_ATOMS_KEY}"
        )
        return findings
    if not schema_version_is_exact(
        payload.get(SOURCE_CLAIM_ATOMS_SCHEMA_KEY), SOURCE_CLAIM_ATOMS_SCHEMA
    ):
        add(
            f"{SOURCE_CLAIM_ATOMS_SCHEMA_KEY} must be "
            f"{SOURCE_CLAIM_ATOMS_SCHEMA}"
        )
        return findings

    for raw_key, raw_item in atom_obligation_items.items():
        source_key = str(raw_key)
        if SOURCE_CLAIM_ATOMS_KEY not in raw_item:
            add(
                f"items.{source_key}: theorem-like source item must enumerate "
                f"{SOURCE_CLAIM_ATOMS_KEY} under schema "
                f"{SOURCE_CLAIM_ATOMS_SCHEMA}"
            )
            continue

        raw_atoms = raw_item.get(SOURCE_CLAIM_ATOMS_KEY)
        for error in source_claim_atoms_validation_errors(raw_atoms):
            add(f"items.{source_key}: {error}")
        if not isinstance(raw_atoms, list):
            continue
        for index, raw_atom in enumerate(raw_atoms):
            if not isinstance(raw_atom, dict):
                continue
            locator = raw_atom.get("source_locator")
            for error in source_file_line_anchor_errors(
                folder,
                locator,
                require_source_bytes=require_source_bytes,
                file_bytes_override=file_bytes_override,
            ):
                add(
                    f"items.{source_key}.{SOURCE_CLAIM_ATOMS_KEY}[{index}].source_locator "
                    f"{error}"
                )
            for error in canonical_artifact_source_span_errors(
                folder,
                locator,
                source_artifact_path=payload.get("source_artifact_path"),
            ):
                add(
                    f"items.{source_key}.{SOURCE_CLAIM_ATOMS_KEY}[{index}].source_locator "
                    f"{error}"
                )
    return findings


def source_spec_correspondence_enabled(payload: object) -> bool:
    """Whether a map explicitly requests the strict realization closeout lane."""

    return isinstance(payload, dict) and schema_version_is_exact(
        payload.get(SOURCE_SPEC_CORRESPONDENCE_SCHEMA_KEY),
        SOURCE_SPEC_CORRESPONDENCE_SCHEMA,
    )


def validated_presentation_alias_contract_exemptions(
    folder: Path,
    payload: object,
) -> dict[str, str]:
    """Return aliases that may inherit, but never own, a semantic contract.

    A repeated source presentation can be claim-bearing while its alias schema
    correctly forbids a second direct Lean route.  It can omit a duplicate
    contract only after three independent source checks: the alias metadata is
    valid, its canonical presentation owns the active proof obligation, and
    both presentations have distinct current byte-pinned source anchors.  A
    canonical compound theorem may legitimately be split into separate
    source-atom claims; in that case the canonical atom's exact current quote
    is the source anchor even when the broad named-result index assigns the
    presentation to a sibling clause.
    """

    if not isinstance(payload, dict):
        return {}
    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        return {}
    mode, mode_error = source_coverage_mode_from_map(payload)
    if mode_error:
        return {}
    aliases, _alias_errors = source_presentation_aliases(raw_items)
    if not aliases:
        return {}
    current_anchor_items = source_index_byte_pinned_anchor_item_ids(
        folder,
        payload,
        mode,
        repository_root=ROOT,
    )
    selected_items = filter_source_map_items_for_proof_obligations(
        raw_items,
        mode,
        declared_environment_kinds=source_named_result_environment_kinds_from_map(
            payload
        ),
        additional_selected_item_ids=current_anchor_items,
    )
    def canonical_has_current_atom_anchor(item: object) -> bool:
        if not isinstance(item, Mapping):
            return False
        atoms = item.get(SOURCE_CLAIM_ATOMS_KEY)
        if source_claim_atoms_validation_errors(atoms, require_source_quote=True):
            return False
        return not _source_claim_atoms_current_quote_binding_errors(
            folder,
            atoms,
            source_artifact_path=payload.get("source_artifact_path"),
            source_artifact_sha256=payload.get("source_artifact_sha256"),
        )

    return {
        alias: canonical
        for alias, canonical in aliases.items()
        if alias in current_anchor_items
        and (
            canonical in selected_items
            or canonical_has_current_atom_anchor(raw_items.get(canonical))
        )
        and (
            canonical in current_anchor_items
            or canonical_has_current_atom_anchor(raw_items.get(canonical))
        )
    }


def source_spec_correspondence_requirement_errors(
    status_payload: object,
) -> list[str]:
    """Validate the explicit future/reissue requirement switch, if present."""

    if not isinstance(status_payload, dict):
        return []
    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return []
    value = review_surface.get("require_source_spec_correspondence")
    if value is None:
        return []
    if not isinstance(value, bool):
        return [
            "review_surface.require_source_spec_correspondence must be Boolean when declared"
        ]
    return []


def source_spec_correspondence_required(status_payload: object) -> bool:
    """Whether a paper declares that v11 realization evidence is mandatory."""

    if not isinstance(status_payload, dict):
        return False
    review_surface = status_payload.get("review_surface")
    return (
        isinstance(review_surface, dict)
        and review_surface.get("require_source_spec_correspondence") is True
    )


def source_spec_correspondence_requested(
    status_payload: object,
    source_map_payload: object | None = None,
    *,
    folder: Path | None = None,
) -> bool:
    """Whether a paper must use the v11 realization protocol.

    The generated theorem-realization ledger is available to all source-record
    audits so it can be inspected or reused later.  Availability alone is not
    activation.  Explicit switches can activate the lane, but they cannot turn
    it off. A new paper is activated automatically by comparison with the
    centrally trusted legacy-v10 baseline; a material repair of a trusted
    legacy paper remains on the current item-level v10 lane unless it
    explicitly upgrades.
    """

    if source_spec_correspondence_required(status_payload):
        return True

    if source_spec_correspondence_enabled(source_map_payload):
        return True
    if not isinstance(status_payload, dict):
        return False
    review_surface = status_payload.get("review_surface")
    statement_review = (
        review_surface.get("llm_statement_review")
        if isinstance(review_surface, dict)
        else None
    )
    if isinstance(statement_review, dict):
        legacy_schema = statement_review.get(
            "require_theorem_realization_contract_schema"
        )
        if statement_review.get("require_theorem_realization_contract") is True or (
            schema_version_is_exact(legacy_schema, 1)
        ):
            return True
    if folder is None:
        return False
    try:
        folder.resolve().relative_to((ROOT / "papers").resolve())
    except ValueError:
        # Test/diagnostic callers may supply an isolated paper tree.  The
        # repository closeout inventory below still treats such a paper as
        # new, but this component-level helper has no trusted baseline root to
        # consult and therefore retains explicit-switch semantics.
        return False
    try:
        try:
            from scripts.theorem_realization_transition import (
                theorem_realization_reissue_requirement,
            )
        except ModuleNotFoundError:
            from theorem_realization_transition import (
                theorem_realization_reissue_requirement,
            )

        return theorem_realization_reissue_requirement(
            ROOT, folder, status_payload
        ).required
    except Exception:
        # Automatic reissue is an acceptance condition.  An unavailable
        # baseline comparison must never behave like an optional paper flag.
        return True


def raw_source_spec_screening_requested(
    status_payload: object,
    source_map_payload: object | None = None,
    *,
    folder: Path | None = None,
) -> bool:
    """Whether the direct raw-source/Lean-target review lane is selected.

    New v11 packets can certify direct source-to-Spec screening without
    retrofitting the older atom-level theorem-realization sidecar. The latter
    remains a stricter optional provenance lane; selecting this direct lane
    never causes its historical receipts to be silently treated as current.
    """

    if source_spec_correspondence_requested(
        status_payload, source_map_payload, folder=folder
    ):
        return True
    if not isinstance(status_payload, dict):
        return False
    review_surface = status_payload.get("review_surface")
    return bool(
        isinstance(review_surface, dict)
        and review_surface.get("require_v11_raw_source_spec_screening") is True
    )


def _source_spec_semantic_basis_artifact_errors(
    folder: Path,
    raw_basis: object,
    *,
    require_source_bytes: bool = True,
) -> tuple[list[str], tuple[str, str] | None]:
    """Check the current bytes and line anchor of a supplemental basis."""

    errors = _source_spec_semantic_basis_validation_errors(raw_basis)
    if errors or not isinstance(raw_basis, dict):
        return errors, None
    artifact_path = _paper_local_artifact_path(folder, raw_basis.get("artifact_path"))
    if artifact_path is None:
        return [
            "semantic_basis.artifact_path must name an existing paper-local artifact"
        ], None
    raw_artifact_path = str(raw_basis.get("artifact_path") or "").strip()
    expected_digest = str(raw_basis.get("artifact_sha256") or "").strip().lower()
    if not artifact_path.exists():
        if require_source_bytes:
            return [
                "semantic_basis.artifact_path must name an existing paper-local artifact"
            ], None
        # A semantic basis is itself a source-facing, byte-pinned source
        # artifact. Structural public checkouts may omit those licensed bytes,
        # just as they may omit the map's primary source artifact. Keep
        # validating path safety, digest shape, and exact locator agreement;
        # the caller emits one non-certifying warning per absent source pin.
        locator = str(raw_basis.get("source_locator") or "")
        errors.extend(
            "semantic_basis.source_locator " + error
            for error in source_file_line_anchor_errors(
                folder,
                locator,
                require_source_bytes=False,
            )
        )
        matches = list(SOURCE_FILE_LINE_RE.finditer(locator))
        if len(matches) == 1:
            anchored = Path(matches[0].group("path"))
            declared = Path(str(raw_basis.get("artifact_path") or "").strip())
            if anchored != declared:
                errors.append(
                    "semantic_basis.source_locator must point into semantic_basis.artifact_path"
                )
        return errors, (raw_artifact_path, expected_digest)
    if not artifact_path.is_file():
        return [
            "semantic_basis.artifact_path must name an existing paper-local artifact"
        ], None
    try:
        actual_digest = sha256_file(artifact_path)
    except OSError as error:
        return [f"semantic_basis.artifact_path could not be read: {error}"], None
    if actual_digest != expected_digest:
        errors.append(
            "semantic_basis.artifact_sha256 does not match its current paper-local artifact"
        )
    locator = str(raw_basis.get("source_locator") or "")
    for error in source_file_line_anchor_errors(folder, locator):
        errors.append("semantic_basis.source_locator " + error)
    matches = list(SOURCE_FILE_LINE_RE.finditer(locator))
    if len(matches) == 1:
        anchored = Path(matches[0].group("path"))
        declared = Path(str(raw_basis.get("artifact_path") or "").strip())
        if anchored != declared:
            errors.append(
                "semantic_basis.source_locator must point into semantic_basis.artifact_path"
            )
    return errors, None


def source_spec_correspondence_inventory_findings(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Validate required atom-level theorem-realization source records.

    This intentionally does not make unchanged legacy semantic contracts
    invalid. Explicit requests and the trusted new-paper selector activate
    v11; at that point every claim selected by the semantic coverage
    mode (plus corrected targets) is held to the stricter atom and closure-
    record shape. The repository Lean pass supplies the current elaborated
    closure and rejects absent components.
    """

    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    # Read the status switch before the source map. A closeout cannot evade a
    # declared realization requirement by deleting or corrupting the map; a
    # not-started scaffold may nevertheless declare its future requirement
    # before creating an inventory.
    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    requirement_errors = source_spec_correspondence_requirement_errors(status_payload)
    required_switch = source_spec_correspondence_required(status_payload)
    automatic_required = False
    automatic_reason = "explicit paper closeout requirement"
    if not required_switch:
        try:
            try:
                from scripts.theorem_realization_transition import (
                    theorem_realization_reissue_requirement,
                )
            except ModuleNotFoundError:
                from theorem_realization_transition import (
                    theorem_realization_reissue_requirement,
                )

            automatic_requirement = theorem_realization_reissue_requirement(
                ROOT, folder, status_payload
            )
            automatic_required = automatic_requirement.required
            automatic_reason = automatic_requirement.reason
        except Exception as error:
            automatic_required = True
            automatic_reason = f"trusted v11 transition comparison failed: {error}"
    required_at_closeout = status in CLOSEOUT_STATUSES and (
        required_switch or automatic_required
    )
    requirement_prefix = (
        "review_surface.require_source_spec_correspondence: true requires "
        if required_switch
        else "automatic v11 theorem-realization reissue requires "
    )
    payload = transaction_json(map_path, context)
    if not isinstance(payload, dict):
        if not requirement_errors and not required_at_closeout:
            return []
        severity = finding_severity(status)
        findings: list[Finding] = []

        def add_unreadable(message: str) -> None:
            findings.append(Finding(severity, folder.name, rel(map_path), message))

        for error in requirement_errors:
            add_unreadable(error)
        if required_at_closeout:
            add_unreadable(
                requirement_prefix
                + f"{SOURCE_SPEC_CORRESPONDENCE_SCHEMA_KEY}: "
                f"{SOURCE_SPEC_CORRESPONDENCE_SCHEMA} for closeout, but the canonical "
                "source map is missing or invalid ("
                + automatic_reason
                + ")"
            )
        return findings
    raw_items = payload.get("items")
    has_item_record = isinstance(raw_items, dict) and any(
        isinstance(raw_item, dict)
        and SOURCE_SPEC_CORRESPONDENCE_KEY in raw_item
        for raw_item in raw_items.values()
    )
    marker_present = SOURCE_SPEC_CORRESPONDENCE_SCHEMA_KEY in payload
    if (
        not marker_present
        and not has_item_record
        and not required_at_closeout
        and not requirement_errors
    ):
        return []

    severity = finding_severity(status)
    findings: list[Finding] = []

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(map_path), message))

    for error in requirement_errors:
        add(error)
    if not marker_present:
        if has_item_record:
            add(
                f"{SOURCE_SPEC_CORRESPONDENCE_SCHEMA_KEY} is required when an item uses "
                f"{SOURCE_SPEC_CORRESPONDENCE_KEY}"
            )
        if required_at_closeout:
            add(
                requirement_prefix
                + f"{SOURCE_SPEC_CORRESPONDENCE_SCHEMA_KEY}: "
                f"{SOURCE_SPEC_CORRESPONDENCE_SCHEMA} for closeout ("
                + automatic_reason
                + ")"
            )
        return findings
    if not schema_version_is_exact(
        payload.get(SOURCE_SPEC_CORRESPONDENCE_SCHEMA_KEY),
        SOURCE_SPEC_CORRESPONDENCE_SCHEMA,
    ):
        add(
            f"{SOURCE_SPEC_CORRESPONDENCE_SCHEMA_KEY} must be "
            + str(SOURCE_SPEC_CORRESPONDENCE_SCHEMA)
        )
        return findings
    if not schema_version_is_exact(
        payload.get(SOURCE_CLAIM_ATOMS_SCHEMA_KEY), SOURCE_CLAIM_ATOMS_SCHEMA
    ):
        add(
            f"{SOURCE_SPEC_CORRESPONDENCE_SCHEMA_KEY} requires "
            f"{SOURCE_CLAIM_ATOMS_SCHEMA_KEY}: {SOURCE_CLAIM_ATOMS_SCHEMA}; "
            "a whole source item cannot stand in for individually anchored clauses"
        )
    # A strict atom receipt is meaningful only relative to the current bytes
    # of the map's canonical source artifact.  This is separate from generic
    # source-anchor evidence because strict correspondence must not rely on a
    # paraphrase or a locator that merely happens to look source-like.
    file_bytes_override = (
        context.file_bytes_override() if context is not None else None
    )
    pin_findings = source_artifact_pin_findings(
        folder,
        status,
        map_path,
        payload,
        require_source_bytes=require_source_bytes,
        file_bytes_override=file_bytes_override,
    )
    findings.extend(pin_findings)
    canonical_source_is_current = not pin_findings
    if not isinstance(raw_items, dict):
        add("source-spec correspondence source map `items` must be an object")
        return findings

    validated_aliases = validated_presentation_alias_contract_exemptions(
        folder, payload
    )
    proof_obligation_items, _mode_error = _source_map_proof_obligation_items(
        folder, payload
    )
    strict_items: list[tuple[str, dict[str, Any]]] = []
    required_source_claim_keys: set[str] = set()
    for raw_key, raw_item in raw_items.items():
        if not isinstance(raw_item, dict):
            continue
        source_key = str(raw_key)
        inherited_contract_alias = source_key in validated_aliases
        if inherited_contract_alias:
            # A repeated source presentation is retained for provenance but
            # inherits the canonical claim's review and proof. It must not
            # create a second theorem-realization obligation or human-review
            # denominator row merely because the source repeats the theorem.
            if raw_item.get("claim_bearing") is not False:
                add(
                    f"items.{source_key}: v11 requires claim_bearing: false for a "
                    "repeated source presentation inheriting its canonical review"
                )
            if SOURCE_SPEC_CORRESPONDENCE_KEY in raw_item:
                add(
                    f"items.{source_key}: a presentation alias inheriting its canonical "
                    f"semantic_contract must not own {SOURCE_SPEC_CORRESPONDENCE_KEY}"
                )
            continue
        if source_key not in proof_obligation_items:
            if SOURCE_SPEC_CORRESPONDENCE_KEY in raw_item:
                add(
                    f"items.{source_key}: {SOURCE_SPEC_CORRESPONDENCE_KEY} is allowed only "
                    "on an item selected by the active semantic proof scope (or an "
                    "explicit corrected target)"
                )
            continue
        source_kind = str(raw_item.get("source_kind") or "").strip().lower()
        source_status = str(raw_item.get("source_status") or "").strip().lower()
        source_claim_is_in_scope = (
            source_kind in SOURCE_SPEC_CORRESPONDENCE_SOURCE_KINDS
            and source_status not in SOURCE_SPEC_CORRESPONDENCE_NONCLAIM_STATUSES
        )
        if source_claim_is_in_scope:
            required_source_claim_keys.add(source_key)
            if raw_item.get("claim_bearing") is not True:
                add(
                    f"items.{source_key}: v11 requires claim_bearing: true for every "
                    "in-scope named source claim; an inventory label cannot omit it from "
                    "the theorem-realization audit"
                )
            if not isinstance(raw_item.get("semantic_contract"), dict):
                add(
                    f"items.{source_key}: v11 requires an exact semantic_contract for "
                    "every in-scope named source claim"
                )
            else:
                strict_items.append((source_key, raw_item))
        elif raw_item.get("claim_bearing") is True and isinstance(
            raw_item.get("semantic_contract"), dict):
            strict_items.append((str(raw_key), raw_item))
        elif SOURCE_SPEC_CORRESPONDENCE_KEY in raw_item:
            add(
                f"items.{raw_key}: {SOURCE_SPEC_CORRESPONDENCE_KEY} is allowed only "
                "on a claim-bearing item with an exact semantic_contract"
            )
    if required_source_claim_keys and not strict_items:
        add(
            f"{SOURCE_SPEC_CORRESPONDENCE_SCHEMA_KEY} requires at least one "
            "claim-bearing exact semantic_contract; otherwise it cannot claim v11 realization coverage"
        )

    missing_basis_pins: dict[str, set[str]] = {}
    for source_key, raw_item in strict_items:
        raw_correspondence = raw_item.get(SOURCE_SPEC_CORRESPONDENCE_KEY)
        # Quote shape is required even when a claim is otherwise incomplete:
        # a missing correspondence record must not make its source clause
        # disappear from the strict source-byte obligation.
        strict_atom_errors = source_claim_atoms_validation_errors(
            raw_item.get(SOURCE_CLAIM_ATOMS_KEY), require_source_quote=True
        )
        if raw_correspondence is None:
            for error in strict_atom_errors:
                add(f"items.{source_key}: {error}")
        if canonical_source_is_current:
            for error in _source_claim_atoms_current_quote_binding_errors(
                folder,
                raw_item.get(SOURCE_CLAIM_ATOMS_KEY),
                source_artifact_path=payload.get("source_artifact_path"),
                source_artifact_sha256=payload.get("source_artifact_sha256"),
            ):
                add(f"items.{source_key}: {error}")
        if raw_correspondence is None:
            add(
                f"items.{source_key}: strict realization closeout requires "
                f"{SOURCE_SPEC_CORRESPONDENCE_KEY} for every claim-bearing semantic_contract"
            )
            continue
        errors = source_spec_correspondence_validation_errors(
            raw_correspondence,
            raw_atoms=raw_item.get(SOURCE_CLAIM_ATOMS_KEY),
            raw_contract=raw_item.get("semantic_contract"),
        )
        for error in errors:
            add(f"items.{source_key}: {error}")
        if not isinstance(raw_correspondence, dict):
            continue
        dispositions = raw_correspondence.get("closure_node_dispositions")
        if not isinstance(dispositions, list):
            continue
        for index, disposition in enumerate(dispositions):
            if not isinstance(disposition, dict) or "semantic_basis" not in disposition:
                continue
            basis_errors, missing_basis_pin = (
                _source_spec_semantic_basis_artifact_errors(
                    folder,
                    disposition.get("semantic_basis"),
                    require_source_bytes=require_source_bytes,
                )
            )
            for error in basis_errors:
                add(
                    f"items.{source_key}.closure_node_dispositions[{index}].{error}"
                )
            if missing_basis_pin is not None:
                basis_path, basis_digest = missing_basis_pin
                missing_basis_pins.setdefault(basis_path, set()).add(basis_digest)
    for basis_path, basis_digests in sorted(missing_basis_pins.items()):
        if len(basis_digests) != 1:
            add(
                "semantic_basis source artifact has conflicting absent-byte SHA-256 "
                f"pins: {basis_path}"
            )
            continue
        findings.append(
            Finding(
                "WARN",
                folder.name,
                rel(map_path),
                "semantic-basis source bytes are not provisioned in this structural "
                f"checkout: {basis_path}; the recorded SHA-256 is not release "
                "certification",
            )
        )
    return findings


def v11_raw_source_spec_screening_findings(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Require one current raw-source-to-transparent-Spec verdict per v11 claim.

    The atom-level realization receipt establishes which source atoms a proof
    endpoint realizes.  This independent screen establishes what an LLM or
    reviewer was actually shown while judging source/Spec meaning: the exact
    byte-pinned source bundle and the one transparent ``Spec`` declaration.
    It deliberately rejects a stale hash, a wrapper endpoint, a missing row,
    and an ``uncertain`` or ``mismatch`` verdict at a full closeout.  A source
    map paraphrase and theorem name never enter this comparison.
    """

    if status not in CLOSEOUT_STATUSES:
        return []
    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    source_map = transaction_json(map_path, context)
    if not isinstance(source_map, dict) or not raw_source_spec_screening_requested(
        status_payload, source_map, folder=folder
    ):
        return []

    severity = finding_severity(status)
    findings: list[Finding] = []

    def add(path: Path, message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(path), message))

    proof_items, scope_error = _source_map_proof_obligation_items(folder, source_map)
    if scope_error:
        add(map_path, "could not select v11 semantic-review scope: " + scope_error)
        return findings
    expected_records: dict[str, dict[str, Any]] = {}
    expected_keys_by_spec: dict[str, list[str]] = {}
    for raw_key, raw_item in proof_items.items():
        if not isinstance(raw_item, dict):
            continue
        contract = raw_item.get("semantic_contract")
        if not isinstance(contract, dict):
            continue
        spec = str(contract.get("spec_declaration") or "").strip()
        if spec:
            expected_keys_by_spec.setdefault(spec, []).append(str(raw_key))
            expected_records[spec] = raw_item
    if not expected_records:
        add(map_path, "v11 closeout selected no source-facing semantic Spec declarations")
        return findings
    for spec, source_keys in sorted(expected_keys_by_spec.items()):
        if len(source_keys) > 1:
            add(
                map_path,
                "v11 requires one semantic Spec per source claim, but "
                + ", ".join(source_keys)
                + f" all route to `{spec}`",
            )

    screening_path = folder / "audit" / "v11_raw_source_spec_screening.json"
    screening = load_json(screening_path)
    if not isinstance(screening, dict):
        add(screening_path, "missing or malformed v11 raw-source-to-expanded-Spec screening")
        return findings
    if screening.get("schema") != 2 or screening.get("paper") != folder.name:
        add(screening_path, "v11 screening has an unsupported schema or paper identity")
        return findings
    if (
        str(screening.get("prompt_version") or "").strip()
        != "statement-match-v11-verbatim-source-anchor-lean-expanded-spec-v2"
    ):
        add(screening_path, "v11 screening does not declare the required raw-source prompt version")
    if not str(screening.get("validator") or "").strip() or not str(
        screening.get("validated_at") or ""
    ).strip():
        add(screening_path, "v11 screening lacks reviewer and validation-time metadata")
    raw_rows = screening.get("items")
    if not isinstance(raw_rows, dict):
        add(screening_path, "v11 screening has no item ledger")
        return findings

    dashboard = _source_scope_dashboard_module()
    interface_path = folder / "PaperInterface.lean"
    interface_items: dict[str, tuple[str, str]] = {}
    try:
        declarations = dashboard.parse_review_source_declarations(interface_path)
    except (OSError, ValueError) as exc:
        add(interface_path, "could not read PaperInterface Specs for v11 screening: " + str(exc))
        return findings
    for kind, short_name, full_name, source, _comment, _line, _path in declarations:
        if short_name.endswith("Spec"):
            interface_items[str(full_name)] = (str(kind), str(source))
    cached_prerequisite_targets: Mapping[str, Any] | None = None
    cached_library_targets: Mapping[str, Any] | None = None
    cached_library_target_errors: Mapping[str, Any] | None = None
    try:
        try:
            from scripts import review_dashboard_packet
        except ModuleNotFoundError:
            import review_dashboard_packet  # type: ignore[no-redef]
        # The packet cache is a Lean-produced display cache, accepted here
        # only when it binds the exact current paper-local Lean tree and the
        # complete selected Spec set.  This validator still replays every
        # source bundle, PaperInterface declaration, screening hash, and
        # semantic prerequisite/library ledger below.  The separate
        # source-to-Spec receipt and repository audit validate the proof and
        # dependency closure; do not launch a second identical display pass
        # merely to render-check already-bound target text.
        packet_cache = review_dashboard_packet._current_packet_lean_cache(
            folder, expected_records
        )
        cached_targets = (
            packet_cache.get("semantic_targets")
            if isinstance(packet_cache, Mapping)
            else None
        )
        cached_prerequisite_targets = (
            packet_cache.get("paper_prerequisite_targets")
            if isinstance(packet_cache, Mapping)
            else None
        )
        cached_library_targets = (
            packet_cache.get("library_semantic_targets")
            if isinstance(packet_cache, Mapping)
            else None
        )
        cached_library_target_errors = (
            packet_cache.get("library_semantic_target_errors")
            if isinstance(packet_cache, Mapping)
            else None
        )
        if (
            isinstance(cached_targets, Mapping)
            and set(expected_records).issubset(cached_targets)
        ):
            semantic_targets = {
                spec: dict(cached_targets[spec])
                for spec in expected_records
                if isinstance(cached_targets[spec], Mapping)
            }
            if set(semantic_targets) != set(expected_records):
                raise ValueError("packet Lean-cache has a malformed semantic target")
        else:
            semantic_targets = review_dashboard_packet.semantic_expanded_spec_targets(
                folder, expected_records
            )
    except (OSError, ValueError) as exc:
        add(
            interface_path,
            "could not obtain Lean-expanded v11 semantic targets: " + str(exc),
        )
        return findings
    paper_prerequisites = review_dashboard_packet.paper_semantic_prerequisites(
        folder,
        semantic_targets,
        semantic_targets_by_name_override=(
            cached_prerequisite_targets
            if isinstance(cached_prerequisite_targets, Mapping)
            else None
        ),
    )
    for prerequisite in paper_prerequisites:
        name = str(prerequisite.get("lean_name") or "").strip()
        if not str(prerequisite.get("paper_declaration_source") or "").strip():
            add(
                interface_path,
                f"{name}: Lean retained a paper-local semantic prerequisite without exact declaration source",
            )
            continue
        if not str(prerequisite.get("paper_semantic_target") or "").strip():
            add(
                interface_path,
                f"{name}: Lean retained a paper-local semantic prerequisite without a semantic target",
            )
            continue
        if prerequisite.get("semantic_current") is not True:
            add(
                folder / "audit" / "paper_semantic_prerequisites.json",
                f"{name}: paper-local semantic prerequisite has no current raw-source review",
            )
        elif str(prerequisite.get("semantic_judgment") or "").strip().lower() != "matches":
            add(
                folder / "audit" / "paper_semantic_prerequisites.json",
                f"{name}: paper-local semantic prerequisite judgment is not `matches`",
            )
    semantic_library_claims = [
        {
            "library_review_owner_declarations": list(
                target.get("library_declarations", ())
            )
        }
        for target in semantic_targets.values()
    ]
    semantic_library_claims.extend(
        {
            "library_review_owner_declarations": list(
                prerequisite.get("direct_library_declarations", ())
            )
        }
        for prerequisite in paper_prerequisites
    )
    for prerequisite in dashboard.human_review_library_prerequisites(
        folder,
        semantic_library_claims,
        semantic_targets_override=(
            cached_library_targets
            if isinstance(cached_library_targets, Mapping)
            else None
        ),
        semantic_target_errors_override=(
            cached_library_target_errors
            if isinstance(cached_library_target_errors, Mapping)
            else None
        ),
    ):
        name = str(prerequisite.get("lean_name") or "").strip()
        if prerequisite.get("semantic_current") is not True:
            add(
                folder / "audit" / "library_semantic_review.json",
                f"{name}: Lean-expanded semantic target has no current raw-source library review",
            )
        elif str(prerequisite.get("semantic_judgment") or "").strip().lower() != "matches":
            add(
                folder / "audit" / "library_semantic_review.json",
                f"{name}: Lean-expanded semantic target library judgment is not `matches`",
            )

    missing_rows = sorted(set(expected_records) - set(raw_rows))
    extra_rows = sorted(set(raw_rows) - set(expected_records))
    if missing_rows:
        add(
            screening_path,
            "v11 screening lacks "
            + str(len(missing_rows))
            + " selected source/Spec row(s): "
            + ", ".join(missing_rows[:4])
            + ("; ..." if len(missing_rows) > 4 else ""),
        )
    if extra_rows:
        add(
            screening_path,
            "v11 screening contains "
            + str(len(extra_rows))
            + " row(s) outside the current selected source/Spec scope: "
            + ", ".join(extra_rows[:4])
            + ("; ..." if len(extra_rows) > 4 else ""),
        )
    for spec, record in expected_records.items():
        row = raw_rows.get(spec)
        interface_item = interface_items.get(spec)
        semantic_target = semantic_targets.get(spec)
        if interface_item is None:
            add(interface_path, f"{spec}: v11 semantic target is absent from PaperInterface.lean")
            continue
        if semantic_target is None:
            add(interface_path, f"{spec}: Lean produced no complete v11 semantic target")
            continue
        kind, lean_text = interface_item
        if kind != "def" or not re.search(r":\s*Prop\s*:=", lean_text, flags=re.DOTALL):
            add(
                interface_path,
                f"{spec}: v11 semantic target must be one explicit `def ...Spec : Prop :=` declaration, not a wrapper or proof endpoint",
            )
        if not isinstance(row, dict):
            continue
        source_error = dashboard.source_anchor_file_error(folder, record)
        if not source_error:
            source_text, source_digest, source_error = dashboard.source_semantic_input_bundle(
                record, require_context_roles=True
            )
        else:
            source_text, source_digest = "", ""
        if source_error or not source_text or not source_digest:
            add(map_path, f"{spec}: current raw source bundle is invalid: {source_error}")
            continue
        expected_lean_digest = str(
            semantic_target.get("display_sha256") or ""
        ).strip().lower()
        expected_interface_digest = str(
            semantic_target.get("paper_interface_sha256") or ""
        ).strip().lower()
        if str(row.get("source_input_protocol") or "").strip() != "verbatim_source_anchor_bundle_v1":
            add(screening_path, f"{spec}: v11 row lacks the verbatim source-input protocol")
        if str(row.get("lean_target_protocol") or "").strip() != "lean_transparent_paper_expansion_v1":
            add(screening_path, f"{spec}: v11 row lacks the expanded-Spec target protocol")
        if str(row.get("semantic_target_declaration") or "").strip() != spec:
            add(screening_path, f"{spec}: v11 row targets a different declaration")
        if str(row.get("source_input_bundle_sha256") or "").strip().lower() != source_digest:
            add(screening_path, f"{spec}: v11 row is stale for the current exact source bundle")
        if str(row.get("paper_statement_sha256") or "").strip().lower() != source_digest:
            add(screening_path, f"{spec}: v11 row does not bind its source-side semantic target")
        if str(row.get("lean_expanded_statement_sha256") or "").strip().lower() != expected_lean_digest:
            add(screening_path, f"{spec}: v11 row is stale for Lean's current expanded semantic target")
        if str(row.get("paper_interface_sha256") or "").strip().lower() != expected_interface_digest:
            add(screening_path, f"{spec}: v11 row is stale for the current PaperInterface source")
        verdict = str(row.get("judgment") or "").strip().lower()
        approved_corrected_target = verdict == APPROVED_CORRECTED_TARGET_MATCH
        is_corrected_source_statement = (
            str(record.get("coverage_status") or "").strip()
            == CORRECTED_SOURCE_STATEMENT_STATUS
        )
        if approved_corrected_target:
            corrected_target = record.get("corrected_target")
            if (
                not is_corrected_source_statement
                or not isinstance(corrected_target, dict)
                or corrected_target.get("archival_equivalence_claimed") is not False
            ):
                add(
                    screening_path,
                    f"{spec}: approved-corrected-target judgment lacks a corrected-source map record",
                )
            elif (
                str(row.get("corrected_target_protocol") or "").strip()
                != "approved_corrected_target_v1"
            ):
                add(
                    screening_path,
                    f"{spec}: approved-corrected-target judgment lacks its correction protocol",
                )
            elif str(row.get("corrected_target_sha256") or "").strip().lower() != str(
                corrected_target.get("corrected_target_sha256") or ""
            ).strip().lower():
                add(
                    screening_path,
                    f"{spec}: approved-corrected-target judgment is stale for the corrected target record",
                )
        elif is_corrected_source_statement:
            # A corrected-source map entry retains the archival proposition;
            # an ordinary `matches` record would falsely certify that archival
            # text against the different approved target.  The narrow
            # correction disposition additionally binds the target and its
            # approval record.
            add(
                screening_path,
                f"{spec}: corrected_source_statement requires `"
                f"{APPROVED_CORRECTED_TARGET_MATCH}`, not `{verdict or 'missing'}`",
            )
        elif verdict != "matches":
            add(
                screening_path,
                f"{spec}: raw source-to-expanded-Spec judgment is `{verdict or 'missing'}`, not `matches`",
            )
        if not str(row.get("reason") or "").strip():
            add(screening_path, f"{spec}: v11 row has no reviewer explanation")
    return findings


def material_library_semantic_review_findings(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Require current raw-source review for every material library primitive.

    The review dashboard owns the bounded library-declaration registry and
    exact source-bundle reconstruction.  This integrity gate makes its result
    a closeout requirement for the v11 source-Spec lane: a reusable library
    name cannot be a silent semantic shortcut merely because it renders in a
    packet.  The check is deliberately limited to papers that explicitly opt
    into source-Spec correspondence, so existing legacy papers are not
    retroactively relabelled as having passed this newer lane.
    """

    if status not in CLOSEOUT_STATUSES:
        return []
    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    source_map = transaction_json(map_path, context)
    if not isinstance(source_map, dict) or not raw_source_spec_screening_requested(
        status_payload, source_map, folder=folder
    ):
        return []
    proof_items, scope_error = _source_map_proof_obligation_items(folder, source_map)
    if scope_error:
        return [
            Finding(
                finding_severity(status),
                folder.name,
                rel(map_path),
                "could not select material-library semantic-review scope: " + scope_error,
            )
        ]
    expected_specs = {
        str(contract.get("spec_declaration") or "").strip()
        for item in proof_items.values()
        if isinstance(item, dict)
        for contract in [item.get("semantic_contract")]
        if isinstance(contract, dict)
        and str(contract.get("spec_declaration") or "").strip()
    }
    if not expected_specs:
        return []
    dashboard = _source_scope_dashboard_module()
    ledger_path = folder / "audit" / "library_semantic_review.json"
    ledger_payload = transaction_json(ledger_path, context)
    if not isinstance(ledger_payload, dict):
        return [
            Finding(
                finding_severity(status),
                folder.name,
                rel(ledger_path),
                "missing or malformed material library semantic-review ledger",
            )
        ]
    try:
        declarations = dashboard.parse_review_source_declarations(
            folder / "PaperInterface.lean"
        )
    except (OSError, ValueError) as exc:
        return [
            Finding(
                finding_severity(status),
                folder.name,
                rel(folder / "PaperInterface.lean"),
                "could not read PaperInterface for material-library semantic review: "
                + str(exc),
            )
        ]
    interface_by_spec = {
        str(full_name): str(source)
        for _kind, _short_name, full_name, source, _comment, _line, _path in declarations
        if str(full_name) in expected_specs
    }
    try:
        cached_library_targets: Mapping[str, Any] | None = None
        cached_library_target_errors: Mapping[str, Any] | None = None
        cached_prerequisite_targets: Mapping[str, Any] | None = None
        try:
            from scripts import review_dashboard_packet
        except ModuleNotFoundError:
            import review_dashboard_packet  # type: ignore[no-redef]
        # See the corresponding v11 source-Spec screen above.  Reuse only a
        # complete cache bound to the current paper Lean tree; all ledger and
        # source pins below remain live validation inputs.
        packet_cache = review_dashboard_packet._current_packet_lean_cache(
            folder, expected_specs
        )
        cached_targets = (
            packet_cache.get("semantic_targets")
            if isinstance(packet_cache, Mapping)
            else None
        )
        cached_prerequisite_targets = (
            packet_cache.get("paper_prerequisite_targets")
            if isinstance(packet_cache, Mapping)
            else None
        )
        cached_library_targets = (
            packet_cache.get("library_semantic_targets")
            if isinstance(packet_cache, Mapping)
            else None
        )
        cached_library_target_errors = (
            packet_cache.get("library_semantic_target_errors")
            if isinstance(packet_cache, Mapping)
            else None
        )
        if isinstance(cached_targets, Mapping) and expected_specs.issubset(cached_targets):
            expanded_targets = {
                spec: dict(cached_targets[spec])
                for spec in expected_specs
                if isinstance(cached_targets[spec], Mapping)
            }
            if set(expanded_targets) != expected_specs:
                raise ValueError("packet Lean-cache has a malformed semantic target")
        else:
            expanded_targets = review_dashboard_packet.semantic_expanded_spec_targets(
                folder, sorted(expected_specs)
            )
    except ValueError as exc:
        expanded_targets = {}
        surface_errors: list[str] = [
            "could not obtain current Lean-expanded Spec library surface: " + str(exc)
        ]
    else:
        surface_errors = []
    if set(expanded_targets) != expected_specs:
        surface_errors.append(
            "Lean-expanded Spec library surface does not cover the selected Spec scope"
        )
    direct_surface = ledger_payload.get("direct_spec_dependency_surface")
    direct_owners: set[str] = set()
    if not isinstance(direct_surface, dict):
        surface_errors.append("ledger has no Lean-resolved direct-library dependency surface")
    else:
        if direct_surface.get("schema") != 1:
            surface_errors.append("direct-library dependency surface has unsupported schema")
        if (
            str(direct_surface.get("protocol") or "").strip()
            != "lean-expanded-paper-spec-library-surface-v1"
        ):
            surface_errors.append("direct-library dependency surface has unsupported protocol")
        try:
            current_interface_sha256 = hashlib.sha256(
                (folder / "PaperInterface.lean").read_bytes()
            ).hexdigest()
        except OSError as exc:
            surface_errors.append("could not read current PaperInterface: " + str(exc))
            current_interface_sha256 = ""
        if (
            str(direct_surface.get("paper_interface_sha256") or "").strip().lower()
            != current_interface_sha256
        ):
            surface_errors.append(
                "direct-library dependency surface is stale for the current PaperInterface bytes"
            )
        raw_items = direct_surface.get("items")
        if not isinstance(raw_items, dict):
            surface_errors.append("direct-library dependency surface has no item ledger")
        else:
            missing = sorted(expected_specs - set(raw_items))
            extra = sorted(set(raw_items) - expected_specs)
            if missing or extra:
                detail: list[str] = []
                if missing:
                    detail.append("missing " + ", ".join(missing[:3]))
                if extra:
                    detail.append("extra " + ", ".join(extra[:3]))
                surface_errors.append(
                    "direct-library dependency surface does not match the selected Spec scope ("
                    + "; ".join(detail)
                    + ")"
                )
            for spec in sorted(expected_specs & set(raw_items)):
                raw = raw_items.get(spec)
                if not isinstance(raw, dict) or set(raw) != {
                    "spec_source_sha256",
                    "semantic_target_sha256",
                    "direct_library_declarations",
                    "review_owner_declarations",
                }:
                    surface_errors.append(f"{spec}: malformed direct-library dependency item")
                    continue
                if (
                    str(raw.get("spec_source_sha256") or "").strip().lower()
                    != dashboard.statement_digest(interface_by_spec.get(spec, ""))
                ):
                    surface_errors.append(
                        f"{spec}: direct-library dependency item is stale for the current Spec"
                    )
                if (
                    str(raw.get("semantic_target_sha256") or "").strip().lower()
                    != str(expanded_targets.get(spec, {}).get("display_sha256") or "").strip().lower()
                ):
                    surface_errors.append(
                        f"{spec}: direct-library dependency item is stale for Lean's current expanded target"
                    )
                dependencies = raw.get("direct_library_declarations")
                owners = raw.get("review_owner_declarations")
                if (
                    not isinstance(dependencies, list)
                    or any(
                        not isinstance(name, str) or not name.startswith("EconCSLib.")
                        for name in dependencies
                    )
                    or dependencies != sorted(set(dependencies))
                ):
                    surface_errors.append(f"{spec}: malformed direct reusable-library declarations")
                    continue
                expected_dependencies = list(
                    expanded_targets.get(spec, {}).get("library_declarations", ())
                )
                if dependencies != expected_dependencies:
                    surface_errors.append(
                        f"{spec}: direct reusable-library declarations do not match the expanded target"
                    )
                expected_owners = sorted(
                    {
                        dashboard.library_review_owner_declaration(name)
                        for name in dependencies
                    }
                )
                if (
                    not isinstance(owners, list)
                    or owners != expected_owners
                    or any(
                        not isinstance(name, str) or not name.startswith("EconCSLib.")
                        for name in owners
                    )
                ):
                    surface_errors.append(
                        f"{spec}: direct reusable-library review owners are incomplete or malformed"
                    )
                    continue
                direct_owners.update(owners)
    findings: list[Finding] = [
        Finding(finding_severity(status), folder.name, rel(ledger_path), error)
        for error in surface_errors
    ]
    try:
        paper_prerequisites = review_dashboard_packet.paper_semantic_prerequisites(
            folder,
            expanded_targets,
            semantic_targets_by_name_override=(
                cached_prerequisite_targets
                if isinstance(cached_prerequisite_targets, Mapping)
                else None
            ),
        )
    except ValueError as exc:
        paper_prerequisites = []
        findings.append(
            Finding(
                finding_severity(status),
                folder.name,
                rel(folder / "PaperInterface.lean"),
                "could not obtain paper-prerequisite library surface: " + str(exc),
            )
        )
    prerequisite_owners = sorted(
        {
            dashboard.library_review_owner_declaration(declaration)
            for prerequisite in paper_prerequisites
            for declaration in prerequisite.get("direct_library_declarations", ())
            if str(declaration).strip().startswith("EconCSLib.")
        }
    )
    claims = [
        {
            "interface_source": str(source),
            "lean_statement": str(source),
            "library_review_owner_declarations": sorted(direct_owners),
        }
        for _kind, _short_name, full_name, source, _comment, _line, _path in declarations
        if str(full_name) in expected_specs
    ]
    if prerequisite_owners:
        claims.append({"library_review_owner_declarations": prerequisite_owners})
    entries = dashboard.human_review_library_prerequisites(
        folder,
        claims,
        semantic_targets_override=(
            cached_library_targets
            if isinstance(cached_library_targets, Mapping)
            else None
        ),
        semantic_target_errors_override=(
            cached_library_target_errors
            if isinstance(cached_library_target_errors, Mapping)
            else None
        ),
    )
    for entry in entries:
        name = str(entry.get("lean_name") or "library declaration").strip()
        current = bool(entry.get("semantic_current"))
        judgment = str(entry.get("semantic_judgment") or "not recorded").strip()
        if current and judgment == "matches":
            continue
        detail = str(entry.get("semantic_status") or "incomplete").strip()
        if current and judgment in {"mismatch", "uncertain"}:
            detail = "current source-to-library judgment is `" + judgment + "`"
        findings.append(
            Finding(
                finding_severity(status),
                folder.name,
                rel(folder / "audit" / "library_semantic_review.json"),
                f"{name}: material library semantic review is not a current `matches` verdict ({detail})",
            )
        )
    return findings


def semantic_contract_validation_errors(
    raw_contract: object,
    *,
    schema: int = SEMANTIC_CONTRACT_SCHEMA,
) -> list[str]:
    """Validate an opt-in source-map contract without trusting Lean names.

    Schema 2 deliberately adds only one specialized source-model shape.  Its
    three clauses are source text, not Lean navigation: a selector law, the
    conditional outcome law, and their composed objective/expectation must
    each carry an independently byte-verifiable source anchor.  The actual
    Lean bridge is generated later from the exact explicit contract route.
    """

    if not isinstance(raw_contract, dict):
        return ["semantic_contract must be an object"]
    errors: list[str] = []
    if not schema_version_is_supported(schema, SEMANTIC_CONTRACT_SCHEMAS):
        return [
            "semantic_contract schema must be one of: "
            + ", ".join(str(value) for value in sorted(SEMANTIC_CONTRACT_SCHEMAS))
        ]

    for field in ("spec_declaration", "evidence_declaration"):
        if not isinstance(raw_contract.get(field), str) or not str(
            raw_contract.get(field) or ""
        ).strip():
            errors.append(f"semantic_contract.{field} must be a nonempty string")
    mode = str(raw_contract.get("evidence_mode") or "").strip()
    if mode not in SEMANTIC_CONTRACT_EVIDENCE_MODES:
        errors.append(
            "semantic_contract.evidence_mode must be one of: "
            + ", ".join(sorted(SEMANTIC_CONTRACT_EVIDENCE_MODES))
        )
    shape = str(raw_contract.get("semantic_shape") or "").strip()
    allowed_shapes = (
        SEMANTIC_CONTRACT_SHAPES
        if schema_version_is_exact(schema, SEMANTIC_CONTRACT_SCHEMA)
        else SEMANTIC_CONTRACT_SCHEMA_2_SHAPES
    )
    if shape not in allowed_shapes:
        if schema_version_is_exact(schema, SEMANTIC_CONTRACT_SCHEMA):
            errors.append(
                "semantic_contract.semantic_shape must be `plain` in schema 1; "
                "specialized runtime, initial-transform, and refinement shapes are "
                "unsupported until they have role-bearing Lean Meta checks"
            )
        else:
            errors.append(
                "semantic_contract.semantic_shape must be one of: "
                + ", ".join(sorted(allowed_shapes))
            )

    allowed_fields = {
        "spec_declaration",
        "evidence_declaration",
        "evidence_mode",
        "semantic_shape",
    }
    if shape == CONDITIONAL_PROBABILITY_COMPOSITION_SEMANTIC_SHAPE:
        allowed_fields.add(CONDITIONAL_PROBABILITY_COMPOSITION_FIELD)
    unknown_fields = sorted(set(raw_contract) - allowed_fields)
    if unknown_fields:
        errors.append(
            "semantic_contract has unsupported field(s): "
            + ", ".join(unknown_fields)
        )

    composition = raw_contract.get(CONDITIONAL_PROBABILITY_COMPOSITION_FIELD)
    if shape != CONDITIONAL_PROBABILITY_COMPOSITION_SEMANTIC_SHAPE:
        if composition is not None:
            errors.append(
                "semantic_contract.conditional_probability_composition is allowed only "
                "with semantic_shape `conditional_probability_composition`"
            )
        return errors

    if not schema_version_is_exact(schema, SEMANTIC_CONTRACT_SCHEMA_2):
        errors.append(
            "semantic_contract semantic_shape `conditional_probability_composition` "
            "requires semantic_contract_schema 2"
        )
        return errors
    if not isinstance(composition, dict):
        errors.append(
            "semantic_contract.conditional_probability_composition must be an object"
        )
        return errors
    unexpected_composition_fields = sorted(
        set(composition) - set(CONDITIONAL_PROBABILITY_COMPOSITION_CLAUSES)
    )
    if unexpected_composition_fields:
        errors.append(
            "semantic_contract.conditional_probability_composition has unsupported "
            "field(s): "
            + ", ".join(unexpected_composition_fields)
        )
    for clause in CONDITIONAL_PROBABILITY_COMPOSITION_CLAUSES:
        prefix = f"semantic_contract.conditional_probability_composition.{clause}"
        raw_clause = composition.get(clause)
        if not isinstance(raw_clause, dict):
            errors.append(f"{prefix} must be an object")
            continue
        unexpected_clause_fields = sorted(
            set(raw_clause) - CONDITIONAL_PROBABILITY_COMPOSITION_CLAUSE_FIELDS
        )
        if unexpected_clause_fields:
            errors.append(
                f"{prefix} has unsupported field(s): "
                + ", ".join(unexpected_clause_fields)
            )
        location = raw_clause.get("source_location")
        if not isinstance(location, str) or not location.strip():
            errors.append(f"{prefix}.source_location must be a nonempty string")
        elif not list(SOURCE_FILE_LINE_RE.finditer(location)):
            errors.append(
                f"{prefix}.source_location must include one or more file:line anchors "
                "into the canonical pinned source artifact"
            )
        statement = raw_clause.get("semantic_statement")
        if not isinstance(statement, str) or not statement.strip():
            errors.append(f"{prefix}.semantic_statement must be a nonempty source semantic statement")
        anchors = raw_clause.get("source_anchor_evidence")
        if not isinstance(anchors, list) or not anchors:
            errors.append(
                f"{prefix}.source_anchor_evidence must be a nonempty byte-pinned "
                "source-anchor list"
            )
    return errors


def conditional_probability_composition_anchor_findings(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
    scoped_items: dict[str, dict[str, Any]],
    *,
    require_source_bytes: bool = True,
) -> list[Finding]:
    """Byte-validate schema-2 composition clauses even without global anchors.

    The three source clauses are not ordinary source-map items and must not
    disappear merely because a paper leaves global anchor validation disabled.
    A synthetic map lets the existing exact byte validator own path, range,
    quote, and canonical-artifact checks without using source keys or Lean
    declaration names as mathematical evidence.
    """

    composition_items: dict[str, dict[str, Any]] = {}
    for source_key, raw_item in scoped_items.items():
        if not isinstance(raw_item, dict):
            continue
        contract = raw_item.get("semantic_contract")
        if not isinstance(contract, dict) or str(
            contract.get("semantic_shape") or ""
        ).strip() != CONDITIONAL_PROBABILITY_COMPOSITION_SEMANTIC_SHAPE:
            continue
        composition_items[str(source_key)] = {
            CONDITIONAL_PROBABILITY_COMPOSITION_FIELD: contract.get(
                CONDITIONAL_PROBABILITY_COMPOSITION_FIELD
            )
        }
    if not composition_items:
        return []
    isolated_payload = {
        "source_artifact_path": payload.get("source_artifact_path"),
        "source_artifact_sha256": payload.get("source_artifact_sha256"),
        SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY: True,
        "items": composition_items,
    }
    return source_anchor_evidence_findings(
        folder,
        status,
        manifest_path,
        isolated_payload,
        require_source_bytes=require_source_bytes,
    )


def _nonempty_qualified_declaration(value: object) -> str | None:
    """Return a syntactically qualified declaration identity, if present.

    This deliberately validates only the explicit metadata shape. It does not
    use declaration spellings to infer a source claim; the equality checks in
    ``source_core_projection_validation_errors`` bind this identity to the
    item's already-declared semantic contract.
    """

    if not isinstance(value, str):
        return None
    declaration = value.strip()
    parts = declaration.split(".")
    if len(parts) < 2 or any(not part for part in parts):
        return None
    return declaration


def _nonempty_string(value: object) -> str | None:
    if not isinstance(value, str):
        return None
    text = value.strip()
    return text or None


def _string_list_or_none(value: object) -> list[str] | None:
    if not isinstance(value, list):
        return None
    values = [_nonempty_string(entry) for entry in value]
    if any(entry is None for entry in values):
        return None
    return [entry for entry in values if entry is not None]


def source_core_projection_validation_errors(raw_item: object) -> list[str]:
    """Validate an optional literal-source-core/checked-strengthening split.

    A source-core split is opt-in map metadata. When present, the primary
    paper-facing declaration must be exactly the direct member of the item's
    semantic contract. Checked stronger results remain visible support, but
    cannot replace or be credited as literal source coverage. All checks below
    are explicit structural associations; no result is classified from a Lean
    declaration, function, map-key, or suffix spelling.
    """

    if not isinstance(raw_item, dict):
        return []
    raw_projection = raw_item.get("source_core_projection")
    if raw_projection is None:
        return []
    if not isinstance(raw_projection, dict):
        return ["source_core_projection must be an object"]

    errors: list[str] = []
    if raw_projection.get("classification") != SOURCE_CORE_PROJECTION_CLASSIFICATION:
        errors.append(
            "source_core_projection.classification must be "
            f"`{SOURCE_CORE_PROJECTION_CLASSIFICATION}`"
        )
    if _nonempty_string(raw_projection.get("description")) is None:
        errors.append("source_core_projection.description must be a nonempty string")

    core_direct = _nonempty_qualified_declaration(
        raw_projection.get("direct_declaration")
    )
    if core_direct is None:
        errors.append(
            "source_core_projection.direct_declaration must be a nonempty fully-qualified declaration"
        )
    core_spec = _nonempty_qualified_declaration(raw_projection.get("spec_declaration"))
    if core_spec is None:
        errors.append(
            "source_core_projection.spec_declaration must be a nonempty fully-qualified declaration"
        )

    raw_contract = raw_item.get("semantic_contract")
    if not isinstance(raw_contract, dict):
        errors.append(
            "source_core_projection requires an item semantic_contract object for exact direct/spec binding"
        )
    else:
        contract_direct = _nonempty_string(raw_contract.get("evidence_declaration"))
        contract_spec = _nonempty_string(raw_contract.get("spec_declaration"))
        if core_direct is not None and core_direct != contract_direct:
            errors.append(
                "source_core_projection.direct_declaration must equal "
                "semantic_contract.evidence_declaration"
            )
        if core_spec is not None and core_spec != contract_spec:
            errors.append(
                "source_core_projection.spec_declaration must equal "
                "semantic_contract.spec_declaration"
            )

    primary_declarations = _string_list_or_none(raw_item.get("lean_declarations"))
    if core_direct is not None:
        core_short_name = core_direct.rsplit(".", maxsplit=1)[-1]
        if primary_declarations != [core_short_name]:
            errors.append(
                "source_core_projection direct declaration's unqualified name must be "
                "the sole lean_declarations entry"
            )
    elif primary_declarations is None:
        errors.append("lean_declarations must be a list of nonempty strings")

    support_declarations = _string_list_or_none(
        raw_item.get("support_lean_declarations")
    )
    if support_declarations is None:
        errors.append("support_lean_declarations must be a list of nonempty strings")
        support_declarations = []
    if primary_declarations is None:
        primary_declarations = []

    raw_strengthenings = raw_item.get("checked_strengthening_declarations")
    if not isinstance(raw_strengthenings, list) or not raw_strengthenings:
        errors.append(
            "checked_strengthening_declarations must be a nonempty list of objects"
        )
        return errors

    core_identities = {identity for identity in (core_direct, core_spec) if identity}
    for index, raw_strengthening in enumerate(raw_strengthenings):
        prefix = f"checked_strengthening_declarations[{index}]"
        if not isinstance(raw_strengthening, dict):
            errors.append(f"{prefix} must be an object")
            continue
        if (
            raw_strengthening.get("classification")
            != CHECKED_STRENGTHENING_CLASSIFICATION
        ):
            errors.append(
                f"{prefix}.classification must be "
                f"`{CHECKED_STRENGTHENING_CLASSIFICATION}`"
            )
        strengthening_declaration = _nonempty_qualified_declaration(
            raw_strengthening.get("declaration")
        )
        if strengthening_declaration is None:
            errors.append(
                f"{prefix}.declaration must be a nonempty fully-qualified declaration"
            )
        strengthening_spec = _nonempty_qualified_declaration(
            raw_strengthening.get("spec_declaration")
        )
        if strengthening_spec is None:
            errors.append(
                f"{prefix}.spec_declaration must be a nonempty fully-qualified declaration"
            )
        if _nonempty_string(raw_strengthening.get("description")) is None:
            errors.append(f"{prefix}.description must be a nonempty string")
        if strengthening_declaration in core_identities:
            errors.append(
                f"{prefix}.declaration must differ from both source-core direct/spec declarations"
            )
        if strengthening_spec in core_identities:
            errors.append(
                f"{prefix}.spec_declaration must differ from both source-core direct/spec declarations"
            )
        if strengthening_declaration is None:
            continue
        strengthening_short_name = strengthening_declaration.rsplit(".", maxsplit=1)[-1]
        if strengthening_short_name not in support_declarations:
            errors.append(
                f"{prefix}.declaration short name must occur in support_lean_declarations"
            )
        if strengthening_short_name in primary_declarations:
            errors.append(
                f"{prefix}.declaration short name must not occur in lean_declarations"
            )
    return errors


def _source_scope_dashboard_module() -> Any:
    """Load the dashboard's source-only scope classifier without a cycle.

    The dashboard does not import this integrity gate.  Keeping this import
    local also preserves direct ``python scripts/...`` execution, where either
    ``scripts.review_dashboard`` or ``review_dashboard`` is importable
    depending on ``sys.path``.
    """

    try:
        from scripts import review_dashboard
    except ModuleNotFoundError:
        import review_dashboard  # type: ignore[no-redef]

    return review_dashboard


def _semantic_contract_scope_item_context(
    payload: dict[str, Any], raw_item: dict[str, Any]
) -> dict[str, Any]:
    """Attach canonical source-pin context needed by the source classifier.

    Statement-map rows inherit the canonical artifact pin from the map.  The
    dashboard validator expects that context directly on an item, so preserve
    any row-level pin (to detect a mismatch) and supply the canonical values as
    a comparison target.  No Lean or map-key data participates.
    """

    item = dict(raw_item)
    canonical_path = payload.get("source_artifact_path")
    canonical_digest = payload.get("source_artifact_sha256")
    if "source_artifact_path" not in item:
        item["source_artifact_path"] = canonical_path
    if "source_artifact_sha256" not in item:
        item["source_artifact_sha256"] = canonical_digest
    item["canonical_source_artifact_path"] = canonical_path
    item["canonical_source_artifact_sha256"] = canonical_digest
    return item


def _semantic_contract_item_requires_proof_evidence(
    payload: dict[str, Any], source_key: str, raw_item: dict[str, Any]
) -> bool:
    """Reuse the canonical source-kind proof/translation boundary.

    A named definition or predicate remains claim-bearing for inventory and
    statement fidelity, but it is reviewed through the translation lane rather
    than by inventing a theorem-shaped Spec/proof contract.  Result-bearing or
    ambiguous source presentations still require proof evidence.  Import or
    classifier failures therefore return ``True``.
    """

    try:
        dashboard = _source_scope_dashboard_module()
        decision = dashboard._source_inventory_item_requires_proof_evidence(
            source_key,
            _semantic_contract_scope_item_context(payload, raw_item),
        )
    except (AttributeError, ModuleNotFoundError, TypeError, ValueError):
        return True
    return decision if isinstance(decision, bool) else True


def _semantic_contract_item_anchor_errors(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
    raw_item: dict[str, Any],
    *,
    require_source_bytes: bool = True,
) -> list[str]:
    """Return exact-source-slice errors for one scope-exception candidate.

    This invokes the same byte-pinned source-anchor validator used by the
    manifest gate, rather than treating the map's quoted text as trusted.  The
    synthetic one-item map is structural plumbing only; eligibility is decided
    solely by the item's source fields and exact source quote.
    """

    isolated_payload = {
        "source_artifact_path": payload.get("source_artifact_path"),
        "source_artifact_sha256": payload.get("source_artifact_sha256"),
        SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY: True,
        "items": {"scope_exception": raw_item},
    }
    errors: list[str] = []
    if not require_source_bytes:
        locator = raw_item.get("source_location")
        errors.extend(
            source_file_line_anchor_errors(
                folder, locator, require_source_bytes=False
            )
        )
        errors.extend(
            canonical_artifact_source_span_errors(
                folder,
                locator,
                source_artifact_path=payload.get("source_artifact_path"),
            )
        )
    for finding in source_anchor_evidence_findings(
        folder,
        status,
        manifest_path,
        isolated_payload,
        require_source_bytes=require_source_bytes,
    ):
        if (
            not require_source_bytes
            and finding.severity == "WARN"
            and finding.message.startswith(
                "source bytes are not provisioned in this structural checkout:"
            )
        ):
            continue
        errors.append(finding.message)
    return list(dict.fromkeys(errors))


def _semantic_contract_nonclaim_scope_error(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
    raw_item: dict[str, Any],
    *,
    require_source_bytes: bool = True,
) -> str:
    """Return why a ``claim_bearing: false`` source item is unsafe.

    Schema-1 semantic contracts are a source-claim inventory, not a way to
    suppress unproved statements.  A row independently classified outside the
    configured source-presentation scope may remain as nonclaim proof/support
    context.  Inside that scope, the only exceptional non-claim lanes are the
    source-validated finite computational illustration and an explicit,
    byte-pinned source observation that declares an issue unresolved.  Every
    decision operates on source presentation and pinned bytes, never on a map
    key or Lean declaration name.
    """

    classification = str(
        raw_item.get("source_scope_classification") or ""
    ).strip().lower()
    if not classification:
        mode, mode_error = source_coverage_mode_from_map(payload)
        declared_environment_kinds = source_named_result_environment_kinds_from_map(
            payload
        )
        outside_presentation_scope = (
            not mode_error
            and mode is not None
            and not source_item_in_coverage_scope(
                raw_item,
                mode,
                declared_environment_kinds=declared_environment_kinds,
            )
        )
        if (
            outside_presentation_scope
            and raw_item.get(USER_APPROVED_SCOPE_EXCLUSION) is None
        ):
            return ""
    if classification == NON_NAMED_COMPUTATIONAL_ILLUSTRATION:
        try:
            dashboard = _source_scope_dashboard_module()
        except ModuleNotFoundError as error:
            return f"cannot load source-only computational scope validator: {error}"
        item = _semantic_contract_scope_item_context(payload, raw_item)
        scope_error = dashboard._source_inventory_item_scope_classification_error(item)
        if scope_error:
            return scope_error
        anchor_errors = _semantic_contract_item_anchor_errors(
            folder,
            status,
            manifest_path,
            payload,
            raw_item,
            require_source_bytes=require_source_bytes,
        )
        if anchor_errors:
            return "; ".join(anchor_errors)
        return ""

    if classification != SOURCE_DECLARED_OPEN_NONRESULT_OBSERVATION:
        return (
            "claim_bearing: false is permitted only for a source-validated "
            "non_named_computational_illustration or a "
            "source_declared_open_nonresult_observation, or nonclaim support "
            "independently outside the configured source-presentation scope"
        )

    # The source kind is not proof; it narrows this exceptional route to the
    # normal source presentation for a non-result observation.  The decisive
    # evidence remains the exact anchored quote below.
    if str(raw_item.get("source_kind") or "").strip().lower() not in {
        "remark",
        "open_problem",
    }:
        return (
            "source_declared_open_nonresult_observation requires source_kind "
            "`remark` or `open_problem`"
        )
    if not meaningful_semantic_text(raw_item.get("scope_reason")):
        return (
            "source_declared_open_nonresult_observation requires a source-grounded "
            "scope_reason"
        )
    if not meaningful_semantic_text(raw_item.get("source_evidence")):
        return (
            "source_declared_open_nonresult_observation requires source_evidence"
        )

    anchor_errors = _semantic_contract_item_anchor_errors(
        folder,
        status,
        manifest_path,
        payload,
        raw_item,
        require_source_bytes=require_source_bytes,
    )
    if anchor_errors:
        return "; ".join(anchor_errors)

    try:
        dashboard = _source_scope_dashboard_module()
    except ModuleNotFoundError as error:
        return f"cannot load source-only scope validator: {error}"
    source_quote, quote_error = dashboard._source_inventory_anchor_quote_text(
        _semantic_contract_scope_item_context(payload, raw_item)
    )
    if quote_error:
        return f"source_declared_open_nonresult_observation {quote_error}"
    if not SOURCE_DECLARED_OPEN_NONRESULT_RE.search(source_quote):
        return (
            "source_declared_open_nonresult_observation requires an explicit "
            "unresolved/open declaration in the byte-verified source quote"
        )
    if dashboard.SOURCE_NAMED_RESULT_PRESENTATION_RE.search(
        source_quote
    ) or SOURCE_POSITIVE_RESULT_PRESENTATION_RE.search(source_quote):
        return (
            "source_declared_open_nonresult_observation cannot combine its open "
            "observation with a positive named or ordinary result assertion"
        )
    return ""


def _semantic_contract_user_scope_exclusion_error(
    folder: Path,
    status: str,
    manifest_path: Path,
    payload: dict[str, Any],
    raw_item: dict[str, Any],
    *,
    require_source_bytes: bool = True,
) -> str:
    """Return why a claim-bearing explicit user scope disposition is invalid.

    A user-approved exclusion does not erase a source claim.  It may waive a
    proof contract only when the existing approval schema and the map item's
    exact byte-pinned source anchor both validate.
    """

    raw_approval = raw_item.get(USER_APPROVED_SCOPE_EXCLUSION)
    if raw_approval is None:
        return ""
    if raw_item.get("claim_bearing") is not True:
        return (
            "user_approved_scope_exclusion must keep the source item "
            "claim_bearing: true"
        )
    if str(raw_item.get("source_scope_classification") or "").strip():
        return (
            "user_approved_scope_exclusion cannot coexist with "
            "source_scope_classification"
        )
    approval_errors = user_approved_scope_exclusion_errors(
        folder,
        raw_approval,
        expected_source_locator=raw_item.get("source_location"),
        require_source_bytes=require_source_bytes,
    )
    if approval_errors:
        return "; ".join(approval_errors)
    try:
        dashboard = _source_scope_dashboard_module()
        scope_error = dashboard._source_inventory_item_user_approved_scope_exclusion_error(
            _semantic_contract_scope_item_context(payload, raw_item)
        )
    except (ModuleNotFoundError, AttributeError) as error:
        return f"cannot load source-only unnumbered-prose scope validator: {error}"
    if scope_error:
        return scope_error
    anchor_errors = _semantic_contract_item_anchor_errors(
        folder,
        status,
        manifest_path,
        payload,
        raw_item,
        require_source_bytes=require_source_bytes,
    )
    if anchor_errors:
        return "; ".join(anchor_errors)
    return ""


def _semantic_surface_string_list(
    raw_surface: dict[str, Any], field: str, errors: list[str], *, required: bool
) -> list[str]:
    """Read one literal-token list from a semantic-surface contract."""

    value = raw_surface.get(field)
    if value is None:
        if required:
            errors.append(f"semantic_surface.{field} must be a nonempty string list")
        return []
    if not isinstance(value, list) or not value:
        errors.append(f"semantic_surface.{field} must be a nonempty string list")
        return []
    if any(not isinstance(token, str) or not token.strip() for token in value):
        errors.append(f"semantic_surface.{field} must contain only nonempty strings")
        return []
    tokens = [token.strip() for token in value]
    if len(set(tokens)) != len(tokens):
        errors.append(f"semantic_surface.{field} must not repeat a token")
    return tokens


def _semantic_surface_pattern_string_list(
    raw_pattern: dict[str, Any], field: str, prefix: str, errors: list[str]
) -> list[str]:
    """Read one optional nonempty string-list from a schema-3 pattern."""

    value = raw_pattern.get(field)
    if value is None:
        return []
    if not isinstance(value, list) or not value:
        errors.append(f"{prefix}.{field} must be a nonempty string list when present")
        return []
    if any(not isinstance(item, str) or not item.strip() for item in value):
        errors.append(f"{prefix}.{field} must contain only nonempty strings")
        return []
    normalized = [item.strip() for item in value]
    if len(normalized) != len(set(normalized)):
        errors.append(f"{prefix}.{field} must not repeat a value")
    return normalized


def _semantic_surface_result_schema_errors(
    raw_surface: dict[str, Any], errors: list[str]
) -> None:
    """Validate schema-3 result-only pattern contracts.

    This validator does not accept source tokens or suffixes.  The live gate
    resolves the fixed feature vocabulary against Lean's canonical result tree.
    """

    outer_binder_sha256 = raw_surface.get("outer_binder_sha256")
    if (
        not isinstance(outer_binder_sha256, str)
        or not SHA256_RE.fullmatch(outer_binder_sha256)
        or outer_binder_sha256 != outer_binder_sha256.lower()
    ):
        errors.append(
            "semantic_surface.outer_binder_sha256 must be a lowercase 64-hex "
            "digest of the elaborated outer binder interface"
        )

    raw_patterns = raw_surface.get("required_result_patterns")
    if not isinstance(raw_patterns, list) or not raw_patterns:
        errors.append(
            "semantic_surface.required_result_patterns must be a nonempty list"
        )
        return

    ids: set[str] = set()
    captures: set[str] = set()
    equality_alias_captures: set[str] = set()
    equality_alias_capture_indices: dict[str, int] = {}
    equality_alias_consumers: dict[str, list[int]] = {}
    for index, raw_pattern in enumerate(raw_patterns):
        prefix = f"semantic_surface.required_result_patterns[{index}]"
        earlier_captures = set(captures)
        earlier_equality_alias_captures = set(equality_alias_captures)
        if not isinstance(raw_pattern, dict):
            errors.append(f"{prefix} must be an object")
            continue
        unknown_fields = sorted(
            set(raw_pattern) - SEMANTIC_SURFACE_RESULT_PATTERN_FIELDS
        )
        if unknown_fields:
            errors.append(
                f"{prefix} has unknown field(s): " + ", ".join(unknown_fields)
            )

        pattern_id = raw_pattern.get("id")
        if not isinstance(pattern_id, str) or not pattern_id.strip():
            errors.append(f"{prefix}.id must be a nonempty string")
        elif pattern_id in ids:
            errors.append(f"{prefix}.id must not repeat `{pattern_id}`")
        else:
            ids.add(pattern_id)

        relation = raw_pattern.get("relation")
        if relation not in SEMANTIC_SURFACE_RESULT_RELATIONS:
            errors.append(
                f"{prefix}.relation must be one of "
                + ", ".join(sorted(SEMANTIC_SURFACE_RESULT_RELATIONS))
            )

        features = _semantic_surface_pattern_string_list(
            raw_pattern, "all_features", prefix, errors
        )
        invalid_features = sorted(
            set(features) - SEMANTIC_SURFACE_RESULT_FEATURES
        )
        if invalid_features:
            errors.append(
                f"{prefix}.all_features contains unsupported feature(s): "
                + ", ".join(invalid_features)
            )

        raw_feature_counts = raw_pattern.get("minimum_feature_counts")
        feature_counts: dict[str, Any] = {}
        if raw_feature_counts is not None:
            if not isinstance(raw_feature_counts, dict) or not raw_feature_counts:
                errors.append(
                    f"{prefix}.minimum_feature_counts must be a nonempty object when present"
                )
            else:
                feature_counts = raw_feature_counts
                for feature, count in feature_counts.items():
                    if not isinstance(feature, str) or feature not in SEMANTIC_SURFACE_RESULT_FEATURES:
                        errors.append(
                            f"{prefix}.minimum_feature_counts has unsupported feature `{feature}`"
                        )
                    if (
                        not isinstance(count, int)
                        or isinstance(count, bool)
                        or count < 1
                    ):
                        errors.append(
                            f"{prefix}.minimum_feature_counts values must be positive integers"
                        )

        canonical_sha256 = raw_pattern.get("canonical_sha256")
        if canonical_sha256 is not None and (
            not isinstance(canonical_sha256, str)
            or not SHA256_RE.fullmatch(canonical_sha256)
            or canonical_sha256 != canonical_sha256.lower()
        ):
            errors.append(
                f"{prefix}.canonical_sha256 must be a lowercase 64-hex digest "
                "of the scope-normalized canonical result formula"
            )
        pattern_has_feature_constraint = bool(features or feature_counts)
        pattern_required_equality_aliases: set[str] = set()

        raw_operand_patterns = raw_pattern.get("operand_patterns")
        operand_patterns: list[Any] = []
        if raw_operand_patterns is not None:
            if relation == "any":
                errors.append(f"{prefix}.operand_patterns requires a relation with operands")
            if not isinstance(raw_operand_patterns, list) or not raw_operand_patterns:
                errors.append(
                    f"{prefix}.operand_patterns must be a nonempty list when present"
                )
            else:
                operand_patterns = raw_operand_patterns
                seen_sides: set[str] = set()
                allowed_sides = (
                    {"left", "right"}
                    if relation in {"eq", "iff", "lt", "le"}
                    else ({"argument"} if relation == "not" else set())
                )
                for operand_index, raw_operand in enumerate(operand_patterns):
                    operand_prefix = f"{prefix}.operand_patterns[{operand_index}]"
                    if not isinstance(raw_operand, dict):
                        errors.append(f"{operand_prefix} must be an object")
                        continue
                    unknown_operand = sorted(
                        set(raw_operand) - SEMANTIC_SURFACE_RESULT_OPERAND_PATTERN_FIELDS
                    )
                    if unknown_operand:
                        errors.append(
                            f"{operand_prefix} has unknown field(s): "
                            + ", ".join(unknown_operand)
                        )
                    side = raw_operand.get("side")
                    if side not in SEMANTIC_SURFACE_RESULT_OPERAND_SIDES:
                        errors.append(
                            f"{operand_prefix}.side must be one of "
                            + ", ".join(sorted(SEMANTIC_SURFACE_RESULT_OPERAND_SIDES))
                        )
                    elif side not in allowed_sides:
                        errors.append(
                            f"{operand_prefix}.side is not valid for relation `{relation}`"
                        )
                    elif side in seen_sides:
                        errors.append(f"{operand_prefix}.side must not repeat `{side}`")
                    else:
                        seen_sides.add(side)
                    operand_features = _semantic_surface_pattern_string_list(
                        raw_operand, "all_features", operand_prefix, errors
                    )
                    invalid_operand_features = sorted(
                        set(operand_features) - SEMANTIC_SURFACE_RESULT_FEATURES
                    )
                    if invalid_operand_features:
                        errors.append(
                            f"{operand_prefix}.all_features contains unsupported feature(s): "
                            + ", ".join(invalid_operand_features)
                        )
                    raw_operand_counts = raw_operand.get("minimum_feature_counts")
                    operand_counts: dict[str, Any] = {}
                    if raw_operand_counts is not None:
                        if not isinstance(raw_operand_counts, dict) or not raw_operand_counts:
                            errors.append(
                                f"{operand_prefix}.minimum_feature_counts must be a nonempty object when present"
                            )
                        else:
                            operand_counts = raw_operand_counts
                            for feature, count in operand_counts.items():
                                if (
                                    not isinstance(feature, str)
                                    or feature not in SEMANTIC_SURFACE_RESULT_FEATURES
                                ):
                                    errors.append(
                                        f"{operand_prefix}.minimum_feature_counts has unsupported feature `{feature}`"
                                    )
                                if (
                                    not isinstance(count, int)
                                    or isinstance(count, bool)
                                    or count < 1
                                ):
                                    errors.append(
                                        f"{operand_prefix}.minimum_feature_counts values must be positive integers"
                                    )
                    operand_captures = _semantic_surface_pattern_string_list(
                        raw_operand, "requires_captures", operand_prefix, errors
                    )
                    unknown_operand_captures = sorted(
                        set(operand_captures) - earlier_captures
                    )
                    if unknown_operand_captures:
                        errors.append(
                            f"{operand_prefix}.requires_captures must refer only to captures from earlier "
                            "patterns: " + ", ".join(unknown_operand_captures)
                        )
                    operand_equality_aliases = _semantic_surface_pattern_string_list(
                        raw_operand,
                        "requires_equality_aliases",
                        operand_prefix,
                        errors,
                    )
                    pattern_required_equality_aliases.update(
                        operand_equality_aliases
                    )
                    if operand_features or operand_counts:
                        pattern_has_feature_constraint = True
                    unknown_operand_equality_aliases = sorted(
                        set(operand_equality_aliases)
                        - earlier_equality_alias_captures
                    )
                    if unknown_operand_equality_aliases:
                        errors.append(
                            f"{operand_prefix}.requires_equality_aliases must refer only "
                            "to equality aliases from earlier patterns: "
                            + ", ".join(unknown_operand_equality_aliases)
                        )
                    if (
                        not operand_features
                        and not operand_counts
                        and not operand_captures
                        and not operand_equality_aliases
                    ):
                        errors.append(
                            f"{operand_prefix} must constrain a feature or earlier capture"
                        )

        require_distinct_operands = raw_pattern.get("require_distinct_operands")
        if require_distinct_operands is not None and not isinstance(
            require_distinct_operands, bool
        ):
            errors.append(f"{prefix}.require_distinct_operands must be boolean when present")
        elif require_distinct_operands is True and relation not in {"eq", "iff", "lt", "le"}:
            errors.append(
                f"{prefix}.require_distinct_operands requires eq, iff, lt, or le"
            )

        raw_guard_patterns = raw_pattern.get("guard_patterns")
        if raw_guard_patterns is not None:
            if not isinstance(raw_guard_patterns, list) or not raw_guard_patterns:
                errors.append(
                    f"{prefix}.guard_patterns must be a nonempty list when present"
                )
            else:
                for guard_index, raw_guard in enumerate(raw_guard_patterns):
                    guard_prefix = f"{prefix}.guard_patterns[{guard_index}]"
                    if not isinstance(raw_guard, dict):
                        errors.append(f"{guard_prefix} must be an object")
                        continue
                    unknown_guard = sorted(
                        set(raw_guard) - SEMANTIC_SURFACE_RESULT_GUARD_PATTERN_FIELDS
                    )
                    if unknown_guard:
                        errors.append(
                            f"{guard_prefix} has unknown field(s): "
                            + ", ".join(unknown_guard)
                        )
                    guard_relation = raw_guard.get("relation")
                    if guard_relation not in SEMANTIC_SURFACE_RESULT_RELATIONS:
                        errors.append(
                            f"{guard_prefix}.relation must be one of "
                            + ", ".join(sorted(SEMANTIC_SURFACE_RESULT_RELATIONS))
                        )
                    guard_features = _semantic_surface_pattern_string_list(
                        raw_guard, "all_features", guard_prefix, errors
                    )
                    invalid_guard_features = sorted(
                        set(guard_features) - SEMANTIC_SURFACE_RESULT_FEATURES
                    )
                    if invalid_guard_features:
                        errors.append(
                            f"{guard_prefix}.all_features contains unsupported feature(s): "
                            + ", ".join(invalid_guard_features)
                        )
                    raw_guard_counts = raw_guard.get("minimum_feature_counts")
                    guard_counts: dict[str, Any] = {}
                    if raw_guard_counts is not None:
                        if not isinstance(raw_guard_counts, dict) or not raw_guard_counts:
                            errors.append(
                                f"{guard_prefix}.minimum_feature_counts must be a nonempty object when present"
                            )
                        else:
                            guard_counts = raw_guard_counts
                            for feature, count in guard_counts.items():
                                if (
                                    not isinstance(feature, str)
                                    or feature not in SEMANTIC_SURFACE_RESULT_FEATURES
                                ):
                                    errors.append(
                                        f"{guard_prefix}.minimum_feature_counts has unsupported feature `{feature}`"
                                    )
                                if (
                                    not isinstance(count, int)
                                    or isinstance(count, bool)
                                    or count < 1
                                ):
                                    errors.append(
                                        f"{guard_prefix}.minimum_feature_counts values must be positive integers"
                                    )
                    canonical_sha256 = raw_guard.get("canonical_sha256")
                    if canonical_sha256 is not None and (
                        not isinstance(canonical_sha256, str)
                        or not SHA256_RE.fullmatch(canonical_sha256)
                        or canonical_sha256 != canonical_sha256.lower()
                    ):
                        errors.append(
                            f"{guard_prefix}.canonical_sha256 must be a lowercase "
                            "64-hex digest of the scope-normalized canonical guard"
                        )
                    if (
                        guard_relation == "any"
                        and not guard_features
                        and not guard_counts
                        and canonical_sha256 is None
                    ):
                        errors.append(
                            f"{guard_prefix} must constrain a relation or exact feature"
                        )

        quantifier_shape = raw_pattern.get("quantifier_shape")
        if not isinstance(quantifier_shape, dict):
            errors.append(
                f"{prefix}.quantifier_shape must be an object with forall and exists counts"
            )
        else:
            unknown_quantifiers = sorted(
                set(quantifier_shape) - SEMANTIC_SURFACE_RESULT_QUANTIFIER_FIELDS
            )
            missing_quantifiers = sorted(
                SEMANTIC_SURFACE_RESULT_QUANTIFIER_FIELDS - set(quantifier_shape)
            )
            if unknown_quantifiers:
                errors.append(
                    f"{prefix}.quantifier_shape has unknown field(s): "
                    + ", ".join(unknown_quantifiers)
                )
            if missing_quantifiers:
                errors.append(
                    f"{prefix}.quantifier_shape is missing field(s): "
                    + ", ".join(missing_quantifiers)
                )
            for quantifier in SEMANTIC_SURFACE_RESULT_QUANTIFIER_FIELDS:
                count = quantifier_shape.get(quantifier)
                if (
                    not isinstance(count, int)
                    or isinstance(count, bool)
                    or count < 0
                ):
                    errors.append(
                        f"{prefix}.quantifier_shape.{quantifier} must be a nonnegative integer"
                    )

        capture = raw_pattern.get("capture")
        if capture is not None:
            if not isinstance(capture, dict):
                errors.append(f"{prefix}.capture must be an object when present")
            else:
                unknown_capture = sorted(
                    set(capture) - SEMANTIC_SURFACE_RESULT_CAPTURE_FIELDS
                )
                if unknown_capture:
                    errors.append(
                        f"{prefix}.capture has unknown field(s): "
                        + ", ".join(unknown_capture)
                    )
                feature = capture.get("feature")
                if feature not in SEMANTIC_SURFACE_RESULT_CAPTURE_FEATURES:
                    errors.append(
                        f"{prefix}.capture.feature must be one of "
                        + ", ".join(sorted(SEMANTIC_SURFACE_RESULT_CAPTURE_FEATURES))
                    )
                mode = capture.get("mode", "root")
                if mode not in SEMANTIC_SURFACE_RESULT_CAPTURE_MODES:
                    errors.append(
                        f"{prefix}.capture.mode must be one of "
                        + ", ".join(sorted(SEMANTIC_SURFACE_RESULT_CAPTURE_MODES))
                    )
                capture_name = capture.get("as")
                if not isinstance(capture_name, str) or not capture_name.strip():
                    errors.append(f"{prefix}.capture.as must be a nonempty string")
                elif (
                    capture_name in captures
                    or capture_name in equality_alias_captures
                ):
                    errors.append(
                        f"{prefix}.capture.as must not repeat a capture or equality alias "
                        f"name `{capture_name}`"
                    )
                else:
                    captures.add(capture_name)
                distinct_from = _semantic_surface_pattern_string_list(
                    capture, "distinct_from", f"{prefix}.capture", errors
                )
                unknown_distinct = sorted(set(distinct_from) - earlier_captures)
                if unknown_distinct:
                    errors.append(
                        f"{prefix}.capture.distinct_from must refer only to captures from "
                        "earlier patterns: " + ", ".join(unknown_distinct)
                    )

        equality_alias_capture = raw_pattern.get("equality_alias_capture")
        if equality_alias_capture is not None:
            if not isinstance(equality_alias_capture, dict):
                errors.append(
                    f"{prefix}.equality_alias_capture must be an object when present"
                )
            else:
                unknown_alias_fields = sorted(
                    set(equality_alias_capture)
                    - SEMANTIC_SURFACE_RESULT_EQUALITY_ALIAS_CAPTURE_FIELDS
                )
                if unknown_alias_fields:
                    errors.append(
                        f"{prefix}.equality_alias_capture has unknown field(s): "
                        + ", ".join(unknown_alias_fields)
                    )
                if relation != "eq":
                    errors.append(
                        f"{prefix}.equality_alias_capture requires relation `eq`"
                    )
                if capture is not None:
                    errors.append(
                        f"{prefix} may not combine capture and equality_alias_capture"
                    )
                alias_side = equality_alias_capture.get("alias_side")
                if alias_side not in {"left", "right"}:
                    errors.append(
                        f"{prefix}.equality_alias_capture.alias_side must be `left` or `right`"
                    )
                construction_feature = equality_alias_capture.get(
                    "construction_feature"
                )
                if construction_feature not in SEMANTIC_SURFACE_RESULT_FEATURES:
                    errors.append(
                        f"{prefix}.equality_alias_capture.construction_feature must be one "
                        "of "
                        + ", ".join(sorted(SEMANTIC_SURFACE_RESULT_FEATURES))
                    )
                alias_name = equality_alias_capture.get("as")
                if not isinstance(alias_name, str) or not alias_name.strip():
                    errors.append(
                        f"{prefix}.equality_alias_capture.as must be a nonempty string"
                    )
                elif (
                    alias_name in equality_alias_captures
                    or alias_name in captures
                ):
                    errors.append(
                        f"{prefix}.equality_alias_capture.as must not repeat a capture name "
                        f"`{alias_name}`"
                    )
                else:
                    equality_alias_captures.add(alias_name)
                    equality_alias_capture_indices[alias_name] = index

        allow_leaf_reuse = raw_pattern.get("allow_leaf_reuse")
        if allow_leaf_reuse is not None and not isinstance(allow_leaf_reuse, bool):
            errors.append(f"{prefix}.allow_leaf_reuse must be boolean when present")
        elif equality_alias_capture is not None and allow_leaf_reuse is True:
            errors.append(
                f"{prefix}.equality_alias_capture forbids allow_leaf_reuse so a later "
                "result leaf must consume the alias"
            )

        required_captures = _semantic_surface_pattern_string_list(
            raw_pattern, "requires_captures", prefix, errors
        )
        unknown_captures = sorted(set(required_captures) - earlier_captures)
        if unknown_captures:
            errors.append(
                f"{prefix}.requires_captures must refer only to captures from earlier "
                "patterns: " + ", ".join(unknown_captures)
            )
        if required_captures and relation in {"eq", "iff", "lt", "le"}:
            if not operand_patterns:
                errors.append(
                    f"{prefix}.requires_captures on a binary relation requires "
                    "operand_patterns that place every capture"
                )
            else:
                placed_captures: set[str] = set()
                for raw_operand in operand_patterns:
                    if isinstance(raw_operand, dict):
                        placed_captures.update(
                            _semantic_surface_pattern_string_list(
                                raw_operand,
                                "requires_captures",
                                prefix,
                                errors,
                            )
                        )
                missing_placed_captures = sorted(
                    set(required_captures) - placed_captures
                )
                if missing_placed_captures:
                    errors.append(
                        f"{prefix}.operand_patterns must place required capture(s): "
                        + ", ".join(missing_placed_captures)
                    )
        if required_captures and relation == "any":
            errors.append(
                f"{prefix}.requires_captures requires an asserted relation, not `any`"
            )
        required_equality_aliases = _semantic_surface_pattern_string_list(
            raw_pattern, "requires_equality_aliases", prefix, errors
        )
        pattern_required_equality_aliases.update(required_equality_aliases)
        unknown_equality_aliases = sorted(
            set(required_equality_aliases) - earlier_equality_alias_captures
        )
        if unknown_equality_aliases:
            errors.append(
                f"{prefix}.requires_equality_aliases must refer only to equality aliases "
                "from earlier patterns: " + ", ".join(unknown_equality_aliases)
            )
        if required_equality_aliases and relation in {"eq", "iff", "lt", "le"}:
            if not operand_patterns:
                errors.append(
                    f"{prefix}.requires_equality_aliases on a binary relation requires "
                    "operand_patterns that place every alias"
                )
            else:
                placed_equality_aliases: set[str] = set()
                for raw_operand in operand_patterns:
                    if isinstance(raw_operand, dict):
                        placed_equality_aliases.update(
                            _semantic_surface_pattern_string_list(
                                raw_operand,
                                "requires_equality_aliases",
                                prefix,
                                errors,
                            )
                        )
                missing_placed_equality_aliases = sorted(
                    set(required_equality_aliases) - placed_equality_aliases
                )
                if missing_placed_equality_aliases:
                    errors.append(
                        f"{prefix}.operand_patterns must place required equality alias(es): "
                        + ", ".join(missing_placed_equality_aliases)
                    )
        if required_equality_aliases and relation not in {"eq", "iff", "lt", "le"}:
            errors.append(
                f"{prefix}.requires_equality_aliases requires a binary asserted relation"
            )
        if pattern_required_equality_aliases:
            if allow_leaf_reuse is True:
                errors.append(
                    f"{prefix}.requires_equality_aliases forbids allow_leaf_reuse so "
                    "an alias is consumed by a distinct result leaf"
                )
            if not pattern_has_feature_constraint:
                errors.append(
                    f"{prefix}.requires_equality_aliases requires independent "
                    "semantic feature content outside the alias"
                )
            for alias_name in pattern_required_equality_aliases:
                equality_alias_consumers.setdefault(alias_name, []).append(index)
        if relation == "any" and capture is not None:
            errors.append(
                f"{prefix}.capture requires an asserted relation, not `any`"
            )

        minimum = raw_pattern.get("min_matches", 1)
        if (
            not isinstance(minimum, int)
            or isinstance(minimum, bool)
            or minimum < 1
        ):
            errors.append(f"{prefix}.min_matches must be a positive integer")
        elif (capture is not None or equality_alias_capture is not None) and minimum != 1:
            errors.append(
                f"{prefix}.capture and equality_alias_capture require min_matches to be 1"
            )
        if (
            relation == "any"
            and not features
            and not feature_counts
            and not operand_patterns
            and capture is None
            and equality_alias_capture is None
            and not required_captures
            and not required_equality_aliases
            and canonical_sha256 is None
        ):
            errors.append(
                f"{prefix} must constrain a result relation, exact feature, or capture"
            )

    for alias_name, capture_index in equality_alias_capture_indices.items():
        if not any(
            consumer_index > capture_index
            for consumer_index in equality_alias_consumers.get(alias_name, [])
        ):
            errors.append(
                "semantic_surface.required_result_patterns["
                f"{capture_index}].equality_alias_capture.as `{alias_name}` must be "
                "required by a later distinct result pattern"
            )


def _semantic_surface_assumption_schema_errors(
    raw_surface: dict[str, Any], errors: list[str]
) -> None:
    """Validate optional schema-3 patterns over explicit theorem assumptions."""

    raw_patterns = raw_surface.get("required_assumption_patterns")
    if raw_patterns is None:
        return
    if not isinstance(raw_patterns, list) or not raw_patterns:
        errors.append(
            "semantic_surface.required_assumption_patterns must be a nonempty list when present"
        )
        return
    ids: set[str] = set()
    for index, raw_pattern in enumerate(raw_patterns):
        prefix = f"semantic_surface.required_assumption_patterns[{index}]"
        if not isinstance(raw_pattern, dict):
            errors.append(f"{prefix} must be an object")
            continue
        unknown_fields = sorted(
            set(raw_pattern) - SEMANTIC_SURFACE_ASSUMPTION_PATTERN_FIELDS
        )
        if unknown_fields:
            errors.append(
                f"{prefix} has unknown field(s): " + ", ".join(unknown_fields)
            )
        pattern_id = raw_pattern.get("id")
        if not isinstance(pattern_id, str) or not pattern_id.strip():
            errors.append(f"{prefix}.id must be a nonempty string")
        elif pattern_id in ids:
            errors.append(f"{prefix}.id must not repeat `{pattern_id}`")
        else:
            ids.add(pattern_id)
        relation = raw_pattern.get("relation")
        if relation not in SEMANTIC_SURFACE_RESULT_RELATIONS:
            errors.append(
                f"{prefix}.relation must be one of "
                + ", ".join(sorted(SEMANTIC_SURFACE_RESULT_RELATIONS))
            )
        features = _semantic_surface_pattern_string_list(
            raw_pattern, "all_features", prefix, errors
        )
        invalid_features = sorted(
            set(features) - SEMANTIC_SURFACE_RESULT_FEATURES
        )
        if invalid_features:
            errors.append(
                f"{prefix}.all_features contains unsupported feature(s): "
                + ", ".join(invalid_features)
            )
        raw_feature_counts = raw_pattern.get("minimum_feature_counts")
        if raw_feature_counts is not None:
            if not isinstance(raw_feature_counts, dict) or not raw_feature_counts:
                errors.append(
                    f"{prefix}.minimum_feature_counts must be a nonempty object when present"
                )
            else:
                for feature, count in raw_feature_counts.items():
                    if (
                        not isinstance(feature, str)
                        or feature not in SEMANTIC_SURFACE_RESULT_FEATURES
                    ):
                        errors.append(
                            f"{prefix}.minimum_feature_counts has unsupported feature `{feature}`"
                        )
                    if (
                        not isinstance(count, int)
                        or isinstance(count, bool)
                        or count < 1
                    ):
                        errors.append(
                            f"{prefix}.minimum_feature_counts values must be positive integers"
                        )
        minimum = raw_pattern.get("min_matches", 1)
        if (
            not isinstance(minimum, int)
            or isinstance(minimum, bool)
            or minimum < 1
        ):
            errors.append(f"{prefix}.min_matches must be a positive integer")


def semantic_surface_validation_errors(raw_surface: object) -> list[str]:
    """Validate a declaration-signature semantic-surface contract.

    The required structural operators are mandatory.  That keeps the contract
    from becoming a second declaration-name convention: exact helper terms may
    refine a source model, but they cannot be the only evidence that a direct
    route exposes its quantifiers, conditionals, integrations, or comparison.
    """

    if not isinstance(raw_surface, dict):
        return ["semantic_surface must be an object"]

    errors: list[str] = []
    schema = raw_surface.get("schema")
    allowed_fields = (
        SEMANTIC_SURFACE_V1_FIELDS
        if schema_version_is_exact(schema, SEMANTIC_SURFACE_LEGACY_SCHEMA)
        else (
            SEMANTIC_SURFACE_V2_FIELDS
            if schema_version_is_exact(schema, SEMANTIC_SURFACE_SCHEMA)
            else SEMANTIC_SURFACE_V3_FIELDS
        )
    )
    unknown_fields = sorted(set(raw_surface) - allowed_fields)
    if unknown_fields:
        errors.append(
            "semantic_surface has unknown field(s): " + ", ".join(unknown_fields)
        )
    if not schema_version_is_supported(schema, SEMANTIC_SURFACE_SCHEMAS):
        errors.append(
            "semantic_surface.schema must be one of "
            + ", ".join(str(value) for value in sorted(SEMANTIC_SURFACE_SCHEMAS))
        )

    if schema_version_is_exact(schema, SEMANTIC_SURFACE_RESULT_SCHEMA):
        _semantic_surface_result_schema_errors(raw_surface, errors)
        _semantic_surface_assumption_schema_errors(raw_surface, errors)
        return errors

    structural_tokens = _semantic_surface_string_list(
        raw_surface, "required_structural_tokens", errors, required=True
    )
    invalid_structural = sorted(
        set(structural_tokens) - SEMANTIC_SURFACE_STRUCTURAL_TOKENS
    )
    if invalid_structural:
        errors.append(
            "semantic_surface.required_structural_tokens contains unsupported "
            "non-structural token(s): "
            + ", ".join(invalid_structural)
        )

    _semantic_surface_string_list(raw_surface, "required_terms", errors, required=False)
    _semantic_surface_string_list(
        raw_surface, "forbidden_opaque_terms", errors, required=False
    )

    if not schema_version_is_exact(schema, SEMANTIC_SURFACE_SCHEMA):
        return errors

    raw_components = raw_surface.get("required_conclusion_components")
    if not isinstance(raw_components, list) or not raw_components:
        errors.append(
            "semantic_surface.required_conclusion_components must be a nonempty list"
        )
        return errors

    for index, raw_component in enumerate(raw_components):
        prefix = f"semantic_surface.required_conclusion_components[{index}]"
        if not isinstance(raw_component, dict):
            errors.append(f"{prefix} must be an object")
            continue
        unknown_component_fields = sorted(
            set(raw_component) - SEMANTIC_SURFACE_CONCLUSION_COMPONENT_FIELDS
        )
        if unknown_component_fields:
            errors.append(
                f"{prefix} has unknown field(s): "
                + ", ".join(unknown_component_fields)
            )

        selector = raw_component.get("selector")
        if selector not in SEMANTIC_SURFACE_CONCLUSION_SELECTORS:
            errors.append(
                f"{prefix}.selector must be one of "
                + ", ".join(sorted(SEMANTIC_SURFACE_CONCLUSION_SELECTORS))
            )
        relation = raw_component.get("relation")
        if relation not in SEMANTIC_SURFACE_CONCLUSION_RELATIONS:
            errors.append(
                f"{prefix}.relation must be one of "
                + ", ".join(sorted(SEMANTIC_SURFACE_CONCLUSION_RELATIONS))
            )

        left_operand = raw_component.get("left_operand")
        if left_operand is not None and left_operand not in (
            SEMANTIC_SURFACE_CONCLUSION_LEFT_OPERANDS
        ):
            errors.append(
                f"{prefix}.left_operand must be one of "
                + ", ".join(sorted(SEMANTIC_SURFACE_CONCLUSION_LEFT_OPERANDS))
            )

        def component_string_list(field: str) -> list[str]:
            value = raw_component.get(field)
            if value is None:
                return []
            if not isinstance(value, list) or not value:
                errors.append(f"{prefix}.{field} must be a nonempty string list when present")
                return []
            if any(not isinstance(item, str) or not item.strip() for item in value):
                errors.append(f"{prefix}.{field} must contain only nonempty strings")
                return []
            normalized = [item.strip() for item in value]
            if len(normalized) != len(set(normalized)):
                errors.append(f"{prefix}.{field} must not repeat a value")
            return normalized

        features = component_string_list("required_semantic_features")
        invalid_features = sorted(set(features) - SEMANTIC_SURFACE_CONCLUSION_FEATURES)
        if invalid_features:
            errors.append(
                f"{prefix}.required_semantic_features contains unsupported feature(s): "
                + ", ".join(invalid_features)
            )
        constants = component_string_list("required_constant_suffixes")
        if any(" " in constant for constant in constants):
            errors.append(
                f"{prefix}.required_constant_suffixes may not contain whitespace"
            )
        if left_operand is None and not features and not constants:
            errors.append(
                f"{prefix} must constrain a relation operand, semantic feature, or source primitive"
            )

        min_matches = raw_component.get("min_matches", 1)
        if not isinstance(min_matches, int) or isinstance(min_matches, bool) or min_matches < 1:
            errors.append(f"{prefix}.min_matches must be a positive integer")
        elif selector == "rightmost_top_level_conjunct" and min_matches != 1:
            errors.append(
                f"{prefix}.min_matches must be 1 for rightmost_top_level_conjunct"
            )
    return errors


def semantic_surface_inventory_findings(
    folder: Path,
    status: str,
    payload: dict[str, Any] | None = None,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Validate opt-in signature-surface contracts in a source map.

    This fast lane deliberately validates only JSON shape.  The repository
    audit resolves each direct declaration and checks its comment-free type
    signature against these tokens, so neither lane needs to infer semantics
    from source-item or Lean declaration names.
    """

    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    if payload is None:
        payload = load_json(map_path)
    if not isinstance(payload, dict):
        return []
    source_coverage_mode, _mode_error = source_coverage_mode_from_map(payload)
    _scoped_payload, raw_items = scoped_source_map_payload(
        payload,
        source_coverage_mode,
        folder=folder,
        repository_root=ROOT,
    )

    findings: list[Finding] = []
    severity = finding_severity(status)
    schema3_items: list[tuple[str, dict[str, Any]]] = []
    for source_key, raw_item in raw_items.items():
        if not isinstance(raw_item, dict) or "semantic_surface" not in raw_item:
            continue
        raw_surface = raw_item.get("semantic_surface")
        for error in semantic_surface_validation_errors(raw_surface):
            findings.append(
                Finding(
                    severity,
                    folder.name,
                    rel(map_path),
                    f"items.{source_key}: {error}",
                )
            )
        if isinstance(raw_surface, dict) and schema_version_is_exact(
            raw_surface.get("schema"), SEMANTIC_SURFACE_RESULT_SCHEMA
        ):
            schema3_items.append((str(source_key), raw_item))

    # Schema 3 intentionally recognizes only a small set of foundational
    # operators.  That is a useful anti-drift check, but no finite operator
    # vocabulary can establish that a source theorem was faithfully stated.
    # A completed paper therefore needs an independently source-anchored,
    # exact Prop specification and Lean-Meta proof/refutation route for every
    # schema-3 source claim.  This prevents a familiar collection of symbols
    # from becoming a substitute for the paper's actual formula.
    if schema3_items and status in CLOSEOUT_STATUSES:
        if not schema_version_is_supported(
            payload.get("semantic_contract_schema"), SEMANTIC_CONTRACT_SCHEMAS
        ):
            findings.append(
                Finding(
                    severity,
                    folder.name,
                    rel(map_path),
                    "schema-3 semantic surfaces require top-level "
                    "semantic_contract_schema 1 or 2 at closeout; "
                    "operator-pattern matches are supplementary evidence only",
                )
            )
        if payload.get(SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY) is not True:
            findings.append(
                Finding(
                    severity,
                    folder.name,
                    rel(map_path),
                    "schema-3 semantic surfaces require "
                    f"{SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY}: true at closeout",
                )
            )
        for source_key, raw_item in schema3_items:
            if raw_item.get("claim_bearing") is not True:
                findings.append(
                    Finding(
                        severity,
                        folder.name,
                        rel(map_path),
                        f"items.{source_key}: schema-3 source claim must set "
                        "claim_bearing: true at closeout",
                    )
                )
            if not isinstance(raw_item.get("semantic_contract"), dict):
                findings.append(
                    Finding(
                        severity,
                        folder.name,
                        rel(map_path),
                        f"items.{source_key}: schema-3 source claim needs an exact "
                        "semantic_contract at closeout",
                    )
                )
    return findings


def v11_direct_semantic_review_state(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> tuple[bool, str]:
    """Return whether the selected v11 direct-review lane is current.

    This is deliberately narrower than a final closure receipt: it establishes
    that the current source-to-expanded-Spec and material-library ledgers are
    complete and valid, but does not claim a focused-build receipt or completed
    human review.  It prevents a historical v10 aggregate record from blocking
    a paper that has explicitly selected the v11 direct semantic-review lane.
    The final receipt remains the only release-closure evidence.
    """

    if status not in CLOSEOUT_STATUSES:
        return False, "paper status does not select a closeout review lane"
    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    source_map = transaction_json(map_path, context)
    if not isinstance(source_map, dict) or not raw_source_spec_screening_requested(
        status_payload, source_map, folder=folder
    ):
        return False, "paper does not select the v11 direct source-to-Spec lane"

    findings = v11_raw_source_spec_screening_findings(
        folder,
        status,
        require_source_bytes=require_source_bytes,
        context=context,
    )
    findings.extend(
        material_library_semantic_review_findings(
            folder,
            status,
            require_source_bytes=require_source_bytes,
            context=context,
        )
    )
    if not findings:
        return True, ""
    detail = str(findings[0].message).strip()
    return False, detail or "v11 direct semantic-review evidence is incomplete"


def semantic_contract_inventory_findings(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Validate opt-in contracts and repaired-defect routing without a Lean build.

    This fast lane checks only schema and cross-sidecar routing. The full
    repository audit independently asks Lean Meta whether the evidence proves
    the exact specification, or its exact negation for a refutation contract.
    """

    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    payload = transaction_json(map_path, context)
    atom_findings = source_claim_atom_inventory_findings(
        folder,
        status,
        require_source_bytes=require_source_bytes,
        context=context,
    )
    correspondence_findings = source_spec_correspondence_inventory_findings(
        folder,
        status,
        require_source_bytes=require_source_bytes,
        context=context,
    )
    v11_screening_findings = v11_raw_source_spec_screening_findings(
        folder,
        status,
        require_source_bytes=require_source_bytes,
        context=context,
    )
    library_semantic_findings = material_library_semantic_review_findings(
        folder,
        status,
        require_source_bytes=require_source_bytes,
        context=context,
    )
    if payload is None:
        return (
            atom_findings
            + correspondence_findings
            + v11_screening_findings
            + library_semantic_findings
        )
    if not isinstance(payload, dict):
        return (
            atom_findings
            + correspondence_findings
            + v11_screening_findings
            + library_semantic_findings
            + source_map_scope_integrity_findings(folder, status, map_path, payload)
        )

    # Map structure and source presentation are always validated over the raw
    # inventory.  Only theorem-level contract obligations are scope-selected.
    findings = source_map_scope_integrity_findings(folder, status, map_path, payload)
    findings.extend(atom_findings)
    findings.extend(correspondence_findings)
    findings.extend(v11_screening_findings)
    findings.extend(library_semantic_findings)
    source_coverage_mode, mode_findings = source_coverage_mode_findings(
        folder, status, map_path, payload
    )
    findings.extend(mode_findings)
    raw_items = payload.get("items")
    _scoped_payload, items = scoped_source_map_payload(
        payload,
        source_coverage_mode,
        folder=folder,
        repository_root=ROOT,
    )
    validated_aliases = validated_presentation_alias_contract_exemptions(
        folder, payload
    )
    explicit_nonclaim_scope_items = {
        str(source_key): raw_item
        for source_key, raw_item in (raw_items.items() if isinstance(raw_items, dict) else [])
        if isinstance(raw_item, dict)
        and raw_item.get("claim_bearing") is False
    }
    marker_present = "semantic_contract_schema" in payload
    marker = payload.get("semantic_contract_schema")
    item_opt_in = any(
        isinstance(item, dict)
        and ("semantic_contract" in item or item.get("claim_bearing") is True)
        for item in items.values()
    )
    # An explicit non-claim classification is a source-scope exception, not a
    # deep-prose theorem obligation.  It nonetheless needs byte-pinned
    # validation even when ordinary named-theory selection excludes the row.
    item_opt_in = item_opt_in or any(
        "source_scope_classification" in item
        for item in explicit_nonclaim_scope_items.values()
    )
    if not marker_present and not item_opt_in:
        return findings

    severity = finding_severity(status)

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(map_path), message))

    if item_opt_in and not marker_present:
        add(
            "semantic_contract_schema is required when an item uses "
            "claim_bearing: true or semantic_contract"
        )
    marker_supported = schema_version_is_supported(
        marker, SEMANTIC_CONTRACT_SCHEMAS
    )
    if marker_present and not marker_supported:
        add(
            "semantic_contract_schema must be one of: "
            + ", ".join(str(value) for value in sorted(SEMANTIC_CONTRACT_SCHEMAS))
            + f"; got {marker!r}"
        )
    if marker_present and not isinstance(raw_items, dict):
        add("semantic-contract source map `items` must be an object")

    validated_nonclaim_scope_items: set[str] = set()
    if marker_supported:
        for source_key, raw_item in explicit_nonclaim_scope_items.items():
            scope_error = _semantic_contract_nonclaim_scope_error(
                folder,
                status,
                map_path,
                payload,
                raw_item,
                require_source_bytes=require_source_bytes,
            )
            if scope_error:
                add(f"items.{source_key}: {scope_error}")
            validated_nonclaim_scope_items.add(source_key)

    valid_contract_items: set[str] = set()
    for source_key, raw_item in items.items():
        if not isinstance(raw_item, dict):
            if marker_supported:
                add(f"items.{source_key} must be an object")
            continue
        claim_bearing = raw_item.get("claim_bearing")
        if marker_supported and "claim_bearing" not in raw_item:
            add(
                f"items.{source_key}.claim_bearing must be explicitly Boolean under "
                "a supported semantic_contract_schema"
            )
        if "claim_bearing" in raw_item and not isinstance(claim_bearing, bool):
            add(f"items.{source_key}.claim_bearing must be Boolean")
        if (
            marker_supported
            and claim_bearing is False
            and str(source_key) not in validated_nonclaim_scope_items
        ):
            scope_error = _semantic_contract_nonclaim_scope_error(
                folder,
                status,
                map_path,
                payload,
                raw_item,
                require_source_bytes=require_source_bytes,
            )
            if scope_error:
                add(f"items.{source_key}: {scope_error}")
        raw_contract = raw_item.get("semantic_contract")
        for error in source_core_projection_validation_errors(raw_item):
            add(f"items.{source_key}: {error}")
        raw_defect_ids = raw_item.get("source_defect_ids")
        if raw_defect_ids is not None and (
            not isinstance(raw_defect_ids, list)
            or any(
                not isinstance(value, str) or not value.strip()
                for value in raw_defect_ids
            )
            or len({value.strip() for value in raw_defect_ids}) != len(raw_defect_ids)
        ):
            add(
                f"items.{source_key}.source_defect_ids must be a list of "
                "unique nonempty strings"
            )
        if (
            claim_bearing is True
            and raw_contract is None
            and str(source_key) not in validated_aliases
            and _semantic_contract_item_requires_proof_evidence(
                payload, str(source_key), raw_item
            )
        ):
            scope_error = _semantic_contract_user_scope_exclusion_error(
                folder,
                status,
                map_path,
                payload,
                raw_item,
                require_source_bytes=require_source_bytes,
            )
            if scope_error:
                add(
                    f"claim-bearing source item `{source_key}` lacks semantic_contract; "
                    f"user_approved_scope_exclusion is not a valid scope disposition: "
                    f"{scope_error}"
                )
            elif raw_item.get(USER_APPROVED_SCOPE_EXCLUSION) is None:
                add(
                    f"claim-bearing source item `{source_key}` lacks semantic_contract"
                )
            continue
        if raw_contract is None:
            continue
        errors = semantic_contract_validation_errors(
            raw_contract,
            schema=marker if marker_supported else SEMANTIC_CONTRACT_SCHEMA,
        )
        for error in errors:
            add(f"items.{source_key}: {error}")
        if not errors:
            valid_contract_items.add(str(source_key))

    findings.extend(
        conditional_probability_composition_anchor_findings(
            folder,
            status,
            map_path,
            payload,
            items,
        )
    )

    if marker_supported:
        status_payload = (
            context.status_payload
            if context is not None
            else (load_json(folder / "status.json") or {})
        )
        config = source_proof_fidelity_config(status_payload)
        if config is None:
            fidelity_path = canonical_sidecar(folder, "source_proof_fidelity.json")
        else:
            fidelity_path, path_error = source_proof_fidelity_ledger_path(
                folder, status_payload
            )
            if path_error:
                add(path_error)
                fidelity_path = None
        fidelity = (
            transaction_json(fidelity_path, context)
            if fidelity_path is not None
            else None
        )
        fidelity = fidelity or {}
        raw_defects = fidelity.get("defects")
        ledger_ids = {
            str(defect.get("id") or "").strip()
            for defect in (raw_defects if isinstance(raw_defects, list) else [])
            if isinstance(defect, dict) and str(defect.get("id") or "").strip()
        }
        for source_key, raw_item in items.items():
            if not isinstance(raw_item, dict):
                continue
            raw_ids = raw_item.get("source_defect_ids")
            cited_ids = {
                str(value).strip()
                for value in (raw_ids if isinstance(raw_ids, list) else [])
                if isinstance(value, str) and value.strip()
            }
            unknown_ids = sorted(cited_ids - ledger_ids)
            if unknown_ids:
                add(
                    f"items.{source_key}.source_defect_ids cites id(s) absent from "
                    "the configured source-proof fidelity ledger: "
                    + ", ".join(unknown_ids)
                )
        repaired_ids = {
            str(defect.get("id") or "").strip()
            for defect in (raw_defects if isinstance(raw_defects, list) else [])
            if isinstance(defect, dict)
            and str(defect.get("resolution") or "").strip() == "repaired_in_lean"
            and str(defect.get("id") or "").strip()
        }
        for defect_id in sorted(repaired_ids):
            routed = False
            for source_key, raw_item in items.items():
                if str(source_key) not in valid_contract_items or not isinstance(
                    raw_item, dict
                ):
                    continue
                raw_ids = raw_item.get("source_defect_ids")
                if isinstance(raw_ids, list) and defect_id in {
                    str(value).strip() for value in raw_ids if isinstance(value, str)
                }:
                    routed = True
                    break
            if not routed:
                add(
                    f"source-proof defect `{defect_id}` is `repaired_in_lean` but no "
                    "source-map item links it through source_defect_ids to a valid "
                    "semantic_contract; the full audit must also Lean-check that contract"
                )
    return findings


def source_proof_fidelity_config(status_payload: dict[str, Any]) -> dict[str, Any] | None:
    """Return the configured proof-fidelity ledger metadata, when present."""

    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return None
    config = review_surface.get("source_proof_fidelity_review")
    return config if isinstance(config, dict) else None


def explicit_source_routes_enabled(status_payload: dict[str, Any]) -> bool:
    """Return whether the status surface opts into exact v10 source routes."""

    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return False
    statement_review = review_surface.get("llm_statement_review")
    return (
        isinstance(statement_review, dict)
        and statement_review.get("require_explicit_source_routes") is True
    )


def canonical_source_map_has_source_defect_links(
    folder: Path,
    *,
    context: EvidenceRunContext | None = None,
) -> bool:
    """Detect source-defect routing structurally, not by source-row spelling."""

    path = transaction_sidecar(folder, "paper_statement_map.json", context)
    payload = transaction_json(path, context) or {}
    for _key, item in item_entries(payload):
        raw_ids = item.get("source_defect_ids")
        if isinstance(raw_ids, list):
            if any(str(value).strip() for value in raw_ids):
                return True
        elif raw_ids:
            # A malformed nonempty value is still evidence that the paper tried
            # to route a source defect. The ledger/configuration must not become
            # optional merely because a second validator will report the shape.
            return True
    return False


def canonical_source_map_defect_ids(
    folder: Path,
    *,
    context: EvidenceRunContext | None = None,
) -> set[str]:
    """Return every nonblank source-proof defect id routed by the source map."""

    path = transaction_sidecar(folder, "paper_statement_map.json", context)
    payload = transaction_json(path, context) or {}
    defect_ids: set[str] = set()
    for _key, item in item_entries(payload):
        raw_ids = item.get("source_defect_ids")
        values = raw_ids if isinstance(raw_ids, list) else [raw_ids]
        for value in values:
            if isinstance(value, str) and value.strip():
                defect_ids.add(value.strip())
            elif value is not None:
                # The map-schema validator reports the bad shape when opted
                # in; this full-closeout route must also fail closed rather
                # than dropping a nonblank malformed id before ledger routing.
                defect_ids.add(
                    f"<malformed-source-defect-id:{type(value).__name__}>"
                )
    return defect_ids


def canonical_source_proof_ledger_has_defects(
    folder: Path,
    *,
    context: EvidenceRunContext | None = None,
) -> bool:
    """Return whether the canonical ledger records any source-proof issue."""

    path = transaction_sidecar(folder, "source_proof_fidelity.json", context)
    payload = transaction_json(path, context)
    return bool(payload and payload.get("defects"))


def canonical_source_proof_ledger_has_deep_observations(
    folder: Path,
    *,
    context: EvidenceRunContext | None = None,
) -> bool:
    """Return whether the canonical ledger records audited deep prose findings."""

    path = transaction_sidecar(folder, "source_proof_fidelity.json", context)
    payload = transaction_json(path, context)
    return bool(payload and payload.get("deep_audit_observations"))


def deep_audit_observation_map_link_errors(
    map_payload: object,
    observation_ids: set[str],
) -> list[str]:
    """Validate the source-map links for normal-scope deep observations.

    A deep observation is documentation for an unnumbered prose finding, not a
    new route for discharging a theorem.  The decision whether its linked row
    is outside ordinary scope is therefore made from the source presentation
    via ``source_item_in_coverage_scope``.  Map keys only identify the row in
    diagnostics and are never evidence of scope or of a Lean proof.
    """

    if not isinstance(map_payload, dict):
        return [
            "deep_audit_observations require a readable canonical source map "
            "with linked source rows"
        ]

    errors: list[str] = []
    mode, mode_error = source_coverage_mode_from_map(map_payload)
    if mode_error:
        errors.append(
            "deep_audit_observations cannot establish their normal-scope "
            f"disposition: {mode_error}"
        )
    elif mode != NAMED_THEORETICAL_STATEMENTS:
        errors.append(
            "deep_audit_observations are permitted only when source_coverage_mode "
            "is named_theoretical_statements; deep all-prose review must audit "
            "the claim as an ordinary in-scope item"
        )

    raw_items = map_payload.get("items")
    if not isinstance(raw_items, dict):
        return errors + [
            "deep_audit_observations require source-map items for semantic link validation"
        ]

    linked_ids: set[str] = set()
    for raw_key, raw_item in raw_items.items():
        if not isinstance(raw_item, dict):
            continue
        raw_ids = raw_item.get(DEEP_AUDIT_OBSERVATION_LINK_FIELD)
        if raw_ids is None:
            continue
        label = f"items.{str(raw_key)}.{DEEP_AUDIT_OBSERVATION_LINK_FIELD}"
        if (
            not isinstance(raw_ids, list)
            or not raw_ids
            or any(
                not isinstance(value, str) or not value.strip() for value in raw_ids
            )
            or len({value.strip() for value in raw_ids}) != len(raw_ids)
        ):
            errors.append(f"{label} must be a nonempty list of unique observation ids")
            continue

        source_kind = str(raw_item.get("source_kind") or "").strip().lower()
        if source_kind not in DEEP_ONLY_SOURCE_KINDS:
            errors.append(
                f"{label} must use a deep-only source_kind; it is not a "
                "normal-scope exemption for a named theory presentation"
            )
        if source_item_in_coverage_scope(
            raw_item,
            NAMED_THEORETICAL_STATEMENTS,
            declared_environment_kinds=source_named_result_environment_kinds_from_map(
                map_payload
            ),
        ):
            errors.append(
                f"{label} links a source presentation selected by the normal "
                "named-theory scope and therefore cannot be a deep observation"
            )
        if not concrete_source_locator(raw_item.get("source_location")):
            errors.append(f"{label} requires the linked row to have a concrete source_location")
        anchors = raw_item.get("source_anchor_evidence")
        if not isinstance(anchors, list) or not anchors:
            errors.append(
                f"{label} requires the linked row to retain byte-pinned "
                "source_anchor_evidence"
            )

        if raw_item.get("corrected_target") is not None or (
            str(raw_item.get("coverage_status") or "").strip().lower()
            == CORRECTED_SOURCE_STATEMENT_STATUS
        ):
            errors.append(
                f"{label} cannot combine a deep observation with a corrected source target"
            )
        if raw_item.get(USER_APPROVED_SCOPE_EXCLUSION) is not None:
            errors.append(
                f"{label} cannot combine a deep observation with a user scope exclusion"
            )
        routed_defects = raw_item.get("source_defect_ids")
        if isinstance(routed_defects, list):
            has_routed_defect = any(str(value).strip() for value in routed_defects)
        else:
            has_routed_defect = bool(str(routed_defects or "").strip())
        if has_routed_defect:
            errors.append(
                f"{label} cannot route a source-proof defect through source_defect_ids; "
                "a deep observation is not a defect resolution"
            )

        for raw_id in raw_ids:
            observation_id = raw_id.strip()
            if observation_id not in observation_ids:
                errors.append(
                    f"{label} cites unknown deep audit observation `{observation_id}`"
                )
                continue
            linked_ids.add(observation_id)

    unlinked_ids = sorted(observation_ids - linked_ids)
    if unlinked_ids:
        errors.append(
            "deep_audit_observations must each link to at least one semantically "
            "outside-normal-scope source row: "
            + ", ".join(unlinked_ids)
        )
    return errors


def source_proof_fidelity_requirement_reasons(
    folder: Path,
    status: str,
    status_payload: dict[str, Any],
    *,
    context: EvidenceRunContext | None = None,
) -> tuple[str, ...]:
    """Return semantic triggers that make a full-closeout ledger mandatory.

    An uncurated historical zero-defect ledger may remain archival without a
    status configuration.  A separate migration gate upgrades that requirement
    when a full-closeout paper has both a source-first curated inventory and a
    canonical ledger.  Once the current surface uses explicit source routes,
    links a source-map item to a source defect, or has a canonical ledger with
    defects, or records a rigorously linked deep prose finding, omitting the
    configuration would hide current source-audit material. These are
    content-level checks and never inspect Lean declaration names.
    """

    if status not in FULL_CLOSEOUT_STATUSES:
        return ()
    reasons: list[str] = []
    if explicit_source_routes_enabled(status_payload):
        reasons.append("the v10 review surface requires explicit source routes")
    if canonical_source_map_has_source_defect_links(folder, context=context):
        reasons.append("the canonical source map links one or more source defects")
    if canonical_source_proof_ledger_has_defects(folder, context=context):
        reasons.append("the canonical source-proof ledger records one or more defects")
    if canonical_source_proof_ledger_has_deep_observations(
        folder, context=context
    ):
        reasons.append(
            "the canonical source-proof ledger records one or more deep audit observations"
        )
    return tuple(reasons)


def source_record_review_sidecar_path(
    folder: Path,
    status_payload: dict[str, Any],
    *,
    config_field: str,
    default_basename: str,
) -> tuple[Path | None, str]:
    """Resolve a configured source-record sidecar inside its paper folder.

    The repository closeout supports paths configured under
    ``llm_source_record_review``.  The fast evidence gate must inspect the
    same artifacts rather than silently consulting a legacy canonical copy.
    Missing configuration deliberately retains the canonical-sidecar default.
    """

    review_surface = status_payload.get("review_surface")
    source_record_review = (
        review_surface.get("llm_source_record_review")
        if isinstance(review_surface, dict)
        else None
    )
    raw_path = (
        source_record_review.get(config_field)
        if isinstance(source_record_review, dict)
        else None
    )
    if not isinstance(raw_path, str) or not raw_path.strip():
        return canonical_sidecar(folder, default_basename), ""

    relative_path = Path(raw_path.strip())
    if relative_path.is_absolute():
        return None, f"llm_source_record_review.{config_field} must be relative"
    try:
        # Status paths are repository-relative, matching audit_repository's
        # source-record helper.  They still must remain inside this paper.
        candidate = (ROOT / relative_path).resolve()
        candidate.relative_to(folder.resolve())
    except (OSError, RuntimeError, ValueError):
        return (
            None,
            f"llm_source_record_review.{config_field} escapes the paper folder",
        )
    return candidate, ""


def source_record_administrative_projection_rebind_context(
    folder: Path,
    status_payload: dict[str, Any],
    *,
    audit_path: Path,
    audit_payload: dict[str, Any],
    statement_map_path: Path,
    statement_map: dict[str, Any] | None,
    receipt_bytes_override: bytes | None | object = _UNSET,
    raw_audit_bytes_override: bytes | None | object = _UNSET,
    statement_map_bytes_override: bytes | None | object = _UNSET,
) -> tuple[Any | None, Path | None, str]:
    """Load one exact direct-source-status transport rebind, if configured.

    A missing optional receipt leaves ordinary current validation unchanged. An
    existing receipt must reconstruct from the exact raw-audit bytes and exact
    current source-map bytes; it is never a loose permission to reinterpret a
    legacy semantic digest.
    """

    rebind_path, path_error = source_record_review_sidecar_path(
        folder,
        status_payload,
        config_field="source_record_administrative_projection_rebind_file",
        default_basename=SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME,
    )
    if path_error:
        return None, rebind_path, path_error
    assert rebind_path is not None
    kwargs: dict[str, object] = {}
    if receipt_bytes_override is not _UNSET:
        kwargs = {
            "receipt_bytes_override": receipt_bytes_override,
            "raw_audit_bytes_override": raw_audit_bytes_override,
            "statement_map_bytes_override": statement_map_bytes_override,
        }
    return load_administrative_projection_rebind_context(
        paper=folder.name,
        paper_dir=folder,
        raw_audit_path=audit_path,
        raw_audit=audit_payload,
        statement_map_path=statement_map_path,
        statement_map=statement_map,
        receipt_path=rebind_path,
        **kwargs,
    )


def source_proof_fidelity_ledger_path(
    folder: Path, status_payload: dict[str, Any]
) -> tuple[Path | None, str]:
    """Resolve a configured proof-fidelity ledger without allowing path escape."""

    config = source_proof_fidelity_config(status_payload)
    if config is None:
        return None, ""
    raw_path = config.get("ledger_file")
    if not isinstance(raw_path, str) or not raw_path.strip():
        return None, "source_proof_fidelity_review.ledger_file is missing"
    relative_path = Path(raw_path.strip())
    if relative_path.is_absolute():
        return None, "source_proof_fidelity_review.ledger_file must be relative"
    anchor = ROOT if relative_path.parts[:1] == ("papers",) else folder
    try:
        candidate = (anchor / relative_path).resolve()
        candidate.relative_to(folder.resolve())
    except (OSError, RuntimeError, ValueError):
        return None, "source_proof_fidelity_review.ledger_file escapes the paper folder"
    return candidate, ""


def approved_source_convention_formalized_note_error(
    folder: Path,
    item: dict[str, Any],
    *,
    context: EvidenceRunContext | None = None,
) -> str:
    """Validate a note-only visible-premise difference without name matching.

    A ``formalized_note`` may document an explicit source-model convention, but
    it must never turn a weakened conclusion or an unreviewed extra premise
    into full-closeout credit.  This check follows the source item's current
    semantic digest and the current proof-fidelity convention receipts.  It
    intentionally does not infer correspondence from a Lean declaration, row,
    binder, or source-map key.
    """

    if (
        str(item.get("source_target_disposition") or "").strip()
        != "approved_source_convention"
    ):
        return (
            "formalized-note visible-premise boundary must use "
            "source_target_disposition approved_source_convention"
        )

    source_semantic_sha256 = str(
        item.get("source_statement_semantic_sha256") or ""
    ).strip().lower()
    if not SHA256_RE.fullmatch(source_semantic_sha256):
        return (
            "formalized-note source_statement_semantic_sha256 must be a current "
            "64-character source semantic digest"
        )
    source_statement_locator = str(
        item.get("source_statement_locator") or ""
    ).strip()
    if not source_statement_locator:
        return "formalized-note source_statement_locator is missing"

    statement_map_path = transaction_sidecar(
        folder, "paper_statement_map.json", context
    )
    statement_map = transaction_json(statement_map_path, context)
    if not isinstance(statement_map, dict):
        return "formalized-note cannot load the canonical paper_statement_map.json"
    source_items = statement_map.get("items")
    if not isinstance(source_items, dict):
        return "formalized-note source map has no source-item dictionary"
    candidates = [
        source_item
        for source_item in source_items.values()
        if isinstance(source_item, dict)
        and source_item_coverage_sha256(source_item, "") == source_semantic_sha256
    ]
    if len(candidates) != 1:
        return (
            "formalized-note source semantic digest must identify exactly one "
            "current in-scope source statement"
        )
    current_source_item = candidates[0]
    if str(current_source_item.get("source_location") or "").strip() != source_statement_locator:
        return (
            "formalized-note source_statement_locator does not match the current "
            "source statement selected by its semantic digest"
        )

    raw_ids = item.get("model_convention_ids")
    if not isinstance(raw_ids, list) or not raw_ids:
        return "formalized-note model_convention_ids must be a nonempty list"
    convention_ids = [
        value.strip() for value in raw_ids if isinstance(value, str) and value.strip()
    ]
    if len(convention_ids) != len(raw_ids) or len(convention_ids) != len(
        set(convention_ids)
    ):
        return "formalized-note model_convention_ids must contain unique nonempty ids"
    raw_digests = item.get("model_convention_sha256_by_id")
    raw_locators = item.get("model_convention_source_locators")
    if not isinstance(raw_digests, dict) or not isinstance(raw_locators, dict):
        return (
            "formalized-note must pin model_convention_sha256_by_id and "
            "model_convention_source_locators"
        )
    normalized_digests = {
        str(key).strip(): str(value).strip().lower()
        for key, value in raw_digests.items()
        if str(key).strip()
    }
    normalized_locators = {
        str(key).strip(): str(value).strip()
        for key, value in raw_locators.items()
        if str(key).strip()
    }
    if set(normalized_digests) != set(convention_ids):
        return (
            "formalized-note model_convention_sha256_by_id must cover exactly "
            "model_convention_ids"
        )
    if set(normalized_locators) != set(convention_ids):
        return (
            "formalized-note model_convention_source_locators must cover exactly "
            "model_convention_ids"
        )

    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    ledger_path, ledger_path_error = source_proof_fidelity_ledger_path(
        folder, status_payload
    )
    if ledger_path_error:
        return "formalized-note cannot resolve source-proof fidelity ledger: " + ledger_path_error
    ledger = (
        transaction_json(ledger_path, context)
        if ledger_path is not None
        else None
    )
    if not isinstance(ledger, dict):
        return "formalized-note cannot load the configured source-proof fidelity ledger"
    raw_conventions = ledger.get("model_conventions")
    if not isinstance(raw_conventions, list):
        return "formalized-note source-proof ledger has no model_conventions list"
    conventions = {
        str(convention.get("id") or "").strip(): convention
        for convention in raw_conventions
        if isinstance(convention, dict) and str(convention.get("id") or "").strip()
    }
    for convention_id in convention_ids:
        convention = conventions.get(convention_id)
        if convention is None:
            return (
                "formalized-note cites source-proof model convention absent from "
                "the current ledger: " + convention_id
            )
        if (
            normalized_digests.get(convention_id)
            != model_convention_semantic_digest(convention)
        ):
            return (
                "formalized-note model-convention digest is stale for "
                + convention_id
            )
        if normalized_locators.get(convention_id) != str(
            convention.get("source_locator") or ""
        ).strip():
            return (
                "formalized-note model-convention locator is stale for "
                + convention_id
            )
        if any(
            not str(convention.get(field) or "").strip()
            for field in SOURCE_PROOF_MODEL_CONVENTION_REQUIRED_FIELDS
        ):
            return (
                "formalized-note cites incomplete source-proof model convention "
                + convention_id
            )

    # Statement-match notes may waive only extra *premises*.  The structured
    # ledger must still show exact source/Lean conclusions and inputs, and all
    # matched atoms must be equivalent rather than merely one-way implications.
    if "judgment" in item:
        if str(item.get("judgment") or "").strip().lower() != "mismatch":
            return "formalized-note statement row must retain its mismatch judgment"
        if str(item.get("resolution") or "").strip().lower() not in {
            "conditional_boundary",
            "visible_premise_boundary",
        }:
            return (
                "formalized-note statement row must retain a visible-premise "
                "boundary resolution"
            )
        if str(item.get("obligation_ledger_error") or "").strip():
            return "formalized-note statement row has an invalid obligation ledger"
        for field in (
            "unmatched_source_conclusions",
            "unmatched_source_inputs",
            "unmatched_lean_conclusions",
        ):
            if item.get(field) != []:
                return (
                    "formalized-note statement row has a non-premise semantic gap "
                    "in " + field
                )
        unjustified = item.get("unjustified_lean_inputs")
        if not isinstance(unjustified, list) or not unjustified:
            return (
                "formalized-note statement row must expose at least one extra "
                "Lean premise"
            )
        alignment = item.get("obligation_alignment")
        if not isinstance(alignment, list) or not alignment or any(
            not isinstance(entry, dict)
            or str(entry.get("relation") or "").strip().lower() != "equivalent"
            for entry in alignment
        ):
            return (
                "formalized-note statement row must retain only equivalent "
                "source/Lean obligation alignments"
            )

    return ""


def canonical_source_first_inventory_present(
    folder: Path,
    *,
    context: EvidenceRunContext | None = None,
) -> bool:
    """Return whether a paper has declared a canonical source-first inventory.

    ``source_curated`` is the inventory's explicit source-facing schema marker.
    We deliberately do not infer this from map keys, source wording, or Lean
    declaration names.  A malformed nonempty inventory still triggers the
    migration gate: separate map validators report its detailed schema error,
    but bad shape must not make a legacy closeout optional.
    """

    path = transaction_sidecar(folder, "paper_statement_map.json", context)
    payload = transaction_json(path, context)
    if not isinstance(payload, dict) or payload.get("source_curated") is not True:
        return False
    raw_items = payload.get("items")
    return isinstance(raw_items, (dict, list)) and bool(raw_items)


def canonical_source_proof_ledger_present(
    folder: Path,
    *,
    context: EvidenceRunContext | None = None,
) -> bool:
    """Return whether the canonical ledger artifact exists, even if malformed."""

    path = transaction_sidecar(folder, "source_proof_fidelity.json", context)
    if context is None:
        return path.is_file()
    snapshot = context.json_snapshot(path)
    return snapshot is not None and snapshot.sha256 is not None


def configured_review_artifact_path_error(
    folder: Path,
    *,
    lane: str,
    field: str,
    value: object,
) -> str:
    """Validate a configured audit artifact path without requiring it to exist.

    Artifact freshness and payload schema have dedicated checks elsewhere.  The
    migration gate only establishes that a closeout is actually wired to the
    current lane, and rejects an empty or escaping pointer that could make a
    later audit silently fall back to unrelated sidecars.
    """

    if not isinstance(value, str) or not value.strip():
        return f"review_surface.{lane}.{field} must be a nonempty artifact path"
    relative_path = Path(value.strip())
    if relative_path.is_absolute():
        return f"review_surface.{lane}.{field} must be relative"
    anchor = ROOT if relative_path.parts[:1] == ("papers",) else folder
    try:
        candidate = (anchor / relative_path).resolve()
        candidate.relative_to(folder.resolve())
    except (OSError, RuntimeError, ValueError):
        return f"review_surface.{lane}.{field} escapes the paper folder"
    return ""


def current_v10_semantic_source_lane_errors(
    folder: Path,
    status_payload: dict[str, Any],
    *,
    context: EvidenceRunContext | None = None,
) -> list[str]:
    """Return missing configuration for the current semantic/source lanes.

    This is intentionally a configuration gate, not a replacement for the
    existing sidecar freshness, source-map, or source-proof-defect validators.
    A successful result means the full closeout is wired to the current v10
    source-route statement lane, source-first coverage lane, recursive source
    record lane, expanded semantic-model lane, and canonical fidelity ledger.
    All inputs are status schema fields and artifact locations.
    """

    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return ["status.json has no review_surface object"]

    errors: list[str] = []

    statement_review = review_surface.get("llm_statement_review")
    if not isinstance(statement_review, dict):
        errors.append("review_surface.llm_statement_review must be an object")
    else:
        if statement_review.get("require_explicit_source_routes") is not True:
            errors.append(
                "review_surface.llm_statement_review.require_explicit_source_routes "
                "must be true"
            )
        atom_requirement = statement_review.get("require_source_claim_atoms")
        if atom_requirement is not None and not isinstance(atom_requirement, bool):
            errors.append(
                "review_surface.llm_statement_review.require_source_claim_atoms "
                "must be Boolean when configured"
            )
        source_map_path = transaction_sidecar(
            folder, "paper_statement_map.json", context
        )
        source_map = transaction_json(source_map_path, context)
        atom_schema = (
            source_map.get(SOURCE_CLAIM_ATOMS_SCHEMA_KEY)
            if isinstance(source_map, dict)
            else None
        )
        if atom_schema is not None and atom_requirement is not True:
            errors.append(
                "review_surface.llm_statement_review.require_source_claim_atoms "
                "must be true when the source map opts into source_claim_atoms"
            )
        if atom_requirement is True and not schema_version_is_exact(
            atom_schema, SOURCE_CLAIM_ATOMS_SCHEMA
        ):
            errors.append(
                "review_surface.llm_statement_review.require_source_claim_atoms "
                f"requires top-level {SOURCE_CLAIM_ATOMS_SCHEMA_KEY}: "
                f"{SOURCE_CLAIM_ATOMS_SCHEMA}"
            )
        for field in V10_STATEMENT_REVIEW_ARTIFACT_FIELDS:
            error = configured_review_artifact_path_error(
                folder,
                lane="llm_statement_review",
                field=field,
                value=statement_review.get(field),
            )
            if error:
                errors.append(error)

    coverage_review = review_surface.get("llm_paper_coverage_review")
    if not isinstance(coverage_review, dict):
        errors.append("review_surface.llm_paper_coverage_review must be an object")
    else:
        for field in V10_PAPER_COVERAGE_ARTIFACT_FIELDS:
            error = configured_review_artifact_path_error(
                folder,
                lane="llm_paper_coverage_review",
                field=field,
                value=coverage_review.get(field),
            )
            if error:
                errors.append(error)

        if (
            canonical_source_map_has_source_defect_links(folder, context=context)
            or canonical_source_proof_ledger_has_defects(folder, context=context)
        ):
            error = configured_review_artifact_path_error(
                folder,
                lane="llm_paper_coverage_review",
                field="defect_support_judgment_file",
                value=coverage_review.get("defect_support_judgment_file"),
            )
            if error:
                errors.append(error)

    source_record_review = review_surface.get("llm_source_record_review")
    if not isinstance(source_record_review, dict):
        errors.append("review_surface.llm_source_record_review must be an object")
    else:
        for field in V10_SOURCE_RECORD_ARTIFACT_FIELDS:
            error = configured_review_artifact_path_error(
                folder,
                lane="llm_source_record_review",
                field=field,
                value=source_record_review.get(field),
            )
            if error:
                errors.append(error)

    semantic_model_review = review_surface.get("semantic_model_review")
    if not isinstance(semantic_model_review, dict):
        errors.append("review_surface.semantic_model_review must be an object")
    else:
        dimensions = semantic_model_review.get("required_dimensions")
        normalized_dimensions = (
            [str(dimension).strip() for dimension in dimensions]
            if isinstance(dimensions, list)
            else []
        )
        if (
            not schema_version_is_exact(
                semantic_model_review.get("schema"), SEMANTIC_MODEL_REVIEW_SCHEMA
            )
            or len(normalized_dimensions) != len(set(normalized_dimensions))
            or set(normalized_dimensions) != SEMANTIC_MODEL_REVIEW_DIMENSIONS
        ):
            errors.append(
                "review_surface.semantic_model_review must use schema 2 with every "
                "expanded-semantic dimension exactly once"
            )

    fidelity_config = source_proof_fidelity_config(status_payload)
    if fidelity_config is None:
        errors.append("review_surface.source_proof_fidelity_review must be an object")
    else:
        ledger_path, ledger_error = source_proof_fidelity_ledger_path(
            folder, status_payload
        )
        if ledger_error:
            errors.append(ledger_error)
        elif ledger_path is not None:
            canonical_ledger_path = transaction_sidecar(
                folder, "source_proof_fidelity.json", context
            )
            if ledger_path.resolve() != canonical_ledger_path.resolve():
                errors.append(
                    "review_surface.source_proof_fidelity_review.ledger_file must "
                    "resolve to the canonical source-proof fidelity ledger"
                )

    return errors


def v10_migration_pending_findings(
    folder: Path,
    status: str,
    status_payload: dict[str, Any],
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Fail closed on a legacy review surface after source-first closeout work.

    A formalized paper that has both source-first inventory metadata and a
    canonical fidelity ledger has enough source-facing audit infrastructure
    that omitting the current v10 lanes is dangerous.  This is a migration
    marker, rather than a declaration-name heuristic: it inspects only the
    inventory marker, canonical ledger artifact, and status/artifact schemas.
    Existing validators still check the referenced artifacts' exact contents.
    """

    if (
        status not in FULL_CLOSEOUT_STATUSES
        or not canonical_source_first_inventory_present(folder, context=context)
        or not canonical_source_proof_ledger_present(folder, context=context)
    ):
        return []
    errors = current_v10_semantic_source_lane_errors(
        folder, status_payload, context=context
    )
    if not errors:
        return []
    return [
        Finding(
            "ERROR",
            folder.name,
            rel(folder / "status.json"),
            "v10-migration-pending: full-closeout source-first inventory plus "
            "canonical source-proof fidelity ledger lacks current semantic/source "
            "review-lane configuration: "
            + "; ".join(errors),
        )
    ]


def meaningful_semantic_text(value: object) -> bool:
    """Require source-facing mathematical text rather than a blank/name-only token."""

    if not isinstance(value, str):
        return False
    text = value.strip()
    return len(text) >= 8 and not PLACEHOLDER_SOURCE_RE.search(text)


def concrete_source_locator(value: object) -> bool:
    """Require a source anchor that can be checked without a Lean identifier."""

    return isinstance(value, str) and bool(
        meaningful_semantic_text(value) and SOURCE_PROOF_LOCATOR_RE.search(value)
    )


def user_approved_scope_exclusion_errors(
    folder: Path,
    raw_approval: object,
    *,
    expected_source_locator: object | None = None,
    require_source_bytes: bool = True,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[str]:
    """Validate an explicit user exclusion against a byte-pinned source slice.

    This is a scope record, never a proof or a claim that the source material is
    non-mathematical.  It is intentionally expressed only in source-facing
    fields: an explicit user reference, date, reason, source locator, evidence,
    and the digest of that exact source slice.  No Lean declaration or map key
    is used as evidence.
    """

    if not isinstance(raw_approval, dict):
        return ["user_approved_scope_exclusion must be an object"]
    errors: list[str] = []

    def add(message: str) -> None:
        errors.append(f"user_approved_scope_exclusion.{message}")

    if not schema_version_is_exact(
        raw_approval.get("schema"), USER_APPROVED_SCOPE_EXCLUSION_SCHEMA
    ):
        add(f"schema must be {USER_APPROVED_SCOPE_EXCLUSION_SCHEMA}")
    if (
        str(raw_approval.get("approval_kind") or "").strip()
        != USER_APPROVED_SCOPE_EXCLUSION_APPROVAL_KIND
    ):
        add(
            "approval_kind must be "
            f"`{USER_APPROVED_SCOPE_EXCLUSION_APPROVAL_KIND}`"
        )
    approval_reference = str(raw_approval.get("approval_reference") or "").strip()
    if not meaningful_semantic_text(approval_reference):
        add("approval_reference must identify the explicit user instruction")
    approved_at = str(raw_approval.get("approved_at") or "").strip()
    if not USER_APPROVED_SCOPE_EXCLUSION_TIMESTAMP_RE.fullmatch(approved_at):
        add("approved_at must be an ISO-like date or timestamp")
    for field in ("reason", "source_evidence"):
        if not meaningful_semantic_text(raw_approval.get(field)):
            add(f"{field} must contain source-facing scope text")

    source_locator = str(raw_approval.get("source_locator") or "").strip()
    if not concrete_source_locator(source_locator):
        add("source_locator must be a concrete source anchor")
        return errors
    if expected_source_locator is not None and source_locator != str(
        expected_source_locator or ""
    ).strip():
        add("source_locator must exactly match the defect's source_locator")
    matches = list(SOURCE_FILE_LINE_RE.finditer(source_locator))
    if len(matches) != 1:
        add("source_locator must contain exactly one file:line anchor")
        return errors
    quote_digest = str(
        raw_approval.get("source_anchor_quote_sha256") or ""
    ).strip().lower()
    if not SHA256_RE.fullmatch(quote_digest):
        add("source_anchor_quote_sha256 must be a SHA-256 digest")
    for error in source_file_line_anchor_errors(
        folder,
        source_locator,
        require_source_bytes=require_source_bytes,
        file_bytes_override=file_bytes_override,
    ):
        add(f"source_locator {error}")
    match = matches[0]
    path, path_error = resolve_paper_source_path(folder, match.group("path"))
    if path is None:
        add(f"source_locator {path_error}")
        return errors
    source_bytes_missing = (
        file_bytes_override is not None
        and path in file_bytes_override
        and file_bytes_override[path] is None
    ) or (file_bytes_override is None and not path.exists())
    if not require_source_bytes and source_bytes_missing:
        return errors
    try:
        source_text = normalized_source_text(
            _exact_file_bytes(path, file_bytes_override)
        )
    except (OSError, RuntimeError, UnicodeDecodeError) as error:
        add(f"source_locator source text cannot be read: {error}")
        return errors
    quote = normalized_source_line_excerpt(
        normalized_source_lines(source_text),
        int(match.group("start")),
        int(match.group("end") or match.group("start")),
    )
    if quote is None:
        # The source_file_line_anchor_errors call above should already have a
        # precise range error; preserve a fail-closed digest diagnosis here.
        add("source_locator cannot produce an exact source quote")
        return errors
    if SHA256_RE.fullmatch(quote_digest) and quote_digest != hashlib.sha256(
        quote.encode("utf-8")
    ).hexdigest():
        add("source_anchor_quote_sha256 must match the exact source quote")
    return errors


def source_file_line_anchor_errors(
    folder: Path,
    value: object,
    *,
    require_source_bytes: bool = True,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[str]:
    """Check file-and-line anchors against the locally pinned source cache.

    The semantic ledger may also use page/theorem references, especially for a
    PDF-only source.  Whenever it supplies a concrete `file:line` anchor,
    however, that anchor must resolve inside the paper folder and refer to an
    existing line range.  This prevents an audit from becoming name-based prose
    that cites a nonexistent source location.
    """

    if not isinstance(value, str):
        return []
    errors: list[str] = []
    for match in SOURCE_FILE_LINE_RE.finditer(value):
        raw_path = Path(match.group("path"))
        try:
            candidate = (folder / raw_path).resolve()
            candidate.relative_to(folder.resolve())
        except (OSError, RuntimeError, ValueError):
            errors.append(f"source anchor `{raw_path}` escapes the paper folder")
            continue
        if file_bytes_override is not None and candidate not in file_bytes_override:
            errors.append(f"frozen input bundle omits source anchor `{raw_path}`")
            continue
        if (
            file_bytes_override is not None
            and file_bytes_override[candidate] is None
        ) or (file_bytes_override is None and not candidate.is_file()):
            if require_source_bytes:
                errors.append(
                    f"source anchor `{raw_path}` does not name a local source file"
                )
            continue
        if candidate.suffix.lower() not in TEXT_SOURCE_SUFFIXES:
            continue
        start = int(match.group("start"))
        end = int(match.group("end") or start)
        try:
            line_count = len(
                _exact_file_bytes(candidate, file_bytes_override)
                .decode("utf-8")
                .splitlines()
            )
        except (OSError, RuntimeError, UnicodeDecodeError):
            errors.append(f"source anchor `{raw_path}` could not be read")
            continue
        if start < 1 or end < start or end > line_count:
            errors.append(
                f"source anchor `{raw_path}:{start}-{end}` is outside its {line_count}-line source"
            )
    return errors


def canonical_artifact_source_span_errors(
    folder: Path,
    value: object,
    *,
    source_artifact_path: object,
) -> list[str]:
    """Require file-and-line spans to identify one pinned canonical artifact.

    Ordinary fidelity defects can cite a supplementary local transcript. A
    deep prose observation, by contrast, exists only to preserve an exact
    out-of-scope source finding, so its evidence must be a concrete span of the
    ledger's own byte-pinned canonical artifact. This is source-byte identity,
    not a map key or Lean declaration heuristic.
    """

    if not isinstance(value, str):
        return ["must be a source locator string"]
    expected_path, expected_error = resolve_paper_source_path(
        folder, source_artifact_path
    )
    if expected_path is None:
        return [
            "cannot resolve the ledger's canonical source artifact: "
            + expected_error
        ]
    matches = list(SOURCE_FILE_LINE_RE.finditer(value))
    if not matches:
        return [
            "must include a file:line span into the ledger's canonical source artifact"
        ]
    errors: list[str] = []
    for match in matches:
        raw_path = match.group("path")
        candidate, path_error = resolve_paper_source_path(folder, raw_path)
        if candidate is None:
            errors.append(f"source span `{raw_path}` {path_error}")
        elif candidate != expected_path:
            errors.append(
                f"source span `{raw_path}` does not identify the ledger's canonical "
                "source artifact"
            )
    return errors


def corrected_target_record_digest(raw: object) -> str:
    """Return the stable digest used by local corrected-target routes.

    Keep this deliberately independent of source-map keys and Lean names.  The
    record itself contains the archival baseline, corrected mathematical text,
    governing defect ids, and approval pin that a reviewer inspected.
    """

    payload = dict(raw) if isinstance(raw, dict) else raw
    if isinstance(payload, dict):
        payload.pop("corrected_target_sha256", None)
    return hashlib.sha256(
        json.dumps(payload, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode(
            "utf-8"
        )
    ).hexdigest()


def corrected_target_primary_declaration(item: object) -> str | None:
    """Return the unique complete endpoint allowed to carry a repaired target."""

    if not isinstance(item, dict):
        return None
    declarations = item.get("lean_declarations")
    if not isinstance(declarations, list) or len(declarations) != 1:
        return None
    declaration = declarations[0]
    if not isinstance(declaration, str) or not declaration.strip():
        return None
    return declaration.strip()


def corrected_target_coverage_rows_match_primary(
    primary_declaration: str,
    review_rows: list[str],
    map_items: object,
    paper_name: str,
) -> bool:
    """Accept the configured endpoint or its unique dashboard-local row name.

    Source maps retain fully qualified Lean declarations, while the dashboard
    records the final PaperInterface declaration component as its review-row
    navigation name. This is an identity translation only: a short name is
    accepted solely for the configured paper's PaperInterface route, and only
    when no other configured direct route has that component. The downstream
    dashboard still checks the current elaborated signature and semantic source
    route, so this helper never grants coverage by a declaration-name match.
    """

    if review_rows == [primary_declaration]:
        return True
    if len(review_rows) != 1:
        return False

    prefix = f"{paper_name}.PaperInterface."
    if not primary_declaration.startswith(prefix):
        return False
    short_name = primary_declaration.rsplit(".", maxsplit=1)[-1]
    if not short_name or review_rows != [short_name]:
        return False
    if not isinstance(map_items, dict):
        return False

    configured_routes: set[str] = set()
    for raw_item in map_items.values():
        if not isinstance(raw_item, dict):
            continue
        declarations = raw_item.get("lean_declarations")
        if not isinstance(declarations, list):
            continue
        for raw_declaration in declarations:
            if not isinstance(raw_declaration, str):
                continue
            declaration = raw_declaration.strip()
            if (
                declaration.startswith(prefix)
                and declaration.rsplit(".", maxsplit=1)[-1] == short_name
            ):
                configured_routes.add(declaration)
    return configured_routes == {primary_declaration}


def corrected_source_statement_map_findings(
    folder: Path,
    status: str,
    payload: dict[str, Any],
    *,
    context: EvidenceRunContext | None = None,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[Finding]:
    """Validate local, explicit replacements for false source statements.

    An archival statement remains the map item's ``statement``.  A separate
    ``corrected_target`` is permitted only through this narrow record, never by
    relabelling a false theorem as ordinary ``covered``.  The validation uses
    source text, hashes, and the source-proof ledger; Lean declaration names
    play no role in deciding whether a correction is authorized.
    """

    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        return []
    presentation_aliases, _presentation_alias_errors = source_presentation_aliases(
        raw_items
    )
    has_corrected_rows = any(
        str(key).strip() not in presentation_aliases
        and isinstance(item, dict)
        and str(item.get("coverage_status") or "").strip().lower()
        == CORRECTED_SOURCE_STATEMENT_STATUS
        for key, item in raw_items.items()
    )
    if not has_corrected_rows and not any(
        str(key).strip() not in presentation_aliases
        and isinstance(item, dict)
        and "corrected_target" in item
        for key, item in raw_items.items()
    ):
        return []

    if file_bytes_override is None and context is not None:
        file_bytes_override = context.file_bytes_override()
    severity = finding_severity(status)
    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    findings: list[Finding] = []

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(map_path), message))

    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    ledger_path, ledger_path_error = source_proof_fidelity_ledger_path(
        folder, status_payload
    )
    ledger = (
        transaction_json(ledger_path, context)
        if ledger_path is not None
        else None
    )
    defects_by_id: dict[str, dict[str, Any]] = {}
    if ledger_path_error:
        add(ledger_path_error)
    elif not isinstance(ledger, dict):
        add("corrected source targets require a readable configured source-proof fidelity ledger")
    else:
        raw_defects = ledger.get("defects")
        if isinstance(raw_defects, list):
            for defect in raw_defects:
                if not isinstance(defect, dict):
                    continue
                defect_id = str(defect.get("id") or "").strip()
                if defect_id:
                    defects_by_id[defect_id] = defect

    governed_defect_ids: set[str] = set()
    for raw_key, raw_item in raw_items.items():
        key = str(raw_key or "").strip() or "<unnamed>"
        if not isinstance(raw_item, dict):
            continue
        # A repeated presentation remains source-visible, including any
        # archival correction context, but its canonical item owns the one
        # corrected-target endpoint and coverage verdict.  Requiring a second
        # endpoint here would reintroduce the duplicate route the alias schema
        # prohibits.
        if key in presentation_aliases:
            continue
        corrected_status = (
            str(raw_item.get("coverage_status") or "").strip().lower()
            == CORRECTED_SOURCE_STATEMENT_STATUS
        )
        target = raw_item.get("corrected_target")
        if corrected_status and not isinstance(target, dict):
            add(f"items.{key} corrected_source_statement requires a structured corrected_target")
            continue
        if not corrected_status and target is not None:
            add(f"items.{key} has corrected_target without coverage_status corrected_source_statement")
            continue
        if not corrected_status:
            continue
        assert isinstance(target, dict)
        prefix = f"items.{key}.corrected_target"
        if corrected_target_primary_declaration(raw_item) is None:
            add(
                f"items.{key}.lean_declarations must be an exact one-element string "
                "list naming the complete corrected-target endpoint"
            )
        raw_proof_declarations = raw_item.get("proof_lean_declarations")
        if (
            isinstance(raw_proof_declarations, (list, tuple, set))
            and raw_proof_declarations
        ) or (
            not isinstance(raw_proof_declarations, (list, tuple, set, type(None)))
            and str(raw_proof_declarations).strip()
        ):
            add(
                f"items.{key}.proof_lean_declarations is prohibited for "
                "corrected_source_statement; move helper proofs to "
                "support_lean_declarations"
            )
        if not schema_version_is_exact(
            target.get("schema"), CORRECTED_TARGET_SCHEMA
        ):
            add(f"{prefix}.schema must be {CORRECTED_TARGET_SCHEMA}")
        archival_statement = str(raw_item.get("statement") or "").strip()
        target_statement = str(target.get("statement") or "").strip()
        if not meaningful_semantic_text(archival_statement):
            add(f"items.{key}.statement must retain a nonempty archival source statement")
        if not meaningful_semantic_text(target_statement):
            add(f"{prefix}.statement must state the corrected mathematical target")
        target_digest = hashlib.sha256(
            re.sub(r"\s+", " ", target_statement).strip().encode("utf-8")
        ).hexdigest()
        if archival_statement and target_statement and re.sub(r"\s+", " ", archival_statement).strip() == re.sub(r"\s+", " ", target_statement).strip():
            add(f"{prefix}.statement must differ from the archival source statement")
        if target.get("archival_equivalence_claimed") is not False:
            add(f"{prefix}.archival_equivalence_claimed must be false")

        raw_governing = target.get("governing_defect_ids")
        if (
            not isinstance(raw_governing, list)
            or not raw_governing
            or any(not isinstance(value, str) or not value.strip() for value in raw_governing)
            or len({value.strip() for value in raw_governing}) != len(raw_governing)
        ):
            add(f"{prefix}.governing_defect_ids must be a nonempty unique string list")
            governing_ids: set[str] = set()
        else:
            governing_ids = {value.strip() for value in raw_governing}
            governed_defect_ids.update(governing_ids)
        raw_routed = raw_item.get("source_defect_ids")
        routed_ids = {
            value.strip()
            for value in (raw_routed if isinstance(raw_routed, list) else [])
            if isinstance(value, str) and value.strip()
        }
        if governing_ids and not governing_ids.issubset(routed_ids):
            add(f"{prefix}.governing_defect_ids must be a subset of source_defect_ids")
        for defect_id in sorted(governing_ids):
            defect = defects_by_id.get(defect_id)
            if defect is None:
                add(f"{prefix}.governing_defect_ids cites unknown fidelity-ledger defect `{defect_id}`")
                continue
            if str(defect.get("statement_impact") or "").strip() != "source_statement":
                add(f"{prefix} governing defect `{defect_id}` is not a source-statement defect")
            if str(defect.get("resolution") or "").strip() != "corrected_source_statement":
                add(f"{prefix} governing defect `{defect_id}` is not resolved as corrected_source_statement")

        locator = str(target.get("archival_source_locator") or "").strip()
        if not concrete_source_locator(locator):
            add(f"{prefix}.archival_source_locator must be one concrete source anchor")
        else:
            locator_matches = list(SOURCE_FILE_LINE_RE.finditer(locator))
            if len(locator_matches) != 1:
                add(f"{prefix}.archival_source_locator must contain exactly one file:line anchor")
            for error in source_file_line_anchor_errors(
                folder, locator, file_bytes_override=file_bytes_override
            ):
                add(f"{prefix}.archival_source_locator {error}")
            if len(locator_matches) == 1:
                match = locator_matches[0]
                path, path_error = resolve_paper_source_path(folder, match.group("path"))
                if path is None:
                    add(f"{prefix}.archival_source_locator {path_error}")
                else:
                    try:
                        source_text = normalized_source_text(
                            _exact_file_bytes(path, file_bytes_override)
                        )
                        quote = normalized_source_line_excerpt(
                            normalized_source_lines(source_text),
                            int(match.group("start")),
                            int(match.group("end") or match.group("start")),
                        )
                    except (OSError, RuntimeError, UnicodeDecodeError) as error:
                        quote = None
                        add(f"{prefix}.archival_source_locator cannot be read: {error}")
                    quote_digest = str(
                        target.get("archival_source_quote_sha256") or ""
                    ).strip().lower()
                    if not SHA256_RE.fullmatch(quote_digest):
                        add(f"{prefix}.archival_source_quote_sha256 must be a SHA-256 digest")
                    elif quote is None or quote_digest != hashlib.sha256(
                        quote.encode("utf-8")
                    ).hexdigest():
                        add(f"{prefix}.archival_source_quote_sha256 must pin the exact archival source anchor")

        approval = target.get("approval")
        if not isinstance(approval, dict):
            add(f"{prefix}.approval must be an object")
            continue
        if str(approval.get("kind") or "").strip() not in CORRECTED_TARGET_APPROVAL_KINDS:
            add(f"{prefix}.approval.kind must identify an approved corrected-target disposition")
        if not USER_APPROVED_SCOPE_EXCLUSION_TIMESTAMP_RE.fullmatch(
            str(approval.get("recorded_at") or "").strip()
        ):
            add(f"{prefix}.approval.recorded_at must be an ISO-like date or timestamp")
        if not meaningful_semantic_text(approval.get("reference")):
            add(f"{prefix}.approval.reference must identify the recorded approval")
        if str(approval.get("target_statement_sha256") or "").strip().lower() != target_digest:
            add(f"{prefix}.approval.target_statement_sha256 must pin the corrected target text")
        approval_path = _paper_local_artifact_path(folder, approval.get("artifact_path"))
        approval_digest = str(approval.get("artifact_sha256") or "").strip().lower()
        approval_snapshot = (
            context.json_snapshot(approval_path)
            if context is not None and approval_path is not None
            else None
        )
        approval_actual_digest = (
            approval_snapshot.sha256
            if approval_snapshot is not None
            else hashlib.sha256(
                _exact_file_bytes(approval_path, file_bytes_override)
            ).hexdigest()
            if file_bytes_override is not None and approval_path is not None
            else sha256_file(approval_path)
            if context is None and approval_path is not None and approval_path.is_file()
            else None
        )
        if approval_path is None or approval_actual_digest is None:
            add(f"{prefix}.approval.artifact_path must name a paper-local approval artifact")
        if not SHA256_RE.fullmatch(approval_digest):
            add(f"{prefix}.approval.artifact_sha256 must be a SHA-256 digest")
        elif approval_actual_digest != approval_digest:
            add(f"{prefix}.approval.artifact_sha256 does not match its approval artifact")
        recorded_digest = str(target.get("corrected_target_sha256") or "").strip().lower()
        if not SHA256_RE.fullmatch(recorded_digest):
            add(f"{prefix}.corrected_target_sha256 must be a SHA-256 digest")
        elif recorded_digest != corrected_target_record_digest(target):
            add(f"{prefix}.corrected_target_sha256 is stale")

    if isinstance(ledger, dict):
        unresolved = sorted(
            str(defect.get("id") or "").strip()
            for defect in ledger.get("defects", [])
            if isinstance(defect, dict)
            and str(defect.get("resolution") or "").strip()
            == "corrected_source_statement"
            and str(defect.get("statement_impact") or "").strip()
            == "source_statement"
            and str(defect.get("id") or "").strip() not in governed_defect_ids
        )
        if unresolved:
            add(
                "source-statement corrections lack an explicit corrected_target map record: "
                + ", ".join(unresolved)
            )
    return findings


@dataclass(frozen=True)
class SemanticContractCloseoutInventory:
    """Source-map dispositions eligible for the exact-contract closeout bridge.

    ``contract_item_keys`` are not inferred from Lean declaration spelling.
    They are the source-inventory entries that need a subsequently
    Lean-Meta-checked exact Spec/evidence route.  ``scope_exclusion_item_keys``
    remain claim-bearing source items, but have the repository's already
    byte-pinned, explicitly user-approved non-proof disposition.  They do not
    receive proof credit and are retained separately so callers cannot quietly
    treat them as ordinary proved claims.
    """

    contract_item_keys: tuple[str, ...]
    scope_exclusion_item_keys: tuple[str, ...]


def semantic_contract_closeout_bridge_inventory(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> tuple[SemanticContractCloseoutInventory | None, list[Finding]]:
    """Return the source-grounded inventory for an exact-contract closeout.

    This is deliberately a *structural* half of the bridge.  It verifies the
    canonical source artifact, every required byte-pinned source excerpt,
    corrected-target records, the semantic-contract JSON schema, and the
    narrow user-approved scope disposition.  It does not inspect a Lean route
    by name and it does not itself assert that any proof is valid; the full
    repository audit must still obtain exact Lean-Meta matches before it can
    bypass a blank legacy statement/coverage scaffold.

    A paper does not enter this lane merely because it has a source map.  It
    must opt into ``semantic_contract_schema: 1`` or ``2`` with a curated source
    inventory and exact source-anchor evidence.  Any ordinary claim-bearing
    row without a contract fails closed.  The sole non-proof disposition is a
    separately validated ``user_approved_scope_exclusion``; it remains visible
    as claim-bearing and is never counted as a proved route.
    """

    file_bytes_override = (
        context.file_bytes_override() if context is not None else None
    )
    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    payload = transaction_json(map_path, context)
    if payload is None:
        return None, []
    if not isinstance(payload, dict):
        return None, source_map_scope_integrity_findings(folder, status, map_path, payload)
    if not schema_version_is_supported(
        payload.get("semantic_contract_schema"), SEMANTIC_CONTRACT_SCHEMAS
    ):
        return None, []

    severity = finding_severity(status)
    findings: list[Finding] = []

    def add(message: str) -> None:
        findings.append(Finding(severity, folder.name, rel(map_path), message))

    # Keep raw map/presentation integrity outside the selected proof surface.
    findings.extend(source_map_scope_integrity_findings(folder, status, map_path, payload))
    source_coverage_mode, mode_findings = source_coverage_mode_findings(
        folder, status, map_path, payload
    )
    findings.extend(mode_findings)

    if payload.get("source_curated") is not True:
        add(
            "semantic-contract closeout bridge requires a source_curated: true "
            "inventory; a seeded or uncurated map cannot replace statement/coverage review"
        )
    if payload.get("seed_scaffold") is True:
        add(
            "semantic-contract closeout bridge cannot use a seed_scaffold source inventory"
        )
    if payload.get(SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY) is not True:
        add(
            "semantic-contract closeout bridge requires "
            f"{SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY}: true"
        )

    raw_items = payload.get("items")
    if not isinstance(raw_items, dict) or not raw_items:
        add("semantic-contract closeout bridge requires a nonempty source-map items object")
        return None, findings
    scoped_payload, coverage_items = scoped_source_map_payload(
        payload,
        source_coverage_mode,
        folder=folder,
        repository_root=ROOT,
    )

    # Reuse the ordinary fail-closed validators rather than duplicating or
    # weakening their artifact, anchor, correction, and scope-exclusion rules.
    findings.extend(
        source_artifact_pin_findings(
            folder,
            status,
            map_path,
            payload,
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        )
    )
    findings.extend(
        source_named_result_inventory_findings(
            folder,
            status,
            map_path,
            payload,
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        )
    )
    findings.extend(
        source_anchor_evidence_findings(
            folder,
            status,
            map_path,
            scoped_payload,
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        )
    )
    findings.extend(
        semantic_context_requirement_findings(
            folder,
            status,
            map_path,
            scoped_payload,
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        )
    )
    findings.extend(
        user_approved_scope_exclusion_map_findings(
            folder,
            status,
            map_path,
            scoped_payload,
            require_source_bytes=require_source_bytes,
            file_bytes_override=file_bytes_override,
        )
    )
    findings.extend(
        corrected_source_statement_map_findings(
            folder,
            status,
            payload,
            context=context,
            file_bytes_override=file_bytes_override,
        )
    )
    findings.extend(
        semantic_contract_inventory_findings(
            folder,
            status,
            require_source_bytes=require_source_bytes,
            context=context,
        )
    )

    contract_keys: list[str] = []
    scope_exclusion_keys: list[str] = []
    for raw_key, raw_item in coverage_items.items():
        source_key = str(raw_key).strip()
        if not source_key or not isinstance(raw_item, dict):
            # The semantic-contract schema validator records the detailed
            # shape failure.  Keep this bridge unavailable as well.
            continue
        if raw_item.get("claim_bearing") is not True:
            continue
        if not str(raw_item.get("source_location") or "").strip():
            add(
                f"items.{source_key}: semantic-contract closeout bridge requires a "
                "concrete source_location for every claim-bearing source item"
            )
            continue

        raw_contract = raw_item.get("semantic_contract")
        if isinstance(raw_contract, dict):
            # Detailed contract-shape validation is already included above.
            contract_keys.append(source_key)
            continue

        # Do not silently turn an approved exclusion into a proof.  This
        # branch only records the separately validated, visible disposition;
        # all ordinary claim-bearing rows need an exact contract.
        scope_error = _semantic_contract_user_scope_exclusion_error(
            folder,
            status,
            map_path,
            payload,
            raw_item,
            require_source_bytes=require_source_bytes,
        )
        if not scope_error and raw_item.get(USER_APPROVED_SCOPE_EXCLUSION) is not None:
            scope_exclusion_keys.append(source_key)
            continue
        add(
            f"items.{source_key}: semantic-contract closeout bridge requires an "
            "exact semantic_contract for every claim-bearing source item unless "
            "the existing byte-pinned user_approved_scope_exclusion validator accepts "
            "its explicit non-proof disposition"
        )

    # A user-approved exclusion is intentionally still a visible source-map
    # disposition even when the ordinary selected proof surface does not
    # include that source kind (for example, an explicitly excluded remark).
    # Keep it in the bridge inventory rather than letting the selection step
    # erase the documented non-proof decision.  It never gains proof credit.
    for raw_key, raw_item in raw_items.items():
        source_key = str(raw_key).strip()
        if (
            not source_key
            or source_key in coverage_items
            or not isinstance(raw_item, dict)
            or raw_item.get("claim_bearing") is not True
            or raw_item.get(USER_APPROVED_SCOPE_EXCLUSION) is None
        ):
            continue
        scope_error = _semantic_contract_user_scope_exclusion_error(
            folder,
            status,
            map_path,
            payload,
            raw_item,
            require_source_bytes=require_source_bytes,
        )
        if scope_error:
            add(f"items.{source_key}: {scope_error}")
        else:
            scope_exclusion_keys.append(source_key)

    if not contract_keys:
        add(
            "semantic-contract closeout bridge requires at least one claim-bearing "
            "source item with an exact Spec/evidence contract"
        )
    if findings:
        return None, findings
    return (
        SemanticContractCloseoutInventory(
            contract_item_keys=tuple(sorted(contract_keys)),
            scope_exclusion_item_keys=tuple(sorted(scope_exclusion_keys)),
        ),
        [],
    )


def corrected_model_anchor_errors(folder: Path, value: object) -> list[str]:
    """Validate corrected-scope anchors in local docs or the pinned source tarball."""

    if not isinstance(value, str):
        return []
    archive_path = folder / "source.tar.gz"
    errors: list[str] = []
    for match in SOURCE_FILE_LINE_RE.finditer(value):
        raw_path = Path(match.group("path"))
        start = int(match.group("start"))
        end = int(match.group("end") or start)
        try:
            local = (folder / raw_path).resolve()
            local.relative_to(folder.resolve())
        except (OSError, RuntimeError, ValueError):
            errors.append(f"corrected-model anchor `{raw_path}` escapes the paper folder")
            continue
        text: str | None = None
        if local.is_file() and local.suffix.lower() in TEXT_SOURCE_SUFFIXES:
            try:
                text = local.read_text(encoding="utf-8")
            except OSError:
                errors.append(f"corrected-model anchor `{raw_path}` could not be read")
                continue
        elif archive_path.is_file():
            try:
                with tarfile.open(archive_path, "r:*") as archive:
                    members = [
                        member
                        for member in archive.getmembers()
                        if member.isfile()
                        and (member.name == str(raw_path) or member.name.endswith(f"/{raw_path}"))
                    ]
                    if len(members) != 1:
                        errors.append(
                            f"corrected-model anchor `{raw_path}` does not identify one source file "
                            "in the pinned archive"
                        )
                        continue
                    if Path(members[0].name).suffix.lower() not in TEXT_SOURCE_SUFFIXES:
                        continue
                    stream = archive.extractfile(members[0])
                    if stream is None:
                        errors.append(f"corrected-model anchor `{raw_path}` could not be extracted")
                        continue
                    text = stream.read().decode("utf-8", errors="replace")
            except (OSError, tarfile.TarError):
                errors.append("pinned source archive could not be read for corrected-model anchors")
                continue
        else:
            errors.append(
                f"corrected-model anchor `{raw_path}` is neither local nor present in the pinned source archive"
            )
            continue
        if text is None:
            continue
        line_count = len(text.splitlines())
        if start < 1 or end < start or end > line_count:
            errors.append(
                f"corrected-model anchor `{raw_path}:{start}-{end}` is outside its {line_count}-line source"
            )
    return errors


def source_proof_fidelity_findings(
    folder: Path,
    status: str,
    status_payload: dict[str, Any],
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
    file_bytes_override: Mapping[Path, bytes | None] | None = None,
) -> list[Finding]:
    """Validate the semantic source-proof defect ledger for configured papers.

    The ledger is intentionally keyed by source locations and mathematical
    repair obligations. It does not treat Lean declaration names as evidence,
    and its resolution enum intentionally has no source-assumption escape hatch.
    """

    if file_bytes_override is None and context is not None:
        file_bytes_override = context.file_bytes_override()

    migration_findings = v10_migration_pending_findings(
        folder, status, status_payload, context=context
    )
    config = source_proof_fidelity_config(status_payload)
    if config is None:
        reasons = source_proof_fidelity_requirement_reasons(
            folder, status, status_payload, context=context
        )
        if not reasons:
            return migration_findings
        return migration_findings + [
            Finding(
                "ERROR",
                folder.name,
                rel(folder / "status.json"),
                f"full-closeout status `{status}` requires "
                "review_surface.source_proof_fidelity_review with a ledger_file because "
                + "; ".join(reasons),
            )
        ]
    severity = finding_severity(status)
    ledger_path, path_error = source_proof_fidelity_ledger_path(folder, status_payload)
    if path_error:
        return migration_findings + [
            Finding(
                severity,
                folder.name,
                rel(folder / "status.json"),
                path_error,
            )
        ]
    assert ledger_path is not None

    # Once the paper has a canonical ledger, a full-closeout configuration may
    # not select a second, cleaner file.  The closeout triggers inspect the
    # canonical source map and ledger, so allowing a different configured file
    # here would let live defect debt disappear from the closeout path.  Keep
    # custom paths available for partial/in-progress papers and for papers that
    # have not yet established a canonical sidecar.
    canonical_ledger_path = transaction_sidecar(
        folder, "source_proof_fidelity.json", context
    )
    canonical_ledger_snapshot = (
        context.json_snapshot(canonical_ledger_path) if context is not None else None
    )
    if context is not None:
        canonical_ledger_exists = (
            canonical_ledger_snapshot is not None
            and canonical_ledger_snapshot.sha256 is not None
        )
    elif file_bytes_override is not None:
        canonical_ledger_exists = (
            canonical_ledger_path.resolve() in file_bytes_override
            and file_bytes_override[canonical_ledger_path.resolve()] is not None
        )
    else:
        canonical_ledger_exists = canonical_ledger_path.exists()
    if (
        status in FULL_CLOSEOUT_STATUSES
        and canonical_ledger_exists
        and ledger_path.resolve() != canonical_ledger_path.resolve()
    ):
        return migration_findings + [
            Finding(
                "ERROR",
                folder.name,
                rel(folder / "status.json"),
                "full-closeout source_proof_fidelity_review.ledger_file must resolve "
                "to the canonical source-proof fidelity ledger; a separate configured "
                "ledger could hide canonical source-proof defects",
            )
        ]
    if context is not None:
        ledger = transaction_json(ledger_path, context)
    elif file_bytes_override is not None:
        try:
            raw_ledger = json.loads(
                _exact_file_bytes(ledger_path, file_bytes_override)
            )
        except (OSError, RuntimeError, UnicodeDecodeError, json.JSONDecodeError):
            raw_ledger = None
        ledger = raw_ledger if isinstance(raw_ledger, dict) else None
    else:
        ledger = transaction_json(ledger_path, None)
    if ledger is None:
        return migration_findings + [
            Finding(
                severity,
                folder.name,
                rel(ledger_path),
                "configured source-proof fidelity ledger is missing or invalid",
            )
        ]

    findings: list[Finding] = list(migration_findings)
    corrected_scope = author_approved_corrected_scope(status_payload)
    if corrected_scope is not None:
        if context is not None:
            findings.extend(context.corrected_scope_findings)
        else:
            findings.extend(
                corrected_model_scope_contract_findings(folder, status, status_payload)
            )
    corrected_scope_ids = {
        str(correction_id).strip()
        for correction_id in (corrected_scope or {}).get("correction_ids") or []
        if str(correction_id).strip()
    }
    corrected_scope_role: str | None = None
    if corrected_scope is not None:
        corrected_scope_role, _ = corrected_model_scope_role(corrected_scope)
    declared_governing_correction_ids = {
        str(correction.get("id") or "").strip()
        for correction in status_payload.get("governing_corrections") or []
        if isinstance(correction, dict) and str(correction.get("id") or "").strip()
    }

    def add(message: str, *, force_error: bool = False) -> None:
        findings.append(
            Finding(
                "ERROR" if force_error else severity,
                folder.name,
                rel(ledger_path),
                message,
            )
        )

    schema = ledger.get("schema")
    if not schema_version_is_supported(schema, SOURCE_PROOF_FIDELITY_SCHEMAS):
        add("source-proof fidelity ledger must use schema 1 or 2")
    paper = str(ledger.get("paper") or "").strip()
    if paper != folder.name:
        add(
            f"source-proof fidelity ledger names paper `{paper or 'missing'}`, not `{folder.name}`"
        )

    review_status = str(ledger.get("review_status") or "").strip()
    if review_status not in SOURCE_PROOF_FIDELITY_REVIEW_STATUSES:
        add(
            "source-proof fidelity review_status must be one of: "
            + ", ".join(sorted(SOURCE_PROOF_FIDELITY_REVIEW_STATUSES))
        )
        return findings

    needs_closeout_review = status in CLOSEOUT_STATUSES
    if status in FULL_CLOSEOUT_STATUSES and not schema_version_is_exact(schema, 2):
        add(
            f"full-closeout status `{status}` requires source-proof fidelity schema 2 "
            "with issue-level status impact",
            force_error=True,
        )
    review_complete = review_status in {"reviewed_no_defects", "defects_recorded"}
    if needs_closeout_review and not review_complete:
        add(
            f"closeout status `{status}` requires a completed source-proof fidelity review; "
            f"ledger remains `{review_status}`",
            force_error=True,
        )
    if review_complete:
        findings.extend(
            source_artifact_pin_findings(
                folder,
                status,
                ledger_path,
                ledger,
                require_source_bytes=require_source_bytes,
                file_bytes_override=file_bytes_override,
            )
        )

    raw_scopes = ledger.get("reviewed_proof_scopes")
    scopes = raw_scopes if isinstance(raw_scopes, list) else []
    if review_complete and not scopes:
        add("completed source-proof fidelity review has no reviewed_proof_scopes")
    for index, scope in enumerate(scopes):
        label = f"reviewed_proof_scopes[{index}]"
        if not isinstance(scope, dict):
            add(f"{label} must be an object with source locator and semantic scope")
            continue
        if not concrete_source_locator(scope.get("source_locator")):
            add(f"{label}.source_locator must be a concrete source anchor")
        else:
            if require_source_bytes:
                for error in source_file_line_anchor_errors(
                    folder,
                    scope["source_locator"],
                    file_bytes_override=file_bytes_override,
                ):
                    add(f"{label}.source_locator {error}")
        if not meaningful_semantic_text(scope.get("semantic_scope")):
            add(f"{label}.semantic_scope must describe the proof mathematics")
        outcome = str(scope.get("outcome") or "").strip()
        if outcome not in SOURCE_PROOF_FIDELITY_SCOPE_OUTCOMES:
            add(
                f"{label}.outcome must be one of: "
                + ", ".join(sorted(SOURCE_PROOF_FIDELITY_SCOPE_OUTCOMES))
            )
        if review_status == "reviewed_no_defects" and outcome == "defect_recorded":
            add(f"{label} records a defect but review_status is reviewed_no_defects")

    def check_semantic_context_entries(
        raw_entries: object,
        *,
        label: str,
        required_fields: tuple[str, ...],
    ) -> None:
        """Validate optional source-located semantic context structurally.

        These entries are deliberately independent of Lean declaration names.
        They preserve the distinction between an explicit formalization
        convention, a checked source-proof step, and a source theorem/assumption
        when the recursive provenance judge receives the ledger.
        """

        if raw_entries is None:
            return
        if not isinstance(raw_entries, list):
            add(f"{label} must be a list when present")
            return
        seen_ids: set[str] = set()
        for index, entry in enumerate(raw_entries):
            entry_label = f"{label}[{index}]"
            if not isinstance(entry, dict):
                add(f"{entry_label} must be an object")
                continue
            entry_id = str(entry.get("id") or "").strip()
            if not SOURCE_PROOF_DEFECT_ID_RE.fullmatch(entry_id):
                add(
                    f"{entry_label}.id must be a stable nonempty identifier using only "
                    "letters, digits, dot, underscore, or hyphen"
                )
            elif entry_id in seen_ids:
                add(f"{entry_label}.id duplicates {label} entry `{entry_id}`")
            else:
                seen_ids.add(entry_id)
            if not concrete_source_locator(entry.get("source_locator")):
                add(f"{entry_label}.source_locator must be a concrete source anchor")
            elif require_source_bytes:
                for error in source_file_line_anchor_errors(
                    folder,
                    entry["source_locator"],
                    file_bytes_override=file_bytes_override,
                ):
                    add(f"{entry_label}.source_locator {error}")
            for field in required_fields:
                if field in {"id", "source_locator"}:
                    continue
                if not meaningful_semantic_text(entry.get(field)):
                    add(
                        f"{entry_label}.{field} must contain a source-vs-Lean "
                        "mathematical explanation, not a declaration-name reference"
                    )

    check_semantic_context_entries(
        ledger.get("model_conventions"),
        label="model_conventions",
        required_fields=SOURCE_PROOF_MODEL_CONVENTION_REQUIRED_FIELDS,
    )
    check_semantic_context_entries(
        ledger.get("checked_proof_steps"),
        label="checked_proof_steps",
        required_fields=SOURCE_PROOF_CHECKED_STEP_REQUIRED_FIELDS,
    )

    raw_deep_observations = ledger.get("deep_audit_observations")
    deep_observations = (
        raw_deep_observations
        if isinstance(raw_deep_observations, list)
        else []
    )
    if raw_deep_observations is not None and not isinstance(
        raw_deep_observations, list
    ):
        add("deep_audit_observations must be a list when present")
    seen_deep_observation_ids: set[str] = set()
    for index, observation in enumerate(deep_observations):
        label = f"deep_audit_observations[{index}]"
        if not isinstance(observation, dict):
            add(f"{label} must be an object")
            continue
        observation_id = str(observation.get("id") or "").strip()
        if not SOURCE_PROOF_DEFECT_ID_RE.fullmatch(observation_id):
            add(
                f"{label}.id must be a stable nonempty identifier using only "
                "letters, digits, dot, underscore, or hyphen"
            )
        elif observation_id in seen_deep_observation_ids:
            add(
                f"{label}.id duplicates deep audit observation `{observation_id}`"
            )
        else:
            seen_deep_observation_ids.add(observation_id)
        for field in DEEP_AUDIT_OBSERVATION_REQUIRED_FIELDS:
            if field not in observation:
                add(f"{label} is missing required field `{field}`")
        if not concrete_source_locator(observation.get("source_locator")):
            add(f"{label}.source_locator must be a concrete source anchor")
        else:
            for error in canonical_artifact_source_span_errors(
                folder,
                observation["source_locator"],
                source_artifact_path=ledger.get("source_artifact_path"),
            ):
                add(f"{label}.source_locator {error}")
            if require_source_bytes:
                for error in source_file_line_anchor_errors(
                    folder,
                    observation["source_locator"],
                    file_bytes_override=file_bytes_override,
                ):
                    add(f"{label}.source_locator {error}")
        affected = observation.get("affected_source_locators")
        if not isinstance(affected, list) or not affected:
            add(f"{label}.affected_source_locators must list concrete source anchors")
        elif any(not concrete_source_locator(locator) for locator in affected):
            add(
                f"{label}.affected_source_locators contains a non-concrete source anchor"
            )
        else:
            for locator in affected:
                for error in canonical_artifact_source_span_errors(
                    folder,
                    locator,
                    source_artifact_path=ledger.get("source_artifact_path"),
                ):
                    add(f"{label}.affected_source_locators {error}")
                if not require_source_bytes:
                    continue
                for error in source_file_line_anchor_errors(
                    folder, locator, file_bytes_override=file_bytes_override
                ):
                    add(f"{label}.affected_source_locators {error}")
        for field in ("source_claim", "finding", "repair_handoff"):
            if not meaningful_semantic_text(observation.get(field)):
                add(f"{label}.{field} must contain a source-facing mathematical explanation")
        if (
            str(observation.get("normal_scope_disposition") or "").strip()
            != DEEP_AUDIT_OBSERVATION_NORMAL_SCOPE_DISPOSITION
        ):
            add(
                f"{label}.normal_scope_disposition must be "
                f"`{DEEP_AUDIT_OBSERVATION_NORMAL_SCOPE_DISPOSITION}`"
            )
        forbidden_fields = {
            "resolution",
            "statement_impact",
            "status_impact",
            "source_defect_ids",
            "corrected_target",
            USER_APPROVED_SCOPE_EXCLUSION,
        }
        present_forbidden = sorted(forbidden_fields & set(observation))
        if present_forbidden:
            add(
                f"{label} is a documentation-only deep observation and cannot "
                "carry source-defect resolution fields: "
                + ", ".join(present_forbidden)
            )

    if review_status == "reviewed_no_defects" and deep_observations:
        add("reviewed_no_defects ledger cannot contain deep_audit_observations")

    map_path = transaction_sidecar(folder, "paper_statement_map.json", context)
    if context is not None:
        map_payload = transaction_json(map_path, context)
    elif file_bytes_override is not None:
        try:
            raw_map_payload = json.loads(
                _exact_file_bytes(map_path, file_bytes_override)
            )
        except (OSError, RuntimeError, UnicodeDecodeError, json.JSONDecodeError):
            raw_map_payload = None
        map_payload = raw_map_payload if isinstance(raw_map_payload, dict) else None
    else:
        map_payload = transaction_json(map_path, None)
    map_has_deep_links = bool(
        isinstance(map_payload, dict)
        and isinstance(map_payload.get("items"), dict)
        and any(
            isinstance(item, dict)
            and DEEP_AUDIT_OBSERVATION_LINK_FIELD in item
            for item in map_payload["items"].values()
        )
    )
    if deep_observations or map_has_deep_links:
        for error in deep_audit_observation_map_link_errors(
            map_payload, seen_deep_observation_ids
        ):
            add(error)
    if map_has_deep_links and isinstance(map_payload, dict):
        raw_items = map_payload.get("items")
        assert isinstance(raw_items, dict)
        deep_link_rows = {
            str(key): item
            for key, item in raw_items.items()
            if isinstance(item, dict)
            and DEEP_AUDIT_OBSERVATION_LINK_FIELD in item
        }
        isolated_map_payload = {
            "source_artifact_path": map_payload.get("source_artifact_path"),
            "source_artifact_sha256": map_payload.get("source_artifact_sha256"),
            SOURCE_ANCHOR_EVIDENCE_REQUIRED_KEY: True,
            "items": deep_link_rows,
        }
        findings.extend(
            source_anchor_evidence_findings(
                folder,
                status,
                map_path,
                isolated_map_payload,
                require_source_bytes=require_source_bytes,
            )
        )

    raw_defects = ledger.get("defects")
    defects = raw_defects if isinstance(raw_defects, list) else []
    if review_status == "reviewed_no_defects" and defects:
        add("reviewed_no_defects ledger cannot contain defect entries")
    if review_status == "defects_recorded" and not defects and not deep_observations:
        add(
            "defects_recorded ledger must contain at least one source-proof defect "
            "or deep audit observation"
        )
    if raw_defects is not None and not isinstance(raw_defects, list):
        add("source-proof fidelity defects must be a list")

    if status in FULL_CLOSEOUT_STATUSES:
        routed_defect_ids = canonical_source_map_defect_ids(folder)
        ledger_defect_ids = {
            str(defect.get("id") or "").strip()
            for defect in defects
            if isinstance(defect, dict) and str(defect.get("id") or "").strip()
        }
        unresolved_routed_defects = sorted(routed_defect_ids - ledger_defect_ids)
        if unresolved_routed_defects:
            add(
                "full-closeout source map references source_defect_ids absent from "
                "the configured source-proof fidelity ledger: "
                + ", ".join(unresolved_routed_defects[:8])
                + ("; ..." if len(unresolved_routed_defects) > 8 else ""),
                force_error=True,
            )

    seen_defect_ids: set[str] = set()
    status_impacts: list[str] = []
    for index, defect in enumerate(defects):
        label = f"defects[{index}]"
        if not isinstance(defect, dict):
            add(f"{label} must be an object")
            continue
        defect_id = str(defect.get("id") or "").strip()
        if not SOURCE_PROOF_DEFECT_ID_RE.fullmatch(defect_id):
            add(
                f"{label}.id must be a stable nonempty identifier using only "
                "letters, digits, dot, underscore, or hyphen"
            )
        elif defect_id in seen_defect_ids:
            add(f"{label}.id duplicates source-proof defect `{defect_id}`")
        else:
            seen_defect_ids.add(defect_id)
        if not concrete_source_locator(defect.get("source_locator")):
            add(f"{label}.source_locator must be a concrete source anchor")
        else:
            if require_source_bytes:
                for error in source_file_line_anchor_errors(
                    folder,
                    defect["source_locator"],
                    file_bytes_override=file_bytes_override,
                ):
                    add(f"{label}.source_locator {error}")
        for key in (
            "source_claim",
            "repair_obligation",
            "acceptance_condition",
            "resolution_evidence",
        ):
            if not meaningful_semantic_text(defect.get(key)):
                add(f"{label}.{key} must contain a mathematical explanation")
        kind = str(defect.get("defect_kind") or "").strip()
        if kind not in SOURCE_PROOF_FIDELITY_DEFECT_KINDS:
            add(
                f"{label}.defect_kind must be one of: "
                + ", ".join(sorted(SOURCE_PROOF_FIDELITY_DEFECT_KINDS))
            )
        impact = str(defect.get("statement_impact") or "").strip()
        if impact not in SOURCE_PROOF_FIDELITY_STATEMENT_IMPACTS:
            add(
                f"{label}.statement_impact must be one of: "
                + ", ".join(sorted(SOURCE_PROOF_FIDELITY_STATEMENT_IMPACTS))
            )
        status_impact = str(defect.get("status_impact") or "").strip()
        if schema_version_is_exact(schema, 2):
            if status_impact not in SOURCE_PROOF_FIDELITY_STATUS_IMPACTS:
                add(
                    f"{label}.status_impact must be one of: "
                    + ", ".join(sorted(SOURCE_PROOF_FIDELITY_STATUS_IMPACTS))
                )
            else:
                status_impacts.append(status_impact)
            if not meaningful_semantic_text(defect.get("status_impact_rationale")):
                add(
                    f"{label}.status_impact_rationale must explain why the issue is "
                    "note-only, a substantial paper error, or a partial-formalization boundary"
                )
        resolution = str(defect.get("resolution") or "").strip()
        if resolution not in SOURCE_PROOF_FIDELITY_RESOLUTIONS:
            add(
                f"{label}.resolution must be one of: "
                + ", ".join(sorted(SOURCE_PROOF_FIDELITY_RESOLUTIONS))
                + "; source assumptions are not a permitted source-proof-defect resolution",
            )
        is_user_approved_scope_exclusion = (
            resolution == USER_APPROVED_SCOPE_EXCLUSION
        )
        if is_user_approved_scope_exclusion:
            if impact != "source_statement":
                add(
                    f"{label}.user_approved_scope_exclusion requires "
                    "statement_impact source_statement; the source claim remains visible"
                )
            if status_impact != "formalized_note":
                add(
                    f"{label}.user_approved_scope_exclusion requires "
                    "status_impact formalized_note"
                )
            for error in user_approved_scope_exclusion_errors(
                folder,
                defect.get(USER_APPROVED_SCOPE_EXCLUSION),
                expected_source_locator=defect.get("source_locator"),
                require_source_bytes=require_source_bytes,
                file_bytes_override=file_bytes_override,
            ):
                add(f"{label}.{error}")
        affected = defect.get("affected_source_locators")
        if not isinstance(affected, list) or not affected:
            add(f"{label}.affected_source_locators must list affected source anchors")
        elif any(not concrete_source_locator(locator) for locator in affected):
            add(f"{label}.affected_source_locators contains a non-concrete source anchor")
        elif require_source_bytes:
            for locator in affected:
                for error in source_file_line_anchor_errors(
                    folder, locator, file_bytes_override=file_bytes_override
                ):
                    add(f"{label}.affected_source_locators {error}")

        if resolution == "corrected_source_statement" and impact == "proof_only":
            add(f"{label} cannot use corrected_source_statement for a proof_only defect")
        # A paper can have one narrowly approved corrected target and separate
        # local source-proof repairs. Every explicit correction reference must
        # resolve to the paper's governing-correction registry. Only a
        # waiver-capable whole-paper scope may additionally demand that the
        # repair belong to its approved target list; component scopes cannot
        # grant source-result credit to either kind of repair.
        governing_metadata_fields = (
            "governing_disposition",
            "correction_id",
            "corrected_clause_anchor",
            "conclusion_relation",
            "does_not_claim_archive_derivation",
        )
        governed_by_corrected_scope = any(
            field in defect for field in governing_metadata_fields
        )
        if corrected_scope is not None and governed_by_corrected_scope:
            governing_disposition = str(
                defect.get("governing_disposition") or ""
            ).strip()
            correction_id = str(defect.get("correction_id") or "").strip()
            corrected_clause_anchor = str(
                defect.get("corrected_clause_anchor") or ""
            ).strip()
            conclusion_relation = str(
                defect.get("conclusion_relation") or ""
            ).strip()
            if governing_disposition not in CORRECTED_MODEL_GOVERNING_DISPOSITIONS:
                add(
                    f"{label}.governing_disposition must be one of: "
                    + ", ".join(sorted(CORRECTED_MODEL_GOVERNING_DISPOSITIONS))
                )
            if correction_id not in declared_governing_correction_ids:
                add(f"{label}.correction_id must cite a declared governing correction")
            elif (
                corrected_scope_role == WHOLE_PAPER_CLOSEOUT_SCOPE_ROLE
                and correction_id not in corrected_scope_ids
            ):
                add(
                    f"{label}.correction_id must cite a correction included by the "
                    "whole-paper corrected scope"
                )
            if not corrected_clause_anchor:
                add(f"{label}.corrected_clause_anchor must identify the approved correction")
            if conclusion_relation not in CORRECTED_MODEL_CONCLUSION_RELATIONS:
                add(
                    f"{label}.conclusion_relation must be one of: "
                    + ", ".join(sorted(CORRECTED_MODEL_CONCLUSION_RELATIONS))
                )
            if defect.get("does_not_claim_archive_derivation") is not True:
                add(
                    f"{label}.does_not_claim_archive_derivation must be true for an "
                    "author-approved corrected target"
                )
        if schema_version_is_exact(schema, 2) and status_impact == "formalized_with_caveat":
            if impact != "source_statement":
                add(
                    f"{label}.status_impact formalized_with_caveat requires a "
                    "source_statement defect"
                )
            if resolution != "corrected_source_statement":
                add(
                    f"{label}.status_impact formalized_with_caveat requires a fully "
                    "checked corrected_source_statement resolution"
                )
            if status != "formalized with caveat":
                add(
                    f"{label}.status_impact formalized_with_caveat conflicts with paper "
                    f"status `{status}`",
                    force_error=True,
                )
        if (
            schema_version_is_exact(schema, 2)
            and status_impact == "partially_formalized"
            and status in FULL_CLOSEOUT_STATUSES
        ):
            add(
                f"full-closeout status `{status}` conflicts with {label}.status_impact "
                "partially_formalized",
                force_error=True,
            )
        if schema_version_is_exact(schema, 2) and resolution == "open_proof_obligation" and status_impact != "partially_formalized":
            add(
                f"{label}.resolution open_proof_obligation requires status_impact "
                "partially_formalized"
            )
        if schema_version_is_exact(schema, 2) and status in FULL_CLOSEOUT_STATUSES and impact == "uncertain":
            add(
                f"full-closeout status `{status}` conflicts with uncertain statement impact "
                f"in {label}",
                force_error=True,
            )
        if (
            status in FULL_CLOSEOUT_STATUSES
            and resolution == "open_proof_obligation"
        ):
            add(
                f"closed status `{status}` conflicts with {label} still marked open_proof_obligation",
                force_error=True,
            )
    overlapping_issue_ids = sorted(seen_deep_observation_ids & seen_defect_ids)
    if overlapping_issue_ids:
        add(
            "deep_audit_observations must not reuse source-proof defect ids: "
            + ", ".join(overlapping_issue_ids)
        )
    if schema_version_is_exact(schema, 2) and status == PLAIN_FORMALIZED:
        incompatible = sorted(set(status_impacts) - {"formalized_note"})
        if incompatible:
            add(
                "plain `formalized` status permits only formalized_note defects, not: "
                + ", ".join(incompatible),
                force_error=True,
            )
    if schema_version_is_exact(schema, 2) and status == "formalized with caveat" and "formalized_with_caveat" not in status_impacts:
        add(
            "`formalized with caveat` requires at least one schema-2 defect with "
            "status_impact formalized_with_caveat",
            force_error=True,
        )
    return findings


def _semantic_contract_revalidation_module() -> Any:
    """Load the optional structural replay without changing raw generation."""

    try:
        from scripts import source_record_semantic_contract_revalidation as replay
    except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
        import source_record_semantic_contract_revalidation as replay
    return replay


def source_record_semantic_contract_revalidation_context(
    folder: Path,
    audit_payload: Mapping[str, Any],
) -> tuple[Any | None, str]:
    """Validate the fixed structural replay for a standalone evidence consumer.

    The replay itself checks the exact canonical raw/map bytes and the optional
    artifact.  An absent artifact returns an empty projection, while a malformed
    or stale artifact fails closed.  Transaction callers pass snapshot-derived
    values directly through ``EvidenceRunContext`` instead.
    """

    try:
        replay = _semantic_contract_revalidation_module()
        return replay.semantic_contract_revalidation_projection(
            paper_dir=folder,
            paper=folder.name,
            raw_audit=audit_payload,
        )
    except Exception as error:  # noqa: BLE001 - optional authority fails closed.
        return None, (
            "could not validate semantic-contract revalidation: "
            f"{type(error).__name__}: {error}"
        )


def _trusted_semantic_contract_revalidation_projection(value: Any) -> Any | None:
    """Accept only the replay module's immutable projection type."""

    try:
        replay = _semantic_contract_revalidation_module()
    except Exception:  # noqa: BLE001 - caller receives no structural credit.
        return None
    return value if replay.projection_is_authenticated(value) else None


def source_record_effective_input_judgment_keys(
    audit_payload: Mapping[str, Any],
    *,
    semantic_contract_revalidation: Any | None = None,
) -> set[str]:
    """Return input obligations after current ledger and structural replay.

    This is intentionally narrower than ``source_record_required_keys`` so
    closeout consumers that separately account for recursive fields and model
    dimensions can share the same authenticated input projection.
    """

    expected_inputs = {
        str(key).strip()
        for key in audit_payload.get("expected_input_judgment_keys") or []
        if str(key).strip()
    }
    statement_ledger_covered = {
        str(key).strip()
        for key in audit_payload.get(
            "statement_ledger_covered_boundary_input_keys"
        )
        or []
        if str(key).strip()
    }
    conclusion_dependency_keys = {
        str(item.get("judgment_key") or "").strip()
        for item in audit_payload.get("conclusion_dependency_items") or []
        if isinstance(item, Mapping)
        and str(item.get("judgment_key") or "").strip()
    }
    # A statement ledger validates endpoint/source correspondence. It does
    # not prove a caller-supplied input that semantic analysis identifies as
    # conclusion-bearing.
    statement_ledger_covered -= conclusion_dependency_keys
    projection = _trusted_semantic_contract_revalidation_projection(
        semantic_contract_revalidation
    )
    suppressed_inputs = (
        set(projection.suppressed_expected_input_keys)
        if projection is not None
        else set()
    )
    return expected_inputs - statement_ledger_covered - suppressed_inputs


def source_record_required_keys(
    audit_payload: dict[str, Any],
    *,
    semantic_contract_revalidation: Any | None = None,
) -> list[str]:
    expected_inputs = {
        str(key).strip()
        for key in audit_payload.get("expected_input_judgment_keys") or []
        if str(key).strip()
    }
    expected_fields = {
        str(key).strip()
        for key in audit_payload.get("expected_field_judgment_keys") or []
        if str(key).strip()
    }
    expected_semantic_model = {
        str(key).strip()
        for key in audit_payload.get("expected_semantic_model_judgment_keys") or []
        if str(key).strip()
    }
    if expected_inputs or expected_fields or expected_semantic_model:
        return sorted(
            source_record_effective_input_judgment_keys(
                audit_payload,
                semantic_contract_revalidation=semantic_contract_revalidation,
            )
            | expected_fields
            | expected_semantic_model
        )

    # Older source-record payloads predate the explicit expected-key ledgers.
    keys: list[str] = []
    for item_key in (
        "boundary_input_items",
        "recursive_field_items",
        "semantic_model_items",
    ):
        raw_items = audit_payload.get(item_key) or []
        if not isinstance(raw_items, list):
            continue
        for item in raw_items:
            if not isinstance(item, dict):
                continue
            if not schema_version_is_exact(
                item.get("source_record_item_digest_schema"),
                SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
            ):
                continue
            key = str(item.get("judgment_key") or "").strip()
            if key:
                keys.append(key)
    return sorted(set(keys))


def source_record_required_item_digest_candidates(
    audit_payload: dict[str, Any],
) -> dict[str, set[str]]:
    """Return every eligible item receipt seen for each current judgment key.

    This mirrors the generator's cache contract.  A key with different receipts
    across generated sections cannot use scalar reuse; a shared receipt at two
    different keys remains valid for direct same-key reuse but is not a safe
    key-independent remapping token.
    """

    candidate_digests: dict[str, set[str]] = {}
    for item_key in SOURCE_RECORD_REUSABLE_ITEM_SECTIONS:
        raw_items = audit_payload.get(item_key) or []
        if not isinstance(raw_items, list):
            continue
        for item in raw_items:
            if not isinstance(item, dict):
                continue
            if not source_record_item_reuse_eligible(
                item,
                expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
            ):
                continue
            key = str(item.get("judgment_key") or "").strip()
            digest = str(item.get("source_record_item_sha256") or "").strip()
            if key and digest:
                candidate_digests.setdefault(key, set()).add(digest)
    return candidate_digests


def source_record_required_item_digests(audit_payload: dict[str, Any]) -> dict[str, str]:
    """Return one complete current receipt for each direct judgment key.

    An ordinary input and its conclusion-dependency expansion can share a key
    while requiring different reviews. Different digests are intentionally
    omitted, forcing freshness through the current aggregate source-record
    digest rather than accepting the weaker item-level surface.

    Different keys may retain the same complete receipt. A direct sidecar entry
    is still safe because its key selects the current obligation; only a
    key-independent remap must require global digest uniqueness.
    """

    return {
        key: next(iter(digests))
        for key, digests in source_record_required_item_digest_candidates(
            audit_payload
        ).items()
        if len(digests) == 1
    }


def source_record_unique_item_digest_keys(
    audit_payload: dict[str, Any],
) -> dict[str, str]:
    """Return only digest-to-key identities safe for a renamed sidecar entry."""

    keys_by_digest: dict[str, set[str]] = {}
    for key, digest in source_record_required_item_digests(audit_payload).items():
        keys_by_digest.setdefault(digest, set()).add(key)
    return {
        digest: next(iter(keys))
        for digest, keys in keys_by_digest.items()
        if len(keys) == 1
    }


def current_paper_statement_map_sha256(folder: Path) -> str:
    """Return the byte identity of the source map currently on disk.

    Source-record judgments may be reused at item granularity, so their saved
    audit must still be tied to the current source inventory as a whole.  This
    helper intentionally hashes the map bytes rather than parsed JSON: any
    source-map edit, including a source locator or scope change, requires a
    fresh generated audit.
    """

    map_path = canonical_sidecar(folder, "paper_statement_map.json")
    try:
        return hashlib.sha256(map_path.read_bytes()).hexdigest()
    except OSError:
        return ""


def current_paper_statement_map_semantic_sha256(folder: Path) -> str:
    """Return the narrow map receipt allowed for raw-cache reuse only.

    This is deliberately separate from the full byte receipt above.  It drops
    only explicitly administrative direct source-item metadata; every other
    source-map edit remains part of the evidence/currentness boundary.
    """

    map_path = canonical_sidecar(folder, "paper_statement_map.json")
    try:
        payload = json.loads(map_path.read_bytes())
    except (OSError, json.JSONDecodeError):
        return ""
    return source_map_cache_semantic_sha256(payload)


def source_record_legacy_v7_fingerprint_is_current(
    legacy_v7: Mapping[str, Any], current: Mapping[str, Any]
) -> bool:
    """Validate the explicit v7 migration identity against current v8 inputs.

    The source-record helper reconstructs this object from the historical
    broad-status/full-ledger algorithm.  Do not accept a merely schema-7-shaped
    payload: every field other than the two deliberately narrowed content
    projections and the schema must agree with current source/interface/map,
    engine, toolchain, and execution inputs.  This makes missing fields or an
    unrecognized future cache schema fail closed.
    """

    if not schema_version_is_exact(legacy_v7.get("schema"), 7):
        return False
    if schema_version_is_exact(current.get("schema"), 7):
        # Pre-projection helper output is an ordinary exact v7 identity.
        return dict(legacy_v7) == dict(current)
    if not schema_version_is_exact(current.get("schema"), 8) or set(legacy_v7) != set(current):
        return False
    narrowed_fields = {
        "schema",
        "relevant_status_sha256",
        "source_proof_fidelity_sha256",
    }
    return all(
        legacy_v7.get(key) == current.get(key)
        for key in current
        if key not in narrowed_fields
    )


def source_record_legacy_v6_fingerprint_matches_current(
    stored: Mapping[str, Any],
    current: Mapping[str, Any],
    *,
    recorded_map_sha256: str,
    current_map_sha256: str,
) -> bool:
    """Accept the exact v6 cache identity only with unchanged map provenance.

    The source-record generator itself retains this compatibility path while a
    paper still has a schema-6 raw receipt.  A v6 fingerprint recorded the
    full map byte hash instead of the v7 semantic receipt, so it cannot use
    any map-edit exception.  Keeping this comparison here identical prevents
    the evidence gate from rejecting a raw audit that the cache correctly
    recognizes as current.
    """

    recorded = recorded_map_sha256.strip().lower()
    current_map = current_map_sha256.strip().lower()
    if not (
        SHA256_RE.fullmatch(recorded)
        and recorded == current_map
        and schema_version_is_exact(current.get("schema"), 7)
    ):
        return False
    legacy = dict(current)
    legacy["schema"] = 6
    legacy.pop("paper_statement_map_semantic_sha256", None)
    legacy["paper_statement_map_sha256"] = current_map
    return dict(stored) == legacy


_SOURCE_RECORD_IDENTITY_STATUS_SOURCE_PATH_FIELDS = (
    "source_file",
    "human_source_file",
    "assumption_source_file",
)
_SOURCE_RECORD_IDENTITY_MAP_ARTIFACT_PATH_FIELDS = (
    "source_artifact_path",
    "canonical_source_artifact_path",
)


def _source_record_identity_map_artifact_values(value: object) -> list[str]:
    """Return schema-declared map artifact paths without name heuristics.

    This deliberately mirrors the raw source-record producer's structured
    source-artifact projection: canonical/source artifacts may occur at any
    map depth, while an ordinary ``path`` field is an artifact route only
    inside ``source_anchor_evidence``.  Lean declaration and map-item names do
    not participate in discovery.
    """

    values: list[str] = []
    if isinstance(value, list):
        for child in value:
            values.extend(_source_record_identity_map_artifact_values(child))
        return values
    if not isinstance(value, dict):
        return values
    for field in _SOURCE_RECORD_IDENTITY_MAP_ARTIFACT_PATH_FIELDS:
        raw = value.get(field)
        if isinstance(raw, str) and raw.strip():
            values.append(raw.strip())
    anchors = value.get("source_anchor_evidence")
    if isinstance(anchors, list):
        for anchor in anchors:
            if not isinstance(anchor, dict):
                continue
            raw = anchor.get("path")
            if isinstance(raw, str) and raw.strip():
                values.append(raw.strip())
    for child in value.values():
        if isinstance(child, (dict, list)):
            values.extend(_source_record_identity_map_artifact_values(child))
    return values


def _source_record_identity_trusted_candidates(
    folder: Path,
    raw_path: str,
    *,
    status_source: bool,
) -> tuple[set[Path], str]:
    """Resolve a declared path under the trusted checkout, or mark it unsafe.

    Map artifacts preserve the producer's paper-relative-then-repository-
    relative resolution and watch both safe candidates.  Watching a currently
    missing candidate is intentional: creating the higher-priority file must
    invalidate a cached producer result.  Status source routes use their
    schema's single-component paper-relative convention.
    """

    root = ROOT.resolve()
    relative = Path(raw_path)
    if relative.is_absolute():
        raw_candidates = [relative]
    elif status_source:
        raw_candidates = [
            folder / relative if len(relative.parts) == 1 else ROOT / relative
        ]
    else:
        raw_candidates = [folder / relative, ROOT / relative]
    candidates: set[Path] = set()
    rejected = False
    for raw_candidate in raw_candidates:
        try:
            candidate = raw_candidate.resolve()
            candidate.relative_to(root)
        except (OSError, RuntimeError, ValueError):
            rejected = True
            continue
        candidates.add(candidate)
    if candidates:
        marker = "partially-untrusted" if rejected else "trusted"
        return candidates, marker
    return set(), "untrusted"


def _source_record_identity_declared_watch_paths(
    folder: Path,
) -> tuple[set[Path], list[str]]:
    """Resolve all structured status/map source artifacts for memoization.

    Parse failures and unsafe routes are retained as digest markers rather
    than ignored.  The status/map bytes are also in the paper-tree watch, so a
    repair changes both the structural marker and the governing input bytes.
    """

    paths: set[Path] = set()
    markers: list[str] = []

    status_path = folder / "status.json"
    try:
        status = json.loads(status_path.read_bytes())
    except FileNotFoundError:
        status = None
        markers.append("status:missing")
    except (OSError, json.JSONDecodeError) as error:
        status = None
        markers.append(f"status:unreadable:{type(error).__name__}")
    review_surface = status.get("review_surface") if isinstance(status, dict) else None
    if isinstance(review_surface, dict):
        for field in _SOURCE_RECORD_IDENTITY_STATUS_SOURCE_PATH_FIELDS:
            raw = review_surface.get(field)
            if raw is None:
                continue
            if not isinstance(raw, str) or not raw.strip():
                markers.append(f"status:{field}:malformed")
                continue
            candidates, trust = _source_record_identity_trusted_candidates(
                folder, raw.strip(), status_source=True
            )
            paths.update(candidates)
            markers.append(f"status:{field}:{trust}:{raw.strip()}")
    elif isinstance(status, dict) and "review_surface" in status:
        markers.append("status:review_surface:malformed")

    map_path = canonical_sidecar(folder, "paper_statement_map.json")
    try:
        statement_map = json.loads(map_path.read_bytes())
    except FileNotFoundError:
        statement_map = None
        markers.append("map:missing")
    except (OSError, json.JSONDecodeError) as error:
        statement_map = None
        markers.append(f"map:unreadable:{type(error).__name__}")
    if isinstance(statement_map, dict):
        for raw in sorted(set(_source_record_identity_map_artifact_values(statement_map))):
            candidates, trust = _source_record_identity_trusted_candidates(
                folder, raw, status_source=False
            )
            paths.update(candidates)
            markers.append(f"map:artifact:{trust}:{raw}")
    elif statement_map is not None:
        markers.append("map:malformed")
    return paths, sorted(markers)


def _fingerprint_identity_watch_paths(
    audit_payload: Mapping[str, Any] | None,
) -> tuple[set[Path], list[str]]:
    """Resolve exact file coordinates already named by the raw fingerprint."""

    paths: set[Path] = set()
    markers: list[str] = []
    fingerprint = (
        audit_payload.get("source_record_input_fingerprint")
        if isinstance(audit_payload, Mapping)
        else None
    )
    if not isinstance(fingerprint, Mapping):
        return paths, ["fingerprint:missing"]

    identity_fields = (
        "audit_engine_identities",
        "raw_producer_code_identities",
        "lean_dependency_identities",
        "source_artifact_identities",
        "review_assumption_source",
        "review_interface_source",
        "toolchain_identities",
    )

    def collect(value: object) -> None:
        if isinstance(value, Mapping):
            raw_path = value.get("path")
            if isinstance(raw_path, str) and raw_path.strip():
                relative = raw_path.split("#", 1)[0].strip()
                candidate = Path(relative)
                try:
                    if candidate.is_absolute():
                        raise ValueError
                    resolved = (ROOT / candidate).resolve()
                    resolved.relative_to(ROOT.resolve())
                except (OSError, RuntimeError, ValueError):
                    markers.append("fingerprint:path-invalid:" + raw_path)
                else:
                    paths.add(resolved)
            for nested in value.values():
                collect(nested)
        elif isinstance(value, (list, tuple)):
            for nested in value:
                collect(nested)

    for field in identity_fields:
        collect(fingerprint.get(field))
    return paths, markers


def _source_record_identity_process_watch_digest(
    folder: Path,
    *,
    audit_payload: Mapping[str, Any] | None = None,
) -> str:
    """Hash exact semantic producer/source inputs for one evidence transaction.

    The source-record fingerprint and configured source/map routes define this
    envelope. Ignored dashboard caches, archival scratch files, and unrelated
    paper or audit modules are deliberately absent: they are neither consumed
    inputs nor authority and must not invalidate a successful closeout.
    """

    paths, fingerprint_markers = _fingerprint_identity_watch_paths(
        audit_payload
    )
    declared_paths, declared_markers = _source_record_identity_declared_watch_paths(
        folder
    )
    paths.update(declared_paths)
    paths.update(
        {
            ROOT / "config" / "formalization_audit_protocol.json",
            ROOT / "lean-toolchain",
            ROOT / "lake-manifest.json",
            ROOT / "lakefile.lean",
            ROOT / "lakefile.toml",
            ROOT / "papers" / f"{folder.name}.lean",
            Path(__file__).resolve(),
            ROOT
            / "skills"
            / "econcs-formalizer"
            / "scripts"
            / "source_record_audit.py",
        }
    )
    digest = hashlib.sha256()
    for marker in sorted((*fingerprint_markers, *declared_markers)):
        digest.update(b"declared\0")
        digest.update(marker.encode("utf-8", errors="surrogateescape"))
        digest.update(b"\0")
    for path in sorted(paths, key=lambda candidate: str(candidate)):
        try:
            display = str(path.resolve().relative_to(ROOT))
        except (OSError, RuntimeError, ValueError):
            display = str(path)
        digest.update(display.encode("utf-8", errors="surrogateescape"))
        digest.update(b"\0")
        try:
            content = path.read_bytes()
        except OSError:
            digest.update(b"<missing>\0")
            continue
        digest.update(str(len(content)).encode("ascii"))
        digest.update(b"\0")
        digest.update(hashlib.sha256(content).digest())
        digest.update(b"\0")
    return digest.hexdigest()


class SourceRecordIdentityRevalidationBusy(RuntimeError):
    """Raised when a fresh source-record scan owns the shared evidence lock."""


class SourceRecordIdentityContextDeferred(RuntimeError):
    """A live identity context could not be minted while a raw scan is busy."""


_CURRENT_SOURCE_RECORD_IDENTITY_CONTEXT_SENTINEL = object()
_SOURCE_RECORD_IDENTITY_REVALIDATION_DEFERRED_PREFIX = (
    "source-record identity revalidation deferred:"
)


@dataclass(frozen=True)
class _CurrentSourceRecordIdentityBinding:
    """Exact live inputs covered by one reusable current-identity result.

    This records only in-process verification inputs, not an evidence receipt.
    It deliberately includes both raw-file bytes and the parsed raw surface:
    callers often hold parsed JSON while a later write could otherwise leave
    the canonical file on disk different from the object that was checked.
    """

    paper_dir: Path
    paper: str
    current_raw_canonical_sha256: str
    current_source_record_audit_sha256: str
    raw_paper_statement_map_sha256: str
    canonical_raw_path: Path
    canonical_raw_file_sha256: str
    statement_map_path: Path
    live_paper_statement_map_sha256: str
    watched_input_digest: str


@dataclass(frozen=True)
class _CurrentSourceRecordIdentityContext:
    """Opaque, per-invocation capability for a checked canonical raw audit.

    It is intentionally private, nonserializable, and cannot be recreated by
    a JSON sidecar.  Reuse always recomputes the raw/map/watch binding below;
    it only avoids replaying the expensive external-artifact helper after that
    binding still proves the exact same live inputs.
    """

    binding: _CurrentSourceRecordIdentityBinding
    # The builder freezes this exact mapping after reading its byte-pinned
    # canonical source-record file.  Retaining object identity lets nested
    # checks avoid repeatedly canonicalizing a very large immutable JSON
    # payload, without granting the optimization to caller-supplied objects.
    raw_audit_payload: Mapping[str, Any] = dataclass_field(
        repr=False,
        compare=False,
    )
    _token: object = dataclass_field(repr=False, compare=False)


def _source_record_identity_context_sha256(value: object) -> str:
    """Return a canonical content digest for an in-memory JSON audit object."""

    try:
        encoded = json.dumps(
            canonical_digest_payload(value),
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    except (TypeError, ValueError):
        return ""
    return hashlib.sha256(encoded).hexdigest()


def _source_record_identity_context_hex(value: object) -> str:
    """Normalize one SHA-256 field without treating malformed text as a pin."""

    text = str(value or "").strip().lower()
    return text if SHA256_RE.fullmatch(text) else ""


def _current_source_record_identity_binding(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    *,
    watched_input_digest_override: str | None = None,
    trusted_canonical_raw_file_sha256: str | None = None,
) -> tuple[_CurrentSourceRecordIdentityBinding | None, str]:
    """Bind a supplied raw object to the canonical current raw/map/watch state.

    This is deliberately stricter than the ordinary identity helper's parsed
    receipt check: a reusable capability is allowed only for the canonical
    live raw file consumed by the current-paper workflow.  Historical raw
    paths remain on their existing replay path and never receive a context.
    """

    if not isinstance(current_raw_audit, Mapping):
        return None, "current source-record identity context raw audit is not an object"
    try:
        resolved_paper_dir = paper_dir.resolve()
    except (OSError, RuntimeError):
        return None, "current source-record identity context paper directory cannot be resolved"
    if resolved_paper_dir.name != paper:
        return None, "current source-record identity context paper directory belongs to another paper"
    if str(current_raw_audit.get("paper") or "").strip() != paper:
        return None, "current source-record identity context belongs to another paper"
    raw_digest = _source_record_identity_context_hex(
        current_raw_audit.get("source_record_audit_sha256")
    )
    raw_map_digest = _source_record_identity_context_hex(
        current_raw_audit.get("paper_statement_map_sha256")
    )
    if not raw_digest or not raw_map_digest:
        return None, "current source-record identity context raw audit lacks canonical receipts"

    canonical_raw_path = resolved_paper_dir / "audit" / "source_record_audit.json"
    try:
        canonical_raw_bytes = canonical_raw_path.read_bytes()
    except OSError as exc:
        return None, "current source-record identity context cannot read canonical raw audit: " + str(exc)
    canonical_raw_file_sha256 = hashlib.sha256(canonical_raw_bytes).hexdigest()
    trusted_file_digest = _source_record_identity_context_hex(
        trusted_canonical_raw_file_sha256
    )
    if trusted_file_digest:
        # This fast path is available only to the exact immutable object read
        # by ``build_evidence_run_context``.  Its raw bytes are still read and
        # rehashed on every check, so a changed canonical file cannot reuse a
        # context.  Other callers retain the complete parsed/canonical replay
        # below.
        if canonical_raw_file_sha256 != trusted_file_digest:
            return None, "current source-record identity context raw file changed"
        payload_digest = canonical_raw_file_sha256
    else:
        payload_digest = _source_record_identity_context_sha256(current_raw_audit)
        if not payload_digest:
            return None, "current source-record identity context raw audit lacks canonical receipts"
        try:
            canonical_raw = json.loads(canonical_raw_bytes)
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            return None, "current source-record identity context cannot read canonical raw audit: " + str(exc)
        if not isinstance(canonical_raw, Mapping):
            return None, "current source-record identity context canonical raw audit is not an object"
        if _source_record_identity_context_sha256(canonical_raw) != payload_digest:
            return None, "current source-record identity context raw audit is stale for canonical raw bytes"
        if _source_record_identity_context_hex(
            canonical_raw.get("source_record_audit_sha256")
        ) != raw_digest:
            return None, "current source-record identity context canonical raw receipt changed"

    statement_map_path = canonical_sidecar(resolved_paper_dir, "paper_statement_map.json")
    try:
        statement_map_bytes = statement_map_path.read_bytes()
    except OSError as exc:
        return None, "current source-record identity context cannot read paper statement map: " + str(exc)
    live_map_digest = hashlib.sha256(statement_map_bytes).hexdigest()
    watched_input_digest = (
        watched_input_digest_override.strip()
        if isinstance(watched_input_digest_override, str)
        and watched_input_digest_override.strip()
        else _source_record_identity_process_watch_digest(
            resolved_paper_dir,
            audit_payload=current_raw_audit,
        )
    )
    if not watched_input_digest:
        return None, "current source-record identity context has no watched-input digest"
    return (
        _CurrentSourceRecordIdentityBinding(
            paper_dir=resolved_paper_dir,
            paper=paper,
            current_raw_canonical_sha256=payload_digest,
            current_source_record_audit_sha256=raw_digest,
            raw_paper_statement_map_sha256=raw_map_digest,
            canonical_raw_path=canonical_raw_path,
            canonical_raw_file_sha256=canonical_raw_file_sha256,
            statement_map_path=statement_map_path,
            live_paper_statement_map_sha256=live_map_digest,
            watched_input_digest=watched_input_digest,
        ),
        "",
    )


def current_source_record_identity_context_error(
    context: object,
    *,
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    expected_paper_statement_map_sha256: str | None = None,
) -> str:
    """Reject a reusable identity capability unless every live binding agrees.

    This helper intentionally does *not* replay the external identity helper.
    Its caller can only reach this point through an opaque capability minted by
    :func:`prepare_current_source_record_identity_context` or the exact
    evidence transaction builder.  It rechecks canonical raw bytes, the live
    statement map, and the complete producer/source watch before each reuse.
    """

    if not isinstance(context, _CurrentSourceRecordIdentityContext):
        return "current source-record identity context is not a private capability"
    if context._token is not _CURRENT_SOURCE_RECORD_IDENTITY_CONTEXT_SENTINEL:
        return "current source-record identity context lacks issuer authority"
    # Reuse races the same producer that mints canonical raw receipts.  Hold a
    # nonblocking shared lock across every live read and the non-external
    # replay below, so a producer cannot begin an exclusive publication after
    # the raw/map/watch binding has been sampled.  Lock contention is neither
    # an empty optional lane nor an authorization; callers must retry.
    try:
        with _source_record_identity_read_lock(ROOT):
            return _current_source_record_identity_context_locked_error(
                context,
                paper_dir=paper_dir,
                paper=paper,
                current_raw_audit=current_raw_audit,
                expected_paper_statement_map_sha256=(
                    expected_paper_statement_map_sha256
                ),
            )
    except SourceRecordIdentityRevalidationBusy as exc:
        return "source-record identity revalidation deferred: " + str(exc)


def _current_source_record_identity_context_locked_error(
    context: _CurrentSourceRecordIdentityContext,
    *,
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    expected_paper_statement_map_sha256: str | None,
) -> str:
    """Revalidate an already-authenticated context while the producer is blocked."""

    trusted_raw_file_sha256 = (
        context.binding.canonical_raw_file_sha256
        if (
            current_raw_audit is context.raw_audit_payload
            # The builder's fast binding deliberately stores the exact
            # byte-file digest in this field.  Contexts issued through the
            # public compatibility helper retain the canonical JSON digest
            # and must keep using the full replay.
            and context.binding.current_raw_canonical_sha256
            == context.binding.canonical_raw_file_sha256
        )
        else None
    )
    live_binding, binding_error = _current_source_record_identity_binding(
        paper_dir,
        paper,
        current_raw_audit,
        trusted_canonical_raw_file_sha256=trusted_raw_file_sha256,
    )
    if binding_error:
        return binding_error
    assert live_binding is not None
    if live_binding != context.binding:
        return "current source-record identity context is stale for live raw/map/watch inputs"
    if expected_paper_statement_map_sha256 is not None:
        expected = _source_record_identity_context_hex(
            expected_paper_statement_map_sha256
        )
        if not expected:
            return "current source-record identity context received a malformed expected statement-map digest"
        if expected != live_binding.live_paper_statement_map_sha256:
            return "current source-record identity context does not match the expected statement map"
    # A builder-issued fast binding already passed the complete identity gate
    # for this immutable snapshot.  The raw-file byte hash, live map hash,
    # producer/source watch digest, and the transaction's final input-mutation
    # check above/below retain its fail-closed coverage without recomputing the
    # multi-megabyte aggregate receipt for every nested overlay.  Public
    # compatibility contexts retain their canonical JSON digest and keep the
    # complete non-external replay.
    if trusted_raw_file_sha256:
        return ""

    # Re-run the non-external portion of the ordinary identity gate as well
    # for contexts not issued from an exact frozen builder snapshot.
    nonexternal_error = _source_record_audit_identity_error(
        dict(current_raw_audit),
        expected_paper_statement_map_sha256=(
            live_binding.live_paper_statement_map_sha256
        ),
        folder=live_binding.paper_dir,
        prevalidated_current_input_fingerprint_error="",
    )
    if nonexternal_error:
        return "current source-record identity context non-external replay failed: " + nonexternal_error
    return ""


def _issue_current_source_record_identity_context(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
    *,
    source_record_identity_error: str,
    watched_input_digest: str | None = None,
    trusted_canonical_raw_file_sha256: str | None = None,
) -> object | None:
    """Issue a runtime-only context after a caller already ran the strict gate."""

    if source_record_identity_error:
        return None
    binding, binding_error = _current_source_record_identity_binding(
        paper_dir,
        paper,
        current_raw_audit,
        watched_input_digest_override=watched_input_digest,
        trusted_canonical_raw_file_sha256=trusted_canonical_raw_file_sha256,
    )
    if binding_error or binding is None:
        return None
    return _CurrentSourceRecordIdentityContext(
        binding=binding,
        raw_audit_payload=current_raw_audit,
        _token=_CURRENT_SOURCE_RECORD_IDENTITY_CONTEXT_SENTINEL,
    )


def prepare_current_source_record_identity_context(
    paper_dir: Path,
    paper: str,
    current_raw_audit: Mapping[str, Any],
) -> object | None:
    """Run one strict current identity gate and return an opaque reusable result.

    The capability is scoped to this Python invocation only.  It is never put
    in a receipt and a later invocation must rerun the strict helper.  A
    transient lock conflict is surfaced explicitly so optional overlay callers
    cannot mistake it for an absent lane.
    """

    before, binding_error = _current_source_record_identity_binding(
        paper_dir,
        paper,
        current_raw_audit,
    )
    if binding_error or before is None:
        return None
    identity_error = source_record_audit_identity_error(
        dict(current_raw_audit),
        expected_paper_statement_map_sha256=(
            before.live_paper_statement_map_sha256
        ),
        folder=before.paper_dir,
    )
    if identity_error:
        if identity_error.strip().startswith(
            _SOURCE_RECORD_IDENTITY_REVALIDATION_DEFERRED_PREFIX
        ):
            raise SourceRecordIdentityContextDeferred(identity_error)
        return None
    after, after_error = _current_source_record_identity_binding(
        paper_dir,
        paper,
        current_raw_audit,
    )
    if after_error or after is None or after != before:
        return None
    return _CurrentSourceRecordIdentityContext(
        binding=after,
        raw_audit_payload=current_raw_audit,
        _token=_CURRENT_SOURCE_RECORD_IDENTITY_CONTEXT_SENTINEL,
    )


@contextmanager
def _source_record_identity_read_lock(root: Path):
    """Hold the producer's shared lock during one strict identity replay.

    A fresh raw source-record scan holds this lock exclusively because it may
    build Lean modules and publish a new raw receipt.  The evidence gate cannot
    safely call a receipt current while that work is in flight, and competing
    for the same Lake and artifact I/O made an otherwise read-only gate appear
    to hang.  A nonblocking shared lock preserves the raw producer's authority
    without importing it (which would create an import cycle).
    """

    lock_path = root.resolve() / SOURCE_RECORD_AUDIT_LOCK_RELATIVE_PATH
    try:
        lock_path.parent.mkdir(parents=True, exist_ok=True)
        handle = lock_path.open("a+", encoding="utf-8")
    except OSError as exc:
        raise SourceRecordIdentityRevalidationBusy(
            "could not open the repository source-record evidence lock: " + str(exc)
        ) from exc
    try:
        try:
            fcntl.flock(handle.fileno(), fcntl.LOCK_SH | fcntl.LOCK_NB)
        except BlockingIOError as exc:
            raise SourceRecordIdentityRevalidationBusy(
                "a fresh source-record scan currently owns the repository evidence "
                "lock; wait for that scan to finish, then rerun this evidence gate once"
            ) from exc
        try:
            yield
        finally:
            fcntl.flock(handle.fileno(), fcntl.LOCK_UN)
    finally:
        handle.close()


def _source_record_identity_external_module_count(
    audit_payload: Mapping[str, Any],
) -> int:
    """Return an informational count without trusting it as audit evidence."""

    closure = audit_payload.get("lean_import_closure")
    modules = (
        closure.get("external_import_modules")
        if isinstance(closure, Mapping)
        else None
    )
    return len(modules) if isinstance(modules, list) else 0


@contextmanager
def _source_record_identity_progress(
    folder: Path,
    audit_payload: Mapping[str, Any],
):
    """Emit bounded stderr progress around a strict identity subprocess.

    The helper emits one JSON object only on completion.  Its exact external
    artifact revalidation can therefore be I/O-heavy without producing stdout
    for tens of seconds.  These stderr messages are deliberately diagnostic;
    the helper's JSON and the evidence decision remain unchanged.
    """

    started = time.monotonic()
    module_count = _source_record_identity_external_module_count(audit_payload)
    scope = (
        f"{module_count} external module artifact(s)"
        if module_count
        else "the saved external artifact closure"
    )
    print(
        "audit-evidence: strict source-record identity revalidation for "
        f"{folder.name} started ({scope}; timeout "
        f"{SOURCE_RECORD_IDENTITY_HELPER_TIMEOUT_SECONDS}s)",
        file=sys.stderr,
        flush=True,
    )
    stopped = threading.Event()

    def heartbeat() -> None:
        interval = max(SOURCE_RECORD_IDENTITY_PROGRESS_HEARTBEAT_SECONDS, 0.1)
        while not stopped.wait(interval):
            print(
                "audit-evidence: strict source-record identity revalidation for "
                f"{folder.name} still running "
                f"({time.monotonic() - started:.0f}s elapsed; {scope})",
                file=sys.stderr,
                flush=True,
            )

    worker = threading.Thread(
        target=heartbeat,
        name="audit-evidence-identity-progress",
        daemon=True,
    )
    worker.start()
    try:
        yield
    finally:
        stopped.set()
        worker.join(timeout=max(SOURCE_RECORD_IDENTITY_PROGRESS_HEARTBEAT_SECONDS, 0.1) + 1)
        print(
            "audit-evidence: strict source-record identity revalidation for "
            f"{folder.name} finished ({time.monotonic() - started:.1f}s elapsed)",
            file=sys.stderr,
            flush=True,
        )


def _source_record_fingerprint_matches_current(
    stored: object,
    current: object,
) -> bool:
    """Match a raw fingerprint using only registered producer compatibility.

    Exact equality is always the ordinary path. A differing raw-producer
    provenance can be accepted only after the formalization engine is clean,
    committed, and registered; then the ledger grant still requires equality
    of every non-producer fingerprint component. This helper is deliberately
    shared in meaning with the raw producer's aggregate-cache check.
    """

    if (
        isinstance(stored, Mapping)
        and isinstance(current, Mapping)
        and dict(stored) == dict(current)
    ):
        return True
    if not (
        isinstance(stored, Mapping)
        and isinstance(current, Mapping)
        and stored.get("schema") == 10
        and current.get("schema") == 10
        and "raw_producer_code_identity_schema" in stored
        and "raw_producer_code_identities" in stored
        and "raw_producer_code_identity_schema" in current
        and "raw_producer_code_identities" in current
    ):
        return False
    if (
        fingerprint_without_raw_producer_provenance(stored)
        != fingerprint_without_raw_producer_provenance(current)
    ):
        return False
    try:
        ledger = validated_runtime_raw_producer_compatibility_ledger(ROOT)
    except EngineRevisionError:
        return False
    return source_record_fingerprint_matches_with_raw_producer_compatibility(
        stored,
        current,
        ledger=ledger,
    )


def _source_record_current_input_fingerprint_error(
    folder: Path,
    audit_payload: dict[str, Any],
    *,
    verify_watch_inputs: bool,
) -> str:
    """Compare a v10 raw audit with the current no-Lean generator identity.

    Importing the source-record helper here would cycle back through this
    evidence module.  Its ``--identity-only`` mode performs the same
    fingerprint computation without a Lean scan, cache lookup, or file write;
    this caller adds a cooperative read lock around that subprocess.  The
    stored options are replayed exactly, so an artifact generated with a
    nondefault recursion bound or ``--no-lean`` cannot be checked under a
    silently different identity.
    """

    stored = audit_payload.get("source_record_input_fingerprint")
    if not isinstance(stored, dict):
        return "source_record_input_fingerprint is missing or malformed"
    max_depth = stored.get("max_depth")
    no_lean = stored.get("no_lean")
    if not isinstance(max_depth, int) or max_depth < 0:
        return "source_record_input_fingerprint has malformed max_depth"
    if not isinstance(no_lean, bool):
        return "source_record_input_fingerprint has malformed no_lean"
    if no_lean:
        return (
            "source_record_input_fingerprint records --no-lean; evidence requires "
            "a full successful Lean scan"
        )
    helper = ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
    if not helper.is_file():
        return "source-record identity helper is unavailable"
    command = [
        sys.executable,
        str(helper),
        "--root",
        str(ROOT),
        "--paper",
        folder.name,
        "--identity-only",
        "--max-depth",
        str(max_depth),
    ]
    # Current schema-10 fingerprints already carry the split coverage-protocol
    # identity. Older receipts need the helper's exact compatibility projections.
    if not schema_version_is_exact(stored.get("schema"), 10):
        command.append("--include-legacy-fingerprint")
    if no_lean:
        command.append("--no-lean")
    try:
        with _source_record_identity_read_lock(ROOT):
            watch_before = (
                _source_record_identity_process_watch_digest(
                    folder, audit_payload=audit_payload
                )
                if verify_watch_inputs
                else ""
            )
            with _source_record_identity_progress(folder, audit_payload):
                proc = subprocess.run(
                    command,
                    cwd=ROOT,
                    text=True,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    check=False,
                    timeout=SOURCE_RECORD_IDENTITY_HELPER_TIMEOUT_SECONDS,
                )
            if verify_watch_inputs:
                watch_after = _source_record_identity_process_watch_digest(
                    folder, audit_payload=audit_payload
                )
                if watch_after != watch_before:
                    return "source-record identity inputs changed while the helper was running"
    except SourceRecordIdentityRevalidationBusy as exc:
        return "source-record identity revalidation deferred: " + str(exc)
    except subprocess.TimeoutExpired:
        return (
            "source-record identity helper timed out after "
            f"{SOURCE_RECORD_IDENTITY_HELPER_TIMEOUT_SECONDS}s during strict "
            "external-artifact verification; no evidence result was accepted. "
            "Wait for concurrent Lake/source-record work to finish, then rerun "
            "this evidence gate once"
        )
    except OSError as exc:
        return f"source-record identity helper could not run: {exc}"
    if proc.returncode != 0:
        detail = " ".join(proc.stderr.split())[-500:]
        return (
            "source-record identity helper failed"
            + (": " + detail if detail else "")
        )
    try:
        current_payload = json.loads(proc.stdout)
    except json.JSONDecodeError:
        return "source-record identity helper did not emit a JSON object"
    if not isinstance(current_payload, dict):
        return "source-record identity helper did not emit a JSON object"
    if current_payload.get("paper") != folder.name:
        return "source-record identity helper returned a paper mismatch"
    current = current_payload.get("source_record_input_fingerprint")
    if not isinstance(current, dict):
        return "source-record identity helper returned no input fingerprint"
    current_map = str(current_payload.get("paper_statement_map_sha256") or "").strip()
    recorded_map = str(audit_payload.get("paper_statement_map_sha256") or "").strip()
    fingerprint_matches = _source_record_fingerprint_matches_current(
        stored,
        current,
    )
    legacy_v9 = current_payload.get("legacy_v9_source_record_input_fingerprint")
    legacy_v9_fingerprint_matches = (
        schema_version_is_exact(current.get("schema"), 10)
        and schema_version_is_exact(stored.get("schema"), 9)
        and isinstance(legacy_v9, dict)
        and schema_version_is_exact(legacy_v9.get("schema"), 9)
        and legacy_v9 == stored
    )
    legacy_v7 = current_payload.get("legacy_v7_source_record_input_fingerprint")
    # Older identity-only helpers emitted a v7 current fingerprint directly.
    # Retain that narrow compatibility for pre-projection test/receipt paths;
    # a schema-8 current identity without the explicit compatibility field
    # never gains legacy acceptance by guesswork.
    if not isinstance(legacy_v7, dict) and schema_version_is_exact(current.get("schema"), 7):
        legacy_v7 = current
    legacy_v7_is_current = isinstance(
        legacy_v7, dict
    ) and source_record_legacy_v7_fingerprint_is_current(legacy_v7, current)
    legacy_v7_fingerprint_matches = legacy_v7_is_current and legacy_v7 == stored
    legacy_v6_fingerprint_matches = legacy_v7_is_current and source_record_legacy_v6_fingerprint_matches_current(
        stored,
        legacy_v7,
        recorded_map_sha256=recorded_map,
        current_map_sha256=current_map,
    )
    selected_surface_rebind_matches = False
    if not (
        fingerprint_matches
        or legacy_v9_fingerprint_matches
        or legacy_v7_fingerprint_matches
        or legacy_v6_fingerprint_matches
    ):
        transition_error = validate_source_record_partial_to_formalized_transition(
            root=ROOT,
            paper=folder.name,
            paper_dir=folder,
            raw_audit=audit_payload,
            current_input_fingerprint=current,
        )
        if transition_error:
            # This optional receipt is deliberately a final fallback. It
            # reconstructs selected source content and the actual dependency
            # surface, rather than treating a source-map key or declaration
            # name as an identity.
            try:
                selected_rebind, _selected_rebind_path, selected_rebind_error = (
                    selected_surface_rebind_context(
                        root=ROOT,
                        paper=folder.name,
                        paper_dir=folder,
                        raw_audit=audit_payload,
                        current_input_fingerprint=current,
                    )
                )
            except Exception as error:  # noqa: BLE001 - rebinds fail closed.
                selected_rebind = None
                selected_rebind_error = (
                    "selected-surface rebind validation raised "
                    f"{type(error).__name__}: {error}"
                )
            selected_surface_rebind_matches = (
                selected_rebind is not None and not selected_rebind_error
            )
            if not selected_surface_rebind_matches:
                rebind_detail = (
                    selected_rebind_error
                    or "selected-surface rebind is not installed"
                )
                return (
                    "source_record_input_fingerprint is stale for current source or "
                    "audit-engine inputs; partial-to-formalized transition rejected: "
                    + transition_error
                    + "; selected-surface rebind rejected: "
                    + rebind_detail
                )
    matched_fingerprint = legacy_v9 if legacy_v9_fingerprint_matches else current
    current_semantic_map = str(
        matched_fingerprint.get("paper_statement_map_semantic_sha256") or ""
    ).strip().lower()
    recorded_semantic_map = str(
        stored.get("paper_statement_map_semantic_sha256") or ""
    ).strip().lower()
    if current_map != recorded_map and not (
        SHA256_RE.fullmatch(current_semantic_map)
        and current_semantic_map == recorded_semantic_map
    ) and not selected_surface_rebind_matches:
        return "source-record identity helper disagrees with paper_statement_map_sha256"
    return ""


def source_record_current_input_fingerprint_error(
    folder: Path,
    audit_payload: dict[str, Any],
) -> str:
    """Validate current generator identity with a standalone TOCTOU watch."""

    return _source_record_current_input_fingerprint_error(
        folder,
        audit_payload,
        verify_watch_inputs=True,
    )


def _source_record_audit_identity_error(
    audit_payload: dict[str, Any],
    *,
    expected_paper_statement_map_sha256: str | None = None,
    folder: Path | None = None,
    prevalidated_current_input_fingerprint_error: str | None = None,
    semantic_contract_revalidation: Any | None = None,
    prevalidated_semantic_contract_revalidation_error: str | None = None,
) -> str:
    """Return a freshness error for a saved source-record audit, if any.

    The generator's aggregate digest and source-map byte pin are both part of
    the semantic review identity.  Do not treat two absent strings as a
    matching digest, and require the map pin for v10 artifacts even when no
    individual judgment happens to carry a reusable item digest.
    """

    audit_digest = str(audit_payload.get("source_record_audit_sha256") or "").strip()
    if not audit_digest:
        return "source_record_audit_sha256 is missing or blank"

    current_source_record_surface = (
        str(audit_payload.get("source_record_policy_version") or "").strip()
        == CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
        or str(audit_payload.get("prompt_version") or "").strip()
        == CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
    )
    if current_source_record_surface:
        integrity_error = source_record_audit_receipt_error(audit_payload)
        if integrity_error:
            return integrity_error
        correction_error = prevalidated_semantic_contract_revalidation_error
        projection = _trusted_semantic_contract_revalidation_projection(
            semantic_contract_revalidation
        )
        if correction_error is None and projection is None and folder is not None:
            projection, correction_error = (
                source_record_semantic_contract_revalidation_context(
                    folder, audit_payload
                )
            )
        if correction_error:
            return "semantic-contract revalidation is invalid: " + correction_error
        raw_semantic_error = source_record_effective_semantic_surface_error(
            audit_payload,
            semantic_contract_revalidation=projection,
        )
        if raw_semantic_error:
            return raw_semantic_error
        scan_error = source_record_raw_scan_completeness_error(audit_payload)
        if scan_error:
            return scan_error
        raw_item_error = source_record_raw_reusable_item_metadata_error(audit_payload)
        if raw_item_error:
            return raw_item_error
        if folder is not None:
            fingerprint_error = prevalidated_current_input_fingerprint_error
            if fingerprint_error is None:
                fingerprint_error = source_record_current_input_fingerprint_error(
                    folder, audit_payload
                )
            if fingerprint_error:
                return fingerprint_error
            if "source_record_direct_route_diagnostic_rebind" in audit_payload:
                # This narrow transport changes a current raw receipt without
                # a Lean/source scan only after replaying its archived raw and
                # exact current source-contract routes.  Import lazily: the
                # rebind validator itself uses this module's contract checks.
                try:
                    from scripts.source_record_diagnostic_rebind import (
                        direct_route_diagnostic_rebind_error,
                    )

                    rebind_error = direct_route_diagnostic_rebind_error(
                        root=folder.parents[1],
                        paper=str(audit_payload.get("paper") or ""),
                        paper_dir=folder,
                        raw_audit=audit_payload,
                    )
                except Exception as error:  # noqa: BLE001 - rebinds fail closed.
                    return (
                        "could not validate direct-route diagnostic rebind: "
                        f"{type(error).__name__}: {error}"
                    )
                if rebind_error:
                    return "direct-route diagnostic rebind is invalid: " + rebind_error

    requires_map_pin = (
        "paper_statement_map_sha256" in audit_payload
        or current_source_record_surface
    )
    if not requires_map_pin or expected_paper_statement_map_sha256 is None:
        return ""

    expected = expected_paper_statement_map_sha256.strip().lower()
    recorded = str(audit_payload.get("paper_statement_map_sha256") or "").strip().lower()
    if not SHA256_RE.fullmatch(expected):
        return "current paper_statement_map.json is missing or unreadable"
    if not SHA256_RE.fullmatch(recorded):
        return "paper_statement_map_sha256 is missing or malformed"
    if recorded != expected:
        stored_fingerprint = audit_payload.get("source_record_input_fingerprint")
        recorded_semantic = (
            str(
                stored_fingerprint.get("paper_statement_map_semantic_sha256")
                or ""
            ).strip().lower()
            if isinstance(stored_fingerprint, Mapping)
            else ""
        )
        current_semantic = (
            current_paper_statement_map_semantic_sha256(folder)
            if folder is not None
            else ""
        )
        if (
            SHA256_RE.fullmatch(recorded_semantic)
            and recorded_semantic == current_semantic
        ):
            return ""
        # A differing semantic map receipt rules out normal exact and v6
        # identity reuse. The transition validator also requires every
        # non-status fingerprint field (including this map receipt) to match.
        # Recheck the optional content-addressed receipt only at this final
        # map-pin boundary, after the ordinary identity path above succeeded.
        if (
            folder is not None
            and current_paper_statement_map_sha256(folder) == expected
        ):
            try:
                selected_rebind, _selected_rebind_path, selected_rebind_error = (
                    selected_surface_rebind_context(
                        root=ROOT,
                        paper=folder.name,
                        paper_dir=folder,
                        raw_audit=audit_payload,
                    )
                )
            except Exception as error:  # noqa: BLE001 - rebinds fail closed.
                selected_rebind = None
                selected_rebind_error = (
                    "selected-surface rebind validation raised "
                    f"{type(error).__name__}: {error}"
                )
            if selected_rebind is not None and not selected_rebind_error:
                return ""
        return "paper_statement_map_sha256 is stale for the current paper_statement_map.json"
    return ""


def source_record_audit_identity_error(
    audit_payload: dict[str, Any],
    *,
    expected_paper_statement_map_sha256: str | None = None,
    folder: Path | None = None,
    semantic_contract_revalidation: Any | None = None,
    prevalidated_semantic_contract_revalidation_error: str | None = None,
) -> str:
    """Validate a raw receipt without accepting caller-supplied authorization."""

    return _source_record_audit_identity_error(
        audit_payload,
        expected_paper_statement_map_sha256=expected_paper_statement_map_sha256,
        folder=folder,
        semantic_contract_revalidation=semantic_contract_revalidation,
        prevalidated_semantic_contract_revalidation_error=(
            prevalidated_semantic_contract_revalidation_error
        ),
    )


def source_record_raw_semantic_surface_error(audit_payload: dict[str, Any]) -> str:
    """Reject generated route/configuration errors before evidence gets credit.

    A raw v10 audit is allowed to *report* an unresolved semantic-model or
    source-contract routing error.  It is not allowed to support an evidence
    gate while that error remains.  This is structural generator output, not a
    judgement about a theorem or the spelling of a declaration.
    """

    target_route_error = source_record_target_route_error(audit_payload)
    if target_route_error:
        return target_route_error
    error_fields = (
        "semantic_model_review_configuration_errors",
        "source_contract_association_errors",
        "source_coverage_route_errors",
        "elaborated_review_signature_errors",
        "elaborated_result_input_path_errors",
        "conclusion_dependency_input_atom_errors",
        "recursive_field_proposition_sort_errors",
        "constructor_field_slot_reconciliation_errors",
        "type_witness_payload_safety_errors",
    )
    for field in error_fields:
        raw_errors = audit_payload.get(field)
        if raw_errors in (None, [], {}, ""):
            continue
        if isinstance(raw_errors, list):
            rendered = "; ".join(str(error) for error in raw_errors[:3])
        else:
            rendered = str(raw_errors)
        return f"generated `{field}` is nonempty: {rendered}"
    return ""


def source_record_effective_semantic_surface_error(
    audit_payload: Mapping[str, Any],
    *,
    semantic_contract_revalidation: Any | None = None,
) -> str:
    """Check a raw semantic surface after one authenticated structural replay.

    Keep ``source_record_raw_semantic_surface_error`` unchanged for the raw
    producer.  Only evidence consumers may replace the two representation-only
    fields through an explicitly validated, byte-pinned projection.
    """

    target_route_error = source_record_target_route_error(audit_payload)
    if target_route_error:
        return target_route_error
    effective_errors = source_record_effective_semantic_errors(
        audit_payload,
        semantic_contract_revalidation=semantic_contract_revalidation,
    )
    error_fields = (
        "semantic_model_review_configuration_errors",
        "source_contract_association_errors",
        "source_coverage_route_errors",
        "elaborated_review_signature_errors",
        "elaborated_result_input_path_errors",
        "conclusion_dependency_input_atom_errors",
        "recursive_field_proposition_sort_errors",
        "constructor_field_slot_reconciliation_errors",
        "type_witness_payload_safety_errors",
    )
    for field in error_fields:
        raw_errors = effective_errors.get(field, audit_payload.get(field))
        if raw_errors in (None, [], {}, ""):
            continue
        if isinstance(raw_errors, list):
            rendered = "; ".join(str(error) for error in raw_errors[:3])
        else:
            rendered = str(raw_errors)
        return f"generated `{field}` is nonempty: {rendered}"
    return ""


def source_record_effective_semantic_errors(
    audit_payload: Mapping[str, Any],
    *,
    semantic_contract_revalidation: Any | None = None,
) -> Mapping[str, list[str]]:
    """Return the two replayable raw error fields after authentication."""

    projection = _trusted_semantic_contract_revalidation_projection(
        semantic_contract_revalidation
    )
    replay = _semantic_contract_revalidation_module()
    return replay.effective_source_record_semantic_errors(
        audit_payload, projection
    )


def source_record_raw_scan_completeness_error(audit_payload: dict[str, Any]) -> str:
    """Reject v10 audit records that did not complete their generator checks.

    A receipt binds what was serialized; it cannot by itself show that the
    generator actually ran the mandatory current-source Lean pass or finished
    its structural scans.  This validation is intentionally about generated
    evidence states (row coverage, recursion, constructor typing, and
    source-premise consistency), not declaration spelling or function names.
    """

    fingerprint = audit_payload.get("source_record_input_fingerprint")
    if not isinstance(fingerprint, dict):
        return "source_record_input_fingerprint is missing or malformed"
    if fingerprint.get("no_lean") is not False:
        return (
            "source_record_input_fingerprint must record no_lean=false for "
            "evidence-bearing audits"
        )

    missing_rows = audit_payload.get("missing_configured_review_rows")
    if not isinstance(missing_rows, list):
        return "generated `missing_configured_review_rows` is not a list"
    if any(not isinstance(row, str) or not row.strip() for row in missing_rows):
        return "generated `missing_configured_review_rows` is malformed"
    if missing_rows:
        return "generated `missing_configured_review_rows` is nonempty"

    configured_rows = audit_payload.get("configured_review_rows")
    if not isinstance(configured_rows, list):
        return "generated `configured_review_rows` is not a list"
    configured_rows_count = audit_payload.get("configured_review_rows_count")
    if type(configured_rows_count) is not int or configured_rows_count != len(
        configured_rows
    ):
        return "generated configured-review-row count does not match its row metadata"
    configured_row_count = audit_payload.get("configured_review_row_count")
    if type(configured_row_count) is not int or configured_row_count < len(
        configured_rows
    ):
        return "generated configured review-surface count is malformed"

    recursion_failures = audit_payload.get("recursion_failures")
    if not isinstance(recursion_failures, list):
        return "generated `recursion_failures` is not a list"
    recursion_failure_count = audit_payload.get("recursion_failure_count")
    if type(recursion_failure_count) is not int:
        return "generated `recursion_failure_count` is missing or malformed"
    if recursion_failure_count != len(recursion_failures):
        return "generated recursion failure count does not match its failure list"
    if recursion_failures:
        return "generated `recursion_failures` is nonempty"

    constructor_error = audit_payload.get("constructor_result_type_check_error")
    if not isinstance(constructor_error, str):
        return "generated `constructor_result_type_check_error` is malformed"
    if constructor_error.strip():
        return "generated `constructor_result_type_check_error` is nonempty"

    if not schema_version_is_exact(
        audit_payload.get("source_premise_consistency_schema"), 1
    ):
        return "generated source-premise consistency scan has an unsupported schema"
    premise_error = audit_payload.get("source_premise_consistency_error")
    if not isinstance(premise_error, str):
        return "generated `source_premise_consistency_error` is malformed"
    if premise_error.strip():
        return "generated `source_premise_consistency_error` is nonempty"
    premise_items = audit_payload.get("source_premise_consistency_items")
    if not isinstance(premise_items, list):
        return "generated `source_premise_consistency_items` is not a list"
    premise_item_count = audit_payload.get("source_premise_consistency_item_count")
    if type(premise_item_count) is not int or premise_item_count != len(premise_items):
        return "generated source-premise consistency item count is malformed"

    lean_check = audit_payload.get("lean_check")
    if not isinstance(lean_check, dict):
        return "generated `lean_check` is missing or malformed"
    if type(lean_check.get("returncode")) is not int or lean_check.get("returncode") != 0:
        return "generated `lean_check` did not complete successfully"
    requested_rows = lean_check.get("requested_checked_rows")
    checked_rows = lean_check.get("checked_rows")
    if not isinstance(requested_rows, list) or not isinstance(checked_rows, list):
        return "generated `lean_check` lacks checked-row coverage metadata"
    if requested_rows != checked_rows:
        return "generated `lean_check` did not check every selected review row"

    review_row_count = audit_payload.get("review_row_count")
    recursive_field_count = audit_payload.get("recursive_field_count")
    if type(review_row_count) is not int or type(recursive_field_count) is not int:
        return "generated review-row or recursive-field count is malformed"
    if review_row_count != len(configured_rows):
        return "generated review-row count does not match configured-row metadata"
    zero_scan = not requested_rows and not checked_rows
    if zero_scan:
        if lean_check.get("command") != "skipped Lean check: no source-record rows or fields":
            return "generated `lean_check` skipped rows without the zero-surface sentinel"
        if review_row_count != 0 or recursive_field_count != 0:
            return "generated `lean_check` skipped a nonempty review surface"
        fresh = audit_payload.get("fresh_source_elaboration")
        if not isinstance(fresh, dict) or fresh.get("mode") != "not_run_without_lean":
            return "generated zero-surface Lean check lacks its explicit skip record"
        return ""

    # A nonempty selected surface must have elaborated the current source in
    # the isolated overlay.  A successful ordinary Lake build is insufficient:
    # it could otherwise be served by an old compiled artifact.
    fresh = lean_check.get("fresh_source_elaboration")
    top_fresh = audit_payload.get("fresh_source_elaboration")
    if not isinstance(fresh, dict) or not isinstance(top_fresh, dict):
        return "generated `lean_check` lacks fresh current-source elaboration evidence"
    for field, expected in (
        ("mode", "isolated_temp_overlay"),
        ("returncode", 0),
    ):
        if fresh.get(field) != expected or top_fresh.get(field) != expected:
            return "generated fresh current-source elaboration did not complete successfully"
    interface_source = audit_payload.get("review_interface_source")
    if not isinstance(interface_source, dict):
        return "generated review-interface source identity is missing or malformed"
    source_file = str(interface_source.get("path") or "").strip()
    source_sha256 = str(interface_source.get("sha256") or "").strip().lower()
    if not source_file or not SHA256_RE.fullmatch(source_sha256):
        return "generated review-interface source identity is incomplete"
    for elaboration in (fresh, top_fresh):
        if (
            str(elaboration.get("source_file") or "").strip() != source_file
            or str(elaboration.get("source_sha256") or "").strip().lower()
            != source_sha256
        ):
            return "generated fresh elaboration does not match the reviewed source identity"
    return ""


def source_record_raw_reusable_item_metadata_error(
    audit_payload: dict[str, Any],
) -> str:
    """Validate all generated v10 item receipts that claim narrow reuse."""

    return _raw_item_metadata_error(
        audit_payload,
        expected_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
    )


def semantic_model_judgment_completeness_errors(
    item: dict[str, Any], judgment: dict[str, Any]
) -> list[str]:
    """Return missing semantic-model evidence before freshness is credited.

    ``audit_repository.py`` supplies detailed diagnostics for these judgments.
    The fast evidence gate must nevertheless reject a sidecar that merely
    attaches a current digest to an unrelated classification: otherwise a
    lightweight CI path can call an incomplete semantic-model review current.
    """

    errors: list[str] = []
    if (
        str(judgment.get("classification") or "").strip()
        != SEMANTIC_MODEL_REVIEW_CLASSIFICATION
    ):
        return ["classification must be `semantic_model_review`"]
    # Structural source-process patterns remain diagnostic outside an explicit
    # source-pinned source_model_derivation dimension. That opt-in dimension
    # carries its generated basis into the shared subanalysis validator, which
    # fail-closes a caller-supplied construction package rather than allowing a
    # declaration name or free-text derivation narrative to decide closeout.
    responses = judgment.get("semantic_model_dimensions")
    dimensions = item.get("dimensions")
    if (
        not isinstance(responses, dict)
        or not isinstance(dimensions, list)
        or not dimensions
    ):
        return ["semantic-model response needs a nonempty dimensions ledger"]
    for raw_dimension in dimensions:
        if not isinstance(raw_dimension, dict):
            errors.append("generated semantic-model dimension is malformed")
            continue
        dimension = str(raw_dimension.get("id") or "").strip()
        if not dimension:
            errors.append("generated semantic-model dimension has no id")
            continue
        response = responses.get(dimension)
        if not isinstance(response, dict):
            errors.append(f"`{dimension}` has no object-valued response")
            continue
        verdict = str(response.get("verdict") or "").strip()
        if verdict not in SEMANTIC_MODEL_REVIEW_VERDICTS:
            errors.append(
                f"`{dimension}.verdict` is not an accepted semantic verdict"
            )
        if not all(
            str(response.get(field) or "").strip()
            for field in ("source_locator", "semantic_comparison", "lean_evidence")
        ):
            errors.append(
                f"`{dimension}` needs source_locator, semantic_comparison, and "
                "lean_evidence"
            )
        if any(
            NAME_ONLY_REASON_RE.search(str(response.get(field) or ""))
            for field in ("semantic_comparison", "lean_evidence", "parameter_translation")
        ):
            errors.append(f"`{dimension}` has name-only semantic evidence")
        detected = bool(raw_dimension.get("detected_from_expanded_surface"))
        if detected and verdict == "not_applicable":
            errors.append(f"`{dimension}` is detected and cannot be not_applicable")
        if detected and raw_dimension.get(
            "requires_parameter_translation_when_detected"
        ) is True:
            if not str(response.get("parameter_translation") or "").strip():
                errors.append(f"`{dimension}` needs parameter_translation")
        errors.extend(
            f"`{dimension}`: {error}"
            for error in semantic_model_subanalysis_errors(
                raw_dimension,
                response,
                name_only=lambda value: bool(NAME_ONLY_REASON_RE.search(value)),
            )
        )
        if dimension in {
            "conditioning_and_calibration_semantics",
            "expectation_definedness",
            "null_cell_totalization_and_partition_scope",
        } and detected:
            basis = raw_dimension.get("expanded_shape_basis")
            if not isinstance(basis, list) or not any(
                isinstance(entry, str) and entry.strip() for entry in basis
            ):
                errors.append(f"`{dimension}` has no generated expanded-shape basis")
        requires_checked_bridge = bool(
            raw_dimension.get("requires_checked_bridge_when_detected")
        ) or dimension in SEMANTIC_MODEL_BRIDGE_DIMENSIONS
        if detected and requires_checked_bridge:
            if not str(response.get("lean_bridge") or "").strip():
                errors.append(f"`{dimension}` needs a checked Lean bridge")
    return errors


def semantic_model_judgment_is_complete(
    item: dict[str, Any], judgment: dict[str, Any]
) -> bool:
    """Check the minimum semantic-model payload before freshness is credited."""

    return not semantic_model_judgment_completeness_errors(item, judgment)


def current_open_semantic_model_dimensions(
    audit_payload: dict[str, Any], current: dict[str, dict[str, Any]]
) -> list[str]:
    """Return current semantic-model dimensions that explicitly remain open."""

    open_dimensions: list[str] = []
    for item in audit_payload.get("semantic_model_items") or []:
        if not isinstance(item, dict):
            continue
        key = str(item.get("judgment_key") or "").strip()
        judgment = current.get(key)
        if not key or not isinstance(judgment, dict):
            continue
        responses = judgment.get("semantic_model_dimensions")
        if not isinstance(responses, dict):
            continue
        for raw_dimension in item.get("dimensions") or []:
            if not isinstance(raw_dimension, dict):
                continue
            dimension = str(raw_dimension.get("id") or "").strip()
            response = responses.get(dimension)
            if not dimension or not isinstance(response, dict):
                continue
            if str(response.get("verdict") or "").strip() in {
                "mismatch_or_open",
                "documented_partial_boundary",
            }:
                open_dimensions.append(f"{key}.{dimension}")
    return sorted(set(open_dimensions))


def current_source_record_judgment_keys(
    audit_payload: dict[str, Any],
    match_payload: dict[str, Any],
    *,
    expected_paper_statement_map_sha256: str | None = None,
    folder: Path | None = None,
) -> set[str]:
    return set(
        current_source_record_judgment_items(
            audit_payload,
            match_payload,
            expected_paper_statement_map_sha256=expected_paper_statement_map_sha256,
            folder=folder,
        )
    )


def source_record_payload_is_non_evidence(payload: dict[str, Any]) -> bool:
    """Reject draft/candidate sidecars before they can satisfy an evidence gate."""

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
    if "candidate" in artifact_kind or "proposal" in artifact_kind:
        return True
    validator_type = str(payload.get("validator_type") or "").strip().lower()
    return "candidate" in validator_type or "proposal" in validator_type


def _historical_descriptor_migration_module() -> Any:
    """Import the optional one-time bridge only after v10 revalidation loads.

    ``source_record_current_revalidation`` imports this evidence gate to reuse
    semantic-model checks.  The historical bridge in turn relies on that
    revalidation module, so importing it at module initialization would make a
    circular, partially initialized authority path.  The loader is needed only
    while consuming evidence, after the shared v10 surface is available.
    """

    try:
        from scripts import source_record_historical_descriptor_migration as historical
    except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
        import source_record_historical_descriptor_migration as historical
    return historical


def _semantic_rebind_module() -> Any:
    """Load the schema-2 rebind lane lazily after the evidence gate exists.

    The transport imports current-revalidation helpers and checks this module's
    folder-aware identity gate while replaying.  Keeping the import lazy makes
    that dependency explicit and permits it to remain a distinct stronger
    lane rather than an implementation detail of the legacy bridge.
    """

    try:
        from scripts import source_record_semantic_rebind as semantic_rebind
    except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
        import source_record_semantic_rebind as semantic_rebind
    return semantic_rebind


def _scoped_receipt_rebind_module() -> Any:
    """Load the legacy scoped-receipt exception lazily to avoid audit cycles."""

    try:
        from scripts import source_record_scoped_receipt_rebind as scoped_rebind
    except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
        import source_record_scoped_receipt_rebind as scoped_rebind
    return scoped_rebind


def _component_projection_module() -> Any:
    """Load the optional derived-component lane after base loaders initialize.

    The component lane replays its parent through this evidence module with
    the lane explicitly disabled.  Keeping the import lazy makes that base
    replay an intentional acyclic call rather than an import-order accident.
    """

    try:
        from scripts import source_record_component_projection as component_projection
    except ModuleNotFoundError:  # pragma: no cover - direct script fallback.
        import source_record_component_projection as component_projection
    return component_projection


def _copy_loaded_source_record_overlay_item(
    value: Mapping[str, Any], updates: Mapping[str, Any] | None = None
) -> dict[str, Any]:
    """Keep an authenticated overlay token through in-memory normalization."""

    historical = _historical_descriptor_migration_module()
    semantic_rebind = _semantic_rebind_module()
    scoped_rebind = _scoped_receipt_rebind_module()
    component_projection = _component_projection_module()
    if component_projection.is_loaded_source_record_component_projection_item(value):
        return component_projection.copy_loaded_source_record_component_projection_item(
            value, updates
        )
    if scoped_rebind.is_loaded_source_record_scoped_receipt_rebind_item(value):
        return scoped_rebind.copy_loaded_source_record_scoped_receipt_rebind_item(
            value, updates
        )
    if semantic_rebind.is_loaded_source_record_semantic_rebind_item(value):
        return semantic_rebind.copy_loaded_source_record_semantic_rebind_item(
            value, updates
        )
    if historical.is_loaded_source_record_historical_descriptor_migration_item(value):
        return historical.copy_loaded_source_record_historical_descriptor_migration_item(
            value, updates
        )
    if is_loaded_source_record_attested_selected_reuse_item(value):
        return copy_loaded_source_record_attested_selected_reuse_item(value, updates)
    if is_loaded_source_record_differential_revalidation_item(value):
        return copy_loaded_source_record_differential_revalidation_item(value, updates)
    return copy_loaded_source_record_schema4_to5_migration_item(value, updates)


def _is_loaded_source_record_overlay_item(value: object) -> bool:
    """Whether an in-memory response came from an authenticated overlay loader.

    This asks the loader-owned private capabilities, never a serialized JSON
    marker.  It is used only to establish that a canonical sidecar's omitted
    response slot is supplied by a separately replayed current overlay; it
    does not infer a semantic match from a source key, declaration, or name.
    """

    historical = _historical_descriptor_migration_module()
    semantic_rebind = _semantic_rebind_module()
    scoped_rebind = _scoped_receipt_rebind_module()
    component_projection = _component_projection_module()
    return bool(
        is_loaded_source_record_schema4_to5_migration_item(value)
        or is_loaded_source_record_differential_revalidation_item(value)
        or is_loaded_source_record_attested_selected_reuse_item(value)
        or semantic_rebind.is_loaded_source_record_semantic_rebind_item(value)
        or historical.is_loaded_source_record_historical_descriptor_migration_item(
            value
        )
        or scoped_rebind.is_loaded_source_record_scoped_receipt_rebind_item(value)
        or component_projection.is_loaded_source_record_component_projection_item(
            value
        )
    )


def _project_current_source_record_response_association_pins(
    audit_payload: Mapping[str, Any],
    current: Mapping[str, Mapping[str, Any]],
    *,
    statement_map: Mapping[str, Any] | None = None,
    configured_assumption_formalization_regularity_context: (
        ConfiguredAssumptionFormalizationRegularityContext | None
    ) = None,
) -> dict[str, dict[str, Any]]:
    """Normalize every admitted response from its exact current raw group.

    This is deliberately after each ordinary/overlay loader has authenticated
    its own receipt and after precedence has selected the response.  It binds
    the selected response to the current raw-member group without treating a
    serialized association field as evidence.  A malformed group or a
    conflicting pin drops that response rather than guessing from its key,
    declaration, or review text.
    """

    groups, group_errors = source_record_raw_item_groups(audit_payload)
    if group_errors:
        return {}
    projected_current: dict[str, dict[str, Any]] = {}
    for raw_key, value in current.items():
        key = str(raw_key).strip()
        if not key or not isinstance(value, Mapping):
            continue
        group = groups.get(key)
        raw_members = group.get("raw_members") if isinstance(group, Mapping) else None
        projected, error = project_source_record_response_association_pins(
            raw_members,
            value,
            judgment_key=key,
            statement_map=statement_map,
            configured_assumption_formalization_regularity_context=(
                configured_assumption_formalization_regularity_context
            ),
        )
        if error or projected is None:
            continue
        projected_current[key] = _copy_loaded_source_record_overlay_item(
            value, projected
        )
    return projected_current


def _current_source_record_judgment_items_from_payload(
    audit_payload: dict[str, Any],
    match_payload: dict[str, Any],
    *,
    expected_paper_statement_map_sha256: str | None = None,
    folder: Path | None = None,
    allow_schema4_to5_migration: bool = False,
    allow_differential_revalidation: bool = False,
    allow_attested_selected_reuse: bool = False,
    allow_semantic_rebind: bool = False,
    allow_historical_descriptor_migration: bool = False,
    allow_scoped_receipt_rebind: bool = False,
    allow_component_projection: bool = False,
    prevalidated_source_record_identity_error: object = _UNSET,
) -> dict[str, dict[str, Any]]:
    identity_error = (
        source_record_audit_identity_error(
            audit_payload,
            expected_paper_statement_map_sha256=expected_paper_statement_map_sha256,
            folder=folder,
        )
        if prevalidated_source_record_identity_error is _UNSET
        else str(prevalidated_source_record_identity_error)
    )
    if identity_error:
        return {}
    if source_record_payload_is_non_evidence(match_payload):
        return {}
    ordinary_protocol_current = formalization_judgment_review_protocol_is_current(
        audit_payload, match_payload
    )
    historical = _historical_descriptor_migration_module()
    semantic_rebind = _semantic_rebind_module()
    scoped_rebind = _scoped_receipt_rebind_module()
    component_projection = _component_projection_module()
    required_prompt = str(audit_payload.get("prompt_version") or "").strip()
    required_digest = str(audit_payload.get("source_record_audit_sha256") or "").strip()
    required_item_digests = source_record_required_item_digests(audit_payload)
    unique_key_by_item_digest = source_record_unique_item_digest_keys(audit_payload)
    payload_prompt = str(match_payload.get("prompt_version") or "").strip()
    payload_digest = str(match_payload.get("source_record_audit_sha256") or "").strip()
    payload_validator = (
        match_payload.get("validator")
        or match_payload.get("model")
        or match_payload.get("judge")
    )
    payload_timestamp = (
        match_payload.get("validated_at")
        or match_payload.get("timestamp")
        or match_payload.get("generated_at")
    )
    raw_items = match_payload.get("items") or match_payload.get("field_judgments") or {}
    if not isinstance(raw_items, dict):
        return {}
    semantic_model_items = {
        str(item.get("judgment_key") or "").strip(): item
        for item in audit_payload.get("semantic_model_items") or []
        if isinstance(item, dict) and str(item.get("judgment_key") or "").strip()
    }
    semantic_model_expected = {
        str(key).strip()
        for key in audit_payload.get("expected_semantic_model_judgment_keys") or []
        if str(key).strip()
    }
    current: dict[str, dict[str, Any]] = {}
    for key, value in raw_items.items():
        if not isinstance(value, dict):
            continue
        if source_record_payload_is_non_evidence(value):
            continue
        migrated_overlay_entry = is_loaded_source_record_schema4_to5_migration_item(value)
        differential_overlay_entry = (
            is_loaded_source_record_differential_revalidation_item(value)
        )
        attested_selected_reuse_entry = (
            is_loaded_source_record_attested_selected_reuse_item(value)
        )
        semantic_rebind_entry = semantic_rebind.is_loaded_source_record_semantic_rebind_item(
            value
        )
        # The legacy helper still recognizes schema-2 private items for
        # backwards-compatible direct callers.  Once schema 2 is exposed as
        # its own lane, do not make one private item require both allowances.
        historical_descriptor_entry = (
            not semantic_rebind_entry
            and historical.is_loaded_source_record_historical_descriptor_migration_item(
                value
            )
        )
        scoped_receipt_entry = (
            scoped_rebind.is_loaded_source_record_scoped_receipt_rebind_item(value)
        )
        component_projection_entry = (
            component_projection.is_loaded_source_record_component_projection_item(
                value
            )
        )
        loaded_overlay_entry = (
            migrated_overlay_entry
            or differential_overlay_entry
            or attested_selected_reuse_entry
            or semantic_rebind_entry
            or historical_descriptor_entry
            or scoped_receipt_entry
            or component_projection_entry
        )
        if (
            (
                source_record_schema4_to5_migration_item_has_provenance(value)
                or source_record_differential_revalidation_item_has_provenance(value)
                or source_record_attested_selected_reuse_item_has_provenance(value)
                or semantic_rebind.source_record_semantic_rebind_item_has_provenance(
                    value
                )
                or historical.source_record_historical_descriptor_migration_item_has_provenance(
                    value
                )
                or scoped_rebind.source_record_scoped_receipt_rebind_item_has_provenance(
                    value
                )
                or component_projection.source_record_component_projection_item_has_provenance(
                    value
                )
            )
            and not loaded_overlay_entry
        ):
            continue
        if migrated_overlay_entry and not allow_schema4_to5_migration:
            continue
        if differential_overlay_entry and not allow_differential_revalidation:
            continue
        if attested_selected_reuse_entry and not allow_attested_selected_reuse:
            continue
        if semantic_rebind_entry and not allow_semantic_rebind:
            continue
        if historical_descriptor_entry and not allow_historical_descriptor_migration:
            continue
        if scoped_receipt_entry and not allow_scoped_receipt_rebind:
            continue
        if component_projection_entry and not allow_component_projection:
            continue
        if not loaded_overlay_entry and not ordinary_protocol_current:
            continue
        classification = str(
            value.get("classification")
            or value.get("judgment")
            or value.get("verdict")
            or value.get("status")
            or ""
        ).strip()
        item_prompt = str(value.get("prompt_version") or payload_prompt).strip()
        item_digest = str(value.get("source_record_audit_sha256") or payload_digest).strip()
        item_semantic_digest = str(value.get("source_record_item_sha256") or "").strip()
        item_semantic_digest_schema = value.get(
            "source_record_item_digest_schema"
        )
        raw_key = str(key)
        resolved_key = raw_key
        required_item_digest = required_item_digests.get(raw_key, "")
        # Item-level semantic reuse still needs an explicit aggregate audit
        # identity on the saved judgment. A matching item digest cannot turn a
        # blank audit field into evidence that this response was reviewed under
        # any generated source-record surface.
        if not item_digest and not loaded_overlay_entry:
            continue
        if loaded_overlay_entry:
            # Authenticated overlay loaders recompare an exact generated semantic
            # descriptor against the current raw audit.  They must not fall
            # back to aggregate freshness or a key/name remap.
            digest_current = True
        else:
            digest_current = source_record_item_judgment_current(
                aggregate_current=bool(required_digest and item_digest == required_digest),
                expected_item_digest=required_item_digest,
                judgment_item_digest=item_semantic_digest,
                judgment_item_digest_schema=item_semantic_digest_schema,
            )
        # A renamed storage key may be recovered only from a globally unique
        # schema-5 semantic receipt.  A digest shared by multiple current keys
        # remains adequate for direct same-key reuse above, but cannot select a
        # destination by a declaration/binder/source-map name heuristic.
        if not loaded_overlay_entry and not digest_current and not (
            required_digest and item_digest == required_digest
        ):
            candidate_key = unique_key_by_item_digest.get(item_semantic_digest)
            if candidate_key is not None:
                digest_current = source_record_item_judgment_current(
                    aggregate_current=False,
                    expected_item_digest=required_item_digests.get(candidate_key, ""),
                    judgment_item_digest=item_semantic_digest,
                    judgment_item_digest_schema=item_semantic_digest_schema,
                )
                if digest_current:
                    resolved_key = candidate_key
        validator = value.get("validator") or value.get("model") or value.get("judge") or payload_validator
        timestamp = (
            value.get("validated_at")
            or value.get("timestamp")
            or value.get("generated_at")
            or payload_timestamp
        )
        if (
            classification
            and validator
            and timestamp
            and item_prompt == required_prompt
            and digest_current
        ):
            semantic_item = semantic_model_items.get(resolved_key)
            if resolved_key in semantic_model_expected or semantic_item is not None:
                if semantic_item is None or not semantic_model_judgment_is_complete(
                    semantic_item, value
                ):
                    continue
            # Two stale aliases must not race to satisfy the same generated
            # item after a unique semantic-ID remap.
            if resolved_key in current:
                continue
            current[resolved_key] = _copy_loaded_source_record_overlay_item(value)
    return current


def _current_source_record_judgment_items(
    audit_payload: dict[str, Any],
    match_payload: dict[str, Any],
    *,
    expected_paper_statement_map_sha256: str | None = None,
    folder: Path | None = None,
    differential_overlay_path: Path | None = None,
    differential_current_raw_audit_path: Path | None = None,
    differential_current_raw_audit_provenance_path: Path | None = None,
    allow_archived_raw_identity: bool = False,
    allow_component_projection: bool = True,
    component_projection_frozen_inputs: object | None = None,
    base_judgment_sidecar_path: Path | None = None,
    prevalidated_source_record_identity_error: object = _UNSET,
    source_record_identity_context: object | None = None,
    statement_map_override: object = _UNSET,
    status_payload_override: object = _UNSET,
    configured_assumption_regularity_context_override: object = _UNSET,
) -> dict[str, dict[str, Any]]:
    """Load ordinary judgments plus authenticated narrow reuse overlays.

    Historical receipt validation may supply exact archived paths.  Normal
    callers leave both optional paths unset and retain the canonical-paper
    behavior.  ``allow_archived_raw_identity`` is restricted to replaying an
    immutable historical receipt before it is semantically compared to a new
    current receipt; it avoids incorrectly requiring that the historical
    source bytes still equal the live source.  The paths authenticate bytes
    only; they never select a match by declaration, binder, or judgment-key
    spelling.
    """

    if allow_archived_raw_identity and (
        differential_current_raw_audit_path is None
        or differential_current_raw_audit_provenance_path is None
    ):
        return {}
    identity_folder = None if allow_archived_raw_identity else folder
    effective_prevalidated_source_record_identity_error = (
        prevalidated_source_record_identity_error
    )
    if source_record_identity_context is not None:
        # This is not a caller-provided authorization bypass.  The opaque
        # capability was minted by the strict gate and is re-bound to live
        # canonical raw bytes, map bytes, and producer/source watch inputs
        # before every nested replay.  Archived raw paths never use it.
        if allow_archived_raw_identity or folder is None:
            return {}
        paper_for_identity = str(audit_payload.get("paper") or folder.name).strip()
        if not paper_for_identity or current_source_record_identity_context_error(
            source_record_identity_context,
            paper_dir=folder,
            paper=paper_for_identity,
            current_raw_audit=audit_payload,
            expected_paper_statement_map_sha256=(
                expected_paper_statement_map_sha256
            ),
        ):
            return {}
        effective_prevalidated_source_record_identity_error = ""

    ordinary = _current_source_record_judgment_items_from_payload(
        audit_payload,
        match_payload,
        expected_paper_statement_map_sha256=expected_paper_statement_map_sha256,
        folder=identity_folder,
        prevalidated_source_record_identity_error=(
            effective_prevalidated_source_record_identity_error
        ),
    )
    if folder is None:
        return _project_current_source_record_response_association_pins(
            audit_payload, ordinary
        )
    paper = str(audit_payload.get("paper") or folder.name).strip()
    if not paper:
        return ordinary
    migrated_items = load_current_source_record_schema4_to5_migration_items(
        folder, paper, audit_payload
    )
    migrated: dict[str, dict[str, Any]] = {}
    if migrated_items:
        migrated = _current_source_record_judgment_items_from_payload(
            audit_payload,
            {"schema": 1, "paper": paper, "items": migrated_items},
            expected_paper_statement_map_sha256=expected_paper_statement_map_sha256,
            folder=identity_folder,
            allow_schema4_to5_migration=True,
            prevalidated_source_record_identity_error=(
                effective_prevalidated_source_record_identity_error
            ),
        )
    differential_items = load_current_source_record_differential_revalidation_items(
        folder,
        paper,
        audit_payload,
        path=differential_overlay_path,
        current_raw_audit_path=differential_current_raw_audit_path,
        current_raw_audit_provenance_path=(
            differential_current_raw_audit_provenance_path
        ),
    )
    differential: dict[str, dict[str, Any]] = {}
    if differential_items:
        differential = _current_source_record_judgment_items_from_payload(
            audit_payload,
            {"schema": 1, "paper": paper, "items": differential_items},
            expected_paper_statement_map_sha256=expected_paper_statement_map_sha256,
            folder=identity_folder,
            allow_differential_revalidation=True,
            prevalidated_source_record_identity_error=(
                effective_prevalidated_source_record_identity_error
            ),
        )
    attested_selected_reuse_items = load_current_attested_selected_semantic_reuse_items(
        folder, paper, audit_payload
    )
    attested_selected_reuse: dict[str, dict[str, Any]] = {}
    if attested_selected_reuse_items:
        attested_selected_reuse = _current_source_record_judgment_items_from_payload(
            audit_payload,
            {"schema": 1, "paper": paper, "items": attested_selected_reuse_items},
            expected_paper_statement_map_sha256=expected_paper_statement_map_sha256,
            folder=identity_folder,
            allow_attested_selected_reuse=True,
            prevalidated_source_record_identity_error=(
                effective_prevalidated_source_record_identity_error
            ),
        )
    semantic_rebind = _semantic_rebind_module()
    semantic_rebind_items = semantic_rebind.load_current_source_record_semantic_rebind_items(
        folder,
        paper,
        audit_payload,
        source_record_identity_context=(
            source_record_identity_context
            if not allow_archived_raw_identity
            else None
        ),
    )
    semantic_rebind_current: dict[str, dict[str, Any]] = {}
    if semantic_rebind_items:
        semantic_rebind_current = _current_source_record_judgment_items_from_payload(
            audit_payload,
            {"schema": 1, "paper": paper, "items": semantic_rebind_items},
            expected_paper_statement_map_sha256=expected_paper_statement_map_sha256,
            folder=identity_folder,
            allow_semantic_rebind=True,
            prevalidated_source_record_identity_error=(
                effective_prevalidated_source_record_identity_error
            ),
        )
    historical = _historical_descriptor_migration_module()
    historical_descriptor_items = historical.load_current_source_record_historical_descriptor_migration_items(
        folder, paper, audit_payload, include_semantic_rebind=False
    )
    historical_descriptor: dict[str, dict[str, Any]] = {}
    if historical_descriptor_items:
        historical_descriptor = _current_source_record_judgment_items_from_payload(
            audit_payload,
            {"schema": 1, "paper": paper, "items": historical_descriptor_items},
            expected_paper_statement_map_sha256=expected_paper_statement_map_sha256,
            folder=identity_folder,
            allow_historical_descriptor_migration=True,
            prevalidated_source_record_identity_error=(
                effective_prevalidated_source_record_identity_error
            ),
        )
    scoped_rebind = _scoped_receipt_rebind_module()
    scoped_receipt_items = scoped_rebind.load_current_source_record_scoped_receipt_rebind_items(
        folder, paper, audit_payload
    )
    scoped_receipt: dict[str, dict[str, Any]] = {}
    if scoped_receipt_items:
        scoped_receipt = _current_source_record_judgment_items_from_payload(
            audit_payload,
            {"schema": 1, "paper": paper, "items": scoped_receipt_items},
            expected_paper_statement_map_sha256=expected_paper_statement_map_sha256,
            folder=identity_folder,
            allow_scoped_receipt_rebind=True,
            prevalidated_source_record_identity_error=(
                effective_prevalidated_source_record_identity_error
            ),
        )
    # The differential loader binds an unchanged prior response to the current
    # semantic obligation. A genuinely current ordinary response is newer
    # evidence, however, and must win over every overlay lane on collision.
    current_raw_digest = str(audit_payload.get("source_record_audit_sha256") or "").strip()
    ordinary_with_current_receipt = {
        key: value
        for key, value in ordinary.items()
        if current_raw_digest
        and str(value.get("source_record_audit_sha256") or "").strip()
        == current_raw_digest
    }
    statement_map_payload = (
        load_json(folder / "audit" / "paper_statement_map.json")
        if statement_map_override is _UNSET
        else statement_map_override
    )
    statement_map = (
        statement_map_payload if isinstance(statement_map_payload, Mapping) else None
    )
    status_payload = (
        load_json(folder / "status.json")
        if status_payload_override is _UNSET
        else status_payload_override
    )
    if configured_assumption_regularity_context_override is _UNSET:
        regularity_context, _regularity_context_error = (
            load_configured_assumption_formalization_regularity_context(
                folder,
                audit_payload,
                status_payload=(
                    status_payload if isinstance(status_payload, Mapping) else None
                ),
            )
        )
    else:
        regularity_context = configured_assumption_regularity_context_override
    base_current = _project_current_source_record_response_association_pins(
        audit_payload,
        {
            # The scoped receipt is an explicit legacy exception. Existing
            # current/reissued evidence remains higher-precedence on a key.
            **scoped_receipt,
            **attested_selected_reuse,
            **historical_descriptor,
            **ordinary,
            **migrated,
            **differential,
            # A schema-2 rebind has byte-pinned immutable inputs, a live raw
            # identity check, and a complete name-independent descriptor. It
            # is therefore stronger than the legacy differential bridge, but
            # still loses to independently reviewed ordinary current evidence.
            **semantic_rebind_current,
            **ordinary_with_current_receipt,
        },
        statement_map=statement_map,
        configured_assumption_formalization_regularity_context=regularity_context,
    )
    component_projection: dict[str, dict[str, Any]] = {}
    if allow_component_projection:
        component_module = _component_projection_module()
        component_items = (
            component_module.load_current_source_record_component_projection_items(
                folder,
                paper,
                audit_payload,
                frozen_inputs=component_projection_frozen_inputs,
                base_parent_items=base_current,
                base_parent_sidecar_path=base_judgment_sidecar_path,
                expected_paper_statement_map_sha256=(
                    expected_paper_statement_map_sha256
                ),
                source_record_identity_context=(
                    source_record_identity_context
                    if not allow_archived_raw_identity
                    else None
                ),
            )
        )
        if component_items:
            component_projection = _current_source_record_judgment_items_from_payload(
                audit_payload,
                {"schema": 1, "paper": paper, "items": component_items},
                expected_paper_statement_map_sha256=expected_paper_statement_map_sha256,
                folder=identity_folder,
                allow_component_projection=True,
                prevalidated_source_record_identity_error=(
                    effective_prevalidated_source_record_identity_error
                ),
            )
    # The component lane is derived from the already materialized base parent
    # surface.  Project only its new child responses, then let direct/current
    # base evidence keep precedence on every collision.
    projected_component = _project_current_source_record_response_association_pins(
        audit_payload,
        component_projection,
        statement_map=statement_map,
        configured_assumption_formalization_regularity_context=regularity_context,
    )
    return {**projected_component, **base_current}


def current_source_record_judgment_items(
    audit_payload: dict[str, Any],
    match_payload: dict[str, Any],
    *,
    expected_paper_statement_map_sha256: str | None = None,
    folder: Path | None = None,
    differential_overlay_path: Path | None = None,
    differential_current_raw_audit_path: Path | None = None,
    differential_current_raw_audit_provenance_path: Path | None = None,
    allow_archived_raw_identity: bool = False,
    allow_component_projection: bool = True,
    source_record_identity_context: object | None = None,
) -> dict[str, dict[str, Any]]:
    """Materialize judgments under one current identity replay when possible.

    ``source_record_identity_context`` is an opaque, verifier-issued runtime
    capability, not a caller-supplied prevalidation result.  Forged, stale,
    cross-paper, or archived-path contexts are rejected by the private loader
    before any judgment receives credit.  Ordinary callers leave it unset and
    this function mints one fresh context for the whole current-lane replay.
    """

    context = source_record_identity_context
    if (
        context is None
        and not allow_archived_raw_identity
        and folder is not None
    ):
        paper = str(audit_payload.get("paper") or folder.name).strip()
        if paper:
            try:
                context = prepare_current_source_record_identity_context(
                    folder,
                    paper,
                    audit_payload,
                )
            except SourceRecordIdentityContextDeferred:
                # The legacy path would reject this raw audit as non-current
                # too.  Do not retry it here, because a busy gate is not an
                # absent optional overlay.
                return {}

    return _current_source_record_judgment_items(
        audit_payload,
        match_payload,
        expected_paper_statement_map_sha256=expected_paper_statement_map_sha256,
        folder=folder,
        differential_overlay_path=differential_overlay_path,
        differential_current_raw_audit_path=differential_current_raw_audit_path,
        differential_current_raw_audit_provenance_path=(
            differential_current_raw_audit_provenance_path
        ),
        allow_archived_raw_identity=allow_archived_raw_identity,
        allow_component_projection=allow_component_projection,
        source_record_identity_context=context,
    )


SOURCE_RECORD_MATCH_SIDECAR_BASENAME = "source_record_match_llm.json"
SOURCE_RECORD_MANUAL_CURRENT_COMPLEMENT_FIELD = "manual_current_complement"
SOURCE_RECORD_MANUAL_CURRENT_COMPLEMENT_SCHEMA = 1
SOURCE_RECORD_MANUAL_CURRENT_COMPLEMENT_POLICY_VERSION = (
    "source-record-v10-manual-current-complement-v3"
)
SOURCE_RECORD_MANUAL_CURRENT_COMPLEMENT_POLICY_VERSIONS = frozenset(
    {
        "source-record-v10-manual-current-complement-v1",
        "source-record-v10-manual-current-complement-v2",
        SOURCE_RECORD_MANUAL_CURRENT_COMPLEMENT_POLICY_VERSION,
    }
)
SOURCE_RECORD_MANUAL_CURRENT_COMPLEMENT_SCOPE = (
    "all_current_generated_groups_without_authenticated_overlay"
)


def canonical_source_record_match_sidecar_path(
    path: Path, paper_dir: Path
) -> bool:
    """Whether ``path`` is one of the two ordinary source-record sidecars.

    Historical snapshots and authenticated overlay artifacts intentionally use
    their own paths.  This guard applies only to the ordinary repository
    sidecar which consumers otherwise treat as the paper's current ledger.
    """

    try:
        resolved = path.resolve()
        root = paper_dir.resolve()
    except (OSError, RuntimeError):
        return False
    return resolved in {
        root / "audit" / SOURCE_RECORD_MATCH_SIDECAR_BASENAME,
        root / SOURCE_RECORD_MATCH_SIDECAR_BASENAME,
    }


def _canonical_source_record_sidecar_item_keys(
    payload: Mapping[str, Any],
) -> tuple[set[str] | None, str]:
    """Read the ordinary response ledger without treating its contents as proof.

    ``field_judgments`` remains a legacy storage spelling.  It is accepted
    only with the same precedence as the ordinary loader, so the coverage gate
    cannot validate a different key ledger than the consumer actually reads.
    """

    raw_items = payload.get("items")
    legacy_items = payload.get("field_judgments")
    if not isinstance(raw_items, Mapping) or (
        not raw_items and isinstance(legacy_items, Mapping)
    ):
        raw_items = legacy_items
    if not isinstance(raw_items, Mapping):
        return None, "canonical source-record sidecar has no object-valued items ledger"
    keys: set[str] = set()
    for raw_key in raw_items:
        key = str(raw_key or "").strip()
        if not key or key in keys:
            return None, "canonical source-record sidecar has an empty or duplicate response key"
        keys.add(key)
    return keys, ""


def _paper_relative_sidecar_path(path: Path, paper_dir: Path) -> str | None:
    try:
        return path.resolve().relative_to(paper_dir.resolve()).as_posix()
    except (OSError, RuntimeError, ValueError):
        return None


def _selected_current_revalidation_coverage_error(
    audit_payload: Mapping[str, Any],
    sidecar: Mapping[str, Any],
    *,
    paper_dir: Path,
    sidecar_path: Path,
) -> str:
    """Validate the selected-current rebind before accepting its union.

    A selected-current sidecar deliberately serializes only the semantic
    complement of a separately authenticated differential overlay.  Its
    provenance is therefore not interchangeable with the older
    ``manual_current_complement`` marker that might have been copied from its
    historical input.  The current-revalidation module owns the replay: it
    checks the exact selected descriptor ledger, attestation bytes, overlay
    bytes, and the complete current generated-group union.  This helper is
    intentionally lazy because that module imports this evidence layer.
    """

    metadata = sidecar.get("current_selected_semantic_revalidation")
    if not isinstance(metadata, Mapping):
        return ""
    paper = str(audit_payload.get("paper") or paper_dir.name).strip()
    if not paper:
        return "canonical selected-current rebind has no paper identity"
    try:
        from scripts import source_record_current_revalidation as revalidation
    except Exception as exc:  # noqa: BLE001 - evidence must fail closed.
        return (
            "canonical selected-current rebind could not load its authenticated "
            f"replay validator: {type(exc).__name__}: {exc}"
        )
    try:
        errors = revalidation.validate_selected_rebound_sidecar(
            dict(audit_payload),
            dict(sidecar),
            paper=paper,
            paper_dir=paper_dir,
            output_sidecar_path=sidecar_path,
            include_downstream_target_disposition=False,
        )
    except Exception as exc:  # noqa: BLE001 - the replay validator fails closed.
        return (
            "canonical selected-current rebind replay raised "
            f"{type(exc).__name__}: {exc}"
        )
    if errors:
        return (
            "canonical selected-current rebind is not an authenticated "
            "selected-plus-overlay union: "
            + "; ".join(str(error) for error in errors[:3])
        )
    return ""


def canonical_source_record_sidecar_effective_coverage_error(
    audit_payload: Mapping[str, Any],
    sidecar: Mapping[str, Any],
    *,
    effective_items: Mapping[str, Mapping[str, Any]],
    paper_dir: Path,
    sidecar_path: Path,
    primary_closeout_source_record_receipt: bool = False,
) -> str:
    """Validate the canonical sidecar's complete effective response coverage.

    A normal ordinary sidecar must serialize exactly one response slot for
    every generator-produced raw judgment group.  A partial sidecar is valid
    only when every omitted slot is supplied by an in-memory,
    loader-authenticated overlay, or when its completed manual-complement
    provenance covers the remaining exact ledger.  A selected-current rebind
    is a stricter overlay-complement case: it must replay its own attestation
    and descriptor ledger first.  Serialized provenance markers are never
    evidence on their own.  The caller must pass the effective mapping
    returned by the ordinary loader after those overlays have been revalidated,
    and the union must exactly match the raw group ledger.

    The comparison is structural: raw groups and loader-authenticated response
    slots are content-addressed audit coordinates.  It does not use theorem,
    declaration, binder, or function-name similarity to infer coverage.
    """

    if not canonical_source_record_match_sidecar_path(sidecar_path, paper_dir):
        return "coverage guard was asked to validate a noncanonical source-record sidecar"
    groups, group_errors = source_record_raw_item_groups(audit_payload)
    if group_errors:
        return (
            "current source-record raw group ledger is malformed: "
            + "; ".join(sorted(group_errors.values())[:3])
        )
    expected = {str(key).strip() for key in groups}
    if not expected:
        # A keyless certificate artifact still belongs to the raw aggregate
        # receipt but has no response slot. There is no canonical-sidecar
        # coverage assertion to make when the generator emitted no groups.
        return ""
    if "" in expected:
        return "current source-record raw group ledger has an empty response key"
    stored, stored_error = _canonical_source_record_sidecar_item_keys(sidecar)
    if stored is None:
        return stored_error
    extra_stored = sorted(stored - expected)
    if extra_stored:
        return (
            "canonical source-record sidecar has response key(s) absent from the "
            "current raw group ledger: "
            + ", ".join(extra_stored[:5])
            + ("; ..." if len(extra_stored) > 5 else "")
        )
    if stored == expected:
        return ""

    # The ordinary loader gives a current authenticated overlay precedence over
    # stale ordinary responses.  When that effective ledger already covers the
    # entire current raw group set, it is sufficient on its own: a historical
    # selected-complement marker cannot make the independently authenticated
    # current union less sound.  This is structural/receipt-based; the keys
    # only index generated groups and never establish semantic correspondence.
    effective = {
        str(key).strip(): value
        for key, value in effective_items.items()
        if str(key).strip()
    }
    if (
        set(effective) == expected
        and all(
            key in stored or _is_loaded_source_record_overlay_item(value)
            for key, value in effective.items()
        )
    ):
        return ""

    # A selected-current rebind has its own authenticated coverage mechanism:
    # the current-revalidation replay proves that this sidecar covers exactly
    # the semantic complement of the loaded differential overlay.  It is not
    # a waiver for an old/manual marker.  In particular, a stale inherited
    # manual-current-complement receipt is ignored only after that replay
    # succeeds and the independently loaded effective union below is exact.
    selected_revalidation_error = _selected_current_revalidation_coverage_error(
        audit_payload,
        sidecar,
        paper_dir=paper_dir,
        sidecar_path=sidecar_path,
    )
    if selected_revalidation_error:
        return selected_revalidation_error
    if isinstance(sidecar.get("current_selected_semantic_revalidation"), Mapping):
        effective_keys = set(effective)
        if effective_keys and effective_keys == expected:
            return ""
        missing = sorted(expected - effective_keys)
        extra = sorted(effective_keys - expected)
        return (
            "canonical selected-current rebind does not have exact authenticated "
            "effective coverage of the current raw group ledger"
            + (f"; missing={missing[:5]}" if missing else "")
            + (f"; extra={extra[:5]}" if extra else "")
        )

    # A generic authenticated overlay may legitimately cover only a subset of
    # the current raw groups while another group awaits manual review.  Preserve
    # that authenticated subset for low-level consumers; the full closeout
    # gate separately compares the effective set with ``expected`` and reports
    # the still-missing groups.  Do not accept a plain partial mapping just
    # because its keys happen to look current: every effective response not
    # serialized by the canonical sidecar must carry a private loader
    # capability from an exact descriptor-replay transport.
    if (
        effective
        and set(effective) <= expected
        and any(key not in stored for key in effective)
        and all(
            key in stored or _is_loaded_source_record_overlay_item(value)
            for key, value in effective.items()
        )
    ):
        return ""

    complement = sidecar.get(SOURCE_RECORD_MANUAL_CURRENT_COMPLEMENT_FIELD)
    if not isinstance(complement, Mapping):
        return (
            "canonical source-record sidecar is an unlabelled partial fragment: "
            f"it serializes {len(stored)} of {len(expected)} current raw response "
            "groups without manual_current_complement provenance"
        )
    if not schema_version_is_exact(
        complement.get("schema"), SOURCE_RECORD_MANUAL_CURRENT_COMPLEMENT_SCHEMA
    ):
        return "canonical manual_current_complement has an unsupported schema"
    if str(complement.get("policy_version") or "").strip() not in (
        SOURCE_RECORD_MANUAL_CURRENT_COMPLEMENT_POLICY_VERSIONS
    ):
        return "canonical manual_current_complement has an unsupported policy version"
    if str(complement.get("completed_template_review_scope") or "").strip() != (
        SOURCE_RECORD_MANUAL_CURRENT_COMPLEMENT_SCOPE
    ):
        return "canonical manual_current_complement has the wrong review scope"
    raw_digest = str(audit_payload.get("source_record_audit_sha256") or "").strip()
    if not raw_digest or str(
        complement.get("current_source_record_audit_sha256") or ""
    ).strip() != raw_digest:
        return "canonical manual_current_complement is not bound to the current raw receipt"
    expected_key_digest = canonical_json_digest(sorted(expected))
    if str(complement.get("generated_judgment_keys_sha256") or "").strip() != (
        expected_key_digest
    ):
        return "canonical manual_current_complement has stale generated-key coverage"
    relative_sidecar_path = _paper_relative_sidecar_path(sidecar_path, paper_dir)
    if relative_sidecar_path is None or str(
        complement.get("output_sidecar_path") or ""
    ).strip() != relative_sidecar_path:
        return "canonical manual_current_complement names a different output sidecar"
    if not str(complement.get("template_reviewer") or "").strip() or not str(
        complement.get("template_validated_at") or ""
    ).strip():
        return "canonical manual_current_complement lacks completed-template reviewer metadata"

    effective = {str(key).strip() for key in effective_items}
    if not effective or "" in effective or effective != expected:
        if primary_closeout_source_record_receipt:
            # The consolidated primary gate has already validated this exact
            # raw ledger, including its runtime-only strict full-Spec receipts.
            # This downstream integrity reader deliberately has no serialized
            # copy of those receipts, so it may not demand duplicate manual
            # semantic-model rows after it has checked the canonical sidecar's
            # path, raw pin, generated-key pin, and complement provenance.
            return ""
        missing = sorted(expected - effective)
        extra = sorted(effective - expected)
        return (
            "canonical manual_current_complement does not have exact authenticated "
            "effective coverage of the current raw group ledger"
            + (f"; missing={missing[:5]}" if missing else "")
            + (f"; extra={extra[:5]}" if extra else "")
        )
    return ""


def explicit_source_route_semantic_model_findings(
    folder: Path,
    status: str,
    status_payload: dict[str, Any],
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Require current expanded-model evidence for explicit-route v10 closeout.

    Exact source routes prevent a paper row from silently drifting away from a
    named source endpoint, but they do not by themselves compare its carrier,
    probability law, conditioning convention, or endpoint behavior.  A full
    closeout using that strict v10 surface therefore needs the schema-2,
    expanded-type semantic-model lane and current judgments for every generated
    semantic item.  The trigger is status configuration and artifact content,
    never a theorem or function name.
    """

    if (
        status not in FULL_CLOSEOUT_STATUSES
        or not explicit_source_routes_enabled(status_payload)
    ):
        return []
    corrected_scope_current = (
        context.corrected_scope_current
        if context is not None
        else author_approved_corrected_scope_contract_is_current(
            folder, status_payload
        )
    )
    if corrected_scope_current:
        # A current author-approved corrected-model contract has its own
        # expanded semantic-item and bridge validation path. It intentionally
        # replaces archive-source matching rather than weakening it by name.
        return []

    # A canonical direct-row receipt is an explicit, current alternative to
    # the raw source-record lane.  It binds the source map, source bytes,
    # direct review ledger, interface closure, protocol, and focused build;
    # do not demand a freshly regenerated raw machine record merely because
    # that distinct evidence lane was not selected.
    direct_receipt_current, _direct_receipt_error = (
        direct_source_row_review_receipt_state(
            folder, require_source_bytes=require_source_bytes
        )
    )
    if direct_receipt_current:
        return []

    # A v11 source-to-Spec campaign retains the same raw-integrity and
    # semantic-model validation, but its occurrence-indexed contract is the
    # authoritative current-evidence selector.  Requiring this legacy v10
    # aggregate lane as well would double-count semantic parents that v11
    # deliberately discharges from its exact runtime receipts.
    source_map_payload = (
        context.statement_map
        if context is not None
        else load_json(canonical_sidecar(folder, "paper_statement_map.json"))
    )
    if raw_source_spec_screening_requested(
        status_payload, source_map_payload, folder=folder
    ):
        return []

    findings: list[Finding] = []

    def add(path: Path, message: str) -> None:
        findings.append(Finding("ERROR", folder.name, rel(path), message))

    review_surface = status_payload.get("review_surface")
    semantic_config = (
        review_surface.get("semantic_model_review")
        if isinstance(review_surface, dict)
        else None
    )
    if not isinstance(semantic_config, dict):
        add(
            folder / "status.json",
            f"full-closeout status `{status}` with explicit v10 source routes requires "
            "review_surface.semantic_model_review schema 2",
        )
        return findings
    dimensions = semantic_config.get("required_dimensions")
    normalized_dimensions = (
        [str(dimension).strip() for dimension in dimensions]
        if isinstance(dimensions, list)
        else []
    )
    if (
        not schema_version_is_exact(
            semantic_config.get("schema"), SEMANTIC_MODEL_REVIEW_SCHEMA
        )
        or len(normalized_dimensions) != len(set(normalized_dimensions))
        or set(normalized_dimensions) != SEMANTIC_MODEL_REVIEW_DIMENSIONS
    ):
        add(
            folder / "status.json",
            "explicit v10 source-route closeout requires semantic_model_review "
            "schema 2 with every expanded-semantic dimension exactly once",
        )
        return findings

    if context is not None:
        audit_path = context.audit_snapshot.path
        audit_path_error = context.audit_path_error
    else:
        audit_path, audit_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_audit_file",
            default_basename="source_record_audit.json",
        )
    if audit_path_error:
        add(folder / "status.json", audit_path_error)
        return findings
    assert audit_path is not None
    audit_payload = (
        context.audit_payload if context is not None else load_json(audit_path)
    )
    if audit_payload is None:
        add(
            audit_path,
            "explicit v10 source-route closeout requires a current generated "
            "source-record semantic-model audit",
        )
        return findings
    if (
        str(audit_payload.get("prompt_version") or "").strip()
        != CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
    ):
        add(
            audit_path,
            "explicit v10 source-route closeout requires source-record prompt "
            f"`{CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION}`",
        )
        return findings
    map_digest = (
        context.paper_statement_map_sha256
        if context is not None
        else current_paper_statement_map_sha256(folder)
    )
    if context is not None:
        semantic_contract_revalidation = context.semantic_contract_revalidation
        semantic_contract_revalidation_error = (
            context.semantic_contract_revalidation_error
        )
        identity_error = context.source_record_identity_error
    else:
        (
            semantic_contract_revalidation,
            semantic_contract_revalidation_error,
        ) = source_record_semantic_contract_revalidation_context(
            folder, audit_payload
        )
        identity_error = source_record_audit_identity_error(
            audit_payload,
            expected_paper_statement_map_sha256=map_digest,
            folder=folder,
            semantic_contract_revalidation=semantic_contract_revalidation,
            prevalidated_semantic_contract_revalidation_error=(
                semantic_contract_revalidation_error
            ),
        )
    if identity_error:
        add(
            audit_path,
            "explicit v10 source-route closeout requires a current generated "
            "source-record audit: " + identity_error,
        )
        return findings
    raw_expected = audit_payload.get("expected_semantic_model_judgment_keys")
    raw_semantic_items = audit_payload.get("semantic_model_items")
    if not isinstance(raw_expected, list):
        add(
            audit_path,
            "explicit v10 source-route closeout requires "
            "expected_semantic_model_judgment_keys to be a list",
        )
        return findings
    if not isinstance(raw_semantic_items, list):
        add(
            audit_path,
            "explicit v10 source-route closeout requires semantic_model_items to be a list",
        )
        return findings
    expected_keys = [
        key.strip() if isinstance(key, str) else ""
        for key in raw_expected
    ]
    if not expected_keys:
        add(
            audit_path,
            "explicit v10 source-route closeout generated no required semantic-model "
            "judgments; regenerate the source-record audit from the configured review surface",
        )
        return findings
    if any(not key for key in expected_keys) or len(expected_keys) != len(set(expected_keys)):
        add(
            audit_path,
            "explicit v10 source-route closeout requires nonempty unique "
            "expected semantic-model judgment keys",
        )
        return findings
    semantic_keys: list[str] = []
    for item in raw_semantic_items:
        key = (
            item.get("judgment_key").strip()
            if isinstance(item, dict) and isinstance(item.get("judgment_key"), str)
            else ""
        )
        semantic_keys.append(key)
        dimensions_for_item = item.get("dimensions") if isinstance(item, dict) else None
        if semantic_model_item_dimension_ids_error(dimensions_for_item):
            add(
                audit_path,
                "explicit v10 source-route closeout requires every generated "
                "semantic-model item to carry each schema-2 base dimension "
                "exactly once, with only explicitly generated source-scoped "
                "extensions; an empty dimension list is not semantic evidence",
            )
            return findings
    if any(not key for key in semantic_keys) or len(semantic_keys) != len(set(semantic_keys)):
        add(
            audit_path,
            "explicit v10 source-route closeout requires semantic_model_items with "
            "nonempty unique judgment keys",
        )
        return findings
    expected = set(expected_keys)
    semantic_items = set(semantic_keys)
    if expected != semantic_items:
        add(
            audit_path,
            "explicit v10 source-route closeout requires generated semantic-model items "
            "to match the expected semantic-model judgment keys exactly",
        )
        return findings

    if context is not None:
        match_path = context.match_snapshot.path
        match_path_error = context.match_path_error
    else:
        match_path, match_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_judgment_file",
            default_basename="source_record_match_llm.json",
        )
    if match_path_error:
        add(folder / "status.json", match_path_error)
        return findings
    assert match_path is not None
    current = (
        context.current_source_record_judgments
        if context is not None
        else current_source_record_judgment_items(
            audit_payload,
            load_json(match_path) or {},
            expected_paper_statement_map_sha256=map_digest,
            folder=folder,
        )
    )
    missing = sorted(expected - set(current))
    if missing:
        add(
            match_path,
            f"explicit v10 source-route closeout has {len(missing)} semantic-model "
            "judgment(s) without current complete source-record evidence: "
            + ", ".join(missing[:5])
            + ("; ..." if len(missing) > 5 else ""),
        )
    return findings


def check_source_record_configured_rows(
    folder: Path, *, context: EvidenceRunContext | None = None
) -> list[Finding]:
    """Fail closed when saved provenance evidence omitted configured Lean rows.

    The source-record helper records this condition explicitly.  Treat it as
    an audit-coverage error for every paper status: a partial paper may carry
    open mathematical obligations, but its configured review surface may not
    vanish because a parser or formatting change missed a declaration.
    """

    audit_path = canonical_sidecar(folder, "source_record_audit.json")
    audit_payload = (
        context.audit_payload
        if context is not None
        and context.audit_snapshot.path.resolve() == audit_path.resolve()
        else load_json(audit_path)
    )
    if not isinstance(audit_payload, dict):
        return []
    missing = sorted(
        {
            str(row).strip()
            for row in audit_payload.get("missing_configured_review_rows") or []
            if isinstance(row, str) and row.strip()
        }
    )
    if not missing:
        return []
    return [
        Finding(
            "ERROR",
            folder.name,
            rel(audit_path),
            "source-record audit omitted "
            f"{len(missing)} configured review row(s); audit coverage is incomplete: "
            + ", ".join(missing[:8])
            + ("; ..." if len(missing) > 8 else ""),
        )
    ]


def check_source_premise_consistency(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Keep Lean-checked source-input contradictions visible at closeout.

    This lane is opt-in by the generated source-record schema so historical
    sidecars remain readable.  Once a current audit declares the schema, a
    direct elaborated route from a reviewed source record to ``False`` blocks a
    full closeout.  A route that still needs extra non-proposition data is
    retained as a warning rather than promoted to a contradiction.
    """

    audit_path = canonical_sidecar(folder, "source_record_audit.json")
    audit_payload = (
        context.audit_payload
        if context is not None
        and context.audit_snapshot.path.resolve() == audit_path.resolve()
        else load_json(audit_path)
    )
    if not isinstance(audit_payload, dict):
        return []
    if not schema_version_is_exact(
        audit_payload.get("source_premise_consistency_schema"), 1
    ):
        return []
    severity = source_record_judgment_freshness_severity(status)
    error = str(audit_payload.get("source_premise_consistency_error") or "").strip()
    if error:
        return [
            Finding(
                severity,
                folder.name,
                rel(audit_path),
                "source-premise consistency scan did not complete: " + error,
            )
        ]
    raw_items = audit_payload.get("source_premise_consistency_items")
    if not isinstance(raw_items, list):
        return [
            Finding(
                severity,
                folder.name,
                rel(audit_path),
                "source-premise consistency schema is present but its elaborated "
                "result list is missing or malformed",
            )
        ]

    findings: list[Finding] = []
    for raw_item in raw_items:
        if not isinstance(raw_item, dict):
            findings.append(
                Finding(
                    severity,
                    folder.name,
                    rel(audit_path),
                    "source-premise consistency result contains a malformed item",
                )
            )
            continue
        reviewed = str(raw_item.get("reviewed_input_type") or "").strip()
        direct = raw_item.get("direct_eliminators")
        data_dependent = raw_item.get("candidate_data_dependent_eliminators")
        if not reviewed or not isinstance(direct, list) or not isinstance(data_dependent, list):
            findings.append(
                Finding(
                    severity,
                    folder.name,
                    rel(audit_path),
                    "source-premise consistency item lacks a reviewed input or "
                    "well-formed eliminator lists",
                )
            )
            continue
        direct_names = sorted(
            {
                str(candidate.get("candidate") or "").strip()
                for candidate in direct
                if isinstance(candidate, dict)
                and str(candidate.get("candidate") or "").strip()
                and candidate.get("direct_eliminator") is True
            }
        )
        if direct_names:
            findings.append(
                Finding(
                    severity,
                    folder.name,
                    rel(audit_path),
                    "Lean elaboration found a direct route from reviewed source input "
                    f"`{reviewed}` to `False` via "
                    + ", ".join(direct_names[:4])
                    + ("; ..." if len(direct_names) > 4 else "")
                    + ". This source-facing model premise is inconsistent and cannot "
                    "support a full formalization claim.",
                )
            )
        data_names = sorted(
            {
                str(candidate.get("candidate") or "").strip()
                for candidate in data_dependent
                if isinstance(candidate, dict)
                and str(candidate.get("candidate") or "").strip()
                and candidate.get("direct_eliminator") is False
            }
        )
        if data_names:
            findings.append(
                Finding(
                    "WARN",
                    folder.name,
                    rel(audit_path),
                    "Lean found a `False` route involving reviewed source input "
                    f"`{reviewed}` plus extra non-proposition data via "
                    + ", ".join(data_names[:4])
                    + ("; ..." if len(data_names) > 4 else "")
                    + ". It is not treated as a direct contradiction, but remains "
                    "source-model proof debt until those extra data parameters are audited.",
                )
            )
    return findings


def check_source_record_judgments(
    folder: Path,
    status: str,
    *,
    require_source_bytes: bool = True,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    corrected_scope_current = (
        context.corrected_scope_current
        if context is not None
        else author_approved_corrected_scope_contract_is_current(
            folder, status_payload
        )
    )
    if corrected_scope_current:
        # The checked author-approved contract supersedes source-to-archive LLM
        # matching for this explicitly different target. Its current source-
        # record digest and expanded model-field mappings are validated above.
        return []
    v11_direct_current, _v11_direct_error = v11_direct_semantic_review_state(
        folder,
        status,
        require_source_bytes=require_source_bytes,
        context=context,
    )
    if v11_direct_current:
        # A current v11 ledger is the selected replacement for the historical
        # generated source-record lane.  The ledger and every material library
        # dependency are validated above; a final closure receipt adds build
        # and closure binding later, rather than requiring a duplicate v10
        # source-record reissue during preparation.
        return []
    if context is not None:
        audit_path = context.audit_snapshot.path
        audit_path_error = context.audit_path_error
    else:
        audit_path, audit_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_audit_file",
            default_basename="source_record_audit.json",
        )
    if audit_path_error:
        return [
            Finding(
                source_record_judgment_freshness_severity(status),
                folder.name,
                rel(folder / "status.json"),
                audit_path_error,
            )
        ]
    assert audit_path is not None
    audit_payload = (
        context.audit_payload if context is not None else load_json(audit_path)
    )
    if not isinstance(audit_payload, dict):
        return []
    map_digest = (
        context.paper_statement_map_sha256
        if context is not None
        else current_paper_statement_map_sha256(folder)
    )
    if context is not None:
        semantic_contract_revalidation = context.semantic_contract_revalidation
        semantic_contract_revalidation_error = (
            context.semantic_contract_revalidation_error
        )
        identity_error = context.source_record_identity_error
    else:
        (
            semantic_contract_revalidation,
            semantic_contract_revalidation_error,
        ) = source_record_semantic_contract_revalidation_context(
            folder, audit_payload
        )
        identity_error = source_record_audit_identity_error(
            audit_payload,
            expected_paper_statement_map_sha256=map_digest,
            folder=folder,
            semantic_contract_revalidation=semantic_contract_revalidation,
            prevalidated_semantic_contract_revalidation_error=(
                semantic_contract_revalidation_error
            ),
        )
    if identity_error:
        direct_receipt_current, _direct_receipt_error = (
            direct_source_row_review_receipt_state(
            folder, require_source_bytes=require_source_bytes
            )
        )
        if direct_receipt_current:
            return []
        return [
            Finding(
                source_record_judgment_freshness_severity(status),
                folder.name,
                rel(audit_path),
                "saved source-record audit cannot support current judgments: "
                + identity_error,
            )
        ]
    # A current direct-row receipt is a deliberately selected alternative to
    # the aggregate raw source-record judgment sidecar.  Its v11 ledger is
    # independently checked by `v11_raw_source_spec_screening_findings`; do
    # not make that selected evidence lane falsely depend on historical raw
    # response-key coordinates after the raw audit itself has changed.
    direct_receipt_current, _direct_receipt_error = direct_source_row_review_receipt_state(
        folder, require_source_bytes=require_source_bytes
    )
    if direct_receipt_current:
        return []
    if context is not None:
        match_path = context.match_snapshot.path
        match_path_error = context.match_path_error
    else:
        match_path, match_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_judgment_file",
            default_basename="source_record_match_llm.json",
        )
    if match_path_error:
        return [
            Finding(
                source_record_judgment_freshness_severity(status),
                folder.name,
                rel(folder / "status.json"),
                match_path_error,
            )
        ]
    assert match_path is not None
    match_payload = (
        context.match_payload if context is not None else (load_json(match_path) or {})
    )
    current_items = (
        context.current_source_record_judgments
        if context is not None
        else current_source_record_judgment_items(
            audit_payload,
            match_payload,
            expected_paper_statement_map_sha256=map_digest,
            folder=folder,
        )
    )
    if canonical_source_record_match_sidecar_path(match_path, folder):
        coverage_error = canonical_source_record_sidecar_effective_coverage_error(
            audit_payload,
            match_payload,
            effective_items=current_items,
            paper_dir=folder,
            sidecar_path=match_path,
            primary_closeout_source_record_receipt=(
                context is not None
                and _has_current_primary_closeout_source_record_judgment_receipt(
                    context
                )
            ),
        )
        if coverage_error:
            return [
                Finding(
                    source_record_judgment_freshness_severity(status),
                    folder.name,
                    rel(match_path),
                    coverage_error,
                )
            ]
    required = source_record_required_keys(
        audit_payload,
        semantic_contract_revalidation=semantic_contract_revalidation,
    )
    if not required:
        return []
    current = set(current_items)
    missing = [key for key in required if key not in current]
    if not missing:
        return []
    if (
        context is not None
        and _has_current_primary_closeout_source_record_judgment_receipt(context)
    ):
        # The exact primary closeout gate has already checked this generated
        # source-record surface, including any strict full-Spec receipt
        # coverage.  Keep the path, raw identity, and current-sidecar checks
        # above; only avoid reporting the same missing-count result a second
        # time inside this one evidence transaction.
        return []
    return [
        Finding(
            source_record_judgment_freshness_severity(status),
            folder.name,
            rel(match_path),
            f"source-record audit has {len(required)} required boundary/field/semantic-model item(s), "
            f"but {len(missing)} lack current validated judgments for the same "
            "prompt version and audit digest: "
            + ", ".join(missing[:5])
            + ("; ..." if len(missing) > 5 else ""),
        )
    ]


def direct_source_row_review_receipt_state(
    folder: Path, *, require_source_bytes: bool = True
) -> tuple[bool, str]:
    """Return whether a canonical receipt selects and validates the direct lane.

    The receipt is optional.  Its absence does not change the ordinary raw
    source-record policy; an existing but invalid receipt remains visible as a
    separate closeout error rather than silently falling back to a bypass.
    """

    try:
        try:
            from scripts.final_closure_receipt import (
                DIRECT_SOURCE_ROW_REVIEW_LANE,
                final_closure_receipt_error,
                final_closure_receipt_path,
            )
        except ModuleNotFoundError:
            from final_closure_receipt import (
                DIRECT_SOURCE_ROW_REVIEW_LANE,
                final_closure_receipt_error,
                final_closure_receipt_path,
            )
        receipt_path = final_closure_receipt_path(ROOT, folder.name)
        if not receipt_path.is_file():
            return False, ""
        error = final_closure_receipt_error(
            ROOT,
            folder.name,
            required_lane=DIRECT_SOURCE_ROW_REVIEW_LANE,
            allow_missing_source_bytes=not require_source_bytes,
        )
        return error == "", error
    except Exception as exc:  # noqa: BLE001 - receipt validation must fail closed.
        return False, f"could not validate canonical direct-review receipt: {exc}"


def final_closure_receipt_findings(
    folder: Path, *, require_source_bytes: bool = True
) -> list[Finding]:
    """Expose an invalid optional canonical receipt without inventing a lane."""

    current, error = direct_source_row_review_receipt_state(
        folder, require_source_bytes=require_source_bytes
    )
    if current or not error:
        return []
    try:
        path = (folder / "FINAL_CLOSURE_RECEIPT.md").relative_to(ROOT)
        display = str(path)
    except ValueError:
        display = str(folder / "FINAL_CLOSURE_RECEIPT.md")
    return [
        Finding(
            "ERROR",
            folder.name,
            display,
            "canonical direct-source-row-review receipt is invalid: " + error,
        )
    ]


def source_record_semantic_target_disposition_findings(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Validate current v10 semantic target verdicts against map and ledger.

    The ordinary source-record freshness gate proves that a response belongs to
    the current generated Lean surface.  This complementary gate decides what
    target that response is allowed to call source-faithful: literal archival
    text, a documented source-model convention, or an approved replacement.
    It runs only for v10 generated records with an explicit source-map
    association, preserving pre-v10 sidecars unchanged.
    """

    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    if context is not None:
        audit_path = context.audit_snapshot.path
        audit_path_error = context.audit_path_error
        match_path = context.match_snapshot.path
        match_path_error = context.match_path_error
    else:
        audit_path, audit_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_audit_file",
            default_basename="source_record_audit.json",
        )
        match_path, match_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_judgment_file",
            default_basename="source_record_match_llm.json",
        )
    if audit_path_error or match_path_error:
        return []
    assert audit_path is not None and match_path is not None
    audit_payload = (
        context.audit_payload if context is not None else load_json(audit_path)
    )
    if (
        not isinstance(audit_payload, dict)
        or str(audit_payload.get("prompt_version") or "").strip()
        != CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
    ):
        return []
    raw_semantic_items = audit_payload.get("semantic_model_items")
    if not isinstance(raw_semantic_items, list):
        return []
    current = (
        context.current_source_record_judgments
        if context is not None
        else current_source_record_judgment_items(
            audit_payload,
            load_json(match_path) or {},
            expected_paper_statement_map_sha256=current_paper_statement_map_sha256(
                folder
            ),
            folder=folder,
        )
    )
    if not current:
        return []

    statement_map_path = transaction_sidecar(
        folder, "paper_statement_map.json", context
    )
    statement_map = transaction_json(statement_map_path, context)
    ledger_path, ledger_path_error = source_proof_fidelity_ledger_path(
        folder, status_payload
    )
    source_proof_fidelity = (
        transaction_json(ledger_path, context)
        if ledger_path_error == "" and ledger_path is not None
        else None
    )
    severity = source_record_judgment_freshness_severity(status)
    findings: list[Finding] = []
    if context is not None:
        rebind = context.administrative_projection_rebind
        rebind_path = context.administrative_projection_rebind_path
        rebind_error = context.administrative_projection_rebind_error
    else:
        rebind, rebind_path, rebind_error = (
            source_record_administrative_projection_rebind_context(
                folder,
                status_payload,
                audit_path=audit_path,
                audit_payload=audit_payload,
                statement_map_path=statement_map_path,
                statement_map=statement_map,
            )
        )
    if rebind_error:
        findings.append(
            Finding(
                severity,
                folder.name,
                rel(rebind_path or audit_path),
                "administrative source-status projection rebind is invalid: " + rebind_error,
            )
        )
    for item in raw_semantic_items:
        if not isinstance(item, dict):
            continue
        key = str(item.get("judgment_key") or "").strip()
        judgment = current.get(key)
        if not key or not isinstance(judgment, dict):
            continue
        responses = judgment.get("semantic_model_dimensions")
        dimensions = item.get("dimensions")
        if not isinstance(responses, dict) or not isinstance(dimensions, list):
            continue
        for raw_dimension in dimensions:
            if not isinstance(raw_dimension, dict):
                continue
            dimension = str(raw_dimension.get("id") or "").strip()
            response = responses.get(dimension)
            if not dimension or not isinstance(response, dict):
                continue
            for error in semantic_target_disposition_errors(
                item,
                response,
                statement_map=statement_map,
                source_proof_fidelity=source_proof_fidelity,
                validated_vocabulary_binding_source_item_ids=(
                    audit_payload.get(
                        "source_coverage_validated_vocabulary_binding_source_items"
                    )
                ),
                validated_vocabulary_direct_route_source_item_ids=(
                    audit_payload.get(
                        "source_coverage_validated_vocabulary_direct_route_source_items"
                    )
                ),
                administrative_projection_rebind=rebind,
            ):
                findings.append(
                    Finding(
                        severity,
                        folder.name,
                        rel(match_path),
                        f"source-record semantic judgment `{key}` dimension "
                        f"`{dimension}` has invalid source target disposition: {error}",
                    )
                )
    return findings


def has_explicit_semantic_contract_route(statement_map: object) -> bool:
    """Return whether a source map declares a fully-qualified direct/Spec route.

    This is a structural source-map check. It deliberately does not compare a
    source map key, row, binder, or Lean function name with any audit item.
    The generator supplies the stronger declaration-content association once
    this route family is present.
    """

    if not isinstance(statement_map, dict):
        return False
    raw_items = statement_map.get("items")
    if not isinstance(raw_items, dict):
        return False
    for source_item in raw_items.values():
        if not isinstance(source_item, dict) or source_item.get("claim_bearing") is not True:
            continue
        contract = source_item.get("semantic_contract")
        if not isinstance(contract, dict):
            continue
        evidence = str(contract.get("evidence_declaration") or "").strip()
        spec = str(contract.get("spec_declaration") or "").strip()
        if evidence and spec and evidence != spec and "." in evidence and "." in spec:
            return True
    return False


def has_explicit_legacy_direct_source_route(statement_map: object) -> bool:
    """Return whether the selected source surface has a direct non-contract route.

    This follows the same source-presentation selection policy as the
    source-record generator. It does not infer a route from a map key, row, or
    declaration spelling: the map must explicitly list a fully-qualified
    direct route under one of the legacy direct-route fields, and an item with
    any semantic-contract metadata is intentionally left to the contract lane.
    """

    if not isinstance(statement_map, dict):
        return False
    raw_items = statement_map.get("items")
    if not isinstance(raw_items, dict):
        return False
    mode, mode_error = source_coverage_mode_from_map(statement_map)
    if mode_error:
        return False
    selected_items = filter_source_map_items_for_coverage(
        raw_items,
        mode,
        declared_environment_kinds=source_named_result_environment_kinds_from_map(
            statement_map
        ),
    )
    for source_item in selected_items.values():
        if not isinstance(source_item, dict):
            continue
        if source_item.get("claim_bearing") is False:
            continue
        if source_item.get("semantic_contract") is not None:
            continue
        for field in (
            "lean_declarations",
            "proof_lean_declarations",
            "spec_lean_declarations",
        ):
            routes = source_item.get(field)
            if not isinstance(routes, list):
                continue
            if any(
                isinstance(route, str)
                and route.strip()
                and "." in route.strip()
                for route in routes
            ):
                return True
    return False


def source_record_input_target_disposition_findings(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Validate current v10 boundary/conclusion source-credit dispositions.

    This mirrors the repository gate, but runs from saved artifacts during the
    fast integrity pass.  It validates only generator-owned source-contract
    associations and their content pins; no row, binder, or Lean function name
    is used to decide the route.
    """

    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    if context is not None:
        audit_path = context.audit_snapshot.path
        audit_path_error = context.audit_path_error
        match_path = context.match_snapshot.path
        match_path_error = context.match_path_error
    else:
        audit_path, audit_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_audit_file",
            default_basename="source_record_audit.json",
        )
        match_path, match_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_judgment_file",
            default_basename="source_record_match_llm.json",
        )
    if audit_path_error or match_path_error:
        return []
    assert audit_path is not None and match_path is not None
    audit_payload = (
        context.audit_payload if context is not None else load_json(audit_path)
    )
    if (
        not isinstance(audit_payload, dict)
        or str(audit_payload.get("prompt_version") or "").strip()
        != CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
    ):
        return []
    severity = source_record_judgment_freshness_severity(status)
    findings: list[Finding] = []
    if context is not None:
        semantic_contract_revalidation = context.semantic_contract_revalidation
        semantic_contract_revalidation_error = (
            context.semantic_contract_revalidation_error
        )
    else:
        (
            semantic_contract_revalidation,
            semantic_contract_revalidation_error,
        ) = source_record_semantic_contract_revalidation_context(
            folder, audit_payload
        )
    if semantic_contract_revalidation_error:
        findings.append(
            Finding(
                severity,
                folder.name,
                rel(audit_path),
                "semantic-contract revalidation is invalid: "
                + semantic_contract_revalidation_error,
            )
        )
    effective_semantic_errors = source_record_effective_semantic_errors(
        audit_payload,
        semantic_contract_revalidation=semantic_contract_revalidation,
    )
    statement_map_path = transaction_sidecar(
        folder, "paper_statement_map.json", context
    )
    statement_map = transaction_json(statement_map_path, context)
    if context is not None:
        rebind = context.administrative_projection_rebind
        rebind_path = context.administrative_projection_rebind_path
        rebind_error = context.administrative_projection_rebind_error
    else:
        rebind, rebind_path, rebind_error = (
            source_record_administrative_projection_rebind_context(
                folder,
                status_payload,
                audit_path=audit_path,
                audit_payload=audit_payload,
                statement_map_path=statement_map_path,
                statement_map=statement_map,
            )
        )
    if rebind_error:
        findings.append(
            Finding(
                severity,
                folder.name,
                rel(rebind_path or audit_path),
                "administrative source-status projection rebind is invalid: "
                + rebind_error,
            )
        )
    has_input_surface = any(
        isinstance(audit_payload.get(section), list)
        and bool(audit_payload.get(section))
        for section in ("boundary_input_items", "conclusion_dependency_items")
    )
    has_contract_route = has_explicit_semantic_contract_route(statement_map)
    has_legacy_direct_route = has_explicit_legacy_direct_source_route(statement_map)
    if (
        (has_legacy_direct_route or (has_input_surface and has_contract_route))
        and not schema_version_is_supported(
            audit_payload.get("source_contract_association_schema"), {1, 2}
        )
    ):
        missing_schema_message = (
            "v10 source-record artifact has an explicit semantic-contract route but "
            "no generated declaration-content source-contract association schema; regenerate the audit"
            if has_contract_route and not has_legacy_direct_route
            else "v10 source-record artifact has an explicit source route but no "
            "generated declaration-content source association schema; regenerate the audit"
        )
        findings.append(
            Finding(
                severity,
                folder.name,
                rel(audit_path),
                missing_schema_message,
            )
        )
    if has_legacy_direct_route:
        counts = audit_payload.get("source_contract_association_counts")
        direct_declaration_count = (
            counts.get("explicit_direct_route_declaration_count")
            if isinstance(counts, dict)
            else None
        )
        direct_association_count = (
            counts.get("explicit_direct_route_association_count")
            if isinstance(counts, dict)
            else None
        )
        if not isinstance(direct_declaration_count, int) or not isinstance(
            direct_association_count, int
        ):
            findings.append(
                Finding(
                    severity,
                    folder.name,
                    rel(audit_path),
                    "v10 source-record artifact has an explicit selected direct source route "
                    "but no generated direct-route association inventory; regenerate the audit",
                )
            )
        elif direct_declaration_count != direct_association_count:
            findings.append(
                Finding(
                    severity,
                    folder.name,
                    rel(audit_path),
                    "generated explicit direct source-route associations are incomplete or "
                    "ambiguous; inspect source_contract_association_errors and regenerate the audit",
                )
            )
    for error in effective_semantic_errors.get(
        "source_contract_association_errors",
        audit_payload.get("source_contract_association_errors") or [],
    ):
        message = str(error).strip()
        if message:
            findings.append(
                Finding(
                    severity,
                    folder.name,
                    rel(audit_path),
                    "generated source-contract association is invalid: " + message,
                )
            )

    current = (
        context.current_source_record_judgments
        if context is not None
        else current_source_record_judgment_items(
            audit_payload,
            load_json(match_path) or {},
            expected_paper_statement_map_sha256=current_paper_statement_map_sha256(
                folder
            ),
            folder=folder,
        )
    )
    if not current:
        return findings
    ledger_path, ledger_path_error = source_proof_fidelity_ledger_path(
        folder, status_payload
    )
    source_proof_fidelity = (
        transaction_json(ledger_path, context)
        if ledger_path_error == "" and ledger_path is not None
        else None
    )
    if context is not None:
        regularity_context = context.configured_assumption_regularity_context
    else:
        regularity_context, _regularity_context_error = (
            load_configured_assumption_formalization_regularity_context(
                folder,
                audit_payload,
                status_payload=status_payload,
            )
        )
    seen: set[tuple[str, str]] = set()
    for section in ("boundary_input_items", "conclusion_dependency_items"):
        raw_items = audit_payload.get(section)
        if not isinstance(raw_items, list):
            continue
        for item in raw_items:
            if not isinstance(item, dict):
                continue
            key = str(item.get("judgment_key") or "").strip()
            judgment = current.get(key)
            if not key or not isinstance(judgment, dict):
                continue
            for error in source_input_target_disposition_errors(
                item,
                judgment,
                statement_map=statement_map,
                source_proof_fidelity=source_proof_fidelity,
                status=status,
                administrative_projection_rebind=rebind,
                configured_assumption_formalization_regularity_context=(
                    regularity_context
                ),
            ):
                dedupe_key = (key, error)
                if dedupe_key in seen:
                    continue
                seen.add(dedupe_key)
                findings.append(
                    Finding(
                        severity,
                        folder.name,
                        rel(match_path),
                        f"source-record input judgment `{key}` has invalid source target disposition: {error}",
                    )
                )
    return findings


def source_record_recursive_field_target_disposition_findings(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Validate convention credit on generated recursive-field route receipts.

    A recursive-field receipt is narrower than a normal theorem-input source
    contract: it binds one structural ancestry path and one convention.  Run
    this saved-artifact check separately so a current LLM sidecar cannot swap
    the convention or use a container receipt to credit an unscoped leaf.
    """

    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    if context is not None:
        audit_path = context.audit_snapshot.path
        audit_path_error = context.audit_path_error
        match_path = context.match_snapshot.path
        match_path_error = context.match_path_error
    else:
        audit_path, audit_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_audit_file",
            default_basename="source_record_audit.json",
        )
        match_path, match_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_judgment_file",
            default_basename="source_record_match_llm.json",
        )
    if audit_path_error or match_path_error:
        return []
    assert audit_path is not None and match_path is not None
    audit_payload = (
        context.audit_payload if context is not None else load_json(audit_path)
    )
    if (
        not isinstance(audit_payload, dict)
        or str(audit_payload.get("prompt_version") or "").strip()
        != CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
    ):
        return []
    raw_items = audit_payload.get("recursive_field_items")
    if not isinstance(raw_items, list):
        return []
    current = (
        context.current_source_record_judgments
        if context is not None
        else current_source_record_judgment_items(
            audit_payload,
            load_json(match_path) or {},
            expected_paper_statement_map_sha256=current_paper_statement_map_sha256(
                folder
            ),
            folder=folder,
        )
    )
    if not current:
        return []
    statement_map_path = transaction_sidecar(
        folder, "paper_statement_map.json", context
    )
    statement_map = transaction_json(statement_map_path, context)
    ledger_path, ledger_path_error = source_proof_fidelity_ledger_path(
        folder, status_payload
    )
    source_proof_fidelity = (
        transaction_json(ledger_path, context)
        if ledger_path_error == "" and ledger_path is not None
        else None
    )
    severity = source_record_judgment_freshness_severity(status)
    findings: list[Finding] = []
    if context is not None:
        rebind = context.administrative_projection_rebind
        rebind_path = context.administrative_projection_rebind_path
        rebind_error = context.administrative_projection_rebind_error
    else:
        rebind, rebind_path, rebind_error = (
            source_record_administrative_projection_rebind_context(
                folder,
                status_payload,
                audit_path=audit_path,
                audit_payload=audit_payload,
                statement_map_path=statement_map_path,
                statement_map=statement_map,
            )
        )
    if rebind_error:
        findings.append(
            Finding(
                severity,
                folder.name,
                rel(rebind_path or audit_path),
                "administrative source-status projection rebind is invalid: "
                + rebind_error,
            )
        )
    for item in raw_items:
        if not isinstance(item, dict):
            continue
        key = str(item.get("judgment_key") or "").strip()
        judgment = current.get(key)
        if not key or not isinstance(judgment, dict):
            continue
        for error in recursive_field_target_disposition_errors(
            item,
            judgment,
            statement_map=statement_map,
            source_proof_fidelity=source_proof_fidelity,
            administrative_projection_rebind=rebind,
        ):
            findings.append(
                Finding(
                    severity,
                    folder.name,
                    rel(match_path),
                    f"source-record recursive-field judgment `{key}` has invalid "
                    f"source target disposition: {error}",
                )
            )
    return findings


def check_plain_formalized_unresolved_source_record_math(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Plain `formalized` cannot retain current unresolved proof obligations."""

    if status != PLAIN_FORMALIZED:
        return []
    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    corrected_scope_current = (
        context.corrected_scope_current
        if context is not None
        else author_approved_corrected_scope_contract_is_current(
            folder, status_payload
        )
    )
    if corrected_scope_current:
        return []
    if context is not None:
        audit_path = context.audit_snapshot.path
        audit_path_error = context.audit_path_error
        match_path = context.match_snapshot.path
        match_path_error = context.match_path_error
    else:
        audit_path, audit_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_audit_file",
            default_basename="source_record_audit.json",
        )
        match_path, match_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_judgment_file",
            default_basename="source_record_match_llm.json",
        )
    if audit_path_error or match_path_error:
        return [
            Finding(
                "ERROR",
                folder.name,
                rel(folder / "status.json"),
                audit_path_error or match_path_error,
            )
        ]
    assert audit_path is not None and match_path is not None
    audit_payload = (
        context.audit_payload if context is not None else load_json(audit_path)
    )
    if audit_payload is None:
        return []
    semantic_contract_revalidation = (
        context.semantic_contract_revalidation
        if context is not None
        else source_record_semantic_contract_revalidation_context(
            folder, audit_payload
        )[0]
    )
    required = set(
        source_record_required_keys(
            audit_payload,
            semantic_contract_revalidation=semantic_contract_revalidation,
        )
    )
    current = (
        context.current_source_record_judgments
        if context is not None
        else current_source_record_judgment_items(
            audit_payload,
            load_json(match_path) or {},
            expected_paper_statement_map_sha256=current_paper_statement_map_sha256(
                folder
            ),
            folder=folder,
        )
    )
    unresolved = sorted(
        key
        for key, value in current.items()
        if key in required
        and str(
            value.get("classification")
            or value.get("judgment")
            or value.get("verdict")
            or value.get("status")
            or ""
        ).strip()
        == "unresolved_assumed_math"
    )
    if not unresolved:
        return []
    return [
        Finding(
            "ERROR",
            folder.name,
            rel(match_path),
            "plain `formalized` status conflicts with "
            f"{len(unresolved)} current source-record item(s) still classified "
            "as unresolved_assumed_math: "
            + ", ".join(unresolved[:5])
            + ("; ..." if len(unresolved) > 5 else ""),
        )
    ]


def check_full_closeout_open_semantic_model_dimensions(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Block either full status when current model semantics remain unresolved."""

    if status not in FULL_CLOSEOUT_STATUSES:
        return []
    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    corrected_scope_current = (
        context.corrected_scope_current
        if context is not None
        else author_approved_corrected_scope_contract_is_current(
            folder, status_payload
        )
    )
    if corrected_scope_current:
        return []
    if context is not None:
        audit_path = context.audit_snapshot.path
        audit_path_error = context.audit_path_error
        match_path = context.match_snapshot.path
        match_path_error = context.match_path_error
    else:
        audit_path, audit_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_audit_file",
            default_basename="source_record_audit.json",
        )
        match_path, match_path_error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field="source_record_judgment_file",
            default_basename="source_record_match_llm.json",
        )
    if audit_path_error or match_path_error:
        return [
            Finding(
                "ERROR",
                folder.name,
                rel(folder / "status.json"),
                audit_path_error or match_path_error,
            )
        ]
    assert audit_path is not None and match_path is not None
    audit_payload = (
        context.audit_payload if context is not None else load_json(audit_path)
    )
    if audit_payload is None:
        return []
    current = (
        context.current_source_record_judgments
        if context is not None
        else current_source_record_judgment_items(
            audit_payload,
            load_json(match_path) or {},
            expected_paper_statement_map_sha256=current_paper_statement_map_sha256(
                folder
            ),
            folder=folder,
        )
    )
    open_semantic_dimensions = current_open_semantic_model_dimensions(
        audit_payload, current
    )
    if not open_semantic_dimensions:
        return []
    return [
        Finding(
            "ERROR",
            folder.name,
            rel(match_path),
            f"full-closeout status `{status}` conflicts with "
            f"{len(open_semantic_dimensions)} current semantic-model dimension(s) "
            "that remain mismatch_or_open/documented_partial_boundary: "
            + ", ".join(open_semantic_dimensions[:5])
            + ("; ..." if len(open_semantic_dimensions) > 5 else ""),
        )
    ]


def check_current_unresolved_source_record_math(
    folder: Path,
    status: str,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Opt-in remediation tracker for current unresolved source-record math debt."""

    if status == PLAIN_FORMALIZED:
        return []
    audit_path = canonical_sidecar(folder, "source_record_audit.json")
    match_path = canonical_sidecar(folder, "source_record_match_llm.json")
    use_context = (
        context is not None
        and context.audit_snapshot.path.resolve() == audit_path.resolve()
        and context.match_snapshot.path.resolve() == match_path.resolve()
    )
    audit_payload = context.audit_payload if use_context else load_json(audit_path)
    if audit_payload is None:
        return []
    semantic_contract_revalidation = (
        context.semantic_contract_revalidation
        if use_context and context is not None
        else source_record_semantic_contract_revalidation_context(
            folder, audit_payload
        )[0]
    )
    required = set(
        source_record_required_keys(
            audit_payload,
            semantic_contract_revalidation=semantic_contract_revalidation,
        )
    )
    if not required:
        return []
    current = (
        context.current_source_record_judgments
        if use_context and context is not None
        else current_source_record_judgment_items(
            audit_payload,
            load_json(match_path) or {},
            expected_paper_statement_map_sha256=current_paper_statement_map_sha256(
                folder
            ),
            folder=folder,
        )
    )
    unresolved = sorted(
        key
        for key, value in current.items()
        if key in required
        and str(
            value.get("classification")
            or value.get("judgment")
            or value.get("verdict")
            or value.get("status")
            or ""
        ).strip()
        == "unresolved_assumed_math"
    )
    open_semantic_dimensions = (
        []
        if status in FULL_CLOSEOUT_STATUSES
        else current_open_semantic_model_dimensions(audit_payload, current)
    )
    if not unresolved and not open_semantic_dimensions:
        return []
    details: list[str] = []
    if unresolved:
        details.append(
            f"{len(unresolved)} current source-record item(s) remain "
            "classified as unresolved_assumed_math: "
            + ", ".join(unresolved[:5])
            + ("; ..." if len(unresolved) > 5 else "")
        )
    if open_semantic_dimensions:
        details.append(
            f"{len(open_semantic_dimensions)} current semantic-model dimension(s) "
            "remain mismatch_or_open/documented_partial_boundary: "
            + ", ".join(open_semantic_dimensions[:5])
            + ("; ..." if len(open_semantic_dimensions) > 5 else "")
        )
    return [
        Finding(
            "WARN",
            folder.name,
            rel(match_path),
            " | ".join(details),
        )
    ]


def check_validator_independence(
    folder: Path,
    status: str,
    release: bool = False,
    *,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Report shared audit identities without mistaking them for proof failure.

    A paper can be mathematically closed after a transparently recorded
    single-agent audit, but it cannot be release-certified as independently
    reviewed. Keep the lack of independence visible in every mode and make it
    blocking only for the explicit release gate.
    """

    lane_payloads: dict[str, dict[str, Any]] = {}
    for basename in INDEPENDENT_LANES:
        path = transaction_sidecar(folder, basename, context)
        payload = transaction_json(path, context)
        if payload is None or not sidecar_has_items(payload):
            continue
        lane_payloads[basename] = payload

    judge_keys = {"validator", "model", "judge", "agent"}
    translator_ids = identities_for_keys(
        lane_payloads.get("lean_to_tex_llm.json", {}),
        {"translator", "translation_producer", "producer"},
    )
    statement_judge_ids = identities_for_keys(
        lane_payloads.get("statement_match_llm.json", {}), judge_keys
    )
    coverage_judge_ids = identities_for_keys(
        lane_payloads.get("paper_coverage_llm.json", {}), judge_keys
    )
    defect_support_judge_ids = identities_for_keys(
        lane_payloads.get("defect_support_match_llm.json", {}), judge_keys
    )
    source_manifest_path = transaction_sidecar(
        folder, "paper_statement_map.json", context
    )
    source_manifest = transaction_json(source_manifest_path, context) or {}
    source_curator_ids = identities_for_keys(
        source_manifest,
        {"source_curator", "curator", "source_inventory_producer", "producer"},
    )
    status_payload = (
        context.status_payload
        if context is not None
        else (load_json(folder / "status.json") or {})
    )
    formalizer_ids = identities_for_keys(
        status_payload,
        {"formalizer", "formalization_agent", "formalization_producer"},
    )

    roles = [
        ("formalizer", formalizer_ids),
        ("source curator", source_curator_ids),
        ("Lean translator", translator_ids),
        ("statement judge", statement_judge_ids),
        ("coverage judge", coverage_judge_ids),
        ("defect-support judge", defect_support_judge_ids),
    ]
    role_pairs = [
        (left_role, left_ids, right_role, right_ids)
        for index, (left_role, left_ids) in enumerate(roles)
        for right_role, right_ids in roles[index + 1 :]
    ]
    findings: list[Finding] = []
    severity = "ERROR" if release and status in CLOSEOUT_STATUSES else "WARN"
    for left_role, left_ids, right_role, right_ids in role_pairs:
        overlap = sorted(left_ids & right_ids)
        if not overlap:
            continue
        findings.append(
            Finding(
                severity,
                folder.name,
                rel(folder / "audit"),
                f"{left_role} and {right_role} roles share identity attestation(s): "
                f"{', '.join(overlap)}; this is single-agent review evidence, "
                "not independent-review certification",
            )
        )
    return findings


def check_human_review(
    folder: Path,
    status: str,
    payload: dict[str, Any],
    release: bool,
    *,
    review_log_present: bool | None = None,
) -> list[Finding]:
    review = payload.get("human_review")
    if not isinstance(review, dict):
        return []
    reviewed = int(review.get("reviewed_rows") or 0)
    total = int(review.get("total_rows") or 0)
    findings: list[Finding] = []
    log_path = folder / ".review_traces" / "paper_theorem_validations.jsonl"
    log_present = log_path.exists() if review_log_present is None else review_log_present
    if reviewed > 0 and not log_present:
        findings.append(
            Finding(
                "ERROR",
                folder.name,
                rel(folder / "status.json"),
                f"status claims {reviewed} human-reviewed row(s), but no append-only review log is tracked at {rel(log_path)}",
            )
        )
    if status in CLOSEOUT_STATUSES and reviewed < total:
        findings.append(
            Finding(
                # A human packet is deliberately a review invitation and
                # evidence record, not a prerequisite for publishing a
                # mathematically closed paper.  Keep an incomplete packet
                # visible in every mode, but never manufacture a sign-off or
                # turn its absence into a release block.
                "WARN",
                folder.name,
                rel(folder / "status.json"),
                f"source-to-Lean human review is incomplete ({reviewed}/{total}); independent human review remains pending",
            )
        )
    return findings


def check_vacuous_assumptions(
    folder: Path,
    status: str,
    *,
    source_bytes_override: bytes | None | object = _UNSET,
) -> list[Finding]:
    path = folder / "Assumptions.lean"
    if source_bytes_override is _UNSET:
        try:
            source_text = path.read_text(encoding="utf-8")
        except OSError:
            return []
    elif source_bytes_override is None:
        return []
    elif isinstance(source_bytes_override, bytes):
        try:
            source_text = source_bytes_override.decode("utf-8")
        except UnicodeDecodeError:
            return [
                Finding(
                    finding_severity(status),
                    folder.name,
                    rel(path),
                    "Assumptions.lean is not valid UTF-8",
                )
            ]
    else:
        return []
    names = sorted(set(VACUOUS_ASSUMPTION_RE.findall(source_text)))
    if not names:
        return []
    return [
        Finding(
            finding_severity(status),
            folder.name,
            rel(path),
            "vacuous `Prop := True` assumption wrapper(s) can hide data/certificate boundaries: "
            + ", ".join(names),
        )
    ]


def active_papers() -> set[str]:
    payload = load_json(AUDIT_CONFIG) or {}
    return active_papers_from_payload(payload)


def active_papers_from_payload(payload: Mapping[str, Any]) -> set[str]:
    """Read active-paper routing from one already snapshotted config."""

    raw = payload.get("active_papers") or []
    return {str(item) for item in raw if str(item)} if isinstance(raw, list) else set()


def check_active_status(folder: Path, status: str, active: set[str]) -> list[Finding]:
    if folder.name not in active or status not in {"formalized", "formalized with caveat"}:
        return []
    return [
        Finding(
            "ERROR",
            folder.name,
            rel(AUDIT_CONFIG),
            f"paper is skipped as active while claiming closeout status `{status}`",
        )
    ]


def lake_targets(
    *, raw_bytes_override: bytes | None | object = _UNSET
) -> tuple[set[str], set[str]]:
    try:
        if raw_bytes_override is _UNSET:
            source = LAKEFILE.read_text(encoding="utf-8")
        elif isinstance(raw_bytes_override, bytes):
            source = raw_bytes_override.decode("utf-8")
        else:
            return set(), set()
        payload = tomllib.loads(source)
    except (OSError, UnicodeDecodeError, tomllib.TOMLDecodeError):
        return set(), set()
    defaults = {str(item) for item in payload.get("defaultTargets") or []}
    libraries = {
        str(item.get("name"))
        for item in payload.get("lean_lib") or []
        if isinstance(item, dict) and item.get("name")
    }
    return defaults, libraries


def _configured_build_command_segments(command: str) -> list[list[str]]:
    """Return shell-command segments from a status ``build_target`` string.

    This is intentionally a narrow static parser: the audit never executes a
    status command, and only recognizes ordinary ``lake`` invocations separated
    by shell control operators. Malformed quoting simply yields no recognized
    focused route and therefore fails closed at closeout.
    """

    try:
        raw_segments = re.split(r"(?:&&|\|\||;)", command)
        return [shlex.split(segment) for segment in raw_segments if segment.strip()]
    except ValueError:
        return []


def _strip_environment_prefix(tokens: list[str]) -> list[str]:
    """Remove conventional leading environment assignments from one command."""

    index = 0
    assignment = re.compile(r"[A-Za-z_][A-Za-z0-9_]*=.*")
    while index < len(tokens) and assignment.fullmatch(tokens[index]):
        index += 1
    if index < len(tokens) and tokens[index] == "env":
        index += 1
        while index < len(tokens) and (
            assignment.fullmatch(tokens[index]) or tokens[index].startswith("-")
        ):
            index += 1
    return tokens[index:]


def configured_focused_build_routes(
    folder: Path, payload: Mapping[str, Any]
) -> tuple[set[str], bool]:
    """Find explicit paper-scoped build routes in ``status.build_target``.

    A closeout may build the registered paper library, a module beneath that
    library (including a forced ``+Paper.PaperInterface`` target), or directly
    elaborate the canonical paper interface with ``lake env lean``. The latter
    supports papers whose interface needs a separate direct elaboration after a
    shared-library build. Merely being listed in ``defaultTargets`` is not a
    paper build route.
    """

    command = payload.get("build_target")
    if not isinstance(command, str) or not command.strip():
        return set(), False

    library = folder.name
    interface_path = f"papers/{library}/PaperInterface.lean"
    targets: set[str] = set()
    direct_interface = False
    for raw_tokens in _configured_build_command_segments(command):
        tokens = _strip_environment_prefix(raw_tokens)
        if len(tokens) >= 3 and tokens[:2] == ["lake", "build"]:
            target = tokens[2]
            canonical_target = target[1:] if target.startswith("+") else target
            if canonical_target == library or canonical_target.startswith(
                library + "."
            ):
                targets.add(target)
            continue
        if len(tokens) >= 4 and tokens[:3] == ["lake", "env", "lean"]:
            direct_interface = direct_interface or any(
                argument.removeprefix("./") == interface_path
                for argument in tokens[3:]
            )
    return targets, direct_interface


def check_build_coverage(
    folder: Path,
    status: str,
    payload: dict[str, Any],
    _defaults: set[str],
    libraries: set[str],
) -> list[Finding]:
    if status not in CLOSEOUT_STATUSES:
        return []
    findings: list[Finding] = []
    if folder.name not in libraries:
        findings.append(
            Finding(
                "ERROR",
                folder.name,
                rel(LAKEFILE),
                f"closeout paper Lean library `{folder.name}` is not declared in `lean_lib`",
            )
        )
    focused_targets, direct_interface = configured_focused_build_routes(
        folder, payload
    )
    if not focused_targets and not direct_interface:
        findings.append(
            Finding(
                "ERROR",
                folder.name,
                rel(folder / "status.json"),
                "closeout paper needs an explicit focused `build_target`: "
                f"`lake build {folder.name}`, a `{folder.name}.…` module target, "
                f"or `lake env lean papers/{folder.name}/PaperInterface.lean`",
            )
        )
    return findings


def check_report_generator(
    *, raw_bytes_override: bytes | None | object = _UNSET
) -> list[Finding]:
    path = ROOT / "scripts" / "refresh_validation_report_audit_summaries.py"
    try:
        if raw_bytes_override is _UNSET:
            text = path.read_text(encoding="utf-8")
        elif isinstance(raw_bytes_override, bytes):
            text = raw_bytes_override.decode("utf-8")
        else:
            return []
    except (OSError, UnicodeDecodeError):
        return []
    if not re.search(r"holistic source-first audit PASS|audit \([^\n]+\): PASS", text):
        return []
    return [
        Finding(
            "ERROR",
            "REPO",
            rel(path),
            "report generator contains unconditional PASS certification text",
        )
    ]


def build_evidence_run_context(
    folder: Path,
    *,
    diagnostics: MutableMapping[str, int] | None = None,
) -> EvidenceRunContext:
    """Build one exact, nonpersistent evidence transaction for ``folder``."""

    _increment_diagnostic(diagnostics, EVIDENCE_DIAGNOSTIC_CONTEXTS)
    snapshots_by_path: dict[Path, EvidenceJSONSnapshot] = {}

    def snapshot(path: Path) -> EvidenceJSONSnapshot:
        try:
            key = path.resolve()
        except (OSError, RuntimeError):
            key = path
        saved = snapshots_by_path.get(key)
        if saved is None:
            saved = _load_json_snapshot(path)
            snapshots_by_path[key] = saved
        return saved

    def canonical_snapshot_path(basename: str) -> Path:
        """Choose an organized/legacy sidecar from the acquired snapshots."""

        organized = folder / "audit" / basename
        legacy = folder / basename
        organized_snapshot = snapshot(organized)
        snapshot(legacy)
        return organized if organized_snapshot.sha256 is not None else legacy

    status_snapshot = snapshot(folder / "status.json")
    audit_config_snapshot = snapshot(AUDIT_CONFIG)
    status_payload = status_snapshot.payload or {}
    status = str(status_payload.get("status") or "").strip().lower()

    review_surface = status_payload.get("review_surface")
    source_record_review = (
        review_surface.get("llm_source_record_review")
        if isinstance(review_surface, dict)
        else None
    )

    def configured_source_record_path(
        *, config_field: str, default_basename: str
    ) -> tuple[Path, str]:
        raw_path = (
            source_record_review.get(config_field)
            if isinstance(source_record_review, dict)
            else None
        )
        if not isinstance(raw_path, str) or not raw_path.strip():
            return canonical_snapshot_path(default_basename), ""
        configured, error = source_record_review_sidecar_path(
            folder,
            status_payload,
            config_field=config_field,
            default_basename=default_basename,
        )
        if configured is None:
            return canonical_snapshot_path(default_basename), error
        snapshot(configured)
        return configured, error

    audit_path, audit_path_error = configured_source_record_path(
        config_field="source_record_audit_file",
        default_basename="source_record_audit.json",
    )
    match_path, match_path_error = configured_source_record_path(
        config_field="source_record_judgment_file",
        default_basename="source_record_match_llm.json",
    )
    statement_map_path = canonical_snapshot_path("paper_statement_map.json")
    audit_snapshot = snapshot(audit_path)
    match_snapshot = snapshot(match_path)
    statement_map_snapshot = snapshot(statement_map_path)

    ledger_path, ledger_path_error = source_proof_fidelity_ledger_path(
        folder, status_payload
    )
    ledger_snapshot = (
        snapshot(ledger_path) if ledger_path is not None else None
    )

    # Acquire every canonical and legacy audit sidecar before any lane derives
    # a verdict.  Besides avoiding repeated JSON parsing, recording absent paths
    # makes a sidecar created during the run an ordinary input mutation.
    for basename in AUDIT_SIDECARS:
        snapshot(folder / basename)
        snapshot(folder / "audit" / basename)
    for basename in SOURCE_RECORD_OPTIONAL_AUTHORITY_SIDECARS:
        snapshot(folder / basename)
        snapshot(folder / "audit" / basename)
    semantic_contract_revalidation_artifact_snapshot = snapshot(
        folder / "audit" / "source_record_semantic_contract_revalidation.json"
    )
    semantic_contract_revalidation_authority_snapshot = snapshot(
        folder / "audit" / "lean_signature_manifest_cache_authority.json"
    )
    # The derived-component receipt is a fixed optional authority artifact.
    # Its only noncanonical input is one receipt-declared, paper-local base
    # sidecar.  Freeze that bounded edge only after a self-authenticating
    # envelope nominates it; malformed receipts never trigger a directory scan
    # or a live fallback during this transaction.
    component_projection = _component_projection_module()
    component_projection_artifact_path = (
        component_projection.component_projection_artifact_path(folder)
    )
    component_projection_artifact_snapshot = snapshot(
        component_projection_artifact_path
    )
    component_projection_base_path: Path | None = None
    component_projection_base_payload: Mapping[str, Any] | None = None
    if component_projection_artifact_snapshot.raw_bytes is not None:
        component_projection_base_path = (
            component_projection.component_projection_declared_base_judgment_sidecar_path(
                component_projection_artifact_snapshot.payload,
                paper_dir=folder,
                paper=folder.name,
            )
        )
        if component_projection_base_path is not None:
            component_projection_base_snapshot = snapshot(
                component_projection_base_path
            )
            component_projection_base_payload = (
                component_projection_base_snapshot.payload
            )
    component_projection_frozen_inputs = (
        component_projection.ComponentProjectionFrozenInputs(
            artifact_path=component_projection_artifact_path,
            artifact_present=(
                component_projection_artifact_snapshot.raw_bytes is not None
            ),
            artifact_payload=component_projection_artifact_snapshot.payload,
            base_sidecar_path=component_projection_base_path,
            base_sidecar_payload=component_projection_base_payload,
        )
    )
    # This receipt is optional and is therefore not part of AUDIT_SIDECARS'
    # ordinary lane validation.  Freeze both default discovery locations so an
    # absent receipt cannot appear, or an existing one change, midway through
    # the transaction.
    snapshot(folder / SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME)
    snapshot(
        folder
        / "audit"
        / SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME
    )
    regularity_path = (
        folder / CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_FILE
    )
    # Capture the optional pair unconditionally. Explicit absence is part of
    # the transaction and avoids a live existence probe before finalization.
    snapshot(regularity_path)
    snapshot(folder / "source.txt")
    if isinstance(review_surface, dict):
        # A paper may route a review lane to a noncanonical paper-local file.
        # Freeze every configured JSON sidecar before any validator runs so a
        # closeout never combines a current canonical artifact with a live
        # reread of a configured alternative (or vice versa).
        for section_name in (
            "llm_statement_review",
            "llm_paper_coverage_review",
            "llm_source_record_review",
        ):
            section = review_surface.get(section_name)
            if not isinstance(section, dict):
                continue
            for field_name, raw_path in section.items():
                if not str(field_name).endswith("_file"):
                    continue
                configured_path, configured_error = resolve_paper_source_path(
                    folder, raw_path
                )
                if configured_path is not None and not configured_error:
                    snapshot(configured_path)
    statement_map_payload = statement_map_snapshot.payload
    raw_statement_items = (
        statement_map_payload.get("items")
        if isinstance(statement_map_payload, dict)
        else None
    )
    if isinstance(raw_statement_items, dict):
        for raw_item in raw_statement_items.values():
            if not isinstance(raw_item, dict):
                continue
            corrected_target = raw_item.get("corrected_target")
            approval = (
                corrected_target.get("approval")
                if isinstance(corrected_target, dict)
                else None
            )
            if isinstance(approval, dict):
                approval_path = _paper_local_artifact_path(
                    folder, approval.get("artifact_path")
                )
                if approval_path is not None:
                    snapshot(approval_path)
    corrected_scope = author_approved_corrected_scope(status_payload)
    if isinstance(corrected_scope, dict):
        for reference_field in ("approval", "semantic_contract", "base_archive"):
            reference = corrected_scope.get(reference_field)
            if not isinstance(reference, dict):
                continue
            artifact_path = _paper_local_artifact_path(folder, reference.get("path"))
            if artifact_path is None and reference_field == "approval":
                artifact_path = _paper_local_artifact_path(
                    folder, reference.get("artifact_path")
                )
            if artifact_path is not None:
                snapshot(artifact_path)

    # The strict dashboard consumes one bounded, declared set of human-facing
    # and source artifacts. Acquire every member once here so the dashboard can
    # neither discover a later file nor fall back to a live read mid-closeout.
    try:
        try:
            from scripts.review_dashboard import required_dashboard_audit_input_paths
        except ModuleNotFoundError:
            from review_dashboard import required_dashboard_audit_input_paths

        if isinstance(status_snapshot.raw_bytes, bytes):
            dashboard_paths = required_dashboard_audit_input_paths(
                folder,
                status_bytes=status_snapshot.raw_bytes,
                statement_map_bytes=statement_map_snapshot.raw_bytes,
                repository_root=ROOT,
            )
            for dashboard_path in dashboard_paths:
                snapshot(dashboard_path)
    except (OSError, RuntimeError, ValueError):
        # Malformed status/map inputs receive their ordinary closeout findings.
        # Do not derive a partial configured path set from untrusted bytes.
        pass
    # Freeze non-JSON controls consumed by the evidence lane as ordinary raw
    # byte snapshots. The JSON parser may return no payload for them; their
    # exact bytes and explicit absence still belong to this transaction.
    snapshot(LAKEFILE)
    snapshot(ROOT / "scripts" / "refresh_validation_report_audit_summaries.py")
    snapshot(folder / "Assumptions.lean")
    snapshot(folder / ".review_traces" / "paper_theorem_validations.jsonl")

    # A semantic-rebind overlay is an authority artifact even though the
    # source-record judgment loader reaches it indirectly.  Its root was
    # acquired with the optional sidecars above.  Follow only its explicitly
    # byte-pinned, paper-local provenance records, then repeat for JSON
    # provenance parents.  This is a bounded structural graph walk, never a
    # filename heuristic or an audit-directory scan.
    try:
        try:
            from scripts.source_record_semantic_rebind import (
                SOURCE_RECORD_SEMANTIC_REBIND_FILENAME,
                source_record_semantic_rebind_declared_provenance_paths,
            )
        except ModuleNotFoundError:
            from source_record_semantic_rebind import (
                SOURCE_RECORD_SEMANTIC_REBIND_FILENAME,
                source_record_semantic_rebind_declared_provenance_paths,
            )

        provenance_queue = [
            snapshot(folder / "audit" / SOURCE_RECORD_SEMANTIC_REBIND_FILENAME),
            snapshot(folder / SOURCE_RECORD_SEMANTIC_REBIND_FILENAME),
        ]
        seen_provenance_payload_paths: set[Path] = set()
        while provenance_queue:
            provenance_snapshot = provenance_queue.pop()
            try:
                provenance_key = provenance_snapshot.path.resolve()
            except (OSError, RuntimeError):
                continue
            if provenance_key in seen_provenance_payload_paths:
                continue
            seen_provenance_payload_paths.add(provenance_key)
            if len(seen_provenance_payload_paths) > 256:
                raise ValueError("semantic rebind provenance graph is too large")
            payload = provenance_snapshot.payload
            if not isinstance(payload, Mapping):
                continue
            for provenance_path in source_record_semantic_rebind_declared_provenance_paths(
                payload,
                paper_dir=folder,
            ):
                declared_snapshot = snapshot(provenance_path)
                if declared_snapshot.payload is not None:
                    provenance_queue.append(declared_snapshot)
    except (OSError, RuntimeError, ValueError):
        # Invalid rebind provenance remains unauthoritative through its own
        # replay validator.  The root snapshot is still watched, and no
        # malformed declaration can make this transaction read outside the
        # paper directory.
        pass

    core_snapshot_paths = {
        candidate.path.resolve()
        for candidate in (
            status_snapshot,
            audit_config_snapshot,
            audit_snapshot,
            match_snapshot,
            statement_map_snapshot,
            ledger_snapshot,
        )
        if candidate is not None
    }
    sidecar_snapshots = tuple(
        saved
        for key, saved in sorted(
            snapshots_by_path.items(), key=lambda item: str(item[0])
        )
        if key not in core_snapshot_paths
    )

    audit_payload = audit_snapshot.payload
    watched_input_digest = ""
    identity_error = ""
    current_surface = False
    semantic_contract_revalidation = None
    semantic_contract_revalidation_error = ""
    if isinstance(audit_payload, dict):
        current_surface = (
            str(audit_payload.get("source_record_policy_version") or "").strip()
            == CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
            or str(audit_payload.get("prompt_version") or "").strip()
            == CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
        )
        if current_surface:
            try:
                replay = _semantic_contract_revalidation_module()
                (
                    semantic_contract_revalidation,
                    semantic_contract_revalidation_error,
                ) = replay.semantic_contract_revalidation_projection(
                    paper_dir=folder,
                    paper=folder.name,
                    raw_audit=audit_payload,
                    raw_audit_raw_bytes=audit_snapshot.raw_bytes,
                    statement_map_payload=statement_map_snapshot.payload,
                    statement_map_raw_bytes=statement_map_snapshot.raw_bytes,
                    artifact_payload=(
                        semantic_contract_revalidation_artifact_snapshot.payload
                    ),
                    artifact_raw_bytes=(
                        semantic_contract_revalidation_artifact_snapshot.raw_bytes
                    ),
                    authority_payload=(
                        semantic_contract_revalidation_authority_snapshot.payload
                    ),
                    authority_raw_bytes=(
                        semantic_contract_revalidation_authority_snapshot.raw_bytes
                    ),
                )
            except Exception as error:  # noqa: BLE001 - authority fails closed.
                semantic_contract_revalidation = None
                semantic_contract_revalidation_error = (
                    "could not validate semantic-contract revalidation: "
                    f"{type(error).__name__}: {error}"
                )
        # Validate the cheap, byte-pinned replay before spawning the expensive
        # current-input fingerprint subprocess. A malformed optional replay
        # cannot authorize anything, so failing before that subprocess saves a
        # full closeout wait without changing accepted evidence.
        fingerprint_error = ""
        if not current_surface or not semantic_contract_revalidation_error:
            _increment_diagnostic(diagnostics, EVIDENCE_DIAGNOSTIC_WATCH_DIGESTS)
            watched_input_digest = _source_record_identity_process_watch_digest(
                folder, audit_payload=audit_payload
            )
            _increment_diagnostic(
                diagnostics, EVIDENCE_DIAGNOSTIC_IDENTITY_VALIDATIONS
            )
            fingerprint_error = (
                _source_record_current_input_fingerprint_error(
                    folder,
                    audit_payload,
                    verify_watch_inputs=False,
                )
                if current_surface
                else ""
            )
        identity_error = _source_record_audit_identity_error(
            audit_payload,
            expected_paper_statement_map_sha256=(
                statement_map_snapshot.sha256 or ""
            ),
            folder=folder,
            prevalidated_current_input_fingerprint_error=fingerprint_error,
            semantic_contract_revalidation=semantic_contract_revalidation,
            prevalidated_semantic_contract_revalidation_error=(
                semantic_contract_revalidation_error
            ),
        )

    corrected_findings: tuple[Finding, ...] = ()
    corrected_model_field_items: dict[str, dict[str, Any]] = {}
    source_record_identity_context: object | None = None
    if isinstance(audit_payload, dict) and not identity_error:
        # The strict gate above has already replayed the external-artifact
        # fingerprint for this exact snapshot.  Issue a nonserialized context
        # only if canonical raw/map/watch state still agrees, then pass it to
        # every nested overlay loader below instead of replaying the helper.
        canonical_raw_path = folder / "audit" / "source_record_audit.json"
        try:
            snapshot_is_canonical_raw = (
                audit_snapshot.path.resolve() == canonical_raw_path.resolve()
            )
        except (OSError, RuntimeError):
            snapshot_is_canonical_raw = False
        source_record_identity_context = _issue_current_source_record_identity_context(
            folder,
            folder.name,
            audit_payload,
            source_record_identity_error=identity_error,
            watched_input_digest=watched_input_digest or None,
            trusted_canonical_raw_file_sha256=(
                audit_snapshot.sha256 if snapshot_is_canonical_raw else None
            ),
        )
    if not identity_error:
        _increment_diagnostic(diagnostics, EVIDENCE_DIAGNOSTIC_CORRECTED_SCOPE)
        corrected_findings = tuple(
            _corrected_model_scope_contract_findings(
                folder,
                status,
                status_payload,
                audit_payload_override=audit_payload,
                prevalidated_source_record_identity_error=identity_error,
                validated_field_items_out=corrected_model_field_items,
                artifact_snapshots_override=snapshots_by_path,
            )
        )
    scope = author_approved_corrected_scope(status_payload)
    scope_role = None
    scope_role_error = ""
    if scope is not None:
        scope_role, scope_role_error = corrected_model_scope_role(scope)
    corrected_scope_current = bool(
        not identity_error
        and scope is not None
        and not scope_role_error
        and scope_role == WHOLE_PAPER_CLOSEOUT_SCOPE_ROLE
        and not corrected_findings
    )

    administrative_rebind = None
    administrative_rebind_path = None
    administrative_rebind_error = ""
    regularity_context = None
    regularity_context_error = ""
    auxiliary_routing_context = None
    auxiliary_routing_context_error = ""
    if isinstance(audit_payload, dict) and not identity_error:
        regularity_snapshot = snapshots_by_path.get(regularity_path.resolve())
        regularity_source_snapshot = snapshots_by_path.get(
            (folder / "source.txt").resolve()
        )
        regularity_context, regularity_context_error = (
            load_configured_assumption_formalization_regularity_context(
                folder,
                audit_payload,
                status_payload=status_payload,
                ledger_bytes_override=(
                    regularity_snapshot.raw_bytes
                    if regularity_snapshot is not None
                    else None
                ),
                source_artifact_sha256_override=(
                    regularity_source_snapshot.sha256
                    if regularity_source_snapshot is not None
                    else None
                ),
            )
        )
        if current_surface:
            rebind_path, _rebind_path_error = source_record_review_sidecar_path(
                folder,
                status_payload,
                config_field=(
                    "source_record_administrative_projection_rebind_file"
                ),
                default_basename=(
                    SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME
                ),
            )
            rebind_snapshot = (
                snapshots_by_path.get(rebind_path.resolve())
                if rebind_path is not None
                else None
            )
            (
                administrative_rebind,
                administrative_rebind_path,
                administrative_rebind_error,
            ) = source_record_administrative_projection_rebind_context(
                folder,
                status_payload,
                audit_path=audit_path,
                audit_payload=audit_payload,
                statement_map_path=statement_map_path,
                statement_map=statement_map_snapshot.payload,
                receipt_bytes_override=(
                    rebind_snapshot.raw_bytes
                    if rebind_snapshot is not None
                    else None
                ),
                raw_audit_bytes_override=audit_snapshot.raw_bytes,
                statement_map_bytes_override=statement_map_snapshot.raw_bytes,
            )
        if (
            str(audit_payload.get("prompt_version") or "").strip()
            == CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
            and str(audit_payload.get("paper") or "").strip() == folder.name
        ):
            (
                auxiliary_routing_context,
                auxiliary_routing_context_error,
            ) = current_auxiliary_routing_context(
                root=ROOT,
                paper_dir=folder,
                paper=folder.name,
                audit_payload=audit_payload,
                verify_current_raw_identity=False,
            )

    current_judgments: dict[str, dict[str, Any]] = {}
    if isinstance(audit_payload, dict) and not identity_error:
        _increment_diagnostic(diagnostics, EVIDENCE_DIAGNOSTIC_CURRENT_JUDGMENTS)
        current_judgments = _current_source_record_judgment_items(
            audit_payload,
            match_snapshot.payload or {},
            expected_paper_statement_map_sha256=(
                statement_map_snapshot.sha256 or ""
            ),
            folder=folder,
            prevalidated_source_record_identity_error=identity_error,
            statement_map_override=statement_map_snapshot.payload,
            status_payload_override=status_payload,
            configured_assumption_regularity_context_override=regularity_context,
            component_projection_frozen_inputs=component_projection_frozen_inputs,
            base_judgment_sidecar_path=match_path,
            source_record_identity_context=source_record_identity_context,
        )
    frozen_current_judgments = _freeze_json(
        current_judgments,
        preserve_dict_subclasses=True,
    )
    assert isinstance(frozen_current_judgments, dict)
    frozen_corrected_model_field_items = _freeze_json(
        corrected_model_field_items,
        preserve_dict_subclasses=True,
    )
    assert isinstance(frozen_corrected_model_field_items, dict)

    issuer_binding = _EvidenceRunContextIssuerBinding()
    context = EvidenceRunContext(
        folder=folder.resolve(),
        status=status,
        audit_config_snapshot=audit_config_snapshot,
        status_snapshot=status_snapshot,
        audit_snapshot=audit_snapshot,
        match_snapshot=match_snapshot,
        statement_map_snapshot=statement_map_snapshot,
        source_proof_fidelity_snapshot=ledger_snapshot,
        sidecar_snapshots=sidecar_snapshots,
        audit_path_error=audit_path_error,
        match_path_error=match_path_error,
        source_proof_fidelity_path_error=ledger_path_error,
        source_record_identity_error=identity_error,
        semantic_contract_revalidation=semantic_contract_revalidation,
        semantic_contract_revalidation_error=semantic_contract_revalidation_error,
        corrected_scope_findings=corrected_findings,
        corrected_scope_current=corrected_scope_current,
        corrected_model_field_items=MappingProxyType(
            frozen_corrected_model_field_items
        ),
        administrative_projection_rebind=administrative_rebind,
        administrative_projection_rebind_path=administrative_rebind_path,
        administrative_projection_rebind_error=administrative_rebind_error,
        configured_assumption_regularity_context=regularity_context,
        configured_assumption_regularity_context_error=(
            regularity_context_error
        ),
        current_source_record_judgments=MappingProxyType(
            frozen_current_judgments
        ),
        auxiliary_routing_context=auxiliary_routing_context,
        auxiliary_routing_context_error=auxiliary_routing_context_error,
        watched_input_digest=watched_input_digest,
        source_record_identity_context=source_record_identity_context,
        _issuer_token=issuer_binding,
    )
    issuer_binding.context = context
    return context


def evidence_run_context_mutation_findings(
    context: EvidenceRunContext,
    *,
    diagnostics: MutableMapping[str, int] | None = None,
) -> list[Finding]:
    """Fail closed if any content bound to a run context changed during use."""

    if not isinstance(context, EvidenceRunContext) or not context.issued_by_builder:
        raw_folder = getattr(context, "folder", None)
        paper = raw_folder.name if isinstance(raw_folder, Path) else "unknown"
        return [
            Finding(
                "ERROR",
                paper,
                "papers",
                "evidence transaction was not issued by the exact snapshot builder",
            )
        ]

    changed_paths: list[Path] = []
    for snapshot in context.input_snapshots:
        if _path_content_sha256(snapshot.path) != snapshot.sha256:
            changed_paths.append(snapshot.path)

    watched_changed = False
    if context.watched_input_digest:
        _increment_diagnostic(diagnostics, EVIDENCE_DIAGNOSTIC_WATCH_DIGESTS)
        current_watch_digest = (
            _source_record_identity_process_watch_digest(context.folder)
            if context.audit_payload is None
            else _source_record_identity_process_watch_digest(
                context.folder, audit_payload=context.audit_payload
            )
        )
        watched_changed = current_watch_digest != context.watched_input_digest
    if not changed_paths and not watched_changed:
        return []

    _increment_diagnostic(diagnostics, EVIDENCE_DIAGNOSTIC_INPUT_MUTATIONS)
    details: list[str] = []
    if changed_paths:
        details.append(
            "exact inputs changed: "
            + ", ".join(rel(path) for path in changed_paths[:5])
            + ("; ..." if len(changed_paths) > 5 else "")
        )
    if watched_changed:
        details.append("source-record producer/source watch digest changed")
    return [
        Finding(
            "ERROR",
            context.folder.name,
            rel(context.folder / "status.json"),
            "evidence inputs changed during the paper audit transaction; "
            "discard all run-scoped authorization results ("
            + "; ".join(details)
            + ")",
        )
    ]


def _run_evidence_integrity(
    paper_filter: str | None,
    release: bool,
    include_source_obligations: bool = False,
    *,
    public_complete: bool = False,
    require_source_bytes: bool = True,
    diagnostics: MutableMapping[str, int] | None = None,
    context: EvidenceRunContext | None = None,
    finalize_context: bool,
) -> list[Finding]:
    folders = paper_dirs(paper_filter, public_complete=public_complete)
    if context is not None and (
        not isinstance(context, EvidenceRunContext)
        or not context.issued_by_builder
    ):
        return [
            Finding(
                "ERROR",
                paper_filter or "REPO",
                "papers",
                "run-scoped evidence context was not issued by the exact "
                "evidence snapshot builder",
            )
        ]
    report_snapshot = (
        context.json_snapshot(
            ROOT / "scripts" / "refresh_validation_report_audit_summaries.py"
        )
        if context is not None
        else None
    )
    lake_snapshot = context.json_snapshot(LAKEFILE) if context is not None else None
    findings = check_report_generator(
        raw_bytes_override=(
            report_snapshot.raw_bytes if report_snapshot is not None else _UNSET
        )
    )
    defaults, libraries = lake_targets(
        raw_bytes_override=(
            lake_snapshot.raw_bytes if lake_snapshot is not None else _UNSET
        )
    )
    if paper_filter and not folders:
        return findings + [
            Finding("ERROR", paper_filter, "papers", "paper folder/status.json not found")
        ]
    if context is not None and (
        len(folders) != 1 or folders[0].resolve() != context.folder
    ):
        return findings + [
            Finding(
                "ERROR",
                paper_filter or "REPO",
                "papers",
                "run-scoped evidence context does not match the selected paper",
            )
        ]
    for folder in folders:
        selected_context = context or build_evidence_run_context(
            folder, diagnostics=diagnostics
        )
        active = active_papers_from_payload(
            selected_context.audit_config_snapshot.payload or {}
        )
        status = selected_context.status
        payload = selected_context.status_payload
        findings.extend(
            check_duplicate_sidecars(folder, status, context=selected_context)
        )
        findings.extend(
            historical_statement_manifest_replay_evidence_findings(
                folder, status, context=selected_context
            )
        )
        findings.extend(
            check_placeholder_evidence(folder, status, context=selected_context)
        )
        findings.extend(
            coverage_row_signature_pin_findings(
                folder, status, context=selected_context
            )
        )
        findings.extend(
            corrected_target_coverage_findings(
                folder, status, context=selected_context
            )
        )
        findings.extend(
            check_status_alignment(folder, status, context=selected_context)
        )
        findings.extend(selected_context.corrected_scope_findings)
        findings.extend(
            check_source_manifest(
                folder,
                status,
                require_source_bytes=require_source_bytes,
                context=selected_context,
            )
        )
        findings.extend(
            semantic_contract_inventory_findings(
                folder,
                status,
                require_source_bytes=require_source_bytes,
                context=selected_context,
            )
        )
        findings.extend(
            source_proof_fidelity_findings(
                folder,
                status,
                payload,
                require_source_bytes=require_source_bytes,
                context=selected_context,
            )
        )
        findings.extend(
            check_source_record_configured_rows(folder, context=selected_context)
        )
        findings.extend(
            check_source_premise_consistency(
                folder, status, context=selected_context
            )
        )
        findings.extend(
            check_source_record_judgments(
                folder,
                status,
                require_source_bytes=require_source_bytes,
                context=selected_context,
            )
        )
        findings.extend(
            final_closure_receipt_findings(
                folder, require_source_bytes=require_source_bytes
            )
        )
        findings.extend(
            source_record_semantic_target_disposition_findings(
                folder, status, context=selected_context
            )
        )
        findings.extend(
            source_record_input_target_disposition_findings(
                folder, status, context=selected_context
            )
        )
        findings.extend(
            source_record_recursive_field_target_disposition_findings(
                folder, status, context=selected_context
            )
        )
        findings.extend(
            explicit_source_route_semantic_model_findings(
                folder,
                status,
                payload,
                require_source_bytes=require_source_bytes,
                context=selected_context,
            )
        )
        findings.extend(
            check_plain_formalized_unresolved_source_record_math(
                folder, status, context=selected_context
            )
        )
        findings.extend(
            check_full_closeout_open_semantic_model_dimensions(
                folder, status, context=selected_context
            )
        )
        if include_source_obligations:
            findings.extend(
                check_current_unresolved_source_record_math(
                    folder, status, context=selected_context
                )
            )
        findings.extend(
            check_validator_independence(
                folder, status, release, context=selected_context
            )
        )
        review_log_snapshot = selected_context.json_snapshot(
            folder / ".review_traces" / "paper_theorem_validations.jsonl"
        )
        assumptions_snapshot = selected_context.json_snapshot(
            folder / "Assumptions.lean"
        )
        findings.extend(
            check_human_review(
                folder,
                status,
                payload,
                release,
                review_log_present=(
                    review_log_snapshot.sha256 is not None
                    if review_log_snapshot is not None
                    else None
                ),
            )
        )
        findings.extend(
            check_vacuous_assumptions(
                folder,
                status,
                source_bytes_override=(
                    assumptions_snapshot.raw_bytes
                    if assumptions_snapshot is not None
                    else _UNSET
                ),
            )
        )
        findings.extend(check_active_status(folder, status, active))
        findings.extend(check_build_coverage(folder, status, payload, defaults, libraries))
        if finalize_context:
            findings.extend(
                evidence_run_context_mutation_findings(
                    selected_context, diagnostics=diagnostics
                )
            )
    return unique_findings(findings)


def run(
    paper_filter: str | None,
    release: bool,
    include_source_obligations: bool = False,
    *,
    public_complete: bool = False,
    require_source_bytes: bool = True,
    diagnostics: MutableMapping[str, int] | None = None,
    context: EvidenceRunContext | None = None,
) -> list[Finding]:
    """Run evidence validation and always finalize its transaction."""

    return _run_evidence_integrity(
        paper_filter,
        release,
        include_source_obligations,
        public_complete=public_complete,
        require_source_bytes=require_source_bytes,
        diagnostics=diagnostics,
        context=context,
        finalize_context=True,
    )


def run_for_consolidated_closeout_transaction(
    paper_filter: str,
    release: bool,
    include_source_obligations: bool = False,
    *,
    require_source_bytes: bool = True,
    diagnostics: MutableMapping[str, int] | None = None,
    context: EvidenceRunContext,
) -> list[Finding]:
    """Run inside a closeout whose owner will perform the final mutation check.

    This deliberately separate API prevents an ordinary caller from disabling
    finalization with a Boolean option and mistaking an unfinalized list for a
    complete audit result. ``audit_repository`` owns the only production use
    and finalizes the same context after every repository-level consumer.
    """

    return _run_evidence_integrity(
        paper_filter,
        release,
        include_source_obligations,
        public_complete=False,
        require_source_bytes=require_source_bytes,
        diagnostics=diagnostics,
        context=context,
        finalize_context=False,
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--paper", help="restrict the audit to one paper folder")
    selection.add_argument(
        "--public-complete",
        action="store_true",
        help=(
            "audit only papers explicitly marked repository_visibility=public "
            "whose mathematical status is formalized or formalized with caveat; "
            "fail if any paper omits repository visibility"
        ),
    )
    parser.add_argument(
        "--release",
        action="store_true",
        help="treat missing independent validator attestations as blocking release errors",
    )
    parser.add_argument(
        "--include-source-obligations",
        action="store_true",
        help=(
            "include non-blocking WARN findings for current source-record items "
            "classified as unresolved_assumed_math"
        ),
    )
    parser.add_argument(
        "--allow-missing-source-bytes",
        action="store_true",
        help=(
            "structural public-checkout mode: require a safe canonical path and "
            "SHA-256 but warn, rather than certify, when licensed source bytes are absent"
        ),
    )
    parser.add_argument("--json", action="store_true", help="emit findings as JSON")
    args = parser.parse_args()

    try:
        selected = paper_dirs(args.paper, public_complete=args.public_complete)
    except ValueError as exc:
        parser.error(str(exc))
    if args.public_complete and not selected:
        parser.error("no explicitly public fully formalized papers found")
    findings = run(
        args.paper,
        args.release,
        args.include_source_obligations,
        public_complete=args.public_complete,
        require_source_bytes=not args.allow_missing_source_bytes,
    )
    if args.json:
        print(json.dumps([asdict(finding) for finding in findings], indent=2, sort_keys=True))
    else:
        for finding in findings:
            print(finding.format())
        errors = sum(finding.severity == "ERROR" for finding in findings)
        warnings = sum(finding.severity == "WARN" for finding in findings)
        print(f"Evidence-integrity audit: {errors} error(s), {warnings} warning(s)")
    return 1 if any(finding.severity == "ERROR" for finding in findings) else 0


if __name__ == "__main__":
    sys.exit(main())
