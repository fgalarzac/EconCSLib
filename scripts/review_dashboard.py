#!/usr/bin/env python3
"""Generate and persist theorem-review metadata from paper interfaces.

This helper creates a local review page for one paper or all papers.  The page
shows side-by-side the paper-facing claim text (when available) and the Lean
statement from the paper's curated review surface, and lets a reviewer record a
checkbox + note pair per theorem.  Each submission is appended to a local JSONL
trace with the reviewer handle and UTC timestamp.
"""

from __future__ import annotations

import argparse
import mimetypes
import hashlib
import csv
import html
import io
import getpass
import os
import json
import re
import signal
import sys
import subprocess
import urllib.parse
import tempfile
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field as dataclass_field
from datetime import datetime, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from threading import Lock
from types import MappingProxyType
from xml.etree import ElementTree
from typing import Any, Callable, Iterable, Iterator, Mapping

try:
    from scripts.lean_signature_manifest import (
        RepositoryBuildInputSnapshotProvider,
        repository_build_input_snapshot,
        paper_owned_module_names_in_import_closure,
        run_lean_semantic_contract_matches,
        run_lean_semantic_contract_transparency_checks,
        run_lean_signature_manifests,
        signature_manifest_cache_context,
        signature_manifest_cache_context_sha256,
        signature_manifest_digest,
    )
    from scripts.authenticated_manifest_store import (
        configured_review_row_proposition_graph_sha256,
        current_source_bound_manifest_bindings,
        elaborated_proposition_graph_sha256,
        merge_authenticated_manifest_store,
        prime_attested_resume_manifests_with_current_revalidation,
        prime_exact_context_attested_resume_manifests,
        prime_authenticated_manifest_store,
        prime_authenticated_manifest_store_with_item_revalidation,
    )
    from scripts.source_artifact_companion import source_text_companion_validation_issues
    from scripts.source_archive_surface import source_archive_surface_validation_issues
    from scripts.source_coverage_scope import (
        DEEP_PAPER_WITH_ALL_PROSE_CLAIMS,
        SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
        deep_source_coverage_attestation_error,
        filter_source_inventory_for_coverage,
        source_index_byte_pinned_anchor_item_ids,
        source_item_has_explicit_nonordinary_obligation,
        source_named_result_environment_kinds_from_map,
        source_coverage_mode_from_map,
        source_coverage_mode_migration_error,
        source_coverage_modes_compatible,
        source_item_scope_classification_errors,
        source_item_coverage_sha256,
        source_item_effective_route_policy,
        source_map_structural_errors,
        source_presentation_aliases,
        source_prose_definition_inventory_errors,
    )
except ModuleNotFoundError:  # Direct `python scripts/review_dashboard.py` execution.
    from lean_signature_manifest import (
        RepositoryBuildInputSnapshotProvider,
        repository_build_input_snapshot,
        paper_owned_module_names_in_import_closure,
        run_lean_semantic_contract_matches,
        run_lean_semantic_contract_transparency_checks,
        run_lean_signature_manifests,
        signature_manifest_cache_context,
        signature_manifest_cache_context_sha256,
        signature_manifest_digest,
    )
    from authenticated_manifest_store import (
        configured_review_row_proposition_graph_sha256,
        current_source_bound_manifest_bindings,
        elaborated_proposition_graph_sha256,
        merge_authenticated_manifest_store,
        prime_attested_resume_manifests_with_current_revalidation,
        prime_exact_context_attested_resume_manifests,
        prime_authenticated_manifest_store,
        prime_authenticated_manifest_store_with_item_revalidation,
    )
    from source_artifact_companion import source_text_companion_validation_issues
    from source_archive_surface import source_archive_surface_validation_issues
    from source_coverage_scope import (
        DEEP_PAPER_WITH_ALL_PROSE_CLAIMS,
        SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
        deep_source_coverage_attestation_error,
        filter_source_inventory_for_coverage,
        source_index_byte_pinned_anchor_item_ids,
        source_item_has_explicit_nonordinary_obligation,
        source_named_result_environment_kinds_from_map,
        source_coverage_mode_from_map,
        source_coverage_mode_migration_error,
        source_coverage_modes_compatible,
        source_item_scope_classification_errors,
        source_item_coverage_sha256,
        source_item_effective_route_policy,
        source_map_structural_errors,
        source_presentation_aliases,
        source_prose_definition_inventory_errors,
    )


ROOT = Path(
    os.environ.get("ECONCSLIB_REPO_ROOT", Path(__file__).resolve().parents[1])
).resolve()
PAPERS_DIR = ROOT / "papers"
AUDIT_CONFIG = PAPERS_DIR / "audit_config.json"
DEFAULT_PAPER_LOG_FILE = "paper_theorem_validations.jsonl"
DEFAULT_PAPER_INTERFACE_CACHE_FILE = "paper_interface_cache.json"
MANIFEST_RESUME_CACHE_DIRNAME = "lean_signature_manifest_resume"
MANIFEST_RESUME_CACHE_SCHEMA = 2
# These records are deliberately ignored local performance data. They are not
# review evidence and never satisfy a paper audit. They are retained across
# publications because deleting them can race an independently interrupted
# refresh; exact context/source binding plus fresh Lean revalidation makes
# stale records harmless cache misses.
MANIFEST_RESUME_CACHE_NON_AUTHORITATIVE = True
DEFAULT_PAPER_STATUS_FILE = "status.json"
PAPER_DOCS_DIR = "docs"
PAPER_AUDIT_DIR = "audit"
FINAL_VALIDATION_REPORT_FILE = "FINAL_VALIDATION_REPORT.md"
DEFAULT_LLM_LEAN_TO_TEX_FILE = f"{PAPER_AUDIT_DIR}/lean_to_tex_llm.json"
DEFAULT_LLM_STATEMENT_JUDGE_FILE = f"{PAPER_AUDIT_DIR}/statement_match_llm.json"
DEFAULT_LLM_REVIEW_SURFACE_FILE = f"{PAPER_AUDIT_DIR}/review_surface_llm.json"
DEFAULT_LLM_PAPER_COVERAGE_FILE = f"{PAPER_AUDIT_DIR}/paper_coverage_llm.json"
DEFAULT_LLM_DEFECT_SUPPORT_FILE = f"{PAPER_AUDIT_DIR}/defect_support_match_llm.json"
DEFAULT_LLM_ASSUMPTION_JUDGE_FILE = f"{PAPER_AUDIT_DIR}/assumption_match_llm.json"
DEFAULT_ASSUMPTION_SOURCE_FILE = "Assumptions.lean"
REQUIRED_LLM_LEAN_TO_TEX_PROMPT_VERSION = "lean-to-tex-v3-strict-context-free-semantic-inputs"
REQUIRED_LLM_STATEMENT_PROMPT_VERSION = (
    "statement-match-v10-semantic-fidelity-seat-stopping"
)
# Prompt labels identify the producer instructions, while these contracts
# identify the semantic obligations that make an existing row reusable.  A
# wording-only prompt or validator update may be added to the code-owned maps
# below only after reviewing that it preserves the same contract.  Sidecars
# never get to assert their own compatibility.
REQUIRED_LLM_LEAN_TO_TEX_SEMANTIC_CONTRACT_VERSION = (
    "lean-to-tex-semantic-inputs-v3"
)
REQUIRED_LLM_STATEMENT_SEMANTIC_CONTRACT_VERSION = (
    "statement-match-semantic-fidelity-v10"
)
LLM_LEAN_TO_TEX_PROMPT_SEMANTIC_CONTRACTS: dict[str, str] = {
    REQUIRED_LLM_LEAN_TO_TEX_PROMPT_VERSION: (
        REQUIRED_LLM_LEAN_TO_TEX_SEMANTIC_CONTRACT_VERSION
    ),
}
LLM_STATEMENT_PROMPT_SEMANTIC_CONTRACTS: dict[str, str] = {
    REQUIRED_LLM_STATEMENT_PROMPT_VERSION: (
        REQUIRED_LLM_STATEMENT_SEMANTIC_CONTRACT_VERSION
    ),
}
REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION = (
    "paper-coverage-v5-semantic-proof-row-signature-pins"
)
LEGACY_LLM_PAPER_COVERAGE_PROMPT_VERSION = (
    "paper-coverage-v3-semantic-proof-declaration-and-defect-support"
)
REQUIRED_LLM_DEFECT_SUPPORT_PROMPT_VERSION = (
    "defect-support-v1-exact-source-defect-to-lean-semantic"
)
REQUIRED_LLM_REVIEW_SURFACE_PROMPT_VERSION = "review-surface-v2-semantic-paper-facing"
REQUIRED_LLM_ASSUMPTION_PROMPT_VERSION = "assumption-provenance-v3-semantic-exact-premise-source"
PAPER_STATEMENT_MAP_FILE = f"{PAPER_AUDIT_DIR}/paper_statement_map.json"
# This is an explicit human-scope disposition for a source-visible claim.  It
# is deliberately not a source classification: the claim remains visible in
# the inventory and must carry byte-pinned source evidence.
USER_APPROVED_SCOPE_EXCLUSION = "user_approved_scope_exclusion"
USER_APPROVED_SCOPE_EXCLUSION_SCHEMA = 1
USER_APPROVED_SCOPE_EXCLUSION_APPROVAL_KIND = "explicit_user_instruction"
# A mechanically generated sidecar can record its frozen inputs without being
# evidence.  Readers must reject this marker until an independent reviewer
# deletes it after supplying the actual translation or semantic judgment.
NON_EVIDENCE_SCAFFOLD_SCHEMA = 1
NON_EVIDENCE_SCAFFOLD_STATUS = "needs_review"
SOURCE_ROUTE_KINDS = {
    "direct",
    "approved_corrected_target",
    "source_component",
    "source_model_convention",
    "defect_or_remark_support",
    "proof_support",
}
CORRECTED_SOURCE_STATEMENT_STATUS = "corrected_source_statement"
CORRECTED_TARGET_SCHEMA = 1
CORRECTED_TARGET_COVERAGE = "covered_corrected_target"
CORRECTED_TARGET_ROUTE_KIND = "approved_corrected_target"
CORRECTED_TARGET_MATCH_RESOLUTION = "approved_corrected_target"
CORRECTED_TARGET_ROUTE_RELATION = "proves_approved_corrected_target"
SOURCE_MODEL_ROUTE_RELATIONS = {
    "equivalent_model_convention",
    "shared_model_convention",
    "source_implies_lean_model",
    "lean_implies_source_model",
}
SOURCE_COMPONENT_ROUTE_RELATIONS = {
    "lean_implies_source_component",
    "equivalent_source_component",
}
SOURCE_DEFINITION_PARTITION_FIELD = "source_definition_partition"
SOURCE_DEFINITION_PARTITION_SCHEMA = 1
SOURCE_DEFINITION_PARTITION_RELATION = (
    "jointly_equivalent_to_source_definition"
)
SOURCE_DEFINITION_COMPONENT_EXACT_STATUS = "exact"
SOURCE_DEFINITION_COMPONENT_CONVENTION_STATUSES = frozenset(
    {
        "documented_model_convention",
        "documented_source_domain_convention",
        "documented_source_model_convention",
        "source_model_convention",
    }
)
SOURCE_DEFINITION_COMPONENT_RELATION = "equivalent_source_component"
SOURCE_COMPONENT_DISPLAY_BINDING_SCHEMA = 2
SOURCE_DEFECT_ROUTE_RELATIONS = {
    "counterexample_to_source_defect",
    "refutes_source_defect",
    "explains_support_only_remark",
}
REVIEW_SURFACE_LLM_AUDIT_THRESHOLD = 30
REVIEW_SURFACE_WARN_THRESHOLD = 120
PAPER_INTERFACE_CACHE_SCHEMA = 20
SEMANTIC_BRIDGE_DECLARATION_FIELDS = (
    "semantic_bridge_declarations",
    "paper_equivalence_declarations",
    "source_equivalence_declarations",
    "library_bridge_declarations",
)
EXACT_SOURCE_LOCATOR_RE = re.compile(
    r"(?:"
    r"\b(?:page|p\.?)\s*\d+|"
    r"\bappendix\s+[A-Z0-9]+|"
    r"\b(?:section|theorem|lemma|proposition|corollary|definition|equation|"
    r"remark|claim|line)s?\s+(?:[A-Z]?\d[\w.()/-]*|[A-Z](?:\.\d+)*)|"
    r"§\s*[A-Z0-9]+|"
    r"\b[\w./-]+\.(?:tex|txt|md|pdf):\d+"
    r")",
    re.I,
)
NAME_ONLY_SOURCE_COVERAGE_REASON_RE = re.compile(
    r"exactly matches current dashboard row name|"
    r"exact source-key|"
    r"\bname[-_ ]?match(?:ed|es|ing)?\b|"
    r"\bmatched by name\b",
    re.I,
)
NAME_ONLY_SEMANTIC_EVIDENCE_RE = re.compile(
    r"\b(?:names? match|matched by name|same (?:theorem|lemma|definition|function|"
    r"field|predicate|wrapper) name|same identifier|identifiers? (?:match|coincide)|"
    r"same symbol|matching labels?|same label|phrase overlap|same wording)\b",
    re.I,
)
PROFILE_QUANTIFICATION_SCOPES = {
    "not_profile_based",
    "fixed_profile",
    "all_profiles",
    "existential_profile",
    "mixed_profile_scope",
}
QUANTIFICATION_RELATIONS = {
    "equivalent",
    "source_stronger",
    "lean_stronger",
    "incomparable",
}
SOURCE_ALGORITHM_CLAIM_LEVELS = {
    "not_algorithmic",
    "existence",
    "executable",
    "polynomial_time",
}
LEAN_ALGORITHM_CLAIM_LEVELS = SOURCE_ALGORITHM_CLAIM_LEVELS | {
    "noncomputable_existence"
}
RUNNER_PROVENANCE_KINDS = {
    "not_applicable",
    "same_formalized_runner",
    "proved_refinement",
    "independent_characterization",
    "missing",
}
RESULT_PROVENANCE_KINDS = {
    "not_applicable",
    "runner_derived",
    "preservation_bridge",
    "independent_characterization",
    "missing",
}
LEGACY_FIDELITY_RISK_REVIEW_VERSION = (
    "fidelity-risk-review-v2-shape-action-witness-count-execution"
)
FIDELITY_RISK_REVIEW_VERSION = (
    "fidelity-risk-review-v3-shape-action-witness-count-generic-execution"
)
SUPPORTED_FIDELITY_RISK_REVIEW_VERSIONS = {
    LEGACY_FIDELITY_RISK_REVIEW_VERSION,
    FIDELITY_RISK_REVIEW_VERSION,
}
LEGACY_FIDELITY_EXECUTION_SCOPE_FIELDS = (
    ("source_quota_turnout_scope", "source quota/turnout scope"),
    ("lean_quota_turnout_scope", "Lean quota/turnout scope"),
    ("source_seat_termination_scope", "source seat-count/stopping scope"),
    ("lean_seat_termination_scope", "Lean seat-count/stopping scope"),
    ("source_round_scope", "source round/executor scope"),
    ("lean_round_scope", "Lean round/executor scope"),
    ("source_arithmetic_domain", "source arithmetic domain"),
    ("lean_arithmetic_domain", "Lean arithmetic domain"),
    ("source_cost_claim_scope", "source cost/complexity scope"),
    ("lean_cost_claim_scope", "Lean cost/complexity scope"),
    ("global_claim_bridge_basis", "global-claim bridge basis"),
)
FIDELITY_EXECUTION_SCOPE_FIELDS = (
    ("source_input_scope", "source input scope"),
    ("lean_input_scope", "Lean input scope"),
    ("source_state_transition_scope", "source state-transition scope"),
    ("lean_state_transition_scope", "Lean state-transition scope"),
    ("source_termination_scope", "source termination scope"),
    ("lean_termination_scope", "Lean termination scope"),
    ("source_numeric_representation", "source numeric representation"),
    ("lean_numeric_representation", "Lean numeric representation"),
    ("source_cost_scope", "source cost/complexity scope"),
    ("lean_cost_scope", "Lean cost/complexity scope"),
    ("global_claim_bridge_basis", "global-claim bridge basis"),
)
FIDELITY_RISK_DIMENSIONS = {
    "output_shape",
    "adversarial_action_space",
    "coherent_extrema_witness",
    "cardinality_fibers",
    "execution_claim_scope",
}
FIDELITY_RISK_RELATIONS = {
    "equivalent",
    "source_stronger",
    "lean_stronger",
    "incomparable",
    "uncertain",
}
COHERENT_EXTREMA_WITNESS_STATUSES = {
    "not_required",
    "same_coherent_witness",
    "proved_jointly_realizable",
    "separate_witnesses_only",
    "missing",
}
COUNTING_SEMANTICS = {
    "syntactic_family_cardinality",
    "nonempty_realized_fibers",
    "other",
}
SURJECTIVITY_STATUSES = {
    "not_required",
    "definitionally_surjective",
    "proved_surjective",
    "missing",
}
SEMANTIC_WORLD_ROLES = {"source", "lean", "shared"}
SEMANTIC_WORLD_BRIDGE_RELATIONS = {
    "definitionally_equal",
    "equivalent",
    "refines",
    "simulates",
    "preserves_result",
}
OPERATIONAL_COMPLEXITY_REVIEW_VERSION = (
    "operational-complexity-review-v1-transitive-work-accounting"
)
OPERATIONAL_WORK_CATEGORIES = {
    "traversal_enumeration_length",
    "duplicate_multiplicity",
    "materialization_rebuilding",
    "representation_container_primitives",
    "exact_rational_bit_growth",
}
OPERATIONAL_WORK_STATUSES = {
    "charged",
    "proved_absent",
    "not_applicable",
    "missing",
    "excluded_by_claim",
}
FULL_RUNTIME_MATCH_WORK_STATUSES = {
    "charged",
    "proved_absent",
    "not_applicable",
}
CLOSURE_ELIMINATION_EVIDENCE_KINDS = {
    "generated_ir_call_graph",
    "cost_threaded_executor",
}
NAMED_DEFINITION_CLASSIFICATIONS = {
    "substantive",
    "self_characterizing",
    "routing_only",
}
NUMERIC_SEMANTIC_RELATIONS = {
    "definitionally_equal",
    "proved_equivalent",
    "witness_specific_equivalent",
    "different",
    "uncertain",
}
DISCRETE_SEMANTIC_RELATIONS = NUMERIC_SEMANTIC_RELATIONS
NUMERIC_SEMANTIC_CONSTANTS = {
    "Add.add",
    "Div.div",
    "HAdd.hAdd",
    "HDiv.hDiv",
    "HMul.hMul",
    "HSub.hSub",
    "LE.le",
    "LT.lt",
    "Mul.mul",
    "Nat.div",
    "OfNat.ofNat",
    "Sub.sub",
}
DISCRETE_SEMANTIC_CONSTANT_PREFIXES = (
    "List.contains",
    "List.drop",
    "List.erase",
    "List.filter",
    "List.find",
    "List.get",
    "List.head",
    "List.idxOf",
    "List.lookup",
    "List.mem",
    "List.tail",
)
REVIEW_SURFACE_SCHEMA = 1
REVIEW_SOURCE_FILENAME = "PaperInterface.lean"
REVIEW_DECL_KINDS = {
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "axiom",
    "structure",
    "class",
    "inductive",
}


def llm_prompt_version_is_semantically_current(
    prompt_version: str,
    *,
    prompt_contracts: Mapping[str, str],
    required_contract: str,
) -> bool:
    """Check a code-owned prompt compatibility mapping.

    A sidecar can report only the prompt version that produced a row. The
    dashboard decides whether that prompt preserves today's semantic contract;
    arbitrary sidecar metadata cannot turn an older or weaker prompt into
    compatible evidence.
    """

    return prompt_contracts.get(str(prompt_version or "").strip()) == required_contract


def active_paper_names() -> set[str]:
    """Return paper folders skipped by whole-repository dashboard checks."""

    if not AUDIT_CONFIG.exists():
        return set()
    try:
        payload = json.loads(AUDIT_CONFIG.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return set()
    raw = payload.get("active_papers", []) if isinstance(payload, dict) else []
    if not isinstance(raw, list):
        return set()
    return {str(item).strip() for item in raw if str(item).strip()}


def paper_relative_file(folder: Path, preferred: str, legacy: str | None = None) -> Path:
    """Return the organized paper-local path, falling back to a legacy root file."""

    preferred_path = folder / preferred
    inputs = _dashboard_audit_inputs()
    if inputs is not None:
        if not inputs.has_snapshot(preferred_path):
            raise DashboardFrozenInputError(
                f"missing frozen dashboard input: {inputs._key(preferred_path)}"
            )
        if inputs.is_file(preferred_path) or legacy is None:
            return preferred_path
        if legacy is not None:
            legacy_path = folder / legacy
            if inputs.has_snapshot(legacy_path):
                return legacy_path
            raise DashboardFrozenInputError(
                "missing frozen dashboard fallback input: "
                f"{inputs._key(legacy_path)}"
            )
        return preferred_path
    if preferred_path.exists() or legacy is None:
        return preferred_path
    legacy_path = folder / legacy
    if legacy_path.exists():
        return legacy_path
    return preferred_path


def is_non_evidence_scaffold_payload(payload: Any) -> bool:
    """Return whether a sidecar is intentionally blank pending real review.

    The marker is deliberately narrow and machine-readable.  It is not a
    semantic judgment, so every loader treats it as incomplete even if someone
    later adds otherwise plausible-looking fields without clearing the marker.
    """

    if not isinstance(payload, dict):
        return False
    marker = payload.get("non_evidence_scaffold")
    return (
        isinstance(marker, dict)
        and marker.get("schema") == NON_EVIDENCE_SCAFFOLD_SCHEMA
        and str(marker.get("status") or "").strip().lower()
        == NON_EVIDENCE_SCAFFOLD_STATUS
    )


ASSUMPTION_DECL_NAME_RE = re.compile(
    r"^(?:paper_)?assumption(?:_|$)|^source_assumption(?:_|$)|_assumption(?:_|$)"
)
APPROVED_ASSUMPTION_JUDGMENTS = {
    "paper_assumption",
    "paper_condition",
    "documented_additional_assumption",
    "documented_caveat",
    "partial_boundary",
}
# `conditional_boundary` is the historical sidecar token. The user-facing
# term is deliberately narrower: the source conclusion is exact and every
# additional Lean input is explicit and audited.
VISIBLE_PREMISE_BOUNDARY_LABEL = "visible-premise boundary"
CONDITIONAL_BOUNDARY_RESOLUTION = "conditional_boundary"
CONDITIONAL_BOUNDARY_RESOLUTION_ALIASES = {
    "conditional_boundary",
    "visible_premise_boundary",
    "visible-premise-boundary",
    "visible premise boundary",
    "accepted_boundary",
    "known_boundary",
    "external_library_boundary",
    "known_dependence_on_external_library",
    "known_external_library_dependence",
    "intentional_mismatch",
}
APPROVED_ASSUMPTION_PREMISE_JUDGMENTS = {
    "paper_assumption",
    "paper_condition",
    "source_text",
    "source_text_model_primitive",
    "derived_from_source_primitives",
    "documented_additional_assumption",
    "documented_caveat",
    "partial_boundary",
    "human_verified_source_implicit",
}
APPROVED_PAPER_COVERAGE_JUDGMENTS = {
    "covered",
    "covered_by_rows",
    CORRECTED_TARGET_COVERAGE,
    "covered_by_support",
    "support_only",
    "covered_with_boundary",
    "conditional_boundary",
    "visible_premise_boundary",
    "out_of_scope",
    "not_a_paper_target",
    "not_a_theorem_statement",
    USER_APPROVED_SCOPE_EXCLUSION,
}
APPROVED_PAPER_COVERAGE_AUDIT_KINDS = {
    "source_to_dashboard_llm",
    "source_to_dashboard_agent",
}
APPROVED_DEFECT_SUPPORT_AUDIT_KINDS = {
    "source_defect_to_lean_llm",
    "source_defect_to_lean_agent",
}
APPROVED_DEFECT_SUPPORT_JUDGMENTS = {
    "valid_counterexample",
    "valid_refutation",
}
DEFECT_SUPPORT_JUDGMENT_RELATIONS = {
    "valid_counterexample": "counterexample_to",
    "valid_refutation": "refutes",
}
PAPER_COVERAGE_SCAFFOLD_KINDS = {
    "all_uncertain_bootstrap",
    "exact_key_scaffold",
    "dashboard_seeded_preliminary",
    "seeded_exact_key",
}
SOURCE_TEXT_ASSUMPTION_PREMISE_JUDGMENTS = {
    "paper_assumption",
    "paper_condition",
    "source_text",
    "source_text_model_primitive",
    "human_verified_source_implicit",
}


DECL_RE = re.compile(
    r"^(?P<indent>\s*)(?:(?:@[A-Za-z_][A-Za-z0-9_]*(?:\([^)]*\))?\s+)*)?"
    r"(?:(?:noncomputable|private|protected)\s+)*"
    r"(?P<kind>theorem|lemma|def|abbrev|axiom|structure|class|inductive)\s+"
    r"(?P<name>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\b"
)
EXPORT_OPEN_RE = re.compile(
    r"^\s*export\s+(?P<source>[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s+\((?P<rest>.*)$"
)
EXPORT_NAME_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_']*\b")
COMMENT_START_RE = re.compile(r"^\s*/-[!]?")
NAMESPACE_OPEN_RE = re.compile(
    r"^\s*namespace\s+([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s*$"
)
SECTION_OPEN_RE = re.compile(r"^\s*section(?:\s+[A-Za-z_][A-Za-z0-9_']*)?\s*$")
END_SCOPE_RE = re.compile(r"^\s*end\b(?:\s+([A-Za-z_][A-Za-z0-9_']*)\s*)?$")
REPORT_CLAUSE_RE = re.compile(
    r"^\s*-\s*`(?:[A-Za-z0-9_]+\.)?(?P<name>[A-Za-z_][A-Za-z0-9_']+)`\s*:\s*(?P<text>.*)"
)
THEOREM_ENV_OPEN_RE = re.compile(r"^\s*\\begin\{(theorem|lemma|proposition|corollary|claim|definition|remark)\}")
THEOREM_ENV_CLOSE_RE = re.compile(r"^\s*\\end\{(theorem|lemma|proposition|corollary|claim|definition|remark)\}")
THEOREM_LABEL_RE = re.compile(r"\\label\{([^}]+)\}")
PAPER_TEXT_STATEMENT_LABEL_RE = re.compile(
    r"^\s*\f?\s*(?P<kind>Definition|Theorem|Lemma|Proposition|Corollary|Claim|Remark)\s+"
    r"(?P<number>[A-Za-z]?\d+(?:\.\d+)?)(?:\s*\((?P<title>[^)]*)\))?\."
)
PAPER_TEXT_STATEMENT_STOP_RE = re.compile(
    r"^\s*(?:Proof\.|Proof\s|The proof\b|To prove\b|The result follows\b|"
    r"The theorem establishes\b|The result establishes\b|Each de|"
    r"Of course\b|Note that\b|Discussion\b|What does\b|Then, we have the following\b)"
)
PAPER_TEX_PRIORITY: list[str] = [
    "{name}.tex",
    "paper.tex",
    "source.tex",
]
AGENT_PREVIEW_TOKEN_RE = re.compile(
    r"^[ \t]*(?:(?:noncomputable|private|protected)\s+)*"
    r"(?:theorem|lemma|def|abbrev)\s+[A-Za-z_][A-Za-z0-9_']*\s*",
    re.MULTILINE,
)
LEAN_TO_TEX_TOKENS: list[tuple[str, str]] = [
    ("→", r"\to"),
    ("↔", r"\iff"),
    ("⇒", r"\Rightarrow"),
    ("⇐", r"\Leftarrow"),
    ("∧", r"\land"),
    ("∨", r"\lor"),
    ("¬", r"\lnot"),
    ("∑", r"\sum"),
    ("∏", r"\prod"),
    ("∫", r"\int"),
    ("∃", r"\exists"),
    ("∀", r"\forall"),
    ("≤", r"\le"),
    ("≥", r"\ge"),
    ("≠", r"\ne"),
    ("≃", r"\simeq"),
    ("≈", r"\approx"),
    ("α", r"\alpha"),
    ("β", r"\beta"),
    ("γ", r"\gamma"),
    ("δ", r"\delta"),
    ("ε", r"\epsilon"),
    ("ι", r"\iota"),
    ("κ", r"\kappa"),
    ("λ", r"\lambda"),
    ("μ", r"\mu"),
    ("ν", r"\nu"),
    ("π", r"\pi"),
    ("σ", r"\sigma"),
    ("τ", r"\tau"),
    ("φ", r"\phi"),
    ("χ", r"\chi"),
    ("ψ", r"\psi"),
    ("ω", r"\omega"),
    ("Γ", r"\Gamma"),
    ("Δ", r"\Delta"),
    ("Π", r"\Pi"),
    ("Σ", r"\Sigma"),
    ("Λ", r"\Lambda"),
    ("Φ", r"\Phi"),
    ("Ψ", r"\Psi"),
    ("Ω", r"\Omega"),
    ("∈", r"\in"),
    ("⊆", r"\subseteq"),
    ("∅", r"\varnothing"),
    ("↦", r"\mapsto"),
]
AGENT_PREVIEW_MAX_LEN = 1800
AGENT_PREVIEW_CHECK_TIMEOUT = 20
PAPER_ASSET_EXTENSIONS = {".pdf", ".txt"}
PAPER_RENDERED_IMAGE_EXTENSIONS = {".png"}
PAPER_RENDERED_STATEMENT_DIR = "paper_statement_images"
PAPER_PDF_PRIORITY: list[str] = [
    "{name}.pdf",
    "source.pdf",
    "paper.pdf",
    "arxiv.pdf",
]
PAPER_TXT_PRIORITY: list[str] = [
    "source.txt",
    "paper.txt",
    "{name}.txt",
]
DEFAULT_USER_ENV_VARS = [
    "GITHUB_ACTOR",
    "GITHUB_USER",
    "GITHUB_USERNAME",
    "GITHUB_REPOSITORY_OWNER",
]
OS_USER_ENV_VARS = [
    "USER",
    "USERNAME",
]
AGENT_PREVIEW_CACHE: dict[str, dict[str, str]] = {}
SIGNATURE_MANIFEST_CACHE: dict[str, dict[str, dict[str, Any]]] = {}


class DashboardFrozenInputError(RuntimeError):
    """A strict dashboard read was not present in its immutable input bundle."""


def _immutable_json_mutation(*_args: object, **_kwargs: object) -> None:
    raise TypeError("frozen dashboard JSON cannot be mutated")


class _FrozenJsonDict(dict[str, Any]):
    """A ``dict``-compatible recursively immutable JSON object."""

    __setitem__ = _immutable_json_mutation
    __delitem__ = _immutable_json_mutation
    clear = _immutable_json_mutation
    pop = _immutable_json_mutation
    popitem = _immutable_json_mutation
    setdefault = _immutable_json_mutation
    update = _immutable_json_mutation
    __ior__ = _immutable_json_mutation


class _FrozenJsonList(list[Any]):
    """A ``list``-compatible recursively immutable JSON array."""

    __setitem__ = _immutable_json_mutation
    __delitem__ = _immutable_json_mutation
    append = _immutable_json_mutation
    clear = _immutable_json_mutation
    extend = _immutable_json_mutation
    insert = _immutable_json_mutation
    pop = _immutable_json_mutation
    remove = _immutable_json_mutation
    reverse = _immutable_json_mutation
    sort = _immutable_json_mutation
    __iadd__ = _immutable_json_mutation
    __imul__ = _immutable_json_mutation


def _freeze_dashboard_json(value: Any) -> Any:
    """Freeze parsed JSON while preserving ``dict``/``list`` compatibility."""

    if isinstance(value, dict):
        frozen = _FrozenJsonDict()
        for key, item in value.items():
            dict.__setitem__(frozen, key, _freeze_dashboard_json(item))
        return frozen
    if isinstance(value, list):
        frozen_list = _FrozenJsonList()
        list.extend(frozen_list, (_freeze_dashboard_json(item) for item in value))
        return frozen_list
    return value


@dataclass(frozen=True)
class DashboardAuditInputs:
    """Exact file bytes used by one strict dashboard extraction.

    ``file_snapshots`` is the complete authority for dashboard-facing file
    reads while this bundle is active. Values are immutable bytes; ``None``
    explicitly records that a path was absent when the transaction started.
    A path omitted from the mapping is not treated as absent: a direct read of
    it fails closed. This distinction prevents a closeout from silently mixing
    frozen status/sidecar inputs with later live repository contents.

    Paths may be absolute or relative to ``repository_root``. Each JSON object
    is parsed at most once and retained as a recursively immutable, ordinary
    ``dict``/``list``-compatible value shared by all dashboard lanes.
    """

    repository_root: Path
    file_snapshots: Mapping[str, bytes | None]
    _json_payload_cache: dict[str, dict[str, Any] | None] = dataclass_field(
        init=False,
        repr=False,
        compare=False,
    )
    _json_payload_lock: Lock = dataclass_field(init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        root = self.repository_root.resolve()
        normalized: dict[str, bytes | None] = {}
        for raw_path, raw_value in self.file_snapshots.items():
            path = Path(raw_path)
            if not path.is_absolute():
                path = root / path
            try:
                key = path.resolve().relative_to(root).as_posix()
            except (OSError, RuntimeError, ValueError) as exc:
                raise ValueError(
                    f"dashboard audit input is outside repository root: {raw_path}"
                ) from exc
            if key in normalized:
                raise ValueError(f"duplicate dashboard audit input path: {key}")
            if raw_value is not None and not isinstance(raw_value, bytes):
                raise TypeError(
                    "dashboard audit input values must be bytes or None; "
                    f"got {type(raw_value).__name__} for {key}"
                )
            normalized[key] = raw_value
        object.__setattr__(self, "repository_root", root)
        object.__setattr__(self, "file_snapshots", MappingProxyType(normalized))
        object.__setattr__(self, "_json_payload_cache", {})
        object.__setattr__(self, "_json_payload_lock", Lock())

    @classmethod
    def from_file_snapshots(
        cls,
        repository_root: Path,
        snapshots: Mapping[Path | str, bytes | str | None],
    ) -> DashboardAuditInputs:
        """Build an immutable bundle from caller-acquired exact snapshots."""

        encoded: dict[str, bytes | None] = {}
        for path, value in snapshots.items():
            encoded[str(path)] = value.encode("utf-8") if isinstance(value, str) else value
        return cls(repository_root=repository_root, file_snapshots=encoded)

    def _key(self, path: Path) -> str:
        try:
            return path.resolve().relative_to(self.repository_root).as_posix()
        except (OSError, RuntimeError, ValueError) as exc:
            raise DashboardFrozenInputError(
                f"dashboard attempted to read outside frozen repository: {path}"
            ) from exc

    def has_snapshot(self, path: Path) -> bool:
        """Whether the transaction explicitly recorded ``path``."""

        return self._key(path) in self.file_snapshots

    def is_file(self, path: Path) -> bool:
        """Return frozen file presence, rejecting an unrecorded path."""

        key = self._key(path)
        if key not in self.file_snapshots:
            raise DashboardFrozenInputError(
                f"missing frozen dashboard input: {key}"
            )
        return self.file_snapshots[key] is not None

    def read_bytes(self, path: Path) -> bytes:
        """Return exact frozen bytes, rejecting absent or unrecorded paths."""

        key = self._key(path)
        if key not in self.file_snapshots:
            raise DashboardFrozenInputError(
                f"missing frozen dashboard input: {key}"
            )
        value = self.file_snapshots[key]
        if value is None:
            raise DashboardFrozenInputError(
                f"frozen dashboard input was absent: {key}"
            )
        return value

    def read_text(self, path: Path) -> str:
        """Decode exact frozen bytes as UTF-8."""

        try:
            return self.read_bytes(path).decode("utf-8")
        except UnicodeDecodeError as exc:
            raise DashboardFrozenInputError(
                f"frozen dashboard input is not UTF-8: {self._key(path)}"
            ) from exc

    def json_payload(self, path: Path) -> dict[str, Any] | None:
        """Return one cached immutable JSON object; absence returns ``None``."""

        if not self.is_file(path):
            return None
        key = self._key(path)
        with self._json_payload_lock:
            if key in self._json_payload_cache:
                return self._json_payload_cache[key]
            try:
                payload = json.loads(self.read_bytes(path))
            except json.JSONDecodeError as exc:
                raise DashboardFrozenInputError(
                    f"invalid frozen dashboard JSON: {key}"
                ) from exc
            frozen = (
                _freeze_dashboard_json(payload)
                if isinstance(payload, dict)
                else None
            )
            self._json_payload_cache[key] = frozen
            return frozen

    def existing_files_under(
        self, folder: Path, *, suffix: str | None = None
    ) -> tuple[Path, ...]:
        """Return frozen-present files directly below ``folder``."""

        folder_key = self._key(folder).rstrip("/")
        prefix = f"{folder_key}/" if folder_key else ""
        paths: list[Path] = []
        for key, value in self.file_snapshots.items():
            if value is None or not key.startswith(prefix):
                continue
            relative = key[len(prefix) :]
            if not relative or "/" in relative:
                continue
            path = self.repository_root / key
            if suffix is None or path.suffix.lower() == suffix.lower():
                paths.append(path)
        return tuple(sorted(paths))

    def file_bytes_override(self) -> Mapping[Path, bytes | None]:
        """Return a read-only absolute-path view for exact-byte validators."""

        return MappingProxyType(
            {
                self.repository_root / relative_path: value
                for relative_path, value in self.file_snapshots.items()
            }
        )


_DASHBOARD_CANONICAL_LEGACY_SIDECARS: tuple[tuple[str, str], ...] = (
    (DEFAULT_LLM_LEAN_TO_TEX_FILE, "lean_to_tex_llm.json"),
    (DEFAULT_LLM_STATEMENT_JUDGE_FILE, "statement_match_llm.json"),
    (DEFAULT_LLM_REVIEW_SURFACE_FILE, "review_surface_llm.json"),
    (DEFAULT_LLM_PAPER_COVERAGE_FILE, "paper_coverage_llm.json"),
    (DEFAULT_LLM_DEFECT_SUPPORT_FILE, "defect_support_match_llm.json"),
    (DEFAULT_LLM_ASSUMPTION_JUDGE_FILE, "assumption_match_llm.json"),
    (PAPER_STATEMENT_MAP_FILE, "paper_statement_map.json"),
    (f"{PAPER_AUDIT_DIR}/source_proof_fidelity.json", "source_proof_fidelity.json"),
    (f"{PAPER_AUDIT_DIR}/source_record_audit.json", "source_record_audit.json"),
    (f"{PAPER_AUDIT_DIR}/source_record_match_llm.json", "source_record_match_llm.json"),
)
_DASHBOARD_STATUS_FILE_FIELDS = frozenset(
    {
        "source_file",
        "human_source_file",
        "assumption_source_file",
        "ledger_file",
        "lean_to_tex_file",
        "match_judgment_file",
        "review_surface_audit_file",
        "paper_coverage_audit_file",
        "defect_support_judgment_file",
        "assumption_judgment_file",
        "source_record_audit_file",
        "source_record_judgment_file",
        "final_validation_report",
        "review_entrypoint",
    }
)
_DASHBOARD_MAP_FILE_FIELDS = frozenset(
    {
        "path",
        "source_artifact_path",
        "source_text_file",
    }
)


def _dashboard_configured_paper_path(
    repository_root: Path,
    folder: Path,
    raw_path: object,
) -> Path | None:
    """Resolve one configured paper-local path without reading the filesystem."""

    if not isinstance(raw_path, str) or not raw_path.strip():
        return None
    relative = Path(raw_path.strip())
    if relative.is_absolute():
        raise DashboardFrozenInputError(
            f"dashboard input path must be repository- or paper-relative: {raw_path}"
        )
    anchor = repository_root if relative.parts[:1] == ("papers",) else folder
    try:
        resolved = Path(os.path.abspath(anchor / relative))
        resolved.relative_to(folder)
    except ValueError as exc:
        raise DashboardFrozenInputError(
            f"dashboard input path escapes paper folder: {raw_path}"
        ) from exc
    return resolved


def _dashboard_mapping_file_values(
    value: object,
    *,
    field_names: frozenset[str],
) -> Iterator[object]:
    """Yield structured file-field values from a JSON-compatible object."""

    if isinstance(value, Mapping):
        for raw_key, item in value.items():
            key = str(raw_key)
            if key in field_names:
                yield item
            yield from _dashboard_mapping_file_values(item, field_names=field_names)
    elif isinstance(value, list):
        for item in value:
            yield from _dashboard_mapping_file_values(item, field_names=field_names)


def _dashboard_companion_file_values(statement_map: Mapping[str, Any]) -> Iterator[object]:
    """Yield exact file descriptors from the source-text companion schema."""

    companion = statement_map.get("source_text_companion")
    if not isinstance(companion, Mapping):
        return
    for field in ("canonical_text", "visual_primary_scan", "transcript_input_scan"):
        descriptor = companion.get(field)
        if isinstance(descriptor, Mapping):
            yield descriptor.get("path")


def required_dashboard_audit_input_paths(
    folder: Path,
    *,
    status_bytes: bytes,
    statement_map_bytes: bytes | None,
    repository_root: Path = ROOT,
) -> tuple[Path, ...]:
    """Return the bounded exact-file set needed by strict dashboard checks.

    Discovery is derived only from caller-supplied status/map bytes and fixed
    dashboard conventions. The collector performs no file read, existence
    probe, glob, or directory walk. Callers must snapshot every returned path,
    recording ``None`` for absence, before constructing
    :class:`DashboardAuditInputs`.
    """

    root = Path(os.path.abspath(repository_root))
    paper_folder = Path(os.path.abspath(folder))
    try:
        paper_folder.relative_to(root)
    except ValueError as exc:
        raise DashboardFrozenInputError(
            f"paper folder is outside dashboard repository root: {folder}"
        ) from exc
    try:
        status_payload = json.loads(status_bytes)
    except json.JSONDecodeError as exc:
        raise DashboardFrozenInputError("strict dashboard status snapshot is invalid JSON") from exc
    if not isinstance(status_payload, Mapping):
        raise DashboardFrozenInputError("strict dashboard status snapshot is not an object")
    if statement_map_bytes is None:
        statement_map: Mapping[str, Any] = {}
    else:
        try:
            raw_map = json.loads(statement_map_bytes)
        except json.JSONDecodeError as exc:
            raise DashboardFrozenInputError(
                "strict dashboard statement-map snapshot is invalid JSON"
            ) from exc
        if not isinstance(raw_map, Mapping):
            raise DashboardFrozenInputError(
                "strict dashboard statement-map snapshot is not an object"
            )
        statement_map = raw_map

    paths: set[Path] = {
        paper_folder / DEFAULT_PAPER_STATUS_FILE,
        paper_folder / REVIEW_SOURCE_FILENAME,
        paper_folder / DEFAULT_ASSUMPTION_SOURCE_FILE,
        paper_folder / FINAL_VALIDATION_REPORT_FILE,
    }
    for canonical, legacy in _DASHBOARD_CANONICAL_LEGACY_SIDECARS:
        paths.add(paper_folder / canonical)
        paths.add(paper_folder / legacy)
    for pattern in PAPER_TEX_PRIORITY:
        paths.add(paper_folder / pattern.format(name=paper_folder.name))
    for pattern in PAPER_TXT_PRIORITY:
        paths.add(paper_folder / pattern.format(name=paper_folder.name))
    for pattern in PAPER_PDF_PRIORITY:
        paths.add(paper_folder / pattern.format(name=paper_folder.name))

    for raw_path in _dashboard_mapping_file_values(
        status_payload,
        field_names=_DASHBOARD_STATUS_FILE_FIELDS,
    ):
        resolved = _dashboard_configured_paper_path(root, paper_folder, raw_path)
        if resolved is not None:
            paths.add(resolved)
    for raw_path in _dashboard_mapping_file_values(
        statement_map,
        field_names=_DASHBOARD_MAP_FILE_FIELDS,
    ):
        resolved = _dashboard_configured_paper_path(root, paper_folder, raw_path)
        if resolved is not None:
            paths.add(resolved)
    for raw_path in _dashboard_companion_file_values(statement_map):
        resolved = _dashboard_configured_paper_path(root, paper_folder, raw_path)
        if resolved is not None:
            paths.add(resolved)
    return tuple(sorted(paths))


# Compatibility for the shorter name advertised during initial integration.
required_dashboard_input_paths = required_dashboard_audit_input_paths


_ACTIVE_DASHBOARD_AUDIT_INPUTS: ContextVar[DashboardAuditInputs | None] = ContextVar(
    "active_dashboard_audit_inputs", default=None
)


@contextmanager
def dashboard_audit_input_scope(
    audit_inputs: DashboardAuditInputs | None,
) -> Iterator[None]:
    """Activate exact dashboard inputs for nested legacy helper calls."""

    if audit_inputs is None:
        yield
        return
    token = _ACTIVE_DASHBOARD_AUDIT_INPUTS.set(audit_inputs)
    try:
        yield
    finally:
        _ACTIVE_DASHBOARD_AUDIT_INPUTS.reset(token)


def _dashboard_audit_inputs() -> DashboardAuditInputs | None:
    return _ACTIVE_DASHBOARD_AUDIT_INPUTS.get()


def _dashboard_is_file(path: Path) -> bool:
    inputs = _dashboard_audit_inputs()
    return inputs.is_file(path) if inputs is not None else path.is_file()


def _dashboard_read_bytes(path: Path) -> bytes:
    inputs = _dashboard_audit_inputs()
    return inputs.read_bytes(path) if inputs is not None else path.read_bytes()


def _dashboard_read_text(path: Path) -> str:
    inputs = _dashboard_audit_inputs()
    return inputs.read_text(path) if inputs is not None else path.read_text(encoding="utf-8")


def _dashboard_file_bytes_override() -> Mapping[Path, bytes | None] | None:
    """Return the active transaction's exact bytes for shared validators."""

    inputs = _dashboard_audit_inputs()
    return inputs.file_bytes_override() if inputs is not None else None


def _dashboard_json_payload(path: Path) -> dict[str, Any] | None:
    inputs = _dashboard_audit_inputs()
    if inputs is not None:
        return inputs.json_payload(path)
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None
    return payload if isinstance(payload, dict) else None


def _normalize_name_key(name: str) -> str:
    """Normalize a declaration-like name into a tolerant lookup key."""

    return re.sub(r"[^A-Za-z0-9_]+", "_", name.strip()).strip("_")


def _add_statement_variant(mapping: dict[str, str], key: str, value: str) -> None:
    mapping[key] = value
    normalized = _normalize_name_key(key)
    if normalized and normalized != key:
        mapping[normalized] = value
    lowered = key.lower()
    if lowered and lowered != key:
        mapping[lowered] = value
    lowered_normalized = normalized.lower()
    if lowered_normalized and lowered_normalized not in {lowered, normalized, key}:
        mapping[lowered_normalized] = value


def _paper_statement_key(kind: str, number: str) -> str:
    """Return a declaration-name-friendly key for a paper statement number."""

    normalized_number = number.strip().replace(".", "_").lower()
    return f"{kind.strip().lower()}{normalized_number}"


def _read_git_config_value(key: str) -> str:
    """Read a git configuration value for this repo, returning empty on failure."""

    try:
        proc = subprocess.run(
            ["git", "-C", str(ROOT), "config", "--get", key],
            check=False,
            capture_output=True,
            text=True,
            timeout=2,
        )
    except (OSError, subprocess.TimeoutExpired):
        return ""
    value = (proc.stdout or "").strip()
    if not value and proc.returncode != 0:
        return ""
    return value


def _read_gh_cli_user() -> str:
    """Read cached GitHub username from gh CLI config if available."""

    host_file = Path.home() / ".config" / "gh" / "hosts.yml"
    if not host_file.exists() or not host_file.is_file():
        return ""
    try:
        lines = host_file.read_text(encoding="utf-8").splitlines()
    except OSError:
        return ""

    in_github_host = False
    for raw_line in lines:
        line = raw_line.rstrip()
        header = re.match(r"^([A-Za-z0-9._-]+):\s*$", line)
        if header and not raw_line.startswith(" "):
            in_github_host = header.group(1).strip() == "github.com"
            continue
        if not in_github_host:
            continue
        match = re.match(r"^\s*user:\s*\"?\'?([^\"\'\\n]+)\"?\'?\s*$", line)
        if match:
            return match.group(1).strip()
    return ""


def _read_gh_api_user() -> str:
    """Return the authenticated GitHub login from `gh`, if available."""

    try:
        proc = subprocess.run(
            ["gh", "api", "user", "--jq", ".login"],
            check=False,
            capture_output=True,
            text=True,
            timeout=3,
        )
    except (OSError, subprocess.TimeoutExpired):
        return ""
    if proc.returncode != 0:
        return ""
    return (proc.stdout or "").strip()


def detect_reviewer_username(explicit_user: str | None, env_vars: list[str]) -> str:
    """Choose the best available reviewer username with sensible fallbacks."""

    user = (explicit_user or "").strip()
    if user:
        return user

    for env_var in env_vars:
        env_user = os.environ.get(env_var)
        if env_user and env_user.strip():
            return env_user.strip()

    authed = _read_gh_api_user()
    if authed:
        return authed

    cached = _read_gh_cli_user()
    if cached:
        return cached

    for key in ("github.user", "user.name", "user.username"):
        git_user = _read_git_config_value(key)
        if git_user:
            return git_user.strip()

    for env_var in OS_USER_ENV_VARS:
        env_user = os.environ.get(env_var)
        if env_user and env_user.strip():
            return env_user.strip()

    return getpass.getuser()


@dataclass
class ReviewItem:
    name: str
    kind: str
    lean_statement: str
    paper_statement: str
    agent_statement: str
    full_name: str = ""
    interface_source: str = ""
    lean_signature_manifest: dict[str, Any] | None = None
    lean_signature_sha256: str = ""
    source_status: str = ""
    source_note: str = ""
    llm_match_judgment: str = ""
    llm_match_reason: str = ""
    llm_match_stale: bool = False
    llm_match_source: str = ""
    llm_match_validator: str = ""
    llm_match_validator_type: str = ""
    llm_match_validated_at: str = ""
    llm_match_lean_statement_sha256: str = ""
    llm_match_lean_signature_sha256: str = ""
    llm_match_paper_statement_sha256: str = ""
    llm_match_tex_statement_sha256: str = ""
    llm_match_resolution: str = ""
    llm_match_boundary_type: str = ""
    llm_match_boundary_names: list[str] | None = None
    llm_match_conditional_premises: list[str] | None = None
    llm_match_resolution_reason: str = ""
    llm_match_source_routes: list[dict[str, Any]] | None = None
    llm_match_component_target_sha256: str = ""
    is_assumption: bool = False
    is_proposition_spec: bool = False
    proposition_spec_role: str = ""
    proposition_spec_proof: str = ""
    semantic_contract_lean_match_verified: bool | None = None
    semantic_contract_lean_transparency_verified: bool | None = None
    llm_assumption_judgment: str = ""
    llm_assumption_reason: str = ""
    llm_assumption_stale: bool = False
    llm_assumption_source: str = ""
    llm_assumption_validator: str = ""
    llm_assumption_validator_type: str = ""
    llm_assumption_validated_at: str = ""
    llm_assumption_lean_statement_sha256: str = ""
    llm_assumption_paper_statement_sha256: str = ""
    llm_assumption_premise_judgments: dict[str, dict[str, str]] | None = None
    paper_statement_image_url: str = ""
    line_number: int = 0
    slice_id: str = "all"
    slice_title: str = "All statements"


def find_review_source_file(folder: Path) -> Path | None:
    """Return the paper's curated human-review Lean surface, if present."""

    def display_path(path: Path) -> str:
        try:
            return str(path.relative_to(ROOT))
        except ValueError:
            return str(path)

    candidate = folder / REVIEW_SOURCE_FILENAME
    payload = load_review_slice_payload(folder)
    raw_source = payload.get("source_file")
    if isinstance(raw_source, str) and raw_source.strip():
        source = Path(raw_source.strip())
        if not source.is_absolute():
            if len(source.parts) == 1:
                source = folder / source
            else:
                source = ROOT / source
        if source.resolve() != candidate.resolve():
            raise FileNotFoundError(
                f"{folder.name} review_surface.source_file must be "
                f"{REVIEW_SOURCE_FILENAME}; got {display_path(source)}"
            )
        if _dashboard_is_file(source):
            return source

    if _dashboard_is_file(candidate):
        return candidate
    return None


def review_source_file(folder: Path) -> Path:
    """Return the paper's review source or raise a readable error."""

    source = find_review_source_file(folder)
    if source is None:
        raise FileNotFoundError(
            f"no canonical human review Lean surface ({REVIEW_SOURCE_FILENAME}) "
            f"for paper: {folder.name}"
        )
    return source


def review_source_module(folder: Path, source_file: Path) -> str:
    """Return the Lean import module for a paper-local review source."""

    return f"{folder.name}.{source_file.stem}"


def assumption_source_file(folder: Path) -> Path:
    """Return the paper-local Lean source that holds explicit assumptions."""

    payload = load_review_slice_payload(folder)
    raw_path = payload.get("assumption_source_file")
    if isinstance(raw_path, str) and raw_path.strip():
        path = Path(raw_path.strip())
        if not path.is_absolute():
            if len(path.parts) == 1:
                path = folder / path
            else:
                path = ROOT / path
        return path
    return folder / DEFAULT_ASSUMPTION_SOURCE_FILE


def find_paper_pdf(folder: Path) -> Path | None:
    """Find the most likely paper pdf in a folder."""

    inputs = _dashboard_audit_inputs()
    if inputs is not None:
        candidates = inputs.existing_files_under(folder, suffix=".pdf")
        by_name = {path.name: path for path in candidates}
        for rel in PAPER_PDF_PRIORITY:
            candidate = by_name.get(rel.format(name=folder.name))
            if candidate is not None:
                return candidate
        return next(
            (
                path
                for path in candidates
                if path.name.lower() not in {"dependencydag.pdf", "dependency_dag.pdf"}
            ),
            None,
        )
    for rel in PAPER_PDF_PRIORITY:
        candidate = folder / rel.format(name=folder.name)
        if candidate.exists() and candidate.is_file():
            return candidate

    for candidate in sorted(
        p
        for p in folder.glob("*.pdf")
        if p.is_file() and p.name.lower() not in {"dependencydag.pdf", "dependency_dag.pdf"}
    ):
        return candidate
    return None


def find_paper_text(folder: Path) -> Path | None:
    """Find a compact text fallback for paper-source viewing."""

    inputs = _dashboard_audit_inputs()
    if inputs is not None:
        candidates = {
            path.name: path for path in inputs.existing_files_under(folder, suffix=".txt")
        }
        for rel in PAPER_TXT_PRIORITY:
            candidate = candidates.get(rel.format(name=folder.name))
            if candidate is not None:
                return candidate
        return None
    for rel in PAPER_TXT_PRIORITY:
        candidate = folder / rel.format(name=folder.name)
        if candidate.exists() and candidate.is_file():
            return candidate
    return None


def paper_asset_url(paper: str, path: Path) -> str:
    """Build a safe route path for a paper-local asset."""

    return f"/paper-assets/{urllib.parse.quote(paper)}/{urllib.parse.quote(path.name)}"


def paper_rendered_statement_url(paper: str, path: Path) -> str:
    """Build a safe route path for a generated statement image."""

    return f"/rendered-statements/{urllib.parse.quote(paper)}/{urllib.parse.quote(path.name)}"


def _file_sha256(path: Path | None) -> str:
    """Return a stable binary digest for a source file."""

    if path is None:
        return ""
    inputs = _dashboard_audit_inputs()
    if inputs is not None:
        if not inputs.is_file(path):
            return ""
        return hashlib.sha256(inputs.read_bytes(path)).hexdigest()
    if not path.exists() or not path.is_file():
        return ""
    digest = hashlib.sha256()
    try:
        with path.open("rb") as handle:
            for chunk in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(chunk)
    except OSError:
        return ""
    return digest.hexdigest()


def parse_block_comment(lines: list[str], start: int) -> tuple[str, int]:
    """Collect a block comment from `start`; return text and first line after it."""

    collected = [lines[start]]
    j = start
    if "-/" in lines[start]:
        return "\n".join(collected), start + 1
    while j + 1 < len(lines):
        j += 1
        collected.append(lines[j])
        if "-/" in lines[j]:
            return "\n".join(collected), j + 1
    return "\n".join(collected), len(lines)


def clean_comment(raw: str) -> str:
    """Strip Lean block comment markers and clean a docstring for display."""

    text = raw.strip()
    if text.startswith("/-!"):
        text = text[3:]
    elif text.startswith("/-"):
        text = text[2:]
    if text.endswith("-/"):
        text = text[:-2]
    text = text.strip()
    lines = [line.lstrip(" *") for line in text.splitlines()]
    return "\n".join(line.strip() for line in lines).strip()


def split_source_metadata(text: str) -> tuple[str, str, str]:
    """Extract dashboard-only source provenance lines from a docstring."""

    kept: list[str] = []
    source_status = ""
    source_notes: list[str] = []
    for raw_line in text.splitlines():
        line = raw_line.strip()
        status_match = re.match(r"^Source status:\s*(.+)$", line, flags=re.IGNORECASE)
        if status_match:
            source_status = status_match.group(1).strip()
            continue
        note_match = re.match(r"^Source note:\s*(.+)$", line, flags=re.IGNORECASE)
        if note_match:
            source_notes.append(note_match.group(1).strip())
            continue
        kept.append(raw_line)
    return "\n".join(kept).strip(), source_status, " ".join(source_notes).strip()


def normalize_statement(text: str) -> str:
    """Normalize statement text for drift comparisons."""

    return re.sub(r"\s+", " ", text.strip())


def statement_digest(text: str) -> str:
    """Generate a stable digest for a statement snapshot."""

    return hashlib.sha256(normalize_statement(text).encode("utf-8")).hexdigest()


def corrected_target_digest(raw: Any) -> str:
    """Hash a corrected-target record independently of JSON key ordering.

    This is source-map evidence, not a Lean declaration identity.  It binds a
    reviewed target to its archival baseline, governing defect, and approval
    pin so a later edit cannot silently keep old coverage credit.
    """

    payload = dict(raw) if isinstance(raw, dict) else raw
    if isinstance(payload, dict):
        payload.pop("corrected_target_sha256", None)
    return hashlib.sha256(
        json.dumps(payload, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode(
            "utf-8"
        )
    ).hexdigest()


def _source_item_is_corrected_target(item: dict[str, Any]) -> bool:
    return (
        str(item.get("coverage_status") or "").strip().lower()
        == CORRECTED_SOURCE_STATEMENT_STATUS
    )


def _corrected_target_primary_declaration(item: dict[str, Any]) -> str | None:
    """Return the sole paper-facing endpoint authorized for a repaired target.

    A corrected target is one complete mathematical proposition. Its map entry
    must therefore name exactly one PaperInterface theorem or lemma in
    ``lean_declarations``. Navigation aliases, proof steps, support rows, and
    semantic bridges may remain in the map, but they cannot each inherit the
    repaired statement or accumulate partial credit for it.
    """

    declarations = item.get("lean_declarations")
    if not isinstance(declarations, list) or len(declarations) != 1:
        return None
    declaration = declarations[0]
    if not isinstance(declaration, str) or not declaration.strip():
        return None
    return declaration.strip()


def _corrected_target_coverage_rows_match_primary(
    primary_declaration: str,
    review_rows: list[str],
    source_inventory: object,
    paper_name: str,
) -> bool:
    """Accept the configured endpoint or its unique dashboard-local row name.

    Source maps retain fully qualified Lean declarations, while a dashboard row
    is named by the final PaperInterface declaration component. This is only a
    navigation translation: a short name is accepted for a corrected target
    when it uniquely identifies a configured route in this paper's
    PaperInterface. The normal coverage checks still require an exact current
    elaborated signature and a semantic source route.
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
    if not isinstance(source_inventory, dict):
        return False

    configured_routes: set[str] = set()
    for item in source_inventory.values():
        if not isinstance(item, dict):
            continue
        declarations = item.get("lean_declarations")
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


def source_item_direct_coverage_declarations(item: dict[str, Any]) -> list[str]:
    """Return the declarations eligible for direct source coverage.

    Only ``lean_declarations`` designates a paper-facing source route.
    ``proof_lean_declarations`` and semantic bridge fields document proof or
    translation support, but are not themselves evidence that the source
    statement was reviewed at that declaration. ``aliases`` are a compatibility
    fallback only for legacy records with no explicit paper-facing declaration
    route at all; they can never supplement an explicit route or select a
    partial wrapper.
    """

    if _source_item_is_corrected_target(item):
        primary = _corrected_target_primary_declaration(item)
        return [primary] if primary else []

    names = _normalize_string_list(item.get("lean_declarations"))
    if names:
        return list(dict.fromkeys(names))
    return list(dict.fromkeys(_normalize_string_list(item.get("aliases"))))


def source_item_statement_routing_declarations(item: dict[str, Any]) -> list[str]:
    """Return rows that need the source text for a semantic comparison.

    A declared semantic bridge can receive the source statement as comparison
    input, because the audit must check whether it actually transports the
    source model to the paper-facing endpoint. That routing does *not* grant
    source-coverage or proof credit: those remain restricted to
    ``source_item_direct_coverage_declarations`` and the independently checked
    bridge contract. A configured proposition specification likewise needs the
    canonical source statement as comparison input, but its declaration label
    supplies no coverage or proof evidence. Aliases and proof/support
    declarations remain excluded. Corrected targets route their corrected text
    to the one explicit endpoint and to configured specifications only; the
    archival statement is never attributed to a helper or bridge.
    """

    direct = source_item_direct_coverage_declarations(item)
    routed = list(direct)
    routed.extend(_source_item_specification_statement_routing_declarations(item))
    if _source_item_is_corrected_target(item):
        return list(dict.fromkeys(routed))
    for field in SEMANTIC_BRIDGE_DECLARATION_FIELDS:
        routed.extend(_normalize_string_list(item.get(field)))
    return list(dict.fromkeys(routed))


def _source_item_specification_statement_routing_declarations(
    item: dict[str, Any],
) -> list[str]:
    """Return configured Spec navigation labels needing comparison text only."""

    routed = _normalize_string_list(item.get("spec_lean_declarations"))
    contract = item.get("semantic_contract")
    if isinstance(contract, dict):
        specification = contract.get("spec_declaration")
        if isinstance(specification, str) and specification.strip():
            routed.append(specification.strip())
    return list(dict.fromkeys(routed))


def _source_item_corrected_target(item: dict[str, Any]) -> dict[str, Any] | None:
    """Return the structured corrected target only when its basic shape is usable.

    Full map-schema and source-ledger validation lives in
    ``audit_evidence_integrity.py``.  Dashboard checks still fail closed here
    when a source route or coverage row tries to use a malformed target.
    """

    target = item.get("corrected_target")
    if not isinstance(target, dict):
        return None
    if target.get("schema") != CORRECTED_TARGET_SCHEMA:
        return None
    statement = str(target.get("statement") or "").strip()
    if not statement:
        return None
    return target


def _source_item_coverage_statement(item: dict[str, Any]) -> tuple[str, str]:
    """Return the statement/digest a coverage row is allowed to credit.

    Ordinary source items use the archival source statement.  A corrected item
    is intentionally different: only its explicit repaired target may be
    matched to Lean, while the archival statement remains visible in the
    inventory and never receives proof credit.
    """

    if _source_item_is_corrected_target(item):
        target = _source_item_corrected_target(item)
        if target is None:
            return "", ""
        statement = normalize_statement(str(target.get("statement") or ""))
        return statement, statement_digest(statement)
    statement = normalize_statement(str(item.get("statement") or ""))
    return statement, statement_digest(statement) if statement else ""


def _source_item_coverage_location(item: dict[str, Any]) -> str:
    """Return the archival anchor associated with the reviewed target."""

    if _source_item_is_corrected_target(item):
        target = _source_item_corrected_target(item)
        if target is None:
            return ""
        return str(target.get("archival_source_locator") or "").strip()
    return str(item.get("source_location") or "").strip()


def _source_item_corrected_target_metadata_error(item: dict[str, Any]) -> str:
    """Return a compact fail-closed error for dashboard corrected-target use."""

    if not _source_item_is_corrected_target(item):
        return "source item is not marked corrected_source_statement"
    if _corrected_target_primary_declaration(item) is None:
        return (
            "lean_declarations must be an exact one-element string list naming "
            "the complete corrected-target endpoint"
        )
    if _normalize_string_list(item.get("proof_lean_declarations")):
        return (
            "proof_lean_declarations is prohibited for corrected_source_statement; "
            "move helper proofs to support_lean_declarations"
        )
    target = _source_item_corrected_target(item)
    if target is None:
        return "source item has no valid structured corrected_target"
    if target.get("archival_equivalence_claimed") is not False:
        return "corrected_target must explicitly set archival_equivalence_claimed to false"
    archival = normalize_statement(str(item.get("statement") or ""))
    corrected, _ = _source_item_coverage_statement(item)
    if not archival or not corrected or archival == corrected:
        return "corrected_target must differ from the archival source statement"
    governing = _normalize_string_list(target.get("governing_defect_ids"))
    routed = _normalize_string_list(item.get("source_defect_ids"))
    if not governing or not set(governing).issubset(set(routed)):
        return "corrected_target governing_defect_ids must be a nonempty subset of source_defect_ids"
    if not str(target.get("archival_source_locator") or "").strip():
        return "corrected_target has no archival source locator"
    archival_quote_digest = str(
        target.get("archival_source_quote_sha256") or ""
    ).strip().lower()
    if not re.fullmatch(r"[0-9a-f]{64}", archival_quote_digest):
        return "corrected_target has no valid archival source quote digest"
    approval = target.get("approval")
    if not isinstance(approval, dict):
        return "corrected_target has no structured approval"
    if str(approval.get("target_statement_sha256") or "").strip().lower() != statement_digest(
        corrected
    ):
        return "corrected_target approval has a stale target statement digest"
    if str(target.get("corrected_target_sha256") or "").strip().lower() != corrected_target_digest(
        target
    ):
        return "corrected_target has a stale corrected-target record digest"
    return ""


def lean_statement_digest_candidates(
    lean_statement: str, interface_source: str = ""
) -> set[str]:
    """Return acceptable Lean-statement digests for freshness checks.

    `lean_statement` may include a rendered `#check` preview when the local Lean
    subprocess succeeds. `interface_source` is the source-level declaration text
    from the paper-facing Lean file. Sidecar freshness must remain stable when
    CI cannot render the optional preview and falls back to source text.
    """

    digests: set[str] = set()
    for text in (interface_source, lean_statement):
        if text and text.strip():
            digests.add(statement_digest(text))
    return digests


def source_metadata_digest(source_status: str, source_note: str) -> str:
    """Digest source-provenance metadata that should invalidate old reviews."""

    status = normalize_statement(source_status)
    note = normalize_statement(source_note)
    if not status and not note:
        return ""
    direct_statuses = {
        "direct paper definition",
        "direct paper statement",
        "direct paper formula",
        "direct source text",
        "direct source formula",
    }
    if status.lower() in direct_statuses and not note:
        return ""
    return statement_digest(f"{status}\n{note}")


def strip_qualified_identifiers(value: str) -> str:
    """Drop long qualified Lean identifiers (`A.B.C`) while preserving base names."""

    return re.sub(
        r"\b([A-Za-z_][A-Za-z0-9_']*\.)+([A-Za-z_][A-Za-z0-9_']*)",
        r"\2",
        value,
    )


def _apply_latex_token_mapping(raw: str) -> str:
    """Apply a compact symbol-to-LaTeX mapping."""

    value = raw.strip().replace("\n", " ")
    value = re.sub(r"\s+", " ", value).strip()
    if not value:
        return ""
    for old, new in LEAN_TO_TEX_TOKENS:
        value = value.replace(old, new)
    for symbol in ("->", "=>", "<->", "<=>"):
        if symbol in value:
            value = value.replace(symbol, " " + symbol + " ")
    return value[:AGENT_PREVIEW_MAX_LEN]


def lean_to_latex_statement(raw: str) -> str:
    """Generate a compact, heuristic TeX-like draft from a Lean declaration signature."""

    if not raw:
        return ""
    value = raw.strip().replace("\n", " ")
    value = re.sub(r"\s+", " ", value).strip()
    if not value:
        return ""
    if ":= by" in value:
        value = value.split(":= by", 1)[0].rstrip()
    value = AGENT_PREVIEW_TOKEN_RE.sub("", value, count=1)
    value = re.sub(r"\s*:\s*[^:=]+:=", " := ", value, count=1)
    value = value.replace(":=", "=")
    value = value.strip().strip(",")
    return _apply_latex_token_mapping(value)


def lean_check_to_latex_statement(raw: str) -> str:
    """Map Lean #check output type text to compact TeX-like form."""

    if not raw:
        return ""
    value = strip_qualified_identifiers(raw)
    return _apply_latex_token_mapping(value)


def _parse_lean_check_previews(output: str, theorem_names: list[str]) -> dict[str, str]:
    """Parse Lean `#check` output into declaration-name to type-text map."""

    names_sorted = sorted(theorem_names, key=len, reverse=True)
    captured: dict[str, list[str]] = {}
    active: str | None = None
    for raw_line in output.splitlines():
        line = raw_line.rstrip()
        matched = False
        for name in names_sorted:
            pattern = rf"^@?{re.escape(name)}\s*:\s*(.*)$"
            match = re.match(pattern, line)
            if not match:
                continue
            body = match.group(1).strip()
            captured[name] = []
            if body:
                captured[name].append(body)
            active = name
            matched = True
            break
        if matched:
            continue
        # Lean's pretty-printer does not indent every continuation. In
        # particular, `let`/`have` chains can begin in column zero. The script
        # contains only #check commands, so everything up to the next known
        # declaration header belongs to the active type preview.
        if active is not None and line.strip():
            captured[active].append(line.strip())

    result: dict[str, str] = {}
    for name, parts in captured.items():
        text = " ".join(parts).strip()
        if text:
            result[name] = text
    return result


def run_lean_check_previews(
    paper_folder: Path,
    theorem_names: list[str],
    timeout_seconds: int = AGENT_PREVIEW_CHECK_TIMEOUT,
    source_file: Path | None = None,
) -> dict[str, str]:
    """Ask Lean for #check output on Lean declarations, with fallback on failure."""

    if not theorem_names:
        return {}
    canonical_names = sorted(set(theorem_names))
    module_file = source_file or find_review_source_file(paper_folder)
    if module_file is None or not _dashboard_is_file(module_file):
        return {}
    cache_key = f"{paper_folder.resolve()}::{module_file.name}::{'|'.join(canonical_names)}"
    if cache_key in AGENT_PREVIEW_CACHE:
        return AGENT_PREVIEW_CACHE[cache_key]

    import_module = review_source_module(paper_folder, module_file)
    lines = [
        f"import {import_module}",
        "set_option pp.universes false",
        "",
    ]
    for name in canonical_names:
        lines.append(f"#check (@{name})")
    script = "\n".join(lines) + "\n"

    with tempfile.TemporaryDirectory() as tmpdir:
        script_path = Path(tmpdir) / "review_agent_preview.lean"
        script_path.write_text(script, encoding="utf-8")
        try:
            proc = subprocess.Popen(
                ["lake", "env", "lean", str(script_path)],
                cwd=str(ROOT),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                start_new_session=True,
            )
            stdout_bytes, _stderr = proc.communicate(timeout=timeout_seconds)
        except (OSError, subprocess.TimeoutExpired):
            if "proc" in locals():
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                try:
                    proc.communicate(timeout=1)
                except (OSError, subprocess.TimeoutExpired):
                    pass
            AGENT_PREVIEW_CACHE[cache_key] = {}
            return {}

    stdout = stdout_bytes.decode("utf-8", errors="replace")

    if proc.returncode != 0 and not stdout.strip():
        AGENT_PREVIEW_CACHE[cache_key] = {}
        return {}

    checked = _parse_lean_check_previews(stdout, canonical_names)
    AGENT_PREVIEW_CACHE[cache_key] = checked
    return checked


def agent_preview_comment(
    comment: str | None, raw_statement: str, check_statement: str | None = None
) -> str:
    """Prefer Lean #check output, then signature heuristic, then doc-comment fallback."""

    if check_statement:
        translated = lean_check_to_latex_statement(check_statement)
        if translated:
            return translated
    translated = lean_to_latex_statement(raw_statement)
    if translated:
        return translated
    if comment:
        text = re.sub(r"\s+", " ", comment).strip()
        return text[:AGENT_PREVIEW_MAX_LEN]
    return "(no auto-generated preview available)"



def parse_report_texts(report_path: Path) -> dict[str, str]:
    """Extract theorem-level paper statement summaries from final report bullets."""

    statements: dict[str, str] = {}
    lines = _dashboard_read_text(report_path).splitlines()
    ignored_sections = {"statement translation audit"}
    active_section = ""
    i = 0
    while i < len(lines):
        line = lines[i]
        heading = re.match(r"^#{2,6}\s+(.+?)\s*$", line)
        if heading:
            active_section = re.sub(
                r"^\d+\.\s*", "", heading.group(1).strip().lower()
            )
            i += 1
            continue
        if active_section in ignored_sections:
            i += 1
            continue
        match = REPORT_CLAUSE_RE.match(line)
        if not match:
            i += 1
            continue

        name = match.group("name")
        text = match.group("text").strip()
        i += 1
        extras: list[str] = []
        while i < len(lines):
            nxt = lines[i]
            if not nxt.strip():
                i += 1
                continue
            if nxt.lstrip().startswith("- "):
                break
            if re.match(r"^\s{2,}\S", nxt):
                extras.append(nxt.strip())
                i += 1
                continue
            break
        if extras:
            text = " ".join([text] + extras).strip()
        if text:
            _add_statement_variant(statements, name, text)
        else:
            _add_statement_variant(statements, name, "(No extracted paper statement text found.)")
    return statements


def find_paper_tex_source(folder: Path) -> Path | None:
    """Find the likely paper TeX source used for display text extraction."""

    inputs = _dashboard_audit_inputs()
    if inputs is not None:
        candidates = inputs.existing_files_under(folder, suffix=".tex")
        by_name = {path.name: path for path in candidates}
        for rel in PAPER_TEX_PRIORITY:
            candidate = by_name.get(rel.format(name=folder.name))
            if candidate is not None:
                return candidate
        return next(
            (
                path
                for path in candidates
                if path.name.lower()
                not in {"dependencydag.tex", "dependency_dag.tex", "paperinterface.tex"}
            ),
            None,
        )
    for rel in PAPER_TEX_PRIORITY:
        candidate = folder / rel.format(name=folder.name)
        if candidate.exists() and candidate.is_file():
            return candidate

    for candidate in sorted(
        p
        for p in folder.glob("*.tex")
        if p.is_file()
    ):
        if candidate.name.lower() in {"dependencydag.tex", "dependency_dag.tex", "paperinterface.tex"}:
            continue
        return candidate
    return None


def parse_paper_tex_statements(folder: Path) -> dict[str, str]:
    """Extract labeled theorem-like statements from a LaTeX source file."""

    source = find_paper_tex_source(folder)
    if source is None:
        return {}

    try:
        lines = _dashboard_read_text(source).splitlines()
    except OSError:
        return {}

    statements: dict[str, str] = {}
    in_env = False
    active_label: str | None = None
    active_kind: str | None = None
    active_lines: list[str] = []

    for raw_line in lines:
        line = raw_line.strip()

        if not in_env:
            open_match = THEOREM_ENV_OPEN_RE.match(line)
            if open_match:
                in_env = True
                active_kind = open_match.group(1)
                active_label = None
                active_lines = [raw_line]
                continue
            else:
                continue

        if in_env and active_kind is not None:
            active_lines.append(raw_line)
            label_match = THEOREM_LABEL_RE.search(raw_line)
            if label_match and not active_label:
                active_label = label_match.group(1).strip()

            close_match = THEOREM_ENV_CLOSE_RE.match(line)
            if close_match:
                if close_match.group(1) == active_kind:
                    if active_label:
                        text = " ".join(active_lines)
                        text = re.sub(r"%.*$", "", text)
                        text = THEOREM_ENV_OPEN_RE.sub("", text)
                        text = THEOREM_ENV_CLOSE_RE.sub("", text)
                        text = THEOREM_LABEL_RE.sub("", text)
                        text = re.sub(r"\s+", " ", text).strip()
                        if text:
                            _add_statement_variant(statements, active_label, text)
                in_env = False
                active_label = None
                active_kind = None
                active_lines = []

    return statements


def _clean_paper_text_statement(lines: list[str]) -> str:
    """Clean a statement block extracted from a PDF text dump."""

    cleaned: list[str] = []
    blank_pending = False
    for raw_line in lines:
        line = raw_line.replace("\f", "").rstrip()
        if not line.strip():
            blank_pending = bool(cleaned)
            continue
        if line.strip().isdigit():
            continue
        if blank_pending and cleaned:
            cleaned.append("")
        cleaned.append(line)
        blank_pending = False
    return "\n".join(cleaned).strip()


def parse_paper_text_statements(folder: Path) -> dict[str, str]:
    """Extract numbered paper statements from `source.txt` when no TeX is present."""

    source = find_paper_text(folder)
    if source is None:
        return {}

    try:
        lines = _dashboard_read_text(source).splitlines()
    except OSError:
        return {}

    statements: dict[str, str] = {}
    active_key: str | None = None
    active_kind: str | None = None
    active_number: str | None = None
    active_lines: list[str] = []

    def flush() -> None:
        nonlocal active_key, active_kind, active_number, active_lines
        if active_key:
            text = _clean_paper_text_statement(active_lines)
            if text:
                _add_statement_variant(statements, active_key, text)
                if active_kind and active_number:
                    _add_statement_variant(
                        statements,
                        f"{active_kind.lower()}_{active_number.replace('.', '_').lower()}",
                        text,
                    )
        active_key = None
        active_kind = None
        active_number = None
        active_lines = []

    for raw_line in lines:
        stripped = raw_line.strip()
        label_match = PAPER_TEXT_STATEMENT_LABEL_RE.match(stripped)
        if label_match:
            flush()
            active_kind = label_match.group("kind")
            active_number = label_match.group("number")
            active_key = _paper_statement_key(active_kind, active_number)
            active_lines = [raw_line]
            continue

        if active_key is not None and PAPER_TEXT_STATEMENT_STOP_RE.match(stripped):
            flush()
            continue

        if active_key is not None:
            active_lines.append(raw_line)

    flush()
    return statements


def parse_paper_statement_map(folder: Path) -> dict[str, str]:
    """Load explicit paper-source line ranges for dashboard statements."""

    map_path = folder / PAPER_STATEMENT_MAP_FILE
    if not _dashboard_is_file(map_path):
        return {}

    payload = _dashboard_json_payload(map_path)
    if payload is None:
        return {}

    raw_items = payload.get("items", payload) if isinstance(payload, dict) else {}
    if not isinstance(raw_items, dict):
        return {}

    statements: dict[str, str] = {}
    text_cache: dict[str, list[str]] = {}
    for key, raw_item in raw_items.items():
        if not isinstance(key, str) or not key.strip() or not isinstance(raw_item, dict):
            continue
        direct_statement = str(raw_item.get("statement") or "").strip()
        if direct_statement:
            archival_text = normalize_statement(direct_statement)
            corrected_target = raw_item.get("corrected_target")
            corrected_text = ""
            if (
                str(raw_item.get("coverage_status") or "").strip().lower()
                == CORRECTED_SOURCE_STATEMENT_STATUS
                and isinstance(corrected_target, dict)
                and corrected_target.get("schema") == CORRECTED_TARGET_SCHEMA
            ):
                corrected_text = normalize_statement(
                    str(corrected_target.get("statement") or "")
                )
            # The map key identifies archival source text. A corrected target
            # may be routed only to the explicitly designated direct endpoint.
            # Navigation aliases and support declarations never inherit a
            # source statement, even for ordinary rows: an alias is not a
            # semantic comparison and a conjunction of helpers is not itself
            # evidence for a paper-facing theorem.
            _add_statement_variant(statements, key.strip(), archival_text)
            primary_declaration = _corrected_target_primary_declaration(raw_item)
            if corrected_text and primary_declaration:
                for declaration in list(
                    dict.fromkeys(
                        [primary_declaration]
                        + _source_item_specification_statement_routing_declarations(
                            raw_item
                        )
                    )
                ):
                    _add_statement_variant(statements, declaration, corrected_text)
            else:
                for declaration in source_item_statement_routing_declarations(raw_item):
                    _add_statement_variant(statements, declaration, archival_text)
            continue
        source_text_file = str(raw_item.get("source_text_file") or "source.txt").strip()
        if not source_text_file or "/" in source_text_file or "\\" in source_text_file:
            continue
        try:
            start_line = int(raw_item.get("start_line"))
            end_line = int(raw_item.get("end_line"))
        except (TypeError, ValueError):
            continue
        if start_line <= 0 or end_line < start_line:
            continue

        source_path = folder / source_text_file
        try:
            lines = text_cache[source_text_file]
        except KeyError:
            try:
                lines = _dashboard_read_text(source_path).splitlines()
            except OSError:
                continue
            text_cache[source_text_file] = lines

        if start_line > len(lines):
            continue
        selected = lines[start_line - 1 : min(end_line, len(lines))]
        text = _clean_paper_text_statement(selected)
        if not text:
            continue
        _add_statement_variant(statements, key.strip(), text)
        for declaration in source_item_statement_routing_declarations(raw_item):
            _add_statement_variant(statements, declaration, text)
    return statements


def paper_statement_inventory(folder: Path) -> dict[str, dict[str, Any]]:
    """Return canonical source-paper statements for paper-level coverage audit.

    `audit/paper_statement_map.json` is the canonical source inventory because
    it separates source items from aliases.  Fallback extraction is intentionally
    lightweight and is best treated as a prompt scaffold, not a closeout-quality
    source inventory.
    """

    map_path = folder / PAPER_STATEMENT_MAP_FILE
    if _dashboard_is_file(map_path):
        payload = _dashboard_json_payload(map_path) or {}
        raw_items = payload.get("items", payload) if isinstance(payload, dict) else {}
        if isinstance(raw_items, dict):
            # Scoped computational illustrations need a source artifact identity and
            # an exact locator.  Preserve the map-level pin on each inventory item
            # so the source-first coverage check can enforce that requirement before
            # an item is allowed to leave the theorem-review lane.
            map_source_artifact_path = str(
                payload.get("source_artifact_path") or ""
            ).strip()
            map_source_artifact_sha256 = str(
                payload.get("source_artifact_sha256") or ""
            ).strip()
            map_source_anchor_evidence_required = (
                payload.get("source_anchor_evidence_required") is True
            )
            inventory: dict[str, dict[str, Any]] = {}
            text_cache: dict[str, list[str]] = {}
            for raw_key, raw_item in raw_items.items():
                key = str(raw_key or "").strip()
                if not key or not isinstance(raw_item, dict):
                    continue
                direct_statement = str(raw_item.get("statement") or "").strip()
                source_text_file = str(raw_item.get("source_text_file") or "source.txt").strip()
                source_location = str(raw_item.get("source_location") or "").strip()
                source_url = str(raw_item.get("source_url") or payload.get("source_url") or "").strip()
                source_note = str(raw_item.get("source_note") or "").strip()
                source_status = str(raw_item.get("source_status") or "").strip()
                text = ""
                if direct_statement:
                    text = normalize_statement(direct_statement)
                else:
                    if not source_text_file or "/" in source_text_file or "\\" in source_text_file:
                        continue
                    try:
                        start_line = int(raw_item.get("start_line"))
                        end_line = int(raw_item.get("end_line"))
                    except (TypeError, ValueError):
                        continue
                    if start_line <= 0 or end_line < start_line:
                        continue
                    source_path = folder / source_text_file
                    try:
                        lines = text_cache[source_text_file]
                    except KeyError:
                        try:
                            lines = _dashboard_read_text(source_path).splitlines()
                        except OSError:
                            continue
                        text_cache[source_text_file] = lines
                    if start_line > len(lines):
                        continue
                    selected = lines[start_line - 1 : min(end_line, len(lines))]
                    text = _clean_paper_text_statement(selected)
                    if not source_location:
                        source_location = f"{source_text_file}:{start_line}-{end_line}"
                if not text:
                    continue
                aliases = [
                    str(alias).strip()
                    for alias in raw_item.get("aliases", []) or []
                    if isinstance(alias, str) and alias.strip()
                ]
                inventory[key] = {
                    "title": str(raw_item.get("title") or "").strip(),
                    "statement": text,
                    "aliases": aliases,
                    # This is source-presentation metadata, not a Lean route.
                    # Preserve it through the prompt projection so ordinary
                    # coverage counts the canonical result once even when its
                    # proof restates the same theorem or lemma later.
                    "source_presentation_alias": raw_item.get(
                        "source_presentation_alias"
                    ),
                    "source": PAPER_STATEMENT_MAP_FILE,
                    "coverage_status": str(
                        raw_item.get("coverage_status") or ""
                    ).strip().lower(),
                    "protocol_role": str(
                        raw_item.get("protocol_role") or ""
                    ).strip().lower(),
                    "corrected_target": raw_item.get("corrected_target"),
                    "source_kind": str(raw_item.get("source_kind") or "").strip().lower(),
                    "claim_bearing": raw_item.get("claim_bearing"),
                    "source_scope_classification": str(
                        raw_item.get("source_scope_classification") or ""
                    ).strip().lower(),
                    "user_approved_scope_exclusion": raw_item.get(
                        "user_approved_scope_exclusion"
                    ),
                    "scope_reason": str(raw_item.get("scope_reason") or "").strip(),
                    "source_evidence": str(raw_item.get("source_evidence") or "").strip(),
                    "source_artifact_path": str(
                        raw_item.get("source_artifact_path")
                        or map_source_artifact_path
                        or ""
                    ).strip(),
                    "source_artifact_sha256": str(
                        raw_item.get("source_artifact_sha256")
                        or map_source_artifact_sha256
                        or ""
                    ).strip(),
                    "canonical_source_artifact_path": map_source_artifact_path,
                    "canonical_source_artifact_sha256": map_source_artifact_sha256,
                    "source_anchor_evidence_required": (
                        raw_item.get("source_anchor_evidence_required") is True
                        or map_source_anchor_evidence_required
                    ),
                    "source_anchor_evidence": raw_item.get(
                        "source_anchor_evidence"
                    ),
                    "source_defect_ids": _normalize_string_list(
                        raw_item.get("source_defect_ids")
                    ),
                    "support_lean_declarations": _normalize_string_list(
                        raw_item.get("support_lean_declarations")
                    ),
                    "spec_lean_declarations": _normalize_string_list(
                        raw_item.get("spec_lean_declarations")
                    ),
                    "semantic_contract": raw_item.get("semantic_contract"),
                    "lean_declarations": _normalize_string_list(
                        raw_item.get("lean_declarations")
                    ),
                    "proof_lean_declarations": _normalize_string_list(
                        raw_item.get("proof_lean_declarations")
                    ),
                    "source_location": source_location,
                    "source_url": source_url,
                    "source_note": source_note,
                    "source_status": source_status,
                    "statement_sha256": statement_digest(text),
                }
                if "model_convention_ids" in raw_item:
                    # Preserve even malformed raw metadata. Downstream semantic
                    # reuse must reject an empty, duplicate, or unresolved
                    # convention receipt instead of treating it as absent.
                    inventory[key]["model_convention_ids"] = raw_item.get(
                        "model_convention_ids"
                    )
                if SOURCE_DEFINITION_PARTITION_FIELD in raw_item:
                    inventory[key][SOURCE_DEFINITION_PARTITION_FIELD] = raw_item.get(
                        SOURCE_DEFINITION_PARTITION_FIELD
                    )
            if inventory:
                return inventory

    tex_statements = parse_paper_tex_statements(folder)
    if tex_statements:
        return {
            key: {
                "statement": value,
                "aliases": [],
                "source": find_paper_tex_source(folder).name if find_paper_tex_source(folder) else "",
                "source_location": key,
                "statement_sha256": statement_digest(value),
            }
            for key, value in sorted(tex_statements.items())
            if key and value
        }

    text_statements = parse_paper_text_statements(folder)
    locations = parse_paper_text_statement_locations(folder)
    if locations:
        inventory = {}
        for location in locations:
            key = str(location.get("key") or "").strip()
            value = text_statements.get(key)
            if key and value:
                inventory[key] = {
                    "statement": value,
                    "aliases": [],
                    "source": find_paper_text(folder).name if find_paper_text(folder) else "",
                    "source_location": f"page {location.get('page')}, line {location.get('line_number')}",
                    "statement_sha256": statement_digest(value),
                }
        return inventory
    return {}


def paper_statement_map_payload(folder: Path) -> dict[str, Any]:
    """Load the canonical source-map object when one is available.

    The full source inventory remains available for an explicit deep audit. The
    ordinary closeout selector below reads only source-presentation metadata
    from this payload; it never uses map keys or Lean declaration names.
    """

    map_path = folder / PAPER_STATEMENT_MAP_FILE
    if not _dashboard_is_file(map_path):
        return {}
    payload = _dashboard_json_payload(map_path)
    return payload if isinstance(payload, dict) else {}


def source_component_route_key(
    source_item_key: str, source_anchor_sha256: str
) -> str:
    """Return the stable identity for a quoted source subclaim.

    A source-map item can contain several mathematical components.  The map
    item key is a navigation handle, not evidence that every paper-interface
    row establishes its whole statement.  This key instead binds a component
    route to the parent source item and to the SHA-256 of the exact quoted
    source bytes.  Lean declaration names are intentionally absent from the
    identity.
    """

    return (
        f"{source_item_key}::source-component::"
        f"{source_anchor_sha256.strip().lower()}"
    )


def paper_source_component_route_inventory(folder: Path) -> dict[str, dict[str, Any]]:
    """Return source-map component anchors as route-only source inventory.

    Components are not added to :func:`paper_statement_inventory`: doing so
    would incorrectly enlarge named-result coverage.  They are available only
    to v10 statement-route validation, where a formula row may honestly review
    one quoted source component rather than a parent theorem's full text.
    Invalid or unpinned component anchors are omitted, so a purported route to
    one fails closed as an unknown source item.
    """

    payload = paper_statement_map_payload(folder)
    raw_items = payload.get("items") if isinstance(payload, dict) else None
    if not isinstance(raw_items, dict):
        return {}

    component_inventory: dict[str, dict[str, Any]] = {}
    for raw_parent_key, raw_parent in raw_items.items():
        parent_key = str(raw_parent_key or "").strip()
        if not parent_key or not isinstance(raw_parent, dict):
            continue
        raw_components = raw_parent.get("source_components")
        if not isinstance(raw_components, list):
            continue
        source_kind = str(raw_parent.get("source_kind") or "").strip().lower()
        source_status = str(raw_parent.get("source_status") or "").strip()
        source_url = str(
            raw_parent.get("source_url") or payload.get("source_url") or ""
        ).strip()
        for raw_component in raw_components:
            if not isinstance(raw_component, dict):
                continue
            source_location = str(raw_component.get("source_location") or "").strip()
            anchors = raw_component.get("source_anchor_evidence")
            if not source_location or not isinstance(anchors, list):
                continue
            for raw_anchor in anchors:
                if not isinstance(raw_anchor, dict):
                    continue
                quoted_text = str(raw_anchor.get("quoted_text") or "")
                anchor_sha256 = str(raw_anchor.get("quoted_text_sha256") or "").strip().lower()
                if (
                    not quoted_text.strip()
                    or not SOURCE_ARTIFACT_SHA256_RE.fullmatch(anchor_sha256)
                    or hashlib.sha256(quoted_text.encode("utf-8")).hexdigest()
                    != anchor_sha256
                ):
                    continue
                statement = normalize_statement(quoted_text)
                if not statement:
                    continue
                key = source_component_route_key(parent_key, anchor_sha256)
                # Duplicate quoted bytes within the same parent describe the
                # same component route.  Do not guess between inconsistent
                # locators; preserving the first one is safe only when it is
                # exactly identical.
                existing = component_inventory.get(key)
                if existing is not None:
                    if (
                        existing.get("source_location") != source_location
                        or existing.get("statement") != statement
                    ):
                        component_inventory.pop(key, None)
                    continue
                component_inventory[key] = {
                    "statement": statement,
                    "statement_sha256": statement_digest(statement),
                    "source_location": source_location,
                    "source_kind": source_kind,
                    "source_status": source_status,
                    "source_url": source_url,
                    "source_component_of": parent_key,
                    "source_component_label": str(
                        raw_component.get("component") or ""
                    ).strip(),
                    "source_component_anchor_sha256": anchor_sha256,
                    "source_anchor_evidence": [raw_anchor],
                }
    return component_inventory


def source_definition_component_route_key(
    source_item_key: str,
    semantic_clause_sha256: str,
    source_anchor_sha256: str,
) -> str:
    """Return a navigation key for one semantically identified definition clause.

    The parent key is only a lookup handle.  Validation and reuse bind the route
    to the clause digest, exact source-anchor identity, parent statement
    digest, and the complete partition digest; no Lean declaration name
    participates.
    """

    return (
        f"{source_item_key}::source-definition-clause::"
        f"{semantic_clause_sha256.strip().lower()}::"
        f"{source_anchor_sha256.strip().lower()}"
    )


def _definition_partition_digest(value: object) -> str:
    return hashlib.sha256(
        json.dumps(
            value,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    ).hexdigest()


def _definition_component_anchor_identity(
    anchors: list[dict[str, Any]],
) -> str:
    """Return a stable identity for one component's exact source anchors.

    Preserve the historical single-quote identity so existing valid routes do
    not churn.  A clause supported by discontiguous source spans instead gets
    a domain-separated digest of the canonical anchor set.  Literal quote
    bytes enter through their individual SHA-256 values; paths and line ranges
    prevent equal text at different source locations from sharing an identity.
    """

    if len(anchors) == 1:
        return str(anchors[0]["quoted_text_sha256"])
    return _definition_partition_digest(
        {
            "schema": 1,
            "kind": "source_definition_component_anchor_set",
            "anchors": [
                {
                    "path": anchor["path"],
                    "line_start": anchor["line_start"],
                    "line_end": anchor["line_end"],
                    "quoted_text_sha256": anchor["quoted_text_sha256"],
                }
                for anchor in anchors
            ],
        }
    )


def source_definition_partition_record(
    source_item: Mapping[str, Any],
) -> tuple[dict[str, Any] | None, list[str]]:
    """Validate and canonicalize an opt-in semantic definition partition.

    A quoted paragraph can state several independent clauses.  Quote identity
    alone therefore cannot identify a component.  Each component is bound to
    both an auditor-written semantic clause digest and exact quoted bytes, while
    the parent record certifies that the clauses are a complete, nonoverlapping
    partition of the whole source definition.
    """

    raw = source_item.get(SOURCE_DEFINITION_PARTITION_FIELD)
    if raw is None:
        return None, []
    if not isinstance(raw, Mapping):
        return None, [f"{SOURCE_DEFINITION_PARTITION_FIELD} must be an object"]
    if _source_item_is_corrected_target(dict(source_item)):
        return None, [
            f"{SOURCE_DEFINITION_PARTITION_FIELD} cannot replace an approved "
            "corrected-target route"
        ]

    required_fields = {
        "schema",
        "source_statement_sha256",
        "semantic_relation",
        "complete",
        "components_semantically_disjoint",
        "completeness_basis",
        "nonoverlap_basis",
        "components",
    }
    errors: list[str] = []
    if set(raw) != required_fields:
        errors.append(
            f"{SOURCE_DEFINITION_PARTITION_FIELD} must contain exactly "
            + ", ".join(sorted(required_fields))
        )
    if raw.get("schema") != SOURCE_DEFINITION_PARTITION_SCHEMA:
        errors.append(
            f"{SOURCE_DEFINITION_PARTITION_FIELD} schema must be "
            f"{SOURCE_DEFINITION_PARTITION_SCHEMA}"
        )

    parent_digest = str(source_item.get("statement_sha256") or "").strip().lower()
    recorded_parent_digest = str(
        raw.get("source_statement_sha256") or ""
    ).strip().lower()
    if (
        not SOURCE_ARTIFACT_SHA256_RE.fullmatch(parent_digest)
        or recorded_parent_digest != parent_digest
    ):
        errors.append(
            f"{SOURCE_DEFINITION_PARTITION_FIELD} has a stale parent source "
            "statement digest"
        )
    if (
        str(raw.get("semantic_relation") or "").strip().lower()
        != SOURCE_DEFINITION_PARTITION_RELATION
    ):
        errors.append(
            f"{SOURCE_DEFINITION_PARTITION_FIELD} has an invalid semantic_relation"
        )
    if raw.get("complete") is not True:
        errors.append(
            f"{SOURCE_DEFINITION_PARTITION_FIELD} must certify complete=true"
        )
    if raw.get("components_semantically_disjoint") is not True:
        errors.append(
            f"{SOURCE_DEFINITION_PARTITION_FIELD} must certify "
            "components_semantically_disjoint=true"
        )
    for field in ("completeness_basis", "nonoverlap_basis"):
        basis = str(raw.get(field) or "").strip()
        if len(basis) < 60 or NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(basis):
            errors.append(
                f"{SOURCE_DEFINITION_PARTITION_FIELD} lacks substantive {field}"
            )

    raw_components = raw.get("components")
    if not isinstance(raw_components, list) or len(raw_components) < 2:
        errors.append(
            f"{SOURCE_DEFINITION_PARTITION_FIELD} components must contain at "
            "least two semantic clauses"
        )
        raw_components = []

    component_fields = {
        "semantic_clause",
        "semantic_clause_sha256",
        "source_location",
        "source_anchor_evidence",
    }
    raw_parent_convention_ids = source_item.get("model_convention_ids")
    parent_convention_ids: list[str] = []
    if "model_convention_ids" in source_item:
        if not isinstance(raw_parent_convention_ids, list):
            errors.append("partition parent model_convention_ids must be a nonempty list")
        else:
            parent_convention_ids = [
                value.strip()
                for value in raw_parent_convention_ids
                if isinstance(value, str) and value.strip()
            ]
            if (
                not parent_convention_ids
                or len(parent_convention_ids) != len(raw_parent_convention_ids)
                or len(set(parent_convention_ids)) != len(parent_convention_ids)
            ):
                errors.append(
                    "partition parent model_convention_ids must be a nonempty "
                    "list of unique strings"
                )
                parent_convention_ids = []
    scoped_component_fields = component_fields | {
        "source_status",
        "model_convention_ids",
    }
    parent_has_conventions = bool(parent_convention_ids)
    anchor_fields = {
        "path",
        "line_start",
        "line_end",
        "quoted_text",
        "quoted_text_sha256",
    }
    canonical_components: list[dict[str, Any]] = []
    seen_clause_digests: set[str] = set()
    seen_pairs: set[tuple[str, str]] = set()
    for index, component in enumerate(raw_components):
        label = f"{SOURCE_DEFINITION_PARTITION_FIELD} components[{index}]"
        if not isinstance(component, Mapping):
            errors.append(f"{label} must be an object")
            continue
        expected_component_fields = (
            component_fields | {"source_status"}
            if parent_has_conventions
            else component_fields
        )
        allowed_component_fields = (
            scoped_component_fields
            if parent_has_conventions
            else component_fields
        )
        if (
            not expected_component_fields <= set(component)
            or not set(component) <= allowed_component_fields
        ):
            errors.append(
                f"{label} must contain "
                + (
                    "explicit component convention scope fields"
                    if parent_has_conventions
                    else "exactly " + ", ".join(sorted(component_fields))
                )
            )
        component_status = str(component.get("source_status") or "").strip().lower()
        component_convention_ids: list[str] = []
        if parent_has_conventions:
            raw_component_ids = component.get("model_convention_ids")
            if component_status == SOURCE_DEFINITION_COMPONENT_EXACT_STATUS:
                if "model_convention_ids" in component:
                    errors.append(
                        f"{label} exact scope must omit model_convention_ids"
                    )
            elif component_status in SOURCE_DEFINITION_COMPONENT_CONVENTION_STATUSES:
                if not isinstance(raw_component_ids, list):
                    errors.append(
                        f"{label} convention scope requires nonempty model_convention_ids"
                    )
                else:
                    component_convention_ids = [
                        value.strip()
                        for value in raw_component_ids
                        if isinstance(value, str) and value.strip()
                    ]
                    if (
                        not component_convention_ids
                        or len(component_convention_ids) != len(raw_component_ids)
                        or len(set(component_convention_ids))
                        != len(component_convention_ids)
                    ):
                        errors.append(
                            f"{label} convention scope requires a nonempty list "
                            "of unique model_convention_ids"
                        )
                        component_convention_ids = []
                    extras = set(component_convention_ids) - set(
                        parent_convention_ids
                    )
                    if extras:
                        errors.append(
                            f"{label} cites convention IDs absent from its parent: "
                            + ", ".join(sorted(extras))
                        )
            else:
                errors.append(
                    f"{label} has invalid explicit source_status for a "
                    "convention-scoped partition"
                )
        semantic_clause = normalize_statement(
            str(component.get("semantic_clause") or "")
        )
        clause_digest = str(
            component.get("semantic_clause_sha256") or ""
        ).strip().lower()
        if not semantic_clause or clause_digest != statement_digest(semantic_clause):
            errors.append(f"{label} has a stale semantic_clause_sha256")
        source_location = str(component.get("source_location") or "").strip()
        if not source_location:
            errors.append(f"{label} has no source_location")
        location_anchors = [
            {
                "path": match.group("path"),
                "line_start": int(match.group("start")),
                "line_end": int(match.group("end") or match.group("start")),
            }
            for match in SOURCE_FILE_LINE_ANCHOR_RE.finditer(source_location)
        ]
        location_keys = [
            (anchor["path"], anchor["line_start"], anchor["line_end"])
            for anchor in location_anchors
        ]
        if not location_anchors:
            errors.append(f"{label} source_location has no exact file:line anchor")
        elif len(set(location_keys)) != len(location_keys):
            errors.append(f"{label} source_location duplicates a source anchor")
        anchors = component.get("source_anchor_evidence")
        if not isinstance(anchors, list) or not anchors:
            errors.append(f"{label} must contain a nonempty pinned source-quote list")
            continue

        canonical_anchors: list[dict[str, Any]] = []
        matched_locations: set[int] = set()
        for anchor_index, anchor in enumerate(anchors):
            anchor_label = f"{label} source_anchor_evidence[{anchor_index}]"
            if not isinstance(anchor, Mapping):
                errors.append(f"{anchor_label} must be an object")
                continue
            if set(anchor) != anchor_fields:
                errors.append(
                    f"{anchor_label} must contain exactly "
                    + ", ".join(sorted(anchor_fields))
                )
            path = str(anchor.get("path") or "").strip()
            raw_line_start = anchor.get("line_start")
            raw_line_end = anchor.get("line_end")
            valid_lines = (
                isinstance(raw_line_start, int)
                and not isinstance(raw_line_start, bool)
                and isinstance(raw_line_end, int)
                and not isinstance(raw_line_end, bool)
            )
            line_start = raw_line_start if valid_lines else 0
            line_end = raw_line_end if valid_lines else -1
            quote = str(anchor.get("quoted_text") or "")
            quote_digest = str(
                anchor.get("quoted_text_sha256") or ""
            ).strip().lower()
            if not path or line_start <= 0 or line_end < line_start:
                errors.append(
                    f"{anchor_label} has an invalid path or line range"
                )
            if (
                not quote
                or not SOURCE_ARTIFACT_SHA256_RE.fullmatch(quote_digest)
                or hashlib.sha256(quote.encode("utf-8")).hexdigest()
                != quote_digest
            ):
                errors.append(f"{anchor_label} has a stale quoted_text_sha256")

            matching_locations = [
                location_index
                for location_index, location_anchor in enumerate(location_anchors)
                if _source_anchor_paths_match(path, location_anchor["path"])
                and line_start == location_anchor["line_start"]
                and line_end == location_anchor["line_end"]
            ]
            if len(matching_locations) != 1:
                errors.append(
                    f"{anchor_label} does not match exactly one declared source anchor"
                )
                continue
            location_index = matching_locations[0]
            if location_index in matched_locations:
                errors.append(f"{anchor_label} duplicates a declared source anchor")
                continue
            matched_locations.add(location_index)
            declared_anchor = location_anchors[location_index]
            canonical_anchors.append(
                {
                    "path": declared_anchor["path"],
                    "line_start": line_start,
                    "line_end": line_end,
                    "quoted_text": quote,
                    "quoted_text_sha256": quote_digest,
                }
            )

        if len(matched_locations) != len(location_anchors):
            errors.append(
                f"{label} must provide exactly one pinned quote for every "
                "declared source anchor"
            )
        canonical_anchors.sort(
            key=lambda anchor: (
                anchor["path"],
                anchor["line_start"],
                anchor["line_end"],
                anchor["quoted_text_sha256"],
            )
        )
        anchor_identity = (
            _definition_component_anchor_identity(canonical_anchors)
            if canonical_anchors
            else ""
        )
        pair = (clause_digest, anchor_identity)
        if clause_digest in seen_clause_digests:
            errors.append(f"{label} duplicates a semantic clause digest")
        if pair in seen_pairs:
            errors.append(
                f"{label} duplicates a semantic-clause/source-anchor pair"
            )
        seen_clause_digests.add(clause_digest)
        seen_pairs.add(pair)
        canonical_component = {
            "semantic_clause": semantic_clause,
            "semantic_clause_sha256": clause_digest,
            "source_location": source_location,
            "source_anchor_sha256": anchor_identity,
            "source_anchor_evidence": canonical_anchors,
        }
        if parent_has_conventions:
            canonical_component["source_status"] = component_status
            if component_convention_ids:
                canonical_component["model_convention_ids"] = sorted(
                    component_convention_ids
                )
        canonical_components.append(canonical_component)

    if parent_has_conventions:
        component_convention_union = {
            convention_id
            for component in canonical_components
            for convention_id in component.get("model_convention_ids", [])
        }
        if component_convention_union != set(parent_convention_ids):
            errors.append(
                "partition component convention scopes do not exactly cover "
                "the parent model_convention_ids"
            )

    if errors:
        return None, errors

    canonical_components.sort(
        key=lambda component: (
            component["semantic_clause_sha256"],
            component["source_anchor_sha256"],
            component["source_location"],
        )
    )
    partition_semantics = {
        "schema": SOURCE_DEFINITION_PARTITION_SCHEMA,
        "source_statement_sha256": parent_digest,
        "semantic_relation": SOURCE_DEFINITION_PARTITION_RELATION,
        "complete": True,
        "components_semantically_disjoint": True,
        "completeness_basis": normalize_statement(
            str(raw.get("completeness_basis") or "")
        ),
        "nonoverlap_basis": normalize_statement(
            str(raw.get("nonoverlap_basis") or "")
        ),
        "components": [
            {
                "semantic_clause": component["semantic_clause"],
                "semantic_clause_sha256": component["semantic_clause_sha256"],
                "source_location": component["source_location"],
                "source_anchor_sha256": component["source_anchor_sha256"],
            }
            for component in canonical_components
        ],
    }
    partition_digest = _definition_partition_digest(partition_semantics)
    for component in canonical_components:
        component["source_definition_component_sha256"] = (
            _definition_partition_digest(
                {
                    "schema": 1,
                    "source_statement_sha256": parent_digest,
                    "source_definition_partition_sha256": partition_digest,
                    "semantic_clause_sha256": component[
                        "semantic_clause_sha256"
                    ],
                    "source_anchor_sha256": component["source_anchor_sha256"],
                    "source_location": component["source_location"],
                    **(
                        {
                            "source_status": component["source_status"],
                            "model_convention_ids": component.get(
                                "model_convention_ids", []
                            ),
                        }
                        if parent_has_conventions
                        else {}
                    ),
                }
            )
        )
    return {
        **partition_semantics,
        "source_definition_partition_sha256": partition_digest,
        "components": canonical_components,
    }, []


def paper_source_definition_component_route_inventory(
    folder: Path,
) -> dict[str, dict[str, Any]]:
    """Return valid definition-partition clauses as route-only inventory."""

    source_inventory = paper_statement_inventory(folder)
    component_inventory: dict[str, dict[str, Any]] = {}
    for parent_key, source_item in source_inventory.items():
        if (
            str(source_item.get("source_kind") or "").strip().lower()
            not in SOURCE_DEFINITION_SEMANTIC_KINDS
        ):
            continue
        partition, errors = source_definition_partition_record(source_item)
        if partition is None or errors:
            continue
        partition_digest = partition["source_definition_partition_sha256"]
        for component in partition["components"]:
            clause_digest = component["semantic_clause_sha256"]
            anchor_digest = component["source_anchor_sha256"]
            key = source_definition_component_route_key(
                parent_key, clause_digest, anchor_digest
            )
            component_inventory[key] = {
                "statement": component["semantic_clause"],
                "statement_sha256": clause_digest,
                "source_location": component["source_location"],
                "source_kind": str(source_item.get("source_kind") or "")
                .strip()
                .lower(),
                "source_status": str(
                    component.get("source_status")
                    or source_item.get("source_status")
                    or ""
                ).strip(),
                "source_url": str(source_item.get("source_url") or "").strip(),
                "source_component_of": parent_key,
                "source_definition_component": True,
                "source_component_anchor_sha256": anchor_digest,
                "source_definition_partition_sha256": partition_digest,
                "source_definition_component_sha256": component[
                    "source_definition_component_sha256"
                ],
                "source_anchor_evidence": component["source_anchor_evidence"],
            }
            if component.get("model_convention_ids"):
                component_inventory[key]["model_convention_ids"] = list(
                    component["model_convention_ids"]
                )
    return component_inventory


def review_source_component_statement_routes(
    folder: Path,
) -> dict[str, dict[str, Any]]:
    """Return explicit row-to-component display bindings for a review surface.

    The row name merely chooses which dashboard display receives a source
    excerpt.  The selected excerpt itself must resolve through the exact
    parent-item key, quoted-byte digest, and source locator held in the source
    map.  Thus a declaration rename or a misleading function name cannot
    manufacture a source comparison.
    """

    payload = load_review_slice_payload(folder)
    raw_routes = payload.get("source_component_statement_routes")
    if not isinstance(raw_routes, list):
        return {}
    components = paper_source_component_route_inventory(folder)
    definition_components = paper_source_definition_component_route_inventory(folder)
    routes: dict[str, dict[str, Any]] = {}
    for raw_route in raw_routes:
        if not isinstance(raw_route, dict):
            continue
        row = str(raw_route.get("row") or "").strip()
        parent = str(raw_route.get("source_item") or "").strip()
        anchor_sha256 = str(
            raw_route.get("source_component_anchor_sha256") or ""
        ).strip().lower()
        clause_sha256 = str(
            raw_route.get("semantic_clause_sha256") or ""
        ).strip().lower()
        source_location = str(raw_route.get("source_location") or "").strip()
        if (
            not row
            or row in routes
            or not parent
            or not SOURCE_ARTIFACT_SHA256_RE.fullmatch(anchor_sha256)
            or not source_location
        ):
            continue
        if clause_sha256:
            component = definition_components.get(
                source_definition_component_route_key(
                    parent, clause_sha256, anchor_sha256
                )
            )
            if component is not None and any(
                str(raw_route.get(field) or "").strip().lower()
                != str(component.get(field) or "").strip().lower()
                for field in (
                    "source_definition_partition_sha256",
                    "source_definition_component_sha256",
                )
            ):
                component = None
        else:
            component = components.get(
                source_component_route_key(parent, anchor_sha256)
            )
        if component is None or component.get("source_location") != source_location:
            continue
        routes[row] = component
    return routes


def resolved_review_source_component_statement_routes(
    folder: Path,
    parsed_rows: Iterable[
        tuple[str, str, str, str, str | None, int, Path]
    ],
    *,
    component_routes: Mapping[str, dict[str, Any]] | None = None,
) -> dict[str, dict[str, Any]]:
    """Resolve component display navigation to exact full declarations.

    A short row name is accepted only when it identifies one reviewed
    declaration.  Qualified row identities bind directly.  The resulting map
    is keyed solely by full declaration navigation, so namespace collisions
    cannot change which semantic source clause is displayed.
    """

    rows = [row for row in parsed_rows if row[0] in REVIEW_DECL_KINDS]
    raw_routes = (
        review_source_component_statement_routes(folder)
        if component_routes is None
        else component_routes
    )
    resolved: dict[str, dict[str, Any]] = {}
    blocked: set[str] = set()
    for navigation, component in raw_routes.items():
        exact = [row for row in rows if row[2] == navigation]
        candidates = exact if exact else [row for row in rows if row[1] == navigation]
        if len(candidates) != 1:
            continue
        full_name = candidates[0][2]
        if full_name in blocked:
            continue
        previous = resolved.get(full_name)
        if previous is not None and previous != component:
            resolved.pop(full_name, None)
            blocked.add(full_name)
            continue
        resolved[full_name] = component
    return resolved


def resolved_direct_source_statement_routes(
    folder: Path,
    parsed_rows: Iterable[
        tuple[str, str, str, str, str | None, int, Path]
    ],
) -> dict[str, str]:
    """Resolve exact source-map display routes to reviewed declarations.

    This is deliberately separate from the tolerant display-key lookup used
    for legacy navigation.  When a map item explicitly names a direct Lean
    endpoint, its canonical source statement is the semantic-comparison
    target for that exact reviewed declaration.  The resolution starts from
    the map's direct-route field and the parsed declaration's qualified name;
    neither a declaration's spelling nor a map-item key is semantic evidence.

    A legacy unqualified route is accepted only when it resolves to exactly
    one current reviewed declaration.  Conflicting direct map statements for
    one declaration are left unresolved rather than letting map iteration
    order choose a paper statement.
    """

    rows = [row for row in parsed_rows if row[0] in REVIEW_DECL_KINDS]
    direct_routes: dict[str, str] = {}
    conflicts: set[str] = set()
    for source_item in paper_statement_inventory(folder).values():
        if not isinstance(source_item, dict):
            continue
        statement, _statement_sha256 = _source_item_coverage_statement(source_item)
        if not statement:
            continue
        for navigation in source_item_direct_coverage_declarations(source_item):
            exact = [row for row in rows if row[2] == navigation]
            candidates = exact if exact else [row for row in rows if row[1] == navigation]
            if len(candidates) != 1:
                continue
            full_name = candidates[0][2]
            if full_name in conflicts:
                continue
            previous = direct_routes.get(full_name)
            if previous is not None and previous != statement:
                direct_routes.pop(full_name, None)
                conflicts.add(full_name)
                continue
            direct_routes[full_name] = statement
    return direct_routes


def paper_statement_for_review_row(
    paper_statements: Mapping[str, str],
    component_routes: Mapping[str, Mapping[str, Any]],
    name: str,
    full_name: str,
    *,
    component_navigation_keys: Iterable[str] = (),
    direct_statement_routes: Mapping[str, str] | None = None,
) -> str:
    """Select an explicit direct route before component and legacy lookup."""

    if direct_statement_routes is not None:
        statement = str(direct_statement_routes.get(full_name) or "").strip()
        if statement:
            return statement

    component = component_routes.get(full_name)
    if component is not None:
        statement = str(component.get("statement") or "").strip()
        if statement:
            return statement
    excluded = set(component_navigation_keys)
    for candidate in paper_statement_candidate_keys(name, full_name):
        if candidate in excluded:
            continue
        if candidate and candidate in paper_statements:
            return paper_statements[candidate]
    return ""


def _source_artifact_identity(payload: object) -> tuple[str, str]:
    """Return the canonical source bytes identity declared by a source map."""

    if not isinstance(payload, dict):
        return "", ""
    path = str(payload.get("source_artifact_path") or "").strip()
    digest = str(payload.get("source_artifact_sha256") or "").strip().lower()
    if not path or not SOURCE_ARTIFACT_SHA256_RE.fullmatch(digest):
        return "", ""
    return path, digest


def _source_artifact_identity_is_declared(payload: object) -> bool:
    """Whether a map explicitly attempts to pin a canonical source artifact.

    This is intentionally distinct from :func:`_source_artifact_identity`.
    The latter returns only a complete, valid identity for equality checks;
    this helper preserves the fact that a malformed or partial pin was
    supplied.  A sidecar that also claims artifact-level freshness must fail
    closed in that case rather than treating the malformed map as an older map
    that never opted into artifact pinning.
    """

    return isinstance(payload, dict) and (
        "source_artifact_path" in payload
        or "source_artifact_sha256" in payload
    )


def _coverage_audit_source_artifact_is_current(
    audit: object, statement_map_payload: object
) -> bool:
    """Whether a coverage sidecar was recorded against current source bytes.

    This is intentionally independent of semantic item digests.  Those digests
    omit artifact-wide hashes so unrelated source edits can reuse an unchanged
    item, but such reuse still requires a current byte-verified anchor whenever
    this aggregate source identity differs or is absent.
    """

    current_path, current_digest = _source_artifact_identity(statement_map_payload)
    if not isinstance(audit, dict) or not current_path or not current_digest:
        return False
    recorded_path = str(audit.get("source_artifact_path") or "").strip()
    recorded_digest = str(audit.get("source_artifact_sha256") or "").strip().lower()
    return recorded_path == current_path and recorded_digest == current_digest


def _coverage_audit_records_source_artifact_identity(audit: object) -> bool:
    """Whether a coverage sidecar opted into artifact-level freshness pins.

    Legacy sidecars predate these optional top-level fields.  They remain
    governed by their aggregate inventory digest until migrated to item-level
    source identities.  Once a sidecar supplies either artifact field, a
    partial or stale identity is evidence of a changed source and must fail
    closed rather than silently falling back to the legacy rule.
    """

    if not isinstance(audit, dict):
        return False
    return bool(
        str(audit.get("source_artifact_path") or "").strip()
        or str(audit.get("source_artifact_sha256") or "").strip()
    )


def paper_source_map_structural_errors(folder: Path) -> list[str]:
    """Validate raw inventory shape before any safe prompt projection.

    ``paper_statement_inventory`` necessarily skips unreadable objects while
    constructing text prompts.  Treating that projection as the audit input
    would let a malformed source row vanish from ordinary named-theory scope.
    Keep this raw-map lane independent of selected coverage items.
    """

    payload = paper_statement_map_payload(folder)
    if not payload:
        return []
    if "items" not in payload:
        return ["source map `items` must be an object"]
    errors = source_map_structural_errors(
        payload.get("items"),
        declared_environment_kinds=source_named_result_environment_kinds_from_map(
            payload
        ),
    )
    raw_items = payload.get("items")
    source_inventory = paper_statement_inventory(folder)
    if isinstance(raw_items, Mapping):
        for raw_key, raw_item in raw_items.items():
            if (
                not isinstance(raw_item, Mapping)
                or SOURCE_DEFINITION_PARTITION_FIELD not in raw_item
            ):
                continue
            key = str(raw_key or "").strip()
            source_item = source_inventory.get(key)
            if source_item is None:
                errors.append(
                    f"{key or '<unnamed>'}: {SOURCE_DEFINITION_PARTITION_FIELD} "
                    "cannot bind to a canonical source item"
                )
                continue
            if (
                str(source_item.get("source_kind") or "").strip().lower()
                not in SOURCE_DEFINITION_SEMANTIC_KINDS
            ):
                errors.append(
                    f"{key}: {SOURCE_DEFINITION_PARTITION_FIELD} is allowed only "
                    "on a source definition"
                )
                continue
            _partition, partition_errors = source_definition_partition_record(
                source_item
            )
            errors.extend(f"{key}: {error}" for error in partition_errors)
    errors.extend(
        "source_prose_definition_inventory: " + error
        for error in source_prose_definition_inventory_errors(
            folder,
            payload,
            repository_root=ROOT,
            file_bytes_override=_dashboard_file_bytes_override(),
        )
    )
    # The dashboard consumes the transcript only after the optional scanned
    # source companion proves that the top-level canonical text pin and visual
    # PDF provenance agree.  This keeps its inexpensive precheck aligned with
    # the release integrity gate without using map keys or Lean routes.
    errors.extend(
        f"source_text_companion: {issue.message}"
        for issue in source_text_companion_validation_issues(
            folder,
            payload,
            repository_root=ROOT,
            require_source_bytes=True,
            file_bytes_override=_dashboard_file_bytes_override(),
        )
    )
    errors.extend(
        f"source_archive_surface: {issue.message}"
        for issue in source_archive_surface_validation_issues(
            folder,
            payload,
            repository_root=ROOT,
            require_source_bytes=True,
            file_bytes_override=_dashboard_file_bytes_override(),
        )
    )
    return sorted(set(errors))


def paper_source_coverage_mode(folder: Path) -> tuple[str, str]:
    """Return the source-inventory coverage mode and any configuration error."""

    return source_coverage_mode_from_map(paper_statement_map_payload(folder))


def paper_coverage_inventory(
    folder: Path,
) -> tuple[dict[str, dict[str, Any]], dict[str, dict[str, Any]], str, str]:
    """Return full and selected inventories for the configured coverage mode.

    Ordinary closeout reviews named source-level theory only.  The full
    inventory is retained for an explicit deep-paper audit, so switching modes
    never loses source material or relies on a declaration/function name.
    """

    full_inventory = paper_statement_inventory(folder)
    statement_map = paper_statement_map_payload(folder)
    mode, mode_error = source_coverage_mode_from_map(statement_map)
    raw_map_items = statement_map.get("items") if isinstance(statement_map, dict) else None
    # A valid presentation alias is independently byte-pinned and reconciled
    # elsewhere, but it deliberately has no direct Lean route.  Keep it out
    # of proof coverage after that reconciliation so a repeated proof
    # presentation cannot double-count a paper-facing result.  Malformed
    # alias metadata is not trusted for this exclusion; structural validation
    # keeps it visible and blocks closeout instead.
    presentation_aliases, _presentation_alias_errors = source_presentation_aliases(
        raw_map_items
    )
    selected_inventory = filter_source_inventory_for_coverage(
        full_inventory,
        mode,
        declared_environment_kinds=source_named_result_environment_kinds_from_map(
            statement_map
        ),
    )
    # Keep the established source-presentation selector for compatible maps,
    # then add the stricter source-index lane.  The latter is deliberately
    # independent of a row's summary text, source_kind, map key, or Lean route:
    # a current byte-pinned anchor to exactly one indexed presentation is enough
    # to include a source item whose prose summary omitted its printed heading.
    for item_id in source_index_byte_pinned_anchor_item_ids(
        folder,
        statement_map,
        mode,
        repository_root=ROOT,
        file_bytes_override=_dashboard_file_bytes_override(),
    ):
        item = full_inventory.get(item_id)
        if item is not None and item_id not in presentation_aliases:
            selected_inventory[item_id] = item
    # Corrections and explicit scope dispositions are source-facing obligations
    # in their own right. Preserve them even when neither ordinary selector
    # applies; their dedicated validators still enforce their anchor/approval
    # contracts.
    for item_id, item in full_inventory.items():
        if source_item_has_explicit_nonordinary_obligation(item):
            selected_inventory[item_id] = item
    return full_inventory, selected_inventory, mode, mode_error


def llm_statement_source_routes_required(folder: Path) -> bool:
    """Return whether a paper opted into exact source-route pins for v10 rows.

    This remains opt-in so legacy sidecars can be refreshed deliberately.  New
    paper scaffolds enable it, and an enabled paper fails closed when a row
    cannot identify the exact source statement(s) it compares.
    """

    status_path = folder / DEFAULT_PAPER_STATUS_FILE
    payload = _dashboard_json_payload(status_path)
    if not isinstance(payload, dict):
        return False
    review_surface = payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return False
    statement_review = review_surface.get("llm_statement_review")
    if not isinstance(statement_review, dict):
        return False
    return statement_review.get("require_explicit_source_routes") is True


DIRECT_EXPRESSION_SEMANTICS_REVIEW_VERSION = "v1"


def llm_direct_expression_semantics_review_required(folder: Path) -> bool:
    """Return whether a paper opts into the versioned formula-domain review.

    Definition and predicate-vocabulary endpoints have always required the
    source-definition semantic review whenever exact v10 source routes are
    enabled.  Formula-like endpoints are an additional review surface, so
    they require an explicit versioned paper policy instead of silently
    invalidating legacy receipt evidence.  This intentionally accepts only
    the literal current protocol version; truthy values and future versions
    must not opt a paper in by accident.
    """

    status_path = folder / DEFAULT_PAPER_STATUS_FILE
    payload = _dashboard_json_payload(status_path)
    if not isinstance(payload, dict):
        return False
    review_surface = payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return False
    statement_review = review_surface.get("llm_statement_review")
    if not isinstance(statement_review, dict):
        return False
    return (
        statement_review.get("require_direct_expression_semantics_review")
        == DIRECT_EXPRESSION_SEMANTICS_REVIEW_VERSION
    )


def direct_source_definition_route_keys(
    raw: Any,
    *,
    inventory: dict[str, dict[str, Any]],
    include_direct_expressions: bool = False,
) -> set[str]:
    """Return direct source routes needing totalization/domain review.

    Definitions and predicate vocabulary always use the legacy v10 gate.
    When the paper's versioned direct-expression policy is enabled, displayed
    formulas, equations, and algorithmic formulas join that same domain and
    totalization review.  This is a source-map semantic classification plus an
    explicit route kind; it intentionally does not inspect row, declaration,
    or function names.  ``source_route_pin_error`` independently verifies
    that each returned route has the exact source digest and conclusion binding
    before it can receive source credit.
    """

    if not isinstance(raw, dict):
        return set()
    routes = raw.get("source_routes")
    if not isinstance(routes, list):
        return set()
    keys: set[str] = set()
    for route in routes:
        if not isinstance(route, dict):
            continue
        source_item_key = str(route.get("source_item") or "").strip()
        source_item = inventory.get(source_item_key)
        if not isinstance(source_item, dict):
            continue
        source_kind = str(source_item.get("source_kind") or "").strip().lower()
        route_kind = str(route.get("route_kind") or "").strip().lower()
        whole_definition_route = route_kind in {
            "direct",
            CORRECTED_TARGET_ROUTE_KIND,
        }
        partition_component_route = (
            route_kind == "source_component"
            and source_item.get("source_definition_component") is True
        )
        semantic_kinds = (
            SOURCE_DIRECT_EXPRESSION_SEMANTIC_KINDS
            if include_direct_expressions
            else SOURCE_DEFINITION_SEMANTIC_KINDS
        )
        if source_kind in semantic_kinds and (
            whole_definition_route or partition_component_route
        ):
            keys.add(source_item_key)
    return keys


def source_route_pin_error(
    raw: Any,
    *,
    inventory: dict[str, dict[str, Any]],
    require_statement_target: bool = False,
) -> str:
    """Validate source-statement pins recorded by an enabled v10 statement row.

    The primary evidence is an exact map-statement digest, exact source
    locator, and a source-conclusion obligation carrying those same values.
    Curated declaration names may help an auditor find candidates, but they are
    not certification evidence and are deliberately not read here.  Production
    v10 consumers also require ``require_statement_target``: the judgment's
    nonempty paper-statement digest must be one of these exact source targets,
    and a ``matches`` judgment must use an equivalence-bearing route.  The
    optional structural-only mode is retained for low-level route-policy tests
    and support-route construction before a statement receipt exists.
    """

    if not isinstance(raw, dict):
        return "judgment is not an object"
    routes = raw.get("source_routes")
    if not isinstance(routes, list) or not routes:
        return "missing nonempty explicit `source_routes` list"
    source_obligations = raw.get("source_obligations")
    if not isinstance(source_obligations, list):
        return "missing source obligations for explicit source-route pins"

    lean_obligations = raw.get("lean_obligations")
    if not isinstance(lean_obligations, list):
        return "missing Lean obligations for explicit source-route pins"
    lean_kinds = {
        str(obligation.get("id") or "").strip(): str(
            obligation.get("kind") or ""
        ).strip().lower()
        for obligation in lean_obligations
        if isinstance(obligation, dict) and str(obligation.get("id") or "").strip()
    }
    conclusion_ids = {
        obligation_id
        for obligation_id, kind in lean_kinds.items()
        if kind == "conclusion"
    }
    if not conclusion_ids:
        return "source-route row has no Lean conclusion obligation"
    alignment = raw.get("obligation_alignment")
    if not isinstance(alignment, list):
        return "missing obligation alignment for explicit source-route pins"

    def exact_endpoint_binding(source_item_key: str, expected_digest: str, expected_location: str) -> bool:
        matching_ids = {
            str(obligation.get("id") or "").strip()
            for obligation in source_obligations
            if isinstance(obligation, dict)
            and str(obligation.get("kind") or "").strip().lower() == "conclusion"
            and str(obligation.get("source_item") or "").strip() == source_item_key
            and str(obligation.get("source_statement_sha256") or "").strip()
            == expected_digest
            and str(obligation.get("source_location") or "").strip()
            == expected_location
            and statement_digest(str(obligation.get("statement") or ""))
            == expected_digest
        }
        return bool(matching_ids) and any(
            isinstance(entry, dict)
            and str(entry.get("source_id") or "").strip() in matching_ids
            and str(entry.get("lean_id") or "").strip() in conclusion_ids
            and str(entry.get("relation") or "").strip().lower() == "equivalent"
            for entry in alignment
        )

    def scope_evidence_error(
        raw_route: dict[str, Any],
        source_item_key: str,
        *,
        require_conclusion: bool,
    ) -> str:
        scope = str(raw_route.get("source_support_scope") or "").strip()
        if len(scope) < 60 or NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(scope):
            return (
                f"source route `{source_item_key}` has no substantive "
                "source_support_scope"
            )
        evidence_ids = _normalize_string_list(raw_route.get("lean_evidence_ids"))
        if not evidence_ids:
            return f"source route `{source_item_key}` has no lean_evidence_ids"
        if any(evidence_id not in lean_kinds for evidence_id in evidence_ids):
            return f"source route `{source_item_key}` references unknown Lean evidence"
        if require_conclusion and not any(
            evidence_id in conclusion_ids for evidence_id in evidence_ids
        ):
            return (
                f"source route `{source_item_key}` has no Lean conclusion in "
                "lean_evidence_ids"
            )
        return ""

    seen_items: set[str] = set()
    route_kinds: dict[str, str] = {}
    source_target_routes: list[tuple[str, str, str, bool]] = []
    for raw_route in routes:
        if not isinstance(raw_route, dict):
            return "source route is not an object"
        source_item_key = str(raw_route.get("source_item") or "").strip()
        if not source_item_key:
            return "source route has no source_item"
        if source_item_key in seen_items:
            return f"source route duplicates `{source_item_key}`"
        seen_items.add(source_item_key)
        source_item = inventory.get(source_item_key)
        if source_item is None:
            return f"source route names unknown source item `{source_item_key}`"

        route_kind = str(raw_route.get("route_kind") or "").strip().lower()
        if route_kind not in SOURCE_ROUTE_KINDS:
            return f"source route `{source_item_key}` has invalid route_kind"
        is_definition_component = (
            source_item.get("source_definition_component") is True
        )
        if is_definition_component and route_kind != "source_component":
            return (
                f"definition-component route `{source_item_key}` must use "
                "source_component; a clause cannot masquerade as a whole-item route"
            )
        is_corrected_target = _source_item_is_corrected_target(source_item)
        target_error = (
            _source_item_corrected_target_metadata_error(source_item)
            if is_corrected_target
            else ""
        )
        if target_error:
            return f"source route `{source_item_key}` {target_error}"
        expected_statement, expected_digest = _source_item_coverage_statement(source_item)
        expected_location = _source_item_coverage_location(source_item)
        recorded_digest = str(raw_route.get("source_statement_sha256") or "").strip()
        recorded_location = str(raw_route.get("source_location") or "").strip()
        if not expected_statement or not expected_digest or not expected_location:
            return f"source route `{source_item_key}` has incomplete canonical source inventory"
        if is_corrected_target and route_kind != CORRECTED_TARGET_ROUTE_KIND:
            return (
                f"corrected-target source route `{source_item_key}` must use "
                "approved_corrected_target; an approved correction cannot be "
                "certified through a component, convention, proof-support, or "
                "archival direct route"
            )
        if recorded_digest != expected_digest:
            return f"source route `{source_item_key}` has a stale source statement digest"
        if recorded_location != expected_location:
            return f"source route `{source_item_key}` has a stale source location"

        route_kinds[source_item_key] = route_kind
        route_policy = source_item_effective_route_policy(source_item)
        relation = str(raw_route.get("semantic_relation") or "").strip().lower()
        endpoint_binding = exact_endpoint_binding(
            source_item_key,
            expected_digest,
            expected_location,
        )
        source_target_routes.append(
            (expected_digest, route_kind, relation, endpoint_binding)
        )

        if route_kind == CORRECTED_TARGET_ROUTE_KIND:
            if not is_corrected_target:
                return (
                    f"approved corrected-target route `{source_item_key}` does not name "
                    "a corrected_source_statement inventory item"
                )
            target = _source_item_corrected_target(source_item)
            assert target is not None
            archival_digest = str(source_item.get("statement_sha256") or "").strip()
            archival_location = _source_item_coverage_location(source_item)
            approval = target.get("approval")
            assert isinstance(approval, dict)
            expected_governing = _normalize_string_list(
                target.get("governing_defect_ids")
            )
            if relation != CORRECTED_TARGET_ROUTE_RELATION:
                return (
                    f"approved corrected-target route `{source_item_key}` has invalid "
                    "semantic_relation"
                )
            if str(raw.get("resolution") or "").strip().lower() != CORRECTED_TARGET_MATCH_RESOLUTION:
                return (
                    f"approved corrected-target route `{source_item_key}` requires "
                    "judgment resolution approved_corrected_target"
                )
            if str(raw_route.get("archival_statement_sha256") or "").strip().lower() != archival_digest:
                return (
                    f"approved corrected-target route `{source_item_key}` has a stale "
                    "archival statement digest"
                )
            if str(raw_route.get("archival_source_location") or "").strip() != archival_location:
                return (
                    f"approved corrected-target route `{source_item_key}` has a stale "
                    "archival source location"
                )
            if str(raw_route.get("corrected_target_sha256") or "").strip().lower() != corrected_target_digest(target):
                return (
                    f"approved corrected-target route `{source_item_key}` has a stale "
                    "corrected-target record digest"
                )
            if _normalize_string_list(raw_route.get("governing_defect_ids")) != expected_governing:
                return (
                    f"approved corrected-target route `{source_item_key}` lacks the "
                    "exact governing source-statement defect ids"
                )
            if raw_route.get("archival_equivalence_claimed") is not False:
                return (
                    f"approved corrected-target route `{source_item_key}` must set "
                    "archival_equivalence_claimed to false"
                )
            if str(raw_route.get("approval_artifact_sha256") or "").strip().lower() != str(
                approval.get("artifact_sha256") or ""
            ).strip().lower():
                return (
                    f"approved corrected-target route `{source_item_key}` has a stale "
                    "approval artifact digest"
                )
            if not endpoint_binding:
                return (
                    f"approved corrected-target route `{source_item_key}` has no exact "
                    "equivalent corrected-target conclusion binding"
                )
        elif route_kind == "direct":
            if route_policy["is_model_convention"]:
                return (
                    f"direct source route `{source_item_key}` is a model/assumption "
                    "convention rather than a source result"
                )
            if not route_policy["allows_direct_route"]:
                return (
                    f"direct source route `{source_item_key}` is quarantined or support-only"
                )
            if not endpoint_binding:
                return (
                    f"direct source route `{source_item_key}` has no exact equivalent "
                    "source-conclusion binding"
                )
        elif route_kind == "source_model_convention":
            if not route_policy["allows_source_model_convention_route"]:
                return (
                    f"source-model route `{source_item_key}` does not identify a "
                    "source model convention"
                )
            if relation not in SOURCE_MODEL_ROUTE_RELATIONS:
                return f"source-model route `{source_item_key}` has invalid semantic_relation"
            scope_error = scope_evidence_error(
                raw_route, source_item_key, require_conclusion=False
            )
            if scope_error:
                return scope_error
            if relation == "equivalent_model_convention" and not endpoint_binding:
                return (
                    f"equivalent source-model route `{source_item_key}` has no exact "
                    "equivalent source-conclusion binding"
                )
        elif route_kind == "source_component":
            if not route_policy["allows_source_component_route"]:
                return (
                    f"source-component route `{source_item_key}` is not an ordinary "
                    "source component"
                )
            if relation not in SOURCE_COMPONENT_ROUTE_RELATIONS:
                return f"source-component route `{source_item_key}` has invalid semantic_relation"
            expected_component_anchor = str(
                source_item.get("source_component_anchor_sha256") or ""
            ).strip().lower()
            if expected_component_anchor and str(
                raw_route.get("source_component_anchor_sha256") or ""
            ).strip().lower() != expected_component_anchor:
                return (
                    f"source-component route `{source_item_key}` has a stale "
                    "source_component_anchor_sha256"
                )
            if is_definition_component:
                if relation != SOURCE_DEFINITION_COMPONENT_RELATION:
                    return (
                        f"definition-component route `{source_item_key}` must use "
                        f"{SOURCE_DEFINITION_COMPONENT_RELATION}"
                    )
                for field in (
                    "source_definition_partition_sha256",
                    "source_definition_component_sha256",
                ):
                    if str(raw_route.get(field) or "").strip().lower() != str(
                        source_item.get(field) or ""
                    ).strip().lower():
                        return (
                            f"definition-component route `{source_item_key}` has "
                            f"a stale {field}"
                        )
                if not endpoint_binding:
                    return (
                        f"definition-component route `{source_item_key}` has no "
                        "exact equivalent clause-conclusion binding"
                    )
            elif relation == "equivalent_source_component" and not endpoint_binding:
                return (
                    f"equivalent source-component route `{source_item_key}` has no "
                    "exact equivalent source-conclusion binding"
                )
            scope_error = scope_evidence_error(
                raw_route, source_item_key, require_conclusion=True
            )
            if scope_error:
                return scope_error
        elif route_kind == "defect_or_remark_support":
            if not route_policy["allows_defect_or_remark_support_route"]:
                return (
                    f"defect/remark support route `{source_item_key}` is not a "
                    "quarantined defect or support-only source item"
                )
            if relation not in SOURCE_DEFECT_ROUTE_RELATIONS:
                return f"defect/remark route `{source_item_key}` has invalid semantic_relation"
            scope_error = scope_evidence_error(
                raw_route, source_item_key, require_conclusion=True
            )
            if scope_error:
                return scope_error
            defect_ids = _normalize_string_list(source_item.get("source_defect_ids"))
            defect_id = str(raw_route.get("defect_id") or "").strip()
            if defect_ids and defect_id not in defect_ids:
                return (
                    f"defect/remark route `{source_item_key}` lacks its exact "
                    "source defect id"
                )
        else:  # proof_support
            if relation != "proof_component_support":
                return f"proof-support route `{source_item_key}` has invalid semantic_relation"
            scope_error = scope_evidence_error(
                raw_route, source_item_key, require_conclusion=True
            )
            if scope_error:
                return scope_error

    # A model convention can contextualize a row, but it cannot replace a
    # source result that the row's own semantic obligation ledger identifies
    # as an endpoint.  This deliberately reads source-item pins from the
    # ledger rather than declaration names: renaming Lean code must not change
    # whether a theorem endpoint is required to have a direct source route.
    endpoint_source_items: set[str] = set()
    for obligation in source_obligations:
        if not isinstance(obligation, dict):
            continue
        if str(obligation.get("kind") or "").strip().lower() != "conclusion":
            continue
        source_item_key = str(obligation.get("source_item") or "").strip()
        source_item = inventory.get(source_item_key)
        if source_item is None:
            continue
        if source_item.get("source_definition_component") is True:
            # This obligation is a certified clause in a complete partition,
            # not a claim that the row alone realizes the whole definition.
            continue
        if str(source_item.get("source_kind") or "").strip().lower() not in (
            SOURCE_RESULT_KINDS | SOURCE_DEFINITION_SEMANTIC_KINDS
        ):
            continue
        if not source_item_effective_route_policy(source_item)[
            "direct_source_endpoint_required"
        ]:
            continue
        # A source item can also anchor a smaller proof component.  It is a
        # theorem endpoint only when the ledger says this exact audited target,
        # rather than merely citing the proposition's location.  Corrected
        # rows deliberately compare their approved target, never the archival
        # statement retained in the source inventory.
        _endpoint_statement, endpoint_digest = _source_item_coverage_statement(
            source_item
        )
        if not (
            str(obligation.get("source_statement_sha256") or "").strip()
            == endpoint_digest
            and str(obligation.get("source_location") or "").strip()
            == _source_item_coverage_location(source_item)
            and statement_digest(str(obligation.get("statement") or ""))
            == endpoint_digest
        ):
            continue
        endpoint_source_items.add(source_item_key)
    missing_direct_endpoints = sorted(
        key
        for key in endpoint_source_items
        if route_kinds.get(key)
        != (
            CORRECTED_TARGET_ROUTE_KIND
            if _source_item_is_corrected_target(inventory[key])
            else "direct"
        )
    )
    if missing_direct_endpoints:
        return (
            "row has source-result/definition endpoint obligations without the required direct or "
            "approved-corrected-target source routes: "
            + ", ".join(missing_direct_endpoints)
        )
    if require_statement_target:
        recorded_target = str(raw.get("paper_statement_sha256") or "").strip().lower()
        empty_target = statement_digest("")
        if not SOURCE_ARTIFACT_SHA256_RE.fullmatch(recorded_target):
            return "statement review has no valid paper_statement_sha256 target receipt"
        if recorded_target == empty_target:
            return "statement review has an empty paper-statement target receipt"
        matching_routes = [
            route
            for route in source_target_routes
            if route[0] == recorded_target
        ]
        if not matching_routes:
            return (
                "statement review paper-statement target is not bound by any "
                "current explicit source route"
            )
        judgment = _normalize_llm_match_judgment(
            raw.get("judgment")
            or raw.get("verdict")
            or raw.get("status")
            or raw.get("matches")
        )
        if judgment == "matches":
            equivalence_bearing = any(
                route_kind in {"direct", CORRECTED_TARGET_ROUTE_KIND}
                or (
                    route_kind == "source_component"
                    and relation == "equivalent_source_component"
                    and endpoint_binding
                )
                or (
                    route_kind == "source_model_convention"
                    and relation == "equivalent_model_convention"
                    and endpoint_binding
                )
                for _digest, route_kind, relation, endpoint_binding in matching_routes
            )
            if not equivalence_bearing:
                return (
                    "matches judgment paper-statement target has no exact "
                    "equivalence-bearing source route"
                )
    return ""


def paper_statement_inventory_digest(inventory: dict[str, dict[str, Any]]) -> str:
    """Return a stable digest of canonical source-paper statement inventory."""

    payload = [
        {
            "key": key,
            "statement": normalize_statement(str(item.get("statement") or "")),
            "aliases": sorted(str(alias) for alias in item.get("aliases", []) or []),
            "source_presentation_alias": item.get("source_presentation_alias"),
            "source": str(item.get("source") or ""),
            "coverage_status": str(item.get("coverage_status") or "").strip().lower(),
            "protocol_role": str(item.get("protocol_role") or "").strip().lower(),
            "corrected_target": item.get("corrected_target"),
            "source_kind": str(item.get("source_kind") or "").strip().lower(),
            "claim_bearing": item.get("claim_bearing"),
            "source_scope_classification": str(
                item.get("source_scope_classification") or ""
            ).strip().lower(),
            "user_approved_scope_exclusion": item.get(
                "user_approved_scope_exclusion"
            ),
            "scope_reason": normalize_statement(str(item.get("scope_reason") or "")),
            "source_evidence": normalize_statement(
                str(item.get("source_evidence") or "")
            ),
            "source_artifact_path": str(item.get("source_artifact_path") or "").strip(),
            "source_artifact_sha256": str(
                item.get("source_artifact_sha256") or ""
            ).strip().lower(),
            "source_anchor_evidence_required": item.get(
                "source_anchor_evidence_required"
            )
            is True,
            "source_anchor_evidence": item.get("source_anchor_evidence"),
            "source_status": str(item.get("source_status") or "").strip(),
            "source_note": normalize_statement(str(item.get("source_note") or "")),
            "source_defect_ids": sorted(
                str(defect_id)
                for defect_id in item.get("source_defect_ids", []) or []
            ),
            "lean_declarations": sorted(
                str(name) for name in item.get("lean_declarations", []) or []
            ),
            "proof_lean_declarations": sorted(
                str(name)
                for name in item.get("proof_lean_declarations", []) or []
            ),
            "support_lean_declarations": sorted(
                str(name)
                for name in item.get("support_lean_declarations", []) or []
            ),
            "spec_lean_declarations": sorted(
                str(name)
                for name in item.get("spec_lean_declarations", []) or []
            ),
            "semantic_contract": item.get("semantic_contract"),
            **(
                {
                    SOURCE_DEFINITION_PARTITION_FIELD: item[
                        SOURCE_DEFINITION_PARTITION_FIELD
                    ]
                }
                if SOURCE_DEFINITION_PARTITION_FIELD in item
                else {}
            ),
            "source_location": str(item.get("source_location") or ""),
            "source_url": str(item.get("source_url") or ""),
        }
        for key, item in sorted(inventory.items())
    ]
    return hashlib.sha256(
        json.dumps(payload, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode(
            "utf-8"
        )
    ).hexdigest()


def paper_coverage_inventory_digest(
    inventory: dict[str, dict[str, Any]],
    *,
    mode: str,
    statement_map_payload: dict[str, Any] | None = None,
) -> str:
    """Return the mode-aware aggregate digest for coverage-sidecar discovery.

    This aggregate is useful to find additions/removals.  It is deliberately
    not the sole freshness gate: a current per-item source digest plus a
    current elaborated Lean signature lets an unchanged obligation retain its
    completed judgment when another source item changes.
    """

    payload: dict[str, Any] = {
        "mode": mode,
        "items": [
            {
                "key": key,
                "source_item_coverage_sha256": source_item_coverage_sha256(
                    item, mode
                ),
            }
            for key, item in sorted(inventory.items())
        ],
    }
    if mode == DEEP_PAPER_WITH_ALL_PROSE_CLAIMS and isinstance(
        statement_map_payload, dict
    ):
        payload["source_prose_inventory_review"] = statement_map_payload.get(
            "source_prose_inventory_review"
        )
    return hashlib.sha256(
        json.dumps(payload, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode(
            "utf-8"
        )
    ).hexdigest()


def _coverage_item_source_digest_is_current(
    coverage_item: dict[str, Any], source_item: dict[str, Any], mode: str
) -> bool:
    """Return per-item freshness without treating aggregate-map drift as stale.

    Legacy sidecars did not record a source-item semantic digest.  They remain
    usable only while their aggregate inventory digest is current; new
    sidecars record this field and can safely reuse unchanged item judgments.
    """

    if (
        coverage_item.get("source_item_coverage_digest_schema")
        != SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
    ):
        return False
    recorded = str(
        coverage_item.get("source_item_coverage_sha256") or ""
    ).strip().lower()
    if not recorded:
        return False
    return recorded == source_item_coverage_sha256(source_item, mode)


def _coverage_item_has_current_source_digest_schema(item: dict[str, Any]) -> bool:
    """Return whether a sidecar item can use semantic item-level freshness."""

    return (
        item.get("source_item_coverage_digest_schema")
        == SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
        and bool(str(item.get("source_item_coverage_sha256") or "").strip())
    )


def _semantic_coverage_item_bindings(
    inventory: dict[str, dict[str, Any]],
    audit_items: dict[str, Any],
    mode: str,
) -> tuple[dict[str, str], list[str]]:
    """Bind current source items to uniquely identical saved judgments.

    Coverage-sidecar object keys are navigation handles, not mathematical
    identity.  Preserve an exact key match (so a changed item reports stale),
    then bind an otherwise renamed current item only when its versioned source
    semantic digest identifies exactly one unused sidecar item.  Ambiguous
    duplicates fail closed rather than guessing which human judgment applies.
    """

    bindings: dict[str, str] = {
        key: key for key in inventory if isinstance(audit_items.get(key), dict)
    }
    used = set(bindings.values())
    candidates_by_digest: dict[str, list[str]] = {}
    for audit_key, raw_item in audit_items.items():
        if audit_key in used or not isinstance(raw_item, dict):
            continue
        if not _coverage_item_has_current_source_digest_schema(raw_item):
            continue
        digest = str(raw_item.get("source_item_coverage_sha256") or "").strip().lower()
        if digest:
            candidates_by_digest.setdefault(digest, []).append(str(audit_key))

    ambiguous: list[str] = []
    for source_key, source_item in inventory.items():
        if source_key in bindings:
            continue
        digest = source_item_coverage_sha256(source_item, mode)
        candidates = sorted(candidates_by_digest.get(digest, []))
        if len(candidates) == 1:
            bindings[source_key] = candidates[0]
            used.add(candidates[0])
        elif len(candidates) > 1:
            ambiguous.append(
                f"{source_key}: multiple sidecar items share its source semantic digest"
            )
    return bindings, ambiguous


def _current_row_signature_digest(row_item: ReviewItem) -> str:
    """Return one row's verified elaborated-signature digest, if available."""

    manifest = row_item.lean_signature_manifest
    if not isinstance(manifest, dict):
        return ""
    digest = signature_manifest_digest(manifest)
    if not digest:
        return ""
    if str(manifest.get("sha256") or "").strip().lower() != digest:
        return ""
    if str(row_item.lean_signature_sha256 or "").strip().lower() != digest:
        return ""
    return digest


def _current_row_signature_index(
    row_items: dict[str, ReviewItem],
) -> dict[str, list[str]]:
    """Index current row navigation by verified elaborated signature once."""

    current_by_signature: dict[str, list[str]] = {}
    for row_name, row_item in row_items.items():
        digest = _current_row_signature_digest(row_item)
        if digest:
            current_by_signature.setdefault(digest, []).append(row_name)
    return current_by_signature


def _semantic_rebound_coverage_item(
    raw_item: dict[str, Any], current_by_signature: dict[str, list[str]]
) -> tuple[dict[str, Any], list[str], bool]:
    """Rebind saved row navigation only through unique current signatures.

    The sidecar retains the original names for traceability, but all later
    coverage checks see current row names.  A missing, malformed, stale, or
    non-unique signature pin is left untouched so the existing fail-closed row
    link diagnostics remain authoritative.
    """

    copied = dict(raw_item)
    rows = _normalize_string_list(raw_item.get("review_rows"))
    if not rows:
        return copied, [], False
    pins = _normalize_review_row_signature_pins(
        raw_item.get("review_row_signature_sha256")
    )
    if pins is None or set(pins) != set(rows) or len(set(rows)) != len(rows):
        return copied, [], False

    rebound_rows: list[str] = []
    changes: list[str] = []
    for old_name in rows:
        digest = str(pins.get(old_name) or "").strip().lower()
        candidates = sorted(current_by_signature.get(digest, []))
        if old_name in candidates:
            rebound_rows.append(old_name)
            continue
        if len(candidates) != 1:
            return copied, [], False
        new_name = candidates[0]
        rebound_rows.append(new_name)
        changes.append(f"{old_name} -> {new_name}")
    if not changes:
        return copied, [], False
    copied["review_rows"] = rebound_rows
    copied["review_row_signature_sha256"] = {
        row_name: pins[old_name]
        for old_name, row_name in zip(rows, rebound_rows)
    }
    return copied, changes, True


def parse_paper_text_statement_locations(folder: Path) -> list[dict[str, Any]]:
    """Extract first source-text locations for numbered paper statements."""

    source = find_paper_text(folder)
    if source is None:
        return []
    try:
        lines = _dashboard_read_text(source).split("\n")
    except OSError:
        return []

    page = 1
    out: list[dict[str, Any]] = []
    seen: set[str] = set()
    for line_number, raw_line in enumerate(lines, start=1):
        line = raw_line
        if "\f" in line:
            page += line.count("\f")
            line = line.rsplit("\f", 1)[-1]
        stripped = line.strip()
        label_match = PAPER_TEXT_STATEMENT_LABEL_RE.match(stripped)
        if not label_match:
            continue
        kind = label_match.group("kind")
        number = label_match.group("number")
        key = _paper_statement_key(kind, number)
        if key in seen:
            continue
        seen.add(key)
        out.append(
            {
                "key": key,
                "kind": kind,
                "number": number,
                "page": page,
                "line_number": line_number,
            }
        )
    return out


def load_llm_lean_to_tex_draft_entries(
    folder: Path,
    *,
    audit_inputs: DashboardAuditInputs | None = None,
) -> dict[str, dict[str, str]]:
    """Load optional context-free LLM TeX draft entries with metadata."""

    if audit_inputs is not None:
        with dashboard_audit_input_scope(audit_inputs):
            return load_llm_lean_to_tex_draft_entries(folder)
    path = llm_lean_to_tex_drafts_file(folder)
    if not _dashboard_is_file(path):
        return {}
    payload = _dashboard_json_payload(path)
    if payload is None:
        return {}
    if is_non_evidence_scaffold_payload(payload):
        # Frozen-input scaffolds deliberately contain no context-free
        # translation.  Ignore any later fields until the marker is removed.
        return {}
    if payload.get("schema") != 1:
        return {}
    if payload.get("paper") not in {None, folder.name}:
        return {}
    items = payload.get("items")
    if not isinstance(items, dict):
        return {}
    out: dict[str, dict[str, Any]] = {}
    source = path.name
    payload_translator = str(
        payload.get("translator")
        or payload.get("validator")
        or payload.get("model")
        or payload.get("agent")
        or payload.get("generator")
        or ""
    ).strip()
    payload_translated_at = str(
        payload.get("translated_at")
        or payload.get("validated_at")
        or payload.get("timestamp")
        or payload.get("generated_at")
        or ""
    ).strip()
    payload_prompt_version = str(payload.get("prompt_version") or "").strip()
    for raw_name, raw_value in items.items():
        name = str(raw_name).strip()
        if isinstance(raw_value, dict):
            value = str(
                raw_value.get("tex_statement")
                or raw_value.get("statement")
                or raw_value.get("latex")
                or raw_value.get("translation")
                or raw_value.get("draft")
                or ""
            ).strip()
            lean_digest = str(raw_value.get("lean_statement_sha256") or "").strip()
            item_prompt_version = str(
                raw_value.get("prompt_version") or payload_prompt_version
            ).strip()
            translator = str(
                raw_value.get("translator")
                or raw_value.get("validator")
                or raw_value.get("model")
                or raw_value.get("agent")
                or raw_value.get("generator")
                or payload_translator
            ).strip()
            translated_at = str(
                raw_value.get("translated_at")
                or raw_value.get("validated_at")
                or raw_value.get("timestamp")
                or raw_value.get("generated_at")
                or payload_translated_at
            ).strip()
        else:
            value = str(raw_value).strip()
            lean_digest = ""
            item_prompt_version = payload_prompt_version
            translator = payload_translator
            translated_at = payload_translated_at
        if name and value:
            out[name] = {
                "statement": value,
                "lean_statement_sha256": lean_digest,
                "source": source,
                "translator": translator,
                "translated_at": translated_at,
                "metadata_missing": not bool(translator and translated_at),
                "prompt_version": item_prompt_version,
                "prompt_version_stale": not llm_prompt_version_is_semantically_current(
                    item_prompt_version,
                    prompt_contracts=LLM_LEAN_TO_TEX_PROMPT_SEMANTIC_CONTRACTS,
                    required_contract=REQUIRED_LLM_LEAN_TO_TEX_SEMANTIC_CONTRACT_VERSION,
                ),
            }
    return out


def load_llm_lean_to_tex_drafts(
    folder: Path,
    *,
    audit_inputs: DashboardAuditInputs | None = None,
) -> dict[str, str]:
    """Load optional context-free LLM TeX drafts for expanded Lean statements."""

    return {
        name: entry["statement"]
        for name, entry in load_llm_lean_to_tex_draft_entries(
            folder, audit_inputs=audit_inputs
        ).items()
        if entry.get("statement")
    }


def llm_statement_judgments_file(folder: Path) -> Path:
    """Return the preferred LLM statement-match judgment sidecar for a paper."""

    tracked_path = paper_relative_file(folder, DEFAULT_LLM_STATEMENT_JUDGE_FILE, "statement_match_llm.json")
    if _dashboard_audit_inputs() is not None or _dashboard_is_file(tracked_path):
        return tracked_path
    return folder / ".review_traces" / "statement_match_llm.json"


def llm_paper_coverage_file(folder: Path) -> Path:
    """Return the preferred LLM source-paper coverage sidecar for a paper."""

    tracked_path = paper_relative_file(folder, DEFAULT_LLM_PAPER_COVERAGE_FILE, "paper_coverage_llm.json")
    if _dashboard_audit_inputs() is not None or _dashboard_is_file(tracked_path):
        return tracked_path
    return folder / ".review_traces" / "paper_coverage_llm.json"


def llm_defect_support_file(folder: Path) -> Path:
    """Return the independent source-defect-to-Lean semantic audit sidecar."""

    tracked_path = paper_relative_file(
        folder,
        DEFAULT_LLM_DEFECT_SUPPORT_FILE,
        "defect_support_match_llm.json",
    )
    if _dashboard_audit_inputs() is not None or _dashboard_is_file(tracked_path):
        return tracked_path
    return folder / ".review_traces" / "defect_support_match_llm.json"


def load_llm_defect_support_audit(
    folder: Path,
    *,
    audit_inputs: DashboardAuditInputs | None = None,
) -> dict[str, Any]:
    """Load exact-hash semantic judgments for quarantined defect support.

    This audit is deliberately separate from paper-coverage classification.  A
    coverage reviewer may select a candidate counterexample route, but that
    route receives defect-support credit only after this sidecar binds the exact
    defect record to the exact elaborated Lean statement and explains the
    mathematical counterexample/refutation relation atom by atom.
    """

    if audit_inputs is not None:
        with dashboard_audit_input_scope(audit_inputs):
            return load_llm_defect_support_audit(folder)
    path = llm_defect_support_file(folder)
    if not _dashboard_is_file(path):
        return {}
    payload = _dashboard_json_payload(path)
    if payload is None:
        return {"source": path.name, "load_error": "invalid JSON", "items": {}}
    if not isinstance(payload, dict):
        return {"source": path.name, "load_error": "top level is not an object", "items": {}}
    if payload.get("schema") != 1:
        return {"source": path.name, "load_error": "schema must be 1", "items": {}}
    if payload.get("paper") != folder.name:
        return {
            "source": path.name,
            "load_error": "paper does not match the paper folder",
            "items": {},
        }
    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        return {"source": path.name, "load_error": "items is not an object", "items": {}}
    items = raw_items
    validator = str(
        payload.get("validator")
        or payload.get("model")
        or payload.get("judge")
        or payload.get("agent")
        or ""
    ).strip()
    validated_at = str(
        payload.get("validated_at")
        or payload.get("timestamp")
        or payload.get("generated_at")
        or ""
    ).strip()
    audit_kind = str(payload.get("audit_kind") or "").strip()
    prompt_version = str(payload.get("prompt_version") or "").strip()
    return {
        "source": path.name,
        "load_error": "",
        "validator": validator,
        "validator_type": str(payload.get("validator_type") or "").strip(),
        "validated_at": validated_at,
        "audit_kind": audit_kind,
        "source_grounded": payload.get("source_grounded") is True,
        "prompt_version": prompt_version,
        "prompt_version_stale": (
            prompt_version != REQUIRED_LLM_DEFECT_SUPPORT_PROMPT_VERSION
        ),
        "metadata_missing": not bool(validator and validated_at),
        "items": items,
    }


def _normalize_llm_match_judgment(raw: Any) -> str:
    """Normalize LLM match verdicts for dashboard display."""

    if isinstance(raw, bool):
        return "matches" if raw else "mismatch"
    value = str(raw or "").strip().lower()
    if value in {"match", "matches", "yes", "true", "equivalent", "same"}:
        return "matches"
    if value in {"mismatch", "does_not_match", "does not match", "no", "false", "different"}:
        return "mismatch"
    if value in {"uncertain", "unknown", "unsure", "partial", "needs_review"}:
        return "uncertain"
    return value


def _normalize_llm_match_resolution(raw: Any) -> str:
    """Normalize optional LLM statement-match resolution categories."""

    value = re.sub(r"[\s-]+", "_", str(raw or "").strip().lower())
    if not value or value in {"none", "unresolved", "open"}:
        return ""
    if value in CONDITIONAL_BOUNDARY_RESOLUTION_ALIASES:
        return CONDITIONAL_BOUNDARY_RESOLUTION
    return value


def _normalize_paper_coverage_judgment(raw: Any) -> str:
    """Normalize paper-level source-coverage verdicts."""

    if isinstance(raw, bool):
        return "covered" if raw else "missing"
    value = str(raw or "").strip().lower().replace("-", "_")
    value = re.sub(r"\s+", "_", value)
    if value in {"match", "matches", "yes", "true", "represented", "present"}:
        return "covered"
    if value in {
        "conditional",
        "conditional_boundary",
        "visible_premise_boundary",
        "covered_with_boundary",
        "covered_conditionally",
        "additional_assumption",
        "covered_with_additional_assumption",
    }:
        return "conditional_boundary"
    if value in {
        "support",
        "support_only",
        "covered_by_support",
        "covered_in_support",
        "covered_by_support_declarations",
    }:
        return "covered_by_support"
    if value in {"partial", "partially_represented", "partial_coverage"}:
        return "partially_covered"
    if value in {"not_covered", "absent", "no", "false"}:
        return "missing"
    if value in {"irrelevant", "background", "not_target", "not_review_target"}:
        return "not_a_paper_target"
    return value


def _normalize_string_list(raw: Any) -> list[str]:
    """Normalize scalar/list sidecar fields into a stable string list."""

    if raw is None:
        return []
    if isinstance(raw, (list, tuple, set)):
        values = raw
    else:
        values = str(raw).split(",")
    out: list[str] = []
    for value in values:
        text = str(value or "").strip()
        if text:
            out.append(text)
    return out


def _normalize_review_row_signature_pins(raw: Any) -> dict[str, str] | None:
    """Normalize one coverage item's exact current-row signature pin map.

    Coverage-sidecar row names are only routing keys.  The value for each key
    must be the canonical digest of the elaborated, normalized Lean signature
    that the source-to-row judgment actually inspected.  Keep a malformed
    non-object distinct from an empty object so the summary can fail closed.
    """

    if not isinstance(raw, dict):
        return None
    return {
        str(name or "").strip(): str(digest or "").strip().lower()
        for name, digest in raw.items()
    }


def is_proposition_definition_manifest(manifest: Any) -> bool:
    """Return whether schema-2 freezes a definition whose instantiated value is Prop."""

    if not isinstance(manifest, dict):
        return False
    if manifest.get("schema") != 2 or manifest.get("declaration_kind") != "definition":
        return False
    atoms = manifest.get("atoms")
    if not isinstance(atoms, list) or not atoms:
        return False
    result = atoms[-1]
    if not isinstance(result, dict) or result.get("ref") != "result":
        return False
    canonical = result.get("canonical")
    if not isinstance(canonical, dict) or canonical.get("tag") != "definition":
        return False
    result_type = canonical.get("type")
    if not isinstance(result_type, dict) or result_type.get("tag") != "sort":
        return False
    level = result_type.get("level")
    return isinstance(level, dict) and level.get("tag") == "zero"


def is_proposition_specification_manifest(manifest: Any) -> bool:
    """Return whether a reviewed declaration defines, rather than proves, a Prop."""

    if is_proposition_definition_manifest(manifest):
        return True
    if not isinstance(manifest, dict):
        return False
    if manifest.get("schema") != 2 or manifest.get("declaration_kind") != "inductive":
        return False
    atoms = manifest.get("atoms")
    if not isinstance(atoms, list) or not atoms:
        return False
    result = atoms[-1]
    if not isinstance(result, dict) or result.get("ref") != "result":
        return False
    canonical = result.get("canonical")
    if not isinstance(canonical, dict) or canonical.get("tag") != "inductive":
        return False
    result_type = canonical.get("type")
    if not isinstance(result_type, dict) or result_type.get("tag") != "sort":
        return False
    level = result_type.get("level")
    return isinstance(level, dict) and level.get("tag") == "zero"


def signature_manifest_atom_digest(atom: Any) -> str:
    """Hash one name-free manifest atom for v10 Lean-obligation routing."""

    if not isinstance(atom, dict):
        return ""
    payload = {
        "ref": str(atom.get("ref") or "").strip(),
        "role": str(atom.get("role") or "").strip(),
        "canonical": atom.get("canonical"),
    }
    if payload["role"] != "conclusion":
        payload["binder_info"] = str(atom.get("binder_info") or "").strip()
    if not payload["ref"] or not payload["role"] or payload["canonical"] is None:
        return ""
    return hashlib.sha256(
        json.dumps(payload, ensure_ascii=False, sort_keys=True, separators=(",", ":")).encode(
            "utf-8"
        )
    ).hexdigest()


def operational_complexity_review_error(
    raw: Any, expected_complexity_conclusion_id: str
) -> str:
    """Validate operational evidence required for a full polynomial-time match.

    Identifiers in this review route graph edges and conclusion references only.
    Runtime credit comes from expanded operation semantics, complete reachable-
    branch coverage, a worst-case recurrence, and explicit work accounting.
    """

    if not isinstance(raw, dict):
        return "polynomial-time match is missing operational_complexity_review"

    def required_string(value: Any) -> str:
        return value.strip() if isinstance(value, str) else ""

    def substantive(value: Any) -> bool:
        text = required_string(value)
        return len(text) >= 20 and not NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(text)

    if required_string(raw.get("schema_version")) != OPERATIONAL_COMPLEXITY_REVIEW_VERSION:
        return "operational complexity review has an invalid schema_version"

    for field, label in (
        ("executor_semantics", "executor semantics"),
        ("input_domain", "input domain"),
        ("input_size_measure", "input-size measure"),
    ):
        if not substantive(raw.get(field)):
            return f"operational complexity review lacks substantive {label}"

    graph = raw.get("dependency_graph")
    if not isinstance(graph, dict):
        return "operational complexity review has no dependency_graph object"
    nodes = graph.get("nodes")
    edges = graph.get("edges")
    roots = graph.get("root_node_ids")
    if not isinstance(nodes, list) or not nodes:
        return "operational dependency graph has no nodes"
    if not isinstance(edges, list):
        return "operational dependency graph has no edges list"
    if not isinstance(roots, list) or not roots:
        return "operational dependency graph has no root_node_ids"

    node_ids: set[str] = set()
    adjacency: dict[str, set[str]] = {}
    node_work_categories: set[str] = set()
    for node in nodes:
        if not isinstance(node, dict):
            return "operational dependency graph node is not an object"
        node_id = required_string(node.get("id"))
        if not node_id or node_id in node_ids:
            return "operational dependency graph node has a missing or duplicate id"
        if not substantive(node.get("operation_semantics")):
            return "operational dependency graph node lacks substantive operation semantics"
        if not substantive(node.get("reachable_branch_domain")):
            return "operational dependency graph node lacks a reachable branch domain"
        categories = node.get("work_accounting_categories")
        if not isinstance(categories, list) or not categories:
            return "operational dependency graph node has no work-accounting categories"
        normalized_categories = [required_string(item) for item in categories]
        if any(not item for item in normalized_categories):
            return "operational dependency graph node has an empty work category"
        if len(normalized_categories) != len(set(normalized_categories)):
            return "operational dependency graph node has duplicate work categories"
        if set(normalized_categories) - OPERATIONAL_WORK_CATEGORIES:
            return "operational dependency graph node has an unknown work category"
        node_work_categories.update(normalized_categories)
        node_ids.add(node_id)
        adjacency[node_id] = set()

    normalized_roots = [required_string(item) for item in roots]
    if any(not item for item in normalized_roots):
        return "operational dependency graph has an empty root node id"
    if len(normalized_roots) != len(set(normalized_roots)):
        return "operational dependency graph has duplicate root node ids"
    if set(normalized_roots) - node_ids:
        return "operational dependency graph references an unknown root node"

    for edge in edges:
        if not isinstance(edge, dict):
            return "operational dependency graph edge is not an object"
        from_node = required_string(edge.get("from_node_id"))
        to_node = required_string(edge.get("to_node_id"))
        if from_node not in node_ids or to_node not in node_ids:
            return "operational dependency graph edge has an unknown endpoint"
        if not substantive(edge.get("invocation_semantics")):
            return "operational dependency graph edge lacks invocation semantics"
        if not substantive(edge.get("branch_condition")):
            return "operational dependency graph edge lacks a branch condition"
        adjacency[from_node].add(to_node)

    reachable = set(normalized_roots)
    frontier = list(normalized_roots)
    while frontier:
        current = frontier.pop()
        for dependency in adjacency[current]:
            if dependency not in reachable:
                reachable.add(dependency)
                frontier.append(dependency)
    if reachable != node_ids:
        return "operational dependency graph contains a node unreachable from its roots"
    if graph.get("transitive_closure_complete") is not True:
        return "operational dependency graph does not certify complete transitive closure"
    if graph.get("all_reachable_branches_complete") is not True:
        return "operational dependency graph does not cover every reachable branch"
    if not substantive(graph.get("coverage_basis")):
        return "operational dependency graph lacks a substantive coverage basis"

    if not substantive(raw.get("worst_case_recurrence")):
        return "operational complexity review lacks a worst-case recurrence"
    if not substantive(raw.get("worst_case_bound")):
        return "operational complexity review lacks a worst-case bound"
    conclusion_id = required_string(raw.get("complexity_lean_conclusion_id"))
    if not conclusion_id or conclusion_id != expected_complexity_conclusion_id:
        return "operational complexity review is not bound to the complexity conclusion"
    if not substantive(raw.get("complexity_statement_binding")):
        return "operational complexity review lacks a semantic complexity-statement binding"

    work_items = raw.get("work_accounting")
    if not isinstance(work_items, list):
        return "operational complexity review has no work_accounting list"
    recorded_categories: set[str] = set()
    for item in work_items:
        if not isinstance(item, dict):
            return "operational work-accounting item is not an object"
        category = required_string(item.get("category")).lower()
        if category not in OPERATIONAL_WORK_CATEGORIES:
            return "operational work-accounting item has an invalid category"
        if category in recorded_categories:
            return "operational work-accounting has a duplicate category"
        recorded_categories.add(category)
        status = required_string(item.get("status")).lower()
        if status not in OPERATIONAL_WORK_STATUSES:
            return "operational work-accounting item has an invalid status"
        if status not in FULL_RUNTIME_MATCH_WORK_STATUSES:
            return (
                "polynomial-time match has missing or excluded_by_claim "
                "operational work"
            )
        if status == "charged" and category not in node_work_categories:
            return (
                "charged operational work category is not linked to a dependency "
                "graph node"
            )
        for field, label in (
            ("operation_semantics", "operation semantics"),
            (
                "worst_case_charge_or_absence_basis",
                "worst-case charge or absence basis",
            ),
            ("evidence_basis", "evidence basis"),
        ):
            if not substantive(item.get(field)):
                return f"operational work-accounting item lacks substantive {label}"
    if recorded_categories != OPERATIONAL_WORK_CATEGORIES:
        return "operational work-accounting does not cover every required category"

    closure = raw.get("closure_elimination")
    if not isinstance(closure, dict):
        return "operational complexity review has no closure_elimination object"
    material = closure.get("material")
    if not isinstance(material, bool):
        return "closure_elimination has no Boolean material field"
    if not material:
        if not substantive(closure.get("non_material_basis")):
            return "non-material closure elimination lacks a substantive basis"
        return ""

    evidence_kind = required_string(closure.get("evidence_kind")).lower()
    if evidence_kind not in CLOSURE_ELIMINATION_EVIDENCE_KINDS:
        return "material closure elimination has an invalid evidence_kind"
    for field, label in (
        ("evidence_artifact_sha256", "evidence artifact"),
        ("audited_source_sha256", "audited source"),
    ):
        digest = required_string(closure.get(field))
        if re.fullmatch(r"[0-9a-f]{64}", digest) is None:
            return f"material closure elimination lacks a valid {label} SHA-256 pin"
    if not required_string(closure.get("evidence_locator")):
        return "material closure elimination has no evidence locator"
    for field, label in (
        ("old_dependency_semantics", "old dependency semantics"),
        ("semantic_binding", "semantic artifact/source binding"),
        ("elimination_basis", "dependency-elimination basis"),
    ):
        if not substantive(closure.get(field)):
            return f"material closure elimination lacks substantive {label}"
    if closure.get("symbol_names_used_as_evidence") is not False:
        return "material closure elimination may not use symbol names as evidence"
    return ""


def fidelity_risk_review_error(
    raw: Any,
    source_obligations: dict[str, str],
    lean_obligations: dict[str, str],
    verdict: str,
    source_algorithm_level: str,
) -> str:
    """Validate source/Lean fidelity hazards without using declaration names.

    The statement manifest and obligation ledger identify where a fact occurs,
    but identifiers do not establish its semantics.  This review forces an
    independent comparison of five recurring failure modes and binds every
    positive match to a visible Lean conclusion.
    """

    if not isinstance(raw, dict):
        return "semantic scope review has no fidelity_risk_review object"
    schema_version = raw.get("schema_version")
    if (
        not isinstance(schema_version, str)
        or schema_version not in SUPPORTED_FIDELITY_RISK_REVIEW_VERSIONS
    ):
        return "fidelity risk review has an invalid schema_version"

    dimensions = raw.get("dimensions")
    if not isinstance(dimensions, dict):
        return "fidelity risk review has no dimensions object"
    dimension_names = set(dimensions)
    if dimension_names != FIDELITY_RISK_DIMENSIONS:
        missing = sorted(FIDELITY_RISK_DIMENSIONS - dimension_names)
        extra = sorted(dimension_names - FIDELITY_RISK_DIMENSIONS)
        details: list[str] = []
        if missing:
            details.append("missing " + ", ".join(missing))
        if extra:
            details.append("unknown " + ", ".join(extra))
        return "fidelity risk review dimensions are incomplete: " + "; ".join(details)

    def required_string(value: Any) -> str:
        return value.strip() if isinstance(value, str) else ""

    def substantive(value: Any) -> bool:
        text = required_string(value)
        return len(text) >= 20 and not NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(text)

    def obligation_ids(
        value: Any, known: dict[str, str], label: str
    ) -> tuple[set[str], str]:
        if not isinstance(value, list) or not value:
            return set(), f"{label} must be a nonempty list"
        normalized = [required_string(item) for item in value]
        if any(not item for item in normalized):
            return set(), f"{label} contains an empty obligation id"
        if len(normalized) != len(set(normalized)):
            return set(), f"{label} contains duplicate obligation ids"
        if set(normalized) - set(known):
            return set(), f"{label} references unknown obligation ids"
        return set(normalized), ""

    conclusion_ids = {
        key for key, kind in lean_obligations.items() if kind == "conclusion"
    }
    normalized: dict[str, dict[str, Any]] = {}
    for name in sorted(FIDELITY_RISK_DIMENSIONS):
        item = dimensions.get(name)
        if not isinstance(item, dict):
            return f"fidelity risk dimension `{name}` is not an object"
        applicable = item.get("applicable")
        if not isinstance(applicable, bool):
            return f"fidelity risk dimension `{name}` has no Boolean applicable field"
        normalized[name] = item
        if not applicable:
            if not substantive(item.get("absence_basis")):
                return f"fidelity risk dimension `{name}` lacks a substantive absence_basis"
            continue

        _, error = obligation_ids(
            item.get("source_obligation_ids"),
            source_obligations,
            f"fidelity risk dimension `{name}` source_obligation_ids",
        )
        if error:
            return error
        lean_ids, error = obligation_ids(
            item.get("lean_obligation_ids"),
            lean_obligations,
            f"fidelity risk dimension `{name}` lean_obligation_ids",
        )
        if error:
            return error
        for field, label in (
            ("source_semantics", "source semantics"),
            ("lean_semantics", "Lean semantics"),
            ("relation_basis", "relation basis"),
        ):
            if not substantive(item.get(field)):
                return f"fidelity risk dimension `{name}` lacks substantive {label}"
        relation = required_string(item.get("relation")).lower()
        if relation not in FIDELITY_RISK_RELATIONS:
            return f"fidelity risk dimension `{name}` has an invalid relation"
        if verdict == "matches":
            if relation != "equivalent":
                return (
                    f"matches judgment records non-equivalent `{name}` semantics"
                )
            if not substantive(item.get("lean_evidence_statement")):
                return (
                    f"matching fidelity risk dimension `{name}` lacks a substantive "
                    "Lean evidence statement"
                )
            evidence_id = required_string(item.get("lean_evidence_conclusion_id"))
            if evidence_id not in conclusion_ids:
                return (
                    f"matching fidelity risk dimension `{name}` is not bound to a "
                    "Lean conclusion obligation"
                )
            if evidence_id not in lean_ids:
                return (
                    f"matching fidelity risk dimension `{name}` evidence conclusion "
                    "is not among its reviewed Lean obligations"
                )

    output_shape = normalized["output_shape"]
    if output_shape.get("applicable"):
        for field, label in (
            ("source_output_shape", "source output arity/shape"),
            ("lean_output_shape", "Lean output arity/shape"),
            ("projection_terminal_policy", "projection and terminal-component policy"),
            ("arity_basis", "arity comparison basis"),
        ):
            if not substantive(output_shape.get(field)):
                return f"output-shape review lacks substantive {label}"

    action_space = normalized["adversarial_action_space"]
    if action_space.get("applicable"):
        for field, label in (
            ("source_action_space", "source action-space semantics"),
            ("lean_action_space", "Lean action-space semantics"),
            ("carrier_capacity_basis", "carrier/capacity basis"),
            ("duplicate_interaction_basis", "duplicate-interaction basis"),
            ("nonvacuity_basis", "nonvacuity basis"),
        ):
            if not substantive(action_space.get(field)):
                return f"adversarial action-space review lacks substantive {label}"
        source_nonvacuous = action_space.get("source_nonvacuous")
        lean_nonvacuous = action_space.get("lean_nonvacuous")
        if not isinstance(source_nonvacuous, bool) or not isinstance(
            lean_nonvacuous, bool
        ):
            return "adversarial action-space review lacks Boolean nonvacuity judgments"
        if verdict == "matches" and not (source_nonvacuous and lean_nonvacuous):
            return (
                "matching universal adversarial transformation has a vacuous or "
                "ill-formed legal action space"
            )

    extrema = normalized["coherent_extrema_witness"]
    if extrema.get("applicable"):
        for field, label in (
            ("source_extrema_semantics", "source extrema semantics"),
            ("lean_extrema_semantics", "Lean extrema semantics"),
            ("coherent_witness_basis", "coherent-witness basis"),
            ("runner_refinement_basis", "actual-runner/refinement basis"),
        ):
            if not substantive(extrema.get(field)):
                return f"coherent-extrema review lacks substantive {label}"
        source_combines = extrema.get("source_combines_candidatewise_extrema")
        lean_combines = extrema.get("lean_combines_candidatewise_extrema")
        if not isinstance(source_combines, bool) or not isinstance(
            lean_combines, bool
        ):
            return "coherent-extrema review lacks Boolean candidatewise-combination judgments"
        witness_status = required_string(extrema.get("coherent_witness_status")).lower()
        if witness_status not in COHERENT_EXTREMA_WITNESS_STATUSES:
            return "coherent-extrema review has an invalid coherent_witness_status"
        if (source_combines or lean_combines) and witness_status == "not_required":
            return "candidatewise extrema are combined without a coherent-witness audit"
        if verdict == "matches" and witness_status not in {
            "not_required",
            "same_coherent_witness",
            "proved_jointly_realizable",
        }:
            return (
                "matching extrema claim combines bounds that are not realized by one "
                "coherent witness"
            )

    counting = normalized["cardinality_fibers"]
    if counting.get("applicable"):
        for field, label in (
            ("source_counted_object", "source counted object"),
            ("lean_counted_object", "Lean counted object"),
            ("realized_fiber_semantics", "realized-fiber semantics"),
            ("surjectivity_basis", "surjectivity basis"),
        ):
            if not substantive(counting.get(field)):
                return f"cardinality/fiber review lacks substantive {label}"
        source_counting = required_string(counting.get("source_counting_semantics")).lower()
        lean_counting = required_string(counting.get("lean_counting_semantics")).lower()
        if source_counting not in COUNTING_SEMANTICS or lean_counting not in COUNTING_SEMANTICS:
            return "cardinality/fiber review has invalid counting semantics"
        source_exact = counting.get("source_claims_exact_cardinality")
        lean_exact = counting.get("lean_claims_exact_cardinality")
        if not isinstance(source_exact, bool) or not isinstance(lean_exact, bool):
            return "cardinality/fiber review lacks Boolean exact-cardinality judgments"
        if verdict == "matches" and source_exact != lean_exact:
            return "matches judgment confuses exact cardinality with a bound"
        status = required_string(counting.get("surjectivity_status")).lower()
        if status not in SURJECTIVITY_STATUSES:
            return "cardinality/fiber review has an invalid surjectivity_status"
        crosses_family_fibers = {
            source_counting,
            lean_counting,
        } == {"syntactic_family_cardinality", "nonempty_realized_fibers"}
        claims_family_fiber_equality = counting.get(
            "claims_syntactic_family_equals_realized_fibers"
        )
        if not isinstance(claims_family_fiber_equality, bool):
            return (
                "cardinality/fiber review lacks a Boolean "
                "claims_syntactic_family_equals_realized_fibers field"
            )
        surjectivity_required = (
            claims_family_fiber_equality
            or (verdict == "matches" and source_exact and crosses_family_fibers)
        )
        if surjectivity_required and status not in {
            "definitionally_surjective",
            "proved_surjective",
        }:
            return (
                "exact syntactic-family/realized-fiber equality lacks surjectivity evidence"
            )
        if status in {"definitionally_surjective", "proved_surjective"}:
            if not substantive(counting.get("surjectivity_statement")):
                return "surjectivity evidence lacks a substantive mathematical statement"
            surjectivity_id = required_string(
                counting.get("surjectivity_lean_conclusion_id")
            )
            if surjectivity_id not in conclusion_ids:
                return "surjectivity evidence is not bound to a Lean conclusion obligation"
            counting_lean_ids = {
                required_string(item)
                for item in counting.get("lean_obligation_ids", [])
            }
            if surjectivity_id not in counting_lean_ids:
                return (
                    "surjectivity evidence conclusion is not among the cardinality "
                    "dimension's reviewed Lean obligations"
                )

    execution_scope = normalized["execution_claim_scope"]
    if source_algorithm_level != "not_algorithmic" and not execution_scope.get(
        "applicable"
    ):
        return "algorithmic row lacks an applicable execution-claim scope review"
    if execution_scope.get("applicable"):
        execution_fields = (
            LEGACY_FIDELITY_EXECUTION_SCOPE_FIELDS
            if schema_version == LEGACY_FIDELITY_RISK_REVIEW_VERSION
            else FIDELITY_EXECUTION_SCOPE_FIELDS
        )
        for field, label in execution_fields:
            if not substantive(execution_scope.get(field)):
                return f"execution-claim scope review lacks substantive {label}"
    return ""


def semantic_scope_review_error(
    raw: Any,
    source_obligations: dict[str, str],
    lean_obligations: dict[str, str],
    lean_manifest_atoms: dict[str, dict[str, Any]],
    verdict: str,
    *,
    require_source_definition_semantics_review: bool = False,
) -> str:
    """Validate the name-independent semantic-world review for one row.

    The declaration manifest freezes the Lean type, but one final proposition
    atom may contain several logically unrelated conjuncts.  In particular,
    runner success and a self-characterizing predicate about an independently
    supplied output do not establish that the runner produced or preserves that
    output. V10 therefore requires the reviewer to record profile scope,
    definition expansion, algorithmic strength, runner/result provenance,
    fidelity-risk dimensions, and every bridge between distinct semantic
    worlds. The enumerated relations are checked structurally; the mathematical
    truth of the prose remains an independent source-review obligation.  A
    source-definition route has one extra structural review because a
    total Lean definition can otherwise conceal a source-domain extension or
    an omitted operational guarantee.
    """

    if not isinstance(raw, dict):
        return "missing `semantic_scope_review` object"

    def required_string(value: Any) -> str:
        return value.strip() if isinstance(value, str) else ""

    def substantive(value: Any) -> bool:
        text = required_string(value)
        return len(text) >= 20 and not NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(text)

    def canonical_contains_constant(value: Any, predicate: Callable[[str], bool]) -> bool:
        if isinstance(value, list):
            return any(canonical_contains_constant(item, predicate) for item in value)
        if not isinstance(value, dict):
            return False
        if value.get("tag") == "const" and predicate(str(value.get("name") or "")):
            return True
        return any(canonical_contains_constant(item, predicate) for item in value.values())

    def lean_atom_has_numeric_semantics(obligation_id: str) -> bool:
        atom = lean_manifest_atoms.get(obligation_id) or {}
        return canonical_contains_constant(
            atom.get("canonical"), lambda name: name in NUMERIC_SEMANTIC_CONSTANTS
        )

    def lean_atom_has_discrete_semantics(obligation_id: str) -> bool:
        atom = lean_manifest_atoms.get(obligation_id) or {}
        return canonical_contains_constant(
            atom.get("canonical"),
            lambda name: name.startswith(DISCRETE_SEMANTIC_CONSTANT_PREFIXES),
        )

    def lean_atom_has_expanded_definition(obligation_id: str) -> bool:
        atom = lean_manifest_atoms.get(obligation_id) or {}

        def contains_expansion(value: Any) -> bool:
            if isinstance(value, list):
                return any(contains_expansion(item) for item in value)
            if not isinstance(value, dict):
                return False
            if value.get("tag") in {
                "definition",
                "inductive",
                "inlined_definition",
                "local_constructor",
                "local_inductive",
                "local_recursor",
                "local_theorem",
            }:
                return True
            return any(contains_expansion(item) for item in value.values())

        return contains_expansion(atom.get("canonical"))

    def lean_conclusion_exposes_equivalence(obligation_id: str) -> bool:
        atom = lean_manifest_atoms.get(obligation_id) or {}
        return canonical_contains_constant(
            atom.get("canonical"), lambda name: name in {"Eq", "Iff"}
        )

    def obligation_id_list(
        value: Any, field: str, known: dict[str, str], *, nonempty: bool
    ) -> tuple[set[str], str]:
        if not isinstance(value, list):
            return set(), f"{field} is not a list"
        normalized = [required_string(item) for item in value]
        if any(not item for item in normalized):
            return set(), f"{field} contains an empty obligation id"
        if len(normalized) != len(set(normalized)):
            return set(), f"{field} contains duplicate obligation ids"
        if nonempty and not normalized:
            return set(), f"{field} must not be empty"
        unknown = set(normalized) - set(known)
        if unknown:
            return set(), f"{field} references unknown obligation ids"
        return set(normalized), ""

    def operator_review_coverage_error(
        review: dict[str, Any],
        items: list[Any],
        *,
        source_item_field: str,
        lean_item_field: str,
        non_source_field: str,
        non_lean_field: str,
        label: str,
        lean_absence_conflict: Callable[[str], bool],
    ) -> str:
        covered_source: set[str] = set()
        covered_lean: set[str] = set()
        for item in items:
            if not isinstance(item, dict):
                return f"{label} review item is not an object"
            source_ids, error = obligation_id_list(
                item.get(source_item_field),
                f"{label} review item {source_item_field}",
                source_obligations,
                nonempty=True,
            )
            if error:
                return error
            lean_ids, error = obligation_id_list(
                item.get(lean_item_field),
                f"{label} review item {lean_item_field}",
                lean_obligations,
                nonempty=True,
            )
            if error:
                return error
            covered_source.update(source_ids)
            covered_lean.update(lean_ids)
        non_source, error = obligation_id_list(
            review.get(non_source_field),
            non_source_field,
            source_obligations,
            nonempty=False,
        )
        if error:
            return error
        non_lean, error = obligation_id_list(
            review.get(non_lean_field),
            non_lean_field,
            lean_obligations,
            nonempty=False,
        )
        if error:
            return error
        if covered_source & non_source:
            return f"{label} source obligations are both reviewed and classified absent"
        if covered_lean & non_lean:
            return f"{label} Lean obligations are both reviewed and classified absent"
        if covered_source | non_source != set(source_obligations):
            return f"{label} review does not cover every source obligation"
        if covered_lean | non_lean != set(lean_obligations):
            return f"{label} review does not cover every Lean obligation"
        conflicts = sorted(item for item in non_lean if lean_absence_conflict(item))
        if conflicts:
            return (
                f"{label} review classifies manifest-visible operator semantics as absent: "
                + ", ".join(conflicts)
            )
        return ""

    source_scope = required_string(raw.get("source_quantification")).lower()
    lean_scope = required_string(raw.get("lean_quantification")).lower()
    scope_relation = required_string(raw.get("quantification_relation")).lower()
    if source_scope not in PROFILE_QUANTIFICATION_SCOPES:
        return "semantic scope review has an invalid source_quantification"
    if lean_scope not in PROFILE_QUANTIFICATION_SCOPES:
        return "semantic scope review has an invalid lean_quantification"
    if scope_relation not in QUANTIFICATION_RELATIONS:
        return "semantic scope review has an invalid quantification_relation"
    if not substantive(raw.get("source_quantification_basis")):
        return "semantic scope review lacks a substantive source quantification basis"
    if not substantive(raw.get("lean_quantification_basis")):
        return "semantic scope review lacks a substantive Lean quantification basis"
    if verdict == "matches":
        if scope_relation != "equivalent":
            return "matches judgment records non-equivalent source/Lean quantification"
        fixed_or_global = {
            "fixed_profile",
            "all_profiles",
            "existential_profile",
        }
        if source_scope in fixed_or_global and lean_scope in fixed_or_global:
            if source_scope != lean_scope:
                return "matches judgment confuses fixed-, existential-, and all-profile scope"
        elif source_scope != lean_scope:
            return "matches judgment records different source/Lean profile scope"

    definition_review = raw.get("named_definition_review")
    if not isinstance(definition_review, dict):
        return "semantic scope review has no named_definition_review object"
    definitions_present = definition_review.get("definitions_present")
    if not isinstance(definitions_present, bool):
        return "named_definition_review has no Boolean definitions_present"
    definition_items = definition_review.get("items")
    if not isinstance(definition_items, list):
        return "named_definition_review has no items list"
    if definitions_present != bool(definition_items):
        return "named_definition_review presence flag does not match its items"
    if not definitions_present and not substantive(
        definition_review.get("absence_basis")
    ):
        return "named_definition_review lacks a substantive absence_basis"
    covered_definition_obligations: set[str] = set()
    for item in definition_items:
        if not isinstance(item, dict):
            return "named definition review item is not an object"
        obligation_ids, error = obligation_id_list(
            item.get("lean_obligation_ids"),
            "named definition review item lean_obligation_ids",
            lean_obligations,
            nonempty=True,
        )
        if error:
            return error
        covered_definition_obligations.update(obligation_ids)
    non_definition_obligations, error = obligation_id_list(
        definition_review.get("non_definition_lean_obligation_ids"),
        "non_definition_lean_obligation_ids",
        lean_obligations,
        nonempty=False,
    )
    if error:
        return error
    if covered_definition_obligations & non_definition_obligations:
        return "Lean obligations are both definition-reviewed and classified definition-free"
    if covered_definition_obligations | non_definition_obligations != set(
        lean_obligations
    ):
        return "named definition review does not cover every Lean obligation"
    hidden_expansions = sorted(
        item
        for item in non_definition_obligations
        if lean_atom_has_expanded_definition(item)
    )
    if hidden_expansions:
        return (
            "named definition review classifies manifest-expanded definitions as absent: "
            + ", ".join(hidden_expansions)
        )
    for item in definition_items:
        if not isinstance(item, dict):
            return "named definition review item is not an object"
        if not required_string(item.get("surface_expression")):
            return "named definition review item has no surface_expression"
        if not substantive(item.get("unfolded_semantics")):
            return "named definition review item lacks substantive unfolded semantics"
        if not substantive(item.get("expansion_basis")):
            return "named definition review item lacks a substantive expansion basis"
        recursive_dependencies = item.get("recursive_result_dependencies")
        if not isinstance(recursive_dependencies, list):
            return "named definition review item has no recursive_result_dependencies list"
        recursive_complete = item.get("recursive_expansion_complete")
        if not isinstance(recursive_complete, bool):
            return "named definition review item has no Boolean recursive_expansion_complete"
        seen_dependencies: set[str] = set()
        for dependency in recursive_dependencies:
            if not isinstance(dependency, dict):
                return "recursive named-definition dependency is not an object"
            dependency_expression = required_string(
                dependency.get("surface_expression")
            )
            if not dependency_expression or dependency_expression in seen_dependencies:
                return "recursive named-definition dependency is missing or duplicated"
            seen_dependencies.add(dependency_expression)
            if not substantive(dependency.get("unfolded_semantics")):
                return (
                    "recursive named-definition dependency lacks substantive "
                    "unfolded semantics"
                )
            if not substantive(dependency.get("expansion_basis")):
                return (
                    "recursive named-definition dependency lacks a substantive "
                    "expansion basis"
                )
        if verdict == "matches" and not recursive_complete:
            return (
                "matches judgment has an incomplete recursive named-definition expansion"
            )
        classification = required_string(item.get("classification")).lower()
        if classification not in NAMED_DEFINITION_CLASSIFICATIONS:
            return "named definition review item has an invalid classification"
        used_as_evidence = item.get("used_as_source_conclusion_evidence")
        if not isinstance(used_as_evidence, bool):
            return (
                "named definition review item has no Boolean "
                "used_as_source_conclusion_evidence"
            )
        if classification == "self_characterizing" and used_as_evidence:
            return (
                "self-characterizing definition cannot justify a source conclusion; "
                "require runner-derived provenance or a preservation/refinement bridge"
            )

    # This is deliberately keyed by the pinned source item's semantic kind
    # (see the caller), not by a declaration name.  It is separate from the
    # recursive named-definition expansion above: that expansion asks what a
    # Lean wrapper means, while this review asks whether the source *defined
    # object* has been extended, totalized, or stripped of an advertised
    # operational property.
    source_definition_review = raw.get("source_definition_semantics_review")
    if require_source_definition_semantics_review and not isinstance(
        source_definition_review, dict
    ):
        return (
            "source-expression route lacks "
            "source_definition_semantics_review"
        )
    if source_definition_review is not None:
        if not isinstance(source_definition_review, dict):
            return "source_definition_semantics_review is not an object"
        source_ids, error = obligation_id_list(
            source_definition_review.get("source_obligation_ids"),
            "source_definition_semantics_review source_obligation_ids",
            source_obligations,
            nonempty=True,
        )
        if error:
            return error
        lean_ids, error = obligation_id_list(
            source_definition_review.get("lean_obligation_ids"),
            "source_definition_semantics_review lean_obligation_ids",
            lean_obligations,
            nonempty=True,
        )
        if error:
            return error
        # A source-facing definition review must cover the full visible
        # interface.  Reviewing just its result lets a hidden domain premise
        # or an instance-carried domain restriction escape the comparison.
        if source_ids != set(source_obligations):
            return (
                "source_definition_semantics_review does not cover every "
                "source obligation"
            )
        if lean_ids != set(lean_obligations):
            return (
                "source_definition_semantics_review does not cover every "
                "Lean obligation"
            )

        for source_field, lean_field, relation_field, label in (
            (
                "source_legal_domain",
                "lean_legal_domain",
                "domain_relation",
                "legal domain",
            ),
            (
                "source_outside_domain_behavior",
                "lean_outside_domain_behavior",
                "outside_domain_relation",
                "outside-domain/totalization behavior",
            ),
            (
                "source_operational_semantics",
                "lean_operational_semantics",
                "operational_relation",
                "operational meaning",
            ),
        ):
            if not substantive(source_definition_review.get(source_field)):
                return (
                    "source_definition_semantics_review lacks substantive source "
                    f"{label}"
                )
            if not substantive(source_definition_review.get(lean_field)):
                return (
                    "source_definition_semantics_review lacks substantive Lean "
                    f"{label}"
                )
            relation = required_string(
                source_definition_review.get(relation_field)
            ).lower()
            if relation not in SOURCE_DEFINITION_SEMANTIC_RELATIONS:
                return (
                    "source_definition_semantics_review has invalid "
                    f"{relation_field}"
                )
            if verdict == "matches" and relation != "equivalent":
                return (
                    "matches judgment records non-equivalent source-definition "
                    f"{label}"
                )

        property_status = required_string(
            source_definition_review.get("advertised_property_status")
        ).lower()
        if property_status not in SOURCE_DEFINITION_PROPERTY_STATUSES:
            return (
                "source_definition_semantics_review has invalid "
                "advertised_property_status"
            )
        properties = source_definition_review.get("advertised_properties")
        if not isinstance(properties, list):
            return "source_definition_semantics_review has no advertised_properties list"
        if property_status == "no_advertised_properties":
            if properties:
                return (
                    "no_advertised_properties status cannot carry advertised "
                    "property entries"
                )
            if not substantive(
                source_definition_review.get("no_advertised_properties_basis")
            ):
                return (
                    "source_definition_semantics_review lacks substantive "
                    "no_advertised_properties_basis"
                )
        elif not properties:
            return (
                "properties_reviewed source-definition status requires at least "
                "one advertised property"
            )

        seen_property_ids: set[str] = set()
        conclusion_ids = {
            key for key, kind in lean_obligations.items() if kind == "conclusion"
        }
        source_conclusion_ids = {
            key for key, kind in source_obligations.items() if kind == "conclusion"
        }
        for property_item in properties:
            if not isinstance(property_item, dict):
                return "source-definition advertised property is not an object"
            property_id = required_string(property_item.get("id"))
            if not property_id or property_id in seen_property_ids:
                return "source-definition advertised property has a missing or duplicate id"
            seen_property_ids.add(property_id)
            for field, label in (
                ("source_property", "source property"),
                ("lean_realization", "Lean realization"),
                ("evidence_basis", "evidence basis"),
            ):
                if not substantive(property_item.get(field)):
                    return (
                        "source-definition advertised property lacks substantive "
                        f"{label}"
                    )
            property_source_ids, error = obligation_id_list(
                property_item.get("source_obligation_ids"),
                "source-definition advertised property source_obligation_ids",
                source_obligations,
                nonempty=True,
            )
            if error:
                return error
            property_lean_ids, error = obligation_id_list(
                property_item.get("lean_obligation_ids"),
                "source-definition advertised property lean_obligation_ids",
                lean_obligations,
                nonempty=True,
            )
            if error:
                return error
            if not (property_source_ids & source_conclusion_ids):
                return (
                    "source-definition advertised property is not bound to a "
                    "source conclusion obligation"
                )
            if not (property_lean_ids & conclusion_ids):
                return (
                    "source-definition advertised property is not bound to a "
                    "Lean conclusion obligation"
                )
            relation = required_string(property_item.get("relation")).lower()
            if relation not in SOURCE_DEFINITION_SEMANTIC_RELATIONS:
                return "source-definition advertised property has an invalid relation"
            if verdict == "matches" and relation != "equivalent":
                return (
                    "matches judgment records a non-equivalent source-definition "
                    "advertised property"
                )
            evidence_kind = required_string(
                property_item.get("lean_evidence_kind")
            ).lower()
            if evidence_kind not in SOURCE_DEFINITION_PROPERTY_EVIDENCE_KINDS:
                return (
                    "source-definition advertised property has an invalid "
                    "lean_evidence_kind"
                )
            if verdict == "matches" and evidence_kind == "missing":
                return (
                    "matches judgment has an advertised source-definition property "
                    "without Lean evidence"
                )
            if evidence_kind in {
                "paper_interface_equivalence",
                "paper_interface_conclusion",
            }:
                evidence_conclusion_id = required_string(
                    property_item.get("lean_evidence_conclusion_id")
                )
                if evidence_conclusion_id not in conclusion_ids:
                    return (
                        "source-definition advertised property paper-interface evidence "
                        "is not a Lean conclusion obligation"
                    )
                if evidence_conclusion_id not in property_lean_ids:
                    return (
                        "source-definition advertised property paper-interface evidence "
                        "is not bound to its Lean obligations"
                    )
                if (
                    evidence_kind == "paper_interface_equivalence"
                    and not lean_conclusion_exposes_equivalence(evidence_conclusion_id)
                ):
                    return (
                        "source-definition advertised property equivalence evidence "
                        "does not explicitly contain equality or iff"
                    )
            elif evidence_kind == "expanded_definition_body":
                if not any(
                    (lean_manifest_atoms.get(obligation_id) or {})
                    .get("canonical", {})
                    .get("tag")
                    == "definition"
                    for obligation_id in property_lean_ids & conclusion_ids
                ):
                    return (
                        "source-definition advertised property claims expanded "
                        "definition-body evidence without a definition-valued Lean conclusion"
                    )

    numeric_review = raw.get("numeric_semantics_review")
    if not isinstance(numeric_review, dict):
        return "semantic scope review has no numeric_semantics_review object"
    formulas_present = numeric_review.get("formulas_present")
    if not isinstance(formulas_present, bool):
        return "numeric_semantics_review has no Boolean formulas_present"
    numeric_items = numeric_review.get("items")
    if not isinstance(numeric_items, list):
        return "numeric_semantics_review has no items list"
    if formulas_present != bool(numeric_items):
        return "numeric_semantics_review presence flag does not match its items"
    if not formulas_present and not substantive(numeric_review.get("absence_basis")):
        return "numeric_semantics_review lacks a substantive absence_basis"
    coverage_error = operator_review_coverage_error(
        numeric_review,
        numeric_items,
        source_item_field="source_obligation_ids",
        lean_item_field="lean_obligation_ids",
        non_source_field="non_numeric_source_obligation_ids",
        non_lean_field="non_numeric_lean_obligation_ids",
        label="numeric semantics",
        lean_absence_conflict=lean_atom_has_numeric_semantics,
    )
    if coverage_error:
        return coverage_error
    conclusion_ids = {
        key for key, kind in lean_obligations.items() if kind == "conclusion"
    }
    seen_numeric_item_ids: set[str] = set()
    for item in numeric_items:
        if not isinstance(item, dict):
            return "numeric semantics review item is not an object"
        item_id = required_string(item.get("id"))
        if not item_id or item_id in seen_numeric_item_ids:
            return "numeric semantics review item has a missing or duplicate id"
        seen_numeric_item_ids.add(item_id)
        if not required_string(item.get("source_expression")):
            return "numeric semantics review item has no source_expression"
        if not required_string(item.get("lean_expression")):
            return "numeric semantics review item has no lean_expression"
        for field, label in (
            ("source_domain", "source domain"),
            ("lean_domain", "Lean domain"),
            ("source_operations", "source operations"),
            ("lean_operations", "Lean operations"),
            ("source_coercions", "source coercion review"),
            ("lean_coercions", "Lean coercion review"),
            ("source_division", "source division convention"),
            ("lean_division", "Lean division convention"),
            ("source_rounding", "source rounding behavior"),
            ("lean_rounding", "Lean rounding behavior"),
            ("source_normalization", "source normalization"),
            ("lean_normalization", "Lean normalization"),
            ("source_strictness", "source strictness"),
            ("lean_strictness", "Lean strictness"),
            ("source_zero_denominator", "source zero-denominator behavior"),
            ("lean_zero_denominator", "Lean zero-denominator behavior"),
            ("relation_basis", "relation basis"),
        ):
            if not substantive(item.get(field)):
                return f"numeric semantics review item lacks a substantive {label}"
        relation = required_string(item.get("relation")).lower()
        if relation not in NUMERIC_SEMANTIC_RELATIONS:
            return "numeric semantics review item has an invalid relation"
        if relation in {"proved_equivalent", "witness_specific_equivalent"}:
            conclusion_id = required_string(
                item.get("lean_equivalence_conclusion_id")
            )
            if conclusion_id not in conclusion_ids:
                return (
                    "numeric semantics equivalence is not exposed by a Lean "
                    "conclusion obligation"
                )
            if conclusion_id not in set(item.get("lean_obligation_ids") or []):
                return (
                    "numeric semantics equivalence conclusion is not bound to the "
                    "reviewed Lean obligations"
                )
            if not lean_conclusion_exposes_equivalence(conclusion_id):
                return (
                    "numeric semantics equivalence conclusion does not explicitly "
                    "contain equality or iff"
                )
            if not substantive(item.get("lean_equivalence_statement")):
                return "numeric semantics equivalence lacks its explicit Lean statement"
        if verdict == "matches" and relation not in {
            "definitionally_equal",
            "proved_equivalent",
        }:
            return (
                "matches judgment records non-equivalent or witness-only numeric semantics"
            )

    discrete_review = raw.get("discrete_semantics_review")
    if not isinstance(discrete_review, dict):
        return "semantic scope review has no discrete_semantics_review object"
    operations_present = discrete_review.get("operations_present")
    if not isinstance(operations_present, bool):
        return "discrete_semantics_review has no Boolean operations_present"
    discrete_items = discrete_review.get("items")
    if not isinstance(discrete_items, list):
        return "discrete_semantics_review has no items list"
    if operations_present != bool(discrete_items):
        return "discrete_semantics_review presence flag does not match its items"
    if not operations_present and not substantive(discrete_review.get("absence_basis")):
        return "discrete_semantics_review lacks a substantive absence_basis"
    coverage_error = operator_review_coverage_error(
        discrete_review,
        discrete_items,
        source_item_field="source_obligation_ids",
        lean_item_field="lean_obligation_ids",
        non_source_field="non_discrete_source_obligation_ids",
        non_lean_field="non_discrete_lean_obligation_ids",
        label="discrete semantics",
        lean_absence_conflict=lean_atom_has_discrete_semantics,
    )
    if coverage_error:
        return coverage_error
    seen_discrete_item_ids: set[str] = set()
    for item in discrete_items:
        if not isinstance(item, dict):
            return "discrete semantics review item is not an object"
        item_id = required_string(item.get("id"))
        if not item_id or item_id in seen_discrete_item_ids:
            return "discrete semantics review item has a missing or duplicate id"
        seen_discrete_item_ids.add(item_id)
        if not required_string(item.get("source_expression")):
            return "discrete semantics review item has no source_expression"
        if not required_string(item.get("lean_expression")):
            return "discrete semantics review item has no lean_expression"
        for field, label in (
            ("source_domain", "source domain"),
            ("lean_domain", "Lean domain"),
            ("source_operation", "source operation"),
            ("lean_operation", "Lean operation"),
            ("source_order_sensitivity", "source order sensitivity"),
            ("lean_order_sensitivity", "Lean order sensitivity"),
            ("relation_basis", "relation basis"),
        ):
            if not substantive(item.get(field)):
                return f"discrete semantics review item lacks a substantive {label}"
        relation = required_string(item.get("relation")).lower()
        if relation not in DISCRETE_SEMANTIC_RELATIONS:
            return "discrete semantics review item has an invalid relation"
        if relation in {"proved_equivalent", "witness_specific_equivalent"}:
            conclusion_id = required_string(
                item.get("lean_equivalence_conclusion_id")
            )
            if conclusion_id not in conclusion_ids:
                return (
                    "discrete semantics equivalence is not exposed by a Lean "
                    "conclusion obligation"
                )
            if conclusion_id not in set(item.get("lean_obligation_ids") or []):
                return (
                    "discrete semantics equivalence conclusion is not bound to the "
                    "reviewed Lean obligations"
                )
            if not lean_conclusion_exposes_equivalence(conclusion_id):
                return (
                    "discrete semantics equivalence conclusion does not explicitly "
                    "contain equality or iff"
                )
            if not substantive(item.get("lean_equivalence_statement")):
                return "discrete semantics equivalence lacks its explicit Lean statement"
        if verdict == "matches" and relation not in {
            "definitionally_equal",
            "proved_equivalent",
        }:
            return (
                "matches judgment records non-equivalent or witness-only discrete semantics"
            )

    algorithm_review = raw.get("algorithm_review")
    if not isinstance(algorithm_review, dict):
        return "semantic scope review has no algorithm_review object"
    source_level = required_string(algorithm_review.get("source_claim_level")).lower()
    lean_level = required_string(algorithm_review.get("lean_claim_level")).lower()
    runner_provenance = required_string(
        algorithm_review.get("runner_provenance")
    ).lower()
    result_provenance = required_string(
        algorithm_review.get("result_provenance")
    ).lower()
    if source_level not in SOURCE_ALGORITHM_CLAIM_LEVELS:
        return "algorithm review has an invalid source_claim_level"
    if lean_level not in LEAN_ALGORITHM_CLAIM_LEVELS:
        return "algorithm review has an invalid lean_claim_level"
    if runner_provenance not in RUNNER_PROVENANCE_KINDS:
        return "algorithm review has an invalid runner_provenance"
    if result_provenance not in RESULT_PROVENANCE_KINDS:
        return "algorithm review has an invalid result_provenance"
    if not substantive(algorithm_review.get("source_claim_basis")):
        return "algorithm review lacks a substantive source_claim_basis"
    if not substantive(algorithm_review.get("lean_claim_basis")):
        return "algorithm review lacks a substantive lean_claim_basis"

    fidelity_error = fidelity_risk_review_error(
        raw.get("fidelity_risk_review"),
        source_obligations,
        lean_obligations,
        verdict,
        source_level,
    )
    if fidelity_error:
        return fidelity_error

    worlds = raw.get("semantic_worlds")
    if not isinstance(worlds, list) or not worlds:
        return "semantic scope review has no semantic_worlds"
    world_roles: dict[str, str] = {}
    for world in worlds:
        if not isinstance(world, dict):
            return "semantic world is not an object"
        world_id = required_string(world.get("id"))
        role = required_string(world.get("role")).lower()
        if not world_id or world_id in world_roles:
            return "semantic world has a missing or duplicate id"
        if role not in SEMANTIC_WORLD_ROLES:
            return f"semantic world `{world_id}` has an invalid role"
        if not substantive(world.get("semantics")):
            return f"semantic world `{world_id}` lacks substantive semantics"
        world_roles[world_id] = role
    if "shared" not in set(world_roles.values()) and not {
        "source",
        "lean",
    }.issubset(set(world_roles.values())):
        return "semantic worlds do not identify shared semantics or both source and Lean worlds"

    bridges = raw.get("world_bridges")
    if not isinstance(bridges, list):
        return "semantic scope review has no world_bridges list"
    normalized_bridges: list[dict[str, str]] = []
    for bridge in bridges:
        if not isinstance(bridge, dict):
            return "semantic world bridge is not an object"
        from_world = required_string(bridge.get("from_world"))
        to_world = required_string(bridge.get("to_world"))
        relation = required_string(bridge.get("relation")).lower()
        statement = required_string(bridge.get("statement"))
        conclusion_id = required_string(bridge.get("lean_conclusion_id"))
        if (
            from_world not in world_roles
            or to_world not in world_roles
            or from_world == to_world
        ):
            return "semantic world bridge has invalid endpoints"
        if relation not in SEMANTIC_WORLD_BRIDGE_RELATIONS:
            return "semantic world bridge has an invalid relation"
        if not substantive(statement):
            return "semantic world bridge lacks a substantive mathematical statement"
        if conclusion_id not in conclusion_ids:
            return "semantic world bridge is not exposed by a Lean conclusion obligation"
        normalized_bridges.append(
            {
                "from": from_world,
                "to": to_world,
                "relation": relation,
                "statement": statement,
            }
        )

    if verdict != "matches":
        return ""

    source_worlds = {
        key for key, role in world_roles.items() if role in {"source", "shared"}
    }
    lean_worlds = {
        key for key, role in world_roles.items() if role in {"lean", "shared"}
    }

    def has_bridge(relations: set[str], expected_statement: str = "") -> bool:
        return any(
            bridge["from"] in source_worlds
            and bridge["to"] in lean_worlds
            and bridge["from"] != bridge["to"]
            and bridge["relation"] in relations
            and (not expected_statement or bridge["statement"] == expected_statement)
            for bridge in normalized_bridges
        )

    separate_worlds = "shared" not in set(world_roles.values())

    def separate_worlds_bridge_error() -> str:
        if not separate_worlds:
            return ""
        if not has_bridge(
            {"definitionally_equal", "equivalent", "refines", "simulates"}
        ):
            return (
                "separate source and Lean semantic worlds have no exposed equality, "
                "equivalence, refinement, or simulation bridge"
            )
        if not has_bridge(
            {"definitionally_equal", "equivalent", "preserves_result"}
        ):
            return (
                "separate source and Lean semantic worlds have no exposed "
                "result-preservation bridge"
            )
        return ""

    compatible_lean_levels = {
        "not_algorithmic": {"not_algorithmic"},
        "existence": {"existence", "noncomputable_existence"},
        "executable": {"executable"},
        "polynomial_time": {"polynomial_time"},
    }
    if lean_level not in compatible_lean_levels[source_level]:
        return (
            "matches judgment conflates noncomputable existence, executable output, "
            "and polynomial-time claims"
        )

    if source_level == "not_algorithmic":
        if runner_provenance != "not_applicable" or result_provenance != "not_applicable":
            return "non-algorithmic row records algorithm runner/result provenance"
        world_error = separate_worlds_bridge_error()
        if world_error:
            return world_error
        return ""

    if source_level == "existence":
        if runner_provenance not in {
            "not_applicable",
            "same_formalized_runner",
            "proved_refinement",
        }:
            return "existence-only match records unsupported runner refinement"
        if result_provenance not in {
            "not_applicable",
            "runner_derived",
            "preservation_bridge",
        }:
            return "existence-only match records unsupported result provenance"
        world_error = separate_worlds_bridge_error()
        if world_error:
            return world_error
        if runner_provenance == "same_formalized_runner" and separate_worlds:
            return "same runner provenance has no shared semantic world"
        if runner_provenance == "proved_refinement":
            if result_provenance != "preservation_bridge":
                return (
                    "a cross-world existence refinement needs an exposed "
                    "result-preservation bridge"
                )
        else:
            return ""

    if runner_provenance in {"independent_characterization", "missing", "not_applicable"}:
        return (
            "algorithmic match lacks source-runner provenance; an independent "
            "characterization is not a refinement"
        )
    if result_provenance in {"independent_characterization", "missing", "not_applicable"}:
        return (
            "algorithmic match lacks runner-derived result provenance or an exposed "
            "preservation bridge"
        )

    if result_provenance == "runner_derived":
        if not substantive(algorithm_review.get("runner_result_statement")):
            return "runner-derived result provenance lacks a substantive result statement"
        runner_result_id = required_string(
            algorithm_review.get("runner_result_lean_conclusion_id")
        )
        if runner_result_id not in conclusion_ids:
            return "runner-derived result is not exposed by a Lean conclusion obligation"

    if runner_provenance == "proved_refinement":
        if result_provenance != "preservation_bridge":
            return (
                "a refined source runner needs an exposed result-preservation bridge; "
                "success of the Lean runner alone is insufficient"
            )
        statement = required_string(algorithm_review.get("refinement_statement"))
        if not substantive(statement):
            return "proved runner refinement lacks a substantive refinement statement"
        if not has_bridge(
            {"definitionally_equal", "refines", "simulates", "equivalent"},
            statement,
        ):
            return "proved runner refinement has no exposed source-to-Lean world bridge"
    elif runner_provenance == "same_formalized_runner":
        if "shared" not in set(world_roles.values()):
            return "same runner provenance has no shared semantic world"

    if result_provenance == "preservation_bridge":
        statement = required_string(
            algorithm_review.get("result_preservation_statement")
        )
        if not substantive(statement):
            return "result preservation provenance lacks a substantive bridge statement"
        if not has_bridge(
            {"definitionally_equal", "preserves_result", "equivalent"}, statement
        ):
            return "result preservation is not exposed as a source-to-Lean world bridge"

    if source_level == "polynomial_time":
        if not substantive(algorithm_review.get("complexity_statement")):
            return "polynomial-time match has no substantive complexity statement"
        if not substantive(algorithm_review.get("arithmetic_model")):
            return "polynomial-time match has no explicit arithmetic/representation model"
        complexity_id = required_string(
            algorithm_review.get("complexity_lean_conclusion_id")
        )
        if complexity_id not in conclusion_ids:
            return "polynomial-time claim is not exposed by a Lean conclusion obligation"
    return ""


def semantic_obligation_ledger_error(
    raw: Any,
    signature_manifest: dict[str, Any] | None = None,
    *,
    require_source_definition_semantics_review: bool = False,
) -> str:
    """Validate the atom-by-atom source/Lean comparison behind a judgment.

    Declaration names and prose similarity are not evidence that a theorem's
    assumptions and conclusions agree. A v10 statement judgment therefore
    carries explicit semantic obligations and relations between them. It also
    requires an exact partition of the binder-name-independent atoms extracted
    from the elaborated Lean type. This is a structural fail-closed check; an
    independent reviewer still has to judge whether the recorded formulas and
    implications are mathematically right.
    """

    if not isinstance(raw, dict):
        return "judgment is not an object"
    source = raw.get("source_obligations")
    lean = raw.get("lean_obligations")
    alignment = raw.get("obligation_alignment")
    if not isinstance(source, list) or not isinstance(lean, list):
        return "missing source_obligations/lean_obligations lists"
    if not isinstance(alignment, list):
        return "missing obligation_alignment list"

    if not isinstance(signature_manifest, dict):
        return "Lean declaration manifest is unavailable"
    manifest_digest = str(signature_manifest.get("sha256") or "").strip()
    recorded_manifest_digest = str(raw.get("lean_signature_sha256") or "").strip()
    if not manifest_digest:
        return "Lean declaration manifest has no canonical digest"
    if signature_manifest_digest(signature_manifest) != manifest_digest:
        return "Lean declaration manifest canonical digest is invalid"
    if not recorded_manifest_digest:
        return "judgment has no `lean_signature_sha256`"
    if recorded_manifest_digest != manifest_digest:
        return "judgment Lean declaration manifest digest is stale"
    manifest_atoms = signature_manifest.get("atoms")
    if not isinstance(manifest_atoms, list) or not manifest_atoms:
        return "Lean declaration manifest has no atoms"
    manifest_roles: dict[str, str] = {}
    manifest_atom_digests: dict[str, str] = {}
    manifest_atoms_by_ref: dict[str, dict[str, Any]] = {}
    for atom in manifest_atoms:
        if not isinstance(atom, dict):
            return "Lean declaration manifest atom is not an object"
        ref = str(atom.get("ref") or "").strip()
        role = str(atom.get("role") or "").strip().lower()
        if not ref or ref in manifest_roles:
            return "Lean declaration manifest has a missing/duplicate atom ref"
        if role not in {"parameter", "assumption", "conclusion"}:
            return f"Lean declaration manifest atom `{ref}` has invalid role"
        manifest_roles[ref] = role
        manifest_atoms_by_ref[ref] = atom
        atom_digest = signature_manifest_atom_digest(atom)
        if not atom_digest:
            return f"Lean declaration manifest atom `{ref}` has no canonical digest"
        manifest_atom_digests[ref] = atom_digest

    def required_string(value: Any) -> str:
        return value.strip() if isinstance(value, str) else ""

    def obligation_index(values: list[Any], side: str) -> tuple[dict[str, str], str]:
        out: dict[str, str] = {}
        for value in values:
            if not isinstance(value, dict):
                return {}, f"{side} obligation is not an object"
            key = required_string(value.get("id"))
            kind = required_string(value.get("kind")).lower()
            if not key or key in out:
                return {}, f"{side} obligation has a missing/duplicate id"
            if kind not in {"parameter", "assumption", "conclusion"}:
                return {}, f"{side} obligation `{key}` has invalid kind"
            if side == "source":
                statement = required_string(value.get("statement"))
                if not statement:
                    return {}, f"source obligation `{key}` has no semantic statement"
                source_location = required_string(value.get("source_location"))
                if not source_location:
                    return {}, f"source obligation `{key}` has no source location"
                if not EXACT_SOURCE_LOCATOR_RE.search(source_location):
                    return {}, f"source obligation `{key}` has no exact source locator"
            elif "statement" in value:
                return {}, (
                    f"Lean obligation `{key}` supplies unaudited prose in `statement`; "
                    "v7 binds it only through signature_ref/signature_atom_sha256"
                )
            out[key] = kind
        if not any(kind == "conclusion" for kind in out.values()):
            return {}, f"{side} ledger has no conclusion"
        return out, ""

    source_index, error = obligation_index(source, "source")
    if error:
        return error
    lean_index, error = obligation_index(lean, "Lean")
    if error:
        return error

    covered_manifest_refs: dict[str, str] = {}
    lean_manifest_atoms: dict[str, dict[str, Any]] = {}
    for value in lean:
        key = required_string(value.get("id"))
        ref = required_string(value.get("signature_ref"))
        if not ref:
            return f"Lean obligation `{key}` has no `signature_ref`"
        if ref not in manifest_roles:
            return f"Lean obligation `{key}` references unknown signature atom `{ref}`"
        if ref in covered_manifest_refs:
            return f"Lean signature atom `{ref}` is referenced by multiple obligations"
        if lean_index[key] != manifest_roles[ref]:
            return f"Lean obligation `{key}` kind does not match signature atom `{ref}` role"
        recorded_atom_digest = required_string(value.get("signature_atom_sha256"))
        if not recorded_atom_digest:
            return f"Lean obligation `{key}` has no `signature_atom_sha256`"
        if recorded_atom_digest != manifest_atom_digests[ref]:
            return f"Lean obligation `{key}` signature atom digest is stale"
        covered_manifest_refs[ref] = key
        lean_manifest_atoms[key] = manifest_atoms_by_ref[ref]
    missing_manifest_refs = set(manifest_roles) - set(covered_manifest_refs)
    if missing_manifest_refs:
        return "Lean obligations omit signature atom(s): " + ", ".join(
            sorted(missing_manifest_refs)
        )

    aligned_source: set[str] = set()
    aligned_lean: set[str] = set()
    has_directional_alignment = False
    for value in alignment:
        if not isinstance(value, dict):
            return "obligation alignment entry is not an object"
        source_id = required_string(value.get("source_id"))
        lean_id = required_string(value.get("lean_id"))
        relation = required_string(value.get("relation")).lower()
        basis = required_string(value.get("semantic_basis"))
        bridge = required_string(value.get("bridge_statement"))
        if source_id not in source_index or lean_id not in lean_index:
            return "obligation alignment references an unknown id"
        if source_index[source_id] != lean_index[lean_id]:
            return "obligation alignment mixes assumption and conclusion kinds"
        if relation not in {"equivalent", "source_implies_lean", "lean_implies_source"}:
            return "obligation alignment has an invalid semantic relation"
        if not basis:
            return "obligation alignment lacks a semantic basis"
        if NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(basis):
            return "obligation alignment semantic_basis relies on names instead of semantics"
        if not bridge:
            return "obligation alignment lacks an explicit semantic bridge statement"
        if NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(bridge):
            return "obligation alignment bridge_statement relies on names instead of semantics"
        aligned_source.add(source_id)
        aligned_lean.add(lean_id)
        has_directional_alignment = has_directional_alignment or relation != "equivalent"

    source_conclusions = {
        key for key, kind in source_index.items() if kind == "conclusion"
    }
    source_inputs = {
        key for key, kind in source_index.items() if kind in {"parameter", "assumption"}
    }
    lean_inputs = {
        key for key, kind in lean_index.items() if kind in {"parameter", "assumption"}
    }
    lean_conclusions = {
        key for key, kind in lean_index.items() if kind == "conclusion"
    }
    missing_conclusions = source_conclusions - aligned_source
    missing_source_inputs = source_inputs - aligned_source
    unjustified_inputs = lean_inputs - aligned_lean
    missing_lean_conclusions = lean_conclusions - aligned_lean

    def recorded_gap_ids(field: str) -> tuple[set[str], str]:
        values = raw.get(field)
        if not isinstance(values, list):
            return set(), f"missing explicit `{field}` list"
        if any(not isinstance(value, str) or not value.strip() for value in values):
            return set(), f"`{field}` must contain nonempty obligation ids"
        normalized = [value.strip() for value in values]
        if len(normalized) != len(set(normalized)):
            return set(), f"`{field}` contains duplicate obligation ids"
        return set(normalized), ""

    unmatched, error = recorded_gap_ids("unmatched_source_conclusions")
    if error:
        return error
    unjustified, error = recorded_gap_ids("unjustified_lean_inputs")
    if error:
        return error
    if unmatched != missing_conclusions:
        return "`unmatched_source_conclusions` does not equal the unmatched source conclusion ids"
    unmatched_inputs, error = recorded_gap_ids("unmatched_source_inputs")
    if error:
        return error
    unmatched_lean_conclusions, error = recorded_gap_ids("unmatched_lean_conclusions")
    if error:
        return error
    if unmatched_inputs != missing_source_inputs:
        return "`unmatched_source_inputs` does not equal the unmatched source input ids"
    if unjustified != unjustified_inputs:
        return "`unjustified_lean_inputs` does not equal the unjustified Lean input ids"
    if unmatched_lean_conclusions != missing_lean_conclusions:
        return "`unmatched_lean_conclusions` does not equal the unmatched Lean conclusion ids"

    verdict = _normalize_llm_match_judgment(
        raw.get("judgment")
        or raw.get("verdict")
        or raw.get("status")
        or raw.get("matches")
    )
    resolution = _normalize_llm_match_resolution(
        raw.get("resolution")
        or raw.get("accepted_resolution")
        or raw.get("review_resolution")
    )
    # A visible-premise boundary may differ from the source only by its
    # explicitly recorded extra Lean inputs.  It must not use the mismatch
    # verdict to bypass checks for weakened quantification, computational
    # capability, runner provenance, or cross-world result preservation.
    scope_verdict = (
        "matches"
        if verdict == "matches"
        or (
            verdict == "mismatch"
            and resolution == CONDITIONAL_BOUNDARY_RESOLUTION
        )
        else verdict
    )
    scope_error = semantic_scope_review_error(
        raw.get("semantic_scope_review"),
        source_index,
        lean_index,
        lean_manifest_atoms,
        scope_verdict,
        require_source_definition_semantics_review=(
            require_source_definition_semantics_review
        ),
    )
    if scope_error:
        return scope_error
    semantic_scope = raw.get("semantic_scope_review")
    algorithm_review = (
        semantic_scope.get("algorithm_review")
        if isinstance(semantic_scope, dict)
        and isinstance(semantic_scope.get("algorithm_review"), dict)
        else {}
    )
    source_claim_level = str(
        algorithm_review.get("source_claim_level") or ""
    ).strip().lower()
    lean_claim_level = str(
        algorithm_review.get("lean_claim_level") or ""
    ).strip().lower()
    if (
        verdict == "matches"
        and source_claim_level == "polynomial_time"
        and lean_claim_level == "polynomial_time"
    ):
        complexity_error = operational_complexity_review_error(
            raw.get("operational_complexity_review"),
            str(
                algorithm_review.get("complexity_lean_conclusion_id") or ""
            ).strip(),
        )
        if complexity_error:
            return complexity_error
    all_gaps = unmatched | unmatched_inputs | unjustified | unmatched_lean_conclusions
    if verdict == "matches" and (all_gaps or has_directional_alignment):
        return "matches judgment records a semantic obligation gap"
    if verdict in {"mismatch", "uncertain"} and not (all_gaps or has_directional_alignment):
        return f"{verdict} judgment records no semantic obligation gap"
    return ""


def _is_conditional_boundary_judgment(judgment: dict[str, Any]) -> bool:
    """Return whether a mismatch has an audited visible-premise boundary."""

    alignment = judgment.get("obligation_alignment")
    relations_are_equivalent = (
        isinstance(alignment, list)
        and bool(alignment)
        and all(
            isinstance(item, dict)
            and str(item.get("relation") or "").strip().lower() == "equivalent"
            for item in alignment
        )
    )
    return (
        str(judgment.get("judgment") or "").strip() == "mismatch"
        and _normalize_llm_match_resolution(judgment.get("resolution"))
        == CONDITIONAL_BOUNDARY_RESOLUTION
        and not judgment.get("obligation_ledger_error")
        and not judgment.get("unmatched_source_conclusions")
        and not judgment.get("unmatched_source_inputs")
        and not judgment.get("unmatched_lean_conclusions")
        and relations_are_equivalent
        and bool(judgment.get("unjustified_lean_inputs"))
    )


def load_llm_statement_judgments(
    folder: Path,
    signature_manifests: dict[str, dict[str, Any]] | None = None,
    *,
    audit_inputs: DashboardAuditInputs | None = None,
) -> dict[str, dict[str, Any]]:
    """Load independent semantic judgments comparing paper text and Lean-to-TeX drafts."""

    if audit_inputs is not None:
        with dashboard_audit_input_scope(audit_inputs):
            return load_llm_statement_judgments(folder, signature_manifests)
    path = llm_statement_judgments_file(folder)
    if not _dashboard_is_file(path):
        return {}
    payload = _dashboard_json_payload(path)
    if payload is None:
        return {}
    if is_non_evidence_scaffold_payload(payload):
        # A scaffold is input provenance, not a semantic judgment.  Treat it
        # exactly like absent evidence until an independent reviewer clears it.
        return {}
    if payload.get("schema") != 1:
        return {}
    if payload.get("paper") not in {None, folder.name}:
        return {}
    items = payload.get("items")
    if not isinstance(items, dict):
        return {}
    out: dict[str, dict[str, Any]] = {}
    source = path.name
    payload_validator = str(
        payload.get("validator")
        or payload.get("model")
        or payload.get("judge")
        or payload.get("agent")
        or payload.get("generator")
        or source
    ).strip()
    payload_has_validator = bool(
        payload.get("validator")
        or payload.get("model")
        or payload.get("judge")
        or payload.get("agent")
        or payload.get("generator")
    )
    payload_validator_type = str(
        payload.get("validator_type")
        or payload.get("generator_type")
        or ("model" if payload.get("model") else "agent" if payload.get("judge") else "")
    ).strip()
    payload_validated_at = str(
        payload.get("validated_at")
        or payload.get("timestamp")
        or payload.get("generated_at")
        or ""
    ).strip()
    payload_has_validated_at = bool(payload_validated_at)
    payload_prompt_version = str(payload.get("prompt_version") or "").strip()
    payload_prompt_version_stale = not llm_prompt_version_is_semantically_current(
        payload_prompt_version,
        prompt_contracts=LLM_STATEMENT_PROMPT_SEMANTIC_CONTRACTS,
        required_contract=REQUIRED_LLM_STATEMENT_SEMANTIC_CONTRACT_VERSION,
    )
    payload_comment = str(
        payload.get("comment")
        or payload.get("notes")
        or payload.get("reason")
        or payload.get("explanation")
        or ""
    ).strip()
    require_source_routes = llm_statement_source_routes_required(folder)
    require_direct_expression_semantics_review = (
        llm_direct_expression_semantics_review_required(folder)
    )
    source_inventory = paper_statement_inventory(folder) if require_source_routes else {}
    # Component anchors are route-only inventory.  They must never enter the
    # named-result coverage selector, but a v10 formula-row judgment may use
    # one when the source map explicitly pins the smaller source claim.
    source_route_inventory = dict(source_inventory)
    if require_source_routes:
        source_route_inventory.update(paper_source_component_route_inventory(folder))
        source_route_inventory.update(
            paper_source_definition_component_route_inventory(folder)
        )
    manifests = signature_manifests or {}
    manifests_by_signature: dict[str, list[dict[str, Any]]] = {}
    seen_manifest_objects: dict[str, set[int]] = {}
    for manifest in manifests.values():
        if not isinstance(manifest, dict):
            continue
        signature = str(manifest.get("sha256") or "").strip().lower()
        if not re.fullmatch(r"[0-9a-f]{64}", signature):
            continue
        # The parser exposes the same manifest under both a short and a fully
        # qualified navigation name.  Collapse only those object aliases. Two
        # independently materialized declarations with the same semantic
        # signature remain ambiguous and therefore fail closed.
        object_id = id(manifest)
        if object_id in seen_manifest_objects.setdefault(signature, set()):
            continue
        seen_manifest_objects[signature].add(object_id)
        manifests_by_signature.setdefault(signature, []).append(manifest)
    for raw_name, raw_value in items.items():
        name = str(raw_name).strip()
        if not name:
            continue
        if isinstance(raw_value, dict):
            item_prompt_version = str(
                raw_value.get("prompt_version") or payload_prompt_version
            ).strip()
            item_prompt_version_stale = not llm_prompt_version_is_semantically_current(
                item_prompt_version,
                prompt_contracts=LLM_STATEMENT_PROMPT_SEMANTIC_CONTRACTS,
                required_contract=REQUIRED_LLM_STATEMENT_SEMANTIC_CONTRACT_VERSION,
            )
            raw_judgment = (
                raw_value.get("judgment")
                or raw_value.get("verdict")
                or raw_value.get("status")
                or raw_value.get("matches")
            )
            judgment = _normalize_llm_match_judgment(raw_judgment)
            reason = str(
                raw_value.get("reason")
                or raw_value.get("notes")
                or raw_value.get("explanation")
                or ""
            ).strip()
            validator = str(
                raw_value.get("validator")
                or raw_value.get("model")
                or raw_value.get("judge")
                or raw_value.get("agent")
                or raw_value.get("generator")
                or payload_validator
            ).strip()
            has_validator = bool(
                raw_value.get("validator")
                or raw_value.get("model")
                or raw_value.get("judge")
                or raw_value.get("agent")
                or raw_value.get("generator")
                or payload_has_validator
            )
            validator_type = str(
                raw_value.get("validator_type")
                or raw_value.get("generator_type")
                or ("model" if raw_value.get("model") else "agent" if raw_value.get("judge") else "")
                or payload_validator_type
            ).strip()
            validated_at = str(
                raw_value.get("validated_at")
                or raw_value.get("timestamp")
                or raw_value.get("generated_at")
                or payload_validated_at
            ).strip()
            has_validated_at = bool(
                raw_value.get("validated_at")
                or raw_value.get("timestamp")
                or raw_value.get("generated_at")
                or payload_has_validated_at
            )
            comment = str(
                raw_value.get("comment")
                or raw_value.get("notes")
                or raw_value.get("reason")
                or raw_value.get("explanation")
                or payload_comment
                or ""
            ).strip()
            resolution = _normalize_llm_match_resolution(
                raw_value.get("resolution")
                or raw_value.get("accepted_resolution")
                or raw_value.get("review_resolution")
            )
            boundary_type = str(
                raw_value.get("boundary_type")
                or raw_value.get("resolution_type")
                or raw_value.get("boundary_kind")
                or ""
            ).strip()
            boundary_names = _normalize_string_list(
                raw_value.get("boundary_names")
                or raw_value.get("boundaries")
                or raw_value.get("boundary_name")
            )
            conditional_premises = _normalize_string_list(
                raw_value.get("conditional_premises")
                or raw_value.get("extra_premises")
                or raw_value.get("conditional_on")
            )
            resolution_reason = str(
                raw_value.get("resolution_reason")
                or raw_value.get("boundary_reason")
                or raw_value.get("resolution_notes")
                or ""
            ).strip()
            # A stored row key is only a navigation locator.  When a sidecar
            # was mechanically rekeyed, recover its manifest solely from one
            # exact elaborated-signature digest; ambiguous matches remain
            # deliberately unbound and therefore fail the obligation ledger.
            signature_manifest = manifests.get(name)
            recorded_signature = str(
                raw_value.get("lean_signature_sha256") or ""
            ).strip().lower()
            if (
                signature_manifest is None
                and re.fullmatch(r"[0-9a-f]{64}", recorded_signature)
            ):
                matching_manifests = manifests_by_signature.get(
                    recorded_signature, []
                )
                if len(matching_manifests) == 1:
                    signature_manifest = matching_manifests[0]
            require_source_definition_semantics_review = bool(
                require_source_routes
                and direct_source_definition_route_keys(
                    raw_value,
                    inventory=source_route_inventory,
                    include_direct_expressions=(
                        require_direct_expression_semantics_review
                    ),
                )
            )
            obligation_ledger_error = semantic_obligation_ledger_error(
                raw_value,
                signature_manifest,
                require_source_definition_semantics_review=(
                    require_source_definition_semantics_review
                ),
            )
            source_route_error = (
                source_route_pin_error(
                    raw_value,
                    inventory=source_route_inventory,
                    require_statement_target=True,
                )
                if require_source_routes
                else ""
            )
            if source_route_error:
                obligation_ledger_error = (
                    f"{obligation_ledger_error}; {source_route_error}"
                    if obligation_ledger_error
                    else source_route_error
                )
            unmatched_source_conclusions = (
                list(raw_value.get("unmatched_source_conclusions"))
                if isinstance(raw_value.get("unmatched_source_conclusions"), list)
                else []
            )
            unjustified_lean_inputs = (
                list(raw_value.get("unjustified_lean_inputs"))
                if isinstance(raw_value.get("unjustified_lean_inputs"), list)
                else []
            )
            unmatched_source_inputs = (
                list(raw_value.get("unmatched_source_inputs"))
                if isinstance(raw_value.get("unmatched_source_inputs"), list)
                else []
            )
            unmatched_lean_conclusions = (
                list(raw_value.get("unmatched_lean_conclusions"))
                if isinstance(raw_value.get("unmatched_lean_conclusions"), list)
                else []
            )
            obligation_alignment = (
                list(raw_value.get("obligation_alignment"))
                if isinstance(raw_value.get("obligation_alignment"), list)
                else []
            )
            out[name] = {
                "judgment": judgment,
                "reason": reason,
                "source": source,
                "validator": validator,
                "validator_type": validator_type,
                "validated_at": validated_at,
                "metadata_missing": not bool(has_validator and has_validated_at),
                "comment": comment,
                "resolution": resolution,
                "boundary_type": boundary_type,
                "boundary_names": boundary_names,
                "conditional_premises": conditional_premises,
                "resolution_reason": resolution_reason,
                "obligation_ledger_error": obligation_ledger_error,
                "source_route_error": source_route_error,
                "source_route_validation_performed": bool(require_source_routes),
                "source_routes": (
                    raw_value.get("source_routes")
                    if isinstance(raw_value.get("source_routes"), list)
                    else []
                ),
                "unmatched_source_conclusions": unmatched_source_conclusions,
                "unmatched_source_inputs": unmatched_source_inputs,
                "unjustified_lean_inputs": unjustified_lean_inputs,
                "unmatched_lean_conclusions": unmatched_lean_conclusions,
                "obligation_alignment": obligation_alignment,
                "semantic_scope_review": (
                    raw_value.get("semantic_scope_review")
                    if isinstance(raw_value.get("semantic_scope_review"), dict)
                    else {}
                ),
                "prompt_version": item_prompt_version,
                "prompt_version_stale": item_prompt_version_stale,
                "lean_statement_sha256": str(raw_value.get("lean_statement_sha256") or "").strip(),
                "lean_signature_sha256": str(raw_value.get("lean_signature_sha256") or "").strip(),
                "paper_statement_sha256": str(raw_value.get("paper_statement_sha256") or "").strip(),
                "tex_statement_sha256": str(raw_value.get("tex_statement_sha256") or "").strip(),
            }
        else:
            judgment = _normalize_llm_match_judgment(raw_value)
            if judgment:
                out[name] = {
                    "judgment": judgment,
                    "reason": "",
                    "source": source,
                    "validator": payload_validator,
                    "validator_type": payload_validator_type,
                    "validated_at": payload_validated_at,
                    "metadata_missing": not bool(payload_has_validator and payload_has_validated_at),
                    "comment": payload_comment,
                    "resolution": "",
                    "boundary_type": "",
                    "boundary_names": [],
                    "conditional_premises": [],
                    "resolution_reason": "",
                    "obligation_ledger_error": "judgment row is not an object",
                    "unmatched_source_conclusions": [],
                    "unmatched_source_inputs": [],
                    "unjustified_lean_inputs": [],
                    "unmatched_lean_conclusions": [],
                    "obligation_alignment": [],
                    "semantic_scope_review": {},
                    "prompt_version": payload_prompt_version,
                    "prompt_version_stale": payload_prompt_version_stale,
                }
    return out


def _validated_unique_source_component_target_sha256(
    judgment: Mapping[str, Any],
) -> str:
    """Return one component target only after full source-route validation.

    The dashboard paper text may be an aggregate parent used for display.  A
    component-routed judgment instead reviews the exact entry-local component,
    but that narrower digest is trustworthy only when the generic source-route
    validator accepted the complete route and exactly one component route pins
    that target.  Route keys and declaration names are deliberately ignored.
    """

    if judgment.get("source_route_validation_performed") is not True:
        return ""
    if "source_route_error" not in judgment or str(
        judgment.get("source_route_error") or ""
    ).strip():
        return ""
    routes = judgment.get("source_routes")
    if not isinstance(routes, list):
        return ""
    recorded_target = str(
        judgment.get("paper_statement_sha256") or ""
    ).strip().lower()
    targets = [
        str(route.get("source_statement_sha256") or "").strip().lower()
        for route in routes
        if isinstance(route, Mapping)
        and str(route.get("route_kind") or "").strip().lower()
        == "source_component"
    ]
    matching_targets = [
        target
        for target in targets
        if target == recorded_target
        and SOURCE_ARTIFACT_SHA256_RE.fullmatch(target)
    ]
    if len(matching_targets) != 1:
        return ""
    return matching_targets[0]


def _llm_statement_judgment_is_stale(
    judgment: dict[str, Any],
    *,
    signature_sha256: str,
    lean_statement: str,
    paper_statement: str,
    agent_statement: str,
) -> bool:
    """Re-evaluate statement evidence against the current audit contract.

    The elaborated signature is necessary but not a substitute for the exact
    current declaration text.  Canonicalizer upgrades can preserve or rewrite
    a signature representation, and an old sidecar field must not make a newly
    added theorem premise look current merely because its source and TeX pins
    still match.
    """

    if not judgment:
        return False
    if not normalize_statement(paper_statement):
        return True
    recorded_signature = str(judgment.get("lean_signature_sha256") or "").strip()
    recorded_lean = str(judgment.get("lean_statement_sha256") or "").strip()
    recorded_paper = str(judgment.get("paper_statement_sha256") or "").strip()
    recorded_tex = str(judgment.get("tex_statement_sha256") or "").strip()
    component_target = _validated_unique_source_component_target_sha256(judgment)
    paper_digest_is_current = recorded_paper == statement_digest(
        paper_statement
    ) or bool(component_target and recorded_paper == component_target)
    return (
        not recorded_signature
        or not recorded_lean
        or not recorded_paper
        or not recorded_tex
        or recorded_signature != signature_sha256
        or recorded_lean != statement_digest(lean_statement)
        or not paper_digest_is_current
        or recorded_tex != statement_digest(agent_statement)
        or bool(judgment.get("prompt_version_stale"))
        or bool(judgment.get("metadata_missing"))
        or bool(judgment.get("obligation_ledger_error"))
        or not signature_sha256
    )


def _semantic_statement_judgment_identity(
    judgment: dict[str, Any],
) -> tuple[str, str, str] | None:
    """Return a judgment's exact semantic reuse identity, never its row name."""

    fields = (
        "lean_signature_sha256",
        "paper_statement_sha256",
        "tex_statement_sha256",
    )
    values = tuple(str(judgment.get(field) or "").strip().lower() for field in fields)
    if (
        not all(re.fullmatch(r"[0-9a-f]{64}", value) for value in values)
        or values[1] == statement_digest("")
    ):
        return None
    return values


def _semantic_statement_judgment_index(
    judgments: Mapping[str, dict[str, Any]],
) -> dict[tuple[str, str, str], list[tuple[str, dict[str, Any]]]]:
    """Index judgments once by exact content identity, preserving ambiguity."""

    index: dict[tuple[str, str, str], list[tuple[str, dict[str, Any]]]] = {}
    for key, judgment in judgments.items():
        identity = _semantic_statement_judgment_identity(judgment)
        if identity is not None:
            index.setdefault(identity, []).append((key, judgment))
    return index


def _current_semantic_statement_judgment_for_item(
    item: ReviewItem,
    judgments: dict[str, dict[str, Any]],
    *,
    identity_index: Mapping[
        tuple[str, str, str], list[tuple[str, dict[str, Any]]]
    ]
    | None = None,
) -> tuple[str, dict[str, Any] | None, bool]:
    """Resolve one current semantic judgment through exact content pins.

    The match deliberately ignores sidecar storage keys and Lean declaration
    spelling.  A key rename can be reused only when exactly one judgment has
    the current elaborated signature plus current source-facing and translated
    statement digests.  Multiple candidates are an ambiguity, not a reason to
    choose the familiar name.
    """

    return _current_semantic_statement_judgment(
        signature_sha256=item.lean_signature_sha256,
        lean_statement=item.lean_statement,
        paper_statement=item.paper_statement,
        agent_statement=item.agent_statement,
        judgments=judgments,
        identity_index=identity_index,
    )


def _current_semantic_statement_judgment(
    *,
    signature_sha256: str,
    lean_statement: str,
    paper_statement: str,
    agent_statement: str,
    judgments: dict[str, dict[str, Any]],
    identity_index: Mapping[
        tuple[str, str, str], list[tuple[str, dict[str, Any]]]
    ]
    | None = None,
) -> tuple[str, dict[str, Any] | None, bool]:
    """Resolve one judgment before or after a ``ReviewItem`` is materialized."""

    signature = str(signature_sha256 or "").strip().lower()
    identity = (
        signature,
        statement_digest(paper_statement),
        statement_digest(agent_statement),
    )
    if not re.fullmatch(r"[0-9a-f]{64}", signature):
        return "", None, False
    identity_candidates = (
        identity_index.get(identity, [])
        if identity_index is not None
        else [
            (key, judgment)
            for key, judgment in judgments.items()
            if _semantic_statement_judgment_identity(judgment) == identity
        ]
    )
    if not identity_candidates:
        translated_digest = statement_digest(agent_statement)
        identity_candidates = [
            (key, judgment)
            for key, judgment in judgments.items()
            if str(judgment.get("lean_signature_sha256") or "")
            .strip()
            .lower()
            == signature
            and str(judgment.get("tex_statement_sha256") or "")
            .strip()
            .lower()
            == translated_digest
            and bool(_validated_unique_source_component_target_sha256(judgment))
        ]
    candidates = [
        (key, judgment)
        for key, judgment in identity_candidates
        if not _llm_statement_judgment_is_stale(
            judgment,
            signature_sha256=signature_sha256,
            lean_statement=lean_statement,
            paper_statement=paper_statement,
            agent_statement=agent_statement,
        )
    ]
    if len(candidates) == 1:
        return candidates[0][0], candidates[0][1], False
    return "", None, len(candidates) > 1


def load_llm_paper_coverage_audit(
    folder: Path,
    *,
    audit_inputs: DashboardAuditInputs | None = None,
) -> dict[str, Any]:
    """Load optional LLM audit of source-paper statement coverage by review rows."""

    if audit_inputs is not None:
        with dashboard_audit_input_scope(audit_inputs):
            return load_llm_paper_coverage_audit(folder)
    path = llm_paper_coverage_file(folder)
    if not _dashboard_is_file(path):
        return {}
    payload = _dashboard_json_payload(path)
    if payload is None:
        return {}
    payload_non_evidence_scaffold = is_non_evidence_scaffold_payload(payload)
    if payload.get("schema") != 1:
        return {}
    if payload.get("paper") not in {None, folder.name}:
        return {}
    raw_items = payload.get("items")
    if not isinstance(raw_items, dict):
        raw_items = {}
    items: dict[str, dict[str, Any]] = {}
    payload_validator = str(
        payload.get("validator")
        or payload.get("model")
        or payload.get("judge")
        or payload.get("agent")
        or payload.get("generator")
        or path.name
    ).strip()
    payload_has_validator = bool(
        payload.get("validator")
        or payload.get("model")
        or payload.get("judge")
        or payload.get("agent")
        or payload.get("generator")
    )
    payload_validator_type = str(
        payload.get("validator_type")
        or payload.get("generator_type")
        or ("model" if payload.get("model") else "agent" if payload.get("judge") else "")
    ).strip()
    payload_validated_at = str(
        payload.get("validated_at")
        or payload.get("timestamp")
        or payload.get("generated_at")
        or ""
    ).strip()
    payload_has_validated_at = bool(payload_validated_at)
    payload_audit_kind = str(
        payload.get("audit_kind")
        or payload.get("coverage_audit_kind")
        or payload.get("kind")
        or ""
    ).strip()
    payload_prompt_version = str(payload.get("prompt_version") or "").strip()
    payload_prompt_version_stale = (
        payload_prompt_version != REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION
    )
    payload_source_grounded = bool(payload.get("source_grounded") is True)
    payload_seed_scaffold = (
        payload_non_evidence_scaffold
        or bool(payload.get("seed_scaffold") is True)
        or payload_audit_kind in PAPER_COVERAGE_SCAFFOLD_KINDS
    )
    for raw_key, raw_value in raw_items.items():
        key = str(raw_key or "").strip()
        if not key:
            continue
        if isinstance(raw_value, dict):
            raw_judgment = (
                raw_value.get("coverage")
                or raw_value.get("judgment")
                or raw_value.get("verdict")
                or raw_value.get("status")
                or raw_value.get("covered")
            )
            items[key] = {
                "coverage": _normalize_paper_coverage_judgment(raw_judgment),
                "review_rows": _normalize_string_list(
                    raw_value.get("review_rows")
                    or raw_value.get("rows")
                    or raw_value.get("lean_rows")
                    or raw_value.get("declarations")
                ),
                "review_row_signature_sha256": _normalize_review_row_signature_pins(
                    raw_value.get("review_row_signature_sha256")
                ),
                "support_declarations": _normalize_string_list(
                    raw_value.get("support_declarations")
                    or raw_value.get("support_rows")
                    or raw_value.get("support_lean_declarations")
                    or raw_value.get("support_lean")
                ),
                "reason": str(
                    raw_value.get("reason")
                    or raw_value.get("notes")
                    or raw_value.get("explanation")
                    or ""
                ).strip(),
                "source_evidence": str(raw_value.get("source_evidence") or "").strip(),
                "source_scope_judgment": str(
                    raw_value.get("source_scope_judgment") or ""
                ).strip(),
                "source_anchor_quote_sha256": str(
                    raw_value.get("source_anchor_quote_sha256") or ""
                ).strip().lower(),
                "target_kind": str(raw_value.get("target_kind") or "").strip().lower(),
                "archival_statement_sha256": str(
                    raw_value.get("archival_statement_sha256") or ""
                ).strip().lower(),
                "corrected_target_sha256": str(
                    raw_value.get("corrected_target_sha256") or ""
                ).strip().lower(),
                "governing_defect_ids": _normalize_string_list(
                    raw_value.get("governing_defect_ids")
                ),
                "archival_equivalence_claimed": raw_value.get(
                    "archival_equivalence_claimed"
                ),
                "dashboard_evidence": str(
                    raw_value.get("dashboard_evidence")
                    or raw_value.get("lean_evidence")
                    or ""
                ).strip(),
                "statement_sha256": str(raw_value.get("statement_sha256") or "").strip(),
                "source_item_coverage_digest_schema": raw_value.get(
                    "source_item_coverage_digest_schema"
                ),
                "source_item_coverage_sha256": str(
                    raw_value.get("source_item_coverage_sha256") or ""
                ).strip().lower(),
                "validator": str(
                    raw_value.get("validator")
                    or raw_value.get("model")
                    or raw_value.get("judge")
                    or raw_value.get("agent")
                    or raw_value.get("generator")
                    or payload_validator
                ).strip(),
                "metadata_missing": not bool(
                    (
                        raw_value.get("validator")
                        or raw_value.get("model")
                        or raw_value.get("judge")
                        or raw_value.get("agent")
                        or raw_value.get("generator")
                        or payload_has_validator
                    )
                    and (
                        raw_value.get("validated_at")
                        or raw_value.get("timestamp")
                        or raw_value.get("generated_at")
                        or payload_has_validated_at
                    )
                ),
                "validator_type": str(
                    raw_value.get("validator_type")
                    or raw_value.get("generator_type")
                    or (
                        "model"
                        if raw_value.get("model")
                        else "agent"
                        if raw_value.get("judge")
                        else ""
                    )
                    or payload_validator_type
                ).strip(),
                "validated_at": str(
                    raw_value.get("validated_at")
                    or raw_value.get("timestamp")
                    or raw_value.get("generated_at")
                    or payload_validated_at
                ).strip(),
                "audit_kind": str(raw_value.get("audit_kind") or payload_audit_kind).strip(),
                "prompt_version": payload_prompt_version,
                "prompt_version_stale": payload_prompt_version_stale,
                "source_grounded": bool(
                    raw_value.get("source_grounded") is True or payload_source_grounded
                ),
                "seed_scaffold": bool(raw_value.get("seed_scaffold") is True or payload_seed_scaffold),
            }
        else:
            items[key] = {
                "coverage": _normalize_paper_coverage_judgment(raw_value),
                "review_rows": [],
                "review_row_signature_sha256": None,
                "support_declarations": [],
                "reason": "",
                "source_evidence": "",
                "source_scope_judgment": "",
                "source_anchor_quote_sha256": "",
                "target_kind": "",
                "archival_statement_sha256": "",
                "corrected_target_sha256": "",
                "governing_defect_ids": [],
                "archival_equivalence_claimed": None,
                "dashboard_evidence": "",
                "statement_sha256": "",
                "source_item_coverage_digest_schema": None,
                "source_item_coverage_sha256": "",
                "validator": payload_validator,
                "validator_type": payload_validator_type,
                "validated_at": payload_validated_at,
                "metadata_missing": not bool(payload_has_validator and payload_has_validated_at),
                "audit_kind": payload_audit_kind,
                "prompt_version": payload_prompt_version,
                "prompt_version_stale": payload_prompt_version_stale,
                "source_grounded": payload_source_grounded,
                "seed_scaffold": payload_seed_scaffold,
            }
    return {
        "source": path.name,
        "validator": payload_validator,
        "validator_type": payload_validator_type,
        "validated_at": payload_validated_at,
        "metadata_missing": not bool(payload_has_validator and payload_has_validated_at),
        "audit_kind": payload_audit_kind,
        "prompt_version": payload_prompt_version,
        "prompt_version_stale": payload_prompt_version_stale,
        "source_grounded": payload_source_grounded,
        "seed_scaffold": payload_seed_scaffold,
        "comment": str(payload.get("comment") or payload.get("notes") or "").strip(),
        "paper_statement_inventory_sha256": str(
            payload.get("paper_statement_inventory_sha256")
            or payload.get("statement_inventory_sha256")
            or payload.get("inventory_sha256")
            or ""
        ).strip(),
        "review_surface_sha256": str(payload.get("review_surface_sha256") or "").strip(),
        "source_coverage_mode": str(payload.get("source_coverage_mode") or "").strip(),
        "source_artifact_path": str(payload.get("source_artifact_path") or "").strip(),
        "source_artifact_sha256": str(
            payload.get("source_artifact_sha256") or ""
        ).strip().lower(),
        "items": items,
    }


def llm_review_surface_file(folder: Path) -> Path:
    """Return the preferred LLM review-surface audit sidecar for a paper."""

    tracked_path = paper_relative_file(folder, DEFAULT_LLM_REVIEW_SURFACE_FILE, "review_surface_llm.json")
    if _dashboard_audit_inputs() is not None or _dashboard_is_file(tracked_path):
        return tracked_path
    return folder / ".review_traces" / "review_surface_llm.json"


def _normalize_surface_audit_judgment(raw: Any) -> str:
    """Normalize review-surface audit verdicts for dashboard display."""

    if isinstance(raw, bool):
        return "passes" if raw else "needs_curation"
    value = str(raw or "").strip().lower()
    if value in {
        "pass",
        "passes",
        "ok",
        "good",
        "paper_facing",
        "paper-facing",
        "only_paper_facing",
        "only paper facing",
    }:
        return "passes"
    if value in {
        "fail",
        "fails",
        "needs_curation",
        "needs curation",
        "too_broad",
        "too broad",
        "not_paper_facing",
        "not paper facing",
    }:
        return "needs_curation"
    if value in {"uncertain", "unknown", "unsure", "needs_review", "needs review"}:
        return "uncertain"
    return value


def load_llm_review_surface_audit(
    folder: Path,
    *,
    audit_inputs: DashboardAuditInputs | None = None,
) -> dict[str, Any]:
    """Load optional LLM audit of whether dashboard rows are paper-facing."""

    if audit_inputs is not None:
        with dashboard_audit_input_scope(audit_inputs):
            return load_llm_review_surface_audit(folder)
    path = llm_review_surface_file(folder)
    if not _dashboard_is_file(path):
        return {}
    payload = _dashboard_json_payload(path)
    if payload is None:
        return {}
    non_evidence_scaffold = is_non_evidence_scaffold_payload(payload)
    if payload.get("schema") != 1:
        return {}
    if payload.get("paper") not in {None, folder.name}:
        return {}
    raw_judgment = (
        payload.get("judgment")
        or payload.get("verdict")
        or payload.get("status")
        or payload.get("paper_facing")
    )
    payload_prompt_version = str(payload.get("prompt_version") or "").strip()
    payload_validator = str(
        payload.get("validator")
        or payload.get("model")
        or payload.get("judge")
        or payload.get("agent")
        or payload.get("generator")
        or ""
    ).strip()
    payload_validated_at = str(
        payload.get("validated_at")
        or payload.get("timestamp")
        or payload.get("generated_at")
        or ""
    ).strip()
    return {
        "judgment": _normalize_surface_audit_judgment(raw_judgment),
        "reason": str(payload.get("reason") or payload.get("notes") or "").strip(),
        "source": path.name,
        "validator": payload_validator,
        "validated_at": payload_validated_at,
        "metadata_missing": not bool(payload_validator and payload_validated_at),
        "review_rows": payload.get("review_rows"),
        "review_surface_sha256": str(payload.get("review_surface_sha256") or "").strip(),
        "prompt_version": payload_prompt_version,
        "prompt_version_stale": payload_prompt_version
        != REQUIRED_LLM_REVIEW_SURFACE_PROMPT_VERSION,
        "non_evidence_scaffold": non_evidence_scaffold,
    }


def llm_assumption_judgments_file(folder: Path) -> Path:
    """Return the preferred LLM paper-assumption provenance sidecar."""

    tracked_path = paper_relative_file(folder, DEFAULT_LLM_ASSUMPTION_JUDGE_FILE, "assumption_match_llm.json")
    if _dashboard_audit_inputs() is not None or _dashboard_is_file(tracked_path):
        return tracked_path
    return folder / ".review_traces" / "assumption_match_llm.json"


def _normalize_assumption_judgment(raw: Any) -> str:
    """Normalize LLM verdicts for paper-assumption provenance."""

    if isinstance(raw, bool):
        return "paper_assumption" if raw else "not_paper_assumption"
    value = str(raw or "").strip().lower()
    if value in {
        "paper_assumption",
        "paper assumption",
        "source_assumption",
        "source assumption",
        "model_assumption",
        "model assumption",
        "match",
        "matches",
        "yes",
        "true",
    }:
        return "paper_assumption"
    if value in {
        "paper_condition",
        "paper condition",
        "source_condition",
        "source condition",
        "statement_condition",
        "statement condition",
        "theorem_condition",
        "theorem condition",
        "paper_statement_condition",
        "paper statement condition",
    }:
        return "paper_condition"
    if value in {
        "documented_additional_assumption",
        "documented additional assumption",
        "additional_assumption",
        "additional assumption",
        "human_approved_additional_assumption",
        "human approved additional assumption",
    }:
        return "documented_additional_assumption"
    if value in {
        "documented_caveat",
        "documented caveat",
        "paper_caveat",
        "paper caveat",
        "source_caveat",
        "source caveat",
        "repair_condition",
        "repair condition",
    }:
        return "documented_caveat"
    if value in {
        "partial_boundary",
        "partial boundary",
        "partial_formalization_boundary",
        "partial formalization boundary",
        "unresolved_boundary",
        "unresolved boundary",
        "needs_derivation",
        "needs derivation",
    }:
        return "partial_boundary"
    if value in {
        "not_paper_assumption",
        "not paper assumption",
        "proof_assumption",
        "proof assumption",
        "not_in_paper",
        "not in paper",
        "mismatch",
        "no",
        "false",
    }:
        return "not_paper_assumption"
    if value in {"uncertain", "unknown", "unsure", "needs_review", "needs review", "partial"}:
        return "uncertain"
    return value


def _normalize_premise_text(raw: str) -> str:
    """Normalize a Lean premise line for robust JSON/source comparisons."""

    return re.sub(r"\s+", " ", str(raw or "").strip())


def _assumption_premise_judgments(raw_value: Any) -> dict[str, dict[str, str]]:
    """Extract nested premise-level provenance judgments from an assumption row."""

    if not isinstance(raw_value, dict):
        return {}
    raw_items = (
        raw_value.get("premise_judgments")
        or raw_value.get("premise_items")
        or raw_value.get("premise_validations")
        or raw_value.get("premises_judged")
    )
    out: dict[str, dict[str, Any]] = {}

    def add_item(raw_premise: Any, raw_item: Any) -> None:
        premise = _normalize_premise_text(str(raw_premise or ""))
        if not premise:
            return
        if isinstance(raw_item, dict):
            raw_judgment = (
                raw_item.get("judgment")
                or raw_item.get("verdict")
                or raw_item.get("status")
                or raw_item.get("source_text_judgment")
            )
            out[premise] = {
                "judgment": _normalize_assumption_judgment(raw_judgment),
                "reason": str(
                    raw_item.get("reason")
                    or raw_item.get("notes")
                    or raw_item.get("explanation")
                    or ""
                ).strip(),
                "source_location": str(raw_item.get("source_location") or "").strip(),
            }
        else:
            out[premise] = {
                "judgment": _normalize_assumption_judgment(raw_item),
                "reason": "",
                "source_location": "",
            }

    if isinstance(raw_items, dict):
        for premise, raw_item in raw_items.items():
            add_item(premise, raw_item)
    elif isinstance(raw_items, list):
        for raw_item in raw_items:
            if isinstance(raw_item, dict):
                add_item(raw_item.get("premise"), raw_item)
            else:
                add_item(raw_item, "uncertain")
    return out


def load_llm_assumption_judgments(
    folder: Path,
    *,
    audit_inputs: DashboardAuditInputs | None = None,
) -> dict[str, dict[str, Any]]:
    """Load optional LLM judgments that listed assumptions are source assumptions."""

    if audit_inputs is not None:
        with dashboard_audit_input_scope(audit_inputs):
            return load_llm_assumption_judgments(folder)
    path = llm_assumption_judgments_file(folder)
    if not _dashboard_is_file(path):
        return {}
    payload = _dashboard_json_payload(path)
    if payload is None:
        return {}
    if payload.get("schema") != 1:
        return {}
    if payload.get("paper") not in {None, folder.name}:
        return {}
    items = payload.get("items")
    if not isinstance(items, dict):
        return {}
    source = path.name
    payload_validator = str(
        payload.get("validator")
        or payload.get("model")
        or payload.get("judge")
        or payload.get("agent")
        or payload.get("generator")
        or source
    ).strip()
    payload_has_validator = bool(
        payload.get("validator")
        or payload.get("model")
        or payload.get("judge")
        or payload.get("agent")
        or payload.get("generator")
    )
    payload_validator_type = str(
        payload.get("validator_type")
        or payload.get("generator_type")
        or ("model" if payload.get("model") else "agent" if payload.get("judge") else "")
    ).strip()
    payload_validated_at = str(
        payload.get("validated_at")
        or payload.get("timestamp")
        or payload.get("generated_at")
        or ""
    ).strip()
    payload_has_validated_at = bool(payload_validated_at)
    payload_comment = str(
        payload.get("comment")
        or payload.get("notes")
        or payload.get("reason")
        or payload.get("explanation")
        or ""
    ).strip()
    payload_prompt_version = str(payload.get("prompt_version") or "").strip()
    payload_prompt_version_stale = payload_prompt_version != REQUIRED_LLM_ASSUMPTION_PROMPT_VERSION
    out: dict[str, dict[str, str]] = {}
    for raw_name, raw_value in items.items():
        name = str(raw_name).strip()
        if not name:
            continue
        if isinstance(raw_value, dict):
            raw_judgment = (
                raw_value.get("judgment")
                or raw_value.get("verdict")
                or raw_value.get("status")
                or raw_value.get("paper_assumption")
            )
            reason = str(
                raw_value.get("reason")
                or raw_value.get("notes")
                or raw_value.get("explanation")
                or ""
            ).strip()
            validator = str(
                raw_value.get("validator")
                or raw_value.get("model")
                or raw_value.get("judge")
                or raw_value.get("agent")
                or raw_value.get("generator")
                or payload_validator
            ).strip()
            has_validator = bool(
                raw_value.get("validator")
                or raw_value.get("model")
                or raw_value.get("judge")
                or raw_value.get("agent")
                or raw_value.get("generator")
                or payload_has_validator
            )
            validator_type = str(
                raw_value.get("validator_type")
                or raw_value.get("generator_type")
                or ("model" if raw_value.get("model") else "agent" if raw_value.get("judge") else "")
                or payload_validator_type
            ).strip()
            validated_at = str(
                raw_value.get("validated_at")
                or raw_value.get("timestamp")
                or raw_value.get("generated_at")
                or payload_validated_at
            ).strip()
            has_validated_at = bool(
                raw_value.get("validated_at")
                or raw_value.get("timestamp")
                or raw_value.get("generated_at")
                or payload_has_validated_at
            )
            comment = str(
                raw_value.get("comment")
                or raw_value.get("notes")
                or raw_value.get("reason")
                or raw_value.get("explanation")
                or payload_comment
                or ""
            ).strip()
            out[name] = {
                "judgment": _normalize_assumption_judgment(raw_judgment),
                "reason": reason,
                "source": source,
                "validator": validator,
                "validator_type": validator_type,
                "validated_at": validated_at,
                "comment": comment,
                "prompt_version": payload_prompt_version,
                "prompt_version_stale": payload_prompt_version_stale,
                "metadata_missing": not bool(has_validator and has_validated_at),
                "lean_statement_sha256": str(raw_value.get("lean_statement_sha256") or "").strip(),
                "lean_signature_sha256": str(raw_value.get("lean_signature_sha256") or "").strip(),
                "paper_statement_sha256": str(raw_value.get("paper_statement_sha256") or "").strip(),
                "premise_judgments": _assumption_premise_judgments(raw_value),
                "source_record_semantic_parent_v1": (
                    dict(raw_value["source_record_semantic_parent_v1"])
                    if isinstance(
                        raw_value.get("source_record_semantic_parent_v1"), dict
                    )
                    else None
                ),
            }
        else:
            judgment = _normalize_assumption_judgment(raw_value)
            if judgment:
                out[name] = {
                    "judgment": judgment,
                    "reason": "",
                    "source": source,
                    "validator": payload_validator,
                    "validator_type": payload_validator_type,
                    "validated_at": payload_validated_at,
                    "comment": payload_comment,
                    "prompt_version": payload_prompt_version,
                    "prompt_version_stale": payload_prompt_version_stale,
                    "metadata_missing": not bool(payload_has_validator and payload_has_validated_at),
                    "premise_judgments": {},
                }
    return out


def llm_lean_to_tex_drafts_file(folder: Path) -> Path:
    """Return the preferred Lean-to-TeX draft sidecar for a paper."""

    tracked_path = paper_relative_file(folder, DEFAULT_LLM_LEAN_TO_TEX_FILE, "lean_to_tex_llm.json")
    if _dashboard_audit_inputs() is not None or _dashboard_is_file(tracked_path):
        return tracked_path
    return folder / ".review_traces" / "lean_to_tex_llm.json"


def _run_pdftotext_bbox(pdf_path: Path, page: int) -> str:
    """Return pdftotext bbox-layout XML for one page, or empty on failure."""

    try:
        proc = subprocess.run(
            [
                "pdftotext",
                "-bbox-layout",
                "-f",
                str(page),
                "-l",
                str(page),
                str(pdf_path),
                "-",
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=10,
        )
    except (OSError, subprocess.TimeoutExpired):
        return ""
    if proc.returncode != 0:
        return ""
    return proc.stdout


def _parse_pdf_bbox_words(xml_text: str) -> tuple[float, float, list[dict[str, Any]]]:
    """Parse pdftotext bbox XML into page dimensions and word boxes."""

    if not xml_text.strip():
        return 0.0, 0.0, []
    try:
        root = ElementTree.fromstring(xml_text)
    except ElementTree.ParseError:
        return _parse_pdf_bbox_words_with_regex(xml_text)
    page_node = next((node for node in root.iter() if node.tag.endswith("page")), None)
    if page_node is None:
        return 0.0, 0.0, []
    try:
        page_width = float(page_node.attrib.get("width", "0"))
        page_height = float(page_node.attrib.get("height", "0"))
    except ValueError:
        page_width = 0.0
        page_height = 0.0
    words: list[dict[str, Any]] = []
    for word_node in root.iter():
        if not word_node.tag.endswith("word"):
            continue
        text = "".join(word_node.itertext()).strip()
        if not text:
            continue
        try:
            words.append(
                {
                    "text": text,
                    "x_min": float(word_node.attrib["xMin"]),
                    "y_min": float(word_node.attrib["yMin"]),
                    "x_max": float(word_node.attrib["xMax"]),
                    "y_max": float(word_node.attrib["yMax"]),
                }
            )
        except (KeyError, ValueError):
            continue
    return page_width, page_height, words


def _parse_pdf_bbox_words_with_regex(xml_text: str) -> tuple[float, float, list[dict[str, Any]]]:
    """Fallback bbox parser for PDFs whose extracted XHTML has invalid glyph bytes."""

    page_match = re.search(
        r"<page\b[^>]*\bwidth=\"([0-9.]+)\"[^>]*\bheight=\"([0-9.]+)\"",
        xml_text,
    )
    if not page_match:
        return 0.0, 0.0, []
    try:
        page_width = float(page_match.group(1))
        page_height = float(page_match.group(2))
    except ValueError:
        return 0.0, 0.0, []

    word_re = re.compile(
        r"<word\b[^>]*\bxMin=\"([0-9.]+)\"[^>]*\byMin=\"([0-9.]+)\""
        r"[^>]*\bxMax=\"([0-9.]+)\"[^>]*\byMax=\"([0-9.]+)\"[^>]*>(.*?)</word>",
        flags=re.DOTALL,
    )
    words: list[dict[str, Any]] = []
    for match in word_re.finditer(xml_text):
        text = re.sub(r"<[^>]+>", "", match.group(5))
        text = html.unescape(text).strip()
        if not text:
            continue
        try:
            words.append(
                {
                    "text": text,
                    "x_min": float(match.group(1)),
                    "y_min": float(match.group(2)),
                    "x_max": float(match.group(3)),
                    "y_max": float(match.group(4)),
                }
            )
        except ValueError:
            continue
    return page_width, page_height, words


def _find_statement_start_y(words: list[dict[str, Any]], kind: str, number: str) -> float | None:
    """Locate a statement heading in bbox word output."""

    for index, word in enumerate(words[:-1]):
        if word["text"].strip(".,") != kind:
            continue
        nxt = words[index + 1]
        if nxt["text"].strip(".,") != number:
            continue
        if abs(float(nxt["y_min"]) - float(word["y_min"])) > 6.0:
            continue
        return float(word["y_min"])
    return None


def _find_statement_stop_y(words: list[dict[str, Any]], top_y: float, current_bottom: float) -> float:
    """Find an earlier paper-proof/section boundary inside a candidate crop."""

    stop_sequences = [
        ("Proof",),
        ("Proof.",),
        ("To", "prove"),
        ("The", "proof"),
        ("What", "does"),
    ]
    for index, word in enumerate(words):
        y_min = float(word["y_min"])
        if y_min <= top_y + 18.0 or y_min >= current_bottom:
            continue
        if float(word["x_min"]) > 115.0:
            continue
        row_words = [
            str(candidate["text"]).strip(".,:;")
            for candidate in words[index : index + 4]
            if abs(float(candidate["y_min"]) - y_min) <= 3.0
        ]
        if any(row_words[: len(sequence)] == list(sequence) for sequence in stop_sequences):
            return y_min - 10.0
    return current_bottom


def _render_pdf_page_to_png(pdf_path: Path, page: int, output_dir: Path, digest: str) -> Path | None:
    """Render a single PDF page to a PNG cache file."""

    page_path = output_dir / f"page-{page}-{digest[:12]}.png"
    if page_path.exists():
        return page_path
    prefix = output_dir / f"page-{page}-{digest[:12]}"
    try:
        proc = subprocess.run(
            [
                "pdftoppm",
                "-f",
                str(page),
                "-l",
                str(page),
                "-r",
                "180",
                "-png",
                str(pdf_path),
                str(prefix),
            ],
            check=False,
            capture_output=True,
            text=True,
            timeout=20,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if proc.returncode != 0:
        return None
    rendered = sorted(output_dir.glob(f"{prefix.name}-*.png"))
    if not rendered:
        return None
    try:
        rendered[0].replace(page_path)
    except OSError:
        return None
    for stale in rendered[1:]:
        try:
            stale.unlink()
        except OSError:
            pass
    return page_path


def attach_rendered_statement_images(folder: Path, items: list[ReviewItem]) -> None:
    """Attach cropped PDF-rendered statement images when a source PDF is available."""

    pdf_path = find_paper_pdf(folder)
    if pdf_path is None:
        return
    locations = parse_paper_text_statement_locations(folder)
    if not locations:
        return

    location_by_key = {str(location["key"]): location for location in locations}
    next_on_same_page: dict[str, dict[str, Any]] = {}
    for index, location in enumerate(locations):
        for later in locations[index + 1 :]:
            if later.get("page") == location.get("page"):
                next_on_same_page[str(location["key"])] = later
                break
            if int(later.get("page") or 0) > int(location.get("page") or 0):
                break

    digest = _file_sha256(pdf_path) or statement_digest(str(pdf_path))
    output_dir = folder / ".review_traces" / PAPER_RENDERED_STATEMENT_DIR
    output_dir.mkdir(parents=True, exist_ok=True)
    bbox_cache: dict[int, tuple[float, float, list[dict[str, Any]]]] = {}

    try:
        from PIL import Image
    except Exception:  # noqa: BLE001 - optional runtime rendering dependency
        Image = None  # type: ignore[assignment]

    for item in items:
        keys = paper_statement_candidate_keys(item.name, item.name)
        location = next((location_by_key[key] for key in keys if key in location_by_key), None)
        if location is None:
            continue
        page = int(location.get("page") or 0)
        if page <= 0:
            continue
        key = str(location["key"])
        crop_path = output_dir / f"{key}-{digest[:12]}.png"
        if crop_path.exists():
            item.paper_statement_image_url = paper_rendered_statement_url(folder.name, crop_path)
            continue
        page_png = _render_pdf_page_to_png(pdf_path, page, output_dir, digest)
        if page_png is None:
            continue
        if Image is None:
            item.paper_statement_image_url = paper_rendered_statement_url(folder.name, page_png)
            continue
        if page not in bbox_cache:
            bbox_cache[page] = _parse_pdf_bbox_words(_run_pdftotext_bbox(pdf_path, page))
        page_width, page_height, words = bbox_cache[page]
        if not page_width or not page_height:
            item.paper_statement_image_url = paper_rendered_statement_url(folder.name, page_png)
            continue
        top_y = _find_statement_start_y(
            words, str(location.get("kind") or ""), str(location.get("number") or "")
        )
        if top_y is None:
            item.paper_statement_image_url = paper_rendered_statement_url(folder.name, page_png)
            continue
        next_location = next_on_same_page.get(key)
        bottom_y = page_height - 48.0
        if next_location is not None:
            next_top = _find_statement_start_y(
                words,
                str(next_location.get("kind") or ""),
                str(next_location.get("number") or ""),
            )
            if next_top is not None and next_top > top_y + 20.0:
                bottom_y = next_top - 10.0
        bottom_y = _find_statement_stop_y(words, top_y, bottom_y)
        try:
            with Image.open(page_png) as image:
                scale_x = image.width / page_width
                scale_y = image.height / page_height
                left = max(0, int(54.0 * scale_x))
                upper = max(0, int((top_y - 14.0) * scale_y))
                right = min(image.width, int((page_width - 54.0) * scale_x))
                lower = min(image.height, int((bottom_y + 4.0) * scale_y))
                if lower <= upper + 20 or right <= left + 20:
                    item.paper_statement_image_url = paper_rendered_statement_url(folder.name, page_png)
                    continue
                cropped = image.crop((left, upper, right, lower))
                cropped.save(crop_path)
        except OSError:
            item.paper_statement_image_url = paper_rendered_statement_url(folder.name, page_png)
            continue
        item.paper_statement_image_url = paper_rendered_statement_url(folder.name, crop_path)


def paper_statement_candidate_keys(name: str, full_name: str) -> list[str]:
    """Return paper-statement keys likely to correspond to a Lean declaration."""

    raw_candidates = [
        full_name,
        name,
        name.split(".")[-1],
        full_name.split(".")[-1],
        _normalize_name_key(full_name),
        _normalize_name_key(name),
    ]
    for base in [name, full_name.split(".")[-1]]:
        for kind in ("definition", "theorem", "lemma", "proposition", "corollary", "claim", "remark"):
            match = re.search(rf"(?:^|_){kind}([A-Za-z]?\d+(?:_\d+)*)", base, flags=re.IGNORECASE)
            if match:
                raw_candidates.append(f"{kind}{match.group(1).lower()}")
                raw_candidates.append(f"{kind}_{match.group(1).lower()}")
    out: list[str] = []
    for candidate in raw_candidates:
        if not candidate:
            continue
        for variant in {candidate, _normalize_name_key(candidate), candidate.lower(), _normalize_name_key(candidate).lower()}:
            if variant and variant not in out:
                out.append(variant)
    return out


def _safe_slice_id(value: str) -> str:
    """Normalize a dashboard slice identifier for local filtering."""

    cleaned = re.sub(r"[^A-Za-z0-9_.-]+", "-", value.strip()).strip("-")
    return cleaned or "all"


def collect_export_names(lines: list[str], start: int) -> tuple[list[str], int] | None:
    """Collect names from a Lean `export Foo (...)` block."""

    match = EXPORT_OPEN_RE.match(lines[start])
    if not match:
        return None
    chunks = [match.group("rest")]
    i = start
    while i < len(lines):
        if ")" in chunks[-1]:
            break
        i += 1
        if i >= len(lines):
            return None
        chunks.append(lines[i])
    text = "\n".join(chunks)
    before_close = text.split(")", 1)[0]
    names = EXPORT_NAME_RE.findall(before_close)
    return names, i + 1


def load_review_slice_payload(
    folder: Path,
    *,
    audit_inputs: DashboardAuditInputs | None = None,
) -> dict[str, Any]:
    """Load paper-local review-surface metadata from status.json."""

    if audit_inputs is not None:
        with dashboard_audit_input_scope(audit_inputs):
            return load_review_slice_payload(folder)
    status_path = folder / DEFAULT_PAPER_STATUS_FILE
    if _dashboard_is_file(status_path):
        status_payload = _dashboard_json_payload(status_path) or {}
        if isinstance(status_payload, dict):
            review_surface = status_payload.get("review_surface")
            if isinstance(review_surface, dict):
                payload: dict[str, Any] = {"schema": REVIEW_SURFACE_SCHEMA}
                include_names = review_surface.get("include_names")
                slices = review_surface.get("slices")
                assumption_names = review_surface.get("assumption_names")
                auxiliary_names = review_surface.get("auxiliary_names")
                source_definition_names = review_surface.get("source_definition_names")
                proposition_spec_proofs = review_surface.get("proposition_spec_proofs")
                source_component_statement_routes = review_surface.get(
                    "source_component_statement_routes"
                )
                source_file = review_surface.get("source_file")
                human_source_file = review_surface.get("human_source_file")
                assumption_source_file = review_surface.get("assumption_source_file")
                assumption_policy = review_surface.get("assumption_policy")
                paper_coverage_required = review_surface.get("paper_coverage_required")
                if isinstance(source_file, str) and source_file.strip():
                    payload["source_file"] = source_file
                if isinstance(human_source_file, str) and human_source_file.strip():
                    payload["human_source_file"] = human_source_file
                if isinstance(include_names, list):
                    payload["include_names"] = include_names
                if isinstance(slices, list):
                    payload["slices"] = slices
                if isinstance(assumption_names, list):
                    payload["assumption_names"] = assumption_names
                if isinstance(auxiliary_names, list):
                    payload["auxiliary_names"] = auxiliary_names
                if isinstance(source_definition_names, list):
                    payload["source_definition_names"] = source_definition_names
                if isinstance(proposition_spec_proofs, dict):
                    payload["proposition_spec_proofs"] = proposition_spec_proofs
                if isinstance(source_component_statement_routes, list):
                    payload["source_component_statement_routes"] = (
                        source_component_statement_routes
                    )
                if isinstance(assumption_source_file, str) and assumption_source_file.strip():
                    payload["assumption_source_file"] = assumption_source_file
                if isinstance(assumption_policy, str):
                    payload["assumption_policy"] = assumption_policy
                if isinstance(paper_coverage_required, (bool, str)):
                    payload["paper_coverage_required"] = paper_coverage_required
                if (
                    "include_names" in payload
                    or "slices" in payload
                    or "assumption_names" in payload
                    or "auxiliary_names" in payload
                    or "source_definition_names" in payload
                    or "proposition_spec_proofs" in payload
                    or "source_component_statement_routes" in payload
                    or "source_file" in payload
                    or "human_source_file" in payload
                    or "assumption_source_file" in payload
                    or "assumption_policy" in payload
                    or "paper_coverage_required" in payload
                ):
                    return payload

    return {}


def review_slice_rules(folder: Path) -> list[dict[str, Any]]:
    """Return validated slice rules for a paper folder."""

    payload = load_review_slice_payload(folder)
    raw_slices = payload.get("slices", [])
    if not isinstance(raw_slices, list):
        return []
    out: list[dict[str, Any]] = []
    for index, raw_slice in enumerate(raw_slices, start=1):
        if not isinstance(raw_slice, dict):
            continue
        title = str(raw_slice.get("title") or raw_slice.get("id") or f"Slice {index}").strip()
        if not title:
            title = f"Slice {index}"
        rule = dict(raw_slice)
        rule["id"] = _safe_slice_id(str(raw_slice.get("id") or title))
        rule["title"] = title
        out.append(rule)
    return out


def review_filter_names(folder: Path) -> set[str] | None:
    """Return an optional paper-local whitelist for human-review rows."""

    payload = load_review_slice_payload(folder)
    names = payload.get("include_names")
    if not isinstance(names, list):
        return None
    out = {str(name).strip() for name in names if str(name).strip()}
    return out if out else None


def review_assumption_names(folder: Path) -> set[str]:
    """Return explicit paper-assumption declarations from status.json."""

    payload = load_review_slice_payload(folder)
    names = payload.get("assumption_names")
    if not isinstance(names, list):
        return set()
    return {str(name).strip() for name in names if str(name).strip()}


def review_auxiliary_names(folder: Path) -> set[str]:
    """Return proof-facing declarations intentionally excluded from statement review."""

    payload = load_review_slice_payload(folder)
    names = payload.get("auxiliary_names")
    if not isinstance(names, list):
        return set()
    return {str(name).strip() for name in names if str(name).strip()}


def review_source_definition_names(folder: Path) -> set[str]:
    """Return reviewed Prop definitions explicitly classified as source definitions."""

    payload = load_review_slice_payload(folder)
    names = payload.get("source_definition_names")
    if not isinstance(names, list):
        return set()
    return {str(name).strip() for name in names if str(name).strip()}


def review_proposition_spec_proofs(folder: Path) -> dict[str, str]:
    """Return explicit Prop-spec to proof-row routing from status.json."""

    payload = load_review_slice_payload(folder)
    raw = payload.get("proposition_spec_proofs")
    if not isinstance(raw, dict):
        return {}
    return {
        str(spec).strip(): str(proof).strip()
        for spec, proof in raw.items()
        if str(spec).strip() and str(proof).strip()
    }


def attach_current_lean_semantic_contract_results(
    folder: Path,
    interface_path: Path,
    items: list[ReviewItem],
    *,
    build_input_provider: RepositoryBuildInputSnapshotProvider,
) -> None:
    """Attach artifact-pinned Lean verdicts to configured Spec/proof rows.

    Declaration names only identify the requested endpoints. Lean compares the
    elaborated propositions and walks the paper-local dependency graph; Python
    does not recreate either semantic operation.
    """

    by_full_name = {
        item.full_name: item for item in items if str(item.full_name or "").strip()
    }
    by_short_name: dict[str, list[ReviewItem]] = {}
    for item in items:
        by_short_name.setdefault(item.name, []).append(item)

    requested: list[tuple[ReviewItem, ReviewItem, tuple[str, str, str]]] = []
    for specification in items:
        proof_name = str(specification.proposition_spec_proof or "").strip()
        if not proof_name or specification.proposition_spec_role != "proof_routed":
            continue
        evidence = by_full_name.get(proof_name)
        if evidence is None:
            candidates = by_short_name.get(proof_name, [])
            if len(candidates) == 1:
                evidence = candidates[0]
        if evidence is None or not specification.full_name or not evidence.full_name:
            continue
        route = (specification.full_name, evidence.full_name, "proves")
        requested.append((specification, evidence, route))

    if not requested:
        return

    import_module = review_source_module(folder, interface_path)
    paper_modules = paper_owned_module_names_in_import_closure(
        ROOT,
        folder,
        import_module,
        provider=build_input_provider,
    )
    try:
        matches = run_lean_semantic_contract_matches(
            ROOT,
            import_module,
            [route for _specification, _evidence, route in requested],
            build_input_provider=build_input_provider,
        )
        transparency = run_lean_semantic_contract_transparency_checks(
            ROOT,
            import_module,
            sorted({route[0] for _specification, _evidence, route in requested}),
            paper_modules,
            build_input_provider=build_input_provider,
        )
    except Exception:  # noqa: BLE001 - unavailable Lean evidence fails closed.
        matches = {}
        transparency = {}

    for specification, _evidence, route in requested:
        match_result = matches.get(route)
        specification.semantic_contract_lean_match_verified = (
            match_result if isinstance(match_result, bool) else None
        )
        transparency_result = transparency.get(route[0])
        passes = (
            transparency_result.get("passes")
            if isinstance(transparency_result, dict)
            else None
        )
        specification.semantic_contract_lean_transparency_verified = (
            passes if isinstance(passes, bool) else None
        )


def is_assumption_item_name(name: str) -> bool:
    """Heuristic for assumption declarations before status.json has been filled."""

    return bool(ASSUMPTION_DECL_NAME_RE.search(name))


def review_item_matches_slice_rule(item: ReviewItem, rule: dict[str, Any]) -> bool:
    """Check whether an item belongs to one review slice rule."""

    names = rule.get("names")
    if isinstance(names, list) and item.name in {str(name) for name in names}:
        return True

    prefixes = rule.get("prefixes")
    if isinstance(prefixes, list) and any(item.name.startswith(str(prefix)) for prefix in prefixes):
        return True

    pattern = rule.get("name_regex")
    if isinstance(pattern, str) and pattern.strip():
        try:
            if re.search(pattern, item.name):
                return True
        except re.error:
            pass

    line_start = rule.get("line_start")
    line_end = rule.get("line_end")
    if isinstance(line_start, int) or isinstance(line_end, int):
        start_ok = not isinstance(line_start, int) or item.line_number >= line_start
        end_ok = not isinstance(line_end, int) or item.line_number <= line_end
        if start_ok and end_ok:
            return True

    return False


def _review_name_survives_surface_filter(
    name: str,
    include_names: set[str] | None,
    assumption_names: set[str],
    auxiliary_names: set[str],
) -> bool:
    """Apply the name filter shared by review selection and Lean elaboration."""

    if (
        include_names is not None
        and name not in include_names
        and name not in assumption_names
    ):
        return False
    return name not in auxiliary_names


def apply_review_slices(folder: Path, items: list[ReviewItem]) -> list[ReviewItem]:
    """Attach paper-local review slice labels to parsed dashboard rows."""

    include_names = review_filter_names(folder)
    assumption_names = review_assumption_names(folder)
    auxiliary_names = review_auxiliary_names(folder)
    items = [
        item
        for item in items
        if _review_name_survives_surface_filter(
            item.name, include_names, assumption_names, auxiliary_names
        )
    ]

    rules = review_slice_rules(folder)
    if not rules:
        for item in items:
            item.slice_id = "all"
            item.slice_title = "All statements"
        return items

    payload = load_review_slice_payload(folder)
    fallback_title = str(payload.get("fallback_title") or "Other statements")
    fallback_id = _safe_slice_id(str(payload.get("fallback_id") or "other"))
    for item in items:
        for rule in rules:
            if review_item_matches_slice_rule(item, rule):
                item.slice_id = str(rule["id"])
                item.slice_title = str(rule["title"])
                break
        else:
            item.slice_id = fallback_id
            item.slice_title = fallback_title
    return items


def summarize_review_slices(items: list[ReviewItem]) -> list[dict[str, Any]]:
    """Summarize slices present in a paper's current dashboard rows."""

    order: list[str] = []
    by_id: dict[str, dict[str, Any]] = {}
    for item in items:
        slice_id = item.slice_id or "all"
        if slice_id not in by_id:
            order.append(slice_id)
            by_id[slice_id] = {
                "id": slice_id,
                "title": item.slice_title or slice_id,
                "count": 0,
                "first_line": item.line_number or None,
                "last_line": item.line_number or None,
            }
        row = by_id[slice_id]
        row["count"] += 1
        if item.line_number:
            first_line = row.get("first_line")
            last_line = row.get("last_line")
            row["first_line"] = item.line_number if first_line is None else min(first_line, item.line_number)
            row["last_line"] = item.line_number if last_line is None else max(last_line, item.line_number)
    return [by_id[slice_id] for slice_id in order]


def filter_items_by_slice(
    items: list[ReviewItem], paper_name: str, slice_filter: str | None
) -> list[ReviewItem]:
    """Filter dashboard rows to one slice id or paper-qualified slice id."""

    if not slice_filter:
        return items
    normalized = slice_filter.strip()
    if not normalized:
        return items
    paper_part = ""
    slice_part = normalized
    if "::" in normalized:
        paper_part, slice_part = normalized.split("::", 1)
        if paper_part and paper_part != paper_name:
            return []
    slice_part = _safe_slice_id(slice_part)
    filtered = [item for item in items if item.slice_id == slice_part]
    if filtered:
        return filtered
    if items and {item.slice_id for item in items} == {"all"}:
        return items
    return filtered


def _is_interface_decl_boundary(line: str) -> bool:
    """Return true when a line starts a new top-level interface item."""

    stripped = line.strip()
    if not stripped:
        return True
    return bool(
        COMMENT_START_RE.match(line)
        or DECL_RE.match(line)
        or NAMESPACE_OPEN_RE.match(stripped)
        or SECTION_OPEN_RE.match(stripped)
        or END_SCOPE_RE.match(stripped)
    )


def _declaration_assignment_index(
    line: str,
    *,
    delimiters: list[str],
    block_comment_depth: int,
    in_string: bool,
    top_level_let: bool,
) -> tuple[int | None, list[str], int, bool, bool]:
    """Find an outer declaration `:=` while preserving theorem `let` types.

    Lean theorem types can contain local `let` bindings, including an inner
    `:=`.  This lightweight lexer intentionally recognizes only enough Lean
    surface syntax to distinguish those from the declaration assignment.  A
    failure to recognize an outer assignment is a cache miss, never a source
    binding to a truncated theorem statement.
    """

    matching = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "⟪": "⟫", "⟦": "⟧"}
    i = 0
    while i < len(line):
        if block_comment_depth:
            if line.startswith("/-", i):
                block_comment_depth += 1
                i += 2
                continue
            if line.startswith("-/", i):
                block_comment_depth -= 1
                i += 2
                continue
            i += 1
            continue
        if in_string:
            if line[i] == "\\":
                i += 2
                continue
            if line[i] == '"':
                in_string = False
            i += 1
            continue
        if line.startswith("--", i):
            break
        if line.startswith("/-", i):
            block_comment_depth += 1
            i += 2
            continue
        if line[i] == '"':
            in_string = True
            i += 1
            continue
        character = line[i]
        if character in matching:
            delimiters.append(matching[character])
            i += 1
            continue
        if delimiters and character == delimiters[-1]:
            delimiters.pop()
            i += 1
            continue
        if not delimiters and character == ";":
            top_level_let = False
            i += 1
            continue
        if not delimiters and line.startswith(":=", i) and not top_level_let:
            return i, delimiters, block_comment_depth, in_string, top_level_let
        if not delimiters and (character.isalpha() or character == "_"):
            end = i + 1
            while end < len(line) and (line[end].isalnum() or line[end] in "_'"):
                end += 1
            if line[i:end] == "let":
                top_level_let = True
            i = end
            continue
        i += 1
    return None, delimiters, block_comment_depth, in_string, top_level_let


def collect_review_decl_text(lines: list[str], start: int, kind: str) -> tuple[str, int] | None:
    """Collect the text shown for one paper-interface declaration."""

    sig_lines: list[str] = []
    delimiters: list[str] = []
    block_comment_depth = 0
    in_string = False
    top_level_let = False
    j = start
    while j < len(lines):
        sig_line = lines[j]
        sig_lines.append(sig_line)
        if kind in {"axiom", "structure", "class", "inductive"} and (
            j + 1 >= len(lines) or _is_interface_decl_boundary(lines[j + 1])
        ):
            return "\n".join(sig_lines).strip(), j + 1
        (
            assignment_index,
            delimiters,
            block_comment_depth,
            in_string,
            top_level_let,
        ) = _declaration_assignment_index(
            sig_line,
            delimiters=delimiters,
            block_comment_depth=block_comment_depth,
            in_string=in_string,
            top_level_let=top_level_let,
        )
        if assignment_index is not None:
            if kind in {"def", "abbrev"}:
                while j + 1 < len(lines) and not _is_interface_decl_boundary(lines[j + 1]):
                    j += 1
                    sig_lines.append(lines[j])
            else:
                sig_lines[-1] = sig_line[:assignment_index]
            return "\n".join(sig_lines).strip(), j + 1
        j += 1
    return None


def parse_review_source_declarations(
    source_path: Path,
    *,
    source_text: str | None = None,
) -> list[tuple[str, str, str, str, str | None, int, Path]]:
    """Parse dashboard-visible Lean declarations from one source file."""

    if source_text is None and not _dashboard_is_file(source_path):
        return []
    lines = (
        source_text if source_text is not None else _dashboard_read_text(source_path)
    ).splitlines()
    parsed: list[tuple[str, str, str, str, str | None, int, Path]] = []
    namespace_stack: list[str] = []
    section_depth = 0
    pending_comment: str | None = None
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()

        namespace_match = NAMESPACE_OPEN_RE.match(stripped)
        if namespace_match:
            namespace_stack.extend(namespace_match.group(1).split("."))
            i += 1
            continue

        section_match = SECTION_OPEN_RE.match(stripped)
        if section_match:
            section_depth += 1
            i += 1
            continue

        end_match = END_SCOPE_RE.match(stripped)
        if end_match:
            end_name = end_match.group(1)
            if end_name and namespace_stack and namespace_stack[-1] == end_name:
                namespace_stack.pop()
            elif end_name:
                if section_depth > 0:
                    section_depth -= 1
            else:
                if section_depth > 0:
                    section_depth -= 1
                elif namespace_stack:
                    namespace_stack.pop()
            i += 1
            continue

        if COMMENT_START_RE.match(line):
            comment, after = parse_block_comment(lines, i)
            if "/-!" in line or line.lstrip().startswith("/-"):
                pending_comment = clean_comment(comment)
            i = after
            continue

        if stripped.startswith("@[") and stripped.endswith("]"):
            i += 1
            continue

        exported = collect_export_names(lines, i)
        if exported is not None:
            names, next_i = exported
            for name in names:
                full_name = ".".join(namespace_stack + [name]) if namespace_stack else name
                parsed.append(
                    (
                        "theorem",
                        name,
                        full_name,
                        f"exported declaration `{full_name}`",
                        pending_comment,
                        i + 1,
                        source_path,
                    )
                )
            pending_comment = None
            i = next_i
            continue

        m = DECL_RE.match(line)
        if m:
            name = m.group("name")
            kind = m.group("kind")
            full_name = ".".join(namespace_stack + [name]) if namespace_stack else name
            collected = collect_review_decl_text(lines, i, kind)
            if collected is not None:
                raw_sig, next_i = collected
                parsed.append((kind, name, full_name, raw_sig, pending_comment, i + 1, source_path))
            else:
                next_i = i + 1
            pending_comment = None
            i = next_i
            continue

        if stripped and not stripped.startswith("--") and not stripped.startswith("/-"):
            pending_comment = None
        i += 1
    return parsed


def parse_interface_items(
    interface_path: Path,
    report_path: Path | None,
    paper_folder: Path | None = None,
    *,
    render_lean_previews: bool = True,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
    audit_inputs: DashboardAuditInputs | None = None,
    progress: Callable[[str], None] | None = None,
) -> list[ReviewItem]:
    """Combine declaration signatures and paper statements for one paper folder."""

    if audit_inputs is not None:
        with dashboard_audit_input_scope(audit_inputs):
            return parse_interface_items(
                interface_path,
                report_path,
                paper_folder,
                render_lean_previews=render_lean_previews,
                build_input_provider=build_input_provider,
                progress=progress,
            )
    owns_build_input_provider = build_input_provider is None
    if build_input_provider is None:
        build_input_provider = RepositoryBuildInputSnapshotProvider(ROOT)
    if paper_folder is None:
        paper_folder = interface_path.parent
    paper_statements = collected_paper_statements(paper_folder, report_path)
    llm_tex_drafts = load_llm_lean_to_tex_drafts(paper_folder)
    include_names = review_filter_names(paper_folder)
    assumption_names = review_assumption_names(paper_folder)
    auxiliary_names = review_auxiliary_names(paper_folder)
    source_definition_names = review_source_definition_names(paper_folder)
    proposition_spec_proofs = review_proposition_spec_proofs(paper_folder)
    assumption_judgments = load_llm_assumption_judgments(paper_folder)

    parsed = parse_review_source_declarations(interface_path)
    assumption_path = assumption_source_file(paper_folder)
    if (
        assumption_names
        and assumption_path != interface_path
        and _dashboard_is_file(assumption_path)
    ):
        for row in parse_review_source_declarations(assumption_path):
            _kind, name, full_name, _raw_sig, _comment, _line_number, _source_path = row
            if name in assumption_names or full_name in assumption_names or is_assumption_item_name(name):
                parsed.append(row)
    component_navigation_routes = review_source_component_statement_routes(
        paper_folder
    )
    component_statement_routes = resolved_review_source_component_statement_routes(
        paper_folder,
        parsed,
        component_routes=component_navigation_routes,
    )
    direct_statement_routes = resolved_direct_source_statement_routes(
        paper_folder,
        parsed,
    )

    semantic_parsed = parsed
    if include_names is not None:
        semantic_parsed = [
            row
            for row in parsed
            if _review_name_survives_surface_filter(
                row[1], include_names, assumption_names, auxiliary_names
            )
        ]

    check_maps: dict[Path, dict[str, str]] = {}
    signature_maps: dict[Path, dict[str, dict[str, Any]]] = {}
    for source_path in sorted({row[6] for row in semantic_parsed}):
        source_module = review_source_module(paper_folder, source_path)
        dependency_modules = paper_owned_module_names_in_import_closure(
            ROOT,
            paper_folder,
            source_module,
            provider=build_input_provider,
        )
        declaration_names = [
            full_name
            for (
                kind,
                _name,
                full_name,
                _raw_sig,
                _comment,
                _line_number,
                row_source,
            ) in semantic_parsed
            if kind in REVIEW_DECL_KINDS and row_source == source_path
        ]
        resume_bindings: dict[str, dict[str, str]] = {}
        duplicate_resume_bindings: set[str] = set()
        for (
            kind,
            _name,
            full_name,
            raw_signature,
            _comment,
            _line_number,
            row_source,
        ) in semantic_parsed:
            if kind not in REVIEW_DECL_KINDS or row_source != source_path:
                continue
            if full_name in duplicate_resume_bindings:
                continue
            if full_name in resume_bindings:
                resume_bindings.pop(full_name, None)
                duplicate_resume_bindings.add(full_name)
                continue
            binding = _manifest_resume_binding(
                paper_folder,
                qualified_declaration=full_name,
                declaration_kind=kind,
                lean_source_declaration=raw_signature,
                source_path=source_path,
            )
            if binding is not None:
                resume_bindings[full_name] = binding
        check_maps[source_path] = (
            run_lean_check_previews(
                paper_folder,
                declaration_names,
                source_file=source_path,
            )
            if render_lean_previews
            else {}
        )
        if not dependency_modules:
            signature_maps[source_path] = {}
            continue
        resume_context = signature_manifest_cache_context(
            ROOT,
            source_module,
            semantic_dependency_modules=dependency_modules,
            build_input_provider=build_input_provider,
        )
        resumed = (
            _prime_manifest_resume_cache(
                paper_folder,
                import_module=source_module,
                semantic_dependency_modules=dependency_modules,
                context=resume_context,
                bindings=resume_bindings,
                progress=progress,
            )
            if isinstance(resume_context, Mapping)
            else set()
        )
        if progress is not None and resumed:
            progress(
                "non-authoritative manifest resume cache reused "
                f"{len(resumed)} declaration(s)"
            )
        if progress is not None:
            progress(
                f"Lean manifest surface {source_module}: "
                f"{len(declaration_names)} declarations started"
            )

        def checkpoint(
            context: Mapping[str, Any],
            completed: Mapping[str, Mapping[str, Any]],
        ) -> None:
            _checkpoint_manifest_resume_cache(
                paper_folder, resume_bindings, context, completed
            )

        signature_maps[source_path] = run_lean_signature_manifests(
            ROOT,
            source_module,
            declaration_names,
            timeout_seconds=300,
            semantic_dependency_modules=dependency_modules,
            build_input_provider=build_input_provider,
            manifest_checkpoint=checkpoint,
        )
        missing_declarations = sorted(
            set(declaration_names) - set(signature_maps[source_path])
        )
        if progress is not None:
            progress(
                f"Lean manifest surface {source_module}: "
                f"{len(signature_maps[source_path])} available, "
                f"{len(missing_declarations)} missing"
            )
        if missing_declarations:
            sample = ", ".join(missing_declarations[:8])
            suffix = "" if len(missing_declarations) <= 8 else ", ..."
            print(
                "review-dashboard: exact Lean signature extraction incomplete "
                f"for {source_module} ({len(missing_declarations)} missing: "
                f"{sample}{suffix})",
                file=sys.stderr,
            )

    signature_manifests: dict[str, dict[str, Any]] = {}
    ambiguous_short_names: set[str] = set()
    for kind, name, full_name, _raw_sig, _comment, _line_number, source_path in parsed:
        if kind not in REVIEW_DECL_KINDS:
            continue
        manifest = signature_maps.get(source_path, {}).get(full_name)
        if manifest is None:
            continue
        signature_manifests[full_name] = manifest
        if name in signature_manifests and signature_manifests[name] is not manifest:
            ambiguous_short_names.add(name)
        else:
            signature_manifests[name] = manifest
    for name in ambiguous_short_names:
        signature_manifests.pop(name, None)
    SIGNATURE_MANIFEST_CACHE[str(paper_folder.resolve())] = signature_manifests
    llm_judgments = load_llm_statement_judgments(
        paper_folder, signature_manifests
    )
    semantic_judgment_index = _semantic_statement_judgment_index(llm_judgments)

    out: list[ReviewItem] = []
    for kind, name, full_name, raw_sig, doc_comment, line_number, source_path in parsed:
        if kind not in REVIEW_DECL_KINDS:
            continue
        check_map = check_maps.get(source_path, {})
        signature_manifest = signature_maps.get(source_path, {}).get(full_name)
        signature_sha256 = str(
            (signature_manifest or {}).get("sha256") or ""
        ).strip()
        check_statement = check_map.get(full_name) or check_map.get(name)
        definition_kinds = {"def", "abbrev", "structure", "class", "inductive"}
        lean_statement = raw_sig if kind in definition_kinds else (
            f"@{full_name} :\n{check_statement}" if check_statement else raw_sig
        )
        paper_text = paper_statement_for_review_row(
            paper_statements,
            component_statement_routes,
            name,
            full_name,
            component_navigation_keys=component_navigation_routes,
            direct_statement_routes=direct_statement_routes,
        )
        comment_text, source_status, source_note = split_source_metadata(doc_comment or "")
        if paper_text:
            displayed_paper_statement = paper_text
            source_status = source_status or "direct source text"
        else:
            displayed_paper_statement = comment_text
        agent_statement = (
            llm_tex_drafts.get(name)
            or llm_tex_drafts.get(full_name)
            or agent_preview_comment(
                doc_comment,
                lean_statement,
                None if kind in definition_kinds else check_statement,
            )
        )
        _semantic_key, semantic_judgment, semantic_ambiguous = (
            _current_semantic_statement_judgment(
                signature_sha256=signature_sha256,
                lean_statement=lean_statement,
                paper_statement=displayed_paper_statement,
                agent_statement=agent_statement,
                judgments=llm_judgments,
                identity_index=semantic_judgment_index,
            )
        )
        judgment = (
            semantic_judgment
            if semantic_judgment is not None
            else {}
            if semantic_ambiguous
            else llm_judgments.get(name) or llm_judgments.get(full_name) or {}
        )
        llm_match_stale = _llm_statement_judgment_is_stale(
            judgment,
            signature_sha256=signature_sha256,
            lean_statement=lean_statement,
            paper_statement=displayed_paper_statement,
            agent_statement=agent_statement,
        )
        is_assumption = name in assumption_names or full_name in assumption_names or is_assumption_item_name(name)
        is_proposition_spec = is_proposition_specification_manifest(signature_manifest)
        proposition_spec_proof = (
            proposition_spec_proofs.get(name)
            or proposition_spec_proofs.get(full_name)
            or ""
        )
        if not is_proposition_spec:
            proposition_spec_role = ""
        elif is_assumption:
            proposition_spec_role = "source_assumption"
        elif name in source_definition_names or full_name in source_definition_names:
            proposition_spec_role = "source_definition"
        elif proposition_spec_proof:
            proposition_spec_role = "proof_routed"
        else:
            proposition_spec_role = "unproved_spec"
        assumption_judgment = (
            assumption_judgments.get(name)
            or assumption_judgments.get(full_name)
            or {}
        )
        llm_assumption_stale = False
        if assumption_judgment:
            recorded_lean = assumption_judgment.get("lean_statement_sha256", "")
            recorded_paper = assumption_judgment.get("paper_statement_sha256", "")
            llm_assumption_stale = (
                not recorded_lean
                or not recorded_paper
                or
                (
                    recorded_lean not in lean_statement_digest_candidates(lean_statement, raw_sig)
                )
                or (recorded_paper != statement_digest(displayed_paper_statement))
                or bool(assumption_judgment.get("prompt_version_stale"))
                or bool(assumption_judgment.get("metadata_missing"))
            )
            semantic_parent_receipt = assumption_judgment.get(
                "source_record_semantic_parent_v1"
            )
            if isinstance(semantic_parent_receipt, dict):
                llm_assumption_stale = llm_assumption_stale or (
                    assumption_judgment.get("lean_signature_sha256")
                    != signature_sha256
                    or str(
                        semantic_parent_receipt.get("lean_signature_sha256") or ""
                    ).strip().lower()
                    != signature_sha256
                )
        out.append(
            ReviewItem(
                name=name,
                kind=kind,
                lean_statement=lean_statement,
                paper_statement=displayed_paper_statement,
                agent_statement=agent_statement,
                full_name=full_name,
                interface_source=raw_sig,
                lean_signature_manifest=signature_manifest,
                lean_signature_sha256=signature_sha256,
                source_status=source_status,
                source_note=source_note,
                llm_match_judgment=judgment.get("judgment", ""),
                llm_match_reason=judgment.get("reason", "") or judgment.get("comment", ""),
                llm_match_stale=llm_match_stale,
                llm_match_source=judgment.get("source", ""),
                llm_match_validator=judgment.get("validator", ""),
                llm_match_validator_type=judgment.get("validator_type", ""),
                llm_match_validated_at=judgment.get("validated_at", ""),
                llm_match_lean_statement_sha256=judgment.get("lean_statement_sha256", ""),
                llm_match_lean_signature_sha256=judgment.get("lean_signature_sha256", ""),
                llm_match_paper_statement_sha256=judgment.get("paper_statement_sha256", ""),
                llm_match_tex_statement_sha256=judgment.get("tex_statement_sha256", ""),
                llm_match_resolution=judgment.get("resolution", ""),
                llm_match_boundary_type=judgment.get("boundary_type", ""),
                llm_match_boundary_names=judgment.get("boundary_names") or [],
                llm_match_conditional_premises=judgment.get("conditional_premises") or [],
                llm_match_resolution_reason=judgment.get("resolution_reason", ""),
                llm_match_source_routes=(
                    judgment.get("source_routes")
                    if isinstance(judgment.get("source_routes"), list)
                    else []
                ),
                llm_match_component_target_sha256=(
                    _validated_unique_source_component_target_sha256(judgment)
                ),
                is_assumption=is_assumption,
                is_proposition_spec=is_proposition_spec,
                proposition_spec_role=proposition_spec_role,
                proposition_spec_proof=proposition_spec_proof,
                llm_assumption_judgment=assumption_judgment.get("judgment", ""),
                llm_assumption_reason=assumption_judgment.get("reason", "")
                or assumption_judgment.get("comment", ""),
                llm_assumption_stale=llm_assumption_stale,
                llm_assumption_source=assumption_judgment.get("source", ""),
                llm_assumption_validator=assumption_judgment.get("validator", ""),
                llm_assumption_validator_type=assumption_judgment.get("validator_type", ""),
                llm_assumption_validated_at=assumption_judgment.get("validated_at", ""),
                llm_assumption_lean_statement_sha256=assumption_judgment.get("lean_statement_sha256", ""),
                llm_assumption_paper_statement_sha256=assumption_judgment.get("paper_statement_sha256", ""),
                llm_assumption_premise_judgments=assumption_judgment.get("premise_judgments") or {},
                line_number=line_number,
            )
        )
    attach_current_lean_semantic_contract_results(
        paper_folder,
        interface_path,
        out,
        build_input_provider=build_input_provider,
    )
    result = apply_review_slices(paper_folder, out)
    if (
        owns_build_input_provider
        and not build_input_provider.finalize_unchanged()
    ):
        raise RuntimeError(
            f"repository build inputs changed while extracting {paper_folder.name}"
        )
    return result


def collected_paper_statements(
    paper_folder: Path, report_path: Path | None = None
) -> dict[str, str]:
    """Collect display statements without elaborating any Lean declarations."""

    paper_statements = (
        parse_report_texts(report_path)
        if report_path is not None and _dashboard_is_file(report_path)
        else {}
    )
    source_statements = parse_paper_tex_statements(paper_folder)
    if not source_statements:
        source_statements = parse_paper_text_statements(paper_folder)
    paper_statements.update(source_statements)
    paper_statements.update(parse_paper_statement_map(paper_folder))
    # Preserve the legacy display collection API for callers that inspect raw
    # navigation keys. Extraction and cache rebind do not trust these aliases:
    # they resolve each route to one exact full declaration and exclude the raw
    # navigation keys from ordinary heuristic fallback.
    paper_statements.update(
        {
            row: str(component.get("statement") or "")
            for row, component in review_source_component_statement_routes(
                paper_folder
            ).items()
            if str(component.get("statement") or "").strip()
        }
    )
    return paper_statements


def _statement_rebind_review_rows(
    folder: Path,
) -> list[tuple[str, str, str, str, str | None, int, Path]]:
    """Return every current declaration that can contribute a cached row."""

    parsed = parse_review_source_declarations(review_source_file(folder))
    assumption_names = review_assumption_names(folder)
    assumption_path = assumption_source_file(folder)
    if assumption_names and assumption_path != review_source_file(folder):
        if _dashboard_is_file(assumption_path):
            parsed.extend(parse_review_source_declarations(assumption_path))
    return parsed


def cached_direct_source_route_statements_are_current(
    folder: Path, items: Iterable[ReviewItem]
) -> bool:
    """Whether cached direct-route displays equal current map statements.

    This is a lightweight cache invariant.  It does not inspect semantic
    sidecars or Lean names heuristically: it compares each cached row's exact
    qualified declaration against the source map's explicit direct route.
    Rows without one such route retain their ordinary display policy.
    """

    parsed = _statement_rebind_review_rows(folder)
    direct_routes = resolved_direct_source_statement_routes(folder, parsed)
    by_name: dict[str, list[tuple[str, str, str, str, str | None, int, Path]]] = {}
    for row in parsed:
        if row[0] in REVIEW_DECL_KINDS:
            by_name.setdefault(row[1], []).append(row)
    for item in items:
        candidates = [
            row
            for row in by_name.get(item.name, [])
            if row[0] == item.kind and row[3] == item.interface_source
        ]
        if len(candidates) != 1:
            # The ordinary cache rebind validates this carrier identity before
            # it can use a row.  Do not guess a direct route here.
            continue
        expected = direct_routes.get(candidates[0][2])
        if expected and normalize_statement(item.paper_statement) != expected:
            return False
    return True


def rebind_cached_report_statements(
    folder: Path, items: list[ReviewItem]
) -> bool:
    """Refresh report-derived display text without repeating Lean Meta work.

    A report can change a dashboard row's human-facing source text while the
    review-surface Lean declarations are byte-for-byte unchanged.  Reparse the
    lightweight declaration comments and report/source text, then preserve the
    cached elaborated manifests only when every cached row still identifies the
    same declaration.  Any source mismatch falls back to the normal full
    extraction path.
    """

    report_path = paper_relative_file(
        folder, FINAL_VALIDATION_REPORT_FILE, "FINAL_VALIDATION_REPORT.md"
    )
    paper_statements = collected_paper_statements(folder, report_path)
    parsed = _statement_rebind_review_rows(folder)
    component_navigation_routes = review_source_component_statement_routes(folder)
    component_statement_routes = resolved_review_source_component_statement_routes(
        folder,
        parsed,
        component_routes=component_navigation_routes,
    )
    direct_statement_routes = resolved_direct_source_statement_routes(folder, parsed)

    by_name: dict[str, list[tuple[str, str, str, str, str | None, int, Path]]] = {}
    for row in parsed:
        kind, name, _full_name, _raw_sig, _comment, _line_number, _source_path = row
        if kind in REVIEW_DECL_KINDS:
            by_name.setdefault(name, []).append(row)

    for item in items:
        candidates = [
            row
            for row in by_name.get(item.name, [])
            if row[0] == item.kind and row[3] == item.interface_source
        ]
        if len(candidates) != 1:
            return False
        _kind, name, full_name, _raw_sig, doc_comment, _line_number, _source_path = candidates[0]
        item.full_name = full_name
        paper_text = paper_statement_for_review_row(
            paper_statements,
            component_statement_routes,
            name,
            full_name,
            component_navigation_keys=component_navigation_routes,
            direct_statement_routes=direct_statement_routes,
        )
        comment_text, source_status, source_note = split_source_metadata(doc_comment or "")
        if paper_text:
            item.paper_statement = paper_text
            item.source_status = source_status or "direct source text"
            item.source_note = source_note
        else:
            item.paper_statement = comment_text
            item.source_status = source_status
            item.source_note = source_note
    return True


def rebind_cached_review_status(
    folder: Path, items: list[ReviewItem]
) -> list[ReviewItem] | None:
    """Refresh status-derived row labels and proposition classifications."""

    rebound = apply_review_slices(folder, items)
    if len(rebound) != len(items):
        return None
    interface_path = review_source_file(folder)
    parsed = parse_review_source_declarations(interface_path)
    assumption_names = review_assumption_names(folder)
    assumption_path = assumption_source_file(folder)
    if (
        assumption_names
        and assumption_path.resolve() != interface_path.resolve()
        and _dashboard_is_file(assumption_path)
    ):
        for row in parse_review_source_declarations(assumption_path):
            _kind, name, full_name, _raw_sig, _comment, _line_number, _source_path = row
            if (
                name in assumption_names
                or full_name in assumption_names
                or is_assumption_item_name(name)
            ):
                parsed.append(row)
    source_definition_names = review_source_definition_names(folder)
    proposition_spec_proofs = review_proposition_spec_proofs(folder)
    for item in rebound:
        candidates = [
            row
            for row in parsed
            if row[0] == item.kind
            and row[1] == item.name
            and (not item.interface_source or row[3] == item.interface_source)
        ]
        if item.full_name:
            candidates = [row for row in candidates if row[2] == item.full_name]
        elif len(candidates) > 1 and item.line_number:
            line_candidates = [row for row in candidates if row[5] == item.line_number]
            if len(line_candidates) == 1:
                candidates = line_candidates
        if len(candidates) != 1:
            return None
        item.full_name = candidates[0][2]
        item.interface_source = candidates[0][3]
        prior_proof = item.proposition_spec_proof
        proof = (
            proposition_spec_proofs.get(item.name)
            or proposition_spec_proofs.get(item.full_name)
            or ""
        )
        item.proposition_spec_proof = proof
        if proof != prior_proof:
            item.semantic_contract_lean_match_verified = None
            item.semantic_contract_lean_transparency_verified = None
        if not item.is_proposition_spec:
            item.proposition_spec_role = ""
        elif item.is_assumption:
            item.proposition_spec_role = "source_assumption"
        elif (
            item.name in source_definition_names
            or item.full_name in source_definition_names
        ):
            item.proposition_spec_role = "source_definition"
        elif proof:
            item.proposition_spec_role = "proof_routed"
        else:
            item.proposition_spec_role = "unproved_spec"
    return rebound


def cached_rows_match_current_extraction_surface(
    folder: Path, items: list[ReviewItem]
) -> bool:
    """Check cached row selection against current Lean sources without Lean."""

    interface_path = review_source_file(folder)
    include_names = review_filter_names(folder)
    assumption_names = review_assumption_names(folder)
    auxiliary_names = review_auxiliary_names(folder)
    parsed = parse_review_source_declarations(interface_path)
    assumption_path = assumption_source_file(folder)
    if (
        assumption_names
        and assumption_path.resolve() != interface_path.resolve()
        and _dashboard_is_file(assumption_path)
    ):
        for row in parse_review_source_declarations(assumption_path):
            _kind, name, full_name, _raw_sig, _comment, _line_number, _source_path = row
            if (
                name in assumption_names
                or full_name in assumption_names
                or is_assumption_item_name(name)
            ):
                parsed.append(row)
    expected = sorted(
        (kind, name, raw_sig)
        for kind, name, _full_name, raw_sig, _comment, _line_number, _source_path in parsed
        if kind in REVIEW_DECL_KINDS
        and _review_name_survives_surface_filter(
            name, include_names, assumption_names, auxiliary_names
        )
    )
    recorded = sorted(
        (item.kind, item.name, item.interface_source) for item in items
    )
    return recorded == expected


def paper_title(folder: Path) -> str:
    readme = folder / "README.md"
    if readme.exists():
        for line in readme.read_text(encoding="utf-8").splitlines():
            if line.startswith("# "):
                return line[2:].strip()
    return folder.name


def iter_paper_folders(paper_filter: str | None = None) -> list[Path]:
    """Return paper directories that have a human-review Lean surface."""

    folders: list[Path] = []
    active = active_paper_names() if paper_filter is None else set()
    for folder in sorted(PAPERS_DIR.iterdir()):
        if not folder.is_dir():
            continue
        if folder.name == "TEMPLATE":
            continue
        if paper_filter and folder.name != paper_filter:
            continue
        if folder.name in active:
            continue
        if find_review_source_file(folder) is None:
            continue
        folders.append(folder)
    return folders


def paper_review_log_file(paper: str | Path) -> Path:
    """Return the default per-paper trace file path for a paper."""

    folder = PAPERS_DIR / str(paper)
    if not folder.exists() or not folder.is_dir():
        raise ValueError(f"unknown paper folder: {paper}")
    if find_review_source_file(folder) is None:
        raise ValueError(f"no human review Lean surface for paper: {paper}")
    return folder / ".review_traces" / DEFAULT_PAPER_LOG_FILE


def paper_interface_cache_file(paper: str | Path) -> Path:
    """Return the local sidecar file for cached declaration and statement rows."""

    folder = PAPERS_DIR / str(paper)
    if not folder.exists() or not folder.is_dir():
        raise ValueError(f"unknown paper folder: {paper}")
    if find_review_source_file(folder) is None:
        raise ValueError(f"no human review Lean surface for paper: {paper}")
    return folder / ".review_traces" / DEFAULT_PAPER_INTERFACE_CACHE_FILE


def manifest_resume_cache_directory(paper: str | Path) -> Path:
    """Return the ignored, non-authoritative manifest-resume cache directory.

    These files make a resource-bounded dashboard refresh resumable. They are
    intentionally separate from the authenticated manifest authority and may
    never supply audit evidence by themselves.
    """

    folder = Path(paper)
    if not folder.is_absolute():
        # Callers commonly already hold a repository-relative paper directory
        # such as ``papers/Foo``. Prefixing it with ``PAPERS_DIR`` created the
        # separate ignored tree ``papers/papers/Foo`` and discarded reusable
        # manifest work. Normalize the path coordinate once, independently of
        # a paper's declaration or audit content.
        folder = (
            ROOT / folder
            if folder.parts and folder.parts[0] == PAPERS_DIR.name
            else PAPERS_DIR / folder
        )
    return folder / ".review_traces" / MANIFEST_RESUME_CACHE_DIRNAME


def _manifest_resume_binding(
    folder: Path,
    *,
    qualified_declaration: str,
    declaration_kind: str,
    lean_source_declaration: str,
    source_path: Path,
) -> dict[str, str] | None:
    """Bind a resume record to exact current source text, not a row name alone."""

    try:
        resolved_source_path = source_path.resolve()
        source_file = resolved_source_path.relative_to(folder.resolve()).as_posix()
    except (OSError, ValueError):
        return None
    qualified = qualified_declaration.strip()
    source = lean_source_declaration.strip()
    kind = declaration_kind.strip()
    source_file_sha256 = _file_sha256(resolved_source_path)
    if (
        not qualified
        or not source
        or kind not in REVIEW_DECL_KINDS
        or not source_file
        or not re.fullmatch(r"[0-9a-f]{64}", source_file_sha256)
    ):
        return None
    return {
        "qualified_declaration": qualified,
        "source_file": source_file,
        "source_file_sha256": source_file_sha256,
        "declaration_kind": kind,
        "lean_source_declaration": source,
    }


def _manifest_resume_binding_digest(binding: Mapping[str, Any]) -> str:
    """Return the stable path key for one exact source declaration binding."""

    required = {
        "qualified_declaration",
        "source_file",
        "source_file_sha256",
        "declaration_kind",
        "lean_source_declaration",
    }
    if set(binding) != required or any(
        not isinstance(binding.get(field), str) or not binding[field].strip()
        for field in required
    ):
        return ""
    return hashlib.sha256(
        json.dumps(
            dict(binding), ensure_ascii=True, sort_keys=True, separators=(",", ":")
        ).encode("utf-8")
    ).hexdigest()


def _manifest_resume_cache_entry_path(
    folder: Path,
    context_sha256: str,
    binding: Mapping[str, Any],
) -> Path | None:
    """Return one deterministic local path for a context/source-bound receipt."""

    if not re.fullmatch(r"[0-9a-f]{64}", context_sha256):
        return None
    binding_sha256 = _manifest_resume_binding_digest(binding)
    if not binding_sha256:
        return None
    return (
        manifest_resume_cache_directory(folder)
        / context_sha256
        / f"{binding_sha256}.json"
    )


def _atomic_write_manifest_resume_payload(path: Path, payload: Mapping[str, Any]) -> None:
    """Atomically write one local optimization record.

    Per-declaration paths avoid a shared mutable index, so an interruption can
    lose at most the row currently being written and concurrent refreshes do
    not overwrite unrelated completed rows.
    """

    path.parent.mkdir(parents=True, exist_ok=True)
    encoded = json.dumps(payload, ensure_ascii=True, sort_keys=True) + "\n"
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    temporary = Path(temporary_name)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
            handle.write(encoded)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
        # Persist the directory entry as well as the file contents when the
        # host supports directory fsync. A crash can otherwise lose a just
        # checkpointed rename even though the payload was flushed.
        try:
            directory_descriptor = os.open(
                path.parent, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
            )
            try:
                os.fsync(directory_descriptor)
            finally:
                os.close(directory_descriptor)
        except OSError:
            pass
    finally:
        try:
            temporary.unlink()
        except FileNotFoundError:
            pass


def checkpoint_manifest_resume_records(
    folder: Path,
    bindings: Mapping[str, Mapping[str, str]],
    context: Mapping[str, Any],
    manifests: Mapping[str, Mapping[str, Any]],
) -> set[str]:
    """Persist exact completed manifests as non-authoritative resume records.

    The caller must already have obtained the manifests from a successful Lean
    extraction.  This helper deliberately records neither audit credit nor a
    claim that the caller's source route is current: consumers still require
    the separately tracked authority/carrier pair, an independently rebuilt
    source binding, and the exact compiled context before the record can seed
    a cache.  Returning only successfully checkpointed coordinates lets a
    producer report the optimization without making its raw result depend on
    persistence.
    """

    context_sha256 = signature_manifest_cache_context_sha256(context)
    if not re.fullmatch(r"[0-9a-f]{64}", context_sha256):
        return set()
    checkpointed: set[str] = set()
    for qualified, raw_manifest in manifests.items():
        binding = bindings.get(qualified)
        if not isinstance(binding, Mapping) or not isinstance(raw_manifest, Mapping):
            continue
        path = _manifest_resume_cache_entry_path(folder, context_sha256, binding)
        manifest = dict(raw_manifest)
        signature = str(manifest.get("sha256") or "").strip().lower()
        if (
            path is None
            or not re.fullmatch(r"[0-9a-f]{64}", signature)
            or signature_manifest_digest(manifest) != signature
        ):
            continue
        payload = {
            "schema": MANIFEST_RESUME_CACHE_SCHEMA,
            "paper": folder.name,
            "non_authoritative_resume_cache": MANIFEST_RESUME_CACHE_NON_AUTHORITATIVE,
            "manifest_cache_context_sha256": context_sha256,
            "binding": dict(binding),
            "manifest": manifest,
        }
        try:
            _atomic_write_manifest_resume_payload(path, payload)
        except OSError:
            # The current extraction still has an in-memory receipt. A failed
            # checkpoint merely means a later process must ask Lean again.
            continue
        checkpointed.add(qualified)
    return checkpointed


def _checkpoint_manifest_resume_cache(
    folder: Path,
    bindings: Mapping[str, Mapping[str, str]],
    context: Mapping[str, Any],
    manifests: Mapping[str, Mapping[str, Any]],
) -> None:
    """Compatibility wrapper for existing interrupted-refresh call sites."""

    checkpoint_manifest_resume_records(folder, bindings, context, manifests)


def _load_manifest_resume_cache_entry(
    path: Path,
    *,
    paper: str,
    context_sha256: str,
    binding: Mapping[str, str],
) -> dict[str, Any] | None:
    """Load one cache record only when it binds this exact context and source."""

    try:
        if path.stat().st_size > 256 * 1024 * 1024:
            return None
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        return None
    if (
        not isinstance(payload, dict)
        or set(payload)
        != {
            "schema",
            "paper",
            "non_authoritative_resume_cache",
            "manifest_cache_context_sha256",
            "binding",
            "manifest",
        }
        or payload.get("schema") != MANIFEST_RESUME_CACHE_SCHEMA
        or payload.get("paper") != paper
        or payload.get("non_authoritative_resume_cache") is not True
        or payload.get("manifest_cache_context_sha256") != context_sha256
        or payload.get("binding") != dict(binding)
        or not isinstance(payload.get("manifest"), Mapping)
    ):
        return None
    manifest = dict(payload["manifest"])
    signature = str(manifest.get("sha256") or "").strip().lower()
    if (
        not re.fullmatch(r"[0-9a-f]{64}", signature)
        or signature_manifest_digest(manifest) != signature
    ):
        return None
    return manifest


def current_manifest_resume_records(
    folder: Path,
    *,
    context: Mapping[str, Any],
    bindings: Mapping[str, Mapping[str, str]],
) -> dict[str, dict[str, Any]]:
    """Load source-bound local resume records without granting them credit.

    The returned records remain ignored optimization data.  Consumers must pass
    them through exact-context authority/carrier attestation before reuse.
    Keeping the loader separate lets source-record scans use their frozen
    current source bindings instead of consulting a stale prior raw audit.
    """

    context_sha256 = signature_manifest_cache_context_sha256(context)
    if not re.fullmatch(r"[0-9a-f]{64}", context_sha256):
        return {}
    recovered: dict[str, dict[str, Any]] = {}
    for qualified, binding in bindings.items():
        path = _manifest_resume_cache_entry_path(folder, context_sha256, binding)
        if path is None:
            continue
        manifest = _load_manifest_resume_cache_entry(
            path,
            paper=folder.name,
            context_sha256=context_sha256,
            binding=binding,
        )
        if manifest is not None:
            recovered[qualified] = {
                "manifest_cache_context_sha256": context_sha256,
                "binding": dict(binding),
                "manifest": manifest,
            }
    return recovered


def _prime_manifest_resume_cache(
    folder: Path,
    *,
    import_module: str,
    semantic_dependency_modules: tuple[str, ...],
    context: Mapping[str, Any],
    bindings: Mapping[str, Mapping[str, str]],
    progress: Callable[[str], None] | None = None,
) -> set[str]:
    """Seed checkpointed rows only after carrier-backed current validation.

    The journal is not evidence and never supplies a Lean graph for cache
    authority.  It contributes only the exact source binding parsed when its
    completed row was checkpointed.  The authenticated carrier supplies the
    manifest after the record's Lean payload, current source binding, exact
    compiled context, and current reached artifacts all agree.  If that exact
    fast path has no accepted row, a tracked carrier from an earlier context
    may be retained only after every candidate receives a fresh compact Lean
    revalidation.  A miss remains a miss; this helper never treats the journal
    as source or audit evidence.
    """

    recovered = current_manifest_resume_records(
        folder, context=context, bindings=bindings
    )
    if not recovered:
        return set()
    try:
        accepted, exact_diagnostics = prime_exact_context_attested_resume_manifests(
            root=ROOT,
            paper_dir=folder,
            import_module=import_module,
            semantic_dependency_modules=semantic_dependency_modules,
            current_context=context,
            current_bindings=bindings,
            resume_records=recovered,
        )
    except Exception:  # noqa: BLE001 - journal reuse must remain a cache miss.
        return set()
    if isinstance(accepted, Mapping) and accepted:
        return set(accepted)

    # A swapped or otherwise unattested journal payload is not an
    # interrupted current computation.  Do not turn that integrity failure
    # into authority for a recovery revalidation merely because the source
    # coordinate still exists.
    rejected_by_reason = (
        exact_diagnostics.get("rejected_by_reason", {})
        if isinstance(exact_diagnostics, Mapping)
        else {}
    )
    if (
        isinstance(exact_diagnostics, Mapping)
        and exact_diagnostics.get("store_status") == "resume_payload_not_attested"
    ) or (
        isinstance(rejected_by_reason, Mapping)
        and bool(rejected_by_reason.get("resume_payload_not_attested"))
    ):
        return set()

    try:
        recovered_accepted, recovery_diagnostics = (
            prime_attested_resume_manifests_with_current_revalidation(
                root=ROOT,
                paper_dir=folder,
                import_module=import_module,
                semantic_dependency_modules=semantic_dependency_modules,
                current_context=context,
                current_bindings=bindings,
                resume_records=recovered,
            )
        )
    except Exception:  # noqa: BLE001 - journal reuse must remain a cache miss.
        return set()
    accepted_names = (
        set(recovered_accepted)
        if isinstance(recovered_accepted, Mapping)
        else set()
    )
    requested_revalidations = int(
        recovery_diagnostics.get("item_revalidation_requested_count") or 0
    ) if isinstance(recovery_diagnostics, Mapping) else 0
    if progress is not None and requested_revalidations:
        progress(
            "manifest resume recovery compact-Lean revalidated "
            f"{requested_revalidations} checkpointed declaration(s); "
            f"reused {len(accepted_names)}"
        )
    return accepted_names


_LEAN_EXTRACTION_REVIEW_SURFACE_FIELDS = {
    "source_file",
    "human_source_file",
    "assumption_source_file",
    "include_names",
    "assumption_names",
    "auxiliary_names",
}


def _review_surface_static_status_digest(status_source: str) -> str:
    """Hash only status fields that determine extracted review rows.

    LLM sidecar policies, paper status labels, and validation receipts are
    rebound dynamically.  Re-extracting elaborated Lean signatures after any
    of those changes is costly and contributes no additional soundness.
    Review-surface selection and source-file fields remain cache inputs.
    """

    try:
        status_payload = json.loads(status_source)
    except json.JSONDecodeError:
        return statement_digest(status_source)
    if not isinstance(status_payload, dict):
        return statement_digest(status_source)
    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return statement_digest("")
    static_surface = {
        key: review_surface.get(key)
        for key in sorted(_LEAN_EXTRACTION_REVIEW_SURFACE_FIELDS)
        if key in review_surface
    }
    return statement_digest(
        json.dumps(static_surface, ensure_ascii=True, sort_keys=True, separators=(",", ":"))
    )


def _review_surface_display_status_digest(status_source: str) -> str:
    """Hash status metadata that changes paper-facing statement display."""

    try:
        status_payload = json.loads(status_source)
    except json.JSONDecodeError:
        return statement_digest("")
    if not isinstance(status_payload, dict):
        return statement_digest("")
    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return statement_digest("")
    component_routes = review_surface.get("source_component_statement_routes")
    display_identity: dict[str, Any] = {
        "source_component_statement_routes": component_routes
    }
    if isinstance(component_routes, list) and component_routes:
        # Bump only caches that use row-specific component display.  This
        # activates the no-Lean rebind for caches written before qualified,
        # ambiguity-checked component precedence was enforced.
        display_identity["source_component_display_binding_schema"] = (
            SOURCE_COMPONENT_DISPLAY_BINDING_SCHEMA
        )
    return statement_digest(
        json.dumps(
            display_identity,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        )
    )


def _review_surface_rebind_status_digest(status_source: str) -> str:
    """Hash all review metadata that does not require Lean extraction."""

    try:
        status_payload = json.loads(status_source)
    except json.JSONDecodeError:
        return statement_digest("")
    if not isinstance(status_payload, dict):
        return statement_digest("")
    review_surface = status_payload.get("review_surface")
    if not isinstance(review_surface, dict):
        return statement_digest("")
    rebind_surface = {
        key: value
        for key, value in review_surface.items()
        if key not in _LEAN_EXTRACTION_REVIEW_SURFACE_FIELDS
    }
    return statement_digest(
        json.dumps(
            rebind_surface,
            ensure_ascii=True,
            sort_keys=True,
            separators=(",", ":"),
        )
    )


def _cache_source_hashes(
    folder: Path,
    *,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
) -> dict[str, str]:
    owns_build_input_provider = build_input_provider is None
    if build_input_provider is None:
        # Cache writers already pass the run's Lean-authored provider.  A
        # standalone cache reader must use the same authority instead of
        # silently switching repository_build_input_snapshot to its legacy
        # Python import-parser compatibility path.
        build_input_provider = RepositoryBuildInputSnapshotProvider(ROOT)
    interface_path = review_source_file(folder)
    report_path = paper_relative_file(
        folder, FINAL_VALIDATION_REPORT_FILE, "FINAL_VALIDATION_REPORT.md"
    )
    tex_path = find_paper_tex_source(folder)
    text_path = find_paper_text(folder)
    pdf_path = find_paper_pdf(folder)
    statement_map_path = folder / PAPER_STATEMENT_MAP_FILE
    status_path = folder / DEFAULT_PAPER_STATUS_FILE

    interface_source = (
        _dashboard_read_text(interface_path) if _dashboard_is_file(interface_path) else ""
    )
    report_source = (
        _dashboard_read_text(report_path) if _dashboard_is_file(report_path) else ""
    )
    tex_source = _dashboard_read_text(tex_path) if tex_path is not None else ""
    text_source = _dashboard_read_text(text_path) if text_path is not None else ""
    statement_map_source = (
        _dashboard_read_text(statement_map_path)
        if _dashboard_is_file(statement_map_path)
        else ""
    )
    status_source = (
        _dashboard_read_text(status_path) if _dashboard_is_file(status_path) else ""
    )
    selected_modules = {review_source_module(folder, interface_path)}
    assumption_path = assumption_source_file(folder)
    if _selected_assumption_source_is_required(
        folder, interface_path, assumption_path
    ):
        selected_modules.add(review_source_module(folder, assumption_path))
    lean_source_closure = {
        module: repository_build_input_snapshot(
            ROOT,
            module,
            provider=build_input_provider,
        )
        or ""
        for module in sorted(selected_modules)
    }

    hashes = {
        "review_source_file": interface_path.name,
        "interface_sha256": statement_digest(interface_source),
        "report_sha256": statement_digest(report_source),
        "tex_sha256": statement_digest(tex_source),
        "text_sha256": statement_digest(text_source),
        "pdf_sha256": _file_sha256(pdf_path),
        "paper_statement_map_sha256": statement_digest(statement_map_source),
        "review_surface_static_sha256": _review_surface_static_status_digest(
            status_source
        ),
        "review_surface_display_sha256": _review_surface_display_status_digest(
            status_source
        ),
        "review_surface_rebind_sha256": _review_surface_rebind_status_digest(
            status_source
        ),
        "lean_source_closure_sha256": statement_digest(
            json.dumps(
                lean_source_closure,
                ensure_ascii=True,
                sort_keys=True,
                separators=(",", ":"),
            )
        ),
    }
    if (
        owns_build_input_provider
        and not build_input_provider.finalize_unchanged()
    ):
        raise RuntimeError(
            f"Lean source-closure inputs changed while hashing {folder.name}"
        )
    return hashes


def _selected_assumption_source_is_required(
    folder: Path, interface_path: Path, assumption_path: Path
) -> bool:
    """Whether the separate assumption module contributes a selected row."""

    assumption_names = review_assumption_names(folder)
    if (
        not assumption_names
        or assumption_path.resolve() == interface_path.resolve()
        or not _dashboard_is_file(assumption_path)
    ):
        return False
    include_names = review_filter_names(folder)
    auxiliary_names = review_auxiliary_names(folder)
    for row in parse_review_source_declarations(assumption_path):
        _kind, name, full_name, _raw_sig, _comment, _line_number, _source_path = row
        if (
            name not in assumption_names
            and full_name not in assumption_names
            and not is_assumption_item_name(name)
        ):
            continue
        if _review_name_survives_surface_filter(
            name, include_names, assumption_names, auxiliary_names
        ):
            return True
    return False


def _current_review_signature_contexts(
    folder: Path,
    *,
    build_input_provider: RepositoryBuildInputSnapshotProvider,
) -> dict[str, Any] | None:
    """Build review modules and return the cache context for their manifests."""

    folder_root = folder.resolve()
    interface_path = review_source_file(folder)
    source_paths = {interface_path}
    assumption_path = assumption_source_file(folder)
    if _selected_assumption_source_is_required(
        folder, interface_path, assumption_path
    ):
        source_paths.add(assumption_path)
    contexts: dict[str, Any] = {}
    for source_path in sorted(source_paths):
        source_module = review_source_module(folder, source_path)
        dependency_modules = paper_owned_module_names_in_import_closure(
            ROOT,
            folder,
            source_module,
            provider=build_input_provider,
        )
        if not dependency_modules:
            return None
        context = signature_manifest_cache_context(
            ROOT,
            source_module,
            semantic_dependency_modules=dependency_modules,
            build_input_provider=build_input_provider,
        )
        if context is None:
            return None
        try:
            cache_key = str(source_path.resolve().relative_to(folder_root))
        except ValueError:
            return None
        contexts[cache_key] = context
    return contexts


def current_review_signature_contexts(
    folder: Path,
    *,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
    audit_inputs: DashboardAuditInputs | None = None,
) -> dict[str, Any] | None:
    """Build review modules from one immutable shared fallback snapshot."""

    if audit_inputs is not None:
        with dashboard_audit_input_scope(audit_inputs):
            return current_review_signature_contexts(
                folder,
                build_input_provider=build_input_provider,
            )
    owns_build_input_provider = build_input_provider is None
    if build_input_provider is None:
        build_input_provider = RepositoryBuildInputSnapshotProvider(ROOT)
    contexts = _current_review_signature_contexts(
        folder,
        build_input_provider=build_input_provider,
    )
    if (
        owns_build_input_provider
        and not build_input_provider.finalize_unchanged()
    ):
        return None
    return contexts


def review_signature_manifest_authority_binding(
    *,
    qualified_declaration: str,
    source_file: str,
    lean_source_declaration: str,
    line_number: int,
    declaration_kind: str,
    elaborated_signature_sha256: str,
    elaborated_proposition_graph_sha256: str,
) -> dict[str, Any]:
    """Return the exact dashboard producer binding for one manifest root."""

    return {
        "qualified_declaration": qualified_declaration,
        "source_file": source_file,
        "lean_source_declaration": lean_source_declaration,
        "line_number": line_number,
        "declaration_kind": declaration_kind,
        "elaborated_signature_sha256": elaborated_signature_sha256,
        "elaborated_proposition_graph_sha256": (
            elaborated_proposition_graph_sha256
        ),
    }


def _review_signature_manifest_declarations(
    folder: Path,
) -> tuple[dict[str, tuple[str, str, int, Path]], set[str]]:
    """Parse the exact dashboard sources into unique qualified coordinates."""

    declarations: dict[str, tuple[str, str, int, Path]] = {}
    duplicates: set[str] = set()
    source_paths = {review_source_file(folder)}
    assumptions = assumption_source_file(folder)
    if _dashboard_is_file(assumptions):
        source_paths.add(assumptions)
    for source_path in sorted(source_paths):
        for (
            kind,
            _name,
            full_name,
            raw_signature,
            _comment,
            line_number,
            parsed_source_path,
        ) in parse_review_source_declarations(source_path):
            if full_name in duplicates:
                continue
            if full_name in declarations:
                declarations.pop(full_name, None)
                duplicates.add(full_name)
                continue
            declarations[full_name] = (
                kind,
                raw_signature,
                line_number,
                parsed_source_path,
            )
    return declarations, duplicates


def current_review_signature_manifest_source_coordinates(
    folder: Path,
) -> tuple[dict[str, dict[str, object]], set[str]]:
    """Return exact current selected review declarations for authority reuse.

    The qualified name is only a join coordinate.  Each returned value binds
    the current parser's exact declaration text, source-relative path, kind,
    and line number.  The tracked manifest authority independently pins the
    same coordinate together with Lean-derived identities; ambiguous routes
    are intentionally omitted and must be extracted again.
    """

    interface_path = review_source_file(folder)
    parsed = parse_review_source_declarations(interface_path)
    include_names = review_filter_names(folder)
    assumption_names = review_assumption_names(folder)
    auxiliary_names = review_auxiliary_names(folder)
    assumptions = assumption_source_file(folder)
    if (
        assumption_names
        and assumptions != interface_path
        and _dashboard_is_file(assumptions)
    ):
        for row in parse_review_source_declarations(assumptions):
            _kind, name, full_name, _raw, _comment, _line, _source = row
            if (
                name in assumption_names
                or full_name in assumption_names
                or is_assumption_item_name(name)
            ):
                parsed.append(row)

    coordinates: dict[str, dict[str, object]] = {}
    duplicates: set[str] = set()
    folder_root = folder.resolve()
    for kind, name, full_name, raw_signature, _comment, line_number, source_path in parsed:
        if (
            kind not in REVIEW_DECL_KINDS
            or not _review_name_survives_surface_filter(
                name, include_names, assumption_names, auxiliary_names
            )
        ):
            continue
        if full_name in duplicates:
            continue
        if full_name in coordinates:
            coordinates.pop(full_name, None)
            duplicates.add(full_name)
            continue
        try:
            source_file = source_path.resolve().relative_to(folder_root).as_posix()
        except (OSError, ValueError):
            duplicates.add(full_name)
            continue
        coordinates[full_name] = {
            "source_file": source_file,
            "lean_source_declaration": raw_signature,
            "line_number": line_number,
            "declaration_kind": kind,
        }
    return coordinates, duplicates


def current_review_signature_manifest_bindings(
    folder: Path,
    validated_configured_review_rows: Iterable[Mapping[str, Any]],
) -> dict[str, dict[str, Any]]:
    """Project independently validated raw rows onto exact dashboard sources.

    Qualified declaration names are lookup coordinates only.  Cache admission
    remains bound to exact source bytes, the Lean-owned signature/dependency/
    proposition-graph identities, and the separately current compiled context.
    Ambiguous or stale coordinates are omitted and therefore receive fresh Lean
    extraction rather than cache credit.
    """

    declarations, declaration_duplicates = (
        _review_signature_manifest_declarations(folder)
    )
    rows_by_qualified: dict[str, Mapping[str, Any]] = {}
    row_duplicates: set[str] = set()
    for raw_row in validated_configured_review_rows:
        if not isinstance(raw_row, Mapping):
            continue
        qualified = str(raw_row.get("qualified_declaration") or "").strip()
        if not qualified or qualified in row_duplicates:
            continue
        if qualified in rows_by_qualified:
            rows_by_qualified.pop(qualified, None)
            row_duplicates.add(qualified)
            continue
        rows_by_qualified[qualified] = raw_row

    root = ROOT.resolve()
    folder_root = folder.resolve()
    bindings: dict[str, dict[str, Any]] = {}
    for qualified, raw_row in sorted(rows_by_qualified.items()):
        if qualified in declaration_duplicates:
            continue
        declaration = declarations.get(qualified)
        if declaration is None:
            continue
        kind, raw_signature, line_number, source_path = declaration
        source_file = str(raw_row.get("source_file") or "").strip()
        source_sha256 = str(raw_row.get("source_sha256") or "").strip().lower()
        signature_sha256 = str(
            raw_row.get("elaborated_signature_sha256") or ""
        ).strip().lower()
        dependency_sha256 = str(
            raw_row.get("semantic_dependency_sha256") or ""
        ).strip().lower()
        proposition_graph_sha256 = (
            configured_review_row_proposition_graph_sha256(raw_row)
        )
        try:
            recorded_source = Path(source_file)
            if recorded_source.is_absolute():
                continue
            recorded_source = (root / recorded_source).resolve()
            recorded_source.relative_to(root)
            context_key = source_path.resolve().relative_to(folder_root).as_posix()
            exact_source = _dashboard_read_bytes(source_path)
        except (OSError, RuntimeError, ValueError, DashboardFrozenInputError):
            continue
        if (
            recorded_source != source_path.resolve()
            or not re.fullmatch(r"[0-9a-f]{64}", source_sha256)
            or hashlib.sha256(exact_source).hexdigest() != source_sha256
            or not re.fullmatch(r"[0-9a-f]{64}", signature_sha256)
            or not re.fullmatch(r"[0-9a-f]{64}", dependency_sha256)
            or not re.fullmatch(r"[0-9a-f]{64}", proposition_graph_sha256)
        ):
            continue
        authority_binding = review_signature_manifest_authority_binding(
            qualified_declaration=qualified,
            source_file=context_key,
            lean_source_declaration=raw_signature,
            line_number=line_number,
            declaration_kind=kind,
            elaborated_signature_sha256=signature_sha256,
            elaborated_proposition_graph_sha256=proposition_graph_sha256,
        )
        bindings[qualified] = {
            "authority_binding": authority_binding,
            "elaborated_signature_sha256": signature_sha256,
            "semantic_dependency_sha256": dependency_sha256,
            "elaborated_proposition_graph_sha256": proposition_graph_sha256,
        }
    return bindings


def _prior_review_manifest_reuse_inputs(
    folder: Path,
) -> tuple[
    tuple[Mapping[str, Any], ...],
    tuple[Mapping[str, Any], ...],
    dict[str, dict[str, str]],
] | None:
    """Load independently receipt-checked prior rows and their manifest context.

    This path is available only to an ordinary mutable cache refresh. Frozen
    closeout inputs already supply their transaction-owned current rows through
    ``validated_configured_review_rows`` and must not read an ignored carrier or
    mutable row cache behind that snapshot.
    """

    if _dashboard_audit_inputs() is not None:
        return None
    raw_path = folder / PAPER_AUDIT_DIR / "source_record_audit.json"
    cache_path = paper_interface_cache_file(folder)
    try:
        raw_payload = json.loads(raw_path.read_text(encoding="utf-8"))
        cache_payload = json.loads(cache_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        return None
    if not isinstance(raw_payload, dict) or not isinstance(cache_payload, dict):
        return None
    try:
        try:
            from scripts.audit_evidence_integrity import (
                source_record_raw_scan_completeness_error,
            )
            from scripts.source_record_integrity import (
                source_record_audit_receipt_error,
            )
        except ModuleNotFoundError:
            from audit_evidence_integrity import (  # type: ignore[no-redef]
                source_record_raw_scan_completeness_error,
            )
            from source_record_integrity import (  # type: ignore[no-redef]
                source_record_audit_receipt_error,
            )
        if source_record_audit_receipt_error(
            raw_payload
        ) or source_record_raw_scan_completeness_error(raw_payload):
            return None
    except Exception:  # noqa: BLE001 - prior evidence failure is a cache miss.
        return None

    raw_rows = raw_payload.get("configured_review_rows")
    if (
        raw_payload.get("paper") != folder.name
        or not isinstance(raw_rows, list)
        or raw_payload.get("configured_review_rows_count") != len(raw_rows)
        or raw_payload.get("missing_configured_review_rows") != []
        or any(not isinstance(row, Mapping) for row in raw_rows)
        or cache_payload.get("schema") != PAPER_INTERFACE_CACHE_SCHEMA
        or cache_payload.get("paper") != folder.name
        or not isinstance(cache_payload.get("signature_contexts"), Mapping)
    ):
        return None

    declarations, duplicate_declarations = _review_signature_manifest_declarations(
        folder
    )
    current: dict[str, dict[str, str]] = {}
    for raw_row in raw_rows:
        qualified = str(raw_row.get("qualified_declaration") or "").strip()
        declaration = declarations.get(qualified)
        if not qualified or qualified in duplicate_declarations or declaration is None:
            continue
        _kind, raw_signature, _line_number, source_path = declaration
        try:
            source_file = source_path.resolve().relative_to(ROOT).as_posix()
        except (OSError, ValueError):
            continue
        current[qualified] = {
            "lean_source_declaration": raw_signature,
            "source_file": source_file,
        }
    prior_contexts = tuple(
        context
        for context in cache_payload["signature_contexts"].values()
        if isinstance(context, Mapping)
    )
    return (
        tuple(row for row in raw_rows if isinstance(row, Mapping)),
        prior_contexts,
        current,
    )


def prime_review_signature_manifest_store_from_prior(
    folder: Path,
    signature_contexts: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    """Seed unchanged dashboard roots from authenticated prior evidence."""

    inputs = _prior_review_manifest_reuse_inputs(folder)
    if inputs is None:
        return {
            "schema": 1,
            "paper": folder.name,
            "requested_count": 0,
            "candidate_count": 0,
            "seeded_count": 0,
            "seeded_declarations": [],
            "fresh_required_count": 0,
            "rejected_by_reason": {},
            "store_status": "skipped_without_authenticated_prior_rows",
        }
    prior_rows, prior_contexts, current_declarations = inputs
    return prime_authenticated_manifest_store_with_item_revalidation(
        root=ROOT,
        paper_dir=folder,
        authenticated_prior_rows=prior_rows,
        current_declarations=current_declarations,
        prior_contexts=prior_contexts,
        current_contexts=(
            context
            for context in signature_contexts.values()
            if isinstance(context, Mapping)
        ),
    )[1]


def _unavailable_manifest_cache_context(*_args: Any, **_kwargs: Any) -> None:
    """Forbid a closeout cache prime from widening its supplied contexts."""

    return None


def prime_review_signature_manifest_store(
    folder: Path,
    signature_contexts: Mapping[str, Mapping[str, Any]],
    *,
    allow_migration_write: bool = True,
    validated_configured_review_rows: Iterable[Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    """Seed exact-context roots from current source or closeout bindings.

    Current source bindings are reconstructed only when a tracked authority
    carries that producer format.  Current raw source-record rows remain an
    additional stronger source when available.  Neither path permits
    changed-context item revalidation here: misses reach the ordinary fresh
    manifest extractor, while journal compatibility is handled separately by
    exact authority/carrier attestation.
    """

    # Strict closeout is read-only. The compatibility flag remains part of the
    # public dashboard API but never authorizes a migration or write here.
    _ = allow_migration_write
    configured_rows = (
        list(validated_configured_review_rows)
        if validated_configured_review_rows is not None
        else None
    )
    # A standalone dashboard has no transaction-owned source-record rows from
    # which to establish an independent current request.  Do not even inspect
    # the paper's review surface or authenticated store in that case: the
    # ignored/local cache must remain an ordinary fresh-extraction miss.
    if configured_rows is None:
        return {
            "schema": 1,
            "paper": folder.name,
            "candidate_count": 0,
            "context_count": 0,
            "accepted_context_count": 0,
            "context_provider_call_count": 0,
            "seeded_count": 0,
            "seeded_declarations": [],
            "fresh_required_count": 0,
            "rejected_by_reason": {},
            "store_status": "skipped_without_independent_current_bindings",
            "source_binding_count": 0,
            "source_binding_duplicates": [],
            "source_binding_store_status": "not_requested",
            "binding_conflicts": [],
            "configured_review_row_count": 0,
            "current_declaration_binding_count": 0,
        }
    source_coordinates, source_duplicates = (
        current_review_signature_manifest_source_coordinates(folder)
    )
    source_bindings, source_binding_diagnostics = (
        current_source_bound_manifest_bindings(
            paper_dir=folder,
            current_declarations={
                qualified: coordinate
                for qualified, coordinate in source_coordinates.items()
                if qualified not in source_duplicates
            },
        )
    )
    raw_bindings: dict[str, dict[str, Any]] = {}
    raw_bindings = current_review_signature_manifest_bindings(
        folder, configured_rows
    )
    bindings: dict[str, dict[str, Any]] = {
        qualified: dict(binding)
        for qualified, binding in source_bindings.items()
    }
    binding_conflicts: set[str] = set()
    for qualified, binding in raw_bindings.items():
        existing = bindings.get(qualified)
        if existing is not None and existing != binding:
            bindings.pop(qualified, None)
            binding_conflicts.add(qualified)
        elif qualified not in binding_conflicts:
            bindings[qualified] = dict(binding)
    current_contexts = [
        context
        for context in signature_contexts.values()
        if isinstance(context, Mapping)
    ]
    if bindings:
        _accepted, diagnostics = prime_authenticated_manifest_store(
            root=ROOT,
            paper_dir=folder,
            current_declaration_bindings=bindings,
            current_contexts=current_contexts,
            context_provider=_unavailable_manifest_cache_context,
        )
    else:
        diagnostics: dict[str, Any] = {
            "schema": 1,
            "paper": folder.name,
            "candidate_count": 0,
            "context_count": 0,
            "accepted_context_count": 0,
            "context_provider_call_count": 0,
            "seeded_count": 0,
            "seeded_declarations": [],
            "fresh_required_count": 0,
            "rejected_by_reason": {},
            "store_status": "skipped_without_reconstructable_current_bindings",
        }
    diagnostics["source_binding_count"] = len(source_bindings)
    diagnostics["source_binding_duplicates"] = sorted(source_duplicates)
    diagnostics["source_binding_store_status"] = str(
        source_binding_diagnostics.get("store_status") or ""
    )
    diagnostics["binding_conflicts"] = sorted(binding_conflicts)
    diagnostics["configured_review_row_count"] = (
        len(configured_rows) if configured_rows is not None else 0
    )
    diagnostics["current_declaration_binding_count"] = len(bindings)
    fresh_required = int(diagnostics.get("fresh_required_count") or 0)
    if fresh_required:
        raw_rejections = diagnostics.get("rejected_by_reason")
        rejection_summary = ""
        if isinstance(raw_rejections, Mapping) and raw_rejections:
            rejection_summary = "; misses: " + ", ".join(
                f"{reason}={len(declarations)}"
                for reason, declarations in sorted(raw_rejections.items())
                if isinstance(declarations, list)
            )
        print(
            "review-dashboard: authenticated manifest-store prime "
            f"seeded {int(diagnostics.get('seeded_count') or 0)} of "
            f"{int(diagnostics.get('candidate_count') or 0)} candidates; "
            f"{fresh_required} require fresh Lean{rejection_summary}",
            file=sys.stderr,
        )
    return diagnostics


def publish_review_signature_manifest_store(
    folder: Path,
    items: Iterable[ReviewItem],
    signature_contexts: Mapping[str, Mapping[str, Any]],
) -> set[str]:
    """Merge exact manifests from one successful strict dashboard extraction."""

    declarations: dict[str, tuple[str, int, Path]] = {}
    duplicates: set[str] = set()
    source_paths = {review_source_file(folder)}
    assumptions = assumption_source_file(folder)
    if _dashboard_is_file(assumptions):
        source_paths.add(assumptions)
    for source_path in sorted(source_paths):
        for (
            _kind,
            _name,
            full_name,
            raw_signature,
            _comment,
            line_number,
            parsed_source_path,
        ) in parse_review_source_declarations(source_path):
            if full_name in declarations:
                duplicates.add(full_name)
                continue
            declarations[full_name] = (
                raw_signature,
                line_number,
                parsed_source_path,
            )

    candidates: list[dict[str, Any]] = []
    for item in items:
        qualified = str(item.full_name or "").strip()
        declaration = declarations.get(qualified)
        manifest = item.lean_signature_manifest
        if (
            not qualified
            or qualified in duplicates
            or declaration is None
            or not isinstance(manifest, Mapping)
        ):
            continue
        try:
            context_key = str(declaration[2].resolve().relative_to(folder.resolve()))
        except ValueError:
            continue
        context = signature_contexts.get(context_key)
        if not isinstance(context, Mapping):
            continue
        candidates.append(
            {
                "qualified_declaration": qualified,
                "manifest": manifest,
                "context": context,
                "authority_binding": review_signature_manifest_authority_binding(
                    qualified_declaration=qualified,
                    source_file=context_key,
                    lean_source_declaration=declaration[0],
                    line_number=declaration[1],
                    declaration_kind=item.kind,
                    elaborated_signature_sha256=item.lean_signature_sha256,
                    elaborated_proposition_graph_sha256=(
                        elaborated_proposition_graph_sha256(
                            manifest.get("elaborated_proposition_graph")
                        )
                    ),
                ),
            }
        )
    return merge_authenticated_manifest_store(
        paper_dir=folder,
        paper=folder.name,
        candidates=candidates,
    )


def rebind_cached_review_sidecars(folder: Path, items: list[ReviewItem]) -> None:
    """Refresh mutable LLM evidence without re-extracting Lean signatures.

    The cache owns syntactic declarations, elaborated signatures, and source
    statements.  TeX translations and judgment sidecars are independently
    versioned evidence, so they must be reread whenever cached rows are used.
    This keeps cache reuse sound while avoiding a second expensive Lean Meta
    pass merely because an audit sidecar was regenerated.
    """

    drafts = load_llm_lean_to_tex_drafts(folder)
    manifests = {
        item.name: item.lean_signature_manifest
        for item in items
        if isinstance(item.lean_signature_manifest, dict)
    }
    judgments = load_llm_statement_judgments(folder, manifests)
    semantic_judgment_index = _semantic_statement_judgment_index(judgments)
    assumption_judgments = load_llm_assumption_judgments(folder)
    for item in items:
        draft = drafts.get(item.name)
        if draft:
            item.agent_statement = draft

        _semantic_key, semantic_judgment, semantic_ambiguous = (
            _current_semantic_statement_judgment_for_item(
                item,
                judgments,
                identity_index=semantic_judgment_index,
            )
        )
        judgment = (
            semantic_judgment
            if semantic_judgment is not None
            else {}
            if semantic_ambiguous
            else judgments.get(item.name) or {}
        )
        item.llm_match_judgment = str(judgment.get("judgment") or "")
        item.llm_match_reason = str(
            judgment.get("reason") or judgment.get("comment") or ""
        )
        item.llm_match_source = str(judgment.get("source") or "")
        item.llm_match_validator = str(judgment.get("validator") or "")
        item.llm_match_validator_type = str(judgment.get("validator_type") or "")
        item.llm_match_validated_at = str(judgment.get("validated_at") or "")
        item.llm_match_lean_statement_sha256 = str(
            judgment.get("lean_statement_sha256") or ""
        )
        item.llm_match_lean_signature_sha256 = str(
            judgment.get("lean_signature_sha256") or ""
        )
        item.llm_match_paper_statement_sha256 = str(
            judgment.get("paper_statement_sha256") or ""
        )
        item.llm_match_tex_statement_sha256 = str(
            judgment.get("tex_statement_sha256") or ""
        )
        item.llm_match_resolution = _normalize_llm_match_resolution(
            judgment.get("resolution")
        )
        item.llm_match_boundary_type = str(judgment.get("boundary_type") or "")
        item.llm_match_boundary_names = _normalize_string_list(
            judgment.get("boundary_names")
        )
        item.llm_match_conditional_premises = _normalize_string_list(
            judgment.get("conditional_premises")
        )
        item.llm_match_resolution_reason = str(
            judgment.get("resolution_reason") or ""
        )
        item.llm_match_source_routes = (
            judgment.get("source_routes")
            if isinstance(judgment.get("source_routes"), list)
            else []
        )
        item.llm_match_component_target_sha256 = (
            _validated_unique_source_component_target_sha256(judgment)
        )
        item.llm_match_stale = _llm_statement_judgment_is_stale(
            judgment,
            signature_sha256=item.lean_signature_sha256,
            lean_statement=item.lean_statement,
            paper_statement=item.paper_statement,
            agent_statement=item.agent_statement,
        )

        assumption_judgment = assumption_judgments.get(item.name) or {}
        item.llm_assumption_judgment = str(assumption_judgment.get("judgment") or "")
        item.llm_assumption_reason = str(
            assumption_judgment.get("reason") or assumption_judgment.get("comment") or ""
        )
        item.llm_assumption_source = str(assumption_judgment.get("source") or "")
        item.llm_assumption_validator = str(assumption_judgment.get("validator") or "")
        item.llm_assumption_validator_type = str(
            assumption_judgment.get("validator_type") or ""
        )
        item.llm_assumption_validated_at = str(
            assumption_judgment.get("validated_at") or ""
        )
        item.llm_assumption_lean_statement_sha256 = str(
            assumption_judgment.get("lean_statement_sha256") or ""
        )
        item.llm_assumption_paper_statement_sha256 = str(
            assumption_judgment.get("paper_statement_sha256") or ""
        )
        raw_premise_judgments = assumption_judgment.get("premise_judgments")
        item.llm_assumption_premise_judgments = (
            raw_premise_judgments if isinstance(raw_premise_judgments, dict) else {}
        )
        item.llm_assumption_stale = bool(assumption_judgment) and (
            not item.llm_assumption_lean_statement_sha256
            or not item.llm_assumption_paper_statement_sha256
            or item.llm_assumption_lean_statement_sha256
            not in lean_statement_digest_candidates(
                item.lean_statement, item.interface_source
            )
            or item.llm_assumption_paper_statement_sha256
            != statement_digest(item.paper_statement)
            or bool(assumption_judgment.get("prompt_version_stale"))
            or bool(assumption_judgment.get("metadata_missing"))
        )
    SIGNATURE_MANIFEST_CACHE[str(folder.resolve())] = manifests


def load_cached_review_rows(
    folder: Path,
    *,
    signature_contexts: dict[str, Any] | None = None,
    source_hashes: dict[str, str] | None = None,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
    persist_rebind: bool = True,
    cache_payload: Mapping[str, Any] | None = None,
) -> list[ReviewItem] | None:
    """Load cached rows when their exact payload still matches current inputs.

    A caller that already acquired and hashed the cache can supply
    ``cache_payload`` so this function does not reopen the mutable path and mix
    rows from a different instant into the caller's transaction.
    """

    cache_path = paper_interface_cache_file(folder)
    if cache_payload is None:
        if not cache_path.exists() or not cache_path.is_file():
            return None
        try:
            payload = json.loads(cache_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            return None
    else:
        payload = dict(cache_payload)

    if payload.get("schema") != PAPER_INTERFACE_CACHE_SCHEMA:
        return None
    if payload.get("paper") != folder.name:
        return None
    if (
        signature_contexts is not None
        and payload.get("signature_contexts") != signature_contexts
    ):
        return None

    hashes = (
        source_hashes
        if source_hashes is not None
        else _cache_source_hashes(
            folder,
            build_input_provider=build_input_provider,
        )
    )
    recorded_hashes = payload.get("hashes", {})
    if not isinstance(recorded_hashes, dict):
        return None
    if payload.get("hashes", {}).get("review_source_file") != hashes["review_source_file"]:
        return None
    if payload.get("hashes", {}).get("interface_sha256") != hashes["interface_sha256"]:
        return None
    if (
        payload.get("hashes", {}).get("lean_source_closure_sha256")
        != hashes["lean_source_closure_sha256"]
    ):
        return None
    report_changed = (
        str(recorded_hashes.get("report_sha256") or "")
        != hashes["report_sha256"]
    )
    if payload.get("hashes", {}).get("tex_sha256") != hashes["tex_sha256"]:
        return None
    if payload.get("hashes", {}).get("text_sha256") != hashes["text_sha256"]:
        return None
    if payload.get("hashes", {}).get("pdf_sha256") != hashes["pdf_sha256"]:
        return None
    # The source map supplies paper-facing display text and source-coverage
    # metadata, but it does not choose or elaborate the Lean review surface.
    # Re-extracting every signature manifest after a coverage-mode, anchor, or
    # source-text edit therefore wastes a current Lean receipt.  Rebind the
    # lightweight paper statements below instead; that recomputes judgment
    # staleness against the updated text and fails closed when declarations no
    # longer align.
    statement_map_changed = (
        payload.get("hashes", {}).get("paper_statement_map_sha256")
        != hashes["paper_statement_map_sha256"]
    )
    display_status_changed = (
        str(recorded_hashes.get("review_surface_display_sha256") or "")
        != hashes["review_surface_display_sha256"]
    )
    status_rebind_changed = (
        str(recorded_hashes.get("review_surface_rebind_sha256") or "")
        != hashes["review_surface_rebind_sha256"]
    )
    recorded_static_status = str(
        recorded_hashes.get("review_surface_static_sha256") or ""
    ).strip()
    static_status_changed = (
        recorded_static_status != hashes["review_surface_static_sha256"]
    )

    rows = payload.get("rows")
    if not isinstance(rows, list):
        return None

    out: list[ReviewItem] = []
    for raw_row in rows:
        if not isinstance(raw_row, dict):
            continue
        name = str(raw_row.get("name") or "").strip()
        kind = str(raw_row.get("kind") or "").strip()
        lean_statement = str(raw_row.get("lean_statement") or "").strip()
        paper_statement = str(raw_row.get("paper_statement") or "").strip()
        agent_statement = str(raw_row.get("agent_statement") or "").strip()
        full_name = str(raw_row.get("full_name") or "").strip()
        interface_source = str(raw_row.get("interface_source") or "").strip()
        raw_signature_manifest = raw_row.get("lean_signature_manifest")
        lean_signature_manifest = (
            raw_signature_manifest if isinstance(raw_signature_manifest, dict) else None
        )
        lean_signature_sha256 = str(
            raw_row.get("lean_signature_sha256") or ""
        ).strip()
        source_status = str(raw_row.get("source_status") or "").strip()
        source_note = str(raw_row.get("source_note") or "").strip()
        llm_match_judgment = str(raw_row.get("llm_match_judgment") or "").strip()
        llm_match_reason = str(raw_row.get("llm_match_reason") or "").strip()
        llm_match_stale = bool(raw_row.get("llm_match_stale") or False)
        llm_match_source = str(raw_row.get("llm_match_source") or "").strip()
        llm_match_validator = str(raw_row.get("llm_match_validator") or "").strip()
        llm_match_validator_type = str(raw_row.get("llm_match_validator_type") or "").strip()
        llm_match_validated_at = str(raw_row.get("llm_match_validated_at") or "").strip()
        llm_match_lean_statement_sha256 = str(
            raw_row.get("llm_match_lean_statement_sha256") or ""
        ).strip()
        llm_match_lean_signature_sha256 = str(
            raw_row.get("llm_match_lean_signature_sha256") or ""
        ).strip()
        llm_match_paper_statement_sha256 = str(
            raw_row.get("llm_match_paper_statement_sha256") or ""
        ).strip()
        llm_match_tex_statement_sha256 = str(
            raw_row.get("llm_match_tex_statement_sha256") or ""
        ).strip()
        llm_match_resolution = _normalize_llm_match_resolution(
            raw_row.get("llm_match_resolution")
        )
        llm_match_boundary_type = str(raw_row.get("llm_match_boundary_type") or "").strip()
        llm_match_boundary_names = _normalize_string_list(
            raw_row.get("llm_match_boundary_names")
        )
        llm_match_conditional_premises = _normalize_string_list(
            raw_row.get("llm_match_conditional_premises")
        )
        llm_match_resolution_reason = str(
            raw_row.get("llm_match_resolution_reason") or ""
        ).strip()
        raw_llm_match_source_routes = raw_row.get("llm_match_source_routes")
        llm_match_source_routes = (
            raw_llm_match_source_routes
            if isinstance(raw_llm_match_source_routes, list)
            else []
        )
        llm_match_component_target_sha256 = str(
            raw_row.get("llm_match_component_target_sha256") or ""
        ).strip()
        is_assumption = bool(raw_row.get("is_assumption") or False)
        is_proposition_spec = bool(raw_row.get("is_proposition_spec") or False)
        proposition_spec_role = str(raw_row.get("proposition_spec_role") or "").strip()
        proposition_spec_proof = str(raw_row.get("proposition_spec_proof") or "").strip()
        raw_semantic_contract_match = raw_row.get(
            "semantic_contract_lean_match_verified"
        )
        semantic_contract_lean_match_verified = (
            raw_semantic_contract_match
            if isinstance(raw_semantic_contract_match, bool)
            else None
        )
        raw_semantic_contract_transparency = raw_row.get(
            "semantic_contract_lean_transparency_verified"
        )
        semantic_contract_lean_transparency_verified = (
            raw_semantic_contract_transparency
            if isinstance(raw_semantic_contract_transparency, bool)
            else None
        )
        llm_assumption_judgment = str(raw_row.get("llm_assumption_judgment") or "").strip()
        llm_assumption_reason = str(raw_row.get("llm_assumption_reason") or "").strip()
        llm_assumption_stale = bool(raw_row.get("llm_assumption_stale") or False)
        llm_assumption_source = str(raw_row.get("llm_assumption_source") or "").strip()
        llm_assumption_validator = str(raw_row.get("llm_assumption_validator") or "").strip()
        llm_assumption_validator_type = str(raw_row.get("llm_assumption_validator_type") or "").strip()
        llm_assumption_validated_at = str(raw_row.get("llm_assumption_validated_at") or "").strip()
        llm_assumption_lean_statement_sha256 = str(
            raw_row.get("llm_assumption_lean_statement_sha256") or ""
        ).strip()
        llm_assumption_paper_statement_sha256 = str(
            raw_row.get("llm_assumption_paper_statement_sha256") or ""
        ).strip()
        raw_premise_judgments = raw_row.get("llm_assumption_premise_judgments")
        llm_assumption_premise_judgments = (
            raw_premise_judgments if isinstance(raw_premise_judgments, dict) else {}
        )
        paper_statement_image_url = str(raw_row.get("paper_statement_image_url") or "").strip()
        line_number = int(raw_row.get("line_number") or 0)
        slice_id = _safe_slice_id(str(raw_row.get("slice_id") or "all"))
        slice_title = str(raw_row.get("slice_title") or "All statements").strip()
        if not name or not kind or not lean_statement:
            continue
        out.append(
            ReviewItem(
                name=name,
                kind=kind,
                lean_statement=lean_statement,
                paper_statement=paper_statement,
                agent_statement=agent_statement,
                full_name=full_name,
                interface_source=interface_source,
                lean_signature_manifest=lean_signature_manifest,
                lean_signature_sha256=lean_signature_sha256,
                source_status=source_status,
                source_note=source_note,
                llm_match_judgment=llm_match_judgment,
                llm_match_reason=llm_match_reason,
                llm_match_stale=llm_match_stale,
                llm_match_source=llm_match_source,
                llm_match_validator=llm_match_validator,
                llm_match_validator_type=llm_match_validator_type,
                llm_match_validated_at=llm_match_validated_at,
                llm_match_lean_statement_sha256=llm_match_lean_statement_sha256,
                llm_match_lean_signature_sha256=llm_match_lean_signature_sha256,
                llm_match_paper_statement_sha256=llm_match_paper_statement_sha256,
                llm_match_tex_statement_sha256=llm_match_tex_statement_sha256,
                llm_match_resolution=llm_match_resolution,
                llm_match_boundary_type=llm_match_boundary_type,
                llm_match_boundary_names=llm_match_boundary_names,
                llm_match_conditional_premises=llm_match_conditional_premises,
                llm_match_resolution_reason=llm_match_resolution_reason,
                llm_match_source_routes=llm_match_source_routes,
                llm_match_component_target_sha256=(
                    llm_match_component_target_sha256
                ),
                is_assumption=is_assumption,
                is_proposition_spec=is_proposition_spec,
                proposition_spec_role=proposition_spec_role,
                proposition_spec_proof=proposition_spec_proof,
                semantic_contract_lean_match_verified=(
                    semantic_contract_lean_match_verified
                ),
                semantic_contract_lean_transparency_verified=(
                    semantic_contract_lean_transparency_verified
                ),
                llm_assumption_judgment=llm_assumption_judgment,
                llm_assumption_reason=llm_assumption_reason,
                llm_assumption_stale=llm_assumption_stale,
                llm_assumption_source=llm_assumption_source,
                llm_assumption_validator=llm_assumption_validator,
                llm_assumption_validator_type=llm_assumption_validator_type,
                llm_assumption_validated_at=llm_assumption_validated_at,
                llm_assumption_lean_statement_sha256=llm_assumption_lean_statement_sha256,
                llm_assumption_paper_statement_sha256=llm_assumption_paper_statement_sha256,
                llm_assumption_premise_judgments=llm_assumption_premise_judgments,
                paper_statement_image_url=paper_statement_image_url,
                line_number=line_number,
                slice_id=slice_id,
                slice_title=slice_title or slice_id,
            )
        )
    direct_route_statement_stale = bool(out) and not (
        cached_direct_source_route_statements_are_current(folder, out)
    )
    if static_status_changed and (
        not out or not cached_rows_match_current_extraction_surface(folder, out)
    ):
        return None
    statement_rebind_required = bool(out) and (
        report_changed
        or statement_map_changed
        or display_status_changed
        or direct_route_statement_stale
    )
    if statement_rebind_required:
        if not rebind_cached_report_statements(folder, out):
            return None
    if out and (
        report_changed
        or statement_map_changed
        or display_status_changed
        or status_rebind_changed
        or static_status_changed
    ):
        rebound = rebind_cached_review_status(folder, out)
        if rebound is None:
            return None
        out = rebound
    if out:
        rebind_cached_review_sidecars(folder, out)
        if persist_rebind and (
            report_changed
            or statement_map_changed
            or display_status_changed
            or status_rebind_changed
            or static_status_changed
            or direct_route_statement_stale
        ):
            payload["hashes"] = hashes
            payload["rows"] = [item.__dict__ for item in out]
            try:
                cache_path.write_text(
                    json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
                    encoding="utf-8",
                )
            except OSError:
                # The returned rows remain valid. Failure to persist only
                # causes a later cheap report-text rebind.
                pass
    return out or None


def write_cached_review_rows(
    folder: Path,
    items: list[ReviewItem],
    *,
    signature_contexts: dict[str, Any] | None = None,
    source_hashes: dict[str, str] | None = None,
) -> None:
    """Persist dashboard rows with source hashes for future reloads."""

    cache_path = paper_interface_cache_file(folder)
    cache_path.parent.mkdir(parents=True, exist_ok=True)
    payload = {
        "schema": PAPER_INTERFACE_CACHE_SCHEMA,
        "paper": folder.name,
        "generated_at": datetime.now(timezone.utc).isoformat(timespec="seconds").replace(
            "+00:00", "Z"
        ),
        "hashes": source_hashes if source_hashes is not None else _cache_source_hashes(folder),
        "rows": [item.__dict__ for item in items],
    }
    if signature_contexts is not None:
        payload["signature_contexts"] = signature_contexts
    cache_path.write_text(json.dumps(payload, indent=2), encoding="utf-8")


def cached_review_row_hashes_match(
    folder: Path, source_hashes: dict[str, str]
) -> bool:
    """Whether the persisted row cache already carries the verified snapshot."""

    cache_path = paper_interface_cache_file(folder)
    try:
        payload = json.loads(cache_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    return payload.get("hashes") == source_hashes


def review_items_for_paper(
    folder: Path,
    use_cache: bool = True,
    *,
    render_images: bool = True,
    require_current_signatures: bool = False,
    persist_cache_rebind: bool = True,
    build_input_provider: RepositoryBuildInputSnapshotProvider | None = None,
    audit_inputs: DashboardAuditInputs | None = None,
    validated_configured_review_rows: Iterable[Mapping[str, Any]] | None = None,
    progress: Callable[[str], None] | None = None,
    publish_manifest_store: bool = False,
) -> list[ReviewItem]:
    """Read cached items if possible, else compute from source files.

    Strict repository audits set `require_current_signatures` so cached rows
    are accepted only after the relevant review modules have rebuilt and their
    Lean-manifest context matches the stored cache metadata.
    """

    if audit_inputs is not None:
        with dashboard_audit_input_scope(audit_inputs):
            return review_items_for_paper(
                folder,
                use_cache=use_cache,
                render_images=render_images,
                require_current_signatures=require_current_signatures,
                persist_cache_rebind=persist_cache_rebind,
                build_input_provider=build_input_provider,
                validated_configured_review_rows=(
                    validated_configured_review_rows
                ),
                progress=progress,
                publish_manifest_store=publish_manifest_store,
            )

    owns_build_input_provider = build_input_provider is None
    if build_input_provider is None:
        build_input_provider = RepositoryBuildInputSnapshotProvider(ROOT)
    build_inputs_finalized = False
    frozen_inputs_active = _dashboard_audit_inputs() is not None

    def emit_progress(message: str) -> None:
        if progress is None:
            return
        try:
            progress(message)
        except Exception:  # noqa: BLE001 - reporting cannot alter audit evidence.
            pass

    def require_unchanged_build_inputs() -> None:
        nonlocal build_inputs_finalized
        if (
            owns_build_input_provider
            and not build_inputs_finalized
            and not build_input_provider.finalize_unchanged()
        ):
            raise RuntimeError(
                f"repository build inputs changed while reviewing {folder.name}; "
                "discarding the result"
            )
        build_inputs_finalized = True

    def finalized(items: list[ReviewItem]) -> list[ReviewItem]:
        require_unchanged_build_inputs()
        return items

    source_hashes_before = (
        _cache_source_hashes(
            folder,
            build_input_provider=build_input_provider,
        )
        if (use_cache or require_current_signatures) and not frozen_inputs_active
        else None
    )
    if require_current_signatures:
        emit_progress("current Lean manifest contexts started")
        signature_contexts = current_review_signature_contexts(
            folder,
            build_input_provider=build_input_provider,
        )
    else:
        signature_contexts = None
    if require_current_signatures and signature_contexts is None:
        raise RuntimeError(f"could not build current Lean signature context for {folder.name}")
    if require_current_signatures and signature_contexts is not None:
        emit_progress(
            f"current Lean manifest contexts ready ({len(signature_contexts)} modules)"
        )
        try:
            prime_diagnostics = prime_review_signature_manifest_store(
                folder,
                signature_contexts,
                allow_migration_write=persist_cache_rebind,
                validated_configured_review_rows=(
                    validated_configured_review_rows
                ),
            )
            # An interactive refresh has no transaction-owned raw rows, so the
            # primary prime intentionally declines to read mutable cache state.
            # It can nevertheless compactly revalidate exact unchanged items
            # against receipt-validated prior raw evidence and a tracked
            # authority/carrier pair.  This stays strictly outside frozen
            # closeout runs, whose inputs must be wholly transaction-owned.
            if (
                validated_configured_review_rows is None
                and persist_cache_rebind
                and not frozen_inputs_active
            ):
                prime_diagnostics = prime_review_signature_manifest_store_from_prior(
                    folder, signature_contexts
                )
            emit_progress(
                "authenticated manifest reuse finished "
                f"({int(prime_diagnostics.get('seeded_count') or 0)} seeded; "
                f"{int(prime_diagnostics.get('fresh_required_count') or 0)} "
                "require fresh Lean; "
                f"{str(prime_diagnostics.get('store_status') or 'unknown')})"
            )
        except Exception as exc:  # noqa: BLE001 - optimization failure stays a miss.
            emit_progress(
                "authenticated manifest reuse unavailable " + type(exc).__name__
            )

    # The ordinary persisted row cache remains an interactive artifact. A
    # strict closeout can reuse only complete manifests independently rebound
    # to its current raw rows and exact compiled contexts above; every cache
    # miss still receives current Lean extraction. Semantic judgments are then
    # checked item by item against that signature-current manifest surface.
    if use_cache and not require_current_signatures and not frozen_inputs_active:
        cached = load_cached_review_rows(
            folder,
            signature_contexts=signature_contexts,
            source_hashes=source_hashes_before,
            build_input_provider=build_input_provider,
            persist_rebind=(persist_cache_rebind and not require_current_signatures),
        )
        if cached is not None:
            if (
                require_current_signatures
                and _cache_source_hashes(
                    folder,
                    build_input_provider=build_input_provider,
                )
                != source_hashes_before
            ):
                raise RuntimeError(
                    f"paper audit sources changed while loading {folder.name}; "
                    "discarding the cache"
                )
            if (
                require_current_signatures
                and source_hashes_before is not None
                and not cached_review_row_hashes_match(
                    folder, source_hashes_before
                )
            ):
                write_cached_review_rows(
                    folder,
                    cached,
                    signature_contexts=signature_contexts,
                    source_hashes=source_hashes_before,
                )
            require_unchanged_build_inputs()
            if render_images:
                attach_rendered_statement_images(folder, cached)
            return cached

    interface = review_source_file(folder)
    report = paper_relative_file(folder, FINAL_VALIDATION_REPORT_FILE, "FINAL_VALIDATION_REPORT.md")
    items = parse_interface_items(
        interface,
        report if _dashboard_is_file(report) else None,
        folder,
        render_lean_previews=not (
            require_current_signatures and not render_images
        ),
        build_input_provider=build_input_provider,
        progress=progress,
    )
    if require_current_signatures:
        stable_contexts = current_review_signature_contexts(
            folder,
            build_input_provider=build_input_provider,
        )
        if stable_contexts is None:
            raise RuntimeError(
                f"could not rebuild Lean signature context after extracting {folder.name}"
            )
        if stable_contexts != signature_contexts:
            raise RuntimeError(
                f"Lean signature context changed while extracting {folder.name}; "
                "discarding the cache"
            )
        source_hashes_after: dict[str, str] | None = None
        if not frozen_inputs_active:
            source_hashes_after = _cache_source_hashes(
                folder,
                build_input_provider=build_input_provider,
            )
            if source_hashes_after != source_hashes_before:
                raise RuntimeError(
                    f"paper audit sources changed while extracting {folder.name}; "
                    "discarding the cache"
                )
        require_unchanged_build_inputs()
        if persist_cache_rebind and source_hashes_after is not None:
            write_cached_review_rows(
                folder,
                items,
                signature_contexts=stable_contexts,
                source_hashes=source_hashes_after,
            )
            emit_progress(f"dashboard row cache written ({len(items)} rows)")
            if publish_manifest_store:
                try:
                    published = publish_review_signature_manifest_store(
                        folder, items, stable_contexts
                    )
                    emit_progress(
                        "authenticated manifest store published "
                        f"({len(published)} entries)"
                    )
                except Exception as exc:  # noqa: BLE001 - persistence is an optimization.
                    emit_progress(
                        "authenticated manifest store publication unavailable "
                        + type(exc).__name__
                    )
    else:
        require_unchanged_build_inputs()
    if render_images:
        attach_rendered_statement_images(folder, items)
    return finalized(items)


def refresh_cached_review_rows(folder: Path) -> None:
    """Force cache regeneration for one paper folder."""

    def progress(message: str) -> None:
        print(
            f"review-dashboard: {folder.name}: {message}",
            file=sys.stderr,
            flush=True,
        )

    review_items_for_paper(
        folder,
        use_cache=False,
        render_images=False,
        require_current_signatures=True,
        progress=progress,
        publish_manifest_store=True,
    )


def review_surface_digest(items: list[ReviewItem]) -> str:
    """Return a stable digest of the human-facing dashboard row surface."""

    payload = [
        {
            "name": item.name,
            "kind": item.kind,
            "lean_statement": normalize_statement(item.interface_source or item.lean_statement),
            "paper_statement": normalize_statement(item.paper_statement),
            "source_status": normalize_statement(item.source_status),
            "source_note": normalize_statement(item.source_note),
            "is_assumption": bool(item.is_assumption),
            "is_proposition_spec": bool(item.is_proposition_spec),
            "proposition_spec_role": item.proposition_spec_role,
            "proposition_spec_proof": item.proposition_spec_proof,
        }
        for item in sorted(items, key=lambda row: row.name)
    ]
    return hashlib.sha256(
        json.dumps(payload, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode(
            "utf-8"
        )
    ).hexdigest()


def review_surface_audit_summary(folder: Path, items: list[ReviewItem]) -> dict[str, Any]:
    """Summarize row-count thresholds and optional LLM review-surface audit status."""

    row_count = len(items)
    surface_hash = review_surface_digest(items)
    audit = load_llm_review_surface_audit(folder)
    recorded_rows = audit.get("review_rows")
    recorded_hash = str(audit.get("review_surface_sha256") or "").strip()
    judgment = str(audit.get("judgment") or "").strip()
    has_completed_audit = bool(
        judgment or audit.get("reason") or recorded_hash or (isinstance(recorded_rows, int) and recorded_rows > 0)
    )
    stale = False
    if audit and has_completed_audit:
        if isinstance(recorded_rows, int) and recorded_rows != row_count:
            stale = True
        if recorded_hash and recorded_hash != surface_hash:
            stale = True
        if audit.get("prompt_version_stale"):
            stale = True
        if audit.get("metadata_missing"):
            stale = True
    audit_required = row_count > REVIEW_SURFACE_LLM_AUDIT_THRESHOLD
    missing_required = audit_required and not has_completed_audit
    needs_curation = judgment == "needs_curation"
    uncertain = judgment == "uncertain"
    unknown = bool(has_completed_audit and judgment not in {"passes", "needs_curation", "uncertain"})
    non_evidence_scaffold = bool(audit.get("non_evidence_scaffold"))
    oversize = row_count >= REVIEW_SURFACE_WARN_THRESHOLD
    needs_attention = (
        missing_required
        or stale
        or needs_curation
        or uncertain
        or unknown
        or non_evidence_scaffold
    )
    return {
        "row_count": row_count,
        "llm_threshold": REVIEW_SURFACE_LLM_AUDIT_THRESHOLD,
        "warn_threshold": REVIEW_SURFACE_WARN_THRESHOLD,
        "audit_required": audit_required,
        "oversize": oversize,
        "missing_required": missing_required,
        "stale": stale,
        "judgment": judgment,
        "unknown_judgment": unknown,
        "reason": str(audit.get("reason") or "").strip(),
        "source": str(audit.get("source") or "").strip() if has_completed_audit else "",
        "has_completed_audit": has_completed_audit,
        "review_surface_sha256": surface_hash,
        "recorded_review_surface_sha256": recorded_hash,
        "recorded_review_rows": recorded_rows if isinstance(recorded_rows, int) else None,
        "prompt_version": str(audit.get("prompt_version") or "").strip(),
        "prompt_version_stale": bool(audit.get("prompt_version_stale")),
        "metadata_missing": bool(audit.get("metadata_missing")),
        "non_evidence_scaffold": non_evidence_scaffold,
        "needs_attention": needs_attention,
        "has_warning": needs_attention or oversize,
    }


def statement_translation_audit_summary(folder: Path, items: list[ReviewItem]) -> dict[str, Any]:
    """Summarize context-free Lean-to-TeX and semantic statement-match coverage."""

    statement_items = [
        item
        for item in items
        if not item.is_assumption and not is_assumption_item_name(item.name)
    ]
    draft_entries = load_llm_lean_to_tex_draft_entries(folder)
    judgments = load_llm_statement_judgments(
        folder,
        {
            item.name: item.lean_signature_manifest
            for item in items
            if isinstance(item.lean_signature_manifest, dict)
        },
    )
    missing_draft: list[str] = []
    stale_draft: list[str] = []
    missing_judgment: list[str] = []
    stale_judgment: list[str] = []
    missing_obligation_ledger: list[str] = []
    mismatch: list[str] = []
    conditional_boundary: list[str] = []
    unresolved_mismatch: list[str] = []
    uncertain: list[str] = []
    unknown: list[str] = []
    ambiguous_semantic_judgment: list[str] = []
    semantic_rebound_judgment: list[str] = []
    semantic_reused_stale_draft: list[str] = []
    semantic_current_judgment_count = 0
    matches = 0
    semantic_judgment_index = _semantic_statement_judgment_index(judgments)

    for item in statement_items:
        semantic_key, semantic_judgment, semantic_ambiguous = (
            _current_semantic_statement_judgment_for_item(
                item,
                judgments,
                identity_index=semantic_judgment_index,
            )
        )
        if semantic_ambiguous:
            ambiguous_semantic_judgment.append(item.name)
        if semantic_judgment is not None:
            semantic_current_judgment_count += 1
            if semantic_key != item.name:
                semantic_rebound_judgment.append(item.name)

        # A stale context-free rendering is non-crediting formatting evidence.
        # It need not force a repeat semantic review when one uniquely pinned,
        # current semantic judgment already covers this exact current row. A
        # missing rendering remains a blocker: this narrow reuse is not a
        # substitute for materializing a review input from nothing.
        draft = draft_entries.get(item.name)
        if not draft:
            missing_draft.append(item.name)
        else:
            recorded_lean = str(draft.get("lean_statement_sha256") or "").strip()
            stale = (
                (
                    recorded_lean
                    and recorded_lean
                    not in lean_statement_digest_candidates(item.lean_statement, item.interface_source)
                )
                or not recorded_lean
                or bool(draft.get("prompt_version_stale"))
                or bool(draft.get("metadata_missing"))
            )
            if stale:
                if str((semantic_judgment or {}).get("judgment") or "").strip() == "matches":
                    semantic_reused_stale_draft.append(item.name)
                else:
                    stale_draft.append(item.name)

        # Prefer the current exact semantic identity over the sidecar key. A
        # stale or nonmatching named entry remains visible below; an ambiguous
        # exact identity is treated as no evidence rather than guessed from a
        # familiar declaration name.
        judgment = semantic_judgment
        if judgment is None and not semantic_ambiguous:
            judgment = judgments.get(item.name)
        if not judgment:
            missing_judgment.append(item.name)
            continue

        value = str(judgment.get("judgment") or "").strip()
        if value == "matches":
            matches += 1
        elif value == "mismatch":
            mismatch.append(item.name)
            if _is_conditional_boundary_judgment(judgment):
                conditional_boundary.append(item.name)
            else:
                unresolved_mismatch.append(item.name)
        elif value == "uncertain":
            uncertain.append(item.name)
        else:
            unknown.append(item.name)
        if _llm_statement_judgment_is_stale(
            judgment,
            signature_sha256=item.lean_signature_sha256,
            lean_statement=item.lean_statement,
            paper_statement=item.paper_statement,
            agent_statement=item.agent_statement,
        ):
            stale_judgment.append(item.name)
        if judgment.get("obligation_ledger_error"):
            missing_obligation_ledger.append(item.name)

    all_uncertain = bool(statement_items) and len(uncertain) == len(statement_items)
    needs_attention = bool(
        missing_draft
        or stale_draft
        or missing_judgment
        or stale_judgment
        or missing_obligation_ledger
        or unresolved_mismatch
        or uncertain
        or unknown
        or ambiguous_semantic_judgment
    )
    return {
        "row_count": len(statement_items),
        "draft_count": len(draft_entries),
        "judgment_count": len(judgments),
        "matches": matches,
        "mismatch_count": len(mismatch),
        "conditional_boundary_count": len(conditional_boundary),
        "unresolved_mismatch_count": len(unresolved_mismatch),
        "uncertain_count": len(uncertain),
        "unknown_count": len(unknown),
        "missing_draft_count": len(missing_draft),
        "stale_draft_count": len(stale_draft),
        "missing_judgment_count": len(missing_judgment),
        "stale_judgment_count": len(stale_judgment),
        "missing_obligation_ledger_count": len(missing_obligation_ledger),
        "mismatch": mismatch,
        "conditional_boundary": conditional_boundary,
        "unresolved_mismatch": unresolved_mismatch,
        "uncertain": uncertain,
        "unknown": unknown,
        "ambiguous_semantic_judgment_count": len(ambiguous_semantic_judgment),
        "ambiguous_semantic_judgment": ambiguous_semantic_judgment,
        "semantic_current_judgment_count": semantic_current_judgment_count,
        "semantic_rebound_judgment_count": len(semantic_rebound_judgment),
        "semantic_rebound_judgment": semantic_rebound_judgment,
        "semantic_reused_stale_draft_count": len(semantic_reused_stale_draft),
        "semantic_reused_stale_draft": semantic_reused_stale_draft,
        "missing_draft": missing_draft,
        "stale_draft": stale_draft,
        "missing_judgment": missing_judgment,
        "stale_judgment": stale_judgment,
        "missing_obligation_ledger": missing_obligation_ledger,
        "has_completed_audit": bool(draft_entries and judgments),
        "all_uncertain": all_uncertain,
        "needs_attention": needs_attention,
    }


def paper_coverage_audit_required(folder: Path, inventory: dict[str, dict[str, Any]]) -> bool:
    """Return whether the paper-level source coverage audit should be enforced."""

    payload = load_review_slice_payload(folder)
    explicit = payload.get("paper_coverage_required")
    explicit_configured = False
    if isinstance(explicit, str):
        normalized_explicit = explicit.strip().lower()
        explicit_configured = normalized_explicit in {
            "0",
            "1",
            "false",
            "true",
            "no",
            "yes",
            "not required",
            "optional",
            "required",
            "off",
            "on",
        }
        explicit_enabled = normalized_explicit in {"1", "true", "yes", "required", "on"}
    elif isinstance(explicit, bool):
        explicit_configured = True
        explicit_enabled = explicit
    else:
        explicit_enabled = False

    status_path = folder / DEFAULT_PAPER_STATUS_FILE
    status_value = ""
    if _dashboard_is_file(status_path):
        status_payload = _dashboard_json_payload(status_path) or {}
        if isinstance(status_payload, dict):
            status_value = str(status_payload.get("status") or "").strip().lower()
    public_facing_status = (
        status_value.startswith("formalized")
        or status_value.startswith("partially formalized")
        or status_value.startswith("conditional")
    )
    if status_value == "paper draft":
        return explicit_enabled if explicit_configured else False
    if public_facing_status:
        return True
    if explicit_configured:
        return explicit_enabled
    return bool(
        inventory
        and _dashboard_is_file(folder / PAPER_STATEMENT_MAP_FILE)
    )


def _is_statement_map_source(source: object) -> bool:
    """Return whether an inventory source label names the statement-map sidecar."""

    return str(source or "") == PAPER_STATEMENT_MAP_FILE


SOURCE_NAMED_CLAIM_RE = re.compile(
    r"""
    (?ix)
    (?:
        # Literal theorem environments and TeX cross references, including a
        # source extracted directly from TeX rather than rendered prose.
        \\begin\s*\{\s*(?:theorem|lemma|proposition|corollary|claim|thm|lem|prop|cor)\*?\s*\}
      | \\(?:auto|[cC]|eq)?ref\s*\{\s*(?:(?:thm|theorem|lem|lemma|prop|proposition|cor|corollary|claim)[^}]*)\}
        # Rendered and TeX-ish named references: ``Theorem 2``,
        # ``Lemma~\\ref{lem:main}``, and ``(Proposition A.1)``.
      | \b(?:theorem|lemma|proposition|corollary|claim)\b\s*
        (?:~|\\[,;! ]*|:)?\s*
        (?:
            \\(?:auto|[cC]|eq)?ref\s*\{[^}]+\}
          | \\label\s*\{[^}]+\}
          | \(?\s*(?:(?-i:[A-Z])(?:\.\d+)+(?:[a-z])?|(?-i:[A-Z])?\d+(?:\.\d+)*(?:[a-z])?|(?-i:[A-Z]))\s*\)?
        )
    )
    """,
    re.IGNORECASE | re.VERBOSE | re.MULTILINE,
)
SOURCE_NAMED_RESULT_PRESENTATION_RE = re.compile(
    r"""
    (?imx)
    (?:
        \\begin\s*\{\s*(?:theorem|lemma|proposition|corollary|claim|thm|lem|prop|cor)\*?\s*\}
      | ^\s*(?:\\(?:textbf|emph|textit|paragraph)\s*\{?\s*)?
        \b(?:theorem|lemma|proposition|corollary|claim)\b\s*
        (?:~|\\[,;! ]*|:)?\s*
        (?:
            \\(?:auto|[cC]|eq)?ref\s*\{[^}]+\}
          | \\label\s*\{[^}]+\}
          | \(?\s*(?:(?-i:[A-Z])(?:\.\d+)+(?:[a-z])?|(?-i:[A-Z])?\d+(?:\.\d+)*(?:[a-z])?|(?-i:[A-Z]))\s*\)?
        )
      | \b(?:theorem|lemma|proposition|corollary|claim)\b\s*
        (?:~|\\[,;! ]*|:)?\s*
        (?:
            \\(?:auto|[cC]|eq)?ref\s*\{[^}]+\}
          | \(?\s*(?:(?-i:[A-Z])(?:\.\d+)+(?:[a-z])?|(?-i:[A-Z])?\d+(?:\.\d+)*(?:[a-z])?|(?-i:[A-Z]))\s*\)?
        )
        (?:(?![.!?;\n]).){0,80}?\b(?:states?|proves?|establishes?|shows?|asserts?|claims?|guarantees?)\b
    )
    """,
    re.IGNORECASE | re.VERBOSE | re.MULTILINE,
)
# The broad presentation matcher above also recognizes an in-text theorem
# reference.  Scope exclusions need the narrower question: does the *anchored
# item itself* begin as a labelled formal result?  This pattern intentionally
# requires a source heading/environment (or an anchored heading-style verb),
# so a remark that says "as in Theorem 3" is not misclassified as Theorem 3.
SOURCE_NAMED_RESULT_HEADING_RE = re.compile(
    r"""
    (?imx)
    (?:
        \\begin\s*\{\s*(?:theorem|lemma|proposition|corollary|claim|thm|lem|prop|cor)\*?\s*\}
      | ^\s*(?:\\(?:textbf|emph|textit|paragraph)\s*\{?\s*)?
        \b(?:theorem|lemma|proposition|corollary|claim)\b\s*
        (?:~|\\[,;! ]*|:)?\s*
        (?:
            \\(?:auto|[cC]|eq)?ref\s*\{[^}]+\}
          | \\label\s*\{[^}]+\}
          | \(?\s*(?:(?-i:[A-Z])(?:\.\d+)+(?:[a-z])?|(?-i:[A-Z])?\d+(?:\.\d+)*(?:[a-z])?|(?-i:[A-Z]))\s*\)?
        )
        (?=\s*(?:[.:()]|$|\b(?:states?|proves?|shows?|asserts?|claims?|guarantees?)\b))
    )
    """,
    re.IGNORECASE | re.VERBOSE | re.MULTILINE,
)
SOURCE_NAMED_ALGORITHM_BLOCK_RE = re.compile(
    r"""
    (?ix)
    (?:
        \\begin\s*\{\s*(?:algorithm|algorithmic|procedure|method)\*?\s*\}
      | \\caption\s*\{[^}]*\b(?:algorithm|procedure|method)\b
      | \b(?:algorithm|procedure|method)\b\s*
        (?:~|\\[,;! ]*|:)?\s*
        (?:
            \\(?:auto|[cC]|eq)?ref\s*\{[^}]+\}
          | \d+(?:\.\d+)*(?:[a-z])?
          | (?-i:[A-Z])[A-Za-z0-9_.-]*
          | :
        )
    )
    """,
    re.IGNORECASE | re.VERBOSE | re.MULTILINE,
)
# Keep performance detection contextual.  In particular, the words
# ``exponential``, ``quadratic``, ``linear``, and ``polynomial`` alone are
# ordinary mathematical vocabulary (distributions, utilities, regressions,
# etc.), not a complexity assertion.  A finite observed benchmark likewise is
# not promoted merely because it contains a number.  The patterns below look
# for resource terminology, asymptotic notation, or a general algorithmic
# behavior instead.
SOURCE_COMPLEXITY_TERMINOLOGY_RE = re.compile(
    r"\b(?:"
    r"run(?:ning)?\s+time|runtime|time\s+complexity|space\s+complexity|"
    r"strongly\s+polynomial|polytime|polynomial[-\s]?(?:query|queries)|"
    r"fixed[-\s]?parameter[-\s]?tractable|fpt|"
    r"(?:polynomial|linear|quadratic|exponential)\s*(?:[-\s]+)"
    r"(?:time|runtime|space|work|steps?|operations?|queries|iterations?)|"
    r"(?:number|count)\s+of\s+(?:arithmetic\s+)?"
    r"(?:steps?|operations?|queries|iterations?)"
    r")\b",
    re.IGNORECASE,
)
SOURCE_BIG_O_COMPLEXITY_RE = re.compile(
    r"""
    (?ix)
    (?:
        (?<![A-Za-z])(?:O|o|Ω|Θ)\s*(?:\\!\s*)?(?:\\left\s*)?\(
      | \\(?:mathcal|mathrm|operatorname)\s*\{\s*(?:O|o|Omega|Theta|Ω|Θ)\s*\}
        \s*(?:\\!\s*)?(?:\\left\s*)?\(
      | \\(?:mathcal|mathrm)\s+(?:O|o|Omega|Theta|Ω|Θ)
        \s*(?:\\!\s*)?(?:\\left\s*)?\(
    )
    """,
    re.IGNORECASE | re.VERBOSE,
)
SOURCE_ALGORITHM_BEHAVIOR_RE = re.compile(
    r"""
    (?ix)
    \b(?:algorithm|procedure|method)\b
    (?:(?![.!?;\n]).){0,120}?
    \b(?:
        runs?|executes?|takes?|terminates?|halts?|outputs?|produces?|returns?|
        computes?|finds?|achieves?|guarantees?
    )\b
    | \b(?:algorithm|procedure|method)\b(?:(?![.!?;\n]).){0,120}?
      \bis\s+(?:correct|optimal)\b
    """,
    re.IGNORECASE | re.VERBOSE,
)
SOURCE_GENERAL_OUTPUT_GUARANTEE_RE = re.compile(
    r"""
    (?ix)
    \b(?:outputs?|produces?|returns?|computes?|finds?|terminates?|halts?)\b
    (?:(?![.!?;\n]).){0,120}?
    \b(?:for|on)\s+(?:every|all|each|any)\s+(?:input|instance|case|problem)\b
    """,
    re.IGNORECASE | re.VERBOSE,
)
SOURCE_RESOURCE_BOUND_RE = re.compile(
    r"""
    (?ix)
    \b(?:takes?|requires?|uses?|needs?)\b
    (?:(?![.!?;\n]).){0,100}?
    \b(?:time|steps?|operations?|queries|iterations?)\b
    """,
    re.IGNORECASE | re.VERBOSE,
)
SOURCE_CONTEXTUAL_EFFICIENCY_RE = re.compile(
    r"""
    (?ix)
    (?:
        \b(?:computationally|algorithmically)\s+(?:efficient|tractable|scalable|fast)\b
      | \b(?:efficient|tractable|scalable|fast)\s+(?:algorithm|procedure|method|implementation)\b
      | \b(?:algorithm|procedure|method)\b(?:(?![.!?;\n]).){0,80}?
        \b(?:efficient|tractable|scalable|fast)\b
      | \b(?:computed|solved|implemented|tested|evaluated|verified)\s+efficiently\b
    )
    """,
    re.IGNORECASE | re.VERBOSE,
)
# The computational-illustration exception is intentionally a narrow positive
# classification.  A Figure/Table/plot label only tells us where source prose
# appears; it does not establish that the prose is a finite numerical,
# simulation, or empirical observation.  These are source-language cues only:
# source-map keys and Lean declarations are deliberately not inputs.
SOURCE_FINITE_OBSERVATION_CONCRETE_CUE_RE = re.compile(
    r"""
    (?ix)
    \b(?:
        simulation|simulated|benchmark|experiment(?:al)?|numerical|
        comput(?:ation|ational|ed|ing)|calibration|empirical|data\s*set|
        sample|observation|measurement|estimate
    )\b
    | \b(?:n|k|m)\s*=\s*\d+\b
    | \b\d+\s*[- ]?(?:candidate|firm|voter|agent|instance|setting|parameter)s?\b
    """,
    re.IGNORECASE | re.VERBOSE,
)
SOURCE_FINITE_OBSERVATION_REPORT_RE = re.compile(
    r"""
    (?ix)
    \b(?:
        reports?|depicts?|plots?|illustrates?|shows?|observes?|finds?|records?|
        displays?|outputs?|estimates?|computes?|calculates?|verif(?:y|ies|ied)
    )\b
    """,
    re.IGNORECASE | re.VERBOSE,
)
# A source may phrase a paper result in ordinary prose instead of attaching a
# theorem number.  Such a claim is still in scope.  The positive finite-
# observation requirement below catches unrecognised mathematical assertions;
# this pattern gives the common correctness/existence/optimality family a
# direct, audit-visible rejection reason.
SOURCE_GENERAL_RESULT_ASSERTION_RE = re.compile(
    r"""
    (?ix)
    (?:
        \b(?:if|when|whenever|provided\s+that|assuming)\b
        (?:(?![.!?;\n]).){0,160}?
        \b(?:then|holds?|implies?|is|are|remains?|becomes?)\b
      | \b(?:for|on)\s+(?:all|every|each|any)\s+
        (?:admissible\s+)?
        (?:input|instance|case|problem|profile|parameter(?:\s+value)?|model|distribution)\b
      | \b(?:always|never|universally|in\s+general|for\s+arbitrary)\b
      | \b(?:there\s+(?:is|are|exists?)|exists?|existence)\b
      | \b(?:correct(?:ness)?|strategy[-\s]?proof(?:ness)?|truthful(?:ness)?|sound(?:ness)?|complete(?:ness)?|incentive[-\s]?compatib(?:le|ility)|condorcet[-\s]?consisten(?:t|cy)|monotonicity|anonymity|proportionality)\b
      | \b(?:optimality|pareto[-\s]?optimal|globally\s+optimal|maximi[sz](?:e|es|ing)|minimi[sz](?:e|es|ing))\b
      | \b(?:approximation|competitive)\s+ratio\b|\bbounded\s+regret\b
      | \b(?:guarantees?|ensures?|certifies?|elects?)\b
        (?:(?![.!?;\n]).){0,100}?
        \b(?:winner|outcome|allocation|matching)\b
      | \b(?:rule|mechanism|method|approach|procedure|algorithm|solution)\b
        (?:(?![.!?;\n]).){0,80}?
        \b(?:satisfies|meets|obeys)\b
      | \b(?:algorithm|procedure|method|mechanism|approach|implementation|solution)\b
        (?:(?![.!?;\n]).){0,80}?
        \b(?:is|are|remains?|becomes?|achieves?|attains?|guarantees?|provides?|yields?|has|have)\b
        (?:(?![.!?;\n]).){0,80}?
        \b(?:correct|optimal|efficient|accurate|tractable|scalable|fast|performance|approximation|competitive)\b
      | \b(?:is|are|remains?|becomes?)\b
        (?:(?![.!?;\n]).){0,40}?
        \b(?:correct|optimal|efficient|accurate|tractable|scalable|fast|strategyproof)\b
    )
    """,
    re.IGNORECASE | re.VERBOSE,
)
SOURCE_ARTIFACT_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.IGNORECASE)
SOURCE_FILE_LINE_ANCHOR_RE = re.compile(
    r"(?P<path>(?:[A-Za-z0-9_.-]+/)*[A-Za-z0-9_.-]+\.(?:tex|txt|md|pdf)):"
    r"(?P<start>[1-9]\d*)(?:-(?P<end>[1-9]\d*))?",
    re.IGNORECASE,
)
SOURCE_RESULT_KINDS = {
    "theorem",
    "proposition",
    "lemma",
    "corollary",
    "claim",
    "runtime_claim",
}
SOURCE_VOCABULARY_KINDS = {"definition", "predicate_vocabulary"}
# Source definitions need a distinct semantic review from theorem proof
# evidence.  A definition can compile while quietly extending a partial source
# operation, replacing a probability law by an unnormalised formula, or naming
# a selector without the advertised attainment property.  This classification
# comes from the source inventory, never from a Lean declaration or map key.
SOURCE_DEFINITION_SEMANTIC_KINDS = {"definition", "predicate_vocabulary"}
# This deliberately extends only the direct-route semantic-review gate below.
# Formula/equation kinds remain outside definition partition and coverage rules:
# they need a domain/totalization review, but are not thereby source definitions.
SOURCE_DIRECT_EXPRESSION_SEMANTIC_KINDS = (
    SOURCE_DEFINITION_SEMANTIC_KINDS
    | {"formula", "equation", "algorithmic_formula"}
)
SOURCE_DEFINITION_SEMANTIC_RELATIONS = {
    "equivalent",
    "source_stronger",
    "lean_stronger",
    "incomparable",
    "uncertain",
}
SOURCE_DEFINITION_PROPERTY_STATUSES = {
    "properties_reviewed",
    "no_advertised_properties",
}
SOURCE_DEFINITION_PROPERTY_EVIDENCE_KINDS = {
    "expanded_definition_body",
    "paper_interface_equivalence",
    "paper_interface_conclusion",
    "missing",
}
SOURCE_CATALOGUED_NONFORMAL_OBSERVATION_KINDS = {"example", "remark"}
# An explicit user scope decision covers only an independent, unnumbered prose
# assertion.  These source kinds are the only inventory presentations that can
# carry that disposition.  This is source metadata, not a Lean declaration or
# map-key convention: every candidate is also checked against its pinned source
# presentation below.
USER_APPROVED_UNNUMBERED_PROSE_SOURCE_KINDS = {
    "example",
    "remark",
    "prose_assertion",
}
USER_APPROVED_SCOPE_EXCLUSION_FORMAL_KINDS = (
    SOURCE_RESULT_KINDS | SOURCE_VOCABULARY_KINDS
)
NON_NAMED_COMPUTATIONAL_ILLUSTRATION = "non_named_computational_illustration"
# This source-only lane is intentionally narrow.  The exact pinned source
# excerpt must itself declare the matter open, so source-map keys and Lean
# helper names cannot turn an ordinary unproved result into a non-claim.
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
SOURCE_SCOPE_CLASSIFICATIONS = {
    NON_NAMED_COMPUTATIONAL_ILLUSTRATION,
    SOURCE_DECLARED_OPEN_NONRESULT_OBSERVATION,
}
USER_APPROVED_SCOPE_EXCLUSION_TIMESTAMP_RE = re.compile(
    r"^\d{4}-\d{2}-\d{2}(?:[T ][0-2]\d:[0-5]\d(?::[0-5]\d(?:\.\d+)?)?(?:Z|[+-][0-2]\d:[0-5]\d)?)?$"
)
SOURCE_INVENTORY_KINDS = SOURCE_RESULT_KINDS | SOURCE_VOCABULARY_KINDS | {
    "formula",
    "equation",
    "algorithmic_formula",
    "model",
    "algorithm",
    "assumption",
    "example",
    "remark",
    "figure",
    "table",
    "caption",
    "figure_caption",
    "table_caption",
    "simulation",
    "empirical_observation",
    "computational_observation",
    "implementation_measurement",
    # A source-visible unnumbered assertion is retained in the inventory but
    # has no inherent theorem-label semantics.  Its explicit user-scope lane
    # still requires claim-bearing/source-anchor validation below.
    "prose_assertion",
    # Named conjectures/open questions are catalogue-visible but have a
    # dedicated source-declared-open non-proof disposition.
    "open_problem",
}


def source_inventory_precheck_summary(folder: Path) -> dict[str, Any]:
    """Check source-map readiness without parsing Lean rows.

    This is deliberately an inexpensive first gate. It separates source-map
    defects that must be repaired before a closeout run spends time extracting
    elaborated signatures from expected source-to-dashboard work that requires
    those rows. It cannot validate row links or semantic theorem fidelity;
    callers must still run the full paper-coverage and source-to-Lean checks
    after refreshing the cache.
    """

    full_inventory, inventory, mode, mode_error = paper_coverage_inventory(folder)
    statement_map_payload = paper_statement_map_payload(folder)
    deep_attestation_error = deep_source_coverage_attestation_error(
        statement_map_payload, mode
    )
    audit = load_llm_paper_coverage_audit(folder)
    audit_items = audit.get("items") if isinstance(audit.get("items"), dict) else {}
    coverage_item_bindings, ambiguous_semantic_item_bindings = (
        _semantic_coverage_item_bindings(inventory, audit_items, mode)
    )
    bound_audit_items = {
        source_key: audit_items[audit_key]
        for source_key, audit_key in coverage_item_bindings.items()
        if isinstance(audit_items.get(audit_key), dict)
    }
    audit_required = paper_coverage_audit_required(folder, inventory)
    mode_migration_error = source_coverage_mode_migration_error(
        statement_map_payload, require_explicit=audit_required
    )
    raw_source_map_errors = paper_source_map_structural_errors(folder)
    source_presentation_classification_errors = sorted(
        set(
            raw_source_map_errors
            if statement_map_payload
            else [
                f"{key}: {error}"
                for key, item in full_inventory.items()
                for error in source_item_scope_classification_errors(item)
            ]
        )
    )
    inventory_hash = paper_coverage_inventory_digest(
        inventory, mode=mode, statement_map_payload=statement_map_payload
    )
    full_inventory_hash = paper_statement_inventory_digest(full_inventory)
    recorded_inventory_hash = str(
        audit.get("paper_statement_inventory_sha256") or ""
    ).strip()
    recorded_mode = str(audit.get("source_coverage_mode") or "").strip()
    mode_mismatch = bool(
        recorded_mode and not source_coverage_modes_compatible(recorded_mode, mode)
    )
    missing_coverage = sorted(key for key in inventory if key not in bound_audit_items)
    # A legacy deep sidecar may contain useful completed work for observations
    # that are outside ordinary named-theory closeout. Keep it visible but do
    # not make it a new default obligation.
    extra_coverage = sorted(
        key
        for key in audit_items
        if key not in full_inventory and key not in set(coverage_item_bindings.values())
    )
    out_of_mode_coverage = sorted(
        key for key in audit_items if key in full_inventory and key not in inventory
    )
    missing_statement_digest = sorted(
        key
        for key, item in bound_audit_items.items()
        if not str(item.get("statement_sha256") or "").strip()
    )
    stale_statement = sorted(
        key
        for key, item in bound_audit_items.items()
        if str(item.get("statement_sha256") or "").strip()
        and str(item.get("statement_sha256") or "").strip()
        != _source_item_coverage_statement(inventory[key])[1]
    )
    aggregate_current = recorded_inventory_hash in {
        inventory_hash,
        # Pre-mode sidecars used the full inventory hash. They remain valid
        # when the full inventory itself is unchanged.
        full_inventory_hash,
    }
    source_artifact_current = _coverage_audit_source_artifact_is_current(
        audit, statement_map_payload
    )
    source_artifact_identity_declared = _source_artifact_identity_is_declared(
        statement_map_payload
    )
    source_artifact_identity_recorded = _coverage_audit_records_source_artifact_identity(
        audit
    )
    stale_source_items = sorted(
        key
        for key, item in bound_audit_items.items()
        if _coverage_item_has_current_source_digest_schema(item)
        and not _coverage_item_source_digest_is_current(item, inventory[key], mode)
    )
    # Source semantic identity deliberately excludes navigation locators so a
    # harmless line shift does not reopen an LLM judgment. Byte anchors are
    # cheap to validate, however, and must be checked on every normal read: a
    # moved map anchor with unchanged source bytes would otherwise evade both
    # the aggregate semantic digest and the artifact-identity comparison.
    semantic_reuse_anchor_errors = _semantic_reuse_source_anchor_errors(
        folder,
        [
            key
            for key, item in bound_audit_items.items()
            if _coverage_item_has_current_source_digest_schema(item)
            and _coverage_item_source_digest_is_current(item, inventory[key], mode)
        ],
    )
    unverified_reused_source_items = sorted(semantic_reuse_anchor_errors)
    legacy_unpinned_items = sorted(
        key
        for key, item in bound_audit_items.items()
        if not _coverage_item_has_current_source_digest_schema(item)
        and (
            not aggregate_current
            or (
                source_artifact_identity_declared
                and source_artifact_identity_recorded
                and not source_artifact_current
            )
        )
    )
    missing_source_url = sorted(
        key
        for key, item in inventory.items()
        if _is_statement_map_source(item.get("source"))
        and not str(item.get("source_url") or "").strip()
    )
    missing_source_provenance = sorted(
        key
        for key, item in inventory.items()
        if _is_statement_map_source(item.get("source"))
        and not (
            str(item.get("source_location") or "").strip()
            or str(item.get("source_note") or "").strip()
            or str(item.get("source_status") or "").strip()
        )
    )
    unknown_source_kind = sorted(
        key
        for key, item in inventory.items()
        if _is_statement_map_source(item.get("source"))
        and str(item.get("source_kind") or "").strip()
        and str(item.get("source_kind") or "").strip().lower()
        not in SOURCE_INVENTORY_KINDS
    )
    source_scope_classification_errors = (
        _source_scope_classification_errors(inventory, bound_audit_items)
        if mode == DEEP_PAPER_WITH_ALL_PROSE_CLAIMS
        else []
    )
    user_approved_scope_exclusion_errors = _user_approved_scope_exclusion_errors(
        inventory, bound_audit_items
    )
    def corrected_target_coverage_error_for(key: str) -> str:
        return _corrected_target_coverage_error(
            inventory[key],
            bound_audit_items[key],
            _normalize_paper_coverage_judgment(bound_audit_items[key].get("coverage")),
            source_inventory=full_inventory,
            paper_name=folder.name,
            semantic_contract_schema=statement_map_payload.get(
                "semantic_contract_schema"
            ),
        )

    corrected_target_coverage_errors = sorted(
        f"{key}: {error}"
        for key in inventory
        if key in bound_audit_items
        for error in [corrected_target_coverage_error_for(key)]
        if error
    )
    source_anchor_evidence_errors = _scoped_source_anchor_evidence_errors(folder)
    source_named_result_inventory_errors = _source_named_result_inventory_errors(
        folder
    )
    missing_inventory_digest = bool(
        audit_items
        and not recorded_inventory_hash
        and any(
            not _coverage_item_has_current_source_digest_schema(item)
            for item in bound_audit_items.values()
        )
    )
    stale_inventory = bool(audit_items and not aggregate_current)
    prompt_version_stale = bool(
        audit_items
        and str(audit.get("prompt_version") or "").strip()
        != REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION
    )
    metadata_missing = bool(audit_items and audit.get("metadata_missing"))
    source_grounded = audit.get("source_grounded") is True
    semantic_audit_kind = str(audit.get("audit_kind") or "").strip()
    audit_not_semantic = bool(
        audit_items
        and (
            semantic_audit_kind not in APPROVED_PAPER_COVERAGE_AUDIT_KINDS
            or not source_grounded
            or bool(audit.get("seed_scaffold"))
        )
    )
    missing_coverage_sidecar = bool(audit_required and not audit_items)

    # A cache refresh needs a well-formed source inventory, but it is often the
    # prerequisite for the semantic source-to-dashboard judgment itself. Keep
    # these categories separate so a blank or intentionally fail-closed
    # scaffold does not instruct users to complete the coverage audit before
    # the current dashboard rows exist.
    pre_manifest_blockers: list[str] = []
    if mode_error:
        pre_manifest_blockers.append("source coverage mode is invalid")
    if mode_migration_error:
        pre_manifest_blockers.append("source coverage mode migration is incomplete")
    if deep_attestation_error:
        pre_manifest_blockers.append("deep source-coverage attestation is invalid")
    if source_presentation_classification_errors:
        pre_manifest_blockers.append(
            f"{len(source_presentation_classification_errors)} source-map structural/classification error(s)"
        )
    if source_named_result_inventory_errors:
        pre_manifest_blockers.append(
            f"{len(source_named_result_inventory_errors)} named-result inventory reconciliation error(s)"
        )
    if missing_source_url:
        pre_manifest_blockers.append(
            f"{len(missing_source_url)} source item(s) lack source URLs"
        )
    if missing_source_provenance:
        pre_manifest_blockers.append(
            f"{len(missing_source_provenance)} source item(s) lack source provenance"
        )
    if unknown_source_kind:
        pre_manifest_blockers.append(
            f"{len(unknown_source_kind)} source item(s) use unknown source_kind values"
        )
    if source_scope_classification_errors:
        pre_manifest_blockers.append(
            f"{len(source_scope_classification_errors)} source-scope classification error(s)"
        )
    if source_anchor_evidence_errors:
        pre_manifest_blockers.append(
            f"{len(source_anchor_evidence_errors)} source-anchor evidence error(s)"
        )

    semantic_coverage_pending: list[str] = []
    if audit_required:
        if missing_coverage_sidecar:
            semantic_coverage_pending.append("missing paper_coverage_llm.json")
        if missing_coverage:
            semantic_coverage_pending.append(
                f"{len(missing_coverage)} source item(s) missing coverage entries"
            )
        if extra_coverage:
            semantic_coverage_pending.append(
                f"{len(extra_coverage)} coverage entries have no source-map item"
            )
        if missing_statement_digest:
            semantic_coverage_pending.append(
                f"{len(missing_statement_digest)} coverage item(s) lack source-statement digests"
            )
        if stale_statement:
            semantic_coverage_pending.append(
                f"{len(stale_statement)} coverage source-statement digest(s) are stale"
            )
        if missing_inventory_digest:
            semantic_coverage_pending.append("coverage sidecar lacks its inventory digest")
        if stale_inventory:
            semantic_coverage_pending.append("coverage sidecar inventory digest is stale")
        if stale_source_items:
            semantic_coverage_pending.append(
                f"{len(stale_source_items)} source-item coverage receipt(s) are stale"
            )
        if unverified_reused_source_items:
            semantic_coverage_pending.append(
                f"{len(unverified_reused_source_items)} reused coverage item(s) lack current source-anchor verification"
            )
        if legacy_unpinned_items:
            semantic_coverage_pending.append(
                f"{len(legacy_unpinned_items)} legacy coverage item(s) need source pins"
            )
        if mode_mismatch:
            semantic_coverage_pending.append("coverage sidecar uses a different source-coverage mode")
        if ambiguous_semantic_item_bindings:
            semantic_coverage_pending.append(
                f"{len(ambiguous_semantic_item_bindings)} ambiguous source-to-coverage bindings"
            )
        if user_approved_scope_exclusion_errors:
            semantic_coverage_pending.append(
                f"{len(user_approved_scope_exclusion_errors)} invalid user-approved scope exclusion(s)"
            )
        if corrected_target_coverage_errors:
            semantic_coverage_pending.append(
                f"{len(corrected_target_coverage_errors)} corrected-target coverage error(s)"
            )
        if prompt_version_stale:
            semantic_coverage_pending.append("coverage prompt version is stale")
        if metadata_missing:
            semantic_coverage_pending.append("coverage sidecar lacks validator/timestamp metadata")
        if audit_not_semantic:
            semantic_coverage_pending.append(
                "coverage sidecar is not a source-grounded semantic audit"
            )

    needs_attention = bool(
        mode_error
        or mode_migration_error
        or deep_attestation_error
        or source_presentation_classification_errors
        or ambiguous_semantic_item_bindings
        or source_named_result_inventory_errors
        or (
            audit_required
            and (
            missing_coverage_sidecar
            or missing_coverage
            or extra_coverage
            or missing_statement_digest
            or stale_statement
            or missing_inventory_digest
            or stale_source_items
            or unverified_reused_source_items
            or legacy_unpinned_items
            or mode_mismatch
            or missing_source_url
            or missing_source_provenance
            or unknown_source_kind
            or source_scope_classification_errors
            or user_approved_scope_exclusion_errors
            or corrected_target_coverage_errors
            or source_anchor_evidence_errors
            or prompt_version_stale
            or metadata_missing
            or audit_not_semantic
            )
        )
    )
    return {
        "paper": folder.name,
        "audit_required": audit_required,
        "source_coverage_mode": mode,
        "source_coverage_mode_error": mode_error,
        "source_coverage_mode_migration_error": mode_migration_error,
        "deep_source_coverage_attestation_error": deep_attestation_error,
        "full_inventory_count": len(full_inventory),
        "inventory_count": len(inventory),
        "coverage_item_count": len(audit_items),
        "paper_statement_inventory_sha256": inventory_hash,
        "recorded_paper_statement_inventory_sha256": recorded_inventory_hash,
        "recorded_source_coverage_mode": recorded_mode,
        "source_coverage_mode_mismatch": mode_mismatch,
        "source_artifact_current": source_artifact_current,
        "missing_coverage_sidecar": missing_coverage_sidecar,
        "missing_coverage": missing_coverage,
        "extra_coverage": extra_coverage,
        "out_of_mode_coverage": out_of_mode_coverage,
        "missing_statement_digest": missing_statement_digest,
        "stale_statement": stale_statement,
        "stale_source_items": stale_source_items,
        "unverified_reused_source_items": unverified_reused_source_items,
        "semantic_reuse_source_anchor_errors": semantic_reuse_anchor_errors,
        "legacy_unpinned_items": legacy_unpinned_items,
        "missing_inventory_digest": missing_inventory_digest,
        "stale_inventory": stale_inventory,
        "missing_source_url": missing_source_url,
        "missing_source_provenance": missing_source_provenance,
        "unknown_source_kind": unknown_source_kind,
        "source_scope_classification_errors": source_scope_classification_errors,
        "source_presentation_classification_errors": source_presentation_classification_errors,
        "source_map_structural_error_count": len(raw_source_map_errors),
        "semantic_item_rebinding_count": sum(
            source_key != audit_key
            for source_key, audit_key in coverage_item_bindings.items()
        ),
        "ambiguous_semantic_item_bindings": ambiguous_semantic_item_bindings,
        "user_approved_scope_exclusion_errors": user_approved_scope_exclusion_errors,
        "corrected_target_coverage_errors": corrected_target_coverage_errors,
        "source_anchor_evidence_errors": source_anchor_evidence_errors,
        "source_named_result_inventory_errors": source_named_result_inventory_errors,
        "source_named_result_inventory_error_count": len(
            source_named_result_inventory_errors
        ),
        "prompt_version_stale": prompt_version_stale,
        "metadata_missing": metadata_missing,
        "audit_not_semantic": audit_not_semantic,
        "pre_manifest_blockers": pre_manifest_blockers,
        "pre_manifest_blocked": bool(pre_manifest_blockers),
        "semantic_coverage_pending": semantic_coverage_pending,
        "needs_attention": needs_attention,
    }
LEAN_PROOF_DECLARATION_KINDS = {"theorem", "lemma"}
LEAN_SPECIFICATION_DECLARATION_KINDS = {"definition"}
SOURCE_REVIEW_TARGET_RE = re.compile(
    r"\b(definition|example|remark|proposition|theorem|corollary|lemma)\b",
    re.IGNORECASE,
)
SOURCE_APPENDIX_RE = re.compile(r"\bappendix\b", re.IGNORECASE)
SOURCE_NON_TARGET_REASONS = (
    "not a separate",
    "not an independent",
    "not a standalone",
    "proof-only",
    "proof step",
    "proof detail",
    "section heading",
    "background",
    "bibliographic",
    "notation-only",
    "purely notational",
    "duplicate restatement",
)


def _source_inventory_core_text(item: dict[str, Any]) -> str:
    """Return the source assertion and locator, excluding curator-only metadata.

    A map key, Lean declaration, or an explanatory note is navigation metadata,
    not evidence that the source itself stated a formal result.  This narrower
    view is used when deciding whether an attempted computational-illustration
    exemption is describing an actual source theorem/algorithm rather than
    merely mentioning one in its curator's explanation.
    """

    fields = (
        item.get("title"),
        item.get("statement"),
        item.get("source_location"),
    )
    return "\n".join(str(field or "") for field in fields if str(field or "").strip())


def _source_text_has_general_computational_claim(text: str) -> bool:
    """Return whether source prose asserts general computational behavior.

    This intentionally does not classify bare mathematical adjectives such as
    ``exponential`` or ``quadratic``.  It recognizes resource bounds, Big-O
    notation, and behavior promised by an algorithm/procedure/method instead.
    """

    return bool(
        SOURCE_COMPLEXITY_TERMINOLOGY_RE.search(text)
        or SOURCE_BIG_O_COMPLEXITY_RE.search(text)
        or SOURCE_ALGORITHM_BEHAVIOR_RE.search(text)
        or SOURCE_GENERAL_OUTPUT_GUARANTEE_RE.search(text)
        or SOURCE_RESOURCE_BOUND_RE.search(text)
        or SOURCE_CONTEXTUAL_EFFICIENCY_RE.search(text)
    )


def _source_text_has_general_result_assertion(text: str) -> bool:
    """Return whether ordinary source prose makes a general paper-result claim.

    This complements the algorithmic/resource-bound detector.  It intentionally
    keys off source words and quantifiers, rather than source-map navigation keys
    or Lean declaration spelling, so an unnumbered existence/correctness/
    optimality result cannot be hidden as an illustration.
    """

    return bool(SOURCE_GENERAL_RESULT_ASSERTION_RE.search(text))


def _source_text_has_finite_computational_observation(text: str) -> bool:
    """Return whether one source sentence presents a finite observed result.

    Requiring both a concrete finite-observation cue and a reporting verb keeps
    the exception positive and narrow.  A display label such as ``Figure 1``
    cannot by itself turn a general source conclusion into an excluded example.
    """

    sentences = re.split(r"[.!?;]+", text.replace("\n", " "))
    return any(
        SOURCE_FINITE_OBSERVATION_CONCRETE_CUE_RE.search(sentence)
        and SOURCE_FINITE_OBSERVATION_REPORT_RE.search(sentence)
        for sentence in sentences
    )


def _source_inventory_item_is_named_algorithm_block(item: dict[str, Any]) -> bool:
    """Return whether the source identifies an Algorithm/Procedure/Method block.

    The source kind is an explicit source-map classification, not a Lean name;
    literal headers/ref forms catch maps produced from TeX or prose inventories.
    """

    if str(item.get("source_kind") or "").strip().lower() == "algorithm":
        return True
    return bool(SOURCE_NAMED_ALGORITHM_BLOCK_RE.search(_source_inventory_core_text(item)))


def _source_anchor_paths_match(left: str, right: str) -> bool:
    """Compare source paths without treating a map key as source evidence."""

    normalized_left = left.replace("\\", "/").lstrip("./")
    normalized_right = right.replace("\\", "/").lstrip("./")
    return (
        normalized_left == normalized_right
        or normalized_left.endswith("/" + normalized_right)
        or normalized_right.endswith("/" + normalized_left)
    )


def _source_inventory_anchor_quote_text(item: dict[str, Any]) -> tuple[str, str]:
    """Return the declared source-anchor quote, or an evidence-shape error.

    The full evidence-integrity gate independently checks these quotes against
    the byte-pinned source artifact.  This local check makes the dashboard's
    scope classifier consume only quotes tied to its declared file-and-line
    anchors, rather than trusting a curator's paraphrase in ``statement`` or
    ``source_evidence``.
    """

    source_location = str(item.get("source_location") or "").strip()
    anchors = [
        (
            match.group("path"),
            int(match.group("start")),
            int(match.group("end") or match.group("start")),
        )
        for match in SOURCE_FILE_LINE_ANCHOR_RE.finditer(source_location)
    ]
    if not anchors:
        return (
            "",
            "requires byte-verified source_anchor_evidence tied to exact "
            "file:line source anchors",
        )

    raw_evidence = item.get("source_anchor_evidence")
    if not isinstance(raw_evidence, list) or not raw_evidence:
        return (
            "",
            "requires a nonempty byte-verified source_anchor_evidence list",
        )

    quotes: list[str | None] = [None] * len(anchors)
    for raw_entry in raw_evidence:
        if not isinstance(raw_entry, dict):
            return "", "source_anchor_evidence entries must be objects"
        raw_path = str(raw_entry.get("path") or "").strip()
        line_start = raw_entry.get("line_start")
        line_end = raw_entry.get("line_end")
        if (
            not raw_path
            or not isinstance(line_start, int)
            or isinstance(line_start, bool)
            or not isinstance(line_end, int)
            or isinstance(line_end, bool)
        ):
            return (
                "",
                "source_anchor_evidence entries require path, line_start, and line_end",
            )
        matches = [
            index
            for index, (anchor_path, anchor_start, anchor_end) in enumerate(anchors)
            if _source_anchor_paths_match(raw_path, anchor_path)
            and line_start == anchor_start
            and line_end == anchor_end
        ]
        if len(matches) != 1 or quotes[matches[0]] is not None:
            return (
                "",
                "source_anchor_evidence must provide exactly one quote for each "
                "declared source anchor",
            )
        raw_quote = raw_entry.get("quoted_text")
        raw_quote_digest = raw_entry.get("quoted_text_sha256")
        if not isinstance(raw_quote, str) or not raw_quote:
            return "", "source_anchor_evidence quoted_text must be a nonempty string"
        quote = raw_quote.replace("\r\n", "\n").replace("\r", "\n")
        if (
            not isinstance(raw_quote_digest, str)
            or not SOURCE_ARTIFACT_SHA256_RE.fullmatch(raw_quote_digest.strip())
            or hashlib.sha256(quote.encode("utf-8")).hexdigest()
            != raw_quote_digest.strip().lower()
        ):
            return (
                "",
                "source_anchor_evidence quoted_text_sha256 must match the "
                "normalized quoted_text",
            )
        quotes[matches[0]] = quote

    if any(quote is None for quote in quotes):
        return (
            "",
            "source_anchor_evidence must provide exactly one quote for each "
            "declared source anchor",
        )
    return "\n".join(quote for quote in quotes if quote is not None), ""


def _source_location_has_pinned_artifact_anchor(item: dict[str, Any]) -> str:
    """Return an error unless a scoped item names a pinned artifact and anchor.

    `audit_evidence_integrity.py` verifies bytes and, when opted in, quoted
    anchor slices.  The dashboard's cheap source-inventory gate additionally
    requires the exception itself to name that same artifact and an exact
    locator, so a free-form ``source_evidence`` string cannot waive review.
    """

    artifact_path = str(item.get("source_artifact_path") or "").strip()
    artifact_sha256 = str(item.get("source_artifact_sha256") or "").strip()
    source_location = str(item.get("source_location") or "").strip()
    if not artifact_path:
        return (
            "non_named_computational_illustration requires a pinned "
            "source_artifact_path"
        )
    if not SOURCE_ARTIFACT_SHA256_RE.fullmatch(artifact_sha256):
        return (
            "non_named_computational_illustration requires a valid pinned "
            "source_artifact_sha256"
        )
    canonical_path = str(item.get("canonical_source_artifact_path") or "").strip()
    canonical_sha256 = str(
        item.get("canonical_source_artifact_sha256") or ""
    ).strip()
    if canonical_path and (
        artifact_path.replace("\\", "/").lstrip("./")
        != canonical_path.replace("\\", "/").lstrip("./")
    ):
        return (
            "non_named_computational_illustration must use the source map's "
            "canonical pinned source artifact"
        )
    if canonical_sha256 and artifact_sha256.lower() != canonical_sha256.lower():
        return (
            "non_named_computational_illustration must use the source map's "
            "canonical source_artifact_sha256"
        )
    if not EXACT_SOURCE_LOCATOR_RE.search(source_location):
        return (
            "non_named_computational_illustration requires an exact "
            "source_location anchor"
        )

    artifact_suffix = Path(artifact_path).suffix.lower()
    file_anchors = list(SOURCE_FILE_LINE_ANCHOR_RE.finditer(source_location))
    if artifact_suffix in {".tex", ".txt", ".md"}:
        if not file_anchors:
            return (
                "non_named_computational_illustration requires a file:line "
                "anchor into the pinned source artifact"
            )
        normalized_artifact = artifact_path.replace("\\", "/").lstrip("./")
        normalized_anchor_paths = {
            match.group("path").replace("\\", "/").lstrip("./")
            for match in file_anchors
        }
        if not any(
            anchor_path == normalized_artifact
            or normalized_artifact.endswith("/" + anchor_path)
            or anchor_path.endswith("/" + normalized_artifact)
            for anchor_path in normalized_anchor_paths
        ):
            return (
                "non_named_computational_illustration source_location must name "
                "the pinned source artifact"
            )

    _, quote_error = _source_inventory_anchor_quote_text(item)
    if quote_error:
        return f"non_named_computational_illustration {quote_error}"
    return ""


def _source_inventory_item_is_named_claim(key: str, item: dict[str, Any]) -> bool:
    """Return whether a source inventory item should have row-level statement audit."""

    del key  # Map keys are navigation metadata, not semantic source evidence.
    return bool(SOURCE_NAMED_CLAIM_RE.search(_source_inventory_search_text("", item)))


def _source_inventory_item_is_named_result_presentation(item: dict[str, Any]) -> bool:
    """Return whether the source assertion itself presents a formal result.

    A cross-reference such as ``By Theorem 2`` is still review-visible, but it
    is not a new theorem endpoint.  A theorem/lemma/proposition heading or TeX
    environment is an endpoint and cannot be credited by a Lean definition.
    """

    return bool(
        SOURCE_NAMED_RESULT_PRESENTATION_RE.search(_source_inventory_core_text(item))
    )


def _source_inventory_item_scope_classification_error(item: dict[str, Any]) -> str:
    """Return an error when an explicit source-scope classification is unsafe."""

    classification = str(item.get("source_scope_classification") or "").strip().lower()
    if not classification:
        return ""
    if classification not in SOURCE_SCOPE_CLASSIFICATIONS:
        return f"unknown source_scope_classification `{classification}`"
    if classification == SOURCE_DECLARED_OPEN_NONRESULT_OBSERVATION:
        if item.get("claim_bearing") is not False:
            return "source_declared_open_nonresult_observation requires claim_bearing: false"
        if str(item.get("coverage_status") or "").strip().lower() != "source_declared_open":
            return (
                "source_declared_open_nonresult_observation requires coverage_status "
                "`source_declared_open`"
            )
        if str(item.get("protocol_role") or "").strip().lower() != "source_declared_open":
            return (
                "source_declared_open_nonresult_observation requires protocol_role "
                "`source_declared_open`"
            )
        if str(item.get("source_kind") or "").strip().lower() not in {
            "remark",
            "open_problem",
        }:
            return (
                "source_declared_open_nonresult_observation requires source_kind "
                "`remark` or `open_problem`"
            )
        artifact_error = _source_location_has_pinned_artifact_anchor(item)
        if artifact_error:
            return artifact_error
        if not str(item.get("scope_reason") or "").strip():
            return (
                "source_declared_open_nonresult_observation requires a "
                "source-grounded scope_reason"
            )
        if not str(item.get("source_evidence") or "").strip():
            return "source_declared_open_nonresult_observation requires source_evidence"
        source_quote, quote_error = _source_inventory_anchor_quote_text(item)
        if quote_error:
            return f"source_declared_open_nonresult_observation {quote_error}"
        if not SOURCE_DECLARED_OPEN_NONRESULT_RE.search(source_quote):
            return (
                "source_declared_open_nonresult_observation requires an explicit "
                "unresolved/open declaration in the byte-verified source quote"
            )
        if (
            SOURCE_NAMED_RESULT_PRESENTATION_RE.search(source_quote)
            or SOURCE_POSITIVE_RESULT_PRESENTATION_RE.search(source_quote)
        ):
            return (
                "source_declared_open_nonresult_observation cannot combine its open "
                "observation with a positive named or ordinary result assertion"
            )
        return ""

    assert classification == NON_NAMED_COMPUTATIONAL_ILLUSTRATION
    if item.get("claim_bearing") is not False:
        return "non_named_computational_illustration requires claim_bearing: false"
    source_kind = str(item.get("source_kind") or "").strip().lower()
    if source_kind not in SOURCE_CATALOGUED_NONFORMAL_OBSERVATION_KINDS:
        return (
            "non_named_computational_illustration requires source_kind "
            "`example` or `remark`"
        )
    artifact_error = _source_location_has_pinned_artifact_anchor(item)
    if artifact_error:
        return artifact_error
    source_assertion = _source_inventory_core_text(item)
    source_quote, quote_error = _source_inventory_anchor_quote_text(item)
    if quote_error:
        return f"non_named_computational_illustration {quote_error}"
    source_title = str(item.get("title") or "").strip()
    source_statement = str(item.get("statement") or "").strip()
    source_location = str(item.get("source_location") or "").strip()
    source_evidence = str(item.get("source_evidence") or "").strip()
    source_presentation = "\n".join(
        text
        for text in (source_title, source_statement, source_location, source_evidence)
        if text
    )
    # A source-evidence note may accurately cite a different theorem while
    # explaining why a figure is only illustrative.  Reject a formal result
    # reference in the item being classified, rather than a contextual mention
    # in that explanatory note; the ordinary inventory review path still sees
    # named references anywhere outside a validated illustration exemption.
    if SOURCE_NAMED_CLAIM_RE.search(source_assertion) or SOURCE_NAMED_CLAIM_RE.search(
        source_quote
    ):
        return (
            "non_named_computational_illustration cannot label a named formal "
            "statement or theorem reference"
        )
    if _source_text_has_general_computational_claim(
        "\n".join((source_presentation, source_quote))
    ):
        return (
            "non_named_computational_illustration cannot label a general "
            "algorithmic, runtime, complexity, or performance assertion"
        )
    if _source_text_has_general_result_assertion(
        "\n".join((source_presentation, source_quote))
    ):
        return (
            "non_named_computational_illustration cannot label a general "
            "correctness, existence, optimality, or mathematical assertion"
        )
    if _source_inventory_item_is_named_algorithm_block(item) or SOURCE_NAMED_ALGORITHM_BLOCK_RE.search(
        source_quote
    ):
        return (
            "non_named_computational_illustration cannot label a named "
            "Algorithm, Procedure, or Method block"
        )
    if not _source_text_has_finite_computational_observation(source_quote):
        return (
            "non_named_computational_illustration requires a literal finite "
            "observation/report in the byte-verified source quote"
        )
    if not str(item.get("scope_reason") or "").strip():
        return "non_named_computational_illustration requires a source-grounded scope_reason"
    if not str(item.get("source_evidence") or "").strip():
        return "non_named_computational_illustration requires source_evidence"
    return ""


def _source_inventory_item_user_approved_scope_exclusion_error(
    item: dict[str, Any],
) -> str:
    """Validate a user-approved exclusion without changing source semantics.

    This deliberately consumes only the source-map item, its pinned quote, and
    the structured human approval.  It never infers eligibility from a map key,
    Lean declaration, or a word such as ``simulation``.  A source-visible claim
    remains claim-bearing for inventory purposes; the user is choosing scope,
    not asserting that the source made no claim.
    """

    raw_approval = item.get(USER_APPROVED_SCOPE_EXCLUSION)
    if raw_approval is None:
        return ""
    if not isinstance(raw_approval, dict):
        return "user_approved_scope_exclusion must be an object"
    if raw_approval.get("schema") != USER_APPROVED_SCOPE_EXCLUSION_SCHEMA:
        return (
            "user_approved_scope_exclusion.schema must be "
            f"{USER_APPROVED_SCOPE_EXCLUSION_SCHEMA}"
        )
    if (
        str(raw_approval.get("approval_kind") or "").strip()
        != USER_APPROVED_SCOPE_EXCLUSION_APPROVAL_KIND
    ):
        return (
            "user_approved_scope_exclusion.approval_kind must be "
            f"`{USER_APPROVED_SCOPE_EXCLUSION_APPROVAL_KIND}`"
        )
    approval_reference = str(raw_approval.get("approval_reference") or "").strip()
    if len(approval_reference) < 8:
        return (
            "user_approved_scope_exclusion.approval_reference must identify "
            "the explicit user instruction"
        )
    approved_at = str(raw_approval.get("approved_at") or "").strip()
    if not USER_APPROVED_SCOPE_EXCLUSION_TIMESTAMP_RE.fullmatch(approved_at):
        return (
            "user_approved_scope_exclusion.approved_at must be an ISO-like "
            "date or timestamp"
        )
    for field in ("reason", "source_evidence"):
        text = str(raw_approval.get(field) or "").strip()
        if len(text) < 8:
            return f"user_approved_scope_exclusion.{field} must be nonempty source-facing text"
        if NAME_ONLY_SOURCE_COVERAGE_REASON_RE.search(text):
            return (
                f"user_approved_scope_exclusion.{field} cannot rely on a "
                "declaration name or map key"
            )
    if item.get("claim_bearing") is not True:
        return (
            "user_approved_scope_exclusion must keep the source assertion "
            "claim_bearing: true"
        )
    if str(item.get("source_scope_classification") or "").strip():
        return (
            "user_approved_scope_exclusion cannot coexist with a "
            "source_scope_classification"
        )
    if str(item.get("inventory_role") or "").strip().lower() == "proof_support":
        return (
            "user_approved_scope_exclusion cannot remove an assertion marked "
            "as proof_support for a retained paper result"
        )
    source_kind = str(item.get("source_kind") or "").strip().lower()
    if source_kind in USER_APPROVED_SCOPE_EXCLUSION_FORMAL_KINDS:
        return (
            "user_approved_scope_exclusion is limited to an unnumbered prose "
            "assertion and cannot exclude a source-labelled formal target"
        )
    if source_kind not in USER_APPROVED_UNNUMBERED_PROSE_SOURCE_KINDS:
        return (
            "user_approved_scope_exclusion requires an unnumbered prose "
            "inventory kind (`example`, `remark`, or `prose_assertion`)"
        )
    source_locator = str(raw_approval.get("source_locator") or "").strip()
    source_location = str(item.get("source_location") or "").strip()
    if not source_locator:
        return "user_approved_scope_exclusion.source_locator must be a concrete source anchor"
    if source_locator != source_location:
        return (
            "user_approved_scope_exclusion.source_locator must exactly match "
            "the source item's source_location"
        )
    if not list(SOURCE_FILE_LINE_ANCHOR_RE.finditer(source_locator)):
        return (
            "user_approved_scope_exclusion.source_locator requires an exact "
            "file:line anchor"
        )
    source_quote, quote_error = _source_inventory_anchor_quote_text(item)
    if quote_error:
        return f"user_approved_scope_exclusion {quote_error}"
    # The kind narrows the inventory lane, but the pinned presentation remains
    # decisive.  A curator cannot relabel a theorem-like source block as a
    # remark to avoid a proof obligation.  Cross-references in explanatory
    # evidence are intentionally irrelevant; this inspects only the asserted
    # source item and its byte-verified quote.
    source_core = _source_inventory_core_text(item)
    if (
        SOURCE_NAMED_RESULT_HEADING_RE.search(source_core)
        or SOURCE_NAMED_RESULT_HEADING_RE.search(source_quote)
        or SOURCE_NAMED_ALGORITHM_BLOCK_RE.search(source_core)
        or SOURCE_NAMED_ALGORITHM_BLOCK_RE.search(source_quote)
    ):
        return (
            "user_approved_scope_exclusion cannot exclude a source-labelled "
            "formal result, theorem-like displayed statement, or named algorithm"
        )
    quoted_digest = str(
        raw_approval.get("source_anchor_quote_sha256") or ""
    ).strip().lower()
    if not SOURCE_ARTIFACT_SHA256_RE.fullmatch(quoted_digest):
        return (
            "user_approved_scope_exclusion.source_anchor_quote_sha256 must be "
            "a SHA-256 digest"
        )
    expected_digest = hashlib.sha256(source_quote.encode("utf-8")).hexdigest()
    if quoted_digest != expected_digest:
        return (
            "user_approved_scope_exclusion.source_anchor_quote_sha256 must pin "
            "the byte-verified source anchor quote"
        )
    return ""


def _source_inventory_item_has_valid_user_approved_scope_exclusion(
    item: dict[str, Any],
) -> bool:
    """Return whether a source item has a complete explicit user exclusion."""

    return (
        item.get(USER_APPROVED_SCOPE_EXCLUSION) is not None
        and not _source_inventory_item_user_approved_scope_exclusion_error(item)
    )


def _source_inventory_item_is_catalogued_nonformal_observation(
    item: dict[str, Any],
) -> bool:
    """Return whether a source item is an explicitly non-theorem observation.

    This is intentionally driven only by source-curated fields and literal source
    presentation.  A numerical figure, experiment, or simulation does not gain
    theorem scope merely because a Lean helper has a theorem-shaped name.  The
    inverse safeguard matters just as much: a source theorem/proposition/etc.
    cannot escape review by setting ``claim_bearing: false``.
    """

    classification = str(item.get("source_scope_classification") or "").strip().lower()
    return (
        classification
        in {
            NON_NAMED_COMPUTATIONAL_ILLUSTRATION,
            SOURCE_DECLARED_OPEN_NONRESULT_OBSERVATION,
        }
        and not _source_inventory_item_scope_classification_error(item)
    )


def _source_scope_classification_errors(
    inventory: dict[str, dict[str, Any]], audit_items: dict[str, Any]
) -> list[str]:
    """Validate source-only scope lanes and reject any Lean coverage credit."""

    out_of_scope_coverage = {
        "out_of_scope",
        "not_a_paper_target",
        "not_a_theorem_statement",
    }
    errors: list[str] = []
    for key, item in inventory.items():
        error = _source_inventory_item_scope_classification_error(item)
        if error:
            errors.append(f"{key}: {error}")
            continue
        if not _source_inventory_item_is_catalogued_nonformal_observation(item):
            continue
        classification = str(
            item.get("source_scope_classification") or ""
        ).strip().lower()
        coverage_item = audit_items.get(key)
        if not isinstance(coverage_item, dict):
            errors.append(
                f"{key}: {classification} requires an explicit "
                "out-of-theorem-scope coverage judgment"
            )
            continue
        coverage = _normalize_paper_coverage_judgment(coverage_item.get("coverage"))
        if coverage not in out_of_scope_coverage:
            errors.append(
                f"{key}: {classification} must use an explicit "
                "out-of-theorem-scope coverage judgment"
            )
        source_quote, quote_error = _source_inventory_anchor_quote_text(item)
        if quote_error:
            # The item-level classifier emits the more precise evidence error;
            # do not invent a digest for untrusted or incomplete quote data.
            continue
        expected_quote_digest = hashlib.sha256(
            source_quote.encode("utf-8")
        ).hexdigest()
        scope_judgment = str(
            coverage_item.get("source_scope_judgment") or ""
        ).strip().lower()
        expected_scope_judgment = (
            "finite_nonclaim_observation"
            if classification == NON_NAMED_COMPUTATIONAL_ILLUSTRATION
            else SOURCE_DECLARED_OPEN_NONRESULT_OBSERVATION
        )
        if scope_judgment != expected_scope_judgment:
            errors.append(
                f"{key}: {classification} requires the independent "
                f"source_scope_judgment `{expected_scope_judgment}`"
            )
        if str(coverage_item.get("source_anchor_quote_sha256") or "").strip().lower() != expected_quote_digest:
            errors.append(
                f"{key}: {classification} coverage must pin "
                "source_anchor_quote_sha256 to the byte-verified anchor quote"
            )
        rows = _normalize_string_list(coverage_item.get("review_rows"))
        support = _normalize_string_list(coverage_item.get("support_declarations"))
        row_signature_pins = coverage_item.get("review_row_signature_sha256")
        if rows or row_signature_pins:
            errors.append(
                f"{key}: {classification} cannot claim review_rows or review-row "
                "signature pins"
            )
        if support:
            errors.append(
                f"{key}: {classification} cannot claim support_declarations"
            )
    return sorted(errors)


def _user_approved_scope_exclusion_errors(
    inventory: dict[str, dict[str, Any]], audit_items: dict[str, Any]
) -> list[str]:
    """Validate the separate explicit-user source-claim exclusion lane.

    A valid record is a visible source claim plus an auditable scope decision.
    It must not use the computational-observation classification, must not
    carry Lean rows as proof credit, and must be represented by the dedicated
    coverage verdict.  All routing is driven by structured source evidence,
    not identifiers or declaration names.
    """

    errors: list[str] = []
    for key, item in inventory.items():
        raw_approval = item.get(USER_APPROVED_SCOPE_EXCLUSION)
        coverage_item = audit_items.get(key)
        coverage = (
            _normalize_paper_coverage_judgment(coverage_item.get("coverage"))
            if isinstance(coverage_item, dict)
            else ""
        )
        if raw_approval is not None:
            error = _source_inventory_item_user_approved_scope_exclusion_error(item)
            if error:
                errors.append(f"{key}: {error}")
            if coverage != USER_APPROVED_SCOPE_EXCLUSION:
                errors.append(
                    f"{key}: user_approved_scope_exclusion requires the explicit "
                    "user_approved_scope_exclusion coverage judgment"
                )
        if coverage != USER_APPROVED_SCOPE_EXCLUSION:
            continue
        if raw_approval is None:
            errors.append(
                f"{key}: user_approved_scope_exclusion coverage requires structured "
                "user_approved_scope_exclusion metadata in the source map"
            )
            continue
        rows = _normalize_string_list(coverage_item.get("review_rows"))
        support = _normalize_string_list(coverage_item.get("support_declarations"))
        if rows:
            errors.append(
                f"{key}: user_approved_scope_exclusion cannot claim review_rows"
            )
        if support:
            errors.append(
                f"{key}: user_approved_scope_exclusion cannot claim support_declarations"
            )
    return sorted(set(errors))


def _scoped_source_anchor_evidence_errors(folder: Path) -> list[str]:
    """Return byte-validation failures on the active semantic source surface.

    The classifier above only consumes structured quote records.  Invoke the
    shared integrity gate here as well, so a dashboard/precheck cannot report a
    scoped row clean until those records are proved to be exact slices of the
    pinned source bytes.  Project the map before invoking that gate: a normal
    named-theory audit must validate its selected theorem/definition surface
    (and explicit correction or exclusion obligations), without silently
    turning an unanchored deep-only formula, caption, or algorithm into a
    normal closeout blocker.  Deep mode projects the whole source inventory.
    """

    map_path = folder / PAPER_STATEMENT_MAP_FILE
    if not _dashboard_is_file(map_path):
        return []
    payload = _dashboard_json_payload(map_path)
    if payload is None:
        return []
    if not isinstance(payload, dict):
        return []
    try:
        try:
            from scripts.audit_evidence_integrity import (
                scoped_source_map_payload,
                source_anchor_evidence_findings,
            )
        except ModuleNotFoundError:
            from audit_evidence_integrity import (
                scoped_source_map_payload,
                source_anchor_evidence_findings,
            )
        mode, _mode_error = source_coverage_mode_from_map(payload)
        scoped_payload, _scoped_items = scoped_source_map_payload(
            payload,
            mode,
            folder=folder,
            repository_root=ROOT,
        )
        findings = source_anchor_evidence_findings(
            folder,
            "formalized",
            map_path,
            scoped_payload,
            file_bytes_override=_dashboard_file_bytes_override(),
        )
    except Exception as error:  # noqa: BLE001 - evidence validation fails closed.
        return [f"source-anchor evidence validator failed: {error}"]
    return sorted(str(finding.message) for finding in findings)


def _source_named_result_inventory_errors(folder: Path) -> list[str]:
    """Return source-only named-result completeness failures for this paper.

    The dashboard uses this small shared integrity lane before it trusts a
    curated map as a complete ordinary source surface.  It is deliberately
    independent of review-row/map-key spelling and remains cheap compared with
    Lean signature extraction.
    """

    map_path = folder / PAPER_STATEMENT_MAP_FILE
    if not _dashboard_is_file(map_path):
        return []
    payload = _dashboard_json_payload(map_path)
    if payload is None:
        return []
    if not isinstance(payload, dict):
        return []
    status_payload = (
        _dashboard_json_payload(folder / DEFAULT_PAPER_STATUS_FILE) or {}
    )
    status = (
        str(status_payload.get("status") or "paper draft")
        if isinstance(status_payload, dict)
        else "paper draft"
    )
    try:
        try:
            from scripts.audit_evidence_integrity import source_named_result_inventory_findings
        except ModuleNotFoundError:
            from audit_evidence_integrity import (
                source_named_result_inventory_findings,
            )
        findings = source_named_result_inventory_findings(
            folder,
            status,
            map_path,
            payload,
            file_bytes_override=_dashboard_file_bytes_override(),
        )
    except Exception as error:  # noqa: BLE001 - completeness fails closed.
        return [f"source named-result inventory validator failed: {error}"]
    return sorted({str(finding.message) for finding in findings})


def _semantic_reuse_source_anchor_errors(
    folder: Path, source_keys: Iterable[str]
) -> dict[str, list[str]]:
    """Byte-validate only source items proposed for per-item cache reuse.

    A semantic source digest can ignore unrelated changes to the source
    artifact only when the item itself has an exact, current source quote.
    This helper deliberately forces quote validation for the candidate subset
    even if the paper has not requested a full deep-paper anchor audit.
    """

    keys = sorted({str(key).strip() for key in source_keys if str(key).strip()})
    if not keys:
        return {}
    map_path = folder / PAPER_STATEMENT_MAP_FILE
    payload = _dashboard_json_payload(map_path)
    if payload is None:
        return {key: ["source map is unavailable for semantic item reuse"] for key in keys}
    if not isinstance(payload, dict) or not isinstance(payload.get("items"), dict):
        return {key: ["source map items are unavailable for semantic item reuse"] for key in keys}
    raw_items = payload["items"]
    selected: dict[str, Any] = {}
    errors: dict[str, list[str]] = {}
    for key in keys:
        raw_item = raw_items.get(key)
        if not isinstance(raw_item, dict):
            errors[key] = ["current source item is unavailable for semantic item reuse"]
        else:
            selected[key] = raw_item
    if not selected:
        return errors

    scoped_payload = dict(payload)
    scoped_payload["items"] = selected
    # This is a narrow cache-freshness requirement, not a request to audit
    # captions/prose.  Each selected item must nevertheless prove its source
    # quote against the current canonical bytes before its old judgment moves.
    scoped_payload["source_anchor_evidence_required"] = True
    try:
        try:
            from scripts.audit_evidence_integrity import source_anchor_evidence_findings
        except ModuleNotFoundError:
            from audit_evidence_integrity import source_anchor_evidence_findings
        findings = source_anchor_evidence_findings(
            folder,
            "formalized",
            map_path,
            scoped_payload,
            file_bytes_override=_dashboard_file_bytes_override(),
        )
    except Exception as error:  # noqa: BLE001 - freshness must fail closed.
        message = f"source-anchor reuse validator failed: {error}"
        return {
            key: [message]
            for key in keys
            if key not in errors
        } | errors

    for finding in findings:
        message = str(finding.message)
        matched = [
            key
            for key in selected
            if message.startswith(f"items.{key}.")
            or message.startswith(f"items.{key}:")
        ]
        # Artifact/payload failures have no item prefix and therefore make all
        # proposed semantic reuse unsafe, rather than attributing a global
        # source-byte failure to an arbitrary item.
        for key in matched or list(selected):
            errors.setdefault(key, []).append(message)
    return {key: sorted(set(messages)) for key, messages in errors.items()}


def _source_inventory_item_requires_proof_evidence(
    key: str, item: dict[str, Any]
) -> bool:
    """Return whether direct coverage must include a Lean proof declaration.

    The primary classification is the structured source kind.  A legacy
    statement-map item without that classification fails closed: it may not use
    a matching ``def``/``abbrev`` row as evidence that a paper-facing result was
    proved.  Explicit source definitions and predicate vocabulary retain their
    ordinary translation-only coverage lane.  Fallback TeX inventories use the
    existing source-label classifier because they have no statement-map schema.
    """

    source_kind = str(item.get("source_kind") or "").strip().lower()
    # A source definition or premise is review-visible, but it is not proof
    # evidence merely because the inventory correctly records it as a claim or
    # governing condition.  These lanes require exact source-to-Lean
    # translation/provenance checks rather than a theorem/lemma declaration.
    if source_kind in {"assumption", "model"}:
        return False
    if source_kind in SOURCE_VOCABULARY_KINDS:
        return False
    if source_kind in SOURCE_RESULT_KINDS:
        return True
    if item.get("claim_bearing") is True:
        return True
    source_text = _source_inventory_search_text(key, item)
    if (
        _source_text_has_general_computational_claim(source_text)
        or _source_text_has_general_result_assertion(source_text)
    ):
        return True
    if _source_inventory_item_is_named_result_presentation(item):
        return True
    if source_kind:
        return source_kind in SOURCE_RESULT_KINDS
    if _is_statement_map_source(item.get("source")):
        return True
    return _source_inventory_item_is_named_claim(key, item)


def _source_inventory_item_is_quarantined_defect(item: dict[str, Any]) -> bool:
    """Return whether the source result is explicitly quarantined as defective."""

    return bool(source_item_effective_route_policy(item)["is_quarantined_source_defect"])


def _review_item_declaration_kind(item: ReviewItem) -> str:
    """Return the declaration kind, preferring the elaborated Lean manifest."""

    manifest = item.lean_signature_manifest
    if isinstance(manifest, dict) and manifest.get("schema") == 2:
        manifest_kind = str(manifest.get("declaration_kind") or "").strip().lower()
        if manifest_kind:
            return manifest_kind
    syntactic_kind = str(item.kind or "").strip().lower()
    if syntactic_kind in {"def", "abbrev"}:
        return "definition"
    return syntactic_kind


SOURCE_PROOF_DEFECT_SNAPSHOT_FIELDS = (
    "id",
    "source_locator",
    "source_claim",
    "defect_kind",
    "affected_source_locators",
    "statement_impact",
    "repair_obligation",
    "acceptance_condition",
    "resolution",
    "resolution_evidence",
)


def source_proof_defect_snapshot(defect: dict[str, Any]) -> dict[str, Any]:
    """Return the exact semantic defect record frozen by support judgments."""

    return {field: defect.get(field) for field in SOURCE_PROOF_DEFECT_SNAPSHOT_FIELDS}


def source_proof_defect_digest(defect: dict[str, Any]) -> str:
    """Hash the source-located mathematics of one validated defect record."""

    encoded = json.dumps(
        source_proof_defect_snapshot(defect),
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _validated_source_proof_defects(folder: Path) -> dict[str, dict[str, Any]]:
    """Return exact records from a fully validated configured defect ledger.

    Quarantine support is a release-relevant claim about a defect in the source,
    so merely finding the same identifier in an arbitrary JSON file is not
    sufficient.  The configured ledger must have completed its defect review and
    pass the source-proof fidelity validator, including source-artifact pins and
    source-located mathematical obligations.
    """

    status_payload = _dashboard_json_payload(folder / DEFAULT_PAPER_STATUS_FILE)
    if not isinstance(status_payload, dict):
        return {}
    ledger_path: Path | None = None
    ledger_error = ""
    try:
        try:
            from scripts.audit_evidence_integrity import (
                source_proof_fidelity_config,
                source_proof_fidelity_findings,
                source_proof_fidelity_ledger_path,
            )
        except ModuleNotFoundError:
            from audit_evidence_integrity import (
                source_proof_fidelity_config,
                source_proof_fidelity_findings,
                source_proof_fidelity_ledger_path,
            )
        if source_proof_fidelity_config(status_payload) is None:
            return {}
        ledger_path, ledger_error = source_proof_fidelity_ledger_path(folder, status_payload)
        status = str(status_payload.get("status") or "not formalized").strip()
        if source_proof_fidelity_findings(
            folder,
            status,
            status_payload,
            file_bytes_override=_dashboard_file_bytes_override(),
        ):
            return {}
    except Exception:  # noqa: BLE001 - unavailable validation fails closed.
        return {}
    if ledger_error:
        return {}
    if ledger_path is None:
        return {}
    payload = _dashboard_json_payload(ledger_path)
    if payload is None:
        return {}
    if not isinstance(payload, dict) or payload.get("review_status") != "defects_recorded":
        return {}
    raw_defects = payload.get("defects") if isinstance(payload, dict) else None
    if not isinstance(raw_defects, list):
        return {}
    return {
        str(defect.get("id") or "").strip(): defect
        for defect in raw_defects
        if isinstance(defect, dict) and str(defect.get("id") or "").strip()
    }


def _canonical_application(canonical: Any) -> tuple[Any, list[Any]]:
    """Flatten the canonical Lean application spine for tautology checks."""

    arguments: list[Any] = []
    current = canonical
    while isinstance(current, dict) and current.get("tag") == "app":
        arguments.append(current.get("arg"))
        current = current.get("fn")
    arguments.reverse()
    return current, arguments


def _review_item_has_trivial_support_conclusion(item: ReviewItem) -> bool:
    """Reject mechanically obvious tautologies as defect-support evidence."""

    manifest = item.lean_signature_manifest
    if not isinstance(manifest, dict) or manifest.get("schema") != 2:
        return True
    atoms = manifest.get("atoms")
    if not isinstance(atoms, list) or not atoms:
        return True
    conclusions = [
        atom for atom in atoms
        if isinstance(atom, dict) and str(atom.get("role") or "").strip() == "conclusion"
    ]
    if not conclusions:
        return True
    for atom in conclusions:
        canonical = atom.get("canonical")
        display = re.sub(r"\s+", "", str(atom.get("display") or ""))
        if display in {"True", "True.intro"}:
            return True
        head, arguments = _canonical_application(canonical)
        head_name = str(head.get("name") or "") if isinstance(head, dict) else ""
        if head_name == "True" and not arguments:
            return True
        if head_name in {"Eq", "Iff"} and len(arguments) >= 2:
            left = arguments[-2]
            right = arguments[-1]
            if left == right:
                return True
    return False


def defect_support_judgment_error(
    raw: Any,
    *,
    source_key: str,
    source_item: dict[str, Any],
    defect: dict[str, Any],
    support_declaration: str,
    row_item: ReviewItem,
) -> str:
    """Validate one exact semantic defect-to-Lean support judgment."""

    if not isinstance(raw, dict):
        return "judgment row is not an object"

    def required_string(key: str) -> str:
        value = raw.get(key)
        return value.strip() if isinstance(value, str) else ""

    if required_string("source_item") != source_key:
        return "source_item does not match the canonical source inventory key"
    source_statement = str(source_item.get("statement") or "")
    expected_source_digest = statement_digest(source_statement)
    if required_string("source_statement_sha256") != expected_source_digest:
        return "source statement digest is missing or stale"
    defect_id = str(defect.get("id") or "").strip()
    if required_string("defect_id") != defect_id:
        return "defect_id does not match the validated source-proof defect"
    expected_snapshot = source_proof_defect_snapshot(defect)
    if raw.get("source_defect") != expected_snapshot:
        return "source_defect snapshot is missing or stale"
    if required_string("source_defect_sha256") != source_proof_defect_digest(defect):
        return "source defect digest is missing or stale"
    if required_string("support_declaration") != support_declaration:
        return "support_declaration does not match the routed review row"

    lean_statement = str(row_item.lean_statement or "")
    if raw.get("lean_statement") != lean_statement:
        return "exact Lean statement is missing or stale"
    if required_string("lean_statement_sha256") != statement_digest(lean_statement):
        return "Lean statement digest is missing or stale"

    manifest = row_item.lean_signature_manifest
    if not isinstance(manifest, dict):
        return "Lean declaration manifest is unavailable"
    manifest_digest = str(manifest.get("sha256") or "").strip()
    if not manifest_digest or signature_manifest_digest(manifest) != manifest_digest:
        return "Lean declaration manifest has no valid canonical digest"
    if required_string("lean_signature_sha256") != manifest_digest:
        return "Lean declaration manifest digest is missing or stale"
    if _review_item_has_trivial_support_conclusion(row_item):
        return "Lean support conclusion is a trivial or reflexive tautology"

    judgment = required_string("judgment").lower()
    if judgment not in APPROVED_DEFECT_SUPPORT_JUDGMENTS:
        return "judgment is not a positive counterexample/refutation verdict"
    reason = required_string("reason")
    if len(reason) < 20 or NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(reason):
        return "judgment reason is missing, too short, or name-based"

    manifest_atoms = manifest.get("atoms")
    if not isinstance(manifest_atoms, list) or not manifest_atoms:
        return "Lean declaration manifest has no semantic atoms"
    manifest_index: dict[str, tuple[str, str]] = {}
    for atom in manifest_atoms:
        if not isinstance(atom, dict):
            return "Lean declaration manifest contains a malformed atom"
        ref = str(atom.get("ref") or "").strip()
        role = str(atom.get("role") or "").strip().lower()
        digest = signature_manifest_atom_digest(atom)
        if not ref or ref in manifest_index or role not in {
            "parameter", "assumption", "conclusion"
        } or not digest:
            return "Lean declaration manifest contains an invalid semantic atom"
        manifest_index[ref] = (role, digest)

    obligations = raw.get("lean_obligations")
    if not isinstance(obligations, list):
        return "missing lean_obligations list"
    obligation_refs: set[str] = set()
    permitted_relevance = {
        "parameter": {"witness_parameter", "source_model_parameter", "universal_parameter"},
        "assumption": {"source_model_condition", "proved_counterexample_fact"},
        "conclusion": {"counterexample_conclusion", "refutation_conclusion"},
    }
    expected_conclusion_relevance = (
        "counterexample_conclusion"
        if judgment == "valid_counterexample"
        else "refutation_conclusion"
    )
    for obligation in obligations:
        if not isinstance(obligation, dict):
            return "Lean obligation is not an object"
        ref = str(obligation.get("signature_ref") or "").strip()
        if ref not in manifest_index or ref in obligation_refs:
            return "Lean obligation references an unknown or duplicate signature atom"
        role, atom_digest = manifest_index[ref]
        if str(obligation.get("role") or "").strip().lower() != role:
            return f"Lean obligation `{ref}` has the wrong semantic role"
        if str(obligation.get("signature_atom_sha256") or "").strip() != atom_digest:
            return f"Lean obligation `{ref}` has a stale atom digest"
        relevance = str(obligation.get("defect_relevance") or "").strip().lower()
        if relevance not in permitted_relevance[role]:
            return f"Lean obligation `{ref}` has an invalid defect_relevance"
        if role == "conclusion" and relevance != expected_conclusion_relevance:
            return f"Lean conclusion `{ref}` does not match the positive judgment kind"
        explanation = str(obligation.get("semantic_explanation") or "").strip()
        if len(explanation) < 20 or NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(explanation):
            return f"Lean obligation `{ref}` lacks a substantive semantic explanation"
        obligation_refs.add(ref)
    if obligation_refs != set(manifest_index):
        return "Lean obligations do not exactly partition the declaration manifest"

    alignment = raw.get("obligation_alignment")
    if not isinstance(alignment, list) or not alignment:
        return "missing obligation_alignment list"
    aligned_refs: set[str] = set()
    has_claim_conclusion = False
    source_fields = set(SOURCE_PROOF_DEFECT_SNAPSHOT_FIELDS) - {
        "id", "defect_kind", "statement_impact", "resolution"
    }
    expected_relation = DEFECT_SUPPORT_JUDGMENT_RELATIONS[judgment]
    for entry in alignment:
        if not isinstance(entry, dict):
            return "obligation alignment entry is not an object"
        source_field = str(entry.get("source_defect_field") or "").strip()
        lean_ref = str(entry.get("lean_signature_ref") or "").strip()
        relation = str(entry.get("relation") or "").strip().lower()
        if source_field not in source_fields or lean_ref not in manifest_index:
            return "obligation alignment references an unknown defect field or Lean atom"
        role = manifest_index[lean_ref][0]
        if role == "conclusion":
            if relation != expected_relation:
                return "Lean conclusion alignment has the wrong defect relation"
            if source_field == "source_claim":
                has_claim_conclusion = True
        elif relation not in {"instantiates", "satisfies", "derived_from"}:
            return "Lean input alignment has an invalid defect relation"
        basis = str(entry.get("semantic_basis") or "").strip()
        witness = str(entry.get("witness_or_derivation") or "").strip()
        if (
            len(basis) < 20
            or len(witness) < 20
            or NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(basis)
            or NAME_ONLY_SEMANTIC_EVIDENCE_RE.search(witness)
        ):
            return "obligation alignment lacks substantive semantic evidence"
        aligned_refs.add(lean_ref)
    if aligned_refs != set(manifest_index):
        return "obligation alignment does not account for every Lean semantic atom"
    if not has_claim_conclusion:
        return "no Lean conclusion is aligned to the exact source defect claim"
    return ""


def _source_inventory_search_text(key: str, item: dict[str, Any]) -> str:
    """Return literal source-facing text used for policy classification.

    ``source_status`` is repository bookkeeping, not a source quotation. Its
    route/quarantine effects are handled by ``source_item_effective_route_policy``
    at the explicit policy branches below; free status wording cannot create or
    suppress a source theorem/claim classification through text matching.
    """

    del key  # Source-map keys and Lean aliases must not drive semantic routing.
    fields = [
        item.get("title"),
        item.get("statement"),
        item.get("source_location"),
        item.get("source_evidence"),
        item.get("source_note"),
    ]
    return " ".join(str(field or "") for field in fields)


def _source_inventory_item_requires_review_row(key: str, item: dict[str, Any]) -> bool:
    """Return whether source-visible material must be represented by dashboard row(s).

    The paper-coverage inventory is source first: a compact dashboard is useful,
    but it must not hide named source material from row-local LLM-as-judge review.
    Main-text definitions, examples, remarks, propositions, theorems, corollaries,
    and lemmas are required review targets. Appendix theorems/corollaries are also
    required. Appendix lemmas remain a judgment call unless a paper marks them as
    active targets elsewhere in the inventory.
    """

    if _source_inventory_item_is_catalogued_nonformal_observation(item):
        return False
    # An attempted exception is not an exception until every source-facing
    # condition above validates.  Otherwise a malformed pin or mislabeled
    # figure could disappear merely because its prose lacks a theorem keyword.
    if str(item.get("source_scope_classification") or "").strip():
        return True
    text = _source_inventory_search_text(key, item)
    if _source_inventory_item_is_named_algorithm_block(item):
        return True
    if _source_text_has_general_computational_claim(text):
        return True
    if _source_text_has_general_result_assertion(text):
        return True
    if _source_inventory_item_requires_proof_evidence(key, item):
        return True
    source_kind = str(item.get("source_kind") or "").strip().lower()
    # A statement-map example/remark is review-visible by default.  The only
    # computational-outcome exception is the validated source-facing lane
    # returned above; otherwise an arbitrary map classification could suppress
    # a claim without source evidence or a canonical artifact pin.
    if (
        _is_statement_map_source(item.get("source"))
        and source_kind in SOURCE_CATALOGUED_NONFORMAL_OBSERVATION_KINDS
    ):
        return True
    if source_item_effective_route_policy(item)[
        "external_support_only_vocabulary"
    ]:
        return False
    if source_kind in SOURCE_VOCABULARY_KINDS:
        return True
    lowered = text.lower()
    if any(reason in lowered for reason in SOURCE_NON_TARGET_REASONS):
        return False
    match = SOURCE_REVIEW_TARGET_RE.search(text)
    if not match:
        return _source_inventory_item_is_named_claim(key, item)
    label = match.group(1).lower()
    in_appendix = bool(SOURCE_APPENDIX_RE.search(text))
    if in_appendix and label == "lemma":
        return False
    return True


def _coverage_link_label(source_key: str, row_name: str) -> str:
    return f"{source_key} -> {row_name}"


def _coverage_review_row_signature_errors(
    source_key: str,
    rows: list[str],
    raw_pins: Any,
    row_items: dict[str, ReviewItem],
) -> list[str]:
    """Return failures for the elaborated-signature binding of one coverage link.

    A source-to-Lean coverage judgment is about the exact elaborated theorem
    type the reviewer inspected.  A declaration name or source route can find
    that theorem, but neither survives an unrecorded change to its normalized
    binders, premises, or conclusion.  Require an exact map from every linked
    row to the current canonical manifest digest.
    """

    if not rows:
        # The caller separately reports a direct coverage item with no rows.
        return []
    pins = _normalize_review_row_signature_pins(raw_pins)
    if pins is None:
        return [
            f"{source_key}: missing or malformed review_row_signature_sha256 map"
        ]

    errors: list[str] = []
    if len(set(rows)) != len(rows):
        errors.append(f"{source_key}: review_rows contains duplicate row names")
    if set(pins) != set(rows):
        errors.append(
            f"{source_key}: review_row_signature_sha256 keys do not exactly match review_rows"
        )

    for row_name in sorted(set(rows)):
        row_item = row_items.get(row_name)
        if row_item is None:
            # `invalid_row_links` gives the primary diagnosis for an absent row.
            continue
        manifest = row_item.lean_signature_manifest
        if not isinstance(manifest, dict):
            errors.append(
                f"{_coverage_link_label(source_key, row_name)}: current elaborated Lean signature manifest is unavailable"
            )
            continue
        manifest_digest = signature_manifest_digest(manifest)
        recorded_manifest_digest = str(manifest.get("sha256") or "").strip().lower()
        current_digest = str(row_item.lean_signature_sha256 or "").strip().lower()
        if (
            not manifest_digest
            or recorded_manifest_digest != manifest_digest
            or current_digest != manifest_digest
        ):
            errors.append(
                f"{_coverage_link_label(source_key, row_name)}: current elaborated normalized Lean signature digest is unavailable or invalid"
            )
            continue
        if pins.get(row_name) != manifest_digest:
            errors.append(
                f"{_coverage_link_label(source_key, row_name)}: review-row elaborated Lean signature digest is missing or stale"
            )
    return errors


def _review_item_statement_audit_target_sha256(row_item: ReviewItem) -> str:
    """Return the current exact paper target reviewed by one row.

    Most rows review their displayed paper statement. A component-routed row
    can instead review one exact clause of an aggregate definition. Accept the
    narrower target only when the statement loader already validated that
    unique route, the judgment is current, and all entry-local pins agree.
    """

    displayed_target = statement_digest(row_item.paper_statement)
    if row_item.is_assumption or row_item.llm_match_stale:
        return displayed_target
    component_target = str(
        row_item.llm_match_component_target_sha256 or ""
    ).strip().lower()
    recorded_target = str(
        row_item.llm_match_paper_statement_sha256 or ""
    ).strip().lower()
    route_targets = [
        str(route.get("source_statement_sha256") or "").strip().lower()
        for route in row_item.llm_match_source_routes or []
        if isinstance(route, Mapping)
        and str(route.get("route_kind") or "").strip().lower()
        == "source_component"
    ]
    if (
        SOURCE_ARTIFACT_SHA256_RE.fullmatch(component_target)
        and component_target == recorded_target
        and route_targets == [component_target]
    ):
        return component_target
    return displayed_target


def _row_statement_match_record(
    source_key: str,
    source_item: dict[str, Any],
    coverage: str,
    row_name: str,
    row_item: ReviewItem,
) -> dict[str, Any]:
    """Return a compact JSON record linking source coverage to row-local LLM audit."""

    _source_statement, source_statement_sha256 = _source_item_coverage_statement(
        source_item
    )
    row_paper_statement_sha256 = statement_digest(row_item.paper_statement)
    row_statement_audit_target_sha256 = (
        _review_item_statement_audit_target_sha256(row_item)
    )
    if row_item.is_assumption:
        correctness_lane = "assumption_provenance"
        judgment = str(row_item.llm_assumption_judgment or "").strip()
        resolution = ""
        stale = bool(row_item.llm_assumption_stale)
        source = str(row_item.llm_assumption_source or "")
        validator = str(row_item.llm_assumption_validator or "")
        validated_at = str(row_item.llm_assumption_validated_at or "")
        recorded_paper_statement_sha256 = str(
            row_item.llm_assumption_paper_statement_sha256 or ""
        ).strip()
        recorded_lean_statement_sha256 = str(
            row_item.llm_assumption_lean_statement_sha256 or ""
        ).strip()
        recorded_lean_signature_sha256 = ""
        recorded_tex_statement_sha256 = ""
    else:
        correctness_lane = "statement_match"
        judgment = str(row_item.llm_match_judgment or "").strip()
        resolution = _normalize_llm_match_resolution(row_item.llm_match_resolution)
        stale = bool(row_item.llm_match_stale)
        source = str(row_item.llm_match_source or "")
        validator = str(row_item.llm_match_validator or "")
        validated_at = str(row_item.llm_match_validated_at or "")
        recorded_paper_statement_sha256 = str(
            row_item.llm_match_paper_statement_sha256 or ""
        ).strip()
        recorded_lean_statement_sha256 = str(
            row_item.llm_match_lean_statement_sha256 or ""
        ).strip()
        recorded_lean_signature_sha256 = str(
            row_item.llm_match_lean_signature_sha256 or ""
        ).strip()
        recorded_tex_statement_sha256 = str(
            row_item.llm_match_tex_statement_sha256 or ""
        ).strip()
    assumption_judgment = str(row_item.llm_assumption_judgment or "").strip()
    return {
        "source_statement": source_key,
        "source_statement_sha256": source_statement_sha256,
        "review_row": row_name,
        "review_row_is_assumption": bool(row_item.is_assumption),
        "review_row_paper_statement_sha256": row_paper_statement_sha256,
        "review_row_statement_audit_target_sha256": (
            row_statement_audit_target_sha256
        ),
        "review_row_paper_statement_matches_source": bool(
            source_statement_sha256 and source_statement_sha256 == row_paper_statement_sha256
        ),
        "coverage": coverage,
        "row_correctness_lane": correctness_lane,
        "row_correctness_judgment": judgment,
        "row_correctness_resolution": resolution,
        "row_correctness_stale": stale,
        "row_correctness_source": source,
        "row_correctness_validator": validator,
        "row_correctness_validated_at": validated_at,
        "row_correctness_paper_statement_sha256": recorded_paper_statement_sha256,
        "row_correctness_lean_statement_sha256": recorded_lean_statement_sha256,
        "row_correctness_lean_signature_sha256": recorded_lean_signature_sha256,
        "review_row_lean_signature_sha256": row_item.lean_signature_sha256,
        "row_correctness_tex_statement_sha256": recorded_tex_statement_sha256,
        "row_correctness_matches_review_row_statement": bool(
            recorded_paper_statement_sha256
            and recorded_paper_statement_sha256
            == row_statement_audit_target_sha256
        ),
        "row_assumption_provenance_judgment": assumption_judgment,
        "row_assumption_provenance_stale": bool(row_item.llm_assumption_stale),
        "row_assumption_provenance_source": str(row_item.llm_assumption_source or ""),
        "row_assumption_provenance_validator": str(row_item.llm_assumption_validator or ""),
        "row_assumption_provenance_validated_at": str(row_item.llm_assumption_validated_at or ""),
        "row_statement_match_judgment": judgment,
        "row_statement_match_resolution": resolution,
        "row_statement_match_stale": stale,
        "row_statement_match_source": source,
        "row_statement_match_validator": validator,
        "row_statement_match_validated_at": validated_at,
        "row_statement_match_paper_statement_sha256": recorded_paper_statement_sha256,
        "row_statement_match_lean_statement_sha256": recorded_lean_statement_sha256,
        "row_statement_match_tex_statement_sha256": recorded_tex_statement_sha256,
    }


def _current_schema2_review_manifest_error(item: ReviewItem) -> str:
    manifest = item.lean_signature_manifest
    if not isinstance(manifest, dict) or manifest.get("schema") != 2:
        return "has no schema-2 elaborated manifest"
    digest = str(manifest.get("sha256") or "").strip().lower()
    if not digest or signature_manifest_digest(manifest) != digest:
        return "has no valid canonical schema-2 manifest digest"
    if str(item.lean_signature_sha256 or "").strip().lower() != digest:
        return "has no current review-row schema-2 manifest pin"
    proposition_graph = manifest.get("elaborated_proposition_graph")
    dependency_graph = manifest.get("semantic_dependency_graph")
    if (
        not isinstance(proposition_graph, dict)
        or proposition_graph.get("complete") is not True
        or not isinstance(dependency_graph, dict)
        or dependency_graph.get("complete") is not True
        or dependency_graph.get("realization_complete") is not True
    ):
        return "has no complete schema-2 proposition/dependency receipt"
    return ""


def _semantic_contract_spec_evidence_lean_error(
    specification: ReviewItem,
    evidence: ReviewItem,
) -> str:
    """Require the artifact-pinned Lean verdict for a Spec/proof contract.

    The schema-2 manifests below establish that both endpoints are current and
    of the right declaration kinds. Semantic equality and transparent
    dependency expansion are deliberately delegated to Lean Meta.
    """

    spec_manifest_error = _current_schema2_review_manifest_error(specification)
    if spec_manifest_error:
        return f"semantic-contract Spec {spec_manifest_error}"
    evidence_manifest_error = _current_schema2_review_manifest_error(evidence)
    if evidence_manifest_error:
        return f"semantic-contract evidence {evidence_manifest_error}"
    spec_manifest = specification.lean_signature_manifest
    evidence_manifest = evidence.lean_signature_manifest
    assert isinstance(spec_manifest, dict) and isinstance(evidence_manifest, dict)
    if (
        _review_item_declaration_kind(specification) != "definition"
        or spec_manifest.get("declaration_kind") != "definition"
        or spec_manifest.get("conclusion_mode") != "type_and_value"
    ):
        return "semantic-contract Spec is not a transparent definition"
    if (
        _review_item_declaration_kind(evidence) not in LEAN_PROOF_DECLARATION_KINDS
        or str(evidence.kind or "").strip().lower()
        not in LEAN_PROOF_DECLARATION_KINDS
        or evidence.is_assumption
        or evidence_manifest.get("declaration_kind") != "theorem"
        or evidence_manifest.get("conclusion_mode") != "type_only"
    ):
        return "semantic-contract evidence is not an actual proved theorem"
    if specification.semantic_contract_lean_transparency_verified is not True:
        return (
            "semantic-contract Spec has no current Lean-AST transitive "
            "transparency proof"
        )
    if specification.semantic_contract_lean_match_verified is not True:
        return (
            "Lean Meta did not establish the exact Spec/evidence semantic contract"
        )
    return ""


def _plain_spec_evidence_contract_declarations(
    source_item: dict[str, Any],
    *,
    semantic_contract_schema: object,
) -> tuple[str, str, str]:
    """Return the exact declaration roles from a valid plain proves contract."""

    if (
        not isinstance(semantic_contract_schema, int)
        or isinstance(semantic_contract_schema, bool)
        or semantic_contract_schema not in {1, 2}
    ):
        return "", "", "source map has no supported semantic-contract schema"
    contract = source_item.get("semantic_contract")
    if not isinstance(contract, dict):
        return "", "", "source item has no explicit Spec/evidence semantic contract"
    allowed_contract_fields = {
        "spec_declaration",
        "evidence_declaration",
        "evidence_mode",
        "semantic_shape",
    }
    spec_declaration = str(contract.get("spec_declaration") or "").strip()
    evidence_declaration = str(contract.get("evidence_declaration") or "").strip()
    if (
        set(contract) != allowed_contract_fields
        or not spec_declaration
        or not evidence_declaration
        or spec_declaration == evidence_declaration
        or str(contract.get("evidence_mode") or "").strip() != "proves"
        or str(contract.get("semantic_shape") or "").strip() != "plain"
    ):
        return "", "", "source item has a malformed proves-mode Spec/evidence contract"
    return spec_declaration, evidence_declaration, ""


def _semantic_contract_spec_coverage_proof_row(
    source_item: dict[str, Any],
    owner: ReviewItem,
    row_items: Mapping[str, ReviewItem],
    *,
    semantic_contract_schema: object,
) -> tuple[ReviewItem | None, str]:
    """Resolve proof credit for one explicit transparent-Spec coverage owner.

    The source item must bind exact qualified Spec/evidence declarations.  The
    owner keeps statement and coverage credit; the returned theorem keeps proof
    credit.  No declaration spelling is treated as mathematical evidence.
    """

    spec_declaration, evidence_declaration, contract_error = (
        _plain_spec_evidence_contract_declarations(
            source_item,
            semantic_contract_schema=semantic_contract_schema,
        )
    )
    if contract_error:
        return None, contract_error
    if str(owner.full_name or "").strip() != spec_declaration:
        return None, "coverage row is not the contract's exact qualified Spec owner"
    if (
        owner.is_proposition_spec is not True
        or owner.proposition_spec_role != "proof_routed"
        or owner.proposition_spec_proof
        not in {evidence_declaration, evidence_declaration.rsplit(".", 1)[-1]}
    ):
        return None, "coverage row is not explicitly configured as the contract Spec"

    direct_declarations = source_item_direct_coverage_declarations(source_item)
    if direct_declarations != [evidence_declaration]:
        return None, "contract evidence is not the sole explicit direct source endpoint"
    evidence_candidates = [
        item
        for item in row_items.values()
        if str(item.full_name or "").strip() == evidence_declaration
    ]
    if len(evidence_candidates) != 1:
        return None, "contract evidence does not resolve to one exact reviewed declaration"
    evidence = evidence_candidates[0]
    lean_contract_error = _semantic_contract_spec_evidence_lean_error(
        owner, evidence
    )
    if lean_contract_error:
        return None, lean_contract_error
    return evidence, ""


def _coverage_proof_evidence_row(
    source_item: dict[str, Any],
    owner: ReviewItem,
    row_items: Mapping[str, ReviewItem],
    *,
    semantic_contract_schema: object,
) -> tuple[ReviewItem | None, str]:
    """Return the theorem that supplies proof credit for a coverage owner."""

    if _review_item_declaration_kind(owner) in LEAN_PROOF_DECLARATION_KINDS:
        return owner, ""
    return _semantic_contract_spec_coverage_proof_row(
        source_item,
        owner,
        row_items,
        semantic_contract_schema=semantic_contract_schema,
    )


def _coverage_route_error(
    source_key: str,
    source_item: dict[str, Any],
    row_item: ReviewItem,
    *,
    row_items: Mapping[str, ReviewItem] | None = None,
    semantic_contract_schema: object = None,
    source_route_inventory: Mapping[str, dict[str, Any]] | None = None,
) -> str:
    """Check that a coverage link uses the row's exact semantic source route.

    A green row-local statement review establishes only the source statement it
    actually reviewed.  It cannot establish coverage for a different map item
    merely because both items were linked to the same Lean declaration.
    """

    if row_item.is_assumption:
        # Explicit assumptions use the separate provenance lane, whose source
        # digest is checked there rather than in theorem statement routes.
        return ""
    if _source_item_is_corrected_target(source_item):
        target_error = _source_item_corrected_target_metadata_error(source_item)
        if target_error:
            return target_error
    source_kind = str(source_item.get("source_kind") or "").strip().lower()
    routes = row_item.llm_match_source_routes or []
    route_inventory = source_route_inventory or {}
    definition_component_routes: list[dict[str, Any]] = []
    if source_kind in SOURCE_DEFINITION_SEMANTIC_KINDS:
        for route in routes:
            if not isinstance(route, dict):
                continue
            if (
                str(route.get("source_item") or "").strip() == source_key
                and str(route.get("route_kind") or "").strip().lower()
                == "source_component"
            ):
                return (
                    "a source-component route to the whole definition cannot "
                    "masquerade as whole-item coverage"
                )
            component = route_inventory.get(
                str(route.get("source_item") or "").strip()
            )
            if not isinstance(component, dict) or (
                component.get("source_definition_component") is not True
                or str(component.get("source_component_of") or "").strip()
                != source_key
            ):
                continue
            for field in (
                "source_statement_sha256",
                "source_location",
                "source_definition_partition_sha256",
                "source_definition_component_sha256",
            ):
                expected_field = (
                    component.get("statement_sha256")
                    if field == "source_statement_sha256"
                    else component.get(field)
                )
                recorded_value = str(route.get(field) or "").strip()
                expected_value = str(expected_field or "").strip()
                if field != "source_location":
                    recorded_value = recorded_value.lower()
                    expected_value = expected_value.lower()
                if recorded_value != expected_value:
                    return f"definition-component coverage route has a stale {field}"
            if (
                str(route.get("route_kind") or "").strip().lower()
                != "source_component"
                or str(route.get("semantic_relation") or "").strip().lower()
                != SOURCE_DEFINITION_COMPONENT_RELATION
            ):
                return "definition-component coverage route has an invalid route or relation"
            definition_component_routes.append(route)
    allowed_rows = source_item_direct_coverage_declarations(source_item)
    if allowed_rows:
        row_full_name = str(row_item.full_name or "").strip()
        is_direct_owner = any(
            row_full_name == declaration
            or ("." not in declaration and row_item.name == declaration)
            or (
                not row_full_name
                and row_item.name == declaration.rsplit(".", 1)[-1]
            )
            for declaration in allowed_rows
        )
        if not is_direct_owner and not definition_component_routes:
            _evidence, contract_error = _semantic_contract_spec_coverage_proof_row(
                source_item,
                row_item,
                row_items or {},
                semantic_contract_schema=semantic_contract_schema,
            )
            if contract_error:
                return (
                    "row is not an explicit direct source route or an exact "
                    f"semantic-contract Spec owner: {contract_error}"
                )
    _expected_statement, expected_digest = _source_item_coverage_statement(source_item)
    expected_location = _source_item_coverage_location(source_item)
    if not expected_digest or not expected_location:
        return "source item has incomplete canonical route metadata"
    route_policy = source_item_effective_route_policy(source_item)
    required_route_kinds = (
        {CORRECTED_TARGET_ROUTE_KIND}
        if _source_item_is_corrected_target(source_item)
        else (
            {"source_model_convention"}
            if route_policy["is_model_convention"]
            else (
                {"direct"}
                if source_kind in SOURCE_DEFINITION_SEMANTIC_KINDS
                else {"direct", "source_component"}
            )
        )
    )
    exact_routes = [
        route
        for route in routes
        if isinstance(route, dict)
        and str(route.get("source_statement_sha256") or "").strip()
        == expected_digest
        and str(route.get("source_location") or "").strip() == expected_location
    ]
    if definition_component_routes:
        return ""
    if not exact_routes:
        return "row has no exact source route for this coverage item"
    compatible_routes = [
        route
        for route in exact_routes
        if str(route.get("route_kind") or "").strip().lower()
        in required_route_kinds
    ]
    if not compatible_routes:
        return (
            "row route is not one of "
            + ", ".join(f"`{kind}`" for kind in sorted(required_route_kinds))
            + " for this coverage item"
        )
    if any(
        str(route.get("route_kind") or "").strip().lower() == "source_component"
        and str(route.get("semantic_relation") or "").strip().lower()
        not in SOURCE_COMPONENT_ROUTE_RELATIONS
        for route in compatible_routes
    ):
        return "source-component coverage route has an invalid semantic relation"
    return ""


def definition_joint_component_coverage_error(
    source_key: str,
    source_item: dict[str, Any],
    linked_rows: Iterable[ReviewItem],
    *,
    source_route_inventory: Mapping[str, dict[str, Any]],
) -> str:
    """Require exact-set coverage when a definition is split across rows."""

    if (
        str(source_item.get("source_kind") or "").strip().lower()
        not in SOURCE_DEFINITION_SEMANTIC_KINDS
    ):
        return ""
    _statement, parent_digest = _source_item_coverage_statement(source_item)
    parent_location = _source_item_coverage_location(source_item)
    direct_routes = []
    component_keys: list[str] = []
    for row in linked_rows:
        for route in row.llm_match_source_routes or []:
            if not isinstance(route, dict):
                continue
            route_kind = str(route.get("route_kind") or "").strip().lower()
            if (
                str(route.get("source_item") or "").strip() == source_key
                and str(route.get("source_statement_sha256") or "").strip()
                == parent_digest
                and str(route.get("source_location") or "").strip()
                == parent_location
                and route_kind
                in {
                    "direct",
                    CORRECTED_TARGET_ROUTE_KIND,
                }
            ):
                direct_routes.append(route)
            component_key = str(route.get("source_item") or "").strip()
            component = source_route_inventory.get(component_key)
            if (
                isinstance(component, dict)
                and component.get("source_definition_component") is True
                and str(component.get("source_component_of") or "").strip()
                == source_key
            ):
                component_keys.append(component_key)
    if direct_routes:
        if component_keys:
            return "definition coverage mixes a whole-item route with partition components"
        return ""
    if not component_keys:
        return ""

    partition, errors = source_definition_partition_record(source_item)
    if partition is None or errors:
        return "definition component coverage has no valid complete parent partition"
    expected_keys = {
        source_definition_component_route_key(
            source_key,
            component["semantic_clause_sha256"],
            component["source_anchor_sha256"],
        )
        for component in partition["components"]
    }
    seen_keys = set(component_keys)
    if len(component_keys) != len(seen_keys):
        return "definition component coverage duplicates a semantic clause"
    missing = expected_keys - seen_keys
    extra = seen_keys - expected_keys
    if missing or extra:
        return (
            "definition component coverage is not the exact complete partition "
            f"(missing={len(missing)}, extra={len(extra)})"
        )
    return ""


def _corrected_target_contract_spec_navigation_matches(
    source_item: dict[str, Any],
    primary_declaration: str,
    review_rows: list[str],
    source_inventory: object,
    paper_name: str,
    *,
    semantic_contract_schema: object,
) -> bool:
    """Perform only the cheap name-resolution part of Spec routing.

    The source-inventory precheck intentionally does not parse Lean rows.  It
    may therefore accept an exact, unambiguous contract Spec as a provisional
    corrected-target owner, but the full dashboard must still establish the
    schema-2 telescope match and proved theorem before closeout.
    """

    spec_declaration, evidence_declaration, contract_error = (
        _plain_spec_evidence_contract_declarations(
            source_item,
            semantic_contract_schema=semantic_contract_schema,
        )
    )
    if contract_error or evidence_declaration != primary_declaration:
        return False
    if review_rows == [spec_declaration]:
        return True
    if len(review_rows) != 1 or not isinstance(source_inventory, dict):
        return False
    prefix = f"{paper_name}.PaperInterface."
    short_name = spec_declaration.rsplit(".", 1)[-1]
    if (
        not spec_declaration.startswith(prefix)
        or not short_name
        or review_rows != [short_name]
    ):
        return False
    configured_specs: set[str] = set()
    for candidate in source_inventory.values():
        if not isinstance(candidate, dict):
            continue
        candidate_spec, _candidate_evidence, candidate_error = (
            _plain_spec_evidence_contract_declarations(
                candidate,
                semantic_contract_schema=semantic_contract_schema,
            )
        )
        if (
            not candidate_error
            and candidate_spec.startswith(prefix)
            and candidate_spec.rsplit(".", 1)[-1] == short_name
        ):
            configured_specs.add(candidate_spec)
    return configured_specs == {spec_declaration}


def _corrected_target_coverage_error(
    source_item: dict[str, Any],
    coverage_item: dict[str, Any],
    coverage: str,
    *,
    source_inventory: dict[str, dict[str, Any]] | None = None,
    paper_name: str = "",
    row_items: Mapping[str, ReviewItem] | None = None,
    semantic_contract_schema: object = None,
) -> str:
    """Validate the source-side pins required for corrected-target coverage.

    The coverage verdict is intentionally distinct from ordinary ``covered``:
    it credits only the approved target and permanently records that the
    archival paper statement was not established by this Lean result.
    """

    is_corrected = _source_item_is_corrected_target(source_item)
    if not is_corrected:
        if coverage == CORRECTED_TARGET_COVERAGE:
            return "covered_corrected_target names a source item without corrected-target status"
        return ""
    if coverage != CORRECTED_TARGET_COVERAGE:
        return "corrected_source_statement must use coverage `covered_corrected_target`, never ordinary covered"
    target_error = _source_item_corrected_target_metadata_error(source_item)
    if target_error:
        return target_error
    target = _source_item_corrected_target(source_item)
    assert target is not None
    primary_declaration = _corrected_target_primary_declaration(source_item)
    assert primary_declaration is not None
    expected_statement, expected_statement_digest = _source_item_coverage_statement(
        source_item
    )
    del expected_statement
    if str(coverage_item.get("target_kind") or "").strip().lower() != CORRECTED_TARGET_ROUTE_KIND:
        return "covered_corrected_target must record target_kind approved_corrected_target"
    review_rows = _normalize_string_list(coverage_item.get("review_rows"))
    direct_owner_matches = _corrected_target_coverage_rows_match_primary(
        primary_declaration,
        review_rows,
        source_inventory,
        paper_name,
    )
    contract_spec_matches = False
    if not direct_owner_matches and row_items is not None and len(review_rows) == 1:
        owner = row_items.get(review_rows[0])
        if owner is not None:
            evidence, contract_error = _semantic_contract_spec_coverage_proof_row(
                source_item,
                owner,
                row_items,
                semantic_contract_schema=semantic_contract_schema,
            )
            contract_spec_matches = bool(
                not contract_error
                and evidence is not None
                and str(evidence.full_name or "").strip() == primary_declaration
            )
    elif not direct_owner_matches:
        contract_spec_matches = _corrected_target_contract_spec_navigation_matches(
            source_item,
            primary_declaration,
            review_rows,
            source_inventory,
            paper_name,
            semantic_contract_schema=semantic_contract_schema,
        )
    if not direct_owner_matches and not contract_spec_matches:
        return (
            "covered_corrected_target must link exactly the sole corrected-target "
            "endpoint in lean_declarations or its exact contract-backed transparent "
            "Spec; aliases and support rows cannot carry target coverage"
        )
    if str(coverage_item.get("statement_sha256") or "").strip().lower() != expected_statement_digest:
        return "covered_corrected_target has a stale corrected target statement digest"
    if str(coverage_item.get("archival_statement_sha256") or "").strip().lower() != str(
        source_item.get("statement_sha256") or ""
    ).strip().lower():
        return "covered_corrected_target has a stale archival statement digest"
    if str(coverage_item.get("corrected_target_sha256") or "").strip().lower() != corrected_target_digest(target):
        return "covered_corrected_target has a stale corrected-target record digest"
    if _normalize_string_list(coverage_item.get("governing_defect_ids")) != _normalize_string_list(
        target.get("governing_defect_ids")
    ):
        return "covered_corrected_target lacks the exact governing source-statement defect ids"
    if coverage_item.get("archival_equivalence_claimed") is not False:
        return "covered_corrected_target must set archival_equivalence_claimed to false"
    return ""


def paper_coverage_audit_summary(folder: Path, items: list[ReviewItem]) -> dict[str, Any]:
    """Summarize source-paper statement coverage by the review dashboard surface."""

    full_inventory, inventory, source_coverage_mode, source_coverage_mode_error = (
        paper_coverage_inventory(folder)
    )
    statement_map_path = folder / PAPER_STATEMENT_MAP_FILE
    statement_map_payload = paper_statement_map_payload(folder)
    deep_source_coverage_attestation = deep_source_coverage_attestation_error(
        statement_map_payload, source_coverage_mode
    )
    inventory_kind = str(statement_map_payload.get("source_inventory_kind") or "").strip()
    inventory_source_curated = statement_map_payload.get("source_curated") is True
    inventory_is_scaffold = (
        inventory_kind in PAPER_COVERAGE_SCAFFOLD_KINDS
        or "dashboard_seeded" in inventory_kind
        or statement_map_payload.get("source_curated") is False
    )
    has_explicit_inventory = bool(inventory) and any(
        _is_statement_map_source(item.get("source"))
        for item in inventory.values()
    )
    inventory_hash = paper_coverage_inventory_digest(
        inventory,
        mode=source_coverage_mode,
        statement_map_payload=statement_map_payload,
    )
    full_inventory_hash = paper_statement_inventory_digest(full_inventory)
    surface_hash = review_surface_digest(items)
    audit = load_llm_paper_coverage_audit(folder)
    audit_items = audit.get("items") if isinstance(audit.get("items"), dict) else {}
    coverage_item_bindings, ambiguous_semantic_item_bindings = (
        _semantic_coverage_item_bindings(
            inventory, audit_items, source_coverage_mode
        )
    )
    bound_audit_items = {
        source_key: audit_items[audit_key]
        for source_key, audit_key in coverage_item_bindings.items()
        if isinstance(audit_items.get(audit_key), dict)
    }
    audit_required = paper_coverage_audit_required(folder, inventory)
    mode_migration_error = source_coverage_mode_migration_error(
        statement_map_payload, require_explicit=audit_required
    )
    raw_source_map_errors = paper_source_map_structural_errors(folder)
    source_presentation_classification_errors = sorted(
        set(
            raw_source_map_errors
            if statement_map_payload
            else [
                f"{key}: {error}"
                for key, item in full_inventory.items()
                for error in source_item_scope_classification_errors(item)
            ]
        )
    )
    unresolved_statement_map = (
        audit_required
        and _dashboard_is_file(statement_map_path)
        and not has_explicit_inventory
    )
    row_names = {item.name for item in items}

    missing_inventory = audit_required and not has_explicit_inventory
    missing_required = audit_required and not audit_items
    inventory_missing_source_url = sorted(
        key
        for key, item in inventory.items()
        if _is_statement_map_source(item.get("source"))
        and not str(item.get("source_url") or "").strip()
    )
    inventory_missing_source_provenance = sorted(
        key
        for key, item in inventory.items()
        if _is_statement_map_source(item.get("source"))
        and not (
            str(item.get("source_location") or "").strip()
            or str(item.get("source_note") or "").strip()
            or str(item.get("source_status") or "").strip()
        )
    )
    inventory_unknown_source_kind = sorted(
        key
        for key, item in inventory.items()
        if _is_statement_map_source(item.get("source"))
        and str(item.get("source_kind") or "").strip()
        and str(item.get("source_kind") or "").strip().lower()
        not in SOURCE_INVENTORY_KINDS
    )
    source_scope_classification_errors = (
        _source_scope_classification_errors(inventory, bound_audit_items)
        if source_coverage_mode == DEEP_PAPER_WITH_ALL_PROSE_CLAIMS
        else []
    )
    user_approved_scope_exclusion_errors = _user_approved_scope_exclusion_errors(
        inventory, bound_audit_items
    )
    source_anchor_evidence_errors = _scoped_source_anchor_evidence_errors(folder)
    source_named_result_inventory_errors = _source_named_result_inventory_errors(
        folder
    )
    missing_coverage = sorted(key for key in inventory if key not in bound_audit_items)
    extra_coverage = sorted(
        key
        for key in audit_items
        if key not in full_inventory and key not in set(coverage_item_bindings.values())
    )
    out_of_mode_coverage = sorted(
        key for key in audit_items if key in full_inventory and key not in inventory
    )
    missing_statement_digest = sorted(
        key
        for key, item in bound_audit_items.items()
        if not str(item.get("statement_sha256") or "").strip()
    )
    stale_statement = sorted(
        key
        for key, item in bound_audit_items.items()
        if str(item.get("statement_sha256") or "").strip()
        and str(item.get("statement_sha256") or "").strip()
        != _source_item_coverage_statement(inventory[key])[1]
    )
    invalid_row_links = sorted(
        {
            row
            for item in bound_audit_items.values()
            for row in _normalize_string_list(item.get("review_rows"))
            if row not in row_names
        }
    )
    recorded_inventory_hash = str(audit.get("paper_statement_inventory_sha256") or "").strip()
    recorded_source_coverage_mode = str(
        audit.get("source_coverage_mode") or ""
    ).strip()
    source_coverage_mode_mismatch = bool(
        recorded_source_coverage_mode
        and not source_coverage_modes_compatible(
            recorded_source_coverage_mode, source_coverage_mode
        )
    )
    recorded_surface_hash = str(audit.get("review_surface_sha256") or "").strip()
    aggregate_inventory_current = recorded_inventory_hash in {
        inventory_hash,
        # A legacy full-inventory sidecar can still supply current judgments
        # for the ordinary subset when its full source inventory is unchanged.
        full_inventory_hash,
    }
    source_artifact_current = _coverage_audit_source_artifact_is_current(
        audit, statement_map_payload
    )
    source_artifact_identity_declared = _source_artifact_identity_is_declared(
        statement_map_payload
    )
    source_artifact_identity_recorded = _coverage_audit_records_source_artifact_identity(
        audit
    )
    stale_inventory = bool(audit_items and not aggregate_inventory_current)
    stale_source_items = sorted(
        key
        for key, item in bound_audit_items.items()
        if _coverage_item_has_current_source_digest_schema(item)
        and not _coverage_item_source_digest_is_current(
            item, inventory[key], source_coverage_mode
        )
    )
    # Keep per-item semantic reuse inexpensive without trusting a locator that
    # changed beneath the same source semantic digest. This byte check is
    # source-only and therefore far cheaper than another Lean extraction or
    # LLM review.
    semantic_reuse_anchor_errors = _semantic_reuse_source_anchor_errors(
        folder,
        [
            key
            for key, item in bound_audit_items.items()
            if _coverage_item_has_current_source_digest_schema(item)
            and _coverage_item_source_digest_is_current(
                item, inventory[key], source_coverage_mode
            )
        ],
    )
    unverified_reused_source_items = sorted(semantic_reuse_anchor_errors)
    legacy_unpinned_items = sorted(
        key
        for key, item in bound_audit_items.items()
        if not _coverage_item_has_current_source_digest_schema(item)
        and (
            not aggregate_inventory_current
            or (
                source_artifact_identity_declared
                and source_artifact_identity_recorded
                and not source_artifact_current
            )
        )
    )
    stale_surface = bool(audit_items and recorded_surface_hash and recorded_surface_hash != surface_hash)
    audit_kind = str(audit.get("audit_kind") or "").strip()
    audit_source_grounded = bool(audit.get("source_grounded") is True)
    audit_is_scaffold = bool(audit.get("seed_scaffold") is True) or audit_kind in PAPER_COVERAGE_SCAFFOLD_KINDS
    audit_prompt_version = str(audit.get("prompt_version") or "").strip()
    inventory_has_quarantined_defect = any(
        _source_inventory_item_is_quarantined_defect(item)
        for item in inventory.values()
    )
    audit_prompt_version_stale = bool(
        audit_prompt_version != REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION
        and not (
            audit_prompt_version == LEGACY_LLM_PAPER_COVERAGE_PROMPT_VERSION
            and not inventory_has_quarantined_defect
        )
    )
    audit_metadata_missing = bool(audit_required and audit_items and audit.get("metadata_missing"))
    missing_source_grounded_audit = bool(
        audit_required
        and audit_items
        and (
            audit_is_scaffold
            or audit_kind not in APPROVED_PAPER_COVERAGE_AUDIT_KINDS
            or not audit_source_grounded
            or audit_prompt_version_stale
            or audit_metadata_missing
        )
    )
    row_items = {item.name: item for item in items}
    current_rows_by_signature = _current_row_signature_index(row_items)
    effective_audit_items: dict[str, dict[str, Any]] = {}
    semantic_row_rebindings: list[str] = []
    for source_key, raw_item in bound_audit_items.items():
        rebound_item, changes, rebound = _semantic_rebound_coverage_item(
            raw_item, current_rows_by_signature
        )
        effective_audit_items[source_key] = rebound_item
        if rebound:
            semantic_row_rebindings.extend(
                f"{source_key}: {change}" for change in changes
            )
    # Re-evaluate row links after a unique signature-based route rebinding.
    # A name change alone is harmless; a missing/ambiguous/different signature
    # deliberately remains an invalid route below.
    invalid_row_links = sorted(
        {
            row
            for item in effective_audit_items.values()
            for row in _normalize_string_list(item.get("review_rows"))
            if row not in row_names
        }
    )
    require_source_routes = llm_statement_source_routes_required(folder)
    source_route_inventory = dict(full_inventory)
    if require_source_routes:
        source_route_inventory.update(paper_source_component_route_inventory(folder))
        source_route_inventory.update(
            paper_source_definition_component_route_inventory(folder)
        )
    validated_source_defects = _validated_source_proof_defects(folder)
    validated_source_defect_ids = set(validated_source_defects)
    quarantine_support_requested = any(
        key in inventory
        and _source_inventory_item_is_quarantined_defect(inventory[key])
        and str(item.get("coverage") or "").strip()
        in {"covered_by_support", "support_only"}
        for key, item in effective_audit_items.items()
    )
    defect_support_audit = load_llm_defect_support_audit(folder)
    defect_support_items = (
        defect_support_audit.get("items")
        if isinstance(defect_support_audit.get("items"), dict)
        else {}
    )
    defect_support_audit_metadata_error = ""
    if quarantine_support_requested:
        if not defect_support_audit:
            defect_support_audit_metadata_error = (
                "missing audit/defect_support_match_llm.json"
            )
        elif defect_support_audit.get("load_error"):
            defect_support_audit_metadata_error = str(
                defect_support_audit.get("load_error")
            )
        elif defect_support_audit.get("prompt_version_stale"):
            defect_support_audit_metadata_error = "defect-support prompt version is stale"
        elif defect_support_audit.get("audit_kind") not in APPROVED_DEFECT_SUPPORT_AUDIT_KINDS:
            defect_support_audit_metadata_error = "defect-support audit_kind is not semantic"
        elif defect_support_audit.get("source_grounded") is not True:
            defect_support_audit_metadata_error = "defect-support audit is not source-grounded"
        elif defect_support_audit.get("metadata_missing") or not str(
            defect_support_audit.get("validator_type") or ""
        ).strip():
            defect_support_audit_metadata_error = (
                "defect-support audit lacks validator, validator_type, or validated_at"
            )
        elif not defect_support_items:
            defect_support_audit_metadata_error = "defect-support audit has no judgments"

    valid_defect_support_pairs: set[tuple[str, str, str]] = set()
    seen_defect_support_pairs: set[tuple[str, str, str]] = set()
    defect_support_judgment_errors: list[str] = []
    if defect_support_audit_metadata_error:
        defect_support_judgment_errors.append(
            f"audit:{defect_support_audit_metadata_error}"
        )
    elif defect_support_items:
        for judgment_key, raw_judgment in defect_support_items.items():
            label = str(judgment_key or "").strip() or "<unnamed>"
            if not isinstance(raw_judgment, dict):
                defect_support_judgment_errors.append(
                    f"{label}:judgment row is not an object"
                )
                continue
            source_key = str(raw_judgment.get("source_item") or "").strip()
            defect_id = str(raw_judgment.get("defect_id") or "").strip()
            support_name = str(
                raw_judgment.get("support_declaration") or ""
            ).strip()
            pair = (source_key, defect_id, support_name)
            if pair in seen_defect_support_pairs:
                valid_defect_support_pairs.discard(pair)
                defect_support_judgment_errors.append(
                    f"{label}:duplicate source-item/defect/declaration judgment"
                )
                continue
            seen_defect_support_pairs.add(pair)
            source_item = inventory.get(source_key)
            defect = validated_source_defects.get(defect_id)
            row_item = row_items.get(support_name)
            if source_item is None or defect is None or row_item is None:
                defect_support_judgment_errors.append(
                    f"{label}:unknown source item, validated defect, or reviewed declaration"
                )
                continue
            error = defect_support_judgment_error(
                raw_judgment,
                source_key=source_key,
                source_item=source_item,
                defect=defect,
                support_declaration=support_name,
                row_item=row_item,
            )
            if error:
                defect_support_judgment_errors.append(f"{label}:{error}")
            else:
                valid_defect_support_pairs.add(pair)

    covered: list[str] = []
    corrected_target_covered: list[str] = []
    conditional_boundary: list[str] = []
    support_only: list[str] = []
    out_of_scope: list[str] = []
    partial: list[str] = []
    missing: list[str] = []
    uncertain: list[str] = []
    unknown: list[str] = []
    covered_without_rows: list[str] = []
    covered_without_reason: list[str] = []
    covered_with_seed_reason: list[str] = []
    covered_without_source_evidence: list[str] = []
    support_without_declarations: list[str] = []
    support_without_reason: list[str] = []
    support_without_source_evidence: list[str] = []
    out_of_scope_without_reason: list[str] = []
    out_of_scope_without_source_evidence: list[str] = []
    coverage_metadata_missing: list[str] = []
    coverage_route_mismatch: list[str] = []
    corrected_target_coverage_errors: list[str] = []
    coverage_row_signature_errors: list[str] = []
    row_statement_match_links: list[dict[str, Any]] = []
    row_statement_match_missing: list[str] = []
    row_statement_match_stale: list[str] = []
    row_statement_match_mismatch: list[str] = []
    row_statement_match_uncertain: list[str] = []
    row_statement_match_unknown: list[str] = []
    row_statement_match_conditional: list[str] = []
    row_statement_match_conditional_without_coverage_boundary: list[str] = []
    row_statement_match_missing_statement_digest: list[str] = []
    row_statement_match_wrong_statement_digest: list[str] = []
    row_assumption_provenance_missing: list[str] = []
    row_assumption_provenance_stale: list[str] = []
    row_assumption_provenance_mismatch: list[str] = []
    row_assumption_provenance_uncertain: list[str] = []
    row_assumption_provenance_unknown: list[str] = []
    row_assumption_provenance_conditional: list[str] = []
    row_assumption_provenance_conditional_without_coverage_boundary: list[str] = []
    result_covered_without_proof_rows: list[str] = []
    result_covered_only_by_definition_rows: list[str] = []
    result_matched_only_by_definition_rows: list[str] = []
    semantic_contract_spec_proof_links: list[str] = []
    quarantined_defect_support: list[str] = []
    invalid_quarantined_defect_support: list[str] = []
    quarantined_defect_direct_coverage: list[str] = []
    support_only_named_claims: list[str] = []
    support_only_required_source_items: list[str] = []
    user_approved_scope_exclusions: list[str] = []
    required_out_of_scope: list[str] = []
    for key, item in effective_audit_items.items():
        if item.get("metadata_missing"):
            coverage_metadata_missing.append(key)
        coverage = _normalize_paper_coverage_judgment(item.get("coverage"))
        rows = _normalize_string_list(item.get("review_rows"))
        corrected_target_error = _corrected_target_coverage_error(
            inventory[key],
            item,
            coverage,
            source_inventory=full_inventory,
            paper_name=folder.name,
            row_items=row_items,
            semantic_contract_schema=statement_map_payload.get(
                "semantic_contract_schema"
            ),
        )
        if corrected_target_error:
            corrected_target_coverage_errors.append(f"{key}: {corrected_target_error}")
        if coverage in {
            "covered",
            "covered_by_rows",
            "conditional_boundary",
            "covered_with_boundary",
            CORRECTED_TARGET_COVERAGE,
        }:
            if _source_inventory_item_is_quarantined_defect(inventory[key]):
                quarantined_defect_direct_coverage.append(key)
            elif coverage in {"conditional_boundary", "covered_with_boundary"}:
                conditional_boundary.append(key)
            elif coverage == CORRECTED_TARGET_COVERAGE and not corrected_target_error:
                corrected_target_covered.append(key)
            elif _source_item_is_corrected_target(inventory[key]):
                # A malformed ordinary verdict for a corrected item receives no
                # direct-coverage count, even before the aggregate error gate.
                pass
            else:
                covered.append(key)
            if not rows:
                covered_without_rows.append(key)
            coverage_row_signature_errors.extend(
                _coverage_review_row_signature_errors(
                    key,
                    rows,
                    item.get("review_row_signature_sha256"),
                    row_items,
                )
            )
            reason = str(item.get("reason") or "").strip()
            source_evidence = str(item.get("source_evidence") or "").strip()
            if not reason:
                covered_without_reason.append(key)
            if NAME_ONLY_SOURCE_COVERAGE_REASON_RE.search(reason):
                covered_with_seed_reason.append(key)
            if not source_evidence:
                covered_without_source_evidence.append(key)
            linked_row_items = [
                row_items[row_name]
                for row_name in rows
                if row_name in row_items
            ]
            proof_evidence_by_owner: dict[str, ReviewItem] = {}
            for owner in linked_row_items:
                evidence, _proof_evidence_error = _coverage_proof_evidence_row(
                    inventory[key],
                    owner,
                    row_items,
                    semantic_contract_schema=statement_map_payload.get(
                        "semantic_contract_schema"
                    ),
                )
                if evidence is None:
                    continue
                proof_evidence_by_owner[owner.name] = evidence
                if evidence is not owner:
                    semantic_contract_spec_proof_links.append(
                        f"{key}: {owner.name} -> {evidence.name}"
                    )
            if require_source_routes:
                for row_name in rows:
                    row_item = row_items.get(row_name)
                    if row_item is None:
                        continue
                    route_error = _coverage_route_error(
                        key,
                        inventory[key],
                        row_item,
                        row_items=row_items,
                        semantic_contract_schema=statement_map_payload.get(
                            "semantic_contract_schema"
                        ),
                        source_route_inventory=source_route_inventory,
                    )
                    if route_error:
                        coverage_route_mismatch.append(
                            f"{_coverage_link_label(key, row_name)}: {route_error}"
                        )
                joint_component_error = definition_joint_component_coverage_error(
                    key,
                    inventory[key],
                    linked_row_items,
                    source_route_inventory=source_route_inventory,
                )
                if joint_component_error:
                    coverage_route_mismatch.append(
                        f"{key}: {joint_component_error}"
                    )
            result_requires_proof = _source_inventory_item_requires_proof_evidence(
                key, inventory[key]
            )
            if (
                result_requires_proof
                and linked_row_items
                and not proof_evidence_by_owner
            ):
                result_covered_without_proof_rows.append(key)
                if all(
                    _review_item_declaration_kind(row_item)
                    in LEAN_SPECIFICATION_DECLARATION_KINDS
                    for row_item in linked_row_items
                ):
                    result_covered_only_by_definition_rows.append(key)
            matching_row_items = [
                row_item
                for row_item in linked_row_items
                if str(row_item.llm_match_judgment or "").strip() == "matches"
            ]
            if (
                result_requires_proof
                and matching_row_items
                and not any(
                    row_item.name in proof_evidence_by_owner
                    for row_item in matching_row_items
                )
                and all(
                    _review_item_declaration_kind(row_item)
                    in LEAN_SPECIFICATION_DECLARATION_KINDS
                    for row_item in matching_row_items
                )
            ):
                result_matched_only_by_definition_rows.append(key)
            for row_name in rows:
                row_item = row_items.get(row_name)
                if row_item is None:
                    continue
                link_label = _coverage_link_label(key, row_name)
                row_statement_match_links.append(
                    _row_statement_match_record(key, inventory[key], coverage, row_name, row_item)
                )
                # Source model conditions are audited in the assumption-provenance
                # lane.  Requiring a second theorem-statement equivalence for the
                # same explicit assumption both duplicates work and misclassifies
                # a condition as a proved paper conclusion.
                if row_item.is_assumption:
                    assumption_judgment = str(row_item.llm_assumption_judgment or "").strip()
                    if row_item.llm_assumption_stale:
                        row_assumption_provenance_stale.append(link_label)
                    if not assumption_judgment:
                        row_assumption_provenance_missing.append(link_label)
                    elif assumption_judgment in {
                        "paper_assumption",
                        "paper_condition",
                        "documented_additional_assumption",
                        "documented_caveat",
                    }:
                        pass
                    elif assumption_judgment == "partial_boundary":
                        row_assumption_provenance_conditional.append(link_label)
                        if coverage not in {"conditional_boundary", "covered_with_boundary"}:
                            row_assumption_provenance_conditional_without_coverage_boundary.append(link_label)
                    elif assumption_judgment == "not_paper_assumption":
                        row_assumption_provenance_mismatch.append(link_label)
                    elif assumption_judgment == "uncertain":
                        row_assumption_provenance_uncertain.append(link_label)
                    else:
                        row_assumption_provenance_unknown.append(link_label)
                    continue
                recorded_paper_digest = str(row_item.llm_match_paper_statement_sha256 or "").strip()
                row_paper_digest = statement_digest(row_item.paper_statement)
                row_audit_target_digest = (
                    _review_item_statement_audit_target_sha256(row_item)
                )
                if not recorded_paper_digest:
                    row_statement_match_missing_statement_digest.append(link_label)
                elif recorded_paper_digest != row_audit_target_digest:
                    row_statement_match_wrong_statement_digest.append(link_label)
                # A corrected-target coverage row can certify only the explicit
                # repaired statement. Its route may be pinned correctly while
                # its row-local review still examined archival wording.
                if _source_item_is_corrected_target(inventory[key]):
                    _target_statement, target_digest = _source_item_coverage_statement(
                        inventory[key]
                    )
                    if row_paper_digest != target_digest:
                        row_statement_match_mismatch.append(link_label)
                judgment = str(row_item.llm_match_judgment or "").strip()
                resolution = _normalize_llm_match_resolution(row_item.llm_match_resolution)
                if row_item.llm_match_stale:
                    row_statement_match_stale.append(link_label)
                if not judgment:
                    row_statement_match_missing.append(link_label)
                elif judgment == "matches":
                    if (
                        _source_item_is_corrected_target(inventory[key])
                        and resolution != CORRECTED_TARGET_MATCH_RESOLUTION
                    ):
                        row_statement_match_mismatch.append(link_label)
                elif judgment == "mismatch" and resolution == CONDITIONAL_BOUNDARY_RESOLUTION:
                    row_statement_match_conditional.append(link_label)
                    if coverage not in {"conditional_boundary", "covered_with_boundary"}:
                        row_statement_match_conditional_without_coverage_boundary.append(link_label)
                elif judgment == "mismatch":
                    row_statement_match_mismatch.append(link_label)
                elif judgment == "uncertain":
                    row_statement_match_uncertain.append(link_label)
                else:
                    row_statement_match_unknown.append(link_label)
        elif coverage == USER_APPROVED_SCOPE_EXCLUSION:
            # This is intentionally a distinct audit disposition.  The source
            # assertion remains in the inventory and is not relabelled as a
            # computational observation or non-claim; validation above ensures
            # its approval and pinned source evidence are complete.
            user_approved_scope_exclusions.append(key)
        elif coverage in {"out_of_scope", "not_a_paper_target", "not_a_theorem_statement"}:
            out_of_scope.append(key)
            reason = str(item.get("reason") or "").strip()
            source_evidence = str(item.get("source_evidence") or "").strip()
            if not reason:
                out_of_scope_without_reason.append(key)
            if not source_evidence:
                out_of_scope_without_source_evidence.append(key)
            if _source_inventory_item_requires_review_row(key, inventory[key]):
                required_out_of_scope.append(key)
        elif coverage in {"covered_by_support", "support_only"}:
            support_only.append(key)
            support_declarations = _normalize_string_list(item.get("support_declarations"))
            reason = str(item.get("reason") or "").strip()
            source_evidence = str(item.get("source_evidence") or "").strip()
            if not support_declarations:
                support_without_declarations.append(key)
            if not reason:
                support_without_reason.append(key)
            if not source_evidence:
                support_without_source_evidence.append(key)
            if _source_inventory_item_is_quarantined_defect(inventory[key]):
                configured_support = set(
                    _normalize_string_list(
                        inventory[key].get("support_lean_declarations")
                    )
                )
                defect_ids = _normalize_string_list(
                    inventory[key].get("source_defect_ids")
                )
                support_rows = [
                    row_items[name]
                    for name in support_declarations
                    if name in row_items
                ]
                defects_with_semantic_support = {
                    defect_id
                    for defect_id in defect_ids
                    if any(
                        (key, defect_id, support_name)
                        in valid_defect_support_pairs
                        for support_name in support_declarations
                    )
                }
                declarations_with_semantic_support = {
                    support_name
                    for support_name in support_declarations
                    if any(
                        (key, defect_id, support_name)
                        in valid_defect_support_pairs
                        for defect_id in defect_ids
                    )
                }
                valid_quarantine_support = bool(
                    defect_ids
                    and set(defect_ids).issubset(validated_source_defect_ids)
                    and support_declarations
                    and set(support_declarations).issubset(configured_support)
                    and len(support_rows) == len(support_declarations)
                    and all(
                        _review_item_declaration_kind(row_item)
                        in LEAN_PROOF_DECLARATION_KINDS
                        for row_item in support_rows
                    )
                    and defects_with_semantic_support == set(defect_ids)
                    and declarations_with_semantic_support
                    == set(support_declarations)
                )
                if valid_quarantine_support:
                    quarantined_defect_support.append(key)
                else:
                    invalid_quarantined_defect_support.append(key)
            else:
                if _source_inventory_item_requires_proof_evidence(key, inventory[key]):
                    support_only_named_claims.append(key)
                if _source_inventory_item_requires_review_row(key, inventory[key]):
                    support_only_required_source_items.append(key)
        elif coverage == "partially_covered":
            partial.append(key)
        elif coverage == "missing":
            missing.append(key)
        elif coverage in {"uncertain", "unknown", "needs_review", ""}:
            uncertain.append(key)
        else:
            unknown.append(key)

    semantic_contract_spec_proof_links = sorted(
        set(semantic_contract_spec_proof_links)
    )
    coverage_needs_attention = bool(
        source_coverage_mode_error
        or mode_migration_error
        or deep_source_coverage_attestation
        or source_presentation_classification_errors
        or ambiguous_semantic_item_bindings
        or source_named_result_inventory_errors
        or (
            audit_required
            and (
            missing_inventory
            or unresolved_statement_map
            or inventory_is_scaffold
            or missing_required
            or missing_source_grounded_audit
            or coverage_metadata_missing
            or coverage_route_mismatch
            or corrected_target_coverage_errors
            or coverage_row_signature_errors
            or inventory_missing_source_url
            or inventory_missing_source_provenance
            or inventory_unknown_source_kind
            or source_scope_classification_errors
            or user_approved_scope_exclusion_errors
            or source_anchor_evidence_errors
            or source_coverage_mode_mismatch
            or missing_coverage
            or missing_statement_digest
            or stale_statement
            # Aggregate source/dashboard digests are discovery signals.  They
            # do not reopen an unchanged source item whose own source digest
            # and every linked elaborated Lean signature remain current.
            or stale_source_items
            or unverified_reused_source_items
            or legacy_unpinned_items
            or invalid_row_links
            or partial
            or missing
            or uncertain
            or unknown
            or covered_without_rows
            or covered_without_reason
            or covered_with_seed_reason
            or covered_without_source_evidence
            or result_covered_without_proof_rows
            or result_matched_only_by_definition_rows
            or quarantined_defect_direct_coverage
            or support_without_declarations
            or support_without_reason
            or support_without_source_evidence
            or invalid_quarantined_defect_support
            or defect_support_judgment_errors
            or required_out_of_scope
            or out_of_scope_without_reason
            or out_of_scope_without_source_evidence
            or extra_coverage
            )
        )
    )
    source_to_lean_needs_attention = bool(
        coverage_needs_attention
        or support_only_named_claims
        or support_only_required_source_items
        or row_statement_match_missing
        or row_statement_match_stale
        or row_statement_match_mismatch
        or row_statement_match_uncertain
        or row_statement_match_unknown
        or row_statement_match_conditional_without_coverage_boundary
        or row_statement_match_missing_statement_digest
        or row_statement_match_wrong_statement_digest
        or row_assumption_provenance_missing
        or row_assumption_provenance_stale
        or row_assumption_provenance_mismatch
        or row_assumption_provenance_uncertain
        or row_assumption_provenance_unknown
        or row_assumption_provenance_conditional_without_coverage_boundary
        or coverage_route_mismatch
        or corrected_target_coverage_errors
        or coverage_row_signature_errors
        or result_covered_without_proof_rows
        or result_matched_only_by_definition_rows
        or quarantined_defect_direct_coverage
        or invalid_quarantined_defect_support
        or defect_support_judgment_errors
    )
    return {
        "source_coverage_mode": source_coverage_mode,
        "source_coverage_mode_error": source_coverage_mode_error,
        "source_coverage_mode_migration_error": mode_migration_error,
        "deep_source_coverage_attestation_error": deep_source_coverage_attestation,
        "full_inventory_count": len(full_inventory),
        "inventory_count": len(inventory),
        "has_statement_map_file": _dashboard_is_file(statement_map_path),
        "has_explicit_inventory": has_explicit_inventory,
        "inventory_kind": inventory_kind,
        "inventory_source_curated": inventory_source_curated,
        "inventory_is_scaffold": inventory_is_scaffold,
        "unresolved_statement_map": unresolved_statement_map,
        "covered_count": len(covered),
        "corrected_target_covered_count": len(corrected_target_covered),
        "conditional_boundary_count": len(conditional_boundary),
        "support_only_count": len(support_only),
        "quarantined_defect_support_count": len(quarantined_defect_support),
        "invalid_quarantined_defect_support_count": len(
            invalid_quarantined_defect_support
        ),
        "defect_support_judgment_error_count": len(
            defect_support_judgment_errors
        ),
        "quarantined_defect_direct_coverage_count": len(
            quarantined_defect_direct_coverage
        ),
        "user_approved_scope_exclusion_count": len(
            user_approved_scope_exclusions
        ),
        "user_approved_scope_exclusion_error_count": len(
            user_approved_scope_exclusion_errors
        ),
        "out_of_scope_count": len(out_of_scope),
        "partial_count": len(partial),
        "missing_count": len(missing),
        "uncertain_count": len(uncertain),
        "unknown_count": len(unknown),
        "audit_required": audit_required,
        "missing_inventory": missing_inventory,
        "missing_required": missing_required,
        "inventory_missing_source_url_count": len(inventory_missing_source_url),
        "inventory_missing_source_provenance_count": len(inventory_missing_source_provenance),
        "inventory_unknown_source_kind_count": len(inventory_unknown_source_kind),
        "source_scope_classification_error_count": len(
            source_scope_classification_errors
        ),
        "source_presentation_classification_error_count": len(
            source_presentation_classification_errors
        ),
        "source_map_structural_error_count": len(raw_source_map_errors),
        "semantic_item_rebinding_count": sum(
            source_key != audit_key
            for source_key, audit_key in coverage_item_bindings.items()
        ),
        "semantic_item_rebindings": [
            f"{source_key} <- {audit_key}"
            for source_key, audit_key in sorted(coverage_item_bindings.items())
            if source_key != audit_key
        ],
        "ambiguous_semantic_item_bindings": ambiguous_semantic_item_bindings,
        "semantic_row_rebinding_count": len(semantic_row_rebindings),
        "semantic_row_rebindings": sorted(semantic_row_rebindings),
        "source_anchor_evidence_error_count": len(source_anchor_evidence_errors),
        "source_named_result_inventory_error_count": len(
            source_named_result_inventory_errors
        ),
        "missing_coverage_count": len(missing_coverage),
        "extra_coverage_count": len(extra_coverage),
        "out_of_mode_coverage_count": len(out_of_mode_coverage),
        "missing_statement_digest_count": len(missing_statement_digest),
        "stale_statement_count": len(stale_statement),
        "stale_source_item_count": len(stale_source_items),
        "unverified_reused_source_item_count": len(
            unverified_reused_source_items
        ),
        "legacy_unpinned_item_count": len(legacy_unpinned_items),
        "invalid_row_link_count": len(invalid_row_links),
        "covered_without_rows_count": len(covered_without_rows),
        "covered_without_reason_count": len(covered_without_reason),
        "covered_with_seed_reason_count": len(covered_with_seed_reason),
        "covered_without_source_evidence_count": len(covered_without_source_evidence),
        "result_covered_without_proof_row_count": len(result_covered_without_proof_rows),
        "result_covered_only_by_definition_row_count": len(
            result_covered_only_by_definition_rows
        ),
        "result_matched_only_by_definition_row_count": len(
            result_matched_only_by_definition_rows
        ),
        "semantic_contract_spec_proof_link_count": len(
            semantic_contract_spec_proof_links
        ),
        "support_without_declarations_count": len(support_without_declarations),
        "support_without_reason_count": len(support_without_reason),
        "support_without_source_evidence_count": len(support_without_source_evidence),
        "support_only_named_claim_count": len(support_only_named_claims),
        "support_only_required_source_item_count": len(support_only_required_source_items),
        "required_out_of_scope_count": len(required_out_of_scope),
        "out_of_scope_without_reason_count": len(out_of_scope_without_reason),
        "out_of_scope_without_source_evidence_count": len(out_of_scope_without_source_evidence),
        "row_statement_match_link_count": len(row_statement_match_links),
        "row_statement_match_missing_count": len(row_statement_match_missing),
        "row_statement_match_stale_count": len(row_statement_match_stale),
        "row_statement_match_mismatch_count": len(row_statement_match_mismatch),
        "row_statement_match_uncertain_count": len(row_statement_match_uncertain),
        "row_statement_match_unknown_count": len(row_statement_match_unknown),
        "row_statement_match_conditional_count": len(row_statement_match_conditional),
        "row_statement_match_conditional_without_coverage_boundary_count": len(
            row_statement_match_conditional_without_coverage_boundary
        ),
        "row_statement_match_missing_statement_digest_count": len(row_statement_match_missing_statement_digest),
        "row_statement_match_wrong_statement_digest_count": len(row_statement_match_wrong_statement_digest),
        "row_assumption_provenance_missing_count": len(row_assumption_provenance_missing),
        "row_assumption_provenance_stale_count": len(row_assumption_provenance_stale),
        "row_assumption_provenance_mismatch_count": len(row_assumption_provenance_mismatch),
        "row_assumption_provenance_uncertain_count": len(row_assumption_provenance_uncertain),
        "row_assumption_provenance_unknown_count": len(row_assumption_provenance_unknown),
        "row_assumption_provenance_conditional_count": len(row_assumption_provenance_conditional),
        "row_assumption_provenance_conditional_without_coverage_boundary_count": len(
            row_assumption_provenance_conditional_without_coverage_boundary
        ),
        "stale_inventory": stale_inventory,
        "stale_surface": stale_surface,
        "recorded_source_coverage_mode": recorded_source_coverage_mode,
        "source_coverage_mode_mismatch": source_coverage_mode_mismatch,
        "source_artifact_current": source_artifact_current,
        "audit_kind": audit_kind,
        "audit_source_grounded": audit_source_grounded,
        "audit_is_scaffold": audit_is_scaffold,
        "prompt_version": str(audit.get("prompt_version") or "").strip(),
        "prompt_version_stale": audit_prompt_version_stale,
        "missing_source_grounded_audit": missing_source_grounded_audit,
        "audit_metadata_missing": audit_metadata_missing,
        "defect_support_audit_required": quarantine_support_requested,
        "defect_support_audit_source": str(
            defect_support_audit.get("source") or ""
        ),
        "defect_support_prompt_version": str(
            defect_support_audit.get("prompt_version") or ""
        ),
        "defect_support_prompt_version_stale": bool(
            defect_support_audit.get("prompt_version_stale")
        ),
        "defect_support_audit_metadata_error": defect_support_audit_metadata_error,
        "coverage_metadata_missing_count": len(coverage_metadata_missing),
        "coverage_route_mismatch_count": len(coverage_route_mismatch),
        "corrected_target_coverage_error_count": len(
            corrected_target_coverage_errors
        ),
        "coverage_row_signature_error_count": len(coverage_row_signature_errors),
        "missing_coverage": missing_coverage,
        "extra_coverage": extra_coverage,
        "out_of_mode_coverage": out_of_mode_coverage,
        "conditional_boundary": conditional_boundary,
        "corrected_target_covered": corrected_target_covered,
        "support_only": support_only,
        "quarantined_defect_support": quarantined_defect_support,
        "invalid_quarantined_defect_support": invalid_quarantined_defect_support,
        "defect_support_judgment_errors": defect_support_judgment_errors,
        "quarantined_defect_direct_coverage": quarantined_defect_direct_coverage,
        "user_approved_scope_exclusions": user_approved_scope_exclusions,
        "inventory_missing_source_url": inventory_missing_source_url,
        "inventory_missing_source_provenance": inventory_missing_source_provenance,
        "inventory_unknown_source_kind": inventory_unknown_source_kind,
        "source_scope_classification_errors": source_scope_classification_errors,
        "source_presentation_classification_errors": source_presentation_classification_errors,
        "user_approved_scope_exclusion_errors": user_approved_scope_exclusion_errors,
        "source_anchor_evidence_errors": source_anchor_evidence_errors,
        "source_named_result_inventory_errors": source_named_result_inventory_errors,
        "missing_statement_digest": missing_statement_digest,
        "stale_statement": stale_statement,
        "stale_source_items": stale_source_items,
        "unverified_reused_source_items": unverified_reused_source_items,
        "semantic_reuse_source_anchor_errors": semantic_reuse_anchor_errors,
        "legacy_unpinned_items": legacy_unpinned_items,
        "invalid_row_links": invalid_row_links,
        "partial": partial,
        "missing": missing,
        "uncertain": uncertain,
        "unknown": unknown,
        "covered_without_rows": covered_without_rows,
        "covered_without_reason": covered_without_reason,
        "covered_with_seed_reason": covered_with_seed_reason,
        "covered_without_source_evidence": covered_without_source_evidence,
        "result_covered_without_proof_rows": result_covered_without_proof_rows,
        "result_covered_only_by_definition_rows": result_covered_only_by_definition_rows,
        "result_matched_only_by_definition_rows": result_matched_only_by_definition_rows,
        "semantic_contract_spec_proof_links": semantic_contract_spec_proof_links,
        "support_without_declarations": support_without_declarations,
        "support_without_reason": support_without_reason,
        "support_without_source_evidence": support_without_source_evidence,
        "support_only_named_claims": support_only_named_claims,
        "support_only_required_source_items": support_only_required_source_items,
        "required_out_of_scope": required_out_of_scope,
        "out_of_scope_without_reason": out_of_scope_without_reason,
        "out_of_scope_without_source_evidence": out_of_scope_without_source_evidence,
        "coverage_metadata_missing": coverage_metadata_missing,
        "coverage_route_mismatch": coverage_route_mismatch,
        "corrected_target_coverage_errors": corrected_target_coverage_errors,
        "coverage_row_signature_errors": coverage_row_signature_errors,
        "row_statement_match_links": row_statement_match_links,
        "row_statement_match_missing": row_statement_match_missing,
        "row_statement_match_stale": row_statement_match_stale,
        "row_statement_match_mismatch": row_statement_match_mismatch,
        "row_statement_match_uncertain": row_statement_match_uncertain,
        "row_statement_match_unknown": row_statement_match_unknown,
        "row_statement_match_conditional": row_statement_match_conditional,
        "row_statement_match_conditional_without_coverage_boundary": row_statement_match_conditional_without_coverage_boundary,
        "row_statement_match_missing_statement_digest": row_statement_match_missing_statement_digest,
        "row_statement_match_wrong_statement_digest": row_statement_match_wrong_statement_digest,
        "row_assumption_provenance_missing": row_assumption_provenance_missing,
        "row_assumption_provenance_stale": row_assumption_provenance_stale,
        "row_assumption_provenance_mismatch": row_assumption_provenance_mismatch,
        "row_assumption_provenance_uncertain": row_assumption_provenance_uncertain,
        "row_assumption_provenance_unknown": row_assumption_provenance_unknown,
        "row_assumption_provenance_conditional": row_assumption_provenance_conditional,
        "row_assumption_provenance_conditional_without_coverage_boundary": row_assumption_provenance_conditional_without_coverage_boundary,
        "source": str(audit.get("source") or "") if audit_items else "",
        "paper_statement_inventory_sha256": inventory_hash,
        "recorded_paper_statement_inventory_sha256": recorded_inventory_hash,
        "review_surface_sha256": surface_hash,
        "recorded_review_surface_sha256": recorded_surface_hash,
        "has_completed_audit": bool(audit_items),
        "needs_attention": coverage_needs_attention,
        "source_to_lean_needs_attention": source_to_lean_needs_attention,
    }


def assumption_surface_digest(items: list[ReviewItem]) -> str:
    """Return a stable digest of the paper-assumption review surface."""

    payload = [
        {
            "name": item.name,
            "kind": item.kind,
            "lean_statement": normalize_statement(item.lean_statement),
            "paper_statement": normalize_statement(item.paper_statement),
            "source_status": normalize_statement(item.source_status),
            "source_note": normalize_statement(item.source_note),
        }
        for item in sorted(items, key=lambda row: row.name)
        if item.is_assumption
    ]
    return hashlib.sha256(
        json.dumps(payload, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode(
            "utf-8"
        )
    ).hexdigest()


def assumption_provenance_audit_summary(folder: Path, items: list[ReviewItem]) -> dict[str, Any]:
    """Summarize whether explicit assumptions have source-assumption judgments."""

    configured_names = review_assumption_names(folder)
    assumption_items = [
        item
        for item in items
        if item.is_assumption or item.name in configured_names or is_assumption_item_name(item.name)
    ]
    item_names = {item.name for item in assumption_items}
    missing_rows = sorted(configured_names - item_names)
    unlisted_rows = sorted(
        item.name
        for item in assumption_items
        if is_assumption_item_name(item.name) and item.name not in configured_names
    )
    missing_judgment: list[str] = []
    stale_judgment: list[str] = []
    not_paper_assumption: list[str] = []
    uncertain: list[str] = []
    unknown: list[str] = []
    partial_boundary_premises: list[str] = []
    unresolved_premises: list[str] = []
    missing_source_location_premises: list[str] = []
    premise_judgment_count = 0
    paper_assumptions = 0
    paper_conditions = 0
    documented_additional_assumptions = 0
    documented_caveats = 0
    partial_boundaries = 0

    for item in assumption_items:
        judgment = str(item.llm_assumption_judgment or "").strip()
        if not judgment:
            missing_judgment.append(item.name)
            continue
        if item.llm_assumption_stale:
            stale_judgment.append(item.name)
        if judgment == "paper_assumption":
            paper_assumptions += 1
        elif judgment == "paper_condition":
            paper_conditions += 1
        elif judgment == "documented_additional_assumption":
            documented_additional_assumptions += 1
        elif judgment == "documented_caveat":
            documented_caveats += 1
        elif judgment == "partial_boundary":
            partial_boundaries += 1
        elif judgment == "not_paper_assumption":
            not_paper_assumption.append(item.name)
        elif judgment == "uncertain":
            uncertain.append(item.name)
        else:
            unknown.append(item.name)
        premise_judgments = item.llm_assumption_premise_judgments or {}
        if not isinstance(premise_judgments, dict):
            premise_judgments = {}
        for premise, raw_premise_judgment in sorted(premise_judgments.items()):
            premise_judgment = ""
            source_location = ""
            if isinstance(raw_premise_judgment, dict):
                premise_judgment = str(raw_premise_judgment.get("judgment") or "").strip()
                source_location = str(raw_premise_judgment.get("source_location") or "").strip()
            else:
                premise_judgment = _normalize_assumption_judgment(raw_premise_judgment)
            premise_judgment_count += 1
            label = f"{item.name}: {premise}"
            if premise_judgment == "partial_boundary":
                partial_boundary_premises.append(label)
                continue
            if premise_judgment not in APPROVED_ASSUMPTION_PREMISE_JUDGMENTS:
                unresolved_premises.append(f"{label} [{premise_judgment or 'missing'}]")
                continue
            if (
                premise_judgment in SOURCE_TEXT_ASSUMPTION_PREMISE_JUDGMENTS
                and not source_location
            ):
                missing_source_location_premises.append(label)

    needs_attention = bool(
        missing_rows
        or unlisted_rows
        or missing_judgment
        or stale_judgment
        or not_paper_assumption
        or uncertain
        or unknown
        or unresolved_premises
        or missing_source_location_premises
    )
    return {
        "row_count": len(assumption_items),
        "configured_count": len(configured_names),
        "paper_assumption_count": paper_assumptions,
        "paper_condition_count": paper_conditions,
        "documented_additional_assumption_count": documented_additional_assumptions,
        "documented_caveat_count": documented_caveats,
        "partial_boundary_count": partial_boundaries,
        "missing_rows_count": len(missing_rows),
        "unlisted_rows_count": len(unlisted_rows),
        "missing_judgment_count": len(missing_judgment),
        "stale_judgment_count": len(stale_judgment),
        "not_paper_assumption_count": len(not_paper_assumption),
        "uncertain_count": len(uncertain),
        "unknown_count": len(unknown),
        "premise_judgment_count": premise_judgment_count,
        "partial_boundary_premise_count": len(partial_boundary_premises),
        "unresolved_premise_count": len(unresolved_premises),
        "missing_source_location_premise_count": len(missing_source_location_premises),
        "missing_rows": missing_rows,
        "unlisted_rows": unlisted_rows,
        "missing_judgment": missing_judgment,
        "stale_judgment": stale_judgment,
        "not_paper_assumption": not_paper_assumption,
        "uncertain": uncertain,
        "unknown": unknown,
        "partial_boundary_premises": partial_boundary_premises,
        "unresolved_premises": unresolved_premises,
        "missing_source_location_premises": missing_source_location_premises,
        "has_completed_audit": bool(assumption_items) and not missing_judgment,
        "assumption_surface_sha256": assumption_surface_digest(assumption_items),
        "needs_attention": needs_attention,
        "has_warning": needs_attention,
    }


def describe_log_target(log_file: Path | None, paper: str | None = None) -> str:
    """User-visible label for where logs are persisted/read."""

    if log_file is not None:
        return str(log_file)
    if paper:
        try:
            return str(paper_review_log_file(paper))
        except ValueError:
            pass
    return "per-paper traces in each folder at <Paper>/.review_traces/paper_theorem_validations.jsonl"


def read_all_log_entries(
    paper_filter: str | None, log_file: Path | None
) -> list[dict[str, Any]]:
    """Collect review logs across selected papers or from an override log file."""

    if log_file is not None:
        entries = read_log_entries(log_file)
        if paper_filter:
            entries = [entry for entry in entries if entry.get("paper") == paper_filter]
        return entries

    entries: list[dict[str, Any]] = []
    for folder in iter_paper_folders(paper_filter):
        entries.extend(read_log_entries(paper_review_log_file(folder.name)))
    entries.sort(key=lambda row: row.get("timestamp", ""))
    return entries


def gather_paper_data(
    paper_filter: str | None = None,
    slice_filter: str | None = None,
    *,
    render_images: bool = True,
) -> list[dict[str, Any]]:
    papers = []
    for folder in iter_paper_folders(paper_filter):
        all_items = review_items_for_paper(
            folder,
            use_cache=True,
            render_images=render_images,
        )
        items = filter_items_by_slice(all_items, folder.name, slice_filter)
        assets = {}
        paper_pdf = find_paper_pdf(folder)
        if paper_pdf:
            assets["pdf"] = {
                "name": paper_pdf.name,
                "url": paper_asset_url(folder.name, paper_pdf),
            }
        paper_text = find_paper_text(folder)
        if paper_text:
            assets["text"] = {
                "name": paper_text.name,
                "url": paper_asset_url(folder.name, paper_text),
                "extension": paper_text.suffix.lower(),
            }
        papers.append(
            {
                "name": folder.name,
                "title": paper_title(folder),
                "items": [item.__dict__ for item in items],
                "slices": summarize_review_slices(all_items),
                "active_slice": slice_filter or "",
                "assets": assets,
                "surface_audit": review_surface_audit_summary(folder, all_items),
                "statement_audit": statement_translation_audit_summary(folder, all_items),
                "paper_coverage_audit": paper_coverage_audit_summary(folder, all_items),
                "assumption_audit": assumption_provenance_audit_summary(folder, all_items),
            }
        )
    return papers


def get_item_statements(paper: str, theorem: str) -> tuple[str, str, str, str, str]:
    """Lookup the current statements and source metadata for one theorem."""

    for paper_data in gather_paper_data(paper):
        if paper_data.get("name") != paper:
            continue
        for item in paper_data.get("items", []):
            if item.get("name") == theorem:
                return (
                    str(item.get("lean_statement") or ""),
                    str(item.get("paper_statement") or ""),
                    str(item.get("agent_statement") or ""),
                    str(item.get("source_status") or ""),
                    str(item.get("source_note") or ""),
                )
    return "", "", "", "", ""


def read_log_entries(log_file: Path, paper: str | None = None) -> list[dict[str, Any]]:
    if not log_file.exists():
        return []
    entries: list[dict[str, Any]] = []
    for raw in log_file.read_text(encoding="utf-8").splitlines():
        raw = raw.strip()
        if not raw:
            continue
        try:
            entry = json.loads(raw)
        except json.JSONDecodeError:
            continue
        if paper and entry.get("paper") != paper:
            continue
        entries.append(entry)
    entries.sort(key=lambda row: row.get("timestamp", ""))
    return entries


def item_digest(item: dict[str, Any], key: str) -> str:
    """Get current or fall-backed digest for an item key."""

    value = str(item.get(key) or "")
    return statement_digest(value)


def review_is_stale(
    entry: dict[str, Any], item: dict[str, Any]
) -> tuple[bool, bool, bool]:
    """Return `(lean_stale, paper_stale, source_stale)` for current item snapshot."""

    if not item:
        return False, False, False

    current_lean = item_digest(item, "lean_statement")
    current_paper = item_digest(item, "paper_statement")
    current_source = source_metadata_digest(
        str(item.get("source_status") or ""),
        str(item.get("source_note") or ""),
    )
    reviewed_lean = str(entry.get("lean_statement_sha256") or statement_digest(str(entry.get("lean_statement", "")))).strip()
    reviewed_paper = str(entry.get("paper_statement_sha256") or statement_digest(str(entry.get("paper_statement", "")))).strip()
    reviewed_source = str(entry.get("source_metadata_sha256") or "").strip()

    return (
        current_lean != reviewed_lean and bool(current_lean),
        current_paper != reviewed_paper and bool(current_paper),
        current_source != reviewed_source and bool(current_source),
    )


def _review_judgment(matches: Any) -> str:
    """Normalize a saved human review decision for validator exports."""

    if matches is True:
        return "matches"
    if matches is False:
        return "mismatch"
    if matches is None:
        return ""
    text = str(matches).strip().lower()
    if text in {"matches", "match", "true", "t", "yes", "y"}:
        return "matches"
    if text in {"mismatch", "does_not_match", "does not match", "false", "f", "no", "n"}:
        return "mismatch"
    if text in {"uncertain", "unknown", "unsure", "needs_review", "needs review"}:
        return "uncertain"
    return ""


def _review_matches_value(judgment: str) -> bool | None:
    """Return the backward-compatible matches field for a normalized judgment."""

    if judgment == "matches":
        return True
    if judgment == "mismatch":
        return False
    return None


def _validator_entry(
    validator: str,
    validator_type: str,
    validated_at: str,
    judgment: str,
    comment: str,
    source: str,
    stale: bool,
) -> dict[str, Any] | None:
    """Build a compact validator ledger entry for status exports."""

    name = str(validator or "").strip()
    if not name:
        return None
    return {
        "validator": name,
        "validator_type": str(validator_type or "").strip(),
        "validated_at": str(validated_at or "").strip(),
        "judgment": str(judgment or "").strip(),
        "comment": str(comment or "").strip(),
        "source": str(source or "").strip(),
        "stale": bool(stale),
    }


def _validator_names(validators: list[dict[str, Any]]) -> str:
    """Return stable unique validator labels for compact table columns."""

    labels: list[str] = []
    seen: set[str] = set()
    for entry in validators:
        name = str(entry.get("validator") or "").strip()
        if not name:
            continue
        validator_type = str(entry.get("validator_type") or "").strip()
        label = f"{name} ({validator_type})" if validator_type else name
        if label in seen:
            continue
        seen.add(label)
        labels.append(label)
    return ", ".join(labels)


def build_review_status(papers: list[dict[str, Any]], reviews: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Build compact theorem-level review status rows."""

    by_key: dict[tuple[str, str], list[dict[str, Any]]] = {}
    for entry in reviews:
        paper = str(entry.get("paper") or "").strip()
        theorem = str(entry.get("theorem") or "").strip()
        if not paper or not theorem:
            continue
        by_key.setdefault((paper, theorem), []).append(entry)

    rows: list[dict[str, Any]] = []
    for paper in papers:
        paper_name = paper["name"]
        for item in paper["items"]:
            theorem = item["name"]
            key = (paper_name, theorem)
            history = sorted(by_key.get(key, []), key=lambda row: row.get("timestamp", ""))
            latest = history[-1] if history else None
            stale_lean = False
            stale_paper = False
            stale_source = False
            if latest:
                stale_lean, stale_paper, stale_source = review_is_stale(latest, item)

            latest_user = latest.get("user") if latest else ""
            latest_ts = latest.get("timestamp") if latest else ""
            latest_judgment = _review_judgment(
                latest.get("judgment") if latest and "judgment" in latest else latest.get("matches") if latest else None
            )
            latest_matches = _review_matches_value(latest_judgment) if latest else None
            validators: list[dict[str, Any]] = []
            for entry in history:
                entry_stale_lean, entry_stale_paper, entry_stale_source = review_is_stale(entry, item)
                entry_judgment = _review_judgment(
                    entry.get("judgment") if "judgment" in entry else entry.get("matches")
                )
                validator_entry = _validator_entry(
                    validator=str(entry.get("user") or "").strip(),
                    validator_type="human",
                    validated_at=str(entry.get("timestamp") or "").strip(),
                    judgment=entry_judgment,
                    comment=str(entry.get("notes") or "").strip(),
                    source="paper_theorem_validations.jsonl",
                    stale=entry_stale_lean or entry_stale_paper or entry_stale_source,
                )
                if validator_entry is not None:
                    validators.append(validator_entry)
            if item.get("llm_match_judgment"):
                llm_comment = str(item.get("llm_match_reason") or "").strip()
                llm_resolution = str(item.get("llm_match_resolution") or "").strip()
                if llm_resolution:
                    resolution_bits = [f"resolution={llm_resolution}"]
                    boundary_names = _normalize_string_list(item.get("llm_match_boundary_names"))
                    conditional_premises = _normalize_string_list(
                        item.get("llm_match_conditional_premises")
                    )
                    resolution_reason = str(item.get("llm_match_resolution_reason") or "").strip()
                    if boundary_names:
                        resolution_bits.append("boundaries=" + ", ".join(boundary_names))
                    if conditional_premises:
                        resolution_bits.append(
                            "conditional_premises=" + ", ".join(conditional_premises)
                        )
                    if resolution_reason:
                        resolution_bits.append("reason=" + resolution_reason)
                    llm_comment = (
                        f"{llm_comment} [{'; '.join(resolution_bits)}]"
                        if llm_comment
                        else "; ".join(resolution_bits)
                    )
                validator_entry = _validator_entry(
                    validator=str(
                        item.get("llm_match_validator")
                        or item.get("llm_match_source")
                        or DEFAULT_LLM_STATEMENT_JUDGE_FILE
                    ).strip(),
                    validator_type=str(item.get("llm_match_validator_type") or "").strip(),
                    validated_at=str(item.get("llm_match_validated_at") or "").strip(),
                    judgment=str(item.get("llm_match_judgment") or "").strip(),
                    comment=llm_comment,
                    source=str(item.get("llm_match_source") or "").strip(),
                    stale=bool(item.get("llm_match_stale", False)),
                )
                if validator_entry is not None:
                    validators.append(validator_entry)
            if item.get("llm_assumption_judgment"):
                validator_entry = _validator_entry(
                    validator=str(
                        item.get("llm_assumption_validator")
                        or item.get("llm_assumption_source")
                        or DEFAULT_LLM_ASSUMPTION_JUDGE_FILE
                    ).strip(),
                    validator_type=str(item.get("llm_assumption_validator_type") or "").strip(),
                    validated_at=str(item.get("llm_assumption_validated_at") or "").strip(),
                    judgment=str(item.get("llm_assumption_judgment") or "").strip(),
                    comment=str(item.get("llm_assumption_reason") or "").strip(),
                    source=str(item.get("llm_assumption_source") or "").strip(),
                    stale=bool(item.get("llm_assumption_stale", False)),
                )
                if validator_entry is not None:
                    validators.append(validator_entry)
            rows.append(
                {
                    "paper": paper_name,
                    "theorem": theorem,
                    "kind": item["kind"],
                    "line_number": item.get("line_number", 0),
                    "slice_id": item.get("slice_id", "all"),
                    "slice_title": item.get("slice_title", "All statements"),
                    "has_review": latest is not None,
                    "review_count": len(history),
                    "needs_attention": latest is None
                    or stale_lean
                    or stale_paper
                    or stale_source
                    or latest_judgment in {"mismatch", "uncertain"},
                    "latest_user": latest_user,
                    "latest_timestamp": latest_ts,
                    "latest_judgment": latest_judgment,
                    "latest_matches": latest_matches,
                    "latest_notes": latest.get("notes") if latest else "",
                    "lean_stale": stale_lean,
                    "paper_stale": stale_paper,
                    "source_stale": stale_source,
                    "source_status": item.get("source_status", ""),
                    "source_note": item.get("source_note", ""),
                    "is_assumption": bool(item.get("is_assumption", False)),
                    "is_proposition_spec": bool(item.get("is_proposition_spec", False)),
                    "proposition_spec_role": item.get("proposition_spec_role", ""),
                    "proposition_spec_proof": item.get("proposition_spec_proof", ""),
                    "validators": validators,
                    "validator_names": _validator_names(validators),
                    "llm_match_judgment": item.get("llm_match_judgment", ""),
                    "llm_match_reason": item.get("llm_match_reason", ""),
                    "llm_match_stale": bool(item.get("llm_match_stale", False)),
                    "llm_match_source": item.get("llm_match_source", ""),
                    "llm_match_validator": item.get("llm_match_validator", ""),
                    "llm_match_validator_type": item.get("llm_match_validator_type", ""),
                    "llm_match_validated_at": item.get("llm_match_validated_at", ""),
                    "llm_match_resolution": item.get("llm_match_resolution", ""),
                    "llm_match_boundary_type": item.get("llm_match_boundary_type", ""),
                    "llm_match_boundary_names": _normalize_string_list(
                        item.get("llm_match_boundary_names")
                    ),
                    "llm_match_conditional_premises": _normalize_string_list(
                        item.get("llm_match_conditional_premises")
                    ),
                    "llm_match_resolution_reason": item.get("llm_match_resolution_reason", ""),
                    "llm_assumption_judgment": item.get("llm_assumption_judgment", ""),
                    "llm_assumption_reason": item.get("llm_assumption_reason", ""),
                    "llm_assumption_stale": bool(item.get("llm_assumption_stale", False)),
                    "llm_assumption_source": item.get("llm_assumption_source", ""),
                    "llm_assumption_validator": item.get("llm_assumption_validator", ""),
                    "llm_assumption_validator_type": item.get("llm_assumption_validator_type", ""),
                    "llm_assumption_validated_at": item.get("llm_assumption_validated_at", ""),
                    "llm_assumption_premise_judgments": item.get(
                        "llm_assumption_premise_judgments", {}
                    ),
                }
            )
    rows.sort(key=lambda row: (row["paper"], row["theorem"]))
    return rows


def filter_review_rows(
    rows: list[dict[str, Any]], user_filter: str | None = None, stale_only: bool = False
) -> list[dict[str, Any]]:
    if user_filter:
        user_filter = user_filter.strip()
    if not user_filter and not stale_only:
        return rows
    out: list[dict[str, Any]] = []
    for row in rows:
        if stale_only and not row.get("needs_attention"):
            continue
        if user_filter and row.get("latest_user") != user_filter:
            continue
        out.append(row)
    return out


def render_csv_summary(rows: list[dict[str, Any]]) -> str:
    header = [
        "paper",
        "slice",
        "theorem",
        "kind",
        "line_number",
        "has_review",
        "review_count",
        "needs_attention",
        "latest_user",
        "latest_timestamp",
        "latest_matches",
        "validators",
        "lean_stale",
        "paper_stale",
        "source_stale",
        "source_status",
        "source_note",
        "llm_match_judgment",
        "llm_match_resolution",
        "llm_match_stale",
    ]
    out = io.StringIO()
    writer = csv.writer(out)
    writer.writerow(header)
    for row in rows:
        writer.writerow(
            [
                row["paper"],
                row.get("slice_title", row.get("slice_id", "")),
                row["theorem"],
                row["kind"],
                str(row.get("line_number") or ""),
                "true" if row["has_review"] else "false",
                str(row["review_count"]),
                "true" if row["needs_attention"] else "false",
                row.get("latest_user", ""),
                row.get("latest_timestamp", ""),
                "true" if row.get("latest_matches") else "false",
                row.get("validator_names", ""),
                "true" if row.get("lean_stale") else "false",
                "true" if row.get("paper_stale") else "false",
                "true" if row.get("source_stale") else "false",
                row.get("source_status", ""),
                row.get("source_note", ""),
                row.get("llm_match_judgment", ""),
                row.get("llm_match_resolution", ""),
                "true" if row.get("llm_match_stale") else "false",
            ]
        )
    rendered = out.getvalue()
    out.close()
    return rendered


def _escape_md(value: Any) -> str:
    return str(value).replace("|", "\\|").replace("\n", "<br/>")


def render_markdown_summary(rows: list[dict[str, Any]]) -> str:
    lines = [
        "| Paper | Slice | Theorem | Kind | Line | Reviewed | Reviews | Needs attention | Latest | Latest timestamp | Matches | Validators | Lean stale | Paper stale | Source stale | Source status | Source note | LLM judgment | LLM resolution | LLM stale | Notes |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for row in rows:
        lines.append(
            "| " + " | ".join(
                [
                    _escape_md(row["paper"]),
                    _escape_md(row.get("slice_title") or row.get("slice_id") or ""),
                    _escape_md(row["theorem"]),
                    _escape_md(row["kind"]),
                    str(row.get("line_number") or ""),
                    "yes" if row["has_review"] else "no",
                    str(row["review_count"]),
                    "yes" if row["needs_attention"] else "no",
                    _escape_md(row.get("latest_user") or "—"),
                    _escape_md(row.get("latest_timestamp", "")),
                    "yes" if row.get("latest_matches") else "no",
                    _escape_md(row.get("validator_names", "")),
                    "yes" if row.get("lean_stale") else "no",
                    "yes" if row.get("paper_stale") else "no",
                    "yes" if row.get("source_stale") else "no",
                    _escape_md(row.get("source_status", "")),
                    _escape_md(row.get("source_note", "")),
                    _escape_md(row.get("llm_match_judgment", "")),
                    _escape_md(row.get("llm_match_resolution", "")),
                    "yes" if row.get("llm_match_stale") else "no",
                    _escape_md(row.get("latest_notes", "")),
                ]
            )
            + " |"
        )
    return "\n".join(lines) + "\n"


def _validator_report_label(entry: dict[str, Any]) -> str:
    name = str(entry.get("validator") or "").strip()
    if not name:
        return ""
    validator_type = str(entry.get("validator_type") or "").strip()
    judgment = str(entry.get("judgment") or "").strip()
    validated_at = str(entry.get("validated_at") or "").strip()
    stale = bool(entry.get("stale"))
    details: list[str] = []
    if validator_type:
        details.append(validator_type)
    if judgment:
        details.append(judgment)
    if validated_at:
        details.append(validated_at)
    if stale:
        details.append("stale")
    if not details:
        return name
    return f"{name} ({'; '.join(details)})"


def render_validator_markdown_summary(rows: list[dict[str, Any]]) -> str:
    """Render the compact validator table intended for final validation reports."""

    lines = [
        "| Paper-facing statement | Lean declaration | Validators | Validator comments |",
        "| --- | --- | --- | --- |",
    ]
    for row in rows:
        validators = row.get("validators") if isinstance(row.get("validators"), list) else []
        labels = [_validator_report_label(entry) for entry in validators if isinstance(entry, dict)]
        labels = [label for label in labels if label]
        comments: list[str] = []
        for entry in validators:
            if not isinstance(entry, dict):
                continue
            comment = str(entry.get("comment") or "").strip()
            if not comment:
                continue
            label = _validator_report_label(entry) or str(entry.get("validator") or "").strip()
            comments.append(f"{label}: {comment}" if label else comment)
        paper_item = f"{row.get('kind', '')} {row.get('theorem', '')}".strip()
        lines.append(
            "| " + " | ".join(
                [
                    _escape_md(paper_item),
                    _escape_md(f"`{row.get('theorem', '')}`" if row.get("theorem") else ""),
                    _escape_md("<br/>".join(labels) if labels else "None recorded"),
                    _escape_md("<br/>".join(comments) if comments else "None"),
                ]
            )
            + " |"
        )
    return "\n".join(lines) + "\n"


def status_totals(rows: list[dict[str, Any]]) -> dict[str, Any]:
    total = len(rows)
    reviewed = sum(1 for row in rows if row.get("has_review"))
    stale = sum(1 for row in rows if row.get("needs_attention"))
    lean_stale = sum(1 for row in rows if row.get("lean_stale"))
    paper_stale = sum(1 for row in rows if row.get("paper_stale"))
    source_stale = sum(1 for row in rows if row.get("source_stale"))
    no_review = total - reviewed
    return {
        "total_items": total,
        "reviewed_items": reviewed,
        "unreviewed_items": no_review,
        "needs_attention_items": stale,
        "lean_stale_items": lean_stale,
        "paper_stale_items": paper_stale,
        "source_stale_items": source_stale,
    }


def surface_audit_rows(papers: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Return paper-level review-surface audit rows for API/export/precheck use."""

    rows: list[dict[str, Any]] = []
    for paper in papers:
        audit = paper.get("surface_audit") or {}
        rows.append({"paper": paper.get("name", ""), **audit})
    return rows


def statement_audit_rows(papers: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Return paper-level statement-translation audit rows for API/export/precheck."""

    rows: list[dict[str, Any]] = []
    for paper in papers:
        audit = paper.get("statement_audit") or {}
        rows.append({"paper": paper.get("name", ""), **audit})
    return rows


def paper_coverage_audit_rows(papers: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Return paper-level source-statement coverage audit rows."""

    rows: list[dict[str, Any]] = []
    for paper in papers:
        audit = paper.get("paper_coverage_audit") or {}
        rows.append({"paper": paper.get("name", ""), **audit})
    return rows


def assumption_audit_rows(papers: list[dict[str, Any]]) -> list[dict[str, Any]]:
    """Return paper-level assumption-provenance audit rows."""

    rows: list[dict[str, Any]] = []
    for paper in papers:
        audit = paper.get("assumption_audit") or {}
        rows.append({"paper": paper.get("name", ""), **audit})
    return rows


def conditional_boundary_statement_premises(folder: Path) -> dict[str, list[str]]:
    """Return accepted visible extra Lean premises keyed by review row.

    The function name is retained for callers that consume the historical
    machine-level category. It does not accept a row with a missing source
    conclusion as a boundary.
    """

    out: dict[str, list[str]] = {}
    manifests = SIGNATURE_MANIFEST_CACHE.get(str(folder.resolve()), {})
    for name, judgment in load_llm_statement_judgments(folder, manifests).items():
        if not _is_conditional_boundary_judgment(judgment):
            continue
        premises = _normalize_string_list(judgment.get("conditional_premises"))
        if premises:
            out[name] = premises
    return out


def _default_hidden_premise_row(paper_name: str) -> dict[str, Any]:
    """Create the hidden-premise audit row shape used by CLI prechecks."""

    return {
        "paper": paper_name,
        "hidden_premise_count": 0,
        "hidden_premise_error_count": 0,
        "hidden_premise_warning_count": 0,
        "hidden_premise_samples": [],
        "accepted_conditional_premise_count": 0,
        "accepted_conditional_premise_samples": [],
        "needs_attention": False,
        "has_warning": False,
    }


FAST_SAVED_SOURCE_RECORD_IDENTITY_TIMEOUT_SECONDS = 45


def _fast_saved_source_record_identity(
    paper: str,
) -> tuple[dict[str, Any] | None, str]:
    """Read the source-record tool's narrow current-repository receipt.

    This intentionally delegates the source/configuration identity calculation
    to the source-record producer.  The producer checks the saved schema-10
    raw receipt and every Lean-owned repository source in its recorded loaded
    closure, but deliberately does not reread external ``.olean`` artifacts.
    It is therefore useful only for a responsive precheck; paper closeout
    keeps the stricter external-artifact and live-Lean validation path.
    """

    script = ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
    if not script.is_file():
        return None, "source-record fast-identity helper is unavailable"
    try:
        proc = subprocess.run(
            [
                sys.executable,
                str(script),
                "--root",
                str(ROOT),
                "--paper",
                paper,
                "--fast-saved-identity",
            ],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
            timeout=FAST_SAVED_SOURCE_RECORD_IDENTITY_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired:
        return None, "source-record fast-identity helper timed out"
    except OSError as exc:
        return None, "could not start source-record fast-identity helper: " + str(exc)
    try:
        payload = json.loads(proc.stdout)
    except json.JSONDecodeError:
        excerpt = " ".join((proc.stderr or proc.stdout or "").splitlines()[-3:])
        return None, "source-record fast-identity helper returned invalid JSON" + (
            ": " + excerpt if excerpt else ""
        )
    if not isinstance(payload, dict):
        return None, "source-record fast-identity helper returned a non-object payload"
    if proc.returncode != 0 or payload.get("current") is not True:
        reason = str(payload.get("reason") or "saved source-record receipt is not current")
        return payload, reason
    return payload, ""


def _fast_source_record_closure_paths(
    payload: Mapping[str, Any],
) -> tuple[set[Path], str]:
    """Return source paths from a saved Lean-owned closure without guessing imports."""

    closure = payload.get("lean_import_closure")
    sources = closure.get("sources") if isinstance(closure, Mapping) else None
    if not isinstance(sources, list):
        return set(), "saved source-record receipt has no Lean import-closure source list"
    paths: set[Path] = set()
    for source in sources:
        if not isinstance(source, Mapping):
            return set(), "saved source-record receipt has a malformed closure source"
        raw_path = str(source.get("path") or "").strip()
        if not raw_path:
            return set(), "saved source-record receipt has an unnamed closure source"
        candidate = (ROOT / raw_path).resolve()
        try:
            candidate.relative_to(ROOT)
        except ValueError:
            return set(), "saved source-record closure source escapes the repository"
        paths.add(candidate)
    return paths, ""


def _fast_source_record_unconfigured_support_scope(
    folder: Path,
    payload: Mapping[str, Any],
    closure_paths: set[Path],
) -> tuple[list[str], list[str], str]:
    """Separate active support debt from an unimported legacy support module.

    This is a graph decision, not a declaration-name convention.  A support
    declaration reported from a separate Assumptions source cannot be an
    active premise of the current review surface when that exact source is
    absent from Lean's loaded closure and is not the status-configured
    assumption source.  It remains reported as inactive legacy inventory.
    """

    rows = [
        str(value).strip()
        for value in payload.get("unconfigured_assumption_support_rows") or []
        if str(value).strip()
    ]
    if not rows:
        return [], [], ""
    raw_source = payload.get("review_assumption_source")
    raw_path = str(raw_source.get("path") or "").strip() if isinstance(raw_source, Mapping) else ""
    if not raw_path:
        return rows, [], "source-record support inventory has no source path"
    source_path = (ROOT / raw_path).resolve()
    try:
        source_path.relative_to(ROOT)
    except ValueError:
        return rows, [], "source-record support source escapes the repository"
    try:
        configured_source = assumption_source_file(folder).resolve()
    except (OSError, ValueError):
        return rows, [], "configured assumption source is unavailable"
    if source_path not in closure_paths and source_path != configured_source:
        return [], rows, ""
    return rows, [], ""


def fast_saved_source_record_assumption_precheck(
    paper: str | None, slice_filter: str | None = None
) -> dict[str, Any] | None:
    """Return a bounded semantic premise precheck, or ``None`` when ineligible.

    The route is intentionally narrow.  It is available only where the paper
    configures no explicit Assumptions.lean declarations and the whole paper
    is selected.  It validates a source-record receipt against exact current
    repository source/configuration inputs, checks current semantic judgment
    coverage, and reads current reachability from Lean's saved loaded-module
    closure.  It does not grant strict closeout credit.
    """

    if not paper or slice_filter:
        return None
    folder = ROOT / "papers" / paper
    if not folder.is_dir() or review_assumption_names(folder):
        return None

    result: dict[str, Any] = {
        "paper": paper,
        "scope": "repository sources/configuration only; strict closeout also revalidates external artifacts and live Lean",
        "needs_attention": False,
        "reasons": [],
        "required_judgment_count": 0,
        "current_judgment_count": 0,
        "inactive_legacy_support_rows": [],
        "reachable_auxiliary_rows": [],
        "inactive_assumption_sidecar_rows": [],
        "hidden_variable_premises": [],
    }
    identity, identity_error = _fast_saved_source_record_identity(paper)
    if identity_error:
        result["needs_attention"] = True
        result["reasons"].append(identity_error)
        return result
    assert identity is not None

    try:
        from scripts import audit_evidence_integrity as evidence
        from scripts import audit_repository
    except ModuleNotFoundError:  # Direct script execution.
        import audit_evidence_integrity as evidence  # type: ignore
        import audit_repository  # type: ignore
    except Exception as exc:  # noqa: BLE001 - an unavailable validator fails closed.
        result["needs_attention"] = True
        result["reasons"].append("could not load semantic premise validators: " + str(exc))
        return result

    status = _dashboard_json_payload(folder / DEFAULT_PAPER_STATUS_FILE)
    if not isinstance(status, dict):
        result["needs_attention"] = True
        result["reasons"].append("paper-local status metadata is unavailable")
        return result
    audit_path, audit_path_error = evidence.source_record_review_sidecar_path(
        folder,
        status,
        config_field="source_record_audit_file",
        default_basename="source_record_audit.json",
    )
    match_path, match_path_error = evidence.source_record_review_sidecar_path(
        folder,
        status,
        config_field="source_record_judgment_file",
        default_basename="source_record_match_llm.json",
    )
    if audit_path_error or match_path_error or audit_path is None or match_path is None:
        result["needs_attention"] = True
        result["reasons"].append(
            audit_path_error or match_path_error or "source-record sidecar path is unavailable"
        )
        return result
    canonical_audit_path = folder / PAPER_AUDIT_DIR / "source_record_audit.json"
    if audit_path.resolve() != canonical_audit_path.resolve():
        result["needs_attention"] = True
        result["reasons"].append(
            "fast precheck only accepts the canonical source-record raw sidecar"
        )
        return result
    raw = _dashboard_json_payload(audit_path)
    match = _dashboard_json_payload(match_path)
    if not isinstance(raw, dict) or not isinstance(match, dict):
        result["needs_attention"] = True
        result["reasons"].append("current source-record raw or judgment sidecar is unavailable")
        return result
    if str(raw.get("source_record_audit_sha256") or "").strip() != str(
        identity.get("source_record_audit_sha256") or ""
    ).strip():
        result["needs_attention"] = True
        result["reasons"].append(
            "source-record raw sidecar changed while its fast identity was checked"
        )
        return result
    try:
        raw_file_sha256 = hashlib.sha256(audit_path.read_bytes()).hexdigest()
    except OSError:
        raw_file_sha256 = ""
    if raw_file_sha256 != str(identity.get("source_record_audit_file_sha256") or ""):
        result["needs_attention"] = True
        result["reasons"].append(
            "source-record raw bytes changed while its fast identity was checked"
        )
        return result

    (
        semantic_contract_revalidation,
        semantic_contract_revalidation_error,
    ) = evidence.source_record_semantic_contract_revalidation_context(
        folder, raw
    )
    if semantic_contract_revalidation_error:
        result["needs_attention"] = True
        result["reasons"].append(
            "semantic-contract revalidation is invalid: "
            + semantic_contract_revalidation_error
        )
        return result
    effective_semantic_errors = evidence.source_record_effective_semantic_errors(
        raw,
        semantic_contract_revalidation=semantic_contract_revalidation,
    )

    closure_paths, closure_error = _fast_source_record_closure_paths(raw)
    if closure_error:
        result["needs_attention"] = True
        result["reasons"].append(closure_error)
        return result
    active_support_rows, inactive_support_rows, support_scope_error = (
        _fast_source_record_unconfigured_support_scope(folder, raw, closure_paths)
    )
    result["inactive_legacy_support_rows"] = inactive_support_rows
    if support_scope_error:
        result["needs_attention"] = True
        result["reasons"].append(support_scope_error)
    if active_support_rows:
        result["needs_attention"] = True
        result["reasons"].append(
            f"{len(active_support_rows)} active unconfigured Assumptions support declaration(s)"
        )

    reachable_auxiliaries = [
        item
        for item in raw.get("unresolved_reachable_paper_interface_auxiliaries") or []
        if isinstance(item, Mapping)
    ]
    result["reachable_auxiliary_rows"] = reachable_auxiliaries
    if reachable_auxiliaries:
        result["needs_attention"] = True
        result["reasons"].append(
            f"{len(reachable_auxiliaries)} selected-root-reachable PaperInterface auxiliary declaration(s) lack a route or quarantine"
        )
    if raw.get("ambiguous_reachable_paper_interface_auxiliary_references"):
        result["needs_attention"] = True
        result["reasons"].append("raw source-record receipt has ambiguous reachable auxiliary references")
    for key, label in (
        ("missing_configured_review_rows", "configured review row(s) missing from raw receipt"),
        ("recursion_failures", "source-record recursion failure(s)"),
        ("semantic_model_review_configuration_errors", "semantic-model review configuration error(s)"),
        ("source_contract_association_errors", "source-contract association error(s)"),
        ("source_coverage_route_errors", "source-coverage route error(s)"),
    ):
        values = effective_semantic_errors.get(key, raw.get(key))
        if isinstance(values, list) and values:
            result["needs_attention"] = True
            result["reasons"].append(f"{len(values)} {label}")

    required = set(
        evidence.source_record_required_keys(
            raw,
            semantic_contract_revalidation=semantic_contract_revalidation,
        )
    )
    try:
        map_sha256 = evidence.current_paper_statement_map_sha256(folder)
        current = evidence._current_source_record_judgment_items(
            raw,
            match,
            expected_paper_statement_map_sha256=map_sha256,
            folder=folder,
            # The subprocess above has already checked the same exact raw
            # source/configuration identity.  This avoids redoing strict
            # external-artifact identity work in a dashboard-only precheck.
            prevalidated_source_record_identity_error="",
        )
    except Exception as exc:  # noqa: BLE001 - missing semantic validation is a failure.
        current = {}
        result["needs_attention"] = True
        result["reasons"].append("could not validate current source-record judgments: " + str(exc))
    result["required_judgment_count"] = len(required)
    result["current_judgment_count"] = len(set(current) & required)
    missing = sorted(required - set(current))
    if missing:
        result["needs_attention"] = True
        result["reasons"].append(
            f"{len(missing)} source-record semantic judgment(s) are missing or stale"
        )

    try:
        closure_files = sorted(
            path for path in closure_paths if path.is_file() and folder in path.parents
        )
        hidden = audit_repository.check_hidden_variable_premises_in_files(closure_files)
        result["hidden_variable_premises"] = [finding.message for finding in hidden]
        if hidden:
            result["needs_attention"] = True
            result["reasons"].append(f"{len(hidden)} hidden `variable` premise finding(s)")
    except Exception as exc:  # noqa: BLE001 - source scan must not silently disappear.
        result["needs_attention"] = True
        result["reasons"].append("could not scan Lean-owned closure for hidden variables: " + str(exc))

    assumption_sidecar = _dashboard_json_payload(llm_assumption_judgments_file(folder))
    sidecar_items = assumption_sidecar.get("items") if isinstance(assumption_sidecar, Mapping) else None
    if isinstance(sidecar_items, Mapping):
        # No configured assumptions means these serialized entries are outside
        # the active explicit-assumption surface.  They are reported for
        # cleanup/provenance but never grant current premise-audit credit.
        result["inactive_assumption_sidecar_rows"] = sorted(
            str(key).strip() for key in sidecar_items if str(key).strip()
        )
    return result


def print_fast_saved_source_record_assumption_precheck(result: Mapping[str, Any]) -> bool:
    """Print a clear bounded precheck result and return whether it needs attention."""

    paper = str(result.get("paper") or "unknown paper")
    scope = str(result.get("scope") or "")
    print(f"Assumption-provenance fast precheck for {paper}: {scope}.")
    inactive_support = list(result.get("inactive_legacy_support_rows") or [])
    if inactive_support:
        print(
            f" - {len(inactive_support)} unconfigured support declaration(s) are in an unimported legacy assumption source, not the current theorem surface: "
            + _format_name_sample(inactive_support)
        )
    inactive_sidecar = list(result.get("inactive_assumption_sidecar_rows") or [])
    if inactive_sidecar:
        print(
            f" - {len(inactive_sidecar)} unselected assumption-sidecar entry/entries receive no current premise-audit credit: "
            + _format_name_sample(inactive_sidecar)
        )
    reachable = list(result.get("reachable_auxiliary_rows") or [])
    if reachable:
        print(
            f" - {len(reachable)} current PaperInterface auxiliary declaration(s) are graph-reachable from selected review rows without a source route or quarantine."
        )
        for item in reachable[:3]:
            declaration = str(item.get("declaration") or "unknown declaration")
            references = item.get("transitively_referenced_from") or []
            chain = ""
            if isinstance(references, list) and references and isinstance(references[0], Mapping):
                chain = " -> ".join(
                    str(value).rsplit(".", 1)[-1]
                    for value in references[0].get("dependency_chain") or []
                    if str(value).strip()
                )
            print(f"   {declaration}" + (f" via {chain}" if chain else ""))
    if result.get("needs_attention"):
        print("Fast precheck needs attention: " + "; ".join(result.get("reasons") or ["unknown reason"]) + ".")
        print("Run strict paper closeout before claiming a formalization result.")
        return True
    print(
        "Fast precheck is current: "
        f"{int(result.get('current_judgment_count') or 0)}/{int(result.get('required_judgment_count') or 0)} "
        "semantic source-record judgments current, with no graph-visible premise defect."
    )
    print("Strict paper closeout remains required before publication.")
    return False


def hidden_premise_repository_audit_rows(paper: str | None) -> list[dict[str, Any]]:
    """Return hidden-premise findings from the repository audit for CLI prechecks."""

    try:
        try:
            from scripts import audit_repository
        except ModuleNotFoundError:  # Direct script execution.
            import audit_repository  # type: ignore
    except Exception as exc:  # pragma: no cover - defensive CLI fallback
        return [
            {
                "paper": paper or "all papers",
                "hidden_premise_audit_error": str(exc),
                "hidden_premise_count": 0,
                "hidden_premise_samples": [],
                "needs_attention": True,
                "has_warning": True,
            }
        ]

    marker = "has premises not routed through explicit Assumptions.lean paper assumptions"
    variable_marker = "proof-boundary `variable` premise"
    source_record_markers = (
        "source-record audit",
        "source-record judge",
    )
    rows: dict[str, dict[str, Any]] = {}
    accepted_conditional_premises: dict[str, dict[str, list[str]]] = {}

    def paper_conditional_premises(paper_name: str) -> dict[str, list[str]]:
        cached = accepted_conditional_premises.get(paper_name)
        if cached is not None:
            return cached
        folder = ROOT / "papers" / paper_name
        cached = conditional_boundary_statement_premises(folder) if folder.exists() else {}
        accepted_conditional_premises[paper_name] = cached
        return cached

    def finding_is_accepted_conditional(paper_name: str, message: str) -> bool:
        for row_name, premises in paper_conditional_premises(paper_name).items():
            if f"`{row_name}`" not in message:
                continue
            if any(premise and premise in message for premise in premises):
                return True
        return False

    findings = list(
        audit_repository.check_machine_paper_status(
            library_premise_audit=False,
            paper_filter=paper,
        )
    )
    if paper:
        paper_dir = ROOT / "papers" / paper
        if paper_dir.exists():
            paper_files = sorted(path for path in paper_dir.rglob("*.lean") if path.is_file())
            findings.extend(audit_repository.check_hidden_variable_premises_in_files(paper_files))
    else:
        findings.extend(audit_repository.check_hidden_variable_premises(include_active=False))
    for finding in findings:
        if (
            marker not in finding.message
            and variable_marker not in finding.message
            and not any(source_marker in finding.message for source_marker in source_record_markers)
        ):
            continue
        rel_path = finding.path.relative_to(ROOT) if finding.path.is_absolute() else finding.path
        parts = rel_path.parts
        if len(parts) < 2 or parts[0] != "papers":
            continue
        paper_name = parts[1]
        if paper and paper_name != paper:
            continue
        row = rows.setdefault(paper_name, _default_hidden_premise_row(paper_name))
        if finding_is_accepted_conditional(paper_name, finding.message):
            row["accepted_conditional_premise_count"] += 1
            if len(row["accepted_conditional_premise_samples"]) < 5:
                row["accepted_conditional_premise_samples"].append(finding.message)
            continue
        row["hidden_premise_count"] += 1
        row["needs_attention"] = True
        row["has_warning"] = True
        if finding.severity == "ERROR":
            row["hidden_premise_error_count"] += 1
        elif finding.severity == "WARN":
            row["hidden_premise_warning_count"] += 1
        if len(row["hidden_premise_samples"]) < 5:
            row["hidden_premise_samples"].append(finding.message)
    return list(rows.values())


def merge_hidden_premise_audit_rows(
    rows: list[dict[str, Any]], paper: str | None
) -> list[dict[str, Any]]:
    """Merge explicit-assumption and hidden-premise audits for CLI reporting."""

    merged = {str(row.get("paper") or ""): dict(row) for row in rows}
    for hidden in hidden_premise_repository_audit_rows(paper):
        paper_name = str(hidden.get("paper") or "")
        row = merged.setdefault(paper_name, {"paper": paper_name})
        prior_needs_attention = bool(row.get("needs_attention"))
        prior_has_warning = bool(row.get("has_warning"))
        row.update(hidden)
        row["needs_attention"] = prior_needs_attention or bool(hidden.get("needs_attention"))
        row["has_warning"] = prior_has_warning or bool(hidden.get("has_warning"))
    return list(merged.values())


def stale_review_rows(rows: list[dict[str, Any]]) -> dict[str, list[dict[str, Any]]]:
    """Partition rows into stale and unreviewed buckets for launch-time diagnostics."""

    stale = [
        row
        for row in rows
        if row.get("has_review")
        and (row.get("lean_stale") or row.get("paper_stale") or row.get("source_stale"))
    ]
    unreviewed = [row for row in rows if not row.get("has_review")]
    mismatch = [
        row
        for row in rows
        if row.get("has_review")
        and not row.get("lean_stale")
        and not row.get("paper_stale")
        and not row.get("source_stale")
        and row.get("latest_matches") is False
    ]
    return {"stale": stale, "unreviewed": unreviewed, "mismatch": mismatch}


def parse_bool_flag(value: str | None) -> bool:
    if not value:
        return False
    return value.lower() in {"1", "true", "t", "yes", "y", "on"}


def append_review(log_file: Path, payload: dict[str, Any], default_user: str) -> dict[str, Any]:
    log_file.parent.mkdir(parents=True, exist_ok=True)

    paper = str(payload.get("paper") or "").strip()
    theorem = str(payload.get("theorem") or "").strip()
    user = str(payload.get("user") or default_user).strip() or default_user
    notes = str(payload.get("notes", "")).strip()
    raw_judgment = payload.get("judgment")
    if raw_judgment is None:
        raw_judgment = payload.get("matches")
    judgment = _review_judgment(raw_judgment)
    if not judgment:
        raise ValueError("missing review judgment")
    matches = _review_matches_value(judgment)
    lean_statement = str(payload.get("lean_statement") or "").strip()
    paper_statement = str(payload.get("paper_statement") or "").strip()
    agent_statement = str(payload.get("agent_statement") or "").strip()
    source_status = str(payload.get("source_status") or "").strip()
    source_note = str(payload.get("source_note") or "").strip()
    if not paper or not theorem:
        raise ValueError("missing paper/theorem")
    if not lean_statement or not paper_statement or not agent_statement or not source_status or not source_note:
        (
            current_lean_statement,
            current_paper_statement,
            current_agent_statement,
            current_source_status,
            current_source_note,
        ) = get_item_statements(
            paper, theorem
        )
        if not lean_statement:
            lean_statement = current_lean_statement
        if not paper_statement:
            paper_statement = current_paper_statement
        if not agent_statement:
            agent_statement = current_agent_statement
        if not source_status:
            source_status = current_source_status
        if not source_note:
            source_note = current_source_note

    entry = {
        "paper": paper,
        "theorem": theorem,
        "user": user,
        "paper_statement": paper_statement,
        "lean_statement": lean_statement,
        "agent_statement": agent_statement,
        "source_status": source_status,
        "source_note": source_note,
        "lean_statement_sha256": statement_digest(lean_statement),
        "paper_statement_sha256": statement_digest(paper_statement),
        "agent_statement_sha256": statement_digest(agent_statement),
        "source_metadata_sha256": source_metadata_digest(source_status, source_note),
        "judgment": judgment,
        "matches": matches,
        "notes": notes,
        "timestamp": datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z"),
    }
    with log_file.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(entry))
        handle.write("\n")
    return entry


HTML_PAGE = """
<!doctype html>
<html lang='en'>
<head>
  <meta charset='utf-8' />
  <meta name='viewport' content='width=device-width, initial-scale=1' />
  <title>Paper Interface Review Dashboard</title>
    <style>
    :root {
      --bg: #f5f7fb;
      --panel: #ffffff;
      --line: #e5e8ee;
      --line-strong: #ccd4e0;
      --muted: #5d6678;
      --text: #172039;
      --accent: #1f6feb;
      --accent-soft: #e8f1ff;
      --ok: #0b8043;
      --ok-soft: #e7f4ed;
      --bad: #aa2e2e;
      --bad-soft: #fae8e8;
      --warn: #a35f00;
      --warn-soft: #fff3dd;
      --neutral-soft: #f2f5f9;
    }
    * { box-sizing: border-box; }
    body {
      margin: 0;
      background: var(--bg);
      color: var(--text);
      font-family: "Inter", "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
      -webkit-font-smoothing: antialiased;
      line-height: 1.35;
    }
    .page {
      width: min(1800px, calc(100% - 16px));
      margin: 0 auto;
      padding: 18px 0 30px;
    }
    h1 {
      margin: 0 0 8px;
      font-size: 28px;
      letter-spacing: 0;
    }
    .subtitle { color: var(--muted); margin: 0 0 14px; }
    .toolbar {
      margin: 14px 0 16px;
      display: flex;
      gap: 12px;
      align-items: center;
      flex-wrap: wrap;
      background: var(--panel);
      padding: 10px 12px;
      border-radius: 8px;
      border: 1px solid var(--line);
      box-shadow: 0 1px 2px rgba(25, 33, 58, 0.06);
    }
    .toolbar label { font-size: 13px; color: #334155; }
    .toolbar input, .toolbar select {
      margin-left: 8px;
      border: 1px solid var(--line);
      border-radius: 7px;
      padding: 8px 10px;
      min-width: 170px;
      font: inherit;
      background: #fff;
    }
    .toolbar select { min-width: 150px; }
    .toolbar-toggle {
      display: inline-flex;
      align-items: center;
      gap: 6px;
      color: #334155;
      font-size: 13px;
    }
    .toolbar-toggle input {
      min-width: 0;
      margin-left: 0;
    }
    .summary-grid {
      display: grid;
      grid-template-columns: repeat(4, minmax(120px, 1fr));
      gap: 10px;
      margin: 0 0 12px;
    }
    .summary-card {
      background: var(--panel);
      border: 1px solid var(--line);
      border-radius: 8px;
      padding: 10px 12px;
      box-shadow: 0 1px 2px rgba(25, 33, 58, 0.04);
    }
    .summary-card .label {
      color: var(--muted);
      font-size: 12px;
      margin-bottom: 2px;
    }
    .summary-card .value {
      color: var(--text);
      font-weight: 700;
      font-size: 20px;
    }
    .muted { color: var(--muted); }
    .small { font-size: 12px; }
    .paper-block {
      margin: 16px 0;
      border: 1px solid var(--line);
      border-radius: 8px;
      padding: 12px;
      background: var(--panel);
      box-shadow: 0 1px 2px rgba(25, 33, 58, 0.04);
    }
    .paper-header {
      display: flex;
      justify-content: space-between;
      gap: 12px;
      align-items: flex-start;
      margin-bottom: 10px;
    }
    .paper-block h2 { margin: 0; font-size: 22px; }
    .paper-progress {
      color: var(--muted);
      font-size: 12px;
      text-align: right;
      min-width: 180px;
    }
    .paper-source-panel {
      border: 1px solid #e5ecff;
      border-radius: 8px;
      padding: 7px 10px;
      background: #f7faff;
      margin-bottom: 10px;
    }
    .paper-source-heading { margin: 0 0 8px; font-size: 14px; }
    .paper-source-subtle {
      color: #334155;
      margin-bottom: 6px;
      font-size: 12px;
      line-height: 1.35;
    }
    .surface-audit-panel {
      border: 1px solid var(--line);
      border-radius: 8px;
      padding: 9px 10px;
      background: #fff;
      margin-bottom: 10px;
      display: grid;
      gap: 5px;
    }
    .surface-audit-panel.ok {
      border-color: #b8dec8;
      background: var(--ok-soft);
    }
    .surface-audit-panel.warn {
      border-color: #f0cf91;
      background: var(--warn-soft);
    }
    .surface-audit-panel.bad {
      border-color: #efb6b6;
      background: var(--bad-soft);
    }
    .surface-audit-heading {
      display: flex;
      justify-content: space-between;
      gap: 8px;
      align-items: center;
      font-weight: 650;
      font-size: 13px;
    }
    .surface-audit-body {
      color: #334155;
      font-size: 12px;
      line-height: 1.35;
    }
    .source-actions {
      display: flex;
      gap: 8px;
      flex-wrap: wrap;
      margin: 8px 0 4px;
    }
    .source-link {
      border: 1px solid #cad3e5;
      border-radius: 7px;
      padding: 6px 9px;
      text-decoration: none;
      color: #1e293b;
      background: #fff;
      font-size: 12px;
      transition: border-color 0.15s ease;
    }
    .source-link:hover {
      border-color: #9fb0d8;
      background: #fbfdff;
    }
    .table-wrap { overflow-x: auto; }
    .paper-details {
      border: 0;
    }
    .paper-details > summary {
      list-style: none;
      cursor: pointer;
    }
    .paper-details > summary::-webkit-details-marker { display: none; }
    table {
      width: 100%;
      border-collapse: collapse;
      margin-top: 0;
      min-width: 0;
      table-layout: auto;
    }
    th, td { border: 1px solid var(--line); padding: 10px; vertical-align: top; }
    thead th {
      background: #f8f9fc;
      text-align: left;
      position: sticky;
      top: 0;
      z-index: 1;
    }
    tbody tr { background: #ffffff; }
    tbody tr:hover { background: #fbfcff; }
    tbody tr:nth-child(odd) { background: #fcfdff; }
    tbody tr.is-hidden { display: none; }
    body.hide-agent .agent-column { display: none; }
    .review-item {
      display: grid;
      grid-template-columns: minmax(0, 1fr) minmax(220px, 280px);
      gap: 12px;
      align-items: start;
    }
    .review-main {
      min-width: 0;
      display: grid;
      gap: 10px;
    }
    .review-controls {
      min-width: 0;
      border-left: 1px solid var(--line);
      padding-left: 12px;
    }
    .review-section {
      min-width: 0;
    }
    .review-section-label {
      font-size: 12px;
      color: var(--muted);
      margin-bottom: 5px;
      font-family: "Inter", "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
    }
    .col-paper, .col-lean, .col-agent { white-space: pre-wrap; font-family: ui-monospace, SFMono-Regular, Menlo, monospace; font-size: 13px; line-height: 1.35; }
    .col-agent { white-space: normal; }
    .col-paper, .col-lean, .col-agent { width: 100%; }
    .statement-box {
      border: 1px solid var(--line);
      border-radius: 7px;
      background: #fff;
    }
    .statement-box[open] {
      background: #fcfdff;
    }
    .statement-box summary {
      cursor: pointer;
      color: #334155;
      background: #f8f9fc;
      padding: 7px 9px;
      border-radius: 7px;
      font-family: "Inter", "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
      font-size: 12px;
    }
    .statement-box[open] summary {
      border-bottom: 1px solid var(--line);
      border-radius: 7px 7px 0 0;
    }
    .statement-body {
      padding: 9px;
      max-height: 520px;
      overflow: auto;
      white-space: pre-wrap;
      word-break: break-word;
    }
    .col-lean .statement-body {
      white-space: pre-wrap;
      overflow-x: hidden;
      overflow-wrap: anywhere;
      word-break: break-word;
    }
    .col-lean .statement-body code {
      display: block;
      max-width: 100%;
      white-space: pre-wrap;
      overflow-wrap: anywhere;
      word-break: break-word;
    }
    .statement-body code {
      white-space: pre-wrap;
      word-break: break-word;
    }
    .paper-statement-image {
      display: block;
      width: 100%;
      max-width: none;
      height: auto;
      background: #fff;
      border: 1px solid #d8e0ec;
      border-radius: 6px;
      margin-bottom: 8px;
    }
    .statement-preview {
      display: block;
      margin-top: 4px;
      color: var(--muted);
      overflow: hidden;
      text-overflow: ellipsis;
      white-space: nowrap;
      max-width: 100%;
    }
    .agent-statement {
      white-space: pre-wrap;
      word-break: break-word;
    }
    .agent-statement code {
      font-family: ui-monospace, SFMono-Regular, Menlo, monospace;
      white-space: pre-wrap;
      word-break: break-word;
    }
    .llm-judge-panel {
      margin-top: 9px;
      border: 1px solid var(--line);
      border-radius: 7px;
      background: #fff;
      padding: 8px 9px;
    }
    .llm-judge-heading {
      display: flex;
      align-items: center;
      justify-content: space-between;
      gap: 8px;
      margin-bottom: 6px;
    }
    .llm-judge-reason {
      color: #334155;
      font-size: 12px;
      white-space: pre-wrap;
      word-break: break-word;
    }
    .col-review { width: 18%; min-width: 220px; }
    .paper-title { font-weight: 600; margin-bottom: 8px; }
    .slice-meta {
      margin: -4px 0 8px;
      color: var(--muted);
      font-size: 12px;
      line-height: 1.3;
    }
    .source-provenance {
      border: 1px solid #f0cf91;
      border-radius: 7px;
      background: var(--warn-soft);
      color: #6f4e07;
      padding: 7px 9px;
      font-size: 12px;
      line-height: 1.35;
      font-family: "Inter", "Segoe UI", Roboto, Helvetica, Arial, sans-serif;
    }
    .source-provenance.direct {
      border-color: #b8dec8;
      background: var(--ok-soft);
      color: var(--ok);
    }
    .source-provenance-label {
      font-weight: 650;
      margin-right: 4px;
    }
    .row-note {
      width: 100%;
      min-height: 72px;
      border: 1px solid var(--line);
      border-radius: 7px;
      padding: 8px;
      font: inherit;
      resize: vertical;
    }
    .review-decision {
      border: 0;
      padding: 0;
      margin: 8px 0 8px;
      display: grid;
      gap: 6px;
    }
    .review-decision legend {
      padding: 0;
      margin-bottom: 2px;
      color: var(--muted);
      font-size: 12px;
    }
    .review-decision-option {
      display: flex;
      align-items: center;
      gap: 7px;
      font-size: 13px;
      line-height: 1.25;
    }
    .history { margin-top: 10px; font-size: 12px; color: #334155; }
    .history-entry { border-top: 1px dashed #d6dce6; padding-top: 8px; margin-top: 8px; }
    .history-entry + .history-entry { border-top: 1px dashed #d6dce6; }
    .ok { color: var(--ok); }
    .bad { color: var(--bad); }
    .warn { color: var(--warn); }
    .btn {
      margin-top: 8px;
      border: 1px solid #2f3d5f;
      border-radius: 7px;
      background: var(--accent);
      color: #fff;
      padding: 8px 10px;
      cursor: pointer;
      font-weight: 600;
      transition: filter 0.12s ease;
    }
    .btn:hover { filter: brightness(0.96); }
    .btn:active { transform: translateY(1px); }
    .btn[disabled] {
      cursor: wait;
      opacity: 0.72;
    }
    .toolbar .btn {
      margin-top: 0;
      padding: 7px 10px;
    }
    .status-pill {
      display: inline-block;
      border: 1px solid var(--line-strong);
      border-radius: 999px;
      padding: 3px 8px;
      font-size: 12px;
      background: var(--neutral-soft);
      color: #334155;
      line-height: 1.2;
    }
    .status-pill.ok {
      background: var(--ok-soft);
      border-color: #b8dec8;
      color: var(--ok);
    }
    .status-pill.warn {
      background: var(--warn-soft);
      border-color: #f0cf91;
      color: var(--warn);
    }
    .status-pill.bad {
      background: var(--bad-soft);
      border-color: #efb6b6;
      color: var(--bad);
    }
    .status-line {
      display: flex;
      flex-wrap: wrap;
      gap: 6px;
      align-items: center;
      margin: 0 0 8px;
    }
    .save-status {
      display: inline-block;
      min-height: 16px;
      margin-left: 8px;
    }
    .summary-pill { margin-left: 8px; }
    .summary { margin-left: auto; display: inline-flex; gap: 10px; }
    .empty-filter {
      display: none;
      background: var(--panel);
      border: 1px dashed var(--line-strong);
      border-radius: 8px;
      padding: 16px;
      color: var(--muted);
      text-align: center;
    }
    @media (max-width: 860px) {
      .summary-grid { grid-template-columns: repeat(2, minmax(120px, 1fr)); }
      .paper-header { display: block; }
      .paper-progress { text-align: left; margin-top: 4px; }
      .toolbar input, .toolbar select { min-width: 130px; }
      .review-item { grid-template-columns: 1fr; }
      .review-controls {
        border-left: 0;
        border-top: 1px solid var(--line);
        padding-left: 0;
        padding-top: 10px;
      }
    }

  </style>
  <script>
    window.MathJax = {
      tex: {
        inlineMath: [["\\\\(", "\\\\)"], ["$", "$"]],
        processEscapes: true,
        tags: "none",
      },
      startup: {
        typeset: false,
      },
    };
  </script>
  <script async id="mathjax-script" src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"></script>
</head>
<body>
  <div class='page'>
    <h1>Paper Interface Review Dashboard</h1>
    <p class='subtitle'>Trace-backed validator for Lean paper-interface theorem statements.</p>
    <div id='summaryCards' class='summary-grid' aria-live='polite'>
      <div class='summary-card'><div class='label'>Reviewed</div><div class='value' id='cardReviewed'>0/0</div></div>
      <div class='summary-card'><div class='label'>Need Action</div><div class='value' id='cardAttention'>0</div></div>
      <div class='summary-card'><div class='label'>Stale</div><div class='value' id='cardStale'>0</div></div>
      <div class='summary-card'><div class='label'>Mismatch</div><div class='value' id='cardMismatch'>0</div></div>
    </div>
    <div class='toolbar'>
      <label>
        GitHub/user handle:
        <input id='userHandle' type='text' value='{user}' />
      </label>
      <label>
        Search:
        <input id='searchBox' type='search' placeholder='Paper or theorem' />
      </label>
      <label>
        View:
        <select id='statusFilter'>
          <option value='all'>All rows</option>
          <option value='attention'>Needs action</option>
          <option value='unreviewed'>Unreviewed</option>
          <option value='stale'>Stale</option>
          <option value='mismatch'>Marked mismatch</option>
          <option value='uncertain'>Marked uncertain</option>
          <option value='reviewed'>Reviewed</option>
        </select>
      </label>
      <label>
        Slice:
        <select id='sliceFilter'>
          <option value='all'>All slices</option>
        </select>
      </label>
      <label class='toolbar-toggle'>
        <input id='hideAgentDraft' type='checkbox' />
        Hide LLM checks
      </label>
      <button id='saveAllReviews' class='btn' type='button'>Save all review</button>
      <span id='saveAllStatus' class='save-status small muted'></span>
      <span id='summary' class='summary small muted'></span>
      <span id='count' class='small muted'></span>
      <span id='logPath' class='small muted'></span>
    </div>
    <div id='emptyFilter' class='empty-filter'>No rows match the current filters.</div>
    <div id='containers'>Loading…</div>
  </div>

  <script>
    window.addEventListener("error", (event) => {
      const container = document.getElementById("containers");
      if (container) {
        container.textContent = `Dashboard render error: ${event.message || "unknown error"}`;
      }
    });
    window.addEventListener("unhandledrejection", (event) => {
      const container = document.getElementById("containers");
      if (container) {
        container.textContent = `Dashboard render error: ${event.reason || "unknown promise rejection"}`;
      }
    });
    const state = {
      papers: __PAPERS__,
      logPath: __LOG_PATH__,
      user: __USER__,
      reviews: [],
      statusRows: [],
    };

    function byLatest(entries) {
      entries.sort((a, b) => (a.timestamp < b.timestamp ? 1 : -1));
    }

    function safeId(value) {
      return String(value).replace(/[^a-zA-Z0-9_-]/g, "_");
    }

    function normalizeStatement(value) {
      return String(value || "").replace(/\\s+/g, " ").trim();
    }

    function escapeHtml(value) {
      const span = document.createElement("span");
      span.textContent = String(value);
      return span.innerHTML;
    }

    function isLongProse(value) {
      const text = value.replace(/[^A-Za-z]/g, " ").trim();
      if (!text) {
        return false;
      }
      const words = text.split(/\\s+/);
      const longWords = words.filter((word) => word.length >= 4);
      return longWords.length > 12;
    }

    function looksLikeLatex(value) {
      return /\\\\[a-zA-Z]+/.test(value)
        || /[∀∃→↔≤≥≠∞∈∉∑∏ℝℕ]/.test(value)
        || /\\\\/.test(value);
    }

    function isFormulaValue(value) {
      if (!value) {
        return false;
      }
      if (isLongProse(value)) {
        return false;
      }
      if (/[`$]/.test(value)) {
        return false;
      }
      return looksLikeLatex(value) && value.length < 1800;
    }

    function renderPaperStatement(value) {
      const text = escapeHtml(value || "No paper-facing summary found.");
      if (!value || !String(value).trim()) {
        return text;
      }

      if (isFormulaValue(String(value))) {
        return `\\\\(${text}\\\\)`;
      }

      const marked = text.replace(/`([^`]+)`/g, (match, content) => {
        const body = content.trim();
        return looksLikeLatex(body) ? `\\(${body}\\)` : `<code>${body}</code>`;
      });
      return marked.replace(/\\n/g, "<br/>");
    }

    function renderTexDraft(value) {
      const text = escapeHtml(value || "No auto-generated preview available.");
      return text.replace(/\\n/g, "<br/>");
    }

    function llmJudgmentLabel(item) {
      const value = String(item.llm_match_judgment || "").toLowerCase();
      const resolution = String(item.llm_match_resolution || "").toLowerCase();
      if (item.llm_match_stale) {
        return "Stale LLM judgment";
      }
      if (value === "matches") {
        return "LLM: matches";
      }
      if (value === "mismatch" && resolution === "conditional_boundary") {
        return "LLM: visible-premise boundary";
      }
      if (value === "mismatch") {
        return "LLM: mismatch";
      }
      if (value === "uncertain") {
        return "LLM: uncertain";
      }
      return "No LLM judgment";
    }

    function llmJudgmentClass(item) {
      const value = String(item.llm_match_judgment || "").toLowerCase();
      const resolution = String(item.llm_match_resolution || "").toLowerCase();
      if (item.llm_match_stale) {
        return "warn";
      }
      if (value === "matches") {
        return "ok";
      }
      if (value === "mismatch" && resolution === "conditional_boundary") {
        return "warn";
      }
      if (value === "mismatch") {
        return "bad";
      }
      if (value === "uncertain") {
        return "warn";
      }
      return "";
    }

    function makeLlmJudgePanel(item) {
      const panel = document.createElement("div");
      panel.className = "llm-judge-panel";
      const heading = document.createElement("div");
      heading.className = "llm-judge-heading";
      const title = document.createElement("span");
      title.className = "small muted";
      title.textContent = "LLM statement-match note";
      const badge = document.createElement("span");
      badge.className = `status-pill ${llmJudgmentClass(item)}`.trim();
      badge.textContent = llmJudgmentLabel(item);
      heading.appendChild(title);
      heading.appendChild(badge);
      panel.appendChild(heading);
      const reason = document.createElement("div");
      reason.className = "llm-judge-reason";
      const bits = [];
      if (item.llm_match_reason) {
        bits.push(String(item.llm_match_reason));
      }
      if (item.llm_match_stale) {
        bits.push("The saved judgment predates the current Lean, paper, or TeX statement.");
      }
      if (item.llm_match_resolution) {
        bits.push(`Resolution: ${item.llm_match_resolution}`);
      }
      if (Array.isArray(item.llm_match_boundary_names) && item.llm_match_boundary_names.length) {
        bits.push(`Boundary: ${item.llm_match_boundary_names.join(", ")}`);
      }
      if (
        Array.isArray(item.llm_match_conditional_premises)
        && item.llm_match_conditional_premises.length
      ) {
        bits.push(`Visible extra Lean premises: ${item.llm_match_conditional_premises.join(", ")}`);
      }
      if (item.llm_match_resolution_reason) {
        bits.push(String(item.llm_match_resolution_reason));
      }
      if (!bits.length) {
        bits.push(item.llm_match_judgment
          ? "No reason recorded."
          : "Run the independent semantic paper-vs-TeX statement check and save statement_match_llm.json.");
      }
      if (item.llm_match_source) {
        bits.push(`Source: ${item.llm_match_source}`);
      }
      reason.textContent = bits.join("\\n");
      panel.appendChild(reason);
      return panel;
    }

    function assumptionJudgmentLabel(item) {
      const value = String(item.llm_assumption_judgment || "").toLowerCase();
      if (item.llm_assumption_stale) {
        return "Stale assumption judgment";
      }
      if (value === "paper_assumption") {
        return "Assumption: in paper";
      }
      if (value === "paper_condition") {
        return "Condition: in paper";
      }
      if (value === "documented_additional_assumption") {
        return "Additional assumption";
      }
      if (value === "documented_caveat") {
        return "Documented caveat";
      }
      if (value === "partial_boundary") {
        return "Partial boundary";
      }
      if (value === "not_paper_assumption") {
        return "Assumption: not in paper";
      }
      if (value === "uncertain") {
        return "Assumption: uncertain";
      }
      return "No assumption judgment";
    }

    function assumptionJudgmentClass(item) {
      const value = String(item.llm_assumption_judgment || "").toLowerCase();
      if (item.llm_assumption_stale) {
        return "warn";
      }
      if (
        value === "paper_assumption" ||
        value === "paper_condition" ||
        value === "documented_additional_assumption" ||
        value === "documented_caveat"
      ) {
        return "ok";
      }
      if (value === "partial_boundary") {
        return "warn";
      }
      if (value === "not_paper_assumption") {
        return "bad";
      }
      if (value === "uncertain") {
        return "warn";
      }
      return "";
    }

    function makeAssumptionJudgePanel(item) {
      const panel = document.createElement("div");
      panel.className = "llm-judge-panel";
      const heading = document.createElement("div");
      heading.className = "llm-judge-heading";
      const title = document.createElement("span");
      title.className = "small muted";
      title.textContent = "LLM assumption-provenance note";
      const badge = document.createElement("span");
      badge.className = `status-pill ${assumptionJudgmentClass(item)}`.trim();
      badge.textContent = assumptionJudgmentLabel(item);
      heading.appendChild(title);
      heading.appendChild(badge);
      panel.appendChild(heading);
      const reason = document.createElement("div");
      reason.className = "llm-judge-reason";
      const bits = [];
      if (item.llm_assumption_reason) {
        bits.push(String(item.llm_assumption_reason));
      }
      if (item.llm_assumption_stale) {
        bits.push("The saved assumption judgment predates the current Lean or paper statement.");
      }
      if (!bits.length) {
        bits.push(item.llm_assumption_judgment
          ? "No reason recorded."
          : "Run the source-assumption judge and save assumption_match_llm.json.");
      }
      if (item.llm_assumption_source) {
        bits.push(`Source: ${item.llm_assumption_source}`);
      }
      reason.textContent = bits.join("\\n");
      panel.appendChild(reason);
      return panel;
    }

    function softWrapLeanSegment(segment) {
      if (segment.length < 24) {
        return segment;
      }
      return segment.replace(/_/g, "_\\u200b");
    }

    function prettyLeanIdentifier(identifier, indent = "      ") {
      const softDot = ".\\u200b";
      const parts = identifier.split(".");
      if (parts.length <= 1) {
        return softWrapLeanSegment(identifier);
      }

      const wrappedParts = parts.map(softWrapLeanSegment);
      const softWrapped = wrappedParts.join(softDot);
      if (identifier.length <= 54) {
        return softWrapped;
      }

      const namespace = wrappedParts.slice(0, -1).join(softDot);
      const last = wrappedParts[wrappedParts.length - 1];
      if (namespace.length <= 64) {
        return `${namespace}.${softDot}\\n${indent}${last}`;
      }

      return wrappedParts
        .map((part, index) => (index < wrappedParts.length - 1 ? `${part}.` : part))
        .join(`\\n${indent}`);
    }

    function prettyLeanIdentifiers(text) {
      return text.replace(
        /[A-Za-z_][A-Za-z0-9_']*(?:\\.[A-Za-z_][A-Za-z0-9_']*)+/g,
        (identifier) => prettyLeanIdentifier(identifier)
      );
    }

    function wrapLeanLine(line, maxWidth = 98) {
      if (line.length <= maxWidth) {
        return line;
      }
      const indent = (line.match(/^\\s*/) || [""])[0];
      const continuation = `${indent}  `;
      const out = [];
      let rest = line.trimEnd();

      while (rest.length > maxWidth) {
        const windowText = rest.slice(0, maxWidth);
        const breakpoints = [" (", " {", " [", "), ", ", ", " "]
          .map((marker) => windowText.lastIndexOf(marker))
          .filter((index) => index > indent.length + 18);
        const breakAt = breakpoints.length ? Math.max(...breakpoints) : -1;
        if (breakAt <= 0) {
          break;
        }
        out.push(rest.slice(0, breakAt).trimEnd());
        rest = continuation + rest.slice(breakAt).trimStart();
      }
      out.push(rest);
      return out.join("\\n");
    }

    function wrapLeanLines(text) {
      return text
        .split("\\n")
        .map((line) => wrapLeanLine(line))
        .join("\\n");
    }

    function prettyLeanStatement(value) {
      let text = String(value || "No statement text.").replace(/\\r\\n/g, "\\n");
      text = text.replace(/ :\\n\\s*/g, " :\\n  ");
      text = text.replace(/\\} \\{/g, "}\\n  {");
      text = text.replace(/\\} \\(/g, "}\\n  (");
      text = text.replace(/\\] \\[/g, "]\\n  [");
      text = text.replace(/\\] \\(/g, "]\\n  (");
      text = text.replace(/\\) \\[/g, ")\\n  [");
      text = text.replace(/\\), /g, "),\\n  ");
      text = text.replace(/, ∀ /g, ",\\n  ∀ ");
      text = text.replace(/, \\(/g, ",\\n  (");
      text = text.replace(/, ([A-Za-z_][A-Za-z0-9_']* : Type u_[0-9]+)/g, ",\\n  $1");
      text = text.replace(/, ([A-Za-z_][A-Za-z0-9_']* : Type\\*)/g, ",\\n  $1");
      text = text.replace(/, (\\[[^\\]]+\\] : [^,]+)/g, ",\\n  $1");
      text = text.replace(/ → /g, "\\n    → ");
      text = text.replace(/ ↔ /g, "\\n    ↔ ");
      text = text.replace(/ ∧ /g, "\\n    ∧ ");
      text = text.replace(/\\) \\(/g, ")\\n  (");
      return wrapLeanLines(prettyLeanIdentifiers(text));
    }

    function compactPreview(value, maxLength = 150) {
      const text = normalizeStatement(value || "");
      if (!text) {
        return "No statement text.";
      }
      if (text.length <= maxLength) {
        return text;
      }
      return `${text.slice(0, maxLength - 1)}…`;
    }

    function makeStatementBox(label, value, options = {}) {
      const details = document.createElement("details");
      details.className = "statement-box";
      if (options.open) {
        details.open = true;
      }
      const summary = document.createElement("summary");
      summary.textContent = label;
      const preview = document.createElement("span");
      preview.className = "statement-preview";
      preview.textContent = compactPreview(value, options.previewLength || 150);
      summary.appendChild(preview);
      const body = document.createElement("div");
      body.className = "statement-body";
      if (options.html) {
        body.innerHTML = options.html;
      } else {
        body.textContent = value || "No statement text.";
      }
      details.appendChild(summary);
      details.appendChild(body);
      return details;
    }

    function makeReviewSectionLabel(text) {
      const label = document.createElement("div");
      label.className = "review-section-label";
      label.textContent = text;
      return label;
    }

    function typesetMath() {
      if (typeof window.MathJax === "undefined") {
        return;
      }
      if (window.MathJax.typesetPromise) {
        window.MathJax.typesetPromise().catch(() => {});
        return;
      }
      if (window.MathJax.Hub && window.MathJax.Hub.Queue) {
        window.MathJax.Hub.Queue(["Typeset", window.MathJax.Hub]);
      }
    }

    function findCurrentItem(paper, theorem) {
      for (const p of state.papers) {
        if (p.name !== paper) continue;
        for (const item of p.items) {
          if (item.name === theorem) return item;
        }
      }
      return null;
    }

    function statusKey(paper, theorem) {
      return `${paper}::${theorem}`;
    }

    function allItemsCount() {
      return state.papers.reduce((acc, paper) => acc + paper.items.length, 0);
    }

    function sliceKey(paper, sliceId) {
      return `${paper}::${sliceId || "all"}`;
    }

    function populateSliceFilter() {
      const select = document.getElementById("sliceFilter");
      const current = select.value || "all";
      select.textContent = "";
      const allOption = document.createElement("option");
      allOption.value = "all";
      allOption.textContent = "All slices";
      select.appendChild(allOption);
      for (const paper of state.papers) {
        const slices = paper.slices || [];
        if (slices.length <= 1 && slices[0] && slices[0].id === "all") {
          continue;
        }
        for (const slice of slices) {
          const option = document.createElement("option");
          option.value = sliceKey(paper.name, slice.id);
          const count = typeof slice.count === "number" ? ` (${slice.count})` : "";
          option.textContent = `${paper.name}: ${slice.title}${count}`;
          select.appendChild(option);
        }
      }
      select.value = Array.from(select.options).some((option) => option.value === current)
        ? current
        : "all";
    }

    function buildStatusMap(rows) {
      const out = new Map();
      for (const row of rows || []) {
        out.set(statusKey(row.paper, row.theorem), row);
      }
      return out;
    }

    function statusFor(paper, theorem) {
      return buildStatusMap(state.statusRows).get(statusKey(paper, theorem)) || null;
    }

    function reviewJudgment(entry) {
      if (!entry) {
        return "";
      }
      const explicit = String(entry.judgment || entry.latest_judgment || "").toLowerCase();
      if (["matches", "mismatch", "uncertain"].includes(explicit)) {
        return explicit;
      }
      if (entry.matches === true || entry.latest_matches === true) {
        return "matches";
      }
      if (entry.matches === false || entry.latest_matches === false) {
        return "mismatch";
      }
      return "";
    }

    function statusLabel(row) {
      if (!row || !row.has_review) {
        return "Unreviewed";
      }
      if (row.lean_stale || row.paper_stale || row.source_stale) {
        return "Stale";
      }
      const judgment = reviewJudgment(row);
      if (judgment === "mismatch") {
        return "Mismatch";
      }
      if (judgment === "uncertain") {
        return "Uncertain";
      }
      return "Reviewed";
    }

    function statusClass(row) {
      const label = statusLabel(row);
      if (label === "Reviewed") {
        return "ok";
      }
      if (label === "Mismatch") {
        return "bad";
      }
      if (label === "Stale" || label === "Uncertain") {
        return "warn";
      }
      return "";
    }

    function staleReason(row) {
      if (!row) {
        return "";
      }
      const reasons = [];
      if (row.lean_stale) reasons.push("Lean changed");
      if (row.paper_stale) reasons.push("paper text changed");
      if (row.source_stale) reasons.push("source provenance changed");
      return reasons.join(", ");
    }

    function sourceMetadataDigestInput(itemOrEntry) {
      if (!itemOrEntry) {
        return "";
      }
      const status = normalizeStatement(itemOrEntry.source_status || "");
      const note = normalizeStatement(itemOrEntry.source_note || "");
      if (!status && !note) {
        return "";
      }
      const directStatuses = new Set([
        "direct paper definition",
        "direct paper statement",
        "direct paper formula",
        "direct source text",
        "direct source formula",
      ]);
      if (directStatuses.has(status.toLowerCase()) && !note) {
        return "";
      }
      return `${status}\n${note}`;
    }

    function isOutdated(entry, paper, theorem) {
      const current = findCurrentItem(paper, theorem);
      if (!current) {
        return false;
      }
      const reviewed = normalizeStatement(entry.lean_statement || "");
      const currentLean = normalizeStatement(current.lean_statement || "");
      const reviewedPaper = normalizeStatement(entry.paper_statement || "");
      const currentPaper = normalizeStatement(current.paper_statement || "");
      const leanOutdated = reviewed && currentLean && reviewed !== currentLean;
      const paperOutdated = reviewedPaper && currentPaper && reviewedPaper !== currentPaper;
      const sourceOutdated =
        sourceMetadataDigestInput(current) &&
        sourceMetadataDigestInput(current) !== sourceMetadataDigestInput(entry);
      return leanOutdated || paperOutdated || sourceOutdated;
    }

    function latestEntryForItem(entries, paper, theorem) {
      const related = entries.filter((entry) => entry.paper === paper && entry.theorem === theorem);
      if (!related.length) {
        return null;
      }
      byLatest(related);
      return related[0];
    }

    function sourceFileButtons(assets) {
      if (!assets || !Object.keys(assets).length) {
        return null;
      }
      const list = document.createElement("div");
      list.className = "source-actions";
      for (const key of ["pdf", "text"]) {
        const asset = assets[key];
        if (!asset || !asset.url || !asset.name) {
          continue;
        }
        const a = document.createElement("a");
        a.className = "source-link";
        a.href = asset.url;
        a.target = "_blank";
        a.rel = "noopener noreferrer";
        a.textContent = `${key === "pdf" ? "Open PDF" : "Open text"}: ${asset.name}`;
        list.appendChild(a);
      }
      return list;
    }

    function makeSourcePanel(paper) {
      const assets = paper.assets || {};
      const links = sourceFileButtons(assets);
      if (!links) {
        const empty = document.createElement("div");
        empty.style.display = "none";
        return empty;
      }
      const panel = document.createElement("section");
      panel.className = "paper-source-panel";

      const heading = document.createElement("h3");
      heading.className = "paper-source-heading";
      heading.textContent = "Paper source";
      panel.appendChild(heading);

      const hint = document.createElement("div");
      hint.className = "paper-source-subtle";
      hint.textContent = "Open source:";
      panel.appendChild(hint);
      panel.appendChild(links);
      return panel;
    }

    function surfaceAuditClass(audit) {
      if (!audit || !audit.audit_required) {
        return "";
      }
      if (audit.judgment === "needs_curation") {
        return "bad";
      }
      if (audit.needs_attention || audit.oversize) {
        return "warn";
      }
      return "ok";
    }

    function surfaceAuditLabel(audit) {
      if (!audit || !audit.audit_required) {
        return "";
      }
      if (audit.judgment === "needs_curation") {
        return "Needs curation";
      }
      if (audit.missing_required) {
        return "LLM audit required";
      }
      if (audit.stale) {
        return "LLM audit stale";
      }
      if (audit.judgment === "uncertain") {
        return "LLM audit uncertain";
      }
      if (audit.oversize) {
        return "50+ row warning";
      }
      return "LLM audit current";
    }

    function makeSurfaceAuditPanel(paper) {
      const audit = paper.surface_audit || {};
      if (!audit.audit_required && !audit.oversize && !audit.source) {
        const empty = document.createElement("div");
        empty.style.display = "none";
        return empty;
      }
      const panel = document.createElement("section");
      const cls = surfaceAuditClass(audit);
      panel.className = `surface-audit-panel ${cls}`.trim();

      const heading = document.createElement("div");
      heading.className = "surface-audit-heading";
      const title = document.createElement("span");
      title.textContent = `Review surface: ${audit.row_count || paper.items.length} rows`;
      const badge = document.createElement("span");
      badge.className = `status-pill ${cls}`.trim();
      badge.textContent = surfaceAuditLabel(audit);
      heading.appendChild(title);
      heading.appendChild(badge);
      panel.appendChild(heading);

      const body = document.createElement("div");
      body.className = "surface-audit-body";
      const notes = [];
      if (audit.oversize) {
        notes.push(`At or above ${audit.warn_threshold} rows, so this surface should be curated before broad human review.`);
      }
      if (audit.missing_required) {
        notes.push(`Above ${audit.llm_threshold} rows, so run an independent LLM pass checking that every dashboard row is paper-facing and save review_surface_llm.json.`);
      } else if (audit.stale) {
        notes.push("The saved review_surface_llm.json no longer matches the current dashboard rows.");
      } else if (audit.judgment === "needs_curation") {
        notes.push("The saved LLM audit says helper or non-paper-facing rows may be present.");
      } else if (audit.judgment === "uncertain") {
        notes.push("The saved LLM audit could not determine whether the surface is fully paper-facing.");
      } else if (audit.audit_required && audit.source) {
        notes.push(`Current surface audit loaded from ${audit.source}.`);
      }
      if (audit.reason) {
        notes.push(audit.reason);
      }
      body.textContent = notes.join(" ");
      panel.appendChild(body);
      return panel;
    }

    function assumptionAuditClass(audit) {
      if (!audit || !audit.row_count) {
        return "";
      }
      if (audit.not_paper_assumption_count) {
        return "bad";
      }
      if (audit.needs_attention) {
        return "warn";
      }
      return "ok";
    }

    function assumptionAuditLabel(audit) {
      if (!audit || !audit.row_count) {
        return "";
      }
      if (audit.not_paper_assumption_count) {
        return "Assumption mismatch";
      }
      if (audit.missing_judgment_count) {
        return "Assumption judge required";
      }
      if (audit.stale_judgment_count) {
        return "Assumption judge stale";
      }
      if (audit.uncertain_count || audit.unknown_count || audit.unlisted_rows_count || audit.missing_rows_count) {
        return "Assumptions need review";
      }
      return "Assumptions current";
    }

    function makeAssumptionAuditPanel(paper) {
      const audit = paper.assumption_audit || {};
      if (!audit.row_count && !audit.configured_count && !audit.needs_attention) {
        const empty = document.createElement("div");
        empty.style.display = "none";
        return empty;
      }
      const panel = document.createElement("section");
      const cls = assumptionAuditClass(audit);
      panel.className = `surface-audit-panel ${cls}`.trim();

      const heading = document.createElement("div");
      heading.className = "surface-audit-heading";
      const title = document.createElement("span");
      title.textContent = `Paper assumptions: ${audit.row_count || 0} row${audit.row_count === 1 ? "" : "s"}`;
      const badge = document.createElement("span");
      badge.className = `status-pill ${cls}`.trim();
      badge.textContent = assumptionAuditLabel(audit);
      heading.appendChild(title);
      heading.appendChild(badge);
      panel.appendChild(heading);

      const body = document.createElement("div");
      body.className = "surface-audit-body";
      const notes = [];
      if (audit.unlisted_rows_count) {
        notes.push("Some assumption-like declarations are not listed in status.json review_surface.assumption_names.");
      }
      if (audit.missing_rows_count) {
        notes.push("Some configured assumptions are missing from the dashboard rows.");
      }
      if (audit.missing_judgment_count) {
        notes.push("Run the source-assumption judge and save assumption_match_llm.json.");
      } else if (audit.stale_judgment_count) {
        notes.push("The saved assumption_match_llm.json no longer matches the current assumptions.");
      } else if (audit.not_paper_assumption_count) {
        notes.push("The assumption judge says at least one row is a proof assumption rather than a paper/source model assumption.");
      } else if (audit.uncertain_count || audit.unknown_count) {
        notes.push("The assumption judge could not confirm every listed assumption.");
      } else if (audit.row_count) {
        notes.push("Every listed assumption has a current source-assumption judgment.");
      }
      body.textContent = notes.join(" ");
      panel.appendChild(body);
      return panel;
    }

    function refreshSummary(entries, statusRows) {
      const summary = document.getElementById("summary");
      if (!state.papers.length) {
        summary.textContent = "No theorem rows.";
        return;
      }

      const allItems = allItemsCount();
      let reviewed = 0;
      let stale = 0;
      let mismatch = 0;
      let needsAttention = 0;

      if (statusRows && statusRows.length) {
        reviewed = statusRows.filter((row) => row.has_review).length;
        stale = statusRows.filter((row) => row.lean_stale || row.paper_stale || row.source_stale).length;
        mismatch = statusRows.filter((row) => row.has_review && reviewJudgment(row) === "mismatch").length;
        needsAttention = statusRows.filter((row) => row.needs_attention || reviewJudgment(row) === "mismatch").length;
      } else {
        for (const paper of state.papers) {
          for (const item of paper.items) {
            const latest = latestEntryForItem(entries, paper.name, item.name);
            if (!latest) {
              continue;
            }
            reviewed++;
            if (isOutdated(latest, paper.name, item.name)) {
              stale++;
            }
            const judgment = reviewJudgment(latest);
            if (judgment === "mismatch") {
              mismatch++;
            }
            if (judgment === "mismatch" || judgment === "uncertain") {
              needsAttention++;
            }
          }
        }
        const unreviewed = allItems - reviewed;
        needsAttention = stale + unreviewed + needsAttention;
      }

      const unreviewed = allItems - reviewed;
      summary.textContent = `${reviewed}/${allItems} items reviewed · ${stale} stale snapshot · ${needsAttention} need action`;
      document.getElementById("cardReviewed").textContent = `${reviewed}/${allItems}`;
      document.getElementById("cardAttention").textContent = String(needsAttention);
      document.getElementById("cardStale").textContent = String(stale);
      document.getElementById("cardMismatch").textContent = String(mismatch);
    }

    function reviewHistory(entries, paper, theorem) {
      const related = entries.filter((entry) => entry.paper === paper && entry.theorem === theorem);
      if (!related.length) return "<div class='small muted'>No reviews yet.</div>";
      byLatest(related);
      const lines = [];
      for (const e of related.slice(0, 5)) {
        const judgment = reviewJudgment(e);
        const cls = judgment === "matches" ? "ok" : judgment === "mismatch" ? "bad" : "warn";
        const status = judgment === "matches"
          ? "matches"
          : judgment === "mismatch"
            ? "does not match"
            : "uncertain";
        const outdated = isOutdated(e, paper, theorem);
        const outdatedMark = outdated
          ? " <span class='warn'>(statement snapshot is out of date)</span>"
          : "";
        const note = e.notes ? ` — ${escapeHtml(e.notes)}` : "";
        lines.push(
          `<div class='history-entry'><span class='small'><span class='${cls}'>${status}</span> by ${escapeHtml(e.user || "")} (${escapeHtml(e.timestamp || "")})${outdatedMark}${note}</span></div>`
        );
      }
      return `<div class='history'><div class='small'><strong>Latest checks</strong></div>${lines.join("")}</div>`;
    }

    function validatorLabel(entry) {
      if (!entry || !entry.validator) return "";
      const type = entry.validator_type ? ` (${entry.validator_type})` : "";
      return `${entry.validator}${type}`;
    }

    function validatorSummary(rowStatus) {
      const validators = rowStatus && Array.isArray(rowStatus.validators) ? rowStatus.validators : [];
      if (!validators.length) return "Validators: none recorded";
      const labels = [];
      const seen = new Set();
      for (const entry of validators) {
        const label = validatorLabel(entry);
        if (!label || seen.has(label)) continue;
        seen.add(label);
        labels.push(label);
      }
      return `Validators: ${labels.join(", ")}`;
    }

    function validatorDetails(rowStatus) {
      const validators = rowStatus && Array.isArray(rowStatus.validators) ? rowStatus.validators : [];
      if (!validators.length) return "";
      return validators.map((entry) => {
        const label = validatorLabel(entry);
        const judgment = entry.judgment ? ` ${entry.judgment}` : "";
        const timestamp = entry.validated_at ? ` @ ${entry.validated_at}` : "";
        const stale = entry.stale ? " (stale)" : "";
        const comment = entry.comment ? `: ${entry.comment}` : "";
        return `${label}${judgment}${timestamp}${stale}${comment}`.trim();
      }).join("\\n");
    }

    function rowElementId(paper, theorem) {
      return `${safeId(paper)}_${safeId(theorem)}`;
    }

    function selectedReviewJudgment(rowId) {
      const match = document.getElementById(`match-${rowId}`);
      const mismatch = document.getElementById(`mismatch-${rowId}`);
      const uncertain = document.getElementById(`uncertain-${rowId}`);
      if (match && match.checked) {
        return "matches";
      }
      if (mismatch && mismatch.checked) {
        return "mismatch";
      }
      if (uncertain && uncertain.checked) {
        return "uncertain";
      }
      return "";
    }

    function matchesValueForJudgment(judgment) {
      if (judgment === "matches") {
        return true;
      }
      if (judgment === "mismatch") {
        return false;
      }
      return null;
    }

    function reviewPayload(paper, item, judgment) {
      const rowId = rowElementId(paper, item.name);
      const note = document.getElementById(`note-${rowId}`);
      const user = document.getElementById("userHandle").value.trim() || state.user;
      return {
        paper: paper,
        theorem: item.name,
        user: user,
        judgment: judgment,
        matches: matchesValueForJudgment(judgment),
        notes: note ? note.value.trim() : "",
        lean_statement: item.lean_statement,
        paper_statement: item.paper_statement,
        agent_statement: item.agent_statement,
        source_status: item.source_status || "",
        source_note: item.source_note || "",
      };
    }

    async function postReviewPayload(payload) {
      const response = await fetch("/api/reviews", {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify(payload),
      });
      const data = await response.json();
      if (!response.ok) {
        throw new Error(data.error || "Failed to save.");
      }
      return data;
    }

    async function saveAllSelectedReviews() {
      const btn = document.getElementById("saveAllReviews");
      const status = document.getElementById("saveAllStatus");
      const selected = [];
      for (const row of document.querySelectorAll("tr[data-paper][data-theorem]")) {
        const paper = row.dataset.paper;
        const theorem = row.dataset.theorem;
        const rowId = rowElementId(paper, theorem);
        const judgment = selectedReviewJudgment(rowId);
        if (!judgment) {
          continue;
        }
        const item = findCurrentItem(paper, theorem);
        if (!item) {
          continue;
        }
        selected.push({ paper, theorem, item, judgment, rowId });
      }
      if (!selected.length) {
        status.textContent = "No selected review decisions.";
        status.className = "save-status small warn";
        return;
      }
      btn.disabled = true;
      btn.textContent = "Saving...";
      status.textContent = `Saving ${selected.length} review${selected.length === 1 ? "" : "s"}...`;
      status.className = "save-status small muted";
      let saved = 0;
      let failed = 0;
      for (const entry of selected) {
        const rowStatus = document.getElementById(`save-status-${entry.rowId}`);
        if (rowStatus) {
          rowStatus.textContent = "";
          rowStatus.className = "save-status small muted";
        }
        try {
          await postReviewPayload(reviewPayload(entry.paper, entry.item, entry.judgment));
          saved++;
          if (rowStatus) {
            rowStatus.textContent = "Saved";
            rowStatus.className = "save-status small ok";
          }
        } catch (err) {
          failed++;
          if (rowStatus) {
            rowStatus.textContent = err.message || "Save failed";
            rowStatus.className = "save-status small bad";
          }
        }
      }
      await refreshReviews();
      status.textContent = failed
        ? `Saved ${saved}; ${failed} failed.`
        : `Saved ${saved} review${saved === 1 ? "" : "s"}.`;
      status.className = failed ? "save-status small bad" : "save-status small ok";
      btn.disabled = false;
      btn.textContent = "Save all review";
    }

    function isDirectSourceStatus(status) {
      const normalized = String(status || "").trim().toLowerCase();
      return [
        "direct paper definition",
        "direct paper statement",
        "direct paper formula",
        "direct source text",
        "direct source formula",
      ].includes(normalized);
    }

    function makeSourceProvenancePanel(item) {
      const status = String(item.source_status || "").trim();
      const note = String(item.source_note || "").trim();
      if (!status && !note) {
        return null;
      }
      const panel = document.createElement("div");
      panel.className = `source-provenance${isDirectSourceStatus(status) && !note ? " direct" : ""}`;
      const label = document.createElement("span");
      label.className = "source-provenance-label";
      label.textContent = status || "Source note";
      panel.appendChild(label);
      if (note) {
        panel.appendChild(document.createTextNode(note));
      }
      return panel;
    }

    function makeRow(paper, item) {
      const row = document.createElement("tr");
      row.dataset.paper = paper;
      row.dataset.theorem = item.name;
      row.dataset.kind = item.kind || "";
      row.dataset.isAssumption = item.is_assumption ? "true" : "false";
      row.dataset.sliceKey = sliceKey(paper, item.slice_id || "all");
      row.dataset.sliceId = item.slice_id || "all";
      row.dataset.sliceTitle = item.slice_title || "All statements";
      row.dataset.searchText = `${paper} ${item.kind || ""} ${item.name} ${item.paper_statement || ""} ${item.lean_statement || ""} ${item.source_status || ""} ${item.source_note || ""}`.toLowerCase();
      const itemCell = document.createElement("td");
      const itemShell = document.createElement("div");
      itemShell.className = "review-item";
      const mainCell = document.createElement("div");
      mainCell.className = "review-main";

      const paperCell = document.createElement("section");
      paperCell.className = "review-section col-paper";
      const paperHtml = renderPaperStatement(item.paper_statement);
      if (item.paper_statement_image_url) {
        paperCell.appendChild(makeReviewSectionLabel("Paper source image"));
        const image = document.createElement("img");
        image.className = "paper-statement-image";
        image.src = item.paper_statement_image_url;
        image.alt = `Rendered source statement for ${paper}.${item.name}`;
        image.loading = "lazy";
        paperCell.appendChild(image);
        paperCell.appendChild(
          makeStatementBox("Extracted text fallback", item.paper_statement || "", {
            html: paperHtml,
            previewLength: 160,
          })
        );
      } else {
        paperCell.appendChild(
          makeStatementBox("Paper source statement", item.paper_statement, {
            html: paperHtml,
            previewLength: (item.paper_statement || "").length > 650 ? 180 : 220,
            open: true,
          })
        );
      }

      const leanCell = document.createElement("section");
      leanCell.className = "review-section col-lean";
      const interfaceSource = String(item.interface_source || "").trim();
      const leanStatement = String(item.lean_statement || "").trim();
      if (interfaceSource && (item.kind === "def" || item.kind === "abbrev")) {
        leanCell.appendChild(
          makeStatementBox(item.kind === "def" ? "Lean definition code" : "Lean alias code", interfaceSource, {
            html: `<code>${escapeHtml(prettyLeanStatement(interfaceSource))}</code>`,
            previewLength: 170,
            open: true,
          })
        );
      }
      if (!interfaceSource || normalizeStatement(interfaceSource) !== normalizeStatement(leanStatement)) {
        leanCell.appendChild(
          makeStatementBox("Expanded Lean statement", item.lean_statement, {
            html: `<code>${escapeHtml(prettyLeanStatement(item.lean_statement))}</code>`,
            previewLength: 170,
            open: true,
          })
        );
      }

      const agentCell = document.createElement("section");
      agentCell.className = "review-section col-agent agent-column";
      const agentHeader = document.createElement("div");
      agentHeader.className = "small muted";
      agentHeader.textContent =
        "LLM Lean-to-TeX draft";
      const agentText = document.createElement("div");
      agentText.className = "agent-statement";
      agentText.appendChild(
        makeStatementBox("Lean-to-TeX draft", item.agent_statement || "", {
          html: renderTexDraft(item.agent_statement || ""),
          previewLength: 130,
          open: true,
        })
      );
      agentText.style.margin = "0";
      agentCell.appendChild(agentHeader);
      agentCell.appendChild(agentText);
      agentCell.appendChild(makeLlmJudgePanel(item));
      if (item.is_assumption || item.llm_assumption_judgment) {
        agentCell.appendChild(makeAssumptionJudgePanel(item));
      }

      const reviewCell = document.createElement("aside");
      reviewCell.className = "review-controls col-review";
      const rowId = rowElementId(paper, item.name);

      const statusLine = document.createElement("div");
      statusLine.className = "status-line";
      const statusBadge = document.createElement("span");
      statusBadge.className = "status-pill";
      statusBadge.id = `status-${rowId}`;
      statusBadge.textContent = "Unreviewed";
      const staleBadge = document.createElement("span");
      staleBadge.className = "status-pill warn";
      staleBadge.id = `stale-${rowId}`;
      staleBadge.style.display = "none";
      statusLine.appendChild(statusBadge);
      statusLine.appendChild(staleBadge);

      const validatorsLine = document.createElement("div");
      validatorsLine.className = "small muted";
      validatorsLine.id = `validators-${rowId}`;
      validatorsLine.textContent = "Validators: none recorded";

      const decision = document.createElement("fieldset");
      decision.className = "review-decision";
      const decisionLegend = document.createElement("legend");
      decisionLegend.textContent = "Review decision";
      decision.appendChild(decisionLegend);

      const decisionName = `decision-${rowId}`;
      const matchLabel = document.createElement("label");
      matchLabel.className = "review-decision-option";
      const matchRadio = document.createElement("input");
      matchRadio.type = "radio";
      matchRadio.name = decisionName;
      matchRadio.value = "match";
      matchRadio.dataset.paper = paper;
      matchRadio.dataset.theorem = item.name;
      matchRadio.id = `match-${rowId}`;
      matchLabel.appendChild(matchRadio);
      matchLabel.appendChild(document.createTextNode("Matches paper statement"));
      decision.appendChild(matchLabel);

      const mismatchLabel = document.createElement("label");
      mismatchLabel.className = "review-decision-option";
      const mismatchRadio = document.createElement("input");
      mismatchRadio.type = "radio";
      mismatchRadio.name = decisionName;
      mismatchRadio.value = "mismatch";
      mismatchRadio.dataset.paper = paper;
      mismatchRadio.dataset.theorem = item.name;
      mismatchRadio.id = `mismatch-${rowId}`;
      mismatchLabel.appendChild(mismatchRadio);
      mismatchLabel.appendChild(document.createTextNode("Mismatch"));
      decision.appendChild(mismatchLabel);

      const uncertainLabel = document.createElement("label");
      uncertainLabel.className = "review-decision-option";
      const uncertainRadio = document.createElement("input");
      uncertainRadio.type = "radio";
      uncertainRadio.name = decisionName;
      uncertainRadio.value = "uncertain";
      uncertainRadio.dataset.paper = paper;
      uncertainRadio.dataset.theorem = item.name;
      uncertainRadio.id = `uncertain-${rowId}`;
      uncertainLabel.appendChild(uncertainRadio);
      uncertainLabel.appendChild(document.createTextNode("Uncertain"));
      decision.appendChild(uncertainLabel);

      const text = document.createElement("textarea");
      text.className = "row-note";
      text.placeholder = "Reviewer notes";
      text.dataset.paper = paper;
      text.dataset.theorem = item.name;
      text.id = `note-${rowId}`;

      const btn = document.createElement("button");
      btn.className = "btn";
      btn.type = "button";
      btn.textContent = "Save review";
      const saveStatus = document.createElement("span");
      saveStatus.className = "save-status small muted";
      saveStatus.id = `save-status-${rowId}`;
      btn.addEventListener("click", async () => {
        const judgment = selectedReviewJudgment(rowId);
        if (!judgment) {
          saveStatus.textContent = "Choose Matches, Mismatch, or Uncertain.";
          saveStatus.className = "save-status small bad";
          return;
        }
        btn.disabled = true;
        btn.textContent = "Saving...";
        saveStatus.textContent = "";
        try {
          await postReviewPayload(reviewPayload(paper, item, judgment));
          saveStatus.textContent = "Saved";
          saveStatus.className = "save-status small ok";
          await refreshReviews();
        } catch (err) {
          saveStatus.textContent = err.message || "Save failed";
          saveStatus.className = "save-status small bad";
        } finally {
          btn.disabled = false;
          btn.textContent = "Save review";
        }
      });

      const status = document.createElement("div");
      status.className = "history";
      status.dataset.paper = paper;
      status.dataset.theorem = item.name;

      const header = document.createElement("div");
      header.className = "paper-title";
      const propSpecLabel = item.is_proposition_spec
        ? item.proposition_spec_role === "source_definition"
          ? " · source proposition definition (not a proof)"
          : item.proposition_spec_role === "source_assumption"
            ? " · proposition assumption (not a proof)"
            : item.proposition_spec_role === "proof_routed"
              ? ` · proposition specification; proof row ${item.proposition_spec_proof || "missing"}`
              : " · unproved proposition specification"
        : "";
      header.textContent = `${item.kind} ${item.name}${propSpecLabel}`;
      const sliceMeta = document.createElement("div");
      sliceMeta.className = "slice-meta";
      const lineText = item.line_number ? `line ${item.line_number}` : "line unavailable";
      sliceMeta.textContent = `${item.slice_title || "All statements"} · ${lineText}`;

      const sourceBadge = document.createElement("span");
      sourceBadge.className = `status-pill ${isDirectSourceStatus(item.source_status) && !item.source_note ? "ok" : item.source_status || item.source_note ? "warn" : ""}`;
      sourceBadge.textContent = item.is_proposition_spec && item.proposition_spec_role === "unproved_spec"
        ? "Unproved specification"
        : item.is_assumption
        ? "Paper assumption"
        : item.source_status || "Source status not labeled";

      reviewCell.appendChild(header);
      reviewCell.appendChild(sliceMeta);
      reviewCell.appendChild(sourceBadge);
      reviewCell.appendChild(statusLine);
      reviewCell.appendChild(validatorsLine);
      reviewCell.appendChild(decision);
      reviewCell.appendChild(text);
      reviewCell.appendChild(document.createElement("br"));
      reviewCell.appendChild(btn);
      reviewCell.appendChild(saveStatus);
      reviewCell.appendChild(status);

      // Populate with existing review history
      const sourcePanel = makeSourceProvenancePanel(item);
      if (sourcePanel) {
        mainCell.appendChild(sourcePanel);
      }
      mainCell.appendChild(paperCell);
      mainCell.appendChild(leanCell);
      mainCell.appendChild(agentCell);
      itemShell.appendChild(mainCell);
      itemShell.appendChild(reviewCell);
      itemCell.appendChild(itemShell);
      row.appendChild(itemCell);
      return { row, status };
    }

    function updateStatusBadges() {
      for (const row of document.querySelectorAll("tr[data-paper][data-theorem]")) {
        const paper = row.dataset.paper;
        const theorem = row.dataset.theorem;
        const rowStatus = statusFor(paper, theorem);
        const rowId = `${safeId(paper)}_${safeId(theorem)}`;
        const badge = document.getElementById(`status-${rowId}`);
        const stale = document.getElementById(`stale-${rowId}`);
        const label = statusLabel(rowStatus);
        const judgment = reviewJudgment(rowStatus);
        row.dataset.status = label.toLowerCase();
        row.dataset.needsAttention = rowStatus && rowStatus.needs_attention ? "true" : "false";
        row.dataset.latestJudgment = judgment;
        row.dataset.latestMatches = judgment === "mismatch" ? "false" : "true";
        row.dataset.hasReview = rowStatus && rowStatus.has_review ? "true" : "false";
        row.dataset.isStale = rowStatus && (rowStatus.lean_stale || rowStatus.paper_stale || rowStatus.source_stale) ? "true" : "false";
        if (badge) {
          badge.textContent = label;
          badge.className = `status-pill ${statusClass(rowStatus)}`.trim();
        }
        if (stale) {
          const reason = staleReason(rowStatus);
          stale.textContent = reason;
          stale.style.display = reason ? "" : "none";
        }
        const validators = document.getElementById(`validators-${rowId}`);
        if (validators) {
          validators.textContent = validatorSummary(rowStatus);
          validators.title = validatorDetails(rowStatus);
        }
      }
    }

    function updatePaperProgress() {
      const statusRows = state.statusRows || [];
      for (const paper of state.papers) {
        const paperRows = statusRows.filter((row) => row.paper === paper.name);
        const total = paper.items.length;
        const reviewed = paperRows.filter((row) => row.has_review).length;
        const attention = paperRows.filter((row) => row.needs_attention || row.latest_matches === false).length;
        const node = document.querySelector(`[data-paper-progress="${paper.name}"]`);
        if (node) {
          node.textContent = `${reviewed}/${total} reviewed; ${attention} need action`;
        }
      }
    }

    function applyFilters() {
      const query = (document.getElementById("searchBox").value || "").trim().toLowerCase();
      const statusFilter = document.getElementById("statusFilter").value;
      const sliceFilter = document.getElementById("sliceFilter").value || "all";
      let visibleRows = 0;
      for (const block of document.querySelectorAll(".paper-block")) {
        let visibleInBlock = 0;
        for (const row of block.querySelectorAll("tr[data-paper][data-theorem]")) {
          const matchesSearch = !query || (row.dataset.searchText || "").includes(query);
          const matchesSlice = sliceFilter === "all" || row.dataset.sliceKey === sliceFilter;
          let matchesStatus = true;
          if (statusFilter === "attention") {
            matchesStatus = row.dataset.needsAttention === "true" || row.dataset.latestMatches === "false";
          } else if (statusFilter === "unreviewed") {
            matchesStatus = row.dataset.hasReview !== "true";
          } else if (statusFilter === "stale") {
            matchesStatus = row.dataset.isStale === "true";
          } else if (statusFilter === "mismatch") {
            matchesStatus = row.dataset.latestJudgment === "mismatch";
          } else if (statusFilter === "uncertain") {
            matchesStatus = row.dataset.latestJudgment === "uncertain";
          } else if (statusFilter === "reviewed") {
            matchesStatus = row.dataset.hasReview === "true";
          }
          const visible = matchesSearch && matchesSlice && matchesStatus;
          row.classList.toggle("is-hidden", !visible);
          if (visible) {
            visibleInBlock++;
            visibleRows++;
          }
        }
        block.style.display = visibleInBlock ? "" : "none";
      }
      document.getElementById("emptyFilter").style.display = visibleRows ? "none" : "block";
    }

    async function refreshReviews() {
      let entries = [];
      let statusRows = [];
      try {
        const [reviewResponse, statusResponse] = await Promise.all([
          fetch("/api/reviews"),
          fetch("/api/status"),
        ]);
        if (reviewResponse.ok) {
          const payload = await reviewResponse.json();
          entries = payload.reviews || [];
        }
        if (statusResponse.ok) {
          const statusPayload = await statusResponse.json();
          statusRows = statusPayload.status || [];
        }
      } catch (_err) {
        entries = state.reviews || [];
        statusRows = state.statusRows || [];
      }
      state.reviews = entries;
      state.statusRows = statusRows;
      refreshSummary(entries, statusRows);
      const total = entries.length;
      document.getElementById("count").textContent = `Reviews logged: ${total}`;
      updateStatusBadges();
      updatePaperProgress();

      const statusNodes = document.querySelectorAll(".history[data-paper][data-theorem]");
      for (const node of statusNodes) {
        const theorem = node.dataset.theorem;
        const paper = node.dataset.paper;
        node.innerHTML = reviewHistory(entries, paper, theorem);
        // Prefill for current user if there is a latest entry
        const user = document.getElementById("userHandle").value.trim() || state.user;
        const mine = entries.filter(
          (entry) => entry.paper === paper && entry.theorem === theorem && entry.user === user
        );
        if (mine.length) {
          mine.sort((a, b) => (a.timestamp < b.timestamp ? 1 : -1));
          const latest = mine[0];
          const rowId = `${safeId(paper)}_${safeId(theorem)}`;
          const match = document.getElementById(`match-${rowId}`);
          const mismatch = document.getElementById(`mismatch-${rowId}`);
          const uncertain = document.getElementById(`uncertain-${rowId}`);
          const ta = document.getElementById(`note-${rowId}`);
          const judgment = reviewJudgment(latest);
          if (match) {
            match.checked = judgment === "matches";
          }
          if (mismatch) {
            mismatch.checked = judgment === "mismatch";
          }
          if (uncertain) {
            uncertain.checked = judgment === "uncertain";
          }
          if (ta) {
            ta.value = latest.notes || "";
          }
        }
      }
      applyFilters();
    }

    function render() {
      const container = document.getElementById("containers");
      document.getElementById("logPath").textContent = `Log file: ${state.logPath}`;
      container.textContent = "";
      const data = state.papers;
      if (!data.length) {
        container.textContent = "No paper interfaces found.";
        return;
      }
      populateSliceFilter();
      for (const paper of data) {
        const block = document.createElement("details");
        block.className = "paper-block";
        block.open = data.length === 1 || paper.items.length <= 80;
        block.classList.add("paper-details");
        const summary = document.createElement("summary");
        const header = document.createElement("div");
        header.className = "paper-header";
        const heading = document.createElement("h2");
        heading.textContent = `${paper.name} — ${paper.title}`;
        const progress = document.createElement("div");
        progress.className = "paper-progress";
        progress.dataset.paperProgress = paper.name;
        progress.textContent = `0/${paper.items.length} reviewed; ${paper.items.length} rows`;
        header.appendChild(heading);
        header.appendChild(progress);
        summary.appendChild(header);
        block.appendChild(summary);
        block.appendChild(makeSurfaceAuditPanel(paper));
        block.appendChild(makeAssumptionAuditPanel(paper));
        block.appendChild(makeSourcePanel(paper));
        const table = document.createElement("table");
        const head = document.createElement("thead");
        head.innerHTML =
          "<tr><th>Paper statement, expanded Lean statement, LLM checks, and review</th></tr>";
        table.appendChild(head);
        const body = document.createElement("tbody");
        for (const item of paper.items) {
          const rowInfo = makeRow(paper.name, item);
          body.appendChild(rowInfo.row);
        }
        table.appendChild(body);
        const tableWrap = document.createElement("div");
        tableWrap.className = "table-wrap";
        tableWrap.appendChild(table);
        block.appendChild(tableWrap);
        container.appendChild(block);
      }
      refreshReviews();
      typesetMath();
    }

    document.getElementById("userHandle").addEventListener("change", refreshReviews);
    document.getElementById("searchBox").addEventListener("input", applyFilters);
    document.getElementById("statusFilter").addEventListener("change", applyFilters);
    document.getElementById("sliceFilter").addEventListener("change", applyFilters);
    document.getElementById("hideAgentDraft").addEventListener("change", (event) => {
      document.body.classList.toggle("hide-agent", event.target.checked);
    });
    document.getElementById("saveAllReviews").addEventListener("click", saveAllSelectedReviews);
    const mathjaxTag = document.getElementById("mathjax-script");
    if (mathjaxTag) {
      mathjaxTag.addEventListener("load", typesetMath);
    }
    document.addEventListener("DOMContentLoaded", render);
  </script>
</body>
</html>
""".strip()


def render_static_html(papers: list[dict[str, Any]], user: str, log_path: str) -> str:
    payload = json.dumps(papers)
    return (
        HTML_PAGE.replace("__USER__", json.dumps(user))
        .replace("__LOG_PATH__", json.dumps(log_path))
        .replace("__PAPERS__", payload)
        .replace("{user}", html.escape(user, quote=True))
    )


def stale_review_summary(
    paper: str | None, log_file: Path | None, slice_filter: str | None = None
) -> dict[str, list[dict[str, Any]] | dict[str, Any]]:
    """Return stale/unreviewed buckets plus overall status for quick checks."""

    papers = gather_paper_data(paper, slice_filter, render_images=False)
    if log_file is not None:
        reviews = read_log_entries(log_file, paper)
    elif paper:
        reviews = read_all_log_entries(paper, None)
    else:
        reviews = read_all_log_entries(None, None)
    rows = build_review_status(papers, reviews)
    buckets = stale_review_rows(rows)
    return {
        "rows": rows,
        "totals": status_totals(rows),
        "surface_audits": surface_audit_rows(papers),
        "statement_audits": statement_audit_rows(papers),
        "paper_coverage_audits": paper_coverage_audit_rows(papers),
        "assumption_audits": merge_hidden_premise_audit_rows(assumption_audit_rows(papers), paper),
        "stale": buckets["stale"],
        "unreviewed": buckets["unreviewed"],
        "mismatch": buckets["mismatch"],
    }


def print_surface_audit_warnings(rows: list[dict[str, Any]], label: str) -> bool:
    """Print paper-level review-surface warnings and return whether any need attention."""

    warnings = [row for row in rows if row.get("has_warning") or row.get("needs_attention")]
    if not warnings:
        return False
    needs_attention = any(row.get("needs_attention") for row in warnings)
    print(f"\nReview-surface audit warnings for {label}:")
    for row in warnings:
        paper = row.get("paper") or "unknown paper"
        count = int(row.get("row_count") or 0)
        reasons: list[str] = []
        if row.get("oversize"):
            reasons.append(
                f"{count} rows is at or above the {row.get('warn_threshold')} row warning threshold"
            )
        if row.get("missing_required"):
            reasons.append(
                f"{count} rows is above {row.get('llm_threshold')} and needs review_surface_llm.json"
            )
        if row.get("stale"):
            reasons.append("the saved review_surface_llm.json audit is stale")
        if row.get("prompt_version_stale"):
            reasons.append(
                "the saved review_surface_llm.json prompt version is stale "
                f"({row.get('prompt_version') or 'missing'})"
            )
        if row.get("metadata_missing"):
            reasons.append("review_surface_llm.json is missing validator or validated_at success metadata")
        if row.get("judgment") == "needs_curation":
            reasons.append("the LLM audit says the surface needs curation")
        if row.get("judgment") == "uncertain":
            reasons.append("the LLM audit is uncertain")
        if row.get("unknown_judgment"):
            reasons.append(
                f"the LLM audit judgment `{row.get('judgment') or 'missing'}` is not recognized"
            )
        if not reasons:
            reasons.append("the review surface needs attention")
        print(f" - {paper}: {'; '.join(reasons)}.")
        if row.get("reason"):
            print(f"   audit note: {row['reason']}")
    print(
        "For papers above 30 dashboard rows, run a no-paper-context LLM pass that "
        "checks whether every row is genuinely paper-facing, then save "
        "review_surface_llm.json."
    )
    return needs_attention


def _format_name_sample(names: list[str], limit: int = 8) -> str:
    """Format a compact sample of dashboard row names."""

    if not names:
        return ""
    shown = ", ".join(f"`{name}`" for name in names[:limit])
    if len(names) > limit:
        shown += f", ... {len(names) - limit} more"
    return shown


def print_statement_audit_warnings(rows: list[dict[str, Any]], label: str) -> bool:
    """Print paper-level statement-translation audit warnings."""

    warnings = [row for row in rows if row.get("needs_attention")]
    if not warnings:
        return False
    print(f"\nStatement-translation audit warnings for {label}:")
    for row in warnings:
        paper = row.get("paper") or "unknown paper"
        reasons: list[str] = []
        if row.get("missing_draft_count"):
            reasons.append(f"{row['missing_draft_count']} missing Lean-to-TeX draft(s)")
        if row.get("stale_draft_count"):
            reasons.append(f"{row['stale_draft_count']} stale Lean-to-TeX draft(s)")
        if row.get("missing_judgment_count"):
            reasons.append(f"{row['missing_judgment_count']} missing statement-judge row(s)")
        if row.get("stale_judgment_count"):
            reasons.append(f"{row['stale_judgment_count']} stale statement-judge row(s)")
        if row.get("missing_obligation_ledger_count"):
            reasons.append(
                f"{row['missing_obligation_ledger_count']} incomplete semantic obligation ledger(s)"
            )
        if row.get("unresolved_mismatch_count"):
            reasons.append(f"{row['unresolved_mismatch_count']} unresolved mismatch judgment(s)")
        if row.get("conditional_boundary_count"):
            reasons.append(
                f"{row['conditional_boundary_count']} visible-premise boundary judgment(s)"
            )
        if row.get("uncertain_count"):
            reasons.append(f"{row['uncertain_count']} uncertain judgment(s)")
        if row.get("unknown_count"):
            reasons.append(f"{row['unknown_count']} unknown judgment value(s)")
        if row.get("all_uncertain"):
            reasons.append("all rows are uncertain, suggesting a source-statement extraction or parser issue")
        if not reasons:
            reasons.append("statement audit needs attention")
        print(f" - {paper}: {'; '.join(str(reason) for reason in reasons)}.")
        if row.get("all_uncertain"):
            print(
                "   fix the extracted source statements or parser first; do not "
                "leave a paper-wide parser failure as row-by-row uncertainty."
            )
        samples: list[str] = []
        for key, label_text in [
            ("unresolved_mismatch", "unresolved mismatch"),
            ("conditional_boundary", "visible-premise boundary"),
            ("uncertain", "uncertain"),
            ("stale_judgment", "stale judgment"),
            ("missing_obligation_ledger", "missing obligation ledger"),
            ("stale_draft", "stale draft"),
            ("missing_judgment", "missing judgment"),
            ("missing_draft", "missing draft"),
            ("unknown", "unknown"),
        ]:
            sample = _format_name_sample(list(row.get(key) or []))
            if sample:
                samples.append(f"{label_text}: {sample}")
        for sample in samples[:3]:
            print(f"   {sample}")
    print(
        "At statement-review boundaries, regenerate lean_to_tex_llm.json from the "
        "Lean statements alone, preserving every visible binder, hypothesis, "
        "domain condition, named predicate/wrapper application, "
        "equivalence/implication direction, conclusion, and input premise. "
        "Then regenerate statement_match_llm.json from the complete original "
        "paper theorem/definition/formula text and that translation. The judge "
        "should scrutinize every input semantically against the paper source "
        "model, expanding named predicates/wrappers when needed. It must not "
        "approve by theorem label, phrase overlap, or source-looking Lean name. "
        "Mark mismatch or uncertain for omitted subparts, extra non-source "
        "conditions, hidden strengthening inside named predicates, broad "
        "aggregate rows, source-row/certificate/replay/process/bridge packages, or "
        "weakened/strengthened statements. A matches judgment must enumerate "
        "source and Lean parameter/assumption/conclusion atoms, reference every "
        "machine-generated Lean signature atom exactly once, and align every "
        "source conclusion and Lean input by semantic "
        "equivalence or a stated implication; names are routing only. If all rows are uncertain, treat that "
        "as a likely source extraction problem and fix the source map before "
        "accepting row-level judgments. A clean statement audit is still row-local; "
        "run `python3 scripts/review_dashboard.py --paper <paper> "
        "--assumption-precheck` or the combined `--precheck` path before treating "
        "theorem premises as certified."
    )
    return True


def print_statement_audit_status(paper: str | None, slice_filter: str | None = None) -> bool:
    """Print only statement-translation audit diagnostics."""

    papers = gather_paper_data(paper, slice_filter, render_images=False)
    rows = statement_audit_rows(papers)
    label = paper or "all papers"
    if slice_filter:
        label = f"{label} slice {slice_filter}"
    has_attention = print_statement_audit_warnings(rows, label)
    if has_attention:
        return True
    total_rows = sum(int(row.get("row_count") or 0) for row in rows)
    total_drafts = sum(int(row.get("draft_count") or 0) for row in rows)
    total_judgments = sum(int(row.get("judgment_count") or 0) for row in rows)
    total_conditional_boundaries = sum(
        int(row.get("conditional_boundary_count") or 0) for row in rows
    )
    boundary_note = (
        f", {total_conditional_boundaries} strict mismatch row(s) accepted as visible-premise boundaries"
        if total_conditional_boundaries
        else ", no missing/stale/flagged items"
    )
    print(
        f"Statement-translation audits for {label} are current: "
        f"{total_rows} row(s), {total_drafts} Lean-to-TeX draft(s), "
        f"{total_judgments} statement-judge row(s){boundary_note}."
    )
    print(
        "This is only the row-local statement match lane. Before treating these "
        "rows as certified paper targets, also run "
        "`python3 scripts/review_dashboard.py --paper <paper> --assumption-precheck` "
        "or the combined `--precheck` path to verify theorem-premise provenance."
    )
    return False


def print_paper_coverage_audit_warnings(
    rows: list[dict[str, Any]], label: str, *, source_to_lean: bool = False
) -> bool:
    """Print paper-level source-statement coverage audit warnings."""

    warnings = [
        row
        for row in rows
        if row.get("needs_attention")
        or (source_to_lean and row.get("source_to_lean_needs_attention"))
    ]
    if not warnings:
        return False
    if source_to_lean:
        print(f"\nSource-to-Lean audit warnings for {label}:")
    else:
        print(f"\nPaper-coverage audit warnings for {label}:")
    for row in warnings:
        paper = row.get("paper") or "unknown paper"
        reasons: list[str] = []
        if row.get("missing_inventory"):
            reasons.append("source-statement inventory is required but empty")
        if row.get("unresolved_statement_map"):
            reasons.append(
                "audit/paper_statement_map.json exists but has no resolvable tracked source statements"
            )
        if row.get("inventory_is_scaffold"):
            reasons.append(
                "audit/paper_statement_map.json is still dashboard-seeded or not marked source-curated"
            )
        if row.get("missing_required"):
            reasons.append("missing paper_coverage_llm.json coverage audit")
        if row.get("missing_source_grounded_audit"):
            reasons.append(
                "paper_coverage_llm.json is not a source-grounded source-to-dashboard LLM audit"
            )
        if row.get("prompt_version_stale"):
            reasons.append(
                "the saved paper_coverage_llm.json prompt version is stale "
                f"({row.get('prompt_version') or 'missing'})"
            )
        if row.get("audit_metadata_missing"):
            reasons.append("paper_coverage_llm.json is missing validator or validated_at success metadata")
        if row.get("coverage_metadata_missing_count"):
            reasons.append(
                f"{row['coverage_metadata_missing_count']} coverage item(s) lack validator/timestamp metadata"
            )
        if row.get("inventory_missing_source_url_count"):
            reasons.append(
                f"{row['inventory_missing_source_url_count']} source-inventory statement(s) lack source URL"
            )
        if row.get("inventory_missing_source_provenance_count"):
            reasons.append(
                f"{row['inventory_missing_source_provenance_count']} source-inventory statement(s) lack source location/status"
            )
        if row.get("inventory_unknown_source_kind_count"):
            reasons.append(
                f"{row['inventory_unknown_source_kind_count']} source-inventory statement(s) use unknown source_kind values"
            )
        if row.get("missing_coverage_count"):
            reasons.append(f"{row['missing_coverage_count']} source statement(s) missing coverage row")
        if row.get("missing_statement_digest_count"):
            reasons.append(
                f"{row['missing_statement_digest_count']} coverage item(s) lack source-statement digest"
            )
        if row.get("partial_count"):
            reasons.append(f"{row['partial_count']} partially covered source statement(s)")
        if row.get("missing_count"):
            reasons.append(f"{row['missing_count']} source statement(s) judged missing")
        if row.get("uncertain_count"):
            reasons.append(f"{row['uncertain_count']} uncertain source-coverage judgment(s)")
        if row.get("unknown_count"):
            reasons.append(f"{row['unknown_count']} unknown coverage judgment value(s)")
        if row.get("stale_inventory"):
            reasons.append("the saved paper_coverage_llm.json source-inventory digest is stale")
        if row.get("stale_surface"):
            reasons.append("the saved paper_coverage_llm.json review-surface digest is stale")
        if row.get("stale_statement_count"):
            reasons.append(f"{row['stale_statement_count']} stale source-statement digest(s)")
        if row.get("invalid_row_link_count"):
            reasons.append(f"{row['invalid_row_link_count']} linked dashboard row(s) no longer exist")
        if row.get("coverage_row_signature_error_count"):
            reasons.append(
                f"{row['coverage_row_signature_error_count']} coverage link(s) lack a current elaborated Lean signature pin"
            )
        if row.get("covered_without_rows_count"):
            reasons.append(f"{row['covered_without_rows_count']} covered source statement(s) lack linked dashboard rows")
        if row.get("covered_without_reason_count"):
            reasons.append(f"{row['covered_without_reason_count']} covered source statement(s) lack match reasons")
        if row.get("covered_with_seed_reason_count"):
            reasons.append(f"{row['covered_with_seed_reason_count']} covered source statement(s) only have exact-key scaffold reasons")
        if row.get("covered_without_source_evidence_count"):
            reasons.append(f"{row['covered_without_source_evidence_count']} covered source statement(s) lack source evidence")
        if row.get("coverage_route_mismatch_count"):
            reasons.append(
                f"{row['coverage_route_mismatch_count']} coverage link(s) are not pinned to the row's exact semantic source route"
            )
        if row.get("result_covered_without_proof_row_count"):
            reasons.append(
                f"{row['result_covered_without_proof_row_count']} paper-facing result(s) are directly covered without a theorem/lemma row"
            )
        if row.get("result_matched_only_by_definition_row_count"):
            reasons.append(
                f"{row['result_matched_only_by_definition_row_count']} paper-facing result(s) have positive match evidence only from def/abbrev rows"
            )
        if row.get("support_without_declarations_count"):
            reasons.append(
                f"{row['support_without_declarations_count']} support-covered source statement(s) lack support declarations"
            )
        if row.get("support_without_reason_count"):
            reasons.append(
                f"{row['support_without_reason_count']} support-covered source statement(s) lack reasons"
            )
        if row.get("support_without_source_evidence_count"):
            reasons.append(
                f"{row['support_without_source_evidence_count']} support-covered source statement(s) lack source evidence"
            )
        if row.get("invalid_quarantined_defect_support_count"):
            reasons.append(
                f"{row['invalid_quarantined_defect_support_count']} quarantined source defect(s) lack exact-hash semantic counterexample/refutation support"
            )
        if row.get("defect_support_judgment_error_count"):
            reasons.append(
                f"{row['defect_support_judgment_error_count']} defect-support semantic judgment(s) are missing, stale, malformed, or tautological"
            )
        if row.get("quarantined_defect_direct_coverage_count"):
            reasons.append(
                f"{row['quarantined_defect_direct_coverage_count']} quarantined source defect(s) are incorrectly counted as direct proof coverage"
            )
        if row.get("user_approved_scope_exclusion_error_count"):
            reasons.append(
                f"{row['user_approved_scope_exclusion_error_count']} user-approved scope exclusion(s) lack complete approval or pinned source evidence"
            )
        if row.get("required_out_of_scope_count"):
            reasons.append(
                f"{row['required_out_of_scope_count']} required source-visible review target(s) are marked out of scope/not paper targets"
            )
        if source_to_lean and row.get("support_only_named_claim_count"):
            reasons.append(
                f"{row['support_only_named_claim_count']} theorem-like source statement(s) are only support-covered, without review-row statement-match audit"
            )
        if source_to_lean and row.get("support_only_required_source_item_count"):
            reasons.append(
                f"{row['support_only_required_source_item_count']} required source-visible review target(s) are only support-covered, without review-row statement-match audit"
            )
        if source_to_lean and row.get("row_statement_match_missing_count"):
            reasons.append(
                f"{row['row_statement_match_missing_count']} source-to-row link(s) lack row-local LLM correctness judgments"
            )
        if source_to_lean and row.get("row_statement_match_stale_count"):
            reasons.append(
                f"{row['row_statement_match_stale_count']} source-to-row link(s) use stale row-local LLM correctness judgments"
            )
        if source_to_lean and row.get("row_statement_match_mismatch_count"):
            reasons.append(
                f"{row['row_statement_match_mismatch_count']} source-to-row link(s) point to row-local LLM correctness mismatches"
            )
        if source_to_lean and row.get("row_statement_match_uncertain_count"):
            reasons.append(
                f"{row['row_statement_match_uncertain_count']} source-to-row link(s) point to uncertain row-local LLM correctness judgments"
            )
        if source_to_lean and row.get("row_statement_match_unknown_count"):
            reasons.append(
                f"{row['row_statement_match_unknown_count']} source-to-row link(s) point to unknown row-local LLM correctness judgments"
            )
        if source_to_lean and row.get("row_statement_match_conditional_without_coverage_boundary_count"):
            reasons.append(
                f"{row['row_statement_match_conditional_without_coverage_boundary_count']} source-to-row link(s) rely on conditional row-local mismatches while source coverage is marked direct"
            )
        if source_to_lean and row.get("row_statement_match_missing_statement_digest_count"):
            reasons.append(
                f"{row['row_statement_match_missing_statement_digest_count']} source-to-row link(s) have row-local statement judgments without saved paper-statement digests"
            )
        if source_to_lean and row.get("row_statement_match_wrong_statement_digest_count"):
            reasons.append(
                f"{row['row_statement_match_wrong_statement_digest_count']} source-to-row link(s) have row-local statement judgments for a different current row statement"
            )
        if source_to_lean and row.get("row_assumption_provenance_missing_count"):
            reasons.append(
                f"{row['row_assumption_provenance_missing_count']} assumption-linked source-to-row link(s) lack assumption-provenance judgments"
            )
        if source_to_lean and row.get("row_assumption_provenance_stale_count"):
            reasons.append(
                f"{row['row_assumption_provenance_stale_count']} assumption-linked source-to-row link(s) use stale assumption-provenance judgments"
            )
        if source_to_lean and row.get("row_assumption_provenance_mismatch_count"):
            reasons.append(
                f"{row['row_assumption_provenance_mismatch_count']} assumption-linked source-to-row link(s) are judged not to be source assumptions"
            )
        if source_to_lean and row.get("row_assumption_provenance_uncertain_count"):
            reasons.append(
                f"{row['row_assumption_provenance_uncertain_count']} assumption-linked source-to-row link(s) have uncertain assumption-provenance judgments"
            )
        if source_to_lean and row.get("row_assumption_provenance_unknown_count"):
            reasons.append(
                f"{row['row_assumption_provenance_unknown_count']} assumption-linked source-to-row link(s) have unknown assumption-provenance judgments"
            )
        if source_to_lean and row.get("row_assumption_provenance_conditional_without_coverage_boundary_count"):
            reasons.append(
                f"{row['row_assumption_provenance_conditional_without_coverage_boundary_count']} assumption-linked source-to-row link(s) are partial boundaries while source coverage is marked direct"
            )
        if row.get("out_of_scope_without_reason_count"):
            reasons.append(
                f"{row['out_of_scope_without_reason_count']} out-of-scope source statement(s) lack reasons"
            )
        if row.get("out_of_scope_without_source_evidence_count"):
            reasons.append(
                f"{row['out_of_scope_without_source_evidence_count']} out-of-scope source statement(s) lack source evidence"
            )
        if row.get("extra_coverage_count"):
            reasons.append(f"{row['extra_coverage_count']} stale extra coverage item(s)")
        if not reasons:
            reasons.append("paper-coverage audit needs attention")
        print(f" - {paper}: {'; '.join(str(reason) for reason in reasons)}.")
        samples: list[str] = []
        sample_specs = [
            ("missing_coverage", "missing coverage"),
            ("inventory_missing_source_url", "missing source URL"),
            ("inventory_missing_source_provenance", "missing source provenance"),
            ("inventory_unknown_source_kind", "unknown source_kind"),
            ("missing_statement_digest", "missing digest"),
            ("missing", "judged missing"),
            ("partial", "partial"),
            ("uncertain", "uncertain"),
            ("stale_statement", "stale statement"),
            ("invalid_row_links", "invalid row link"),
            ("coverage_row_signature_errors", "row-signature pin"),
            ("covered_without_rows", "covered without row"),
            ("covered_without_reason", "covered without reason"),
            ("covered_with_seed_reason", "exact-key scaffold reason"),
            ("covered_without_source_evidence", "missing source evidence"),
            ("coverage_route_mismatch", "coverage route mismatch"),
            ("result_covered_without_proof_rows", "result without proof row"),
            (
                "result_matched_only_by_definition_rows",
                "result matched only by def/abbrev",
            ),
            ("coverage_metadata_missing", "missing audit metadata"),
            ("support_without_declarations", "support missing declarations"),
            ("support_without_reason", "support without reason"),
            ("support_without_source_evidence", "support missing source evidence"),
            (
                "invalid_quarantined_defect_support",
                "invalid quarantined-defect support",
            ),
            (
                "defect_support_judgment_errors",
                "invalid defect-support semantic judgment",
            ),
            (
                "quarantined_defect_direct_coverage",
                "quarantined defect counted as proved",
            ),
            (
                "user_approved_scope_exclusion_errors",
                "invalid user-approved scope exclusion",
            ),
            ("required_out_of_scope", "required source target scoped out"),
            ("out_of_scope_without_reason", "out-of-scope without reason"),
            ("out_of_scope_without_source_evidence", "out-of-scope missing source evidence"),
            ("extra_coverage", "extra stale item"),
            ("unknown", "unknown"),
        ]
        if source_to_lean:
            sample_specs.extend(
                [
                    ("support_only_named_claims", "support-only named claim"),
                    ("support_only_required_source_items", "support-only required source target"),
                    ("row_statement_match_missing", "missing row correctness"),
                    ("row_statement_match_stale", "stale row correctness"),
                    ("row_statement_match_mismatch", "mismatched row correctness"),
                    ("row_statement_match_uncertain", "uncertain row correctness"),
                    ("row_statement_match_unknown", "unknown row correctness"),
                    (
                        "row_statement_match_conditional_without_coverage_boundary",
                        "conditional row but direct coverage",
                    ),
                    ("row_statement_match_missing_statement_digest", "missing row-statement digest"),
                    ("row_statement_match_wrong_statement_digest", "wrong row-statement digest"),
                    ("row_assumption_provenance_missing", "missing assumption provenance"),
                    ("row_assumption_provenance_stale", "stale assumption provenance"),
                    ("row_assumption_provenance_mismatch", "assumption provenance mismatch"),
                    ("row_assumption_provenance_uncertain", "uncertain assumption provenance"),
                    ("row_assumption_provenance_unknown", "unknown assumption provenance"),
                    (
                        "row_assumption_provenance_conditional_without_coverage_boundary",
                        "partial assumption but direct coverage",
                    ),
                ]
            )
        for key, label_text in sample_specs:
            sample = _format_name_sample(list(row.get(key) or []))
            if sample:
                samples.append(f"{label_text}: {sample}")
        for sample in samples[:4]:
            print(f"   {sample}")
    print(
        "This is the paper-level coverage lane: build a source-statement inventory "
        "from the source PDF/TeX/text, not from Lean row names, then have an "
        "independent LLM judge whether each paper statement is covered by one or "
        "more dashboard rows. Save that semantic source-to-dashboard judgment in "
        "paper_coverage_llm.json with audit_kind=source_to_dashboard_llm, "
        "source_grounded=true, source evidence, linked dashboard rows, an exact "
        "review_row_signature_sha256 pin for every linked row, and a "
        "nontrivial match reason. Exact-key seeding is only a scaffold. Do not "
        "mark source-visible definitions, examples, remarks, propositions, "
        "theorems, corollaries, or main-text lemmas as out of scope merely to keep "
        "the review surface compact; expose dashboard rows so the LLM-as-judge "
        "can inspect them. Appendix lemmas are a judgment call, but appendix "
        "theorems and corollaries should be covered. The "
        "source result lane requires an actual reviewed theorem/lemma declaration; "
        "a matching def/abbrev is specification vocabulary and cannot supply proof "
        "credit. A quarantined_source_defect item remains unproved and may use "
        "support_only only with a current defect_support_match_llm.json judgment "
        "that exact-hash pins the validated source defect, Lean statement, and "
        "elaborated signature and semantically aligns every theorem atom. Trivial "
        "or reflexive tautologies cannot provide defect support. The "
        "stricter source-to-Lean lane requires linked non-assumption rows to have "
        "current row-local LLM correctness judgments in statement_match_llm.json "
        "for the same current dashboard paper statement. Explicit Assumptions.lean "
        "rows instead require current assumption_match_llm.json provenance evidence; "
        "they are source model conditions, not duplicate theorem conclusions."
    )
    return True


def print_source_inventory_precheck_status(paper: str | None) -> bool:
    """Print source-map blockers and nonblocking coverage work separately.

    Return ``True`` only when the source-map itself blocks a manifest refresh.
    Missing or seed-scaffold semantic coverage remains visible here, but the
    strict paper-coverage/source-to-Lean checks are the fail-closed gates after
    current dashboard rows have been generated.
    """

    summaries = [
        source_inventory_precheck_summary(folder)
        for folder in iter_paper_folders(paper)
    ]
    label = paper or "all papers"
    blockers = [summary for summary in summaries if summary.get("pre_manifest_blocked")]
    pending = [
        summary for summary in summaries if summary.get("semantic_coverage_pending")
    ]
    if blockers:
        print(f"\nSource-map preflight blockers for {label}:")
        for summary in blockers:
            reasons = list(summary.get("pre_manifest_blockers") or [])
            print(f" - {summary['paper']}: {'; '.join(reasons)}.")
        print(
            "Fix these source-map blockers before refreshing Lean signature manifests. "
            "This structural gate does not replace --paper-coverage-check."
        )
    if pending:
        print(f"\nSource-to-dashboard coverage pending for {label}:")
        for summary in pending:
            reasons = list(summary.get("semantic_coverage_pending") or [])
            print(f" - {summary['paper']}: {'; '.join(reasons)}.")
        print(
            "This is expected before the first current row cache exists and does not "
            "block a paper-only --refresh-cache. After that refresh, complete the "
            "source-grounded coverage audit and run --paper-coverage-check and "
            "--source-to-lean-check; those later checks remain fail closed."
        )
    if blockers:
        return True
    if pending:
        return False

    total_inventory = sum(int(summary.get("inventory_count") or 0) for summary in summaries)
    total_coverage = sum(int(summary.get("coverage_item_count") or 0) for summary in summaries)
    print(
        f"Source-inventory precheck for {label} is current: "
        f"{total_inventory} mapped source item(s), {total_coverage} coverage item(s). "
        "Run the full paper-coverage and source-to-Lean checks after refreshing Lean rows."
    )
    return False


def print_paper_coverage_audit_status(
    paper: str | None,
    slice_filter: str | None = None,
    *,
    source_to_lean: bool = False,
) -> bool:
    """Print only paper-level source-coverage diagnostics."""

    papers = gather_paper_data(paper, slice_filter, render_images=False)
    rows = paper_coverage_audit_rows(papers)
    label = paper or "all papers"
    if slice_filter:
        label = f"{label} slice {slice_filter}"
    has_attention = print_paper_coverage_audit_warnings(
        rows, label, source_to_lean=source_to_lean
    )
    if has_attention:
        return True
    total_inventory = sum(int(row.get("inventory_count") or 0) for row in rows)
    total_covered = sum(int(row.get("covered_count") or 0) for row in rows)
    total_corrected_targets = sum(
        int(row.get("corrected_target_covered_count") or 0) for row in rows
    )
    total_conditional = sum(int(row.get("conditional_boundary_count") or 0) for row in rows)
    total_support = sum(int(row.get("support_only_count") or 0) for row in rows)
    total_quarantined_support = sum(
        int(row.get("quarantined_defect_support_count") or 0) for row in rows
    )
    total_regular_support = max(total_support - total_quarantined_support, 0)
    total_out_of_scope = sum(int(row.get("out_of_scope_count") or 0) for row in rows)
    total_user_approved_exclusions = sum(
        int(row.get("user_approved_scope_exclusion_count") or 0) for row in rows
    )
    required = sum(1 for row in rows if row.get("audit_required"))
    print(
        f"{'Source-to-Lean' if source_to_lean else 'Paper-coverage'} audits for {label} are current: "
        f"{total_covered}/{total_inventory} source statement(s) covered directly, "
        f"{total_corrected_targets} covered as approved corrected target(s), "
        f"{total_conditional} covered with visible-premise boundaries, "
        f"{total_regular_support} covered by support declarations, "
        f"{total_quarantined_support} quarantined defect(s) supported by counterexamples/refutations (not proof coverage), "
        f"{total_out_of_scope} marked out of scope/not paper targets, "
        f"{total_user_approved_exclusions} source-visible claim(s) expressly excluded by the user, "
        f"{required} required paper audit(s), no missing/stale/flagged items."
    )
    return False


def print_assumption_audit_warnings(rows: list[dict[str, Any]], label: str) -> bool:
    """Print paper-level assumption-provenance warnings."""

    warnings = [row for row in rows if row.get("has_warning") or row.get("needs_attention")]
    if not warnings:
        return False
    print(f"\nAssumption-provenance audit warnings for {label}:")
    for row in warnings:
        paper = row.get("paper") or "unknown paper"
        reasons: list[str] = []
        if row.get("missing_rows_count"):
            reasons.append(f"{row['missing_rows_count']} configured assumption declaration(s) missing")
        if row.get("unlisted_rows_count"):
            reasons.append(f"{row['unlisted_rows_count']} assumption-like declaration(s) not listed in status.json")
        if row.get("missing_judgment_count"):
            reasons.append(f"{row['missing_judgment_count']} missing assumption-judge declaration(s)")
        if row.get("stale_judgment_count"):
            reasons.append(f"{row['stale_judgment_count']} stale assumption-judge declaration(s)")
        if row.get("not_paper_assumption_count"):
            reasons.append(f"{row['not_paper_assumption_count']} declaration(s) judged not to be paper assumptions")
        if row.get("uncertain_count"):
            reasons.append(f"{row['uncertain_count']} uncertain assumption-judge declaration(s)")
        if row.get("unknown_count"):
            reasons.append(f"{row['unknown_count']} unknown assumption-judge value(s)")
        if row.get("partial_boundary_count"):
            reasons.append(f"{row['partial_boundary_count']} partial-boundary declaration(s)")
        if row.get("partial_boundary_premise_count"):
            reasons.append(
                f"{row['partial_boundary_premise_count']} premise-level partial boundary finding(s)"
            )
        if row.get("unresolved_premise_count"):
            reasons.append(
                f"{row['unresolved_premise_count']} unresolved premise-level judgment(s)"
            )
        if row.get("missing_source_location_premise_count"):
            reasons.append(
                f"{row['missing_source_location_premise_count']} source-text premise judgment(s) missing source_location"
            )
        if row.get("hidden_premise_count"):
            hidden_bits: list[str] = [f"{row['hidden_premise_count']} hidden premise finding(s)"]
            if row.get("hidden_premise_error_count"):
                hidden_bits.append(f"{row['hidden_premise_error_count']} error")
            if row.get("hidden_premise_warning_count"):
                hidden_bits.append(f"{row['hidden_premise_warning_count']} warning")
            reasons.append(", ".join(hidden_bits))
        if row.get("accepted_conditional_premise_count"):
            reasons.append(
                f"{row['accepted_conditional_premise_count']} accepted visible-premise finding(s)"
            )
        if row.get("hidden_premise_audit_error"):
            reasons.append(f"could not run hidden-premise audit: {row['hidden_premise_audit_error']}")
        if not reasons:
            reasons.append("assumption provenance needs attention")
        print(f" - {paper}: {'; '.join(str(reason) for reason in reasons)}.")
        samples: list[str] = []
        for key, label_text in [
            ("missing_rows", "missing declaration"),
            ("unlisted_rows", "unlisted declaration"),
            ("not_paper_assumption", "not paper assumption"),
            ("uncertain", "uncertain"),
            ("stale_judgment", "stale judgment"),
            ("missing_judgment", "missing judgment"),
            ("unknown", "unknown"),
            ("partial_boundary_premises", "partial premise"),
            ("unresolved_premises", "unresolved premise"),
            ("missing_source_location_premises", "missing premise source"),
        ]:
            sample = _format_name_sample(list(row.get(key) or []))
            if sample:
                samples.append(f"{label_text}: {sample}")
        for sample in samples[:4]:
            print(f"   {sample}")
        for sample in list(row.get("hidden_premise_samples") or [])[:3]:
            print(f"   hidden premise: {sample}")
        for sample in list(row.get("accepted_conditional_premise_samples") or [])[:3]:
            print(f"   accepted visible premise: {sample}")
    print(
        "Every paper-facing theorem premise that is not derived in Lean must be "
        "declared in Assumptions.lean, listed in "
        "status.json review_surface.assumption_names, and judged in "
        "assumption_match_llm.json as a true paper/source model assumption, "
        "unless it is an explicitly accepted statement-level visible-premise "
        "boundary recorded in statement_match_llm.json. The judge must inspect "
        "premise semantics rather than names: certificate, replay, process, "
        "bridge, source-row, or broad package premises need a constructor from "
        "paper primitives or they remain partial/conditional."
    )
    return True


def print_assumption_audit_status(paper: str | None, slice_filter: str | None = None) -> bool:
    """Print only assumption-provenance audit diagnostics."""

    fast_precheck = fast_saved_source_record_assumption_precheck(paper, slice_filter)
    if fast_precheck is not None:
        return print_fast_saved_source_record_assumption_precheck(fast_precheck)

    papers = gather_paper_data(paper, slice_filter, render_images=False)
    rows = merge_hidden_premise_audit_rows(assumption_audit_rows(papers), paper)
    label = paper or "all papers"
    if slice_filter:
        label = f"{label} slice {slice_filter}"
    has_attention = print_assumption_audit_warnings(rows, label)
    if has_attention:
        return True
    total_rows = sum(int(row.get("row_count") or 0) for row in rows)
    print(
        f"Assumption-provenance audits for {label} are current: "
        f"{total_rows} assumption declaration(s), no missing/stale/flagged items."
    )
    return False


def print_stale_review_warning(
    paper: str | None, log_file: Path | None, slice_filter: str | None = None
) -> bool:
    """Print a lightweight launch-time check summary and return whether stale data exists."""

    summary = stale_review_summary(paper, log_file, slice_filter)
    stale_rows = summary["stale"]
    unreviewed_rows = summary["unreviewed"]
    mismatch_rows = summary["mismatch"]
    surface_audits = summary["surface_audits"]
    statement_audits = summary["statement_audits"]
    paper_coverage_audits = summary["paper_coverage_audits"]
    assumption_audits = summary["assumption_audits"]
    totals = summary["totals"]
    label = paper or "all papers"
    if slice_filter:
        label = f"{label} slice {slice_filter}"
    total_items = int(totals.get("total_items") or 0)
    reviewed_items = int(totals.get("reviewed_items") or 0)
    needs_attention = int(totals.get("needs_attention_items") or 0)
    print(
        f"Review status for {label}: {reviewed_items}/{total_items} reviewed, "
        f"{needs_attention} need attention ({len(stale_rows)} stale, "
        f"{len(unreviewed_rows)} unreviewed, {len(mismatch_rows)} mismatch)."
    )
    surface_needs_attention = print_surface_audit_warnings(surface_audits, label)
    statement_needs_attention = print_statement_audit_warnings(statement_audits, label)
    paper_coverage_needs_attention = print_paper_coverage_audit_warnings(
        paper_coverage_audits,
        label,
    )
    assumption_needs_attention = print_assumption_audit_warnings(assumption_audits, label)

    if not stale_rows:
        if not unreviewed_rows and not mismatch_rows:
            print(f"Review checks for {label} are currently up to date.")
            return (
                surface_needs_attention
                or statement_needs_attention
                or paper_coverage_needs_attention
                or assumption_needs_attention
            )
        else:
            print(
                f"Review checks for {label}: no stale checks, but "
                f"{len(unreviewed_rows)} item(s) have no review entry yet and "
                f"{len(mismatch_rows)} item(s) are marked as not matching."
            )
            return True

    print(f"\nReview check: found {len(stale_rows)} stale check(s) in {label}.")
    print("The dashboard loads current Lean/Paper statements on launch, but these")
    print("previously logged entries were checked against an earlier interface snapshot:")
    for row in stale_rows[:12]:
        reasons = []
        if row.get("lean_stale"):
            reasons.append("Lean signature changed")
        if row.get("paper_stale"):
            reasons.append("paper-facing text changed")
        print(
            f" - {row['paper']}.{row['theorem']} "
            f"({' / '.join(reasons) if reasons else 'statement changed'})"
        )
    if len(stale_rows) > 12:
        print(f" - ... {len(stale_rows) - 12} more")
    if unreviewed_rows:
        print(f"{len(unreviewed_rows)} additional item(s) currently need an initial review.")
    if mismatch_rows:
        print(f"{len(mismatch_rows)} additional reviewed item(s) are marked as not matching.")
    print("Open the dashboard and resave checks for these items to refresh the trace.")
    print("The agent Lean drafts are regenerated from the current declarations automatically.")
    return True


class ReusableThreadingHTTPServer(ThreadingHTTPServer):
    allow_reuse_address = True


class ReviewHTTPHandler(BaseHTTPRequestHandler):
    papers: list[dict[str, Any]] = []
    log_file: Path | None = None
    default_user: str = getpass.getuser()
    paper_filter: str | None = None
    slice_filter: str | None = None

    def log_message(self, *_args: Any) -> None:  # silence noisy HTTP logs
        return

    def _json_response(self, status: int, payload: dict[str, Any]) -> None:
        data = json.dumps(payload).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def _collect_path(self) -> tuple[str, dict[str, str]]:
        parsed = urllib.parse.urlsplit(self.path)
        query = urllib.parse.parse_qs(parsed.query)
        clean_query = {k: v[0] for k, v in query.items()}
        return parsed.path, clean_query

    def _send_file(self, path: Path) -> None:
        """Serve a single local file."""

        data = path.read_bytes()
        content_type, _ = mimetypes.guess_type(str(path))
        if path.suffix.lower() == ".txt":
            content_type = "text/plain; charset=utf-8"
        self.send_response(200)
        self.send_header("Content-Type", content_type or "application/octet-stream")
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Content-Disposition", "inline")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.end_headers()
        self.wfile.write(data)

    def _send_asset(self, paper: str, filename: str) -> None:
        """Serve a validated paper asset if it belongs to the selected paper."""

        target_paper_dir = None
        for folder in iter_paper_folders(self.paper_filter):
            if folder.name == paper:
                target_paper_dir = folder
                break
        if target_paper_dir is None:
            self.send_error(404, "paper not found")
            return
        if not filename or "/" in filename or "\\" in filename or ".." in filename:
            self.send_error(404, "invalid asset")
            return
        if not filename.lower().endswith(tuple(PAPER_ASSET_EXTENSIONS)):
            self.send_error(404, "unsupported paper asset")
            return
        candidate = target_paper_dir / filename
        if not candidate.exists() or not candidate.is_file():
            self.send_error(404, "asset not found")
            return
        self._send_file(candidate)

    def _send_rendered_statement(self, paper: str, filename: str) -> None:
        """Serve a generated statement-render PNG if it belongs to the paper cache."""

        target_paper_dir = None
        for folder in iter_paper_folders(self.paper_filter):
            if folder.name == paper:
                target_paper_dir = folder
                break
        if target_paper_dir is None:
            self.send_error(404, "paper not found")
            return
        if not filename or "/" in filename or "\\" in filename or ".." in filename:
            self.send_error(404, "invalid rendered statement")
            return
        if not filename.lower().endswith(tuple(PAPER_RENDERED_IMAGE_EXTENSIONS)):
            self.send_error(404, "unsupported rendered statement")
            return
        candidate = target_paper_dir / ".review_traces" / PAPER_RENDERED_STATEMENT_DIR / filename
        if not candidate.exists() or not candidate.is_file():
            self.send_error(404, "rendered statement not found")
            return
        self._send_file(candidate)

    def do_GET(self) -> None:
        path, query = self._collect_path()
        if path == "/":
            papers = gather_paper_data(self.paper_filter, self.slice_filter)
            html = render_static_html(
                papers,
                self.default_user,
                describe_log_target(self.log_file, self.paper_filter),
            )
            body = html.encode("utf-8")
            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.send_header("Content-Length", str(len(body)))
            self.end_headers()
            self.wfile.write(body)
            return
        if path.startswith("/paper-assets/"):
            pieces = [segment for segment in path.split("/") if segment]
            if len(pieces) != 3:
                self.send_error(404, "invalid asset request")
                return
            paper = urllib.parse.unquote(pieces[1])
            filename = urllib.parse.unquote(pieces[2])
            self._send_asset(paper, filename)
            return
        if path.startswith("/rendered-statements/"):
            pieces = [segment for segment in path.split("/") if segment]
            if len(pieces) != 3:
                self.send_error(404, "invalid rendered statement request")
                return
            paper = urllib.parse.unquote(pieces[1])
            filename = urllib.parse.unquote(pieces[2])
            self._send_rendered_statement(paper, filename)
            return
        if path == "/api/papers":
            papers = gather_paper_data(self.paper_filter, self.slice_filter)
            self._json_response(200, {"papers": papers})
            return
        if path == "/api/reviews":
            paper = query.get("paper")
            if paper and self.log_file is None:
                try:
                    reviews = read_log_entries(paper_review_log_file(paper))
                except ValueError:
                    reviews = []
            elif paper:
                reviews = read_log_entries(self.log_file, paper)
            else:
                reviews = read_all_log_entries(self.paper_filter, self.log_file)
            self._json_response(200, {"reviews": reviews})
            return
        if path == "/api/status":
            requested_paper = query.get("paper")
            user_filter = query.get("user")
            stale_only = parse_bool_flag(query.get("stale_only"))
            papers = gather_paper_data(
                requested_paper or self.paper_filter,
                self.slice_filter,
                render_images=False,
            )
            if self.log_file is not None:
                if requested_paper:
                    reviews = read_log_entries(self.log_file, requested_paper)
                else:
                    reviews = read_log_entries(self.log_file)
            elif requested_paper:
                try:
                    reviews = read_log_entries(paper_review_log_file(requested_paper))
                except ValueError:
                    reviews = []
            else:
                reviews = read_all_log_entries(self.paper_filter, None)
            rows = build_review_status(papers, reviews)
            rows = filter_review_rows(rows, user_filter=user_filter, stale_only=stale_only)
            self._json_response(
                200,
                {
                    "status": rows,
                    "totals": status_totals(rows),
                    "surface_audits": surface_audit_rows(papers),
                    "statement_audits": statement_audit_rows(papers),
                    "paper_coverage_audits": paper_coverage_audit_rows(papers),
                    "assumption_audits": merge_hidden_premise_audit_rows(
                        assumption_audit_rows(papers),
                        requested_paper or self.paper_filter,
                    ),
                },
            )
            return
        self.send_error(404, "not found")

    def do_POST(self) -> None:
        path, _ = self._collect_path()
        if path != "/api/reviews":
            self.send_error(404, "not found")
            return
        length = int(self.headers.get("Content-Length", "0"))
        raw = self.rfile.read(length).decode("utf-8")
        try:
            payload = json.loads(raw or "{}")
        except json.JSONDecodeError:
            self._json_response(400, {"error": "invalid json body"})
            return
        try:
            paper_name = str(payload.get("paper") or "").strip()
            if self.log_file is None:
                log_file = paper_review_log_file(paper_name)
            else:
                log_file = self.log_file
            entry = append_review(log_file, payload, self.default_user)
        except Exception as exc:  # noqa: BLE001 - user input surface
            self._json_response(400, {"error": str(exc)})
            return
        self._json_response(200, {"entry": entry})


def main() -> None:
    parser = argparse.ArgumentParser(description="Review dashboard for paper interface statements.")
    parser.add_argument("--paper", help="Optional paper folder name to limit the dashboard.")
    parser.add_argument(
        "--slice",
        dest="slice_filter",
        default="",
        help="Optional review slice id, or PAPER::slice id, to limit dashboard rows.",
    )
    parser.add_argument(
        "--log-file",
        default="",
        help="Optional single JSONL trace path that overrides per-paper storage.",
    )
    parser.add_argument(
        "--user",
        default="",
        help="Reviewer handle (fallback used in saved entries).",
    )
    parser.add_argument(
        "--user-var",
        action="append",
        dest="user_vars",
        help="Environment variable(s) to check for default username (default GitHub variables).",
    )
    parser.add_argument(
        "--export-format",
        choices=("json", "csv", "md", "validators-md"),
        help="Generate a review status export instead of static HTML when not in server mode.",
    )
    parser.add_argument("--export-file", default="", help="Optional path for exported report output.")
    parser.add_argument("--status-user", default="", help="Filter status rows by reviewer handle.")
    parser.add_argument(
        "--stale-only",
        action="store_true",
        help="Filter status export to rows that need attention.",
    )
    parser.add_argument(
        "--precheck",
        action="store_true",
        help="Print stale review diagnostics for the selected paper and exit.",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="Like --precheck, but return non-zero if any item needs review or is stale.",
    )
    parser.add_argument(
        "--statement-precheck",
        action="store_true",
        help="Print only Lean-to-TeX and statement-judge audit diagnostics, then exit.",
    )
    parser.add_argument(
        "--statement-check",
        action="store_true",
        help="Like --statement-precheck, but return non-zero for missing/stale/flagged statement-audit rows.",
    )
    parser.add_argument(
        "--paper-coverage-precheck",
        action="store_true",
        help="Print only source-paper statement coverage diagnostics, then exit.",
    )
    parser.add_argument(
        "--paper-coverage-check",
        action="store_true",
        help="Like --paper-coverage-precheck, but return non-zero for missing/stale/flagged coverage rows.",
    )
    parser.add_argument(
        "--source-inventory-precheck",
        action="store_true",
        help=(
            "Check source-map structural readiness without parsing Lean rows; report "
            "coverage work separately before an expensive cache refresh."
        ),
    )
    parser.add_argument(
        "--source-inventory-check",
        action="store_true",
        help=(
            "Like --source-inventory-precheck, but return non-zero only for "
            "source-map blockers. Semantic coverage remains enforced later by "
            "--paper-coverage-check and --source-to-lean-check."
        ),
    )
    parser.add_argument(
        "--source-to-lean-precheck",
        action="store_true",
        help="Print source-paper-to-Lean row correctness diagnostics, then exit.",
    )
    parser.add_argument(
        "--source-to-lean-check",
        action="store_true",
        help=(
            "Like --source-to-lean-precheck, but return non-zero when source coverage "
            "lacks current row-local LLM correctness judgments."
        ),
    )
    parser.add_argument(
        "--assumption-precheck",
        action="store_true",
        help="Print only paper-assumption provenance audit diagnostics, then exit.",
    )
    parser.add_argument(
        "--assumption-check",
        action="store_true",
        help="Like --assumption-precheck, but return non-zero for missing/stale/flagged assumption-audit rows.",
    )
    parser.add_argument(
        "--refresh-cache",
        action="store_true",
        help="Regenerate cached paper-interface rows and exit.",
    )
    parser.add_argument("--serve", action="store_true", help="Start a local review web server.")
    parser.add_argument("--host", default="127.0.0.1", help="Server host when --serve is set.")
    parser.add_argument("--port", type=int, default=8765, help="Server port when --serve is set.")
    args = parser.parse_args()

    if args.user_vars is None:
        args.user_vars = DEFAULT_USER_ENV_VARS.copy()
    user = detect_reviewer_username(args.user, args.user_vars)

    log_file = Path(args.log_file) if args.log_file else None

    if args.precheck or args.check:
        has_attention = print_stale_review_warning(args.paper, log_file, args.slice_filter)
        if args.check and has_attention:
            sys.exit(1)
        return

    if args.statement_precheck or args.statement_check:
        has_attention = print_statement_audit_status(args.paper, args.slice_filter)
        if args.statement_check and has_attention:
            sys.exit(1)
        return

    if args.source_inventory_precheck or args.source_inventory_check:
        has_attention = print_source_inventory_precheck_status(args.paper)
        if args.source_inventory_check and has_attention:
            sys.exit(1)
        return

    if args.paper_coverage_precheck or args.paper_coverage_check:
        has_attention = print_paper_coverage_audit_status(args.paper, args.slice_filter)
        if args.paper_coverage_check and has_attention:
            sys.exit(1)
        return

    if args.source_to_lean_precheck or args.source_to_lean_check:
        has_attention = print_paper_coverage_audit_status(
            args.paper, args.slice_filter, source_to_lean=True
        )
        if args.source_to_lean_check and has_attention:
            sys.exit(1)
        return

    if args.assumption_precheck or args.assumption_check:
        has_attention = print_assumption_audit_status(args.paper, args.slice_filter)
        if args.assumption_check and has_attention:
            sys.exit(1)
        return

    if args.refresh_cache:
        papers = iter_paper_folders(args.paper)
        if not papers:
            if args.paper:
                raise SystemExit(
                    f"no canonical human-review PaperInterface.lean found for paper '{args.paper}'"
                )
            raise SystemExit("no papers with canonical human-review PaperInterface.lean found")
        for folder in papers:
            refresh_cached_review_rows(folder)
            print(f"refreshed dashboard cache for {folder.name}")
        return

    if args.serve:
        handler = ReviewHTTPHandler
        handler.papers = gather_paper_data(args.paper, args.slice_filter)
        handler.log_file = log_file
        handler.default_user = user
        handler.paper_filter = args.paper
        handler.slice_filter = args.slice_filter
        print_stale_review_warning(args.paper, log_file, args.slice_filter)
        try:
            server = ReusableThreadingHTTPServer((args.host, args.port), handler)
        except OSError as exc:
            print(
                f"Failed to start dashboard server on {args.host}:{args.port}: {exc}"
            )
            if args.host == "0.0.0.0":
                print(
                    "Hint: in WSL2, you may retry with --host 127.0.0.1 or use "
                    "localhost in Windows."
                )
            else:
                print(
                    "Hint: check if another process is already using this port, "
                    "or try a different --port value."
                )
            sys.exit(1)
        print(f"Review dashboard: http://{args.host}:{args.port}/")
        print(f"Log target: {describe_log_target(log_file, args.paper)}")
        print("Press Ctrl-C to stop.")
        server.serve_forever()

    if args.export_format:
        papers = gather_paper_data(args.paper, args.slice_filter, render_images=False)
        if log_file is not None:
            if args.paper:
                reviews = read_log_entries(log_file, args.paper)
            else:
                reviews = read_log_entries(log_file)
        elif args.paper:
            reviews = read_all_log_entries(args.paper, None)
        else:
            reviews = read_all_log_entries(None, None)
        rows = build_review_status(papers, reviews)
        rows = filter_review_rows(rows, user_filter=(args.status_user or "").strip() or None, stale_only=args.stale_only)
        if args.export_format == "json":
            payload = json.dumps(
                {
                    "status": rows,
                    "totals": status_totals(rows),
                    "surface_audits": surface_audit_rows(papers),
                    "statement_audits": statement_audit_rows(papers),
                    "paper_coverage_audits": paper_coverage_audit_rows(papers),
                    "assumption_audits": merge_hidden_premise_audit_rows(
                        assumption_audit_rows(papers),
                        args.paper,
                    ),
                },
                indent=2,
            )
        elif args.export_format == "csv":
            payload = render_csv_summary(rows)
        elif args.export_format == "validators-md":
            payload = render_validator_markdown_summary(rows)
        else:
            payload = render_markdown_summary(rows)
        if args.export_file:
            out = Path(args.export_file)
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(payload, encoding="utf-8")
            print(f"Wrote report to {out}")
        else:
            if args.export_format == "json":
                print(payload)
            else:
                sys.stdout.write(payload)
        return

    else:
        papers = gather_paper_data(args.paper, args.slice_filter)
        html = render_static_html(papers, user, describe_log_target(log_file, args.paper))
        if log_file is not None:
            out = log_file.parent / "review_dashboard.html"
        elif args.paper:
            out = paper_review_log_file(args.paper).parent / "review_dashboard.html"
        else:
            out = ROOT / ".review_traces" / "review_dashboard.html"
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(html, encoding="utf-8")
        print(f"Wrote dashboard HTML to {out}")
        print("Run with --serve to allow interactive saving to the local review log.")


if __name__ == "__main__":
    main()
