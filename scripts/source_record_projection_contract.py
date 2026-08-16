#!/usr/bin/env python3
"""Validate sidecar contracts for source-record provenance evidence.

The source-record scan can statically identify a paper-local constructor whose
result supplies a conclusion-bearing theorem premise, but whose proof still
depends on source-model antecedents.  A free-form ``lean_derivation`` string is
not enough evidence that a sidecar chose the right constructor or supplied the
right antecedents.  This module binds that sidecar claim to the generated
conditional-constructor surface.

It also keeps a small shared contract for generated semantic-model subreviews
whose trigger comes from expanded type structure rather than Lean names.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from typing import Any, Callable


CHECKED_PROJECTION_FIELD = "checked_projection"
CHECKED_PROJECTION_CONSTRUCTOR_FIELD = "constructor_declaration"
CHECKED_PROJECTION_RESULT_TYPE_FIELD = "conditional_constructor_result_type"
CHECKED_PROJECTION_ANTECEDENTS_FIELD = "source_antecedent_keys"

# These subreviews are intentionally keyed by generated expanded type shapes,
# not by paper-local theorem, function, wrapper, or field names.  The source
# record generator requests them only for a finite carrier or a probability-law
# surface, respectively; the validators below make an omitted or name-only
# narrative fail closed.
CARDINALITY_BOUNDARY_ANALYSIS_FIELD = "cardinality_boundary_analysis"
CARDINALITY_BOUNDARY_ANALYSIS_VERDICTS = {
    "threshold_checked",
    "no_strictness_or_interior_requirement",
    "mismatch_or_open",
    "documented_partial_boundary",
}
CARDINALITY_BOUNDARY_ANALYSIS_FIELDS = (
    "source_cardinality_domain",
    "lean_cardinality_domain",
    "boundary_cases_checked",
    "strictness_witness_or_reason",
    "lean_boundary_evidence",
)
TRANSFORMED_LAW_ANALYSIS_FIELD = "transformed_law_analysis"
TRANSFORMED_LAW_ANALYSIS_VERDICTS = {
    "no_transform_or_canonicalization",
    "transformed_law_checked",
    "canonicalization_checked",
    "mismatch_or_open",
    "documented_partial_boundary",
}
TRANSFORMED_LAW_ANALYSIS_FIELDS = (
    "source_operation",
    "lean_operation",
    "parameter_domain_and_endpoints",
    "law_normalization_or_pushforward_evidence",
    "outcome_equivariance_or_no_relabeling_evidence",
    "lean_semantic_bridge",
)
# A transformed-law review can establish that both sides are normalized PMFs
# while still missing a material convention mismatch.  For example, a source
# can fix unit-variance noise and then divide it by ``theta``, whereas Lean can
# expose a Laplace *rate* named ``theta``.  The two are related by a concrete
# factor, not by declaration spelling or the bare fact that both parameters are
# positive.  This subanalysis is attached to the same expanded probability-law
# shape as transformed-law review, so its trigger is independent of local Lean
# names.
DISTRIBUTION_PARAMETERIZATION_ANALYSIS_FIELD = (
    "distribution_parameterization_analysis"
)
DISTRIBUTION_PARAMETERIZATION_ANALYSIS_VERDICTS = {
    "no_parameterized_law_or_scale",
    "definitionally_same_parameterization",
    "proved_exact_law_equivalence",
    "proved_outcome_equivalence_after_translation",
    "mismatch_or_open",
    "documented_partial_boundary",
}
DISTRIBUTION_PARAMETERIZATION_ANALYSIS_FIELDS = (
    "source_parameterization",
    "source_scale_or_variance",
    "lean_parameterization",
    "lean_scale_or_variance",
    "parameter_translation",
    "family_coupling_scope",
    "family_coupling_evidence",
    "law_equivalence_evidence",
    "outcome_preservation_evidence",
    "lean_semantic_bridge",
)
# A stagewise kernel/product construction can have the right marginal law at
# each step while describing a different joint experiment: it may redraw a
# source endpoint that the paper treats as one random variable.  Likewise, a
# weighted or restricted measure is useful proof machinery, but is not itself
# a source pushforward unless a bridge identifies it as one.  This subreview
# is opt-in from generated expanded type/term structure, never from a Lean
# declaration name.  The source-record generator should set the trigger for a
# detected joint-law surface with a measure/kernel/carrier transport.
SOURCE_CARRIER_COHERENCE_ANALYSIS_FIELD = "source_carrier_coherence_analysis"
SOURCE_CARRIER_COHERENCE_ANALYSIS_VERDICTS = {
    "source_carrier_pushforward_checked",
    "source_conditioned_or_restricted_pushforward_checked",
    "source_defined_joint_kernel_law_checked",
    "generated_product_or_kernel_not_source_pushforward",
    "weighted_or_tilted_not_source_pushforward",
    "mismatch_or_open",
    "documented_partial_boundary",
}
SOURCE_CARRIER_COHERENCE_MEASURE_CONSTRUCTIONS = {
    "single_source_carrier_pushforward",
    "source_conditioned_or_restricted_pushforward",
    "source_defined_joint_kernel_law",
    "generated_product_or_kernel_measure",
    "weighted_or_tilted_measure",
    "unresolved",
}
SOURCE_CARRIER_COHERENCE_SOURCE_RATE_SCOPES = {
    "not_rate_parameterized",
    "fixed_rate_claim",
    "rate_indexed_claim",
    "rate_free_claim",
}
SOURCE_CARRIER_COHERENCE_LEAN_RATE_SCOPES = {
    "not_rate_parameterized",
    "fixed_rate_instance",
    "rate_indexed_family",
}
SOURCE_CARRIER_COHERENCE_FIELDS = (
    "source_random_variable_carrier",
    "lean_random_variable_carrier",
    "stage_identity_or_resampling_evidence",
    "joint_law_bridge_evidence",
    "measure_construction",
    "measure_transport_evidence",
    "source_rate_scope",
    "lean_rate_scope",
    "rate_family_evidence",
)
SOURCE_CARRIER_COHERENCE_NARRATIVE_FIELDS = {
    "source_random_variable_carrier",
    "lean_random_variable_carrier",
    "stage_identity_or_resampling_evidence",
    "joint_law_bridge_evidence",
    "measure_transport_evidence",
    "rate_family_evidence",
}

# A source may define an objective in two stages while a paper-facing Lean
# theorem exposes only a scalar equality.  The ordinary expanded-type scan can
# therefore see no PMF/Measure/integral constructor at all.  This opt-in
# subreview is driven by a byte-pinned schema-2 source contract and its
# generated semantic association, never by a declaration or function name.
SOURCE_MODEL_COMPOSITION_ANALYSIS_FIELD = "source_model_composition_analysis"
SOURCE_MODEL_COMPOSITION_ASSOCIATION_FIELD = "source_model_composition_association"
SOURCE_MODEL_COMPOSITION_REQUIREMENT_FIELD = "source_model_composition"
SOURCE_MODEL_COMPOSITION_CLAUSES_FIELD = "clauses"
SOURCE_MODEL_COMPOSITION_BRIDGE_FORMS = {
    "two_stage_finite_expectation",
    "joint_law_factorization",
}
SOURCE_MODEL_COMPOSITION_ANALYSIS_FIELDS = (
    "semantic_association_sha256",
    "selector_law_bridge",
    "conditional_outcome_law_bridge",
    "composed_objective_or_expectation_bridge",
    "lean_bridge_evidence",
)

# A source-defined type/class partition can be silently weakened by retaining
# only the convenient direction ``same class -> same feature row``.  This
# review is requested solely by a byte-pinned source context contract and is
# bound to a generated source/signature association.  Neither the trigger nor
# either required implication is inferred from a Lean declaration, binder, or
# field name.
SOURCE_EQUALITY_PARTITION_ANALYSIS_FIELD = "source_equality_partition_analysis"
SOURCE_EQUALITY_PARTITION_ASSOCIATION_FIELD = "source_equality_partition_association"
SOURCE_EQUALITY_PARTITION_REQUIREMENT_FIELD = "source_equality_partition"
SOURCE_EQUALITY_PARTITION_CONTRACTS_FIELD = "contracts"
SOURCE_EQUALITY_PARTITION_RELATION = "feature_equality_iff_class_equality"
SOURCE_EQUALITY_PARTITION_DIRECTIONS = (
    "feature_equality_implies_class_equality",
    "class_equality_implies_feature_equality",
)
SOURCE_EQUALITY_PARTITION_DIRECTION_VERDICTS = {
    "exposed_as_source_model_condition",
    "proved_from_source_primitives",
    "missing_or_weaker",
    "mismatch_or_open",
    "documented_partial_boundary",
}
SOURCE_EQUALITY_PARTITION_ACCEPTED_DIRECTION_VERDICTS = {
    "exposed_as_source_model_condition",
    "proved_from_source_primitives",
}
SOURCE_EQUALITY_PARTITION_ANALYSIS_FIELDS = (
    "semantic_association_sha256",
    "relation",
    *SOURCE_EQUALITY_PARTITION_DIRECTIONS,
    "lean_bridge_evidence",
)

# This source-scoped lane makes an equilibrium/best-response theorem account
# for every action-relevant observation branch.  The source map supplies a
# byte-pinned context describing the action and conditional-value semantics;
# the generated association then binds the review to the exact source content
# and current elaborated review signature.  No Lean declaration, predicate,
# field, binder, or function name selects this obligation.
STRATEGIC_OBSERVATION_TOTALITY_ANALYSIS_FIELD = (
    "strategic_observation_totality_analysis"
)
STRATEGIC_OBSERVATION_TOTALITY_ASSOCIATION_FIELD = (
    "strategic_observation_totality_association"
)
STRATEGIC_OBSERVATION_TOTALITY_REQUIREMENT_FIELD = (
    "strategic_observation_totality"
)
STRATEGIC_OBSERVATION_TOTALITY_CONTRACTS_FIELD = "contracts"
STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONTRACT_SCHEMA = 2
STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMA = 3
STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMAS = {
    STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONTRACT_SCHEMA,
    STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMA,
}
STRATEGIC_OBSERVATION_TOTALITY_LEGACY_REQUIREMENT_SCHEMA = 2
STRATEGIC_OBSERVATION_TOTALITY_REQUIREMENT_SCHEMA = 3
STRATEGIC_OBSERVATION_TOTALITY_REQUIREMENT_SCHEMAS = {
    STRATEGIC_OBSERVATION_TOTALITY_LEGACY_REQUIREMENT_SCHEMA,
    STRATEGIC_OBSERVATION_TOTALITY_REQUIREMENT_SCHEMA,
}
STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONDITIONALIZATION_SCOPE_FIELD = (
    "conditionalization_scope"
)
STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES_FIELD = (
    "conditionalization_scopes"
)
STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPE_EVIDENCE_FIELD = (
    "conditionalization_scope_evidence"
)
STRATEGIC_OBSERVATION_TOTALITY_CONDITIONING_POPULATION_SCOPES = {
    "entire_source_population",
    "source_defined_subpopulation_or_access_event",
    "source_defined_conditioned_or_restricted_population",
}
STRATEGIC_OBSERVATION_TOTALITY_SELECTED_EVENT_HISTORY_SCOPES = {
    "single_action_without_prior_strategic_history",
    "source_defined_sequential_action_history",
    "source_defined_pre_action_state_or_history",
}
STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES = {
    "positive_measurable_event",
    "source_totalized_pointwise_observation_branch",
    "ae_regular_conditional_distribution_or_disintegration",
}
STRATEGIC_OBSERVATION_TOTALITY_SAFE_VERDICTS = {
    "source_totalizes_all_action_relevant_observations_checked",
    "all_feasible_action_observations_positive_checked",
    "offpath_action_infeasibility_checked",
    "source_explicitly_restricts_equilibrium_domain_checked",
    "source_ae_or_event_scoped_equilibrium_checked",
}
STRATEGIC_OBSERVATION_TOTALITY_OPEN_VERDICTS = {
    "mismatch_or_open",
    "documented_partial_boundary",
}
STRATEGIC_OBSERVATION_TOTALITY_VERDICTS = {
    *STRATEGIC_OBSERVATION_TOTALITY_SAFE_VERDICTS,
    *STRATEGIC_OBSERVATION_TOTALITY_OPEN_VERDICTS,
}
STRATEGIC_OBSERVATION_TOTALITY_BRANCH_DISPOSITIONS = {
    "all_action_relevant_observations_positive",
    "source_totalizes_zero_probability_observations",
    "offpath_action_is_infeasible",
    "source_equilibrium_domain_excludes_offpath_branch",
    "source_ae_or_event_scope_excludes_pointwise_offpath_choice",
    "source_leaves_branch_unresolved",
    "lean_only_offpath_completion",
}
STRATEGIC_OBSERVATION_TOTALITY_SAFE_BRANCH_DISPOSITIONS = {
    "all_action_relevant_observations_positive",
    "source_totalizes_zero_probability_observations",
    "offpath_action_is_infeasible",
    "source_equilibrium_domain_excludes_offpath_branch",
    "source_ae_or_event_scope_excludes_pointwise_offpath_choice",
}
STRATEGIC_OBSERVATION_TOTALITY_CONDITIONING_POPULATION_DISPOSITIONS = {
    "source_entire_population_carrier_checked",
    "source_conditioned_or_restricted_population_checked",
    "mixed_source_population_scopes_checked",
    "mismatch_or_open",
    "documented_partial_boundary",
}
STRATEGIC_OBSERVATION_TOTALITY_SAFE_CONDITIONING_POPULATION_DISPOSITIONS = {
    "source_entire_population_carrier_checked",
    "source_conditioned_or_restricted_population_checked",
    "mixed_source_population_scopes_checked",
}
STRATEGIC_OBSERVATION_TOTALITY_SELECTED_EVENT_HISTORY_DISPOSITIONS = {
    "single_action_event_checked",
    "source_history_in_selected_event_checked",
    "mixed_source_history_scopes_checked",
    "mismatch_or_open",
    "documented_partial_boundary",
}
STRATEGIC_OBSERVATION_TOTALITY_SAFE_SELECTED_EVENT_HISTORY_DISPOSITIONS = {
    "single_action_event_checked",
    "source_history_in_selected_event_checked",
    "mixed_source_history_scopes_checked",
}
STRATEGIC_OBSERVATION_TOTALITY_EVENT_MEASURABILITY_DISPOSITIONS = {
    "measurable_action_and_observation_event_checked",
    "source_event_measurability_or_null_handling_open",
    "mismatch_or_open",
    "documented_partial_boundary",
}
STRATEGIC_OBSERVATION_TOTALITY_SAFE_EVENT_MEASURABILITY_DISPOSITIONS = {
    "measurable_action_and_observation_event_checked",
}
STRATEGIC_OBSERVATION_TOTALITY_FIBRE_BASE_SCOPE_DISPOSITIONS = {
    "positive_measurable_event_checked",
    "source_totalized_pointwise_fibres_checked",
    "ae_fibre_base_scope_and_version_checked",
    "mixed_source_conditionalization_scopes_checked",
    "mismatch_or_open",
    "documented_partial_boundary",
}
STRATEGIC_OBSERVATION_TOTALITY_SAFE_FIBRE_BASE_SCOPE_DISPOSITIONS = {
    "positive_measurable_event_checked",
    "source_totalized_pointwise_fibres_checked",
    "ae_fibre_base_scope_and_version_checked",
    "mixed_source_conditionalization_scopes_checked",
}
STRATEGIC_OBSERVATION_TOTALITY_DISPOSITION_FIELDS = {
    "zero_probability_branch_disposition",
    "conditioning_population_disposition",
    "selected_event_history_disposition",
    "event_measurability_disposition",
    "fibre_base_scope_disposition",
}
STRATEGIC_OBSERVATION_TOTALITY_ANALYSIS_FIELDS = (
    "semantic_association_sha256",
    "equilibrium_action_domain",
    "lean_feasible_action_domain",
    "conditioning_population_disposition",
    "conditioning_population_carrier_evidence",
    "selected_event_history_disposition",
    "selected_event_history_evidence",
    "event_measurability_disposition",
    "action_observation_event_measurability_evidence",
    "fibre_base_scope_disposition",
    "ae_fibre_or_base_scope_evidence",
    "observation_branch_analysis",
    "zero_probability_branch_disposition",
    "conditional_value_totality",
    "offpath_completion_or_infeasibility_evidence",
    "lean_bridge_evidence",
)

# Conditional expectations, posterior/PBO beliefs, and conditional laws need a
# source-pinned information-set comparison even when the source row is not a
# strategic equilibrium.  The source contract is attached by source semantic
# identity plus the current elaborated review signature; these protocol labels
# are not inferred from Lean theorem, function, binder, or field names.
CONDITIONING_INFORMATION_ANALYSIS_FIELD = "conditioning_information_analysis"
CONDITIONING_INFORMATION_ASSOCIATION_FIELD = "conditioning_information_association"
CONDITIONING_INFORMATION_REQUIREMENT_FIELD = "conditioning_information"
CONDITIONING_INFORMATION_CONTRACTS_FIELD = "contracts"
CONDITIONING_INFORMATION_REQUIREMENT_SCHEMA = 1
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
CONDITIONING_INFORMATION_MATCH_VERDICT = (
    "source_and_lean_conditioning_information_match"
)
CONDITIONING_INFORMATION_OPEN_VERDICTS = {
    "mismatch_or_open",
    "documented_partial_boundary",
}
CONDITIONING_INFORMATION_ANALYSIS_VERDICTS = {
    CONDITIONING_INFORMATION_MATCH_VERDICT,
    *CONDITIONING_INFORMATION_OPEN_VERDICTS,
}
CONDITIONING_INFORMATION_ANALYSIS_FIELDS = (
    "semantic_association_sha256",
    "verdict",
    "contracts",
    "lean_bridge_evidence",
)
CONDITIONING_INFORMATION_RESPONSE_CONTRACT_FIELDS = {
    "source_semantic_sha256",
    "source_conditional_value_kind",
    "lean_conditional_value_kind",
    "source_observed_component_ids",
    "lean_observed_components",
    "source_action_selection_stage_ids",
    "lean_action_selection_stages",
    "source_law_population",
    "lean_law_population",
    "source_conditionalization_scopes",
    "lean_conditionalization_scopes",
    "comparison_evidence",
}
CONDITIONING_INFORMATION_LEAN_COMPONENT_FIELDS = {
    "source_component_id",
    "description",
}
CONDITIONING_INFORMATION_LEAN_STAGE_FIELDS = {
    "source_stage_id",
    "description",
}

# A paper-facing theorem can hide a material model construction behind a
# record-valued argument: for example, a renewal-cycle package, an execution
# trace, or a conditional-law certificate.  The ordinary source-model review
# sees the record's expanded fields, but a source map must opt in before this
# stricter question is asked: did Lean *derive* the declared consequence from
# the literal source primitives, or merely receive it as a field?  The source
# contract and generated association select the obligation; no theorem,
# record, field, binder, or function name does.
SOURCE_MODEL_DERIVATION_ANALYSIS_FIELD = "source_model_derivation_analysis"
SOURCE_MODEL_DERIVATION_ASSOCIATION_FIELD = "source_model_derivation_association"
SOURCE_MODEL_DERIVATION_REQUIREMENT_FIELD = "source_model_derivation"
SOURCE_MODEL_DERIVATION_CONTRACTS_FIELD = "contracts"
SOURCE_MODEL_DERIVATION_CALLER_SUPPLIED_BASIS_FIELD = (
    "caller_supplied_model_construction_basis"
)
SOURCE_MODEL_DERIVATION_REQUIREMENT_SCHEMA = 2
SOURCE_MODEL_DERIVATION_CONTRACT_SCHEMA = 2
SOURCE_MODEL_DERIVATION_SAFE_VERDICT = "derived_from_source_primitives"
SOURCE_MODEL_DERIVATION_OPEN_VERDICTS = {
    "mismatch_or_open",
    "documented_partial_boundary",
}
SOURCE_MODEL_DERIVATION_ANALYSIS_VERDICTS = {
    SOURCE_MODEL_DERIVATION_SAFE_VERDICT,
    *SOURCE_MODEL_DERIVATION_OPEN_VERDICTS,
}
SOURCE_MODEL_DERIVATION_SAFE_ROUTE = (
    "checked_lean_derivation_from_source_primitives"
)
SOURCE_MODEL_DERIVATION_OPEN_ROUTES = {
    "caller_supplied_derived_conclusion",
    "unresolved_or_no_checked_derivation",
}
SOURCE_MODEL_DERIVATION_ROUTES = {
    SOURCE_MODEL_DERIVATION_SAFE_ROUTE,
    *SOURCE_MODEL_DERIVATION_OPEN_ROUTES,
}
SOURCE_MODEL_DERIVATION_RESPONSE_CONTRACT_FIELDS = {
    "source_semantic_sha256",
    "source_primitive_component_ids",
    "lean_primitive_components",
    "source_derived_conclusion_description",
    "lean_derived_conclusion_description",
    "derivation_route",
    "derivation_evidence",
}
SOURCE_MODEL_DERIVATION_ANALYSIS_FIELDS = {
    "semantic_association_sha256",
    "verdict",
    "contracts",
    "lean_bridge_evidence",
}
SOURCE_MODEL_DERIVATION_LEAN_PRIMITIVE_COMPONENT_FIELDS = {
    "source_primitive_component_id",
    "description",
}
SOURCE_MODEL_DERIVATION_SOURCE_COMPONENT_FIELDS = {
    "id",
    "description",
    "source_location",
    "source_anchor_evidence",
}
SOURCE_MODEL_DERIVATION_SOURCE_CONCLUSION_FIELDS = {
    "description",
    "source_location",
    "source_anchor_evidence",
}
SOURCE_MODEL_DERIVATION_SOURCE_ANCHOR_FIELDS = {
    "path",
    "line_start",
    "line_end",
    "quoted_text",
    "quoted_text_sha256",
}
SOURCE_MODEL_DERIVATION_SEMANTIC_ID_RE = re.compile(
    r"^[a-z][a-z0-9_]*(?:[.-][a-z][a-z0-9_]*)*$"
)
_SOURCE_MODEL_DERIVATION_SOURCE_LOCATION_RE = re.compile(
    r"^[^:\s]+:\d+(?:-\d+)?$"
)
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$", re.I)
_SOURCE_CARRIER_IDENTITY_RE = re.compile(
    r"\b(?:same|single|shared|one|joint|carrier|outcome|sample\s+path|"
    r"random\s+variable|underlying)\b",
    re.I,
)
_STAGE_IDENTITY_RE = re.compile(
    r"\b(?:same|single|shared|joint|conditional|coupl(?:e|ing)|"
    r"disintegrat(?:ion|e)|not\s+resampl(?:ed|ing)|one\s+draw|"
    r"kernel\s+composition)\b",
    re.I,
)
_JOINT_LAW_BRIDGE_RE = re.compile(
    r"(?:\b(?:checked|proved|proven|theorem|lemma|deriv(?:ed|ation)?)\b"
    r"[\s\S]{0,180}\b(?:joint\s+law|pushforward|map|measure|"
    r"distribution|kernel|disintegrat|equality|equivalence)\b|"
    r"\b(?:joint\s+law|pushforward|map|measure|distribution|kernel|"
    r"disintegrat|equality|equivalence)\b[\s\S]{0,180}"
    r"\b(?:checked|proved|proven|theorem|lemma|deriv(?:ed|ation)?)\b)",
    re.I,
)
_SOURCE_PUSHFORWARD_TRANSPORT_RE = re.compile(
    r"\b(?:pushforward|map(?:ped)?\s+(?:measure|law|distribution)|"
    r"image\s+measure|law\s+equality|measure\s+equality|"
    r"distribution\s+equality|condition(?:ed|ing)|restrict(?:ed|ion)|event)\b",
    re.I,
)
_GENERATED_MEASURE_DISCLOSURE_RE = re.compile(
    r"\b(?:generated|constructed|product|kernel|weighted|tilt(?:ed)?|"
    r"likelihood|not\s+(?:a\s+)?source\s+pushforward|no\s+source\s+"
    r"pushforward)\b",
    re.I,
)
_RATE_FAMILY_RE = re.compile(
    r"(?:\b(?:for\s+all|every|each|uniform(?:ly)?)\b[\s\S]{0,100}"
    r"\b(?:rate|parameter)\b|\b(?:rate|parameter)\b[\s\S]{0,100}"
    r"\b(?:for\s+all|every|each|uniform(?:ly)?)\b)"
    r"[\s\S]{0,100}\b(?:family|index(?:ed|ing)?|same\s+model|"
    r"shared\s+model|bridge)\b",
    re.I,
)


def source_carrier_coherence_analysis_errors(
    raw_dimension: dict[str, Any],
    response: dict[str, Any],
    *,
    name_only: Callable[[str], bool] | None = None,
) -> list[str]:
    """Validate a source-carrier/joint-law coherence review when requested.

    The generated trigger is tied to expanded measure/kernel/carrier structure.
    This validator intentionally does not infer a process from identifiers or
    prose labels.  It instead requires the reviewer to make the carrier,
    stage-coupling, measure role, and rate scope explicit enough for an
    independent repair agent to check the actual bridge.
    """

    if not (
        bool(raw_dimension.get("detected_from_expanded_surface"))
        and raw_dimension.get(
            "requires_source_carrier_coherence_analysis_when_detected"
        )
        is True
    ):
        return []

    field = SOURCE_CARRIER_COHERENCE_ANALYSIS_FIELD
    analysis = response.get(field)
    if not isinstance(analysis, dict):
        return [f"needs `{field}` object"]

    errors: list[str] = []
    verdict = str(analysis.get("verdict") or "").strip()
    if verdict not in SOURCE_CARRIER_COHERENCE_ANALYSIS_VERDICTS:
        errors.append(
            f"`{field}.verdict` must be one of "
            + ", ".join(sorted(SOURCE_CARRIER_COHERENCE_ANALYSIS_VERDICTS))
        )
    for required_field in SOURCE_CARRIER_COHERENCE_FIELDS:
        value = str(analysis.get(required_field) or "").strip()
        if not value:
            errors.append(f"`{field}.{required_field}` is required")
        elif required_field in SOURCE_CARRIER_COHERENCE_NARRATIVE_FIELDS and (
            BARE_QUALIFIED_REFERENCE_RE.fullmatch(value)
            or (name_only is not None and name_only(value))
        ):
            errors.append(
                f"`{field}.{required_field}` is name-only evidence; "
                "state the source and expanded Lean semantics"
            )

    construction = str(analysis.get("measure_construction") or "").strip()
    if (
        construction
        and construction not in SOURCE_CARRIER_COHERENCE_MEASURE_CONSTRUCTIONS
    ):
        errors.append(
            f"`{field}.measure_construction` must be one of "
            + ", ".join(sorted(SOURCE_CARRIER_COHERENCE_MEASURE_CONSTRUCTIONS))
        )

    source_rate_scope = str(analysis.get("source_rate_scope") or "").strip()
    if (
        source_rate_scope
        and source_rate_scope not in SOURCE_CARRIER_COHERENCE_SOURCE_RATE_SCOPES
    ):
        errors.append(
            f"`{field}.source_rate_scope` must be one of "
            + ", ".join(sorted(SOURCE_CARRIER_COHERENCE_SOURCE_RATE_SCOPES))
        )
    lean_rate_scope = str(analysis.get("lean_rate_scope") or "").strip()
    if (
        lean_rate_scope
        and lean_rate_scope not in SOURCE_CARRIER_COHERENCE_LEAN_RATE_SCOPES
    ):
        errors.append(
            f"`{field}.lean_rate_scope` must be one of "
            + ", ".join(sorted(SOURCE_CARRIER_COHERENCE_LEAN_RATE_SCOPES))
        )

    carrier = str(analysis.get("source_random_variable_carrier") or "").strip()
    lean_carrier = str(analysis.get("lean_random_variable_carrier") or "").strip()
    stages = str(analysis.get("stage_identity_or_resampling_evidence") or "").strip()
    bridge = str(analysis.get("joint_law_bridge_evidence") or "").strip()
    transport = str(analysis.get("measure_transport_evidence") or "").strip()
    rate_family = str(analysis.get("rate_family_evidence") or "").strip()

    source_constructions = {
        "single_source_carrier_pushforward",
        "source_conditioned_or_restricted_pushforward",
        "source_defined_joint_kernel_law",
    }
    generated_constructions = {
        "generated_product_or_kernel_measure",
        "weighted_or_tilted_measure",
    }
    source_pushforward_verdicts = {
        "source_carrier_pushforward_checked",
        "source_conditioned_or_restricted_pushforward_checked",
        "source_defined_joint_kernel_law_checked",
    }

    if construction in source_constructions:
        if not _SOURCE_CARRIER_IDENTITY_RE.search(carrier):
            errors.append(
                f"`{field}.source_random_variable_carrier` must identify the "
                "source carrier or one shared source random variable"
            )
        if not _SOURCE_CARRIER_IDENTITY_RE.search(lean_carrier):
            errors.append(
                f"`{field}.lean_random_variable_carrier` must identify the Lean "
                "carrier or one shared Lean random variable"
            )
        if not _STAGE_IDENTITY_RE.search(stages):
            errors.append(
                f"`{field}.stage_identity_or_resampling_evidence` must state how "
                "all stages use one joint draw, or why a source-defined conditional "
                "kernel composition does not resample a source variable"
            )
        if not _JOINT_LAW_BRIDGE_RE.search(bridge):
            errors.append(
                f"`{field}.joint_law_bridge_evidence` must identify checked joint-law, "
                "coupling, disintegration, pushforward, or measure-equality evidence"
            )
        if not _SOURCE_PUSHFORWARD_TRANSPORT_RE.search(transport):
            errors.append(
                f"`{field}.measure_transport_evidence` must state the source "
                "pushforward/conditioning/restriction transport, not just a likelihood "
                "calculation"
            )
    if construction in generated_constructions:
        if verdict in source_pushforward_verdicts:
            errors.append(
                f"`{field}` calls a generated or weighted measure a checked source "
                "pushforward; use an explicit source-carrier transport or record it as "
                "a generated/weighted non-source measure"
            )
        if not _GENERATED_MEASURE_DISCLOSURE_RE.search(transport):
            errors.append(
                f"`{field}.measure_transport_evidence` must explicitly disclose that "
                "the generated/weighted measure is not itself the source pushforward"
            )
    if verdict in source_pushforward_verdicts and construction not in source_constructions:
        errors.append(
            f"`{field}.verdict` claims a source pushforward but "
            f"`{field}.measure_construction` is not a source-carrier or source-defined "
            "joint-law construction"
        )

    if source_rate_scope in {"rate_free_claim", "rate_indexed_claim"}:
        if lean_rate_scope != "rate_indexed_family":
            errors.append(
                f"`{field}.lean_rate_scope` must be `rate_indexed_family` when the "
                "source claim is rate-free or rate-indexed; a fixed-rate witness cannot "
                "support the family claim"
            )
        if not _RATE_FAMILY_RE.search(rate_family):
            errors.append(
                f"`{field}.rate_family_evidence` must identify a checked all-rate "
                "indexed family bridge, not one selected rate"
            )
    return errors


def source_model_composition_analysis_errors(
    raw_dimension: dict[str, Any],
    response: dict[str, Any],
    *,
    name_only: Callable[[str], bool] | None = None,
) -> list[str]:
    """Validate a source-pinned selector/conditional/objective bridge.

    This check is intentionally independent of whether the expanded Lean type
    happens to contain a probability constructor.  The generator adds it only
    for a schema-2 source contract whose exact direct evidence route has a
    current source-semantic plus elaborated-signature association.  A response
    must choose one mathematically explicit bridge form rather than describing
    a familiar helper by name.
    """

    if raw_dimension.get("requires_source_model_composition_analysis") is not True:
        return []

    errors: list[str] = []
    requirement = raw_dimension.get(SOURCE_MODEL_COMPOSITION_REQUIREMENT_FIELD)
    clause_source_digests: list[str] = []
    if not isinstance(requirement, dict):
        errors.append(
            "has no generated source-model-composition source-clause requirement"
        )
    else:
        if requirement.get("schema") != 1:
            errors.append(
                "generated source-model-composition source-clause requirement must use schema 1"
            )
        raw_clauses = requirement.get(SOURCE_MODEL_COMPOSITION_CLAUSES_FIELD)
        if not isinstance(raw_clauses, list) or not raw_clauses:
            errors.append(
                "generated source-model-composition source-clause requirement has no clauses"
            )
        else:
            for index, raw_clause in enumerate(raw_clauses):
                prefix = (
                    f"generated source-model-composition source-clause requirement."
                    f"clauses[{index}]"
                )
                if not isinstance(raw_clause, dict):
                    errors.append(f"{prefix} is not an object")
                    continue
                source_digest = str(
                    raw_clause.get("source_semantic_sha256") or ""
                ).strip().lower()
                if not _SHA256_RE.fullmatch(source_digest):
                    errors.append(f"{prefix}.source_semantic_sha256 is missing or malformed")
                else:
                    clause_source_digests.append(source_digest)
                for clause_name in (
                    "selector_law",
                    "conditional_outcome_law",
                    "composed_objective_or_expectation",
                ):
                    clause = raw_clause.get(clause_name)
                    if not isinstance(clause, dict):
                        errors.append(f"{prefix}.{clause_name} is not an object")
                        continue
                    if not str(clause.get("semantic_statement") or "").strip():
                        errors.append(
                            f"{prefix}.{clause_name}.semantic_statement is missing"
                        )
                    anchors = clause.get("source_anchor_evidence")
                    if not isinstance(anchors, list) or not anchors:
                        errors.append(
                            f"{prefix}.{clause_name}.source_anchor_evidence is missing"
                        )
            if len(clause_source_digests) != len(set(clause_source_digests)):
                errors.append(
                    "generated source-model-composition source-clause requirement duplicates a source semantic identity"
                )

    association = raw_dimension.get(SOURCE_MODEL_COMPOSITION_ASSOCIATION_FIELD)
    expected_pin = ""
    if not isinstance(association, dict):
        errors.append(
            "has no generated source-model-composition semantic association"
        )
    else:
        if association.get("schema") != 2:
            errors.append(
                "generated source-model-composition association must use schema 2"
            )
        expected_pin = str(
            association.get("semantic_association_sha256") or ""
        ).strip().lower()
        if not _SHA256_RE.fullmatch(expected_pin):
            errors.append(
                "generated source-model-composition association lacks a current semantic_association_sha256"
            )
        raw_source_digests = association.get("source_item_semantic_sha256")
        association_source_digests: list[str] = []
        if not isinstance(raw_source_digests, list) or not raw_source_digests:
            errors.append(
                "generated source-model-composition association has no source semantic identities"
            )
        else:
            association_source_digests = [
                str(value or "").strip().lower() for value in raw_source_digests
            ]
            if (
                any(
                    not _SHA256_RE.fullmatch(value)
                    for value in association_source_digests
                )
                or len(association_source_digests)
                != len(set(association_source_digests))
            ):
                errors.append(
                    "generated source-model-composition association has malformed or duplicate source semantic identities"
                )
        signature = association.get("reviewed_elaborated_signature_identity")
        signature_sha = ""
        if not isinstance(signature, dict):
            errors.append(
                "generated source-model-composition association lacks a current elaborated review signature"
            )
        else:
            qualified = str(signature.get("qualified_declaration") or "").strip()
            signature_sha = str(
                signature.get("elaborated_signature_sha256") or ""
            ).strip().lower()
            if not qualified or "." not in qualified or not _SHA256_RE.fullmatch(
                signature_sha
            ):
                errors.append(
                    "generated source-model-composition association has an invalid elaborated review signature"
                )
        reviewed_identity = association.get("reviewed_declaration_identity")
        if not isinstance(reviewed_identity, dict):
            errors.append(
                "generated source-model-composition association lacks a reviewed declaration identity"
            )
        else:
            reviewed_qualified = str(
                reviewed_identity.get("qualified_declaration") or ""
            ).strip()
            reviewed_sha = str(
                reviewed_identity.get("declaration_sha256") or ""
            ).strip().lower()
            signature_qualified = (
                str(signature.get("qualified_declaration") or "").strip()
                if isinstance(signature, dict)
                else ""
            )
            if (
                not reviewed_qualified
                or "." not in reviewed_qualified
                or not _SHA256_RE.fullmatch(reviewed_sha)
                or reviewed_qualified != signature_qualified
            ):
                errors.append(
                    "generated source-model-composition association has an invalid reviewed declaration identity"
                )
        if clause_source_digests and association_source_digests:
            if sorted(clause_source_digests) != sorted(association_source_digests):
                errors.append(
                    "generated source-model-composition association source identities do not match its source clauses"
                )
        if association_source_digests and _SHA256_RE.fullmatch(signature_sha):
            expected_association_pin = hashlib.sha256(
                json.dumps(
                    {
                        "schema": 2,
                        "source_item_semantic_sha256": sorted(association_source_digests),
                        "elaborated_signature_sha256": signature_sha,
                    },
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode("utf-8")
            ).hexdigest()
            if expected_pin != expected_association_pin:
                errors.append(
                    "generated source-model-composition association semantic_association_sha256 does not match its current source/signature pins"
                )

    field = SOURCE_MODEL_COMPOSITION_ANALYSIS_FIELD
    analysis = response.get(field)
    if not isinstance(analysis, dict):
        return errors + [f"needs `{field}` object"]
    bridge_form = str(analysis.get("bridge_form") or "").strip()
    if bridge_form not in SOURCE_MODEL_COMPOSITION_BRIDGE_FORMS:
        errors.append(
            f"`{field}.bridge_form` must be one of "
            + ", ".join(sorted(SOURCE_MODEL_COMPOSITION_BRIDGE_FORMS))
        )
    supplied_pin = str(
        analysis.get("semantic_association_sha256") or ""
    ).strip().lower()
    if not _SHA256_RE.fullmatch(expected_pin) or supplied_pin != expected_pin:
        errors.append(
            f"`{field}.semantic_association_sha256` must equal the current generated "
            "source-model-composition semantic association pin"
        )
    for required_field in SOURCE_MODEL_COMPOSITION_ANALYSIS_FIELDS[1:]:
        value = str(analysis.get(required_field) or "").strip()
        if not value:
            errors.append(f"`{field}.{required_field}` is required")
        elif BARE_QUALIFIED_REFERENCE_RE.fullmatch(value) or (
            name_only is not None and name_only(value)
        ):
            errors.append(
                f"`{field}.{required_field}` is name-only evidence; state the "
                "source clause and checked Lean semantics"
            )
    return errors


def source_equality_partition_analysis_errors(
    raw_dimension: dict[str, Any],
    response: dict[str, Any],
    *,
    name_only: Callable[[str], bool] | None = None,
) -> list[str]:
    """Validate an exact source-defined equality-partition comparison.

    A generated request is valid only when a byte-pinned source context says
    that class labels are *exactly* equality classes of the described feature.
    The response must then account for both implications independently.  A
    one-way within-class agreement is explicitly a weaker result, not a
    source-faithful partition.
    """

    if raw_dimension.get("requires_source_equality_partition_analysis") is not True:
        return []

    errors: list[str] = []
    requirement = raw_dimension.get(SOURCE_EQUALITY_PARTITION_REQUIREMENT_FIELD)
    contract_source_digests: list[str] = []
    if not isinstance(requirement, dict):
        errors.append("has no generated source-equality-partition requirement")
    else:
        if requirement.get("schema") != 1:
            errors.append(
                "generated source-equality-partition requirement must use schema 1"
            )
        raw_contracts = requirement.get(SOURCE_EQUALITY_PARTITION_CONTRACTS_FIELD)
        if not isinstance(raw_contracts, list) or not raw_contracts:
            errors.append(
                "generated source-equality-partition requirement has no contracts"
            )
        else:
            for index, raw_contract in enumerate(raw_contracts):
                prefix = (
                    "generated source-equality-partition requirement."
                    f"contracts[{index}]"
                )
                if not isinstance(raw_contract, dict):
                    errors.append(f"{prefix} is not an object")
                    continue
                source_digest = str(
                    raw_contract.get("source_semantic_sha256") or ""
                ).strip().lower()
                if not _SHA256_RE.fullmatch(source_digest):
                    errors.append(
                        f"{prefix}.source_semantic_sha256 is missing or malformed"
                    )
                else:
                    contract_source_digests.append(source_digest)
                for field_name in ("source_location", "explanation"):
                    if not str(raw_contract.get(field_name) or "").strip():
                        errors.append(f"{prefix}.{field_name} is missing")
                anchors = raw_contract.get("source_anchor_evidence")
                if not isinstance(anchors, list) or not anchors:
                    errors.append(f"{prefix}.source_anchor_evidence is missing")
                partition_contract = raw_contract.get("equality_partition_contract")
                if not isinstance(partition_contract, dict):
                    errors.append(f"{prefix}.equality_partition_contract is not an object")
                    continue
                if partition_contract.get("schema") != 1:
                    errors.append(
                        f"{prefix}.equality_partition_contract.schema must be 1"
                    )
                if (
                    partition_contract.get("relation")
                    != SOURCE_EQUALITY_PARTITION_RELATION
                ):
                    errors.append(
                        f"{prefix}.equality_partition_contract.relation must be "
                        f"`{SOURCE_EQUALITY_PARTITION_RELATION}`"
                    )
                for field_name in ("feature_description", "class_description"):
                    if not str(partition_contract.get(field_name) or "").strip():
                        errors.append(
                            f"{prefix}.equality_partition_contract.{field_name} "
                            "is missing"
                        )
                directions = partition_contract.get("required_directions")
                normalized_directions = (
                    [direction.strip() for direction in directions]
                    if isinstance(directions, list)
                    and all(isinstance(direction, str) for direction in directions)
                    else []
                )
                if (
                    set(normalized_directions)
                    != set(SOURCE_EQUALITY_PARTITION_DIRECTIONS)
                    or len(normalized_directions)
                    != len(SOURCE_EQUALITY_PARTITION_DIRECTIONS)
                ):
                    errors.append(
                        f"{prefix}.equality_partition_contract.required_directions "
                        "must contain both equality directions exactly once"
                    )
            if len(contract_source_digests) != len(set(contract_source_digests)):
                errors.append(
                    "generated source-equality-partition requirement duplicates a "
                    "source semantic identity"
                )

    association = raw_dimension.get(SOURCE_EQUALITY_PARTITION_ASSOCIATION_FIELD)
    expected_pin = ""
    association_source_digests: list[str] = []
    signature_sha = ""
    if not isinstance(association, dict):
        errors.append("has no generated source-equality-partition semantic association")
    else:
        if association.get("schema") != 2:
            errors.append(
                "generated source-equality-partition association must use schema 2"
            )
        expected_pin = str(
            association.get("semantic_association_sha256") or ""
        ).strip().lower()
        if not _SHA256_RE.fullmatch(expected_pin):
            errors.append(
                "generated source-equality-partition association lacks a current "
                "semantic_association_sha256"
            )
        raw_source_digests = association.get("source_item_semantic_sha256")
        if not isinstance(raw_source_digests, list) or not raw_source_digests:
            errors.append(
                "generated source-equality-partition association has no source semantic identities"
            )
        else:
            association_source_digests = [
                str(value or "").strip().lower() for value in raw_source_digests
            ]
            if (
                any(
                    not _SHA256_RE.fullmatch(value)
                    for value in association_source_digests
                )
                or len(association_source_digests)
                != len(set(association_source_digests))
            ):
                errors.append(
                    "generated source-equality-partition association has malformed "
                    "or duplicate source semantic identities"
                )
        signature = association.get("reviewed_elaborated_signature_identity")
        if not isinstance(signature, dict):
            errors.append(
                "generated source-equality-partition association lacks a current "
                "elaborated review signature"
            )
        else:
            qualified = str(signature.get("qualified_declaration") or "").strip()
            signature_sha = str(
                signature.get("elaborated_signature_sha256") or ""
            ).strip().lower()
            if not qualified or "." not in qualified or not _SHA256_RE.fullmatch(
                signature_sha
            ):
                errors.append(
                    "generated source-equality-partition association has an invalid "
                    "elaborated review signature"
                )
        reviewed_identity = association.get("reviewed_declaration_identity")
        if not isinstance(reviewed_identity, dict):
            errors.append(
                "generated source-equality-partition association lacks a reviewed "
                "declaration identity"
            )
        else:
            reviewed_qualified = str(
                reviewed_identity.get("qualified_declaration") or ""
            ).strip()
            reviewed_sha = str(
                reviewed_identity.get("declaration_sha256") or ""
            ).strip().lower()
            signature_qualified = (
                str(signature.get("qualified_declaration") or "").strip()
                if isinstance(signature, dict)
                else ""
            )
            if (
                not reviewed_qualified
                or "." not in reviewed_qualified
                or not _SHA256_RE.fullmatch(reviewed_sha)
                or reviewed_qualified != signature_qualified
            ):
                errors.append(
                    "generated source-equality-partition association has an invalid "
                    "reviewed declaration identity"
                )
        if contract_source_digests and association_source_digests and sorted(
            contract_source_digests
        ) != sorted(association_source_digests):
            errors.append(
                "generated source-equality-partition association source identities "
                "do not match its source contexts"
            )
        if association_source_digests and _SHA256_RE.fullmatch(signature_sha):
            expected_association_pin = hashlib.sha256(
                json.dumps(
                    {
                        "schema": 2,
                        "source_item_semantic_sha256": sorted(
                            association_source_digests
                        ),
                        "elaborated_signature_sha256": signature_sha,
                    },
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode("utf-8")
            ).hexdigest()
            if expected_pin != expected_association_pin:
                errors.append(
                    "generated source-equality-partition association "
                    "semantic_association_sha256 does not match its current "
                    "source/signature pins"
                )

    field = SOURCE_EQUALITY_PARTITION_ANALYSIS_FIELD
    analysis = response.get(field)
    if not isinstance(analysis, dict):
        return errors + [f"needs `{field}` object"]
    supplied_pin = str(
        analysis.get("semantic_association_sha256") or ""
    ).strip().lower()
    if not _SHA256_RE.fullmatch(expected_pin) or supplied_pin != expected_pin:
        errors.append(
            f"`{field}.semantic_association_sha256` must equal the current generated "
            "source-equality-partition semantic association pin"
        )
    if analysis.get("relation") != SOURCE_EQUALITY_PARTITION_RELATION:
        errors.append(
            f"`{field}.relation` must be `{SOURCE_EQUALITY_PARTITION_RELATION}`"
        )
    direction_verdicts: list[str] = []
    for direction in SOURCE_EQUALITY_PARTITION_DIRECTIONS:
        response_direction = analysis.get(direction)
        if not isinstance(response_direction, dict):
            errors.append(f"`{field}.{direction}` must be an object")
            continue
        verdict = str(response_direction.get("verdict") or "").strip()
        direction_verdicts.append(verdict)
        if verdict not in SOURCE_EQUALITY_PARTITION_DIRECTION_VERDICTS:
            errors.append(
                f"`{field}.{direction}.verdict` must be one of "
                + ", ".join(
                    sorted(SOURCE_EQUALITY_PARTITION_DIRECTION_VERDICTS)
                )
            )
        evidence = str(response_direction.get("lean_evidence") or "").strip()
        if not evidence:
            errors.append(f"`{field}.{direction}.lean_evidence` is required")
        elif BARE_QUALIFIED_REFERENCE_RE.fullmatch(evidence) or (
            name_only is not None and name_only(evidence)
        ):
            errors.append(
                f"`{field}.{direction}.lean_evidence` is name-only evidence; "
                "state the expanded implication or checked source-model bridge"
            )
    bridge = str(analysis.get("lean_bridge_evidence") or "").strip()
    if not bridge:
        errors.append(f"`{field}.lean_bridge_evidence` is required")
    elif BARE_QUALIFIED_REFERENCE_RE.fullmatch(bridge) or (
        name_only is not None and name_only(bridge)
    ):
        errors.append(
            f"`{field}.lean_bridge_evidence` is name-only evidence; state how the "
            "two expanded implications establish the source equality partition"
        )

    outer_verdict = str(response.get("verdict") or "").strip()
    if outer_verdict == "not_applicable":
        errors.append(
            "cannot mark a source-required equality-partition dimension not_applicable"
        )
    if any(
        verdict not in SOURCE_EQUALITY_PARTITION_ACCEPTED_DIRECTION_VERDICTS
        for verdict in direction_verdicts
    ) and outer_verdict == "matches_source_model":
        errors.append(
            "records a missing/weaker equality-partition direction while the "
            "enclosing dimension claims matches_source_model"
        )
    return errors


def strategic_observation_totality_analysis_errors(
    raw_dimension: dict[str, Any],
    response: dict[str, Any],
    *,
    name_only: Callable[[str], bool] | None = None,
) -> list[str]:
    """Validate a source-game observation-totality review when requested.

    A best-response result is source-faithful only if every observation branch
    used by a feasible action has a source-backed value, or the source itself
    proves that the branch/action lies outside the equilibrium comparison.
    In particular, a finite payoff or posterior silently supplied only by Lean
    on an off-path zero-probability observation cannot certify a full match.
    The trigger and route are source-content/signature pinned; none of this
    logic inspects a theorem, function, field, or binder name.
    """

    if raw_dimension.get("requires_strategic_observation_totality_analysis") is not True:
        return []

    errors: list[str] = []
    requirement = raw_dimension.get(STRATEGIC_OBSERVATION_TOTALITY_REQUIREMENT_FIELD)
    contract_source_digests: list[str] = []
    conditioning_population_scopes: list[str] = []
    selected_event_history_scopes: list[str] = []
    conditionalization_scopes: list[str] = []
    requirement_schema: int | None = None
    if not isinstance(requirement, dict):
        errors.append("has no generated strategic-observation-totality requirement")
    else:
        raw_requirement_schema = requirement.get("schema")
        if (
            isinstance(raw_requirement_schema, int)
            and not isinstance(raw_requirement_schema, bool)
            and raw_requirement_schema
            in STRATEGIC_OBSERVATION_TOTALITY_REQUIREMENT_SCHEMAS
        ):
            assert isinstance(raw_requirement_schema, int)
            requirement_schema = raw_requirement_schema
        else:
            errors.append(
                "generated strategic-observation-totality requirement must use schema "
                f"{STRATEGIC_OBSERVATION_TOTALITY_LEGACY_REQUIREMENT_SCHEMA} or "
                f"{STRATEGIC_OBSERVATION_TOTALITY_REQUIREMENT_SCHEMA}"
            )
        raw_contracts = requirement.get(STRATEGIC_OBSERVATION_TOTALITY_CONTRACTS_FIELD)
        if not isinstance(raw_contracts, list) or not raw_contracts:
            errors.append(
                "generated strategic-observation-totality requirement has no contracts"
            )
        else:
            for index, raw_contract in enumerate(raw_contracts):
                prefix = (
                    "generated strategic-observation-totality requirement."
                    f"contracts[{index}]"
                )
                if not isinstance(raw_contract, dict):
                    errors.append(f"{prefix} is not an object")
                    continue
                source_digest = str(
                    raw_contract.get("source_semantic_sha256") or ""
                ).strip().lower()
                if not _SHA256_RE.fullmatch(source_digest):
                    errors.append(
                        f"{prefix}.source_semantic_sha256 is missing or malformed"
                    )
                else:
                    contract_source_digests.append(source_digest)
                for field_name in ("source_location", "explanation"):
                    if not str(raw_contract.get(field_name) or "").strip():
                        errors.append(f"{prefix}.{field_name} is missing")
                anchors = raw_contract.get("source_anchor_evidence")
                if not isinstance(anchors, list) or not anchors:
                    errors.append(f"{prefix}.source_anchor_evidence is missing")
                context_contract = raw_contract.get(
                    "strategic_observation_totality_contract"
                )
                if not isinstance(context_contract, dict):
                    errors.append(
                        f"{prefix}.strategic_observation_totality_contract is not an object"
                    )
                    continue
                contract_schema = context_contract.get("schema")
                contract_schema_is_supported = (
                    isinstance(contract_schema, int)
                    and not isinstance(contract_schema, bool)
                    and contract_schema
                    in STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMAS
                )
                if not contract_schema_is_supported:
                    errors.append(
                        f"{prefix}.strategic_observation_totality_contract.schema must be "
                        f"{STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONTRACT_SCHEMA} or "
                        f"{STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMA}"
                    )
                elif (
                    requirement_schema
                    == STRATEGIC_OBSERVATION_TOTALITY_LEGACY_REQUIREMENT_SCHEMA
                    and contract_schema
                    != STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONTRACT_SCHEMA
                ):
                    errors.append(
                        f"{prefix}.strategic_observation_totality_contract.schema must be "
                        f"{STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONTRACT_SCHEMA} under "
                        f"legacy generated requirement schema "
                        f"{STRATEGIC_OBSERVATION_TOTALITY_LEGACY_REQUIREMENT_SCHEMA}"
                    )
                action_scope = str(
                    context_contract.get("equilibrium_action_scope") or ""
                ).strip()
                if action_scope not in {
                    "all_feasible_actions",
                    "source_defined_restricted_action_domain",
                }:
                    errors.append(
                        f"{prefix}.strategic_observation_totality_contract "
                        "has an invalid equilibrium action scope"
                    )
                value_kind = str(
                    context_contract.get("conditional_value_kind") or ""
                ).strip()
                if value_kind not in {
                    "conditional_expectation_or_posterior",
                    "observation_contingent_payoff_or_belief",
                }:
                    errors.append(
                        f"{prefix}.strategic_observation_totality_contract "
                        "has an invalid conditional-value kind"
                    )
                conditioning_population_scope = str(
                    context_contract.get("conditioning_population_scope") or ""
                ).strip()
                if (
                    conditioning_population_scope
                    not in STRATEGIC_OBSERVATION_TOTALITY_CONDITIONING_POPULATION_SCOPES
                ):
                    errors.append(
                        f"{prefix}.strategic_observation_totality_contract has an invalid "
                        "conditioning-population scope"
                    )
                else:
                    conditioning_population_scopes.append(
                        conditioning_population_scope
                    )
                selected_event_history_scope = str(
                    context_contract.get("selected_event_history_scope") or ""
                ).strip()
                if (
                    selected_event_history_scope
                    not in STRATEGIC_OBSERVATION_TOTALITY_SELECTED_EVENT_HISTORY_SCOPES
                ):
                    errors.append(
                        f"{prefix}.strategic_observation_totality_contract has an invalid "
                        "selected-event history scope"
                    )
                else:
                    selected_event_history_scopes.append(selected_event_history_scope)
                if (
                    contract_schema
                    == STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONTRACT_SCHEMA
                ):
                    if (
                        STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES_FIELD
                        in context_contract
                    ):
                        errors.append(
                            f"{prefix}.strategic_observation_totality_contract mixes "
                            "legacy and schema-3 conditionalization fields"
                        )
                    conditionalization_scope = str(
                        context_contract.get(
                            STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONDITIONALIZATION_SCOPE_FIELD
                        )
                        or ""
                    ).strip()
                    if (
                        conditionalization_scope
                        not in STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES
                    ):
                        errors.append(
                            f"{prefix}.strategic_observation_totality_contract has an "
                            "invalid legacy conditionalization scope"
                        )
                    else:
                        conditionalization_scopes.append(conditionalization_scope)
                elif contract_schema == STRATEGIC_OBSERVATION_TOTALITY_CONTRACT_SCHEMA:
                    if (
                        STRATEGIC_OBSERVATION_TOTALITY_LEGACY_CONDITIONALIZATION_SCOPE_FIELD
                        in context_contract
                    ):
                        errors.append(
                            f"{prefix}.strategic_observation_totality_contract mixes "
                            "legacy and schema-3 conditionalization fields"
                        )
                    raw_scopes = context_contract.get(
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
                            scope
                            not in STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPES
                            for scope in scopes
                        )
                    ):
                        errors.append(
                            f"{prefix}.strategic_observation_totality_contract has an "
                            "invalid conditionalization-scope list"
                        )
                    else:
                        conditionalization_scopes.extend(scopes)
                for field_name in (
                    "action_description",
                    "observation_description",
                    "conditional_value_description",
                    "conditioning_population_description",
                    "selected_event_history_description",
                    "selected_event_description",
                ):
                    if not str(context_contract.get(field_name) or "").strip():
                        errors.append(
                            f"{prefix}.strategic_observation_totality_contract."
                            f"{field_name} is missing"
                        )
                checks = context_contract.get("required_checks")
                expected_checks = {
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
                normalized_checks = (
                    [check.strip() for check in checks]
                    if isinstance(checks, list)
                    and all(isinstance(check, str) for check in checks)
                    else []
                )
                if (
                    set(normalized_checks) != expected_checks
                    or len(normalized_checks) != len(expected_checks)
                ):
                    errors.append(
                        f"{prefix}.strategic_observation_totality_contract.required_checks "
                        "must contain every totality check exactly once"
                    )
            if len(contract_source_digests) != len(set(contract_source_digests)):
                errors.append(
                    "generated strategic-observation-totality requirement duplicates "
                    "a source semantic identity"
                )

    association = raw_dimension.get(STRATEGIC_OBSERVATION_TOTALITY_ASSOCIATION_FIELD)
    expected_pin = ""
    association_source_digests: list[str] = []
    signature_sha = ""
    if not isinstance(association, dict):
        errors.append(
            "has no generated strategic-observation-totality semantic association"
        )
    else:
        if association.get("schema") != 2:
            errors.append(
                "generated strategic-observation-totality association must use schema 2"
            )
        expected_pin = str(
            association.get("semantic_association_sha256") or ""
        ).strip().lower()
        if not _SHA256_RE.fullmatch(expected_pin):
            errors.append(
                "generated strategic-observation-totality association lacks a current "
                "semantic_association_sha256"
            )
        raw_source_digests = association.get("source_item_semantic_sha256")
        if not isinstance(raw_source_digests, list) or not raw_source_digests:
            errors.append(
                "generated strategic-observation-totality association has no source "
                "semantic identities"
            )
        else:
            association_source_digests = [
                str(value or "").strip().lower() for value in raw_source_digests
            ]
            if (
                any(
                    not _SHA256_RE.fullmatch(value)
                    for value in association_source_digests
                )
                or len(association_source_digests)
                != len(set(association_source_digests))
            ):
                errors.append(
                    "generated strategic-observation-totality association has malformed "
                    "or duplicate source semantic identities"
                )
        signature = association.get("reviewed_elaborated_signature_identity")
        if not isinstance(signature, dict):
            errors.append(
                "generated strategic-observation-totality association lacks a current "
                "elaborated review signature"
            )
        else:
            qualified = str(signature.get("qualified_declaration") or "").strip()
            signature_sha = str(
                signature.get("elaborated_signature_sha256") or ""
            ).strip().lower()
            if not qualified or "." not in qualified or not _SHA256_RE.fullmatch(
                signature_sha
            ):
                errors.append(
                    "generated strategic-observation-totality association has an invalid "
                    "elaborated review signature"
                )
        reviewed_identity = association.get("reviewed_declaration_identity")
        if not isinstance(reviewed_identity, dict):
            errors.append(
                "generated strategic-observation-totality association lacks a reviewed "
                "declaration identity"
            )
        else:
            reviewed_qualified = str(
                reviewed_identity.get("qualified_declaration") or ""
            ).strip()
            reviewed_sha = str(
                reviewed_identity.get("declaration_sha256") or ""
            ).strip().lower()
            signature_qualified = (
                str(signature.get("qualified_declaration") or "").strip()
                if isinstance(signature, dict)
                else ""
            )
            if (
                not reviewed_qualified
                or "." not in reviewed_qualified
                or not _SHA256_RE.fullmatch(reviewed_sha)
                or reviewed_qualified != signature_qualified
            ):
                errors.append(
                    "generated strategic-observation-totality association has an invalid "
                    "reviewed declaration identity"
                )
        if contract_source_digests and association_source_digests and sorted(
            contract_source_digests
        ) != sorted(association_source_digests):
            errors.append(
                "generated strategic-observation-totality association source identities "
                "do not match its source contexts"
            )
        if association_source_digests and _SHA256_RE.fullmatch(signature_sha):
            expected_association_pin = hashlib.sha256(
                json.dumps(
                    {
                        "schema": 2,
                        "source_item_semantic_sha256": sorted(
                            association_source_digests
                        ),
                        "elaborated_signature_sha256": signature_sha,
                    },
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode("utf-8")
            ).hexdigest()
            if expected_pin != expected_association_pin:
                errors.append(
                    "generated strategic-observation-totality association "
                    "semantic_association_sha256 does not match its current "
                    "source/signature pins"
                )

    field = STRATEGIC_OBSERVATION_TOTALITY_ANALYSIS_FIELD
    analysis = response.get(field)
    if not isinstance(analysis, dict):
        return errors + [f"needs `{field}` object"]
    supplied_pin = str(
        analysis.get("semantic_association_sha256") or ""
    ).strip().lower()
    if not _SHA256_RE.fullmatch(expected_pin) or supplied_pin != expected_pin:
        errors.append(
            f"`{field}.semantic_association_sha256` must equal the current generated "
            "strategic-observation-totality semantic association pin"
        )
    verdict = str(analysis.get("verdict") or "").strip()
    if verdict not in STRATEGIC_OBSERVATION_TOTALITY_VERDICTS:
        errors.append(
            f"`{field}.verdict` must be one of "
            + ", ".join(sorted(STRATEGIC_OBSERVATION_TOTALITY_VERDICTS))
        )
    for required_field in STRATEGIC_OBSERVATION_TOTALITY_ANALYSIS_FIELDS[1:]:
        value = str(analysis.get(required_field) or "").strip()
        if not value:
            errors.append(f"`{field}.{required_field}` is required")
        elif required_field not in STRATEGIC_OBSERVATION_TOTALITY_DISPOSITION_FIELDS and (
            BARE_QUALIFIED_REFERENCE_RE.fullmatch(value)
            or (
            name_only is not None and name_only(value)
            )
        ):
            errors.append(
                f"`{field}.{required_field}` is name-only evidence; state the "
                "source and expanded Lean semantics"
            )
    branch_disposition = str(
        analysis.get("zero_probability_branch_disposition") or ""
    ).strip()
    if branch_disposition not in STRATEGIC_OBSERVATION_TOTALITY_BRANCH_DISPOSITIONS:
        errors.append(
            f"`{field}.zero_probability_branch_disposition` must be one of "
            + ", ".join(
                sorted(STRATEGIC_OBSERVATION_TOTALITY_BRANCH_DISPOSITIONS)
            )
        )

    disposition_specs = (
        (
            "conditioning_population_disposition",
            STRATEGIC_OBSERVATION_TOTALITY_CONDITIONING_POPULATION_DISPOSITIONS,
            STRATEGIC_OBSERVATION_TOTALITY_SAFE_CONDITIONING_POPULATION_DISPOSITIONS,
        ),
        (
            "selected_event_history_disposition",
            STRATEGIC_OBSERVATION_TOTALITY_SELECTED_EVENT_HISTORY_DISPOSITIONS,
            STRATEGIC_OBSERVATION_TOTALITY_SAFE_SELECTED_EVENT_HISTORY_DISPOSITIONS,
        ),
        (
            "event_measurability_disposition",
            STRATEGIC_OBSERVATION_TOTALITY_EVENT_MEASURABILITY_DISPOSITIONS,
            STRATEGIC_OBSERVATION_TOTALITY_SAFE_EVENT_MEASURABILITY_DISPOSITIONS,
        ),
        (
            "fibre_base_scope_disposition",
            STRATEGIC_OBSERVATION_TOTALITY_FIBRE_BASE_SCOPE_DISPOSITIONS,
            STRATEGIC_OBSERVATION_TOTALITY_SAFE_FIBRE_BASE_SCOPE_DISPOSITIONS,
        ),
    )
    granular_dispositions: dict[str, str] = {}
    for disposition_field, allowed, _safe in disposition_specs:
        disposition = str(analysis.get(disposition_field) or "").strip()
        granular_dispositions[disposition_field] = disposition
        if disposition not in allowed:
            errors.append(
                f"`{field}.{disposition_field}` must be one of "
                + ", ".join(sorted(allowed))
            )

    def expected_scope_disposition(
        raw_scopes: list[str],
        by_scope: dict[str, str],
        mixed_disposition: str,
    ) -> str | None:
        scopes = set(raw_scopes)
        if not scopes:
            return None
        if len(scopes) > 1:
            return mixed_disposition
        return by_scope.get(next(iter(scopes)))

    scope_requirements = (
        (
            "conditioning_population_disposition",
            expected_scope_disposition(
                conditioning_population_scopes,
                {
                    "entire_source_population": (
                        "source_entire_population_carrier_checked"
                    ),
                    "source_defined_subpopulation_or_access_event": (
                        "source_conditioned_or_restricted_population_checked"
                    ),
                    "source_defined_conditioned_or_restricted_population": (
                        "source_conditioned_or_restricted_population_checked"
                    ),
                },
                "mixed_source_population_scopes_checked",
            ),
        ),
        (
            "selected_event_history_disposition",
            expected_scope_disposition(
                selected_event_history_scopes,
                {
                    "single_action_without_prior_strategic_history": (
                        "single_action_event_checked"
                    ),
                    "source_defined_sequential_action_history": (
                        "source_history_in_selected_event_checked"
                    ),
                    "source_defined_pre_action_state_or_history": (
                        "source_history_in_selected_event_checked"
                    ),
                },
                "mixed_source_history_scopes_checked",
            ),
        ),
        (
            "fibre_base_scope_disposition",
            expected_scope_disposition(
                conditionalization_scopes,
                {
                    "positive_measurable_event": (
                        "positive_measurable_event_checked"
                    ),
                    "source_totalized_pointwise_observation_branch": (
                        "source_totalized_pointwise_fibres_checked"
                    ),
                    "ae_regular_conditional_distribution_or_disintegration": (
                        "ae_fibre_base_scope_and_version_checked"
                    ),
                },
                "mixed_source_conditionalization_scopes_checked",
            ),
        ),
    )
    safe_dispositions_by_field = {
        disposition_field: safe
        for disposition_field, _allowed, safe in disposition_specs
    }
    for disposition_field, expected_disposition in scope_requirements:
        actual_disposition = granular_dispositions.get(disposition_field)
        if (
            expected_disposition is not None
            and actual_disposition
            in safe_dispositions_by_field[disposition_field]
            and actual_disposition != expected_disposition
        ):
            errors.append(
                f"`{field}.{disposition_field}` does not match the source-pinned "
                "conditioning/history/conditionalization scope"
            )

    if requirement_schema == STRATEGIC_OBSERVATION_TOTALITY_REQUIREMENT_SCHEMA:
        raw_scope_evidence = analysis.get(
            STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPE_EVIDENCE_FIELD
        )
        expected_scope_evidence_keys = set(conditionalization_scopes)
        if not isinstance(raw_scope_evidence, dict):
            errors.append(
                f"`{field}.{STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPE_EVIDENCE_FIELD}` "
                "must be an object with one source-vs-Lean explanation for each "
                "declared conditionalization scope"
            )
        else:
            raw_scope_evidence_keys = set(raw_scope_evidence)
            if raw_scope_evidence_keys != expected_scope_evidence_keys:
                errors.append(
                    f"`{field}.{STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPE_EVIDENCE_FIELD}` "
                    "must have exactly the declared conditionalization scopes as keys"
                )
            for scope in sorted(expected_scope_evidence_keys):
                raw_value = raw_scope_evidence.get(scope)
                value = raw_value.strip() if isinstance(raw_value, str) else ""
                if not value:
                    errors.append(
                        f"`{field}.{STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPE_EVIDENCE_FIELD}."
                        f"{scope}` is required"
                    )
                elif BARE_QUALIFIED_REFERENCE_RE.fullmatch(value) or (
                    name_only is not None and name_only(value)
                ):
                    errors.append(
                        f"`{field}.{STRATEGIC_OBSERVATION_TOTALITY_CONDITIONALIZATION_SCOPE_EVIDENCE_FIELD}."
                        f"{scope}` is name-only evidence; state the source and expanded "
                        "Lean semantics"
                    )

    outer_verdict = str(response.get("verdict") or "").strip()
    if outer_verdict == "not_applicable":
        errors.append(
            "cannot mark a source-required strategic-observation-totality dimension "
            "not_applicable"
        )
    if (
        verdict in STRATEGIC_OBSERVATION_TOTALITY_SAFE_VERDICTS
        and branch_disposition
        not in STRATEGIC_OBSERVATION_TOTALITY_SAFE_BRANCH_DISPOSITIONS
    ):
        errors.append(
            f"`{field}` claims a safe totality verdict while its branch disposition "
            "does not establish source-backed totality, infeasibility, or an explicit "
            "equilibrium-domain restriction"
        )
    if verdict in STRATEGIC_OBSERVATION_TOTALITY_SAFE_VERDICTS and any(
        granular_dispositions.get(disposition_field) not in safe
        for disposition_field, _allowed, safe in disposition_specs
    ):
        errors.append(
            f"`{field}` claims a safe totality verdict while its population, action-history, "
            "event-measurability, or fibre/base review remains open"
        )
    if (
        verdict in STRATEGIC_OBSERVATION_TOTALITY_OPEN_VERDICTS
        or branch_disposition
        in {"source_leaves_branch_unresolved", "lean_only_offpath_completion"}
    ) and outer_verdict == "matches_source_model":
        errors.append(
            "records an unresolved or Lean-only off-path branch while the enclosing "
            "dimension claims matches_source_model"
        )
    if any(
        granular_dispositions.get(disposition_field) not in safe
        for disposition_field, _allowed, safe in disposition_specs
    ) and outer_verdict == "matches_source_model":
        errors.append(
            "records an unresolved population-carrier, action-history, "
            "event-measurability, or fibre/base issue while the enclosing dimension "
            "claims matches_source_model"
        )
    return errors


def _conditioning_information_source_entries(
    value: object,
    *,
    field: str,
    require_nonempty: bool,
) -> tuple[list[str], list[str]]:
    """Validate generated source component/stage entries and return their ids."""

    if not isinstance(value, list):
        return [], [f"{field} must be a list"]
    if require_nonempty and not value:
        return [], [f"{field} must be nonempty"]
    ids: list[str] = []
    errors: list[str] = []
    for index, entry in enumerate(value):
        prefix = f"{field}[{index}]"
        if not isinstance(entry, dict):
            errors.append(f"{prefix} is not an object")
            continue
        identifier = str(entry.get("id") or "").strip()
        description = str(entry.get("description") or "").strip()
        if not identifier:
            errors.append(f"{prefix}.id is missing")
        else:
            ids.append(identifier)
        if not description:
            errors.append(f"{prefix}.description is missing")
    if len(ids) != len(set(ids)):
        errors.append(f"{field} has duplicate semantic ids")
    return ids, errors


def _conditioning_information_scope_list(
    value: object,
    *,
    field: str,
) -> tuple[list[str], list[str]]:
    """Validate a conditionalization scope list without inferring any Lean role."""

    scopes = (
        [scope.strip() for scope in value]
        if isinstance(value, list) and all(isinstance(scope, str) for scope in value)
        else []
    )
    if (
        not scopes
        or len(scopes) != (len(value) if isinstance(value, list) else 0)
        or len(set(scopes)) != len(scopes)
        or any(
            scope not in CONDITIONING_INFORMATION_CONDITIONALIZATION_SCOPES
            for scope in scopes
        )
    ):
        return [], [
            f"{field} must be a nonempty duplicate-free list of declared "
            "conditionalization scopes"
        ]
    return scopes, []


def _conditioning_information_response_entries(
    value: object,
    *,
    field: str,
    id_field: str,
) -> tuple[list[str], list[str]]:
    """Validate Lean-side semantic entry descriptions, not declaration names."""

    if not isinstance(value, list):
        return [], [f"{field} must be a list"]
    ids: list[str] = []
    errors: list[str] = []
    for index, entry in enumerate(value):
        prefix = f"{field}[{index}]"
        if not isinstance(entry, dict):
            errors.append(f"{prefix} is not an object")
            continue
        identifier = str(entry.get(id_field) or "").strip()
        description = str(entry.get("description") or "").strip()
        if not identifier:
            errors.append(f"{prefix}.{id_field} is missing")
        else:
            ids.append(identifier)
        if not description:
            errors.append(f"{prefix}.description is required")
        elif BARE_QUALIFIED_REFERENCE_RE.fullmatch(description):
            errors.append(
                f"{prefix}.description is name-only evidence; state the expanded Lean "
                "observation or selection semantics"
            )
    if len(ids) != len(set(ids)):
        errors.append(f"{field} has duplicate source-semantic ids")
    return ids, errors


def conditioning_information_analysis_errors(
    raw_dimension: dict[str, Any],
    response: dict[str, Any],
    *,
    name_only: Callable[[str], bool] | None = None,
) -> list[str]:
    """Validate source-vs-Lean conditioning information for a direct claim.

    The test is intentionally component and stage based.  It does not inspect
    whether Lean happened to call an argument `posterior`, `observed`, or
    `condDistrib`: a direct match is accepted only when the source-pinned
    observed-component set, ordered action-selection history, raw-vs-selected
    conditional-value kind, law population, and conditionalization scope all
    agree with the declared Lean semantics.
    """

    if raw_dimension.get("requires_conditioning_information_analysis") is not True:
        return []

    errors: list[str] = []
    requirement = raw_dimension.get(CONDITIONING_INFORMATION_REQUIREMENT_FIELD)
    source_contracts: dict[str, dict[str, Any]] = {}
    if not isinstance(requirement, dict):
        errors.append("has no generated conditioning-information requirement")
    else:
        if requirement.get("schema") != CONDITIONING_INFORMATION_REQUIREMENT_SCHEMA:
            errors.append(
                "generated conditioning-information requirement must use schema "
                f"{CONDITIONING_INFORMATION_REQUIREMENT_SCHEMA}"
            )
        raw_contracts = requirement.get(CONDITIONING_INFORMATION_CONTRACTS_FIELD)
        if not isinstance(raw_contracts, list) or not raw_contracts:
            errors.append("generated conditioning-information requirement has no contracts")
        else:
            for index, raw_contract in enumerate(raw_contracts):
                prefix = (
                    "generated conditioning-information requirement."
                    f"contracts[{index}]"
                )
                if not isinstance(raw_contract, dict):
                    errors.append(f"{prefix} is not an object")
                    continue
                source_digest = str(
                    raw_contract.get("source_semantic_sha256") or ""
                ).strip().lower()
                if not _SHA256_RE.fullmatch(source_digest):
                    errors.append(
                        f"{prefix}.source_semantic_sha256 is missing or malformed"
                    )
                    continue
                if source_digest in source_contracts:
                    errors.append(
                        "generated conditioning-information requirement duplicates a "
                        "source semantic identity"
                    )
                    continue
                for field_name in ("source_location", "explanation"):
                    if not str(raw_contract.get(field_name) or "").strip():
                        errors.append(f"{prefix}.{field_name} is missing")
                anchors = raw_contract.get("source_anchor_evidence")
                if not isinstance(anchors, list) or not anchors:
                    errors.append(f"{prefix}.source_anchor_evidence is missing")
                contract = raw_contract.get("conditioning_information_contract")
                if not isinstance(contract, dict):
                    errors.append(
                        f"{prefix}.conditioning_information_contract is not an object"
                    )
                    continue
                if contract.get("schema") != CONDITIONING_INFORMATION_CONTRACT_SCHEMA:
                    errors.append(
                        f"{prefix}.conditioning_information_contract.schema must be "
                        f"{CONDITIONING_INFORMATION_CONTRACT_SCHEMA}"
                    )
                value_kind = str(contract.get("conditional_value_kind") or "").strip()
                if value_kind not in CONDITIONING_INFORMATION_VALUE_KINDS:
                    errors.append(
                        f"{prefix}.conditioning_information_contract has an invalid "
                        "conditional-value kind"
                    )
                component_ids, component_errors = _conditioning_information_source_entries(
                    contract.get("source_observed_components"),
                    field=(
                        f"{prefix}.conditioning_information_contract."
                        "source_observed_components"
                    ),
                    # An empty list explicitly represents conditioning on the
                    # trivial sigma-algebra. Missing or malformed fields are
                    # still rejected by the list-shape validator.
                    require_nonempty=False,
                )
                stage_ids, stage_errors = _conditioning_information_source_entries(
                    contract.get("source_action_selection_stages"),
                    field=(
                        f"{prefix}.conditioning_information_contract."
                        "source_action_selection_stages"
                    ),
                    require_nonempty=False,
                )
                errors.extend(component_errors)
                errors.extend(stage_errors)
                law_population = str(
                    contract.get("source_law_population") or ""
                ).strip()
                if law_population not in CONDITIONING_INFORMATION_LAW_POPULATIONS:
                    errors.append(
                        f"{prefix}.conditioning_information_contract has an invalid "
                        "source-law population"
                    )
                elif law_population == "raw_unselected_source_law" and stage_ids:
                    errors.append(
                        f"{prefix}.conditioning_information_contract gives action stages "
                        "for a raw/unselected law"
                    )
                elif law_population == "selected_by_source_actions" and not stage_ids:
                    errors.append(
                        f"{prefix}.conditioning_information_contract omits ordered action "
                        "stages for a selected law"
                    )
                scopes, scope_errors = _conditioning_information_scope_list(
                    contract.get("conditionalization_scopes"),
                    field=(
                        f"{prefix}.conditioning_information_contract."
                        "conditionalization_scopes"
                    ),
                )
                errors.extend(scope_errors)
                source_contracts[source_digest] = {
                    "value_kind": value_kind,
                    "component_ids": component_ids,
                    "stage_ids": stage_ids,
                    "law_population": law_population,
                    "scopes": scopes,
                }

    association = raw_dimension.get(CONDITIONING_INFORMATION_ASSOCIATION_FIELD)
    expected_pin = ""
    if not isinstance(association, dict):
        errors.append("has no generated conditioning-information semantic association")
    else:
        if association.get("schema") != 2:
            errors.append(
                "generated conditioning-information association must use schema 2"
            )
        raw_source_digests = association.get("source_item_semantic_sha256")
        association_digests = (
            [str(value or "").strip().lower() for value in raw_source_digests]
            if isinstance(raw_source_digests, list)
            else []
        )
        if (
            not association_digests
            or any(not _SHA256_RE.fullmatch(value) for value in association_digests)
            or len(association_digests) != len(set(association_digests))
        ):
            errors.append(
                "generated conditioning-information association has malformed or "
                "duplicate source semantic identities"
            )
        elif sorted(association_digests) != sorted(source_contracts):
            errors.append(
                "generated conditioning-information association source identities do "
                "not match its source contracts"
            )
        signature = association.get("reviewed_elaborated_signature_identity")
        signature_sha = ""
        signature_qualified = ""
        if not isinstance(signature, dict):
            errors.append(
                "generated conditioning-information association lacks a current "
                "elaborated review signature"
            )
        else:
            signature_qualified = str(
                signature.get("qualified_declaration") or ""
            ).strip()
            signature_sha = str(
                signature.get("elaborated_signature_sha256") or ""
            ).strip().lower()
            if (
                not signature_qualified
                or "." not in signature_qualified
                or not _SHA256_RE.fullmatch(signature_sha)
            ):
                errors.append(
                    "generated conditioning-information association has an invalid "
                    "elaborated review signature"
                )
        reviewed_identity = association.get("reviewed_declaration_identity")
        if not isinstance(reviewed_identity, dict):
            errors.append(
                "generated conditioning-information association lacks a reviewed "
                "declaration identity"
            )
        else:
            reviewed_qualified = str(
                reviewed_identity.get("qualified_declaration") or ""
            ).strip()
            reviewed_sha = str(
                reviewed_identity.get("declaration_sha256") or ""
            ).strip().lower()
            if (
                not reviewed_qualified
                or "." not in reviewed_qualified
                or not _SHA256_RE.fullmatch(reviewed_sha)
                or reviewed_qualified != signature_qualified
            ):
                errors.append(
                    "generated conditioning-information association has an invalid "
                    "reviewed declaration identity"
                )
        if association_digests and _SHA256_RE.fullmatch(signature_sha):
            expected_pin = hashlib.sha256(
                json.dumps(
                    {
                        "schema": 2,
                        "source_item_semantic_sha256": sorted(association_digests),
                        "elaborated_signature_sha256": signature_sha,
                    },
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode("utf-8")
            ).hexdigest()
            supplied_association_pin = str(
                association.get("semantic_association_sha256") or ""
            ).strip().lower()
            if supplied_association_pin != expected_pin:
                errors.append(
                    "generated conditioning-information association "
                    "semantic_association_sha256 does not match its current "
                    "source/signature pins"
                )

    field = CONDITIONING_INFORMATION_ANALYSIS_FIELD
    analysis = response.get(field)
    if not isinstance(analysis, dict):
        return errors + [f"needs `{field}` object"]
    supplied_pin = str(analysis.get("semantic_association_sha256") or "").strip().lower()
    if not _SHA256_RE.fullmatch(expected_pin) or supplied_pin != expected_pin:
        errors.append(
            f"`{field}.semantic_association_sha256` must equal the current generated "
            "conditioning-information semantic association pin"
        )
    verdict = str(analysis.get("verdict") or "").strip()
    if verdict not in CONDITIONING_INFORMATION_ANALYSIS_VERDICTS:
        errors.append(
            f"`{field}.verdict` must be one of "
            + ", ".join(sorted(CONDITIONING_INFORMATION_ANALYSIS_VERDICTS))
        )
    bridge = str(analysis.get("lean_bridge_evidence") or "").strip()
    if not bridge:
        errors.append(f"`{field}.lean_bridge_evidence` is required")
    elif BARE_QUALIFIED_REFERENCE_RE.fullmatch(bridge) or (
        name_only is not None and name_only(bridge)
    ):
        errors.append(
            f"`{field}.lean_bridge_evidence` is name-only evidence; state the "
            "source-to-Lean conditioning bridge"
        )
    raw_response_contracts = analysis.get("contracts")
    response_by_digest: dict[str, dict[str, Any]] = {}
    if not isinstance(raw_response_contracts, list) or not raw_response_contracts:
        errors.append(f"`{field}.contracts` must be a nonempty list")
    else:
        for index, raw_response_contract in enumerate(raw_response_contracts):
            prefix = f"`{field}.contracts[{index}]`"
            if not isinstance(raw_response_contract, dict):
                errors.append(f"{prefix} is not an object")
                continue
            unexpected = sorted(
                set(raw_response_contract)
                - CONDITIONING_INFORMATION_RESPONSE_CONTRACT_FIELDS
            )
            if unexpected:
                errors.append(
                    f"{prefix} has unsupported field(s): " + ", ".join(unexpected)
                )
            source_digest = str(
                raw_response_contract.get("source_semantic_sha256") or ""
            ).strip().lower()
            if not _SHA256_RE.fullmatch(source_digest):
                errors.append(f"{prefix}.source_semantic_sha256 is missing or malformed")
                continue
            if source_digest in response_by_digest:
                errors.append(f"`{field}.contracts` duplicates a source semantic identity")
                continue
            response_by_digest[source_digest] = raw_response_contract
    if set(response_by_digest) != set(source_contracts):
        errors.append(
            f"`{field}.contracts` must have exactly one source-vs-Lean comparison "
            "for every generated source conditioning contract"
        )

    for source_digest, source_contract in source_contracts.items():
        response_contract = response_by_digest.get(source_digest)
        if not isinstance(response_contract, dict):
            continue
        prefix = f"`{field}.contracts[{source_digest}]`"
        source_value_kind = str(
            response_contract.get("source_conditional_value_kind") or ""
        ).strip()
        if source_value_kind != source_contract["value_kind"]:
            errors.append(
                f"{prefix}.source_conditional_value_kind does not reproduce the "
                "generated source conditional-value kind"
            )
        lean_value_kind = str(
            response_contract.get("lean_conditional_value_kind") or ""
        ).strip()
        if lean_value_kind not in CONDITIONING_INFORMATION_VALUE_KINDS:
            errors.append(
                f"{prefix}.lean_conditional_value_kind has an invalid "
                "conditional-value kind"
            )
        raw_source_components = response_contract.get("source_observed_component_ids")
        source_components = (
            [value.strip() for value in raw_source_components]
            if isinstance(raw_source_components, list)
            and all(isinstance(value, str) for value in raw_source_components)
            else []
        )
        if (
            len(source_components) != len(raw_source_components)
            if isinstance(raw_source_components, list)
            else True
        ) or len(set(source_components)) != len(source_components):
            errors.append(
                f"{prefix}.source_observed_component_ids must be a duplicate-free list"
            )
        elif set(source_components) != set(source_contract["component_ids"]):
            errors.append(
                f"{prefix}.source_observed_component_ids does not reproduce the "
                "generated source observed-component contract"
            )
        raw_source_stages = response_contract.get("source_action_selection_stage_ids")
        source_stages = (
            [value.strip() for value in raw_source_stages]
            if isinstance(raw_source_stages, list)
            and all(isinstance(value, str) for value in raw_source_stages)
            else []
        )
        if (
            len(source_stages) != len(raw_source_stages)
            if isinstance(raw_source_stages, list)
            else True
        ) or len(set(source_stages)) != len(source_stages):
            errors.append(
                f"{prefix}.source_action_selection_stage_ids must be a duplicate-free list"
            )
        elif source_stages != source_contract["stage_ids"]:
            errors.append(
                f"{prefix}.source_action_selection_stage_ids does not reproduce the "
                "generated ordered source action-selection stages"
            )
        raw_source_scopes = response_contract.get("source_conditionalization_scopes")
        source_scopes, source_scope_errors = _conditioning_information_scope_list(
            raw_source_scopes,
            field=f"{prefix}.source_conditionalization_scopes",
        )
        errors.extend(source_scope_errors)
        if source_scopes and set(source_scopes) != set(source_contract["scopes"]):
            errors.append(
                f"{prefix}.source_conditionalization_scopes does not reproduce the "
                "generated source scope"
            )
        source_law_population = str(
            response_contract.get("source_law_population") or ""
        ).strip()
        if source_law_population != source_contract["law_population"]:
            errors.append(
                f"{prefix}.source_law_population does not reproduce the generated "
                "raw-vs-selected source law"
            )

        lean_components, lean_component_errors = _conditioning_information_response_entries(
            response_contract.get("lean_observed_components"),
            field=f"{prefix}.lean_observed_components",
            id_field="source_component_id",
        )
        lean_stages, lean_stage_errors = _conditioning_information_response_entries(
            response_contract.get("lean_action_selection_stages"),
            field=f"{prefix}.lean_action_selection_stages",
            id_field="source_stage_id",
        )
        errors.extend(lean_component_errors)
        errors.extend(lean_stage_errors)
        lean_law_population = str(
            response_contract.get("lean_law_population") or ""
        ).strip()
        if lean_law_population not in CONDITIONING_INFORMATION_LAW_POPULATIONS:
            errors.append(f"{prefix}.lean_law_population has an invalid law population")
        lean_scopes, lean_scope_errors = _conditioning_information_scope_list(
            response_contract.get("lean_conditionalization_scopes"),
            field=f"{prefix}.lean_conditionalization_scopes",
        )
        errors.extend(lean_scope_errors)
        comparison = str(response_contract.get("comparison_evidence") or "").strip()
        if not comparison:
            errors.append(f"{prefix}.comparison_evidence is required")
        elif BARE_QUALIFIED_REFERENCE_RE.fullmatch(comparison) or (
            name_only is not None and name_only(comparison)
        ):
            errors.append(
                f"{prefix}.comparison_evidence is name-only evidence; state the "
                "actual source and Lean information sets"
            )

        if verdict == CONDITIONING_INFORMATION_MATCH_VERDICT:
            if lean_value_kind != source_contract["value_kind"]:
                errors.append(
                    f"{prefix} claims a direct conditioning match while Lean's "
                    "conditional-value kind differs from the source"
                )
            if set(lean_components) != set(source_contract["component_ids"]):
                errors.append(
                    f"{prefix} claims a direct conditioning match while Lean omits or "
                    "adds a source observed component"
                )
            if lean_stages != source_contract["stage_ids"]:
                errors.append(
                    f"{prefix} claims a direct conditioning match while Lean omits, "
                    "adds, or reorders a source action-selection stage"
                )
            if lean_law_population != source_contract["law_population"]:
                errors.append(
                    f"{prefix} claims a direct conditioning match while raw-vs-selected "
                    "law population differs"
                )
            if set(lean_scopes) != set(source_contract["scopes"]):
                errors.append(
                    f"{prefix} claims a direct conditioning match while a.e./pointwise "
                    "conditionalization scope differs"
                )

    outer_verdict = str(response.get("verdict") or "").strip()
    if outer_verdict == "not_applicable":
        errors.append(
            "cannot mark a source-required conditioning-information dimension "
            "not_applicable"
        )
    if (
        verdict in CONDITIONING_INFORMATION_OPEN_VERDICTS
        and outer_verdict == "matches_source_model"
    ):
        errors.append(
            "records an unresolved conditioning-information comparison while the "
            "enclosing dimension claims matches_source_model"
        )
    return errors


def _source_model_derivation_source_anchor_errors(
    value: dict[str, Any],
    *,
    field: str,
) -> list[str]:
    """Check generated per-component provenance shape before sidecar credit.

    Exact source-byte verification belongs to the source-map integrity lane.
    This duplicate shape check keeps a hand-edited raw dimension from dropping
    the independently generated component anchor while retaining its outer
    source/signature association.
    """

    errors: list[str] = []
    source_location = str(value.get("source_location") or "").strip()
    if not _SOURCE_MODEL_DERIVATION_SOURCE_LOCATION_RE.fullmatch(source_location):
        errors.append(
            f"{field}.source_location must contain exactly one source file:line span"
        )
    raw_anchors = value.get("source_anchor_evidence")
    if not isinstance(raw_anchors, list) or not raw_anchors:
        errors.append(f"{field}.source_anchor_evidence must be a nonempty list")
        return errors
    for index, raw_anchor in enumerate(raw_anchors):
        prefix = f"{field}.source_anchor_evidence[{index}]"
        if not isinstance(raw_anchor, dict):
            errors.append(f"{prefix} is not an object")
            continue
        missing = sorted(
            SOURCE_MODEL_DERIVATION_SOURCE_ANCHOR_FIELDS - set(raw_anchor)
        )
        if missing:
            errors.append(
                f"{prefix} is missing required field(s): " + ", ".join(missing)
            )
    return errors


def _source_model_derivation_source_primitives(
    value: object,
    *,
    field: str,
) -> tuple[list[str], list[str]]:
    """Read one source-pinned primitive basis without Lean-name inference."""

    if not isinstance(value, list) or not value:
        return [], [f"{field} must be a nonempty list"]
    ids: list[str] = []
    errors: list[str] = []
    for index, raw_component in enumerate(value):
        prefix = f"{field}[{index}]"
        if not isinstance(raw_component, dict):
            errors.append(f"{prefix} is not an object")
            continue
        unexpected = sorted(
            set(raw_component) - SOURCE_MODEL_DERIVATION_SOURCE_COMPONENT_FIELDS
        )
        if unexpected:
            errors.append(
                f"{prefix} has unsupported field(s): " + ", ".join(unexpected)
            )
        identifier = str(raw_component.get("id") or "").strip()
        if not SOURCE_MODEL_DERIVATION_SEMANTIC_ID_RE.fullmatch(identifier):
            errors.append(f"{prefix}.id must be a lowercase source-semantic identifier")
        else:
            ids.append(identifier)
        description = str(raw_component.get("description") or "").strip()
        if not description:
            errors.append(f"{prefix}.description is required")
        errors.extend(
            _source_model_derivation_source_anchor_errors(
                raw_component,
                field=prefix,
            )
        )
    if len(ids) != len(set(ids)):
        errors.append(f"{field} must not duplicate a source primitive component id")
    return ids, errors


def _source_model_derivation_lean_primitives(
    value: object,
    *,
    field: str,
    name_only: Callable[[str], bool] | None,
) -> tuple[list[str], list[str]]:
    """Read Lean-side primitive roles by source IDs, never local field names."""

    if not isinstance(value, list) or not value:
        return [], [f"{field} must be a nonempty list"]
    ids: list[str] = []
    errors: list[str] = []
    for index, raw_component in enumerate(value):
        prefix = f"{field}[{index}]"
        if not isinstance(raw_component, dict):
            errors.append(f"{prefix} is not an object")
            continue
        unexpected = sorted(
            set(raw_component) - SOURCE_MODEL_DERIVATION_LEAN_PRIMITIVE_COMPONENT_FIELDS
        )
        if unexpected:
            errors.append(
                f"{prefix} has unsupported field(s): " + ", ".join(unexpected)
            )
        identifier = str(raw_component.get("source_primitive_component_id") or "").strip()
        if not SOURCE_MODEL_DERIVATION_SEMANTIC_ID_RE.fullmatch(identifier):
            errors.append(
                f"{prefix}.source_primitive_component_id must be a lowercase "
                "source-semantic identifier"
            )
        else:
            ids.append(identifier)
        description = str(raw_component.get("description") or "").strip()
        if not description:
            errors.append(f"{prefix}.description is required")
        elif BARE_QUALIFIED_REFERENCE_RE.fullmatch(description) or (
            name_only is not None and name_only(description)
        ):
            errors.append(
                f"{prefix}.description is name-only evidence; state how the Lean "
                "primitive realizes the source primitive"
            )
    if len(ids) != len(set(ids)):
        errors.append(f"{field} must not duplicate a source primitive component id")
    return ids, errors


def source_model_derivation_analysis_errors(
    raw_dimension: dict[str, Any],
    response: dict[str, Any],
    *,
    name_only: Callable[[str], bool] | None = None,
) -> list[str]:
    """Require a source-pinned model consequence to be derived, not received.

    This activates only for a generated source-context dimension.  It compares
    a literal source primitive basis with an explicit Lean primitive basis and
    permits a direct source-model match only through a checked derivation route.
    In particular, a response that says the central cycle, process, execution,
    or conditional law is a caller-supplied record field is an open boundary,
    not a formalized derivation.  When the generated expanded surface already
    structurally carries a model-construction package, the current generic lane
    is intentionally fail-closed: no free-text route can restore a direct
    match, and only a documented partial boundary is accepted until a separate
    machine-generated primitive-level derivation receipt exists.  The test is
    about source-declared roles and current source/signature association, never
    about record or declaration spelling.
    """

    if raw_dimension.get("requires_source_model_derivation_analysis") is not True:
        return []

    errors: list[str] = []
    raw_caller_supplied_basis = raw_dimension.get(
        SOURCE_MODEL_DERIVATION_CALLER_SUPPLIED_BASIS_FIELD
    )
    caller_supplied_basis: list[str] = []
    if not isinstance(raw_caller_supplied_basis, list):
        errors.append(
            "generated source-model-derivation dimension has no structural "
            "caller-supplied model-construction basis"
        )
    elif any(
        not isinstance(entry, str) or not entry.strip()
        for entry in raw_caller_supplied_basis
    ) or len(raw_caller_supplied_basis) != len(set(raw_caller_supplied_basis)):
        errors.append(
            "generated source-model-derivation caller-supplied model-construction "
            "basis must be a duplicate-free list of nonempty structural findings"
        )
    else:
        caller_supplied_basis = [entry.strip() for entry in raw_caller_supplied_basis]
    requirement = raw_dimension.get(SOURCE_MODEL_DERIVATION_REQUIREMENT_FIELD)
    source_contracts: dict[str, dict[str, object]] = {}
    if not isinstance(requirement, dict):
        errors.append("has no generated source-model-derivation requirement")
    else:
        if requirement.get("schema") != SOURCE_MODEL_DERIVATION_REQUIREMENT_SCHEMA:
            errors.append(
                "generated source-model-derivation requirement must use schema "
                f"{SOURCE_MODEL_DERIVATION_REQUIREMENT_SCHEMA}"
            )
        raw_contracts = requirement.get(SOURCE_MODEL_DERIVATION_CONTRACTS_FIELD)
        if not isinstance(raw_contracts, list) or not raw_contracts:
            errors.append(
                "generated source-model-derivation requirement has no contracts"
            )
        else:
            for index, raw_contract in enumerate(raw_contracts):
                prefix = f"generated source-model-derivation requirement.contracts[{index}]"
                if not isinstance(raw_contract, dict):
                    errors.append(f"{prefix} is not an object")
                    continue
                source_digest = str(
                    raw_contract.get("source_semantic_sha256") or ""
                ).strip().lower()
                if not _SHA256_RE.fullmatch(source_digest):
                    errors.append(f"{prefix}.source_semantic_sha256 is missing or malformed")
                    continue
                if source_digest in source_contracts:
                    errors.append(
                        "generated source-model-derivation requirement duplicates a "
                        "source semantic identity"
                    )
                    continue
                source_contract = raw_contract.get(
                    "source_model_derivation_contract"
                )
                if not isinstance(source_contract, dict):
                    errors.append(
                        f"{prefix}.source_model_derivation_contract is not an object"
                    )
                    continue
                if source_contract.get("schema") != SOURCE_MODEL_DERIVATION_CONTRACT_SCHEMA:
                    errors.append(
                        f"{prefix}.source_model_derivation_contract.schema must be "
                        f"{SOURCE_MODEL_DERIVATION_CONTRACT_SCHEMA}"
                    )
                primitive_ids, primitive_errors = _source_model_derivation_source_primitives(
                    source_contract.get("source_primitive_components"),
                    field=(
                        f"{prefix}.source_model_derivation_contract."
                        "source_primitive_components"
                    ),
                )
                errors.extend(primitive_errors)
                derived = source_contract.get("derived_conclusion")
                derived_description = ""
                if not isinstance(derived, dict):
                    errors.append(
                        f"{prefix}.source_model_derivation_contract.derived_conclusion "
                        "is not an object"
                    )
                else:
                    unexpected = sorted(
                        set(derived)
                        - SOURCE_MODEL_DERIVATION_SOURCE_CONCLUSION_FIELDS
                    )
                    if unexpected:
                        errors.append(
                            f"{prefix}.source_model_derivation_contract.derived_conclusion "
                            "has unsupported field(s): "
                            + ", ".join(unexpected)
                        )
                    derived_description = str(derived.get("description") or "").strip()
                    if not derived_description:
                        errors.append(
                            f"{prefix}.source_model_derivation_contract.derived_conclusion."
                            "description is required"
                        )
                    errors.extend(
                        _source_model_derivation_source_anchor_errors(
                            derived,
                            field=(
                                f"{prefix}.source_model_derivation_contract."
                                "derived_conclusion"
                            ),
                        )
                    )
                source_contracts[source_digest] = {
                    "primitive_ids": primitive_ids,
                    "derived_description": derived_description,
                }

    association = raw_dimension.get(SOURCE_MODEL_DERIVATION_ASSOCIATION_FIELD)
    expected_pin = ""
    if not isinstance(association, dict):
        errors.append("has no generated source-model-derivation semantic association")
    else:
        if association.get("schema") != 2:
            errors.append(
                "generated source-model-derivation association must use schema 2"
            )
        raw_source_digests = association.get("source_item_semantic_sha256")
        association_digests = (
            [str(value or "").strip().lower() for value in raw_source_digests]
            if isinstance(raw_source_digests, list)
            else []
        )
        if (
            not association_digests
            or any(not _SHA256_RE.fullmatch(value) for value in association_digests)
            or len(association_digests) != len(set(association_digests))
        ):
            errors.append(
                "generated source-model-derivation association has malformed or "
                "duplicate source semantic identities"
            )
        elif sorted(association_digests) != sorted(source_contracts):
            errors.append(
                "generated source-model-derivation association source identities do "
                "not match its source contracts"
            )
        signature = association.get("reviewed_elaborated_signature_identity")
        signature_sha = ""
        signature_qualified = ""
        if not isinstance(signature, dict):
            errors.append(
                "generated source-model-derivation association lacks a current "
                "elaborated review signature"
            )
        else:
            signature_qualified = str(
                signature.get("qualified_declaration") or ""
            ).strip()
            signature_sha = str(
                signature.get("elaborated_signature_sha256") or ""
            ).strip().lower()
            if (
                not signature_qualified
                or "." not in signature_qualified
                or not _SHA256_RE.fullmatch(signature_sha)
            ):
                errors.append(
                    "generated source-model-derivation association has an invalid "
                    "elaborated review signature"
                )
        reviewed_identity = association.get("reviewed_declaration_identity")
        if not isinstance(reviewed_identity, dict):
            errors.append(
                "generated source-model-derivation association lacks a reviewed "
                "declaration identity"
            )
        else:
            reviewed_qualified = str(
                reviewed_identity.get("qualified_declaration") or "").strip()
            reviewed_sha = str(
                reviewed_identity.get("declaration_sha256") or "").strip().lower()
            if (
                not reviewed_qualified
                or "." not in reviewed_qualified
                or not _SHA256_RE.fullmatch(reviewed_sha)
                or reviewed_qualified != signature_qualified
            ):
                errors.append(
                    "generated source-model-derivation association has an invalid "
                    "reviewed declaration identity"
                )
        if association_digests and _SHA256_RE.fullmatch(signature_sha):
            expected_pin = hashlib.sha256(
                json.dumps(
                    {
                        "schema": 2,
                        "source_item_semantic_sha256": sorted(association_digests),
                        "elaborated_signature_sha256": signature_sha,
                    },
                    sort_keys=True,
                    separators=(",", ":"),
                ).encode("utf-8")
            ).hexdigest()
            supplied_association_pin = str(
                association.get("semantic_association_sha256") or ""
            ).strip().lower()
            if supplied_association_pin != expected_pin:
                errors.append(
                    "generated source-model-derivation association "
                    "semantic_association_sha256 does not match its current "
                    "source/signature pins"
                )

    field = SOURCE_MODEL_DERIVATION_ANALYSIS_FIELD
    analysis = response.get(field)
    if not isinstance(analysis, dict):
        return errors + [f"needs `{field}` object"]
    unexpected_analysis = sorted(set(analysis) - SOURCE_MODEL_DERIVATION_ANALYSIS_FIELDS)
    if unexpected_analysis:
        errors.append(
            f"`{field}` has unsupported field(s): " + ", ".join(unexpected_analysis)
        )
    supplied_pin = str(analysis.get("semantic_association_sha256") or "").strip().lower()
    if not _SHA256_RE.fullmatch(expected_pin) or supplied_pin != expected_pin:
        errors.append(
            f"`{field}.semantic_association_sha256` must equal the current generated "
            "source-model-derivation semantic association pin"
        )
    verdict = str(analysis.get("verdict") or "").strip()
    if verdict not in SOURCE_MODEL_DERIVATION_ANALYSIS_VERDICTS:
        errors.append(
            f"`{field}.verdict` must be one of "
            + ", ".join(sorted(SOURCE_MODEL_DERIVATION_ANALYSIS_VERDICTS))
        )
    if caller_supplied_basis and verdict != "documented_partial_boundary":
        errors.append(
            "generated source-model-derivation dimension structurally detects a "
            "caller-supplied model-construction basis; only "
            "documented_partial_boundary is allowed until a separate machine-generated "
            "primitive-level derivation receipt exists"
        )
    bridge = str(analysis.get("lean_bridge_evidence") or "").strip()
    if not bridge:
        errors.append(f"`{field}.lean_bridge_evidence` is required")
    elif BARE_QUALIFIED_REFERENCE_RE.fullmatch(bridge) or (
        name_only is not None and name_only(bridge)
    ):
        errors.append(
            f"`{field}.lean_bridge_evidence` is name-only evidence; state the "
            "source-primitive-to-conclusion derivation"
        )
    elif (
        verdict == SOURCE_MODEL_DERIVATION_SAFE_VERDICT
        and not _SOURCE_MODEL_DERIVATION_EVIDENCE_RE.search(bridge)
    ):
        errors.append(
            f"`{field}.lean_bridge_evidence` must identify a checked derivation "
            "from the listed source primitives"
        )

    raw_response_contracts = analysis.get("contracts")
    response_by_digest: dict[str, dict[str, Any]] = {}
    if not isinstance(raw_response_contracts, list) or not raw_response_contracts:
        errors.append(f"`{field}.contracts` must be a nonempty list")
    else:
        for index, raw_response_contract in enumerate(raw_response_contracts):
            prefix = f"`{field}.contracts[{index}]`"
            if not isinstance(raw_response_contract, dict):
                errors.append(f"{prefix} is not an object")
                continue
            unexpected = sorted(
                set(raw_response_contract)
                - SOURCE_MODEL_DERIVATION_RESPONSE_CONTRACT_FIELDS
            )
            if unexpected:
                errors.append(f"{prefix} has unsupported field(s): " + ", ".join(unexpected))
            source_digest = str(
                raw_response_contract.get("source_semantic_sha256") or ""
            ).strip().lower()
            if not _SHA256_RE.fullmatch(source_digest):
                errors.append(f"{prefix}.source_semantic_sha256 is missing or malformed")
                continue
            if source_digest in response_by_digest:
                errors.append(f"`{field}.contracts` duplicates a source semantic identity")
                continue
            response_by_digest[source_digest] = raw_response_contract
    if set(response_by_digest) != set(source_contracts):
        errors.append(
            f"`{field}.contracts` must have exactly one primitive-to-conclusion "
            "comparison for every generated source model derivation contract"
        )

    for source_digest, source_contract in source_contracts.items():
        response_contract = response_by_digest.get(source_digest)
        if not isinstance(response_contract, dict):
            continue
        prefix = f"`{field}.contracts[{source_digest}]`"
        raw_source_ids = response_contract.get("source_primitive_component_ids")
        source_ids = (
            [str(value).strip() for value in raw_source_ids]
            if isinstance(raw_source_ids, list)
            and all(isinstance(value, str) for value in raw_source_ids)
            else []
        )
        if (
            not isinstance(raw_source_ids, list)
            or len(source_ids) != len(raw_source_ids)
            or len(source_ids) != len(set(source_ids))
        ):
            errors.append(
                f"{prefix}.source_primitive_component_ids must be a duplicate-free list"
            )
        elif source_ids != source_contract["primitive_ids"]:
            errors.append(
                f"{prefix}.source_primitive_component_ids does not reproduce the "
                "generated ordered source primitive basis"
            )
        lean_ids, lean_errors = _source_model_derivation_lean_primitives(
            response_contract.get("lean_primitive_components"),
            field=f"{prefix}.lean_primitive_components",
            name_only=name_only,
        )
        errors.extend(lean_errors)
        source_conclusion = str(
            response_contract.get("source_derived_conclusion_description") or ""
        ).strip()
        if source_conclusion != source_contract["derived_description"]:
            errors.append(
                f"{prefix}.source_derived_conclusion_description does not reproduce "
                "the generated source derived conclusion"
            )
        lean_conclusion = str(
            response_contract.get("lean_derived_conclusion_description") or ""
        ).strip()
        if not lean_conclusion:
            errors.append(f"{prefix}.lean_derived_conclusion_description is required")
        elif BARE_QUALIFIED_REFERENCE_RE.fullmatch(lean_conclusion) or (
            name_only is not None and name_only(lean_conclusion)
        ):
            errors.append(
                f"{prefix}.lean_derived_conclusion_description is name-only evidence; "
                "state the actual Lean conclusion"
            )
        route = str(response_contract.get("derivation_route") or "").strip()
        if route not in SOURCE_MODEL_DERIVATION_ROUTES:
            errors.append(
                f"{prefix}.derivation_route must be one of "
                + ", ".join(sorted(SOURCE_MODEL_DERIVATION_ROUTES))
            )
        derivation_evidence = str(
            response_contract.get("derivation_evidence") or "").strip()
        if not derivation_evidence:
            errors.append(f"{prefix}.derivation_evidence is required")
        elif BARE_QUALIFIED_REFERENCE_RE.fullmatch(derivation_evidence) or (
            name_only is not None and name_only(derivation_evidence)
        ):
            errors.append(
                f"{prefix}.derivation_evidence is name-only evidence; explain the "
                "checked source-primitive derivation"
            )
        elif (
            route == SOURCE_MODEL_DERIVATION_SAFE_ROUTE
            and not _SOURCE_MODEL_DERIVATION_EVIDENCE_RE.search(derivation_evidence)
        ):
            errors.append(
                f"{prefix}.derivation_evidence must identify a checked derivation "
                "from the listed source primitives"
            )

        if verdict == SOURCE_MODEL_DERIVATION_SAFE_VERDICT:
            if source_ids != source_contract["primitive_ids"]:
                errors.append(
                    f"{prefix} claims a source-model derivation while the source "
                    "primitive basis differs from the generated contract"
                )
            if lean_ids != source_contract["primitive_ids"]:
                errors.append(
                    f"{prefix} claims a source-model derivation while Lean omits, "
                    "adds, or reorders a source primitive"
                )
            if route != SOURCE_MODEL_DERIVATION_SAFE_ROUTE:
                errors.append(
                    f"{prefix} claims a source-model derivation but its conclusion is "
                    "caller-supplied or lacks a checked derivation from source primitives"
                )
        if caller_supplied_basis and route not in SOURCE_MODEL_DERIVATION_OPEN_ROUTES:
            errors.append(
                f"{prefix} has a structurally caller-supplied model-construction basis; "
                "its documented partial boundary must use an open derivation route"
            )

    outer_verdict = str(response.get("verdict") or "").strip()
    if outer_verdict == "not_applicable":
        errors.append(
            "cannot mark a source-required model-derivation dimension not_applicable"
        )
    if (
        verdict in SOURCE_MODEL_DERIVATION_OPEN_VERDICTS
        and outer_verdict == "matches_source_model"
    ):
        errors.append(
            "records an unresolved source-model derivation while the enclosing "
            "dimension claims matches_source_model"
        )
    if caller_supplied_basis and outer_verdict != "documented_partial_boundary":
        errors.append(
            "generated source-model-derivation dimension structurally detects a "
            "caller-supplied model-construction basis; its enclosing review must use "
            "documented_partial_boundary rather than a direct source-model match"
        )
    return errors


_SCALE_OR_VARIANCE_RE = re.compile(
    r"\b(?:variance|var\.?|standard\s+deviation|std\.?|scale|rate|"
    r"precision|dispersion)\b",
    re.I,
)
_UNIT_NORMALIZATION_RE = re.compile(
    r"\b(?:unit|one)[-\s]*(?:variance|standard\s+deviation|std\.?)\b"
    r"|\b(?:variance|var\.?|standard\s+deviation|std\.?)\s*"
    r"(?:=|is|of|:)?\s*(?:1|one)\b",
    re.I,
)
_UNIT_NORMALIZATION_EVIDENCE_RE = re.compile(
    r"(?:\b(?:checked|proved|proven|proof|theorem|lemma|deriv(?:ed|ation)?)\b"
    r"[\s\S]{0,160}\b(?:variance|var\.?|standard\s+deviation|std\.?|"
    r"second\s+moment|moment|integral)\b"
    r"|\b(?:variance|var\.?|standard\s+deviation|std\.?|second\s+moment|"
    r"moment|integral)\b[\s\S]{0,160}"
    r"\b(?:checked|proved|proven|proof|theorem|lemma|deriv(?:ed|ation)?)\b)",
    re.I,
)
_PARAMETER_TRANSLATION_RE = re.compile(
    r"(?:=|->|\b(?:same\s+parameter|identity\s+map|maps?\s+to|"
    r"corresponds?\s+to|translated?\s+by|represented\s+by)\b)",
    re.I,
)
_LAW_EQUIVALENCE_RE = re.compile(
    r"\b(?:equal(?:ity)?|equivalent|same\s+law|pushforward|"
    r"density\s+equality|measure\s+equality|pmf\s+equality|"
    r"distribution\s+equality)\b",
    re.I,
)
_NO_PARAMETERIZED_LAW_RE = re.compile(
    r"\b(?:no|without|absent)\b.*\b(?:parameter|scale|variance|rate)\b",
    re.I,
)
_FAMILY_COUPLING_RE = re.compile(
    r"(?:\b(?:same|shared|common|single|fixed|parameter[-\s]independent|"
    r"separate(?:ly)?|both|no\s+cross[-\s]parameter)\b.*"
    r"\b(?:base|noise|law|distribution|latent|parameter|accuracy|theta|θ)\b|"
    r"\b(?:base|noise|law|distribution|latent|parameter|accuracy|theta|θ)\b.*"
    r"\b(?:same|shared|common|single|fixed|parameter[-\s]independent|"
    r"separate(?:ly)?|both|no\s+cross[-\s]parameter)\b)",
    re.I,
)
BARE_QUALIFIED_REFERENCE_RE = re.compile(
    r"\s*(?:«[^»\n]+»|[A-Za-z_][A-Za-z0-9_']*)"
    r"(?:\.(?:«[^»\n]+»|[A-Za-z_][A-Za-z0-9_']*))*\s*"
)
_SOURCE_MODEL_DERIVATION_EVIDENCE_RE = re.compile(
    r"(?:\bchecked\b[\s\S]{0,160}\bderiv(?:e|ed|ation)\b[\s\S]{0,160}"
    r"\b(?:source\s+)?primitives?\b|\b(?:source\s+)?primitives?\b"
    r"[\s\S]{0,160}\bchecked\b[\s\S]{0,160}\bderiv(?:e|ed|ation)\b)",
    re.I,
)


def semantic_model_subanalysis_errors(
    raw_dimension: dict[str, Any],
    response: dict[str, Any],
    *,
    name_only: Callable[[str], bool] | None = None,
) -> list[str]:
    """Return missing structured semantic-model evidence for one dimension.

    A finite carrier can hide a missing ``N >= k`` threshold, and a probability
    law can hide a missing change-of-variables/sorting/relabeling bridge.  Both
    failures survived free-form source-model reviews in the past.  These
    requirements deliberately trigger from generated *type-shape* metadata,
    rather than by looking for terms such as ``sort`` or ``map`` in a theorem
    name.  A reviewer may explicitly record that the semantic operation is
    absent, but must still explain that conclusion against source and Lean
    semantics.
    """

    detected = bool(raw_dimension.get("detected_from_expanded_surface"))
    # Most subreviews are triggered by an expanded Lean shape. Source-pinned
    # equality-partition, strategic-observation, conditioning-information, and
    # source-model-derivation lanes are intentionally different: a scalar
    # endpoint can hide a partition, game, information-set, or derived model
    # consequence. Do not let a source obligation disappear merely because a
    # generic type scan saw no matching constructor.
    if (
        not detected
        and raw_dimension.get("requires_source_equality_partition_analysis") is not True
        and raw_dimension.get(
            "requires_strategic_observation_totality_analysis"
        )
        is not True
        and raw_dimension.get("requires_conditioning_information_analysis")
        is not True
        and raw_dimension.get("requires_source_model_derivation_analysis")
        is not True
    ):
        return []

    contracts = (
        (
            "requires_cardinality_boundary_analysis_when_detected",
            CARDINALITY_BOUNDARY_ANALYSIS_FIELD,
            CARDINALITY_BOUNDARY_ANALYSIS_VERDICTS,
            CARDINALITY_BOUNDARY_ANALYSIS_FIELDS,
        ),
        (
            "requires_transformed_law_analysis_when_detected",
            TRANSFORMED_LAW_ANALYSIS_FIELD,
            TRANSFORMED_LAW_ANALYSIS_VERDICTS,
            TRANSFORMED_LAW_ANALYSIS_FIELDS,
        ),
    )
    errors: list[str] = []
    for trigger, field, verdicts, required_fields in contracts:
        if raw_dimension.get(trigger) is not True:
            continue
        analysis = response.get(field)
        if not isinstance(analysis, dict):
            errors.append(f"needs `{field}` object")
            continue
        verdict = str(analysis.get("verdict") or "").strip()
        if verdict not in verdicts:
            errors.append(
                f"`{field}.verdict` must be one of " + ", ".join(sorted(verdicts))
            )
        for required_field in required_fields:
            value = str(analysis.get(required_field) or "").strip()
            if not value:
                errors.append(f"`{field}.{required_field}` is required")
            elif BARE_QUALIFIED_REFERENCE_RE.fullmatch(value) or (
                name_only is not None and name_only(value)
            ):
                errors.append(
                    f"`{field}.{required_field}` is name-only evidence; "
                    "state the source and expanded Lean semantics"
                )

    if raw_dimension.get(
        "requires_distribution_parameterization_analysis_when_detected"
    ) is True:
        field = DISTRIBUTION_PARAMETERIZATION_ANALYSIS_FIELD
        analysis = response.get(field)
        if not isinstance(analysis, dict):
            errors.append(f"needs `{field}` object")
            return errors
        verdict = str(analysis.get("verdict") or "").strip()
        if verdict not in DISTRIBUTION_PARAMETERIZATION_ANALYSIS_VERDICTS:
            errors.append(
                f"`{field}.verdict` must be one of "
                + ", ".join(sorted(DISTRIBUTION_PARAMETERIZATION_ANALYSIS_VERDICTS))
            )
        for required_field in DISTRIBUTION_PARAMETERIZATION_ANALYSIS_FIELDS:
            value = str(analysis.get(required_field) or "").strip()
            if not value:
                errors.append(f"`{field}.{required_field}` is required")
            elif BARE_QUALIFIED_REFERENCE_RE.fullmatch(value) or (
                name_only is not None and name_only(value)
            ):
                errors.append(
                    f"`{field}.{required_field}` is name-only evidence; "
                    "state the source and expanded Lean semantics"
                )

        source_scale = str(analysis.get("source_scale_or_variance") or "").strip()
        lean_scale = str(analysis.get("lean_scale_or_variance") or "").strip()
        if source_scale and not _SCALE_OR_VARIANCE_RE.search(source_scale):
            errors.append(
                f"`{field}.source_scale_or_variance` must state a source scale, "
                "rate, precision, standard deviation, or variance convention"
            )
        if lean_scale and not _SCALE_OR_VARIANCE_RE.search(lean_scale):
            errors.append(
                f"`{field}.lean_scale_or_variance` must state the corresponding Lean "
                "scale, rate, precision, standard deviation, or variance convention"
            )

        # A source declaration that its innovations have unit variance (or
        # unit standard deviation) is not discharged by a positive rate/scale
        # translation alone.  The reviewer must identify checked moment or
        # variance evidence tying the chosen Lean base law to that source
        # normalization.  This is driven by the recorded source convention,
        # never by a declaration name such as `unitVariance...`.
        if _UNIT_NORMALIZATION_RE.search(source_scale):
            normalization_evidence = str(
                analysis.get("unit_normalization_evidence") or ""
            ).strip()
            if not normalization_evidence:
                errors.append(
                    f"`{field}.unit_normalization_evidence` is required when the "
                    "source fixes unit variance or unit standard deviation"
                )
            elif BARE_QUALIFIED_REFERENCE_RE.fullmatch(normalization_evidence) or (
                name_only is not None and name_only(normalization_evidence)
            ):
                errors.append(
                    f"`{field}.unit_normalization_evidence` is name-only evidence; "
                    "state the checked source-to-Lean moment/variance link"
                )
            elif not _UNIT_NORMALIZATION_EVIDENCE_RE.search(normalization_evidence):
                errors.append(
                    f"`{field}.unit_normalization_evidence` must identify checked "
                    "moment, variance, standard-deviation, or integral evidence"
                )

        translation = str(analysis.get("parameter_translation") or "").strip()
        if verdict == "no_parameterized_law_or_scale":
            if translation and not _NO_PARAMETERIZED_LAW_RE.search(translation):
                errors.append(
                    f"`{field}.parameter_translation` must explicitly explain why no "
                    "distributional parameter translation applies"
                )
        elif translation and not _PARAMETER_TRANSLATION_RE.search(translation):
            errors.append(
                f"`{field}.parameter_translation` must give an explicit mapping or "
                "formula, not merely say that a positive reparameterization exists"
            )

        coupling_scope = str(analysis.get("family_coupling_scope") or "").strip()
        coupling_evidence = str(analysis.get("family_coupling_evidence") or "").strip()
        if coupling_scope and not _FAMILY_COUPLING_RE.search(coupling_scope):
            errors.append(
                f"`{field}.family_coupling_scope` must state whether compared "
                "parameter instances use one shared base law/latent source, "
                "separate laws, or no cross-parameter family"
            )
        if coupling_evidence and not _FAMILY_COUPLING_RE.search(coupling_evidence):
            errors.append(
                f"`{field}.family_coupling_evidence` must give checked evidence "
                "about the shared base law/latent source or the absence of a "
                "cross-parameter family"
            )

        law_evidence = str(analysis.get("law_equivalence_evidence") or "").strip()
        if law_evidence and not _LAW_EQUIVALENCE_RE.search(law_evidence):
            errors.append(
                f"`{field}.law_equivalence_evidence` must identify a checked equality, "
                "equivalence, density/PMF/measure equality, or pushforward of laws"
            )
        if verdict in {"mismatch_or_open", "documented_partial_boundary"} and str(
            response.get("verdict") or ""
        ).strip() == "matches_source_model":
            errors.append(
                f"`{field}` records `{verdict}` while the enclosing dimension claims "
                "matches_source_model"
            )
    errors.extend(
        source_carrier_coherence_analysis_errors(
            raw_dimension,
            response,
            name_only=name_only,
        )
    )
    errors.extend(
        source_model_composition_analysis_errors(
            raw_dimension,
            response,
            name_only=name_only,
        )
    )
    errors.extend(
        source_equality_partition_analysis_errors(
            raw_dimension,
            response,
            name_only=name_only,
        )
    )
    errors.extend(
        strategic_observation_totality_analysis_errors(
            raw_dimension,
            response,
            name_only=name_only,
        )
    )
    errors.extend(
        conditioning_information_analysis_errors(
            raw_dimension,
            response,
            name_only=name_only,
        )
    )
    errors.extend(
        source_model_derivation_analysis_errors(
            raw_dimension,
            response,
            name_only=name_only,
        )
    )
    return errors


@dataclass(frozen=True)
class CheckedProjectionResult:
    """The result of checking a sidecar projection against static evidence."""

    accepted: bool
    reason: str = ""
    constructor: dict[str, Any] | None = None


def source_record_classification(judgment: dict[str, Any] | None) -> str:
    """Return the normalized sidecar classification without name-based inference."""

    if not isinstance(judgment, dict):
        return ""
    return str(
        judgment.get("classification")
        or judgment.get("judgment")
        or judgment.get("verdict")
        or judgment.get("status")
        or ""
    ).strip()


def source_antecedent_key(field: object) -> str:
    """Return the generated key for one static required antecedent field."""

    if not isinstance(field, dict):
        return ""
    structure = str(field.get("structure") or "").strip()
    name = str(field.get("field") or "").strip()
    return f"{structure}.{name}" if structure and name else ""


def required_source_antecedent_keys(
    candidate: dict[str, Any],
) -> tuple[set[str], str]:
    """Return exact static antecedent keys, rejecting malformed candidate data."""

    raw_fields = candidate.get("required_source_antecedent_fields")
    if not isinstance(raw_fields, list) or not raw_fields:
        return set(), "static conditional constructor has no required source antecedent fields"
    keys = [source_antecedent_key(field) for field in raw_fields]
    if not all(keys):
        return set(), "static conditional constructor has malformed required source antecedent fields"
    if len(keys) != len(set(keys)):
        return set(), "static conditional constructor repeats a required source antecedent key"
    return set(keys), ""


def checked_projection_result(
    item: dict[str, Any],
    judgment: dict[str, Any] | None,
    current_exact_source_antecedent_keys: set[str],
) -> CheckedProjectionResult:
    """Check a ``proved_from_primitives`` sidecar claim for one conclusion input.

    The contract must select exactly one generated *conditional* constructor,
    reproduce its result type literally, and enumerate exactly the generated
    source antecedent keys.  Each listed antecedent must already have a current
    ``validated_source_assumption`` judgment with exact source evidence in the
    caller-provided set.  A candidate in the rejected/circular list is never
    accepted even if the sidecar names it.
    """

    if source_record_classification(judgment) != "proved_from_primitives":
        return CheckedProjectionResult(
            False,
            "conclusion-bearing premise is not classified `proved_from_primitives`",
        )
    if not isinstance(judgment, dict):
        return CheckedProjectionResult(False, "conclusion-bearing premise has no sidecar judgment")

    contract = judgment.get(CHECKED_PROJECTION_FIELD)
    if not isinstance(contract, dict):
        return CheckedProjectionResult(
            False,
            "proved_from_primitives conclusion premise has no checked_projection contract",
        )
    declaration = str(contract.get(CHECKED_PROJECTION_CONSTRUCTOR_FIELD) or "").strip()
    result_type = str(contract.get(CHECKED_PROJECTION_RESULT_TYPE_FIELD) or "").strip()
    raw_antecedents = contract.get(CHECKED_PROJECTION_ANTECEDENTS_FIELD)
    if not declaration:
        return CheckedProjectionResult(
            False,
            "checked_projection has no exact constructor_declaration",
        )
    if not result_type:
        return CheckedProjectionResult(
            False,
            "checked_projection has no exact conditional_constructor_result_type",
        )
    if not isinstance(raw_antecedents, list) or not raw_antecedents:
        return CheckedProjectionResult(
            False,
            "checked_projection has no source_antecedent_keys",
        )
    antecedent_keys = [str(key).strip() for key in raw_antecedents]
    if not all(antecedent_keys) or len(antecedent_keys) != len(set(antecedent_keys)):
        return CheckedProjectionResult(
            False,
            "checked_projection source_antecedent_keys are empty or duplicated",
        )

    rejected_declarations = {
        str(candidate.get("declaration") or "").strip()
        for candidate in item.get("rejected_constructors") or []
        if isinstance(candidate, dict)
    }
    if declaration in rejected_declarations:
        return CheckedProjectionResult(
            False,
            "checked_projection names a statically rejected/circular constructor",
        )

    matching_candidates = [
        candidate
        for candidate in item.get("conditional_constructors") or []
        if isinstance(candidate, dict)
        and str(candidate.get("declaration") or "").strip() == declaration
    ]
    if not matching_candidates:
        return CheckedProjectionResult(
            False,
            "checked_projection constructor is not in this conclusion input's static conditional-constructor list",
        )
    if len(matching_candidates) != 1:
        return CheckedProjectionResult(
            False,
            "checked_projection constructor is ambiguous in the static conditional-constructor list",
        )
    candidate = matching_candidates[0]
    if candidate.get("circular_inputs"):
        return CheckedProjectionResult(
            False,
            "checked_projection constructor has statically detected circular inputs",
        )
    static_result_type = str(candidate.get("result_type") or "").strip()
    if not static_result_type or result_type != static_result_type:
        return CheckedProjectionResult(
            False,
            "checked_projection conditional_constructor_result_type does not exactly match the static constructor result type",
        )
    expected_antecedents, malformed_reason = required_source_antecedent_keys(candidate)
    if malformed_reason:
        return CheckedProjectionResult(False, malformed_reason)
    provided_antecedents = set(antecedent_keys)
    if provided_antecedents != expected_antecedents:
        missing = sorted(expected_antecedents - provided_antecedents)
        extra = sorted(provided_antecedents - expected_antecedents)
        details: list[str] = []
        if missing:
            details.append("missing " + ", ".join(missing))
        if extra:
            details.append("unlisted " + ", ".join(extra))
        return CheckedProjectionResult(
            False,
            "checked_projection source_antecedent_keys do not exactly match static requirements"
            + (": " + "; ".join(details) if details else ""),
        )
    stale_or_unvalidated = sorted(
        provided_antecedents - current_exact_source_antecedent_keys
    )
    if stale_or_unvalidated:
        return CheckedProjectionResult(
            False,
            "checked_projection antecedent(s) lack current validated_source_assumption evidence: "
            + ", ".join(stale_or_unvalidated),
        )
    return CheckedProjectionResult(True, constructor=candidate)
