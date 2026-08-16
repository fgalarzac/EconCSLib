#!/usr/bin/env python3
"""Regression tests for source-game off-path observation totality auditing."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import sys
import tempfile
import unittest
from copy import deepcopy
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    value = str(import_root)
    if value not in sys.path:
        sys.path.insert(0, value)

from scripts import audit_evidence_integrity as evidence  # noqa: E402
from scripts import source_record_projection_contract as projection  # noqa: E402


HELPER = ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
SPEC = importlib.util.spec_from_file_location(
    "econcs_strategic_observation_source_record_audit", HELPER
)
assert SPEC is not None and SPEC.loader is not None
AUDIT = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = AUDIT
SPEC.loader.exec_module(AUDIT)


class StrategicObservationTotalityTests(unittest.TestCase):
    def source_quote(
        self,
        *,
        conditioning_population_scope: str,
        selected_event_history_scope: str,
        conditionalization_scopes: tuple[str, ...],
    ) -> str:
        population_sentence = {
            "entire_source_population": (
                "The posterior is evaluated on the entire source population."
            ),
            "source_defined_subpopulation_or_access_event": (
                "The posterior is evaluated only on the source-defined subgroup or "
                "access event."
            ),
            "source_defined_conditioned_or_restricted_population": (
                "The posterior is evaluated on the source-defined conditioned or "
                "restricted population."
            ),
        }.get(
            conditioning_population_scope,
            "The source declares the conditioning population explicitly.",
        )
        history_sentence = {
            "single_action_without_prior_strategic_history": (
                "The selected event contains the current action and resulting "
                "observation, with no prior strategic action history."
            ),
            "source_defined_sequential_action_history": (
                "The selected event includes the source-defined earlier strategic "
                "actions before the current action and observation."
            ),
            "source_defined_pre_action_state_or_history": (
                "The selected event includes the source-defined pre-action state or "
                "history before the current action and observation."
            ),
        }.get(
            selected_event_history_scope,
            "The source declares the selected-event history explicitly.",
        )
        conditionalization_sentences = {
            "positive_measurable_event": (
                "A conditional integral is used only on a measurable selected event "
                "after the source establishes that it has positive probability."
            ),
            "source_totalized_pointwise_observation_branch": (
                "The source defines a conditional value on every action-relevant "
                "observation branch."
            ),
            "ae_regular_conditional_distribution_or_disintegration": (
                "The regular conditional law is used only almost everywhere under its "
                "stated source base marginal."
            ),
        }
        conditionalization_text = " ".join(
            conditionalization_sentences.get(
                scope, "The source declares this conditionalization mode explicitly."
            )
            for scope in conditionalization_scopes
        )
        return " ".join(
            (
                "An equilibrium compares every feasible action by a posterior value "
                "after the resulting observation.",
                population_sentence,
                history_sentence,
                "The action decision and resulting selected observation event are "
                "measurable, and null events are handled before conditional evaluation.",
                conditionalization_text,
            )
        )

    def context(
        self,
        *,
        conditionalization_scopes: tuple[str, ...] = (
            "source_totalized_pointwise_observation_branch",
        ),
        contract_schema: int = 3,
        conditioning_population_scope: str = "entire_source_population",
        selected_event_history_scope: str = (
            "single_action_without_prior_strategic_history"
        ),
    ) -> dict[str, object]:
        quote = self.source_quote(
            conditioning_population_scope=conditioning_population_scope,
            selected_event_history_scope=selected_event_history_scope,
            conditionalization_scopes=conditionalization_scopes,
        )
        contract: dict[str, object] = {
            "schema": contract_schema,
            "equilibrium_action_scope": "all_feasible_actions",
            "action_description": "Every feasible report/action is compared.",
            "observation_description": (
                "Each feasible action has an observation branch used by the payoff."
            ),
            "conditional_value_kind": "conditional_expectation_or_posterior",
            "conditional_value_description": (
                "The payoff is a posterior or conditional expectation at the source "
                "selected observation event."
            ),
            "conditioning_population_scope": conditioning_population_scope,
            "conditioning_population_description": (
                "The source quote identifies the entire population, subgroup/access "
                "event, or conditioned population on which the conditional value is taken."
            ),
            "selected_event_history_scope": selected_event_history_scope,
            "selected_event_history_description": (
                "The source quote identifies every earlier strategic action or pre-action "
                "state/history component of the selected event."
            ),
            "selected_event_description": (
                "The source quote identifies the current action, resulting observation, "
                "measurability, and null-event handling for the selected event."
            ),
            "required_checks": [
                "equilibrium_action_domain",
                "observation_branch_domain",
                "zero_probability_observation_branches",
                "conditional_value_totality",
                "offpath_completion_or_infeasibility",
                "conditioning_population_carrier",
                "sequential_action_history_in_selected_event",
                "action_observation_event_measurability",
                "ae_fibre_or_base_scope",
            ],
        }
        if contract_schema == 2:
            contract["conditionalization_scope"] = (
                conditionalization_scopes[0]
                if len(conditionalization_scopes) == 1
                else ""
            )
        else:
            contract["conditionalization_scopes"] = list(conditionalization_scopes)
        return {
            "kind": "strategic_observation_totality",
            "source_location": "source.txt:1",
            "explanation": (
                "The source equilibrium ranges over feasible actions and uses an "
                "observation-contingent posterior value, so off-path observations "
                "need an explicit totality or domain argument."
            ),
            "source_anchor_evidence": [
                {
                    "path": "source.txt",
                    "line_start": 1,
                    "line_end": 1,
                    "quoted_text": quote,
                    "quoted_text_sha256": hashlib.sha256(
                        quote.encode("utf-8")
                    ).hexdigest(),
                }
            ],
            "strategic_observation_totality_contract": contract,
        }

    def map_payload(self, context: dict[str, object]) -> dict[str, object]:
        quote = context["source_anchor_evidence"][0]["quoted_text"]
        assert isinstance(quote, str)
        return {
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": hashlib.sha256(
                (quote + "\n").encode("utf-8")
            ).hexdigest(),
            "source_coverage_mode": "named_theoretical_statements",
            "items": {
                # This storage key deliberately has no game/equilibrium name.
                "source_semantic_contract": {
                    "claim_bearing": True,
                    "source_kind": "proposition",
                    "source_location": "source.txt:1",
                    "semantic_context_requirements": [context],
                }
            },
        }

    def generated_dimension(
        self, context: dict[str, object] | None = None
    ) -> dict[str, object]:
        source_map = self.map_payload(context or self.context())
        source_item = source_map["items"]["source_semantic_contract"]
        assert isinstance(source_item, dict)
        source_identity = AUDIT.semantic_contract_source_identity(
            "source_semantic_contract", source_item
        )
        # Neither review row nor declaration contains a game-related spelling.
        declaration = "theorem opaque_endpoint (x : Nat) : x = x := by rfl"
        qualified = "Fixture.Interface.opaque_endpoint"
        declaration_identity = AUDIT.reviewed_declaration_identity(
            qualified, declaration
        )
        assert declaration_identity is not None
        signature_sha = hashlib.sha256(b"opaque elaborated surface").hexdigest()
        signature = {
            "qualified_declaration": qualified,
            "elaborated_signature_sha256": signature_sha,
        }
        association = {
            "schema": 2,
            "association_origin": AUDIT.EXPLICIT_DIRECT_SOURCE_ROUTE_ORIGIN,
            "role": AUDIT.EXPLICIT_DIRECT_SOURCE_ROUTE_ROLE,
            "source_item_identities": [source_identity],
            "reviewed_declaration_identity": declaration_identity,
            "reviewed_elaborated_signature_identity": signature,
            "semantic_association_sha256": AUDIT.semantic_source_association_digest(
                [source_identity], signature
            ),
        }
        item: dict[str, object] = {
            "row": "unrelated_navigation_label",
            "judgment_key": "semantic-model::opaque",
            "qualified_declaration": qualified,
            "dimensions": [
                {
                    "id": "expanded_binders_and_domain",
                    "detected_from_expanded_surface": False,
                    "required_check": "ordinary semantic review",
                }
            ],
            "source_statement_association": association,
        }
        items, errors, counts = AUDIT.attach_strategic_observation_totality_requirements(
            [item],
            paper_statement_map=source_map,
            elaborated_signature_sha256_by_qualified={qualified: signature_sha},
        )
        self.assertEqual(errors, [])
        self.assertEqual(counts["strategic_observation_totality_context_count"], 1)
        self.assertEqual(
            counts["strategic_observation_totality_requirement_count"], 1
        )
        result = items[0]
        assert isinstance(result, dict)
        return next(
            dimension
            for dimension in result["dimensions"]
            if dimension["id"] == AUDIT.STRATEGIC_OBSERVATION_TOTALITY_DIMENSION
        )

    def conditionalization_scopes_for_dimension(
        self, dimension: dict[str, object]
    ) -> tuple[str, ...]:
        requirement = dimension["strategic_observation_totality"]
        assert isinstance(requirement, dict)
        contracts = requirement["contracts"]
        assert isinstance(contracts, list)
        scopes: set[str] = set()
        for entry in contracts:
            assert isinstance(entry, dict)
            contract = entry["strategic_observation_totality_contract"]
            assert isinstance(contract, dict)
            raw_scopes = contract.get("conditionalization_scopes")
            if isinstance(raw_scopes, list):
                scopes.update(scope for scope in raw_scopes if isinstance(scope, str))
                continue
            legacy_scope = contract.get("conditionalization_scope")
            if isinstance(legacy_scope, str):
                scopes.add(legacy_scope)
        return tuple(sorted(scopes))

    def response_for(
        self, dimension: dict[str, object]
    ) -> dict[str, object]:
        pin = dimension["strategic_observation_totality_association"][
            "semantic_association_sha256"
        ]
        assert isinstance(pin, str)
        scopes = self.conditionalization_scopes_for_dimension(dimension)
        scope_evidence = {
            "positive_measurable_event": (
                "The source and Lean routes both evaluate the conditional integral only "
                "after proving the selected measurable event has positive probability."
            ),
            "source_totalized_pointwise_observation_branch": (
                "The source gives every action-relevant observation branch a finite "
                "value, and the checked Lean bridge identifies that totalized value."
            ),
            "ae_regular_conditional_distribution_or_disintegration": (
                "The source and Lean routes use the regular conditional version only on "
                "the stated almost-everywhere base marginal, never as a pointwise fibre "
                "identity outside that scope."
            ),
        }
        scope_dispositions = {
            "positive_measurable_event": "positive_measurable_event_checked",
            "source_totalized_pointwise_observation_branch": (
                "source_totalized_pointwise_fibres_checked"
            ),
            "ae_regular_conditional_distribution_or_disintegration": (
                "ae_fibre_base_scope_and_version_checked"
            ),
        }
        assert scopes
        fibre_disposition = (
            "mixed_source_conditionalization_scopes_checked"
            if len(scopes) > 1
            else scope_dispositions[scopes[0]]
        )
        response: dict[str, object] = {
            "verdict": "matches_source_model",
            "source_locator": "source.txt:1",
            "semantic_comparison": (
                "The source and Lean routes compare the same feasible action and "
                "observation domains."
            ),
            "lean_evidence": (
                "The expanded model exposes the action domain and the observation value."
            ),
            "strategic_observation_totality_analysis": {
                "semantic_association_sha256": pin,
                "verdict": "source_totalizes_all_action_relevant_observations_checked",
                "equilibrium_action_domain": (
                    "The source maximizes over every feasible action, including a "
                    "deviation that would otherwise make an observation off path."
                ),
                "lean_feasible_action_domain": (
                    "The expanded Lean model quantifies over the same full feasible "
                    "action domain."
                ),
                "conditioning_population_disposition": (
                    "source_entire_population_carrier_checked"
                ),
                "conditioning_population_carrier_evidence": (
                    "The source and Lean conditional values both use the whole source "
                    "population; no subgroup, access event, or generated restriction "
                    "changes the carrier."
                ),
                "selected_event_history_disposition": "single_action_event_checked",
                "selected_event_history_evidence": (
                    "The source selected event contains only the current feasible action "
                    "and resulting observation, and the Lean event has no omitted prior "
                    "strategic action history."
                ),
                "event_measurability_disposition": (
                    "measurable_action_and_observation_event_checked"
                ),
                "action_observation_event_measurability_evidence": (
                    "The checked route establishes measurability of the action decision "
                    "and resulting observation event, and separately classifies its null "
                    "case before conditional evaluation."
                ),
                "fibre_base_scope_disposition": (
                    fibre_disposition
                ),
                "ae_fibre_or_base_scope_evidence": (
                    "The source and Lean routes use exactly the declared positive-event, "
                    "pointwise, or almost-everywhere conditionalization scope; no chosen "
                    "conditional version is upgraded into an unsupported pointwise claim."
                ),
                "conditionalization_scope_evidence": {
                    scope: scope_evidence[scope] for scope in scopes
                },
                "observation_branch_analysis": (
                    "Every action-induced observation branch is compared, including "
                    "branches with zero probability under a candidate profile."
                ),
                "zero_probability_branch_disposition": (
                    "source_totalizes_zero_probability_observations"
                ),
                "conditional_value_totality": (
                    "The source defines a finite conditional value for each action-"
                    "relevant observation branch, not merely positive-probability ones."
                ),
                "offpath_completion_or_infeasibility_evidence": (
                    "A source-backed completion specifies the off-path conditional "
                    "value before the best-response comparison."
                ),
                "lean_bridge_evidence": (
                    "A checked bridge proves that the source totalized value is the "
                    "Lean observation payoff on every feasible branch."
                ),
            },
        }
        return response

    def full_model_item(self, dimension: dict[str, object]) -> dict[str, object]:
        return {
            "dimensions": [
                *[
                    {"id": dimension_id, "detected_from_expanded_surface": False}
                    for dimension_id in sorted(evidence.SEMANTIC_MODEL_REVIEW_DIMENSIONS)
                ],
                dimension,
            ]
        }

    def full_judgment(self, dimension: dict[str, object]) -> dict[str, object]:
        base = {
            dimension_id: {
                "verdict": "matches_source_model",
                "source_locator": "source.txt:1",
                "semantic_comparison": "The source and Lean component agree.",
                "lean_evidence": "The expanded Lean component is checked.",
            }
            for dimension_id in evidence.SEMANTIC_MODEL_REVIEW_DIMENSIONS
        }
        base[AUDIT.STRATEGIC_OBSERVATION_TOTALITY_DIMENSION] = self.response_for(
            dimension
        )
        return {
            "classification": "semantic_model_review",
            "semantic_model_dimensions": base,
        }

    def test_context_is_byte_pinned_and_dimension_is_not_name_selected(self) -> None:
        context = self.context()
        payload = self.map_payload(context)
        with tempfile.TemporaryDirectory() as tmpdir:
            paper = Path(tmpdir) / "Fixture"
            paper.mkdir()
            quote = context["source_anchor_evidence"][0]["quoted_text"]
            assert isinstance(quote, str)
            (paper / "source.txt").write_text(quote + "\n", encoding="utf-8")
            audit_dir = paper / "audit"
            audit_dir.mkdir()
            map_path = audit_dir / "paper_statement_map.json"
            map_path.write_text(json.dumps(payload), encoding="utf-8")
            findings = evidence.semantic_context_requirement_findings(
                paper, "partially formalized", map_path, payload
            )
            contexts, errors = AUDIT.source_map_semantic_context_requirements(paper)
            malformed = deepcopy(payload)
            malformed_contract = malformed["items"]["source_semantic_contract"][
                "semantic_context_requirements"
            ][0]["strategic_observation_totality_contract"]
            malformed_contract["required_checks"] = [
                "equilibrium_action_domain"
            ]
            malformed_findings = evidence.semantic_context_requirement_findings(
                paper, "partially formalized", map_path, malformed
            )
            missing_scope_fields = deepcopy(payload)
            missing_contract = missing_scope_fields["items"][
                "source_semantic_contract"
            ]["semantic_context_requirements"][0][
                "strategic_observation_totality_contract"
            ]
            del missing_contract["conditioning_population_description"]
            del missing_contract["selected_event_history_description"]
            del missing_contract["selected_event_description"]
            del missing_contract["conditionalization_scopes"]
            missing_scope_findings = evidence.semantic_context_requirement_findings(
                paper, "partially formalized", map_path, missing_scope_fields
            )
            empty_scopes = deepcopy(payload)
            empty_scopes["items"]["source_semantic_contract"][
                "semantic_context_requirements"
            ][0]["strategic_observation_totality_contract"][
                "conditionalization_scopes"
            ] = []
            empty_scope_findings = evidence.semantic_context_requirement_findings(
                paper, "partially formalized", map_path, empty_scopes
            )
            duplicate_scopes = deepcopy(payload)
            duplicate_contract = duplicate_scopes["items"][
                "source_semantic_contract"
            ]["semantic_context_requirements"][0][
                "strategic_observation_totality_contract"
            ]
            duplicate_contract["conditionalization_scopes"] = [
                "positive_measurable_event",
                "positive_measurable_event",
            ]
            duplicate_scope_findings = evidence.semantic_context_requirement_findings(
                paper, "partially formalized", map_path, duplicate_scopes
            )
            malformed_schema = deepcopy(payload)
            malformed_schema["items"]["source_semantic_contract"][
                "semantic_context_requirements"
            ][0]["strategic_observation_totality_contract"]["schema"] = []
            malformed_schema_findings = evidence.semantic_context_requirement_findings(
                paper, "partially formalized", map_path, malformed_schema
            )

        self.assertEqual(findings, [])
        self.assertEqual(errors, [])
        self.assertEqual(
            contexts[0]["kind"], "strategic_observation_totality"
        )
        self.assertIn(
            "strategic_observation_totality_contract", contexts[0]
        )
        self.assertTrue(
            any(
                "must contain every equilibrium-domain" in finding.message
                for finding in malformed_findings
            ),
            malformed_findings,
        )
        missing_scope_messages = [finding.message for finding in missing_scope_findings]
        self.assertTrue(
            any("conditioning_population_description" in message for message in missing_scope_messages),
            missing_scope_messages,
        )
        self.assertTrue(
            any("selected_event_history_description" in message for message in missing_scope_messages),
            missing_scope_messages,
        )
        self.assertTrue(
            any("selected_event_description" in message for message in missing_scope_messages),
            missing_scope_messages,
        )
        self.assertTrue(
            any("conditionalization_scopes" in message for message in missing_scope_messages),
            missing_scope_messages,
        )
        self.assertTrue(
            any(
                "nonempty duplicate-free list" in finding.message
                for finding in empty_scope_findings
            ),
            empty_scope_findings,
        )
        self.assertTrue(
            any(
                "nonempty duplicate-free list" in finding.message
                for finding in duplicate_scope_findings
            ),
            duplicate_scope_findings,
        )
        self.assertTrue(
            any("schema must be 2 or 3" in finding.message for finding in malformed_schema_findings),
            malformed_schema_findings,
        )

        dimension = self.generated_dimension()
        serialized = json.dumps(dimension)
        self.assertNotIn("unrelated_navigation_label", serialized)
        self.assertNotIn("source_semantic_contract", serialized)
        self.assertTrue(dimension["required_from_source_pinned_context"])
        self.assertTrue(
            dimension["requires_strategic_observation_totality_analysis"]
        )

    def test_lean_only_offpath_completion_cannot_close_source_match(self) -> None:
        dimension = self.generated_dimension()
        judgment = self.full_judgment(dimension)
        item = self.full_model_item(dimension)
        self.assertTrue(evidence.semantic_model_judgment_is_complete(item, judgment))

        unsafe = deepcopy(judgment)
        analysis = unsafe["semantic_model_dimensions"][
            AUDIT.STRATEGIC_OBSERVATION_TOTALITY_DIMENSION
        ]["strategic_observation_totality_analysis"]
        analysis["zero_probability_branch_disposition"] = "lean_only_offpath_completion"
        analysis["conditional_value_totality"] = (
            "Lean selected a finite default on the zero-probability branch, but "
            "the source did not define that conditional value."
        )
        self.assertFalse(evidence.semantic_model_judgment_is_complete(item, unsafe))
        errors = projection.strategic_observation_totality_analysis_errors(
            dimension,
            unsafe["semantic_model_dimensions"][
                AUDIT.STRATEGIC_OBSERVATION_TOTALITY_DIMENSION
            ],
        )
        self.assertTrue(
            any("Lean-only off-path branch" in error for error in errors), errors
        )

    def test_source_ae_equilibrium_scope_can_close_null_branches(self) -> None:
        dimension = self.generated_dimension(
            self.context(
                conditionalization_scopes=(
                    "ae_regular_conditional_distribution_or_disintegration",
                )
            )
        )
        judgment = self.full_judgment(dimension)
        item = self.full_model_item(dimension)
        analysis = judgment["semantic_model_dimensions"][
            AUDIT.STRATEGIC_OBSERVATION_TOTALITY_DIMENSION
        ]["strategic_observation_totality_analysis"]
        analysis["verdict"] = "source_ae_or_event_scoped_equilibrium_checked"
        analysis["equilibrium_action_domain"] = (
            "The source compares actions up to the realized population law and "
            "requires a profitable deviation only on a positive-mass event."
        )
        analysis["lean_feasible_action_domain"] = (
            "The Lean route proves the same almost-everywhere action condition "
            "on the source population carrier."
        )
        analysis["fibre_base_scope_disposition"] = (
            "ae_fibre_base_scope_and_version_checked"
        )
        analysis["ae_fibre_or_base_scope_evidence"] = (
            "The conditional law is an RCD only for almost every base point under "
            "the stated source population marginal, and the Lean result is stated on "
            "that same a.e. base rather than at every individual fibre."
        )
        analysis["observation_branch_analysis"] = (
            "A conditional value is used only for a positive-mass observation "
            "event; the proof shows every positive-mass departure is unstable."
        )
        analysis["zero_probability_branch_disposition"] = (
            "source_ae_or_event_scope_excludes_pointwise_offpath_choice"
        )
        analysis["conditional_value_totality"] = (
            "The source PBO formula is required on positive-mass information "
            "sets and does not assign a value to a null branch."
        )
        analysis["offpath_completion_or_infeasibility_evidence"] = (
            "The source's a.e. equilibrium scope excludes a singleton or null "
            "branch from the deviation comparison rather than supplying a Lean-only payoff."
        )
        analysis["lean_bridge_evidence"] = (
            "A checked positive-mass instability theorem transports the source "
            "a.e. convention to the Lean equilibrium conclusion."
        )

        self.assertTrue(evidence.semantic_model_judgment_is_complete(item, judgment))
        self.assertEqual(
            projection.strategic_observation_totality_analysis_errors(
                dimension,
                judgment["semantic_model_dimensions"][
                    AUDIT.STRATEGIC_OBSERVATION_TOTALITY_DIMENSION
                ],
            ),
            [],
        )

    def test_positive_measurable_event_scope_can_close_without_fibre_version(
        self,
    ) -> None:
        dimension = self.generated_dimension(
            self.context(conditionalization_scopes=("positive_measurable_event",))
        )
        judgment = self.full_judgment(dimension)
        item = self.full_model_item(dimension)
        analysis = judgment["semantic_model_dimensions"][
            AUDIT.STRATEGIC_OBSERVATION_TOTALITY_DIMENSION
        ]["strategic_observation_totality_analysis"]
        analysis["verdict"] = "source_ae_or_event_scoped_equilibrium_checked"
        analysis["fibre_base_scope_disposition"] = (
            "positive_measurable_event_checked"
        )
        analysis["ae_fibre_or_base_scope_evidence"] = (
            "The conditional value is an integral over the source-pinned measurable "
            "selected event after proving that event has positive mass; no RCD or "
            "pointwise fibre version is used."
        )
        analysis["observation_branch_analysis"] = (
            "The action/observation event is evaluated only after its positive source "
            "mass is established, while null branches remain outside the a.e. comparison."
        )
        analysis["zero_probability_branch_disposition"] = (
            "source_ae_or_event_scope_excludes_pointwise_offpath_choice"
        )
        analysis["conditional_value_totality"] = (
            "The source does not assign a conditional value on a null event; every "
            "used conditional integral has an explicit positive measurable event."
        )
        analysis["offpath_completion_or_infeasibility_evidence"] = (
            "The source a.e. equilibrium scope rules out pointwise off-path comparison "
            "instead of introducing a Lean-only default value."
        )
        analysis["lean_bridge_evidence"] = (
            "A checked positive-event bridge identifies the source selected event, its "
            "probability, and the Lean conditional integral."
        )

        self.assertTrue(evidence.semantic_model_judgment_is_complete(item, judgment))
        self.assertEqual(
            projection.strategic_observation_totality_analysis_errors(
                dimension,
                judgment["semantic_model_dimensions"][
                    AUDIT.STRATEGIC_OBSERVATION_TOTALITY_DIMENSION
                ],
            ),
            [],
        )

    def test_multiple_conditionalization_scopes_require_mixed_evidence(
        self,
    ) -> None:
        dimension = self.generated_dimension(
            self.context(
                conditionalization_scopes=(
                    "positive_measurable_event",
                    "ae_regular_conditional_distribution_or_disintegration",
                )
            )
        )
        judgment = self.full_judgment(dimension)
        item = self.full_model_item(dimension)
        analysis = judgment["semantic_model_dimensions"][
            AUDIT.STRATEGIC_OBSERVATION_TOTALITY_DIMENSION
        ]["strategic_observation_totality_analysis"]
        analysis["verdict"] = "source_ae_or_event_scoped_equilibrium_checked"
        analysis["observation_branch_analysis"] = (
            "The selected event is used only after positive source mass is established, "
            "and the posterior kernel is compared only on its stated a.e. base."
        )
        analysis["zero_probability_branch_disposition"] = (
            "source_ae_or_event_scope_excludes_pointwise_offpath_choice"
        )
        analysis["conditional_value_totality"] = (
            "The event integral is defined only on the positive selected event, while "
            "the posterior kernel remains scoped to its source a.e. base."
        )
        analysis["offpath_completion_or_infeasibility_evidence"] = (
            "The source a.e. equilibrium convention excludes a null off-path branch "
            "instead of adding a Lean-only conditional value."
        )
        analysis["lean_bridge_evidence"] = (
            "Checked bridges identify both the positive selected event and the a.e. "
            "regular conditional base without converting either into a pointwise default."
        )

        self.assertTrue(evidence.semantic_model_judgment_is_complete(item, judgment))
        self.assertEqual(
            projection.strategic_observation_totality_analysis_errors(
                dimension,
                judgment["semantic_model_dimensions"][
                    AUDIT.STRATEGIC_OBSERVATION_TOTALITY_DIMENSION
                ],
            ),
            [],
        )

        missing_one_mode = deepcopy(judgment)
        missing_analysis = missing_one_mode["semantic_model_dimensions"][
            AUDIT.STRATEGIC_OBSERVATION_TOTALITY_DIMENSION
        ]["strategic_observation_totality_analysis"]
        del missing_analysis["conditionalization_scope_evidence"][
            "ae_regular_conditional_distribution_or_disintegration"
        ]
        self.assertFalse(
            evidence.semantic_model_judgment_is_complete(item, missing_one_mode)
        )
        errors = projection.strategic_observation_totality_analysis_errors(
            dimension,
            missing_one_mode["semantic_model_dimensions"][
                AUDIT.STRATEGIC_OBSERVATION_TOTALITY_DIMENSION
            ],
        )
        self.assertTrue(
            any("must have exactly the declared conditionalization scopes" in error for error in errors),
            errors,
        )

    def test_legacy_single_scope_context_is_safely_reissued_as_schema_three(
        self,
    ) -> None:
        dimension = self.generated_dimension(self.context(contract_schema=2))
        requirement = dimension["strategic_observation_totality"]
        assert isinstance(requirement, dict)
        self.assertEqual(requirement["schema"], 3)
        judgment = self.full_judgment(dimension)
        self.assertTrue(
            evidence.semantic_model_judgment_is_complete(
                self.full_model_item(dimension), judgment
            )
        )

    def test_malformed_generated_schema_fails_closed_without_crashing(self) -> None:
        dimension = self.generated_dimension()
        malformed = deepcopy(dimension)
        requirement = malformed["strategic_observation_totality"]
        assert isinstance(requirement, dict)
        requirement["schema"] = []
        judgment = self.full_judgment(malformed)
        item = self.full_model_item(malformed)
        self.assertFalse(evidence.semantic_model_judgment_is_complete(item, judgment))
        errors = projection.strategic_observation_totality_analysis_errors(
            malformed,
            judgment["semantic_model_dimensions"][
                AUDIT.STRATEGIC_OBSERVATION_TOTALITY_DIMENSION
            ],
        )
        self.assertTrue(
            any("generated strategic-observation-totality requirement must use schema" in error for error in errors),
            errors,
        )

        mixed_fields = deepcopy(dimension)
        mixed_requirement = mixed_fields["strategic_observation_totality"]
        assert isinstance(mixed_requirement, dict)
        contracts = mixed_requirement["contracts"]
        assert isinstance(contracts, list) and contracts
        first_contract = contracts[0]
        assert isinstance(first_contract, dict)
        source_contract = first_contract["strategic_observation_totality_contract"]
        assert isinstance(source_contract, dict)
        source_contract["conditionalization_scope"] = "positive_measurable_event"
        mixed_judgment = self.full_judgment(mixed_fields)
        mixed_errors = projection.strategic_observation_totality_analysis_errors(
            mixed_fields,
            mixed_judgment["semantic_model_dimensions"][
                AUDIT.STRATEGIC_OBSERVATION_TOTALITY_DIMENSION
            ],
        )
        self.assertTrue(
            any("mixes legacy and schema-3 conditionalization fields" in error for error in mixed_errors),
            mixed_errors,
        )

    def test_source_subpopulation_and_sequential_history_requirements_can_close(
        self,
    ) -> None:
        dimension = self.generated_dimension(
            self.context(
                conditioning_population_scope=(
                    "source_defined_subpopulation_or_access_event"
                ),
                selected_event_history_scope=(
                    "source_defined_sequential_action_history"
                ),
            )
        )
        judgment = self.full_judgment(dimension)
        item = self.full_model_item(dimension)
        analysis = judgment["semantic_model_dimensions"][
            AUDIT.STRATEGIC_OBSERVATION_TOTALITY_DIMENSION
        ]["strategic_observation_totality_analysis"]
        analysis["conditioning_population_disposition"] = (
            "source_conditioned_or_restricted_population_checked"
        )
        analysis["conditioning_population_carrier_evidence"] = (
            "The source conditions on the stated subgroup/access event, and the checked "
            "Lean bridge restricts exactly that source population rather than the whole "
            "population or a generated weighting measure."
        )
        analysis["selected_event_history_disposition"] = (
            "source_history_in_selected_event_checked"
        )
        analysis["selected_event_history_evidence"] = (
            "The source selected event includes the stated earlier strategic actions "
            "before the current action and observation, and the Lean selected event "
            "contains the same history in the same order."
        )

        self.assertTrue(evidence.semantic_model_judgment_is_complete(item, judgment))
        self.assertEqual(
            projection.strategic_observation_totality_analysis_errors(
                dimension,
                judgment["semantic_model_dimensions"][
                    AUDIT.STRATEGIC_OBSERVATION_TOTALITY_DIMENSION
                ],
            ),
            [],
        )

    def test_missing_population_history_event_or_fibre_evidence_fails_closed(
        self,
    ) -> None:
        dimension = self.generated_dimension()
        judgment = self.full_judgment(dimension)
        item = self.full_model_item(dimension)
        analysis = judgment["semantic_model_dimensions"][
            AUDIT.STRATEGIC_OBSERVATION_TOTALITY_DIMENSION
        ]["strategic_observation_totality_analysis"]
        del analysis["conditioning_population_carrier_evidence"]
        del analysis["selected_event_history_evidence"]
        del analysis["action_observation_event_measurability_evidence"]
        del analysis["ae_fibre_or_base_scope_evidence"]
        del analysis["conditionalization_scope_evidence"]

        self.assertFalse(evidence.semantic_model_judgment_is_complete(item, judgment))
        errors = projection.strategic_observation_totality_analysis_errors(
            dimension,
            judgment["semantic_model_dimensions"][
                AUDIT.STRATEGIC_OBSERVATION_TOTALITY_DIMENSION
            ],
        )
        self.assertTrue(
            any("conditioning_population_carrier_evidence" in error for error in errors),
            errors,
        )
        self.assertTrue(
            any("selected_event_history_evidence" in error for error in errors), errors
        )
        self.assertTrue(
            any(
                "action_observation_event_measurability_evidence" in error
                for error in errors
            ),
            errors,
        )
        self.assertTrue(
            any("ae_fibre_or_base_scope_evidence" in error for error in errors),
            errors,
        )
        self.assertTrue(
            any("conditionalization_scope_evidence" in error for error in errors),
            errors,
        )

    def test_extension_requires_generated_marker_and_preserves_base_schema(self) -> None:
        dimension = self.generated_dimension()
        dimensions = [
            *[{"id": dimension_id} for dimension_id in evidence.SEMANTIC_MODEL_REVIEW_DIMENSIONS],
            dimension,
        ]
        self.assertEqual(evidence.semantic_model_item_dimension_ids_error(dimensions), "")

        unmarked = deepcopy(dimensions)
        for item in unmarked:
            if item["id"] == AUDIT.STRATEGIC_OBSERVATION_TOTALITY_DIMENSION:
                del item["requires_strategic_observation_totality_analysis"]
        self.assertIn(
            "explicitly generated source-pinned",
            evidence.semantic_model_item_dimension_ids_error(unmarked),
        )

    def test_non_opt_in_source_maps_keep_feature_scoped_reuse_identity(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            paper = root / "papers" / "Fixture"
            audit_dir = paper / "audit"
            audit_dir.mkdir(parents=True)
            map_path = audit_dir / "paper_statement_map.json"
            map_path.write_text(json.dumps({"items": {}}), encoding="utf-8")
            baseline = AUDIT.source_record_feature_scoped_engine_identities(root, paper)

            map_path.write_text(
                json.dumps(
                    {
                        "items": {
                            "ordinary": {
                                "semantic_context_requirements": [
                                    {
                                        "kind": "ordinary_source_convention",
                                        "source_location": "source.txt:1",
                                        "explanation": "A source-only convention.",
                                        "source_anchor_evidence": [],
                                    }
                                ]
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            unchanged = AUDIT.source_record_feature_scoped_engine_identities(root, paper)

            map_path.write_text(
                json.dumps(self.map_payload(self.context())), encoding="utf-8"
            )
            opted_in = AUDIT.source_record_feature_scoped_engine_identities(root, paper)

        self.assertEqual(baseline, unchanged)
        self.assertNotIn(
            AUDIT.STRATEGIC_OBSERVATION_TOTALITY_CONTEXT_SURFACE_ENGINE_IDENTITY,
            unchanged,
        )
        self.assertIn(
            AUDIT.STRATEGIC_OBSERVATION_TOTALITY_CONTEXT_SURFACE_ENGINE_IDENTITY,
            opted_in,
        )


if __name__ == "__main__":
    unittest.main()
