#!/usr/bin/env python3
"""Regression tests for source-vs-Lean conditional-information auditing."""

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
    "econcs_conditioning_information_source_record_audit", HELPER
)
assert SPEC is not None and SPEC.loader is not None
AUDIT = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = AUDIT
SPEC.loader.exec_module(AUDIT)


class ConditioningInformationContractTests(unittest.TestCase):
    source_quote = (
        "The belief after a report conditions on access, the take decision, the "
        "report decision, and the reported score. The law is selected by the take "
        "and report decisions and holds almost everywhere under the observation marginal."
    )

    def context(self) -> dict[str, object]:
        return {
            "kind": "conditioning_information",
            "source_location": "source.txt:1",
            "explanation": (
                "The source specifies a PBO belief after both action stages and the "
                "reported score, rather than a raw score-only posterior."
            ),
            "source_anchor_evidence": [
                {
                    "path": "source.txt",
                    "line_start": 1,
                    "line_end": 1,
                    "quoted_text": self.source_quote,
                    "quoted_text_sha256": hashlib.sha256(
                        self.source_quote.encode("utf-8")
                    ).hexdigest(),
                }
            ],
            "conditioning_information_contract": {
                "schema": 1,
                "conditional_value_kind": "bayesian_or_pbo_belief",
                "source_observed_components": [
                    {
                        "id": "access",
                        "description": "Whether the individual has access.",
                    },
                    {
                        "id": "take",
                        "description": "Whether the individual takes the assessment.",
                    },
                    {
                        "id": "report",
                        "description": "Whether the assessment result is reported.",
                    },
                    {
                        "id": "reported_score",
                        "description": "The score observed on the reporting branch.",
                    },
                ],
                "source_action_selection_stages": [
                    {
                        "id": "take_decision",
                        "description": "Taking occurs before reporting.",
                    },
                    {
                        "id": "report_decision",
                        "description": "Reporting occurs after taking.",
                    },
                ],
                "source_law_population": "selected_by_source_actions",
                "conditionalization_scopes": [
                    "ae_regular_conditional_distribution_or_disintegration"
                ],
            },
        }

    def source_map(self, context: dict[str, object]) -> dict[str, object]:
        return {
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": hashlib.sha256(
                (self.source_quote + "\n").encode("utf-8")
            ).hexdigest(),
            "source_coverage_mode": "named_theoretical_statements",
            "items": {
                # Neither this storage key nor the direct Lean declaration below
                # contains a conditional/belief/posterior naming hint.
                "neutral_source_route": {
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
        source_map = self.source_map(context or self.context())
        source_item = source_map["items"]["neutral_source_route"]
        assert isinstance(source_item, dict)
        source_identity = AUDIT.semantic_contract_source_identity(
            "neutral_source_route", source_item
        )
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
        items, errors, counts = AUDIT.attach_conditioning_information_requirements(
            [item],
            paper_statement_map=source_map,
            elaborated_signature_sha256_by_qualified={qualified: signature_sha},
        )
        self.assertEqual(errors, [])
        self.assertEqual(counts["conditioning_information_context_count"], 1)
        self.assertEqual(counts["conditioning_information_requirement_count"], 1)
        result = items[0]
        assert isinstance(result, dict)
        return next(
            dimension
            for dimension in result["dimensions"]
            if dimension["id"] == "conditioning_information"
        )

    def direct_response(self, dimension: dict[str, object]) -> dict[str, object]:
        requirement = dimension["conditioning_information"]
        assert isinstance(requirement, dict)
        contract = requirement["contracts"][0]
        assert isinstance(contract, dict)
        source_contract = contract["conditioning_information_contract"]
        assert isinstance(source_contract, dict)
        source_digest = contract["source_semantic_sha256"]
        assert isinstance(source_digest, str)
        source_value_kind = source_contract["conditional_value_kind"]
        assert isinstance(source_value_kind, str)
        source_law_population = source_contract["source_law_population"]
        assert isinstance(source_law_population, str)
        source_scopes = source_contract["conditionalization_scopes"]
        assert isinstance(source_scopes, list)
        component_ids = [
            entry["id"] for entry in source_contract["source_observed_components"]
        ]
        stage_ids = [
            entry["id"]
            for entry in source_contract["source_action_selection_stages"]
        ]
        pin = dimension["conditioning_information_association"][
            "semantic_association_sha256"
        ]
        assert isinstance(pin, str)
        return {
            "verdict": "matches_source_model",
            "source_locator": "source.txt:1",
            "semantic_comparison": (
                "The source and Lean routes use the same selected observation "
                "information and conditional-law scope."
            ),
            "lean_evidence": (
                "The expanded Lean observation map retains access, both actions, and "
                "the reporting-branch score before conditional evaluation."
            ),
            "conditioning_information_analysis": {
                "semantic_association_sha256": pin,
                "verdict": "source_and_lean_conditioning_information_match",
                "contracts": [
                    {
                        "source_semantic_sha256": source_digest,
                        "source_conditional_value_kind": source_value_kind,
                        "lean_conditional_value_kind": source_value_kind,
                        "source_observed_component_ids": component_ids,
                        "lean_observed_components": [
                            {
                                "source_component_id": component_id,
                                "description": (
                                    "The expanded Lean observed map preserves source "
                                    f"component `{component_id}`."
                                ),
                            }
                            for component_id in component_ids
                        ],
                        "source_action_selection_stage_ids": stage_ids,
                        "lean_action_selection_stages": [
                            {
                                "source_stage_id": stage_id,
                                "description": (
                                    "The expanded Lean selected event retains source "
                                    f"stage `{stage_id}` in the same order."
                                ),
                            }
                            for stage_id in stage_ids
                        ],
                        "source_law_population": source_law_population,
                        "lean_law_population": source_law_population,
                        "source_conditionalization_scopes": source_scopes,
                        "lean_conditionalization_scopes": source_scopes,
                        "comparison_evidence": (
                            "The checked bridge identifies the same selected population "
                            "and retains the RCD only almost everywhere under the same "
                            "observation marginal."
                        ),
                    }
                ],
                "lean_bridge_evidence": (
                    "A checked source-to-Lean bridge transports the selected joint law "
                    "to the enumerated observation map without dropping either action."
                ),
            },
        }

    def test_context_schema_requires_complete_source_information(self) -> None:
        context = self.context()
        self.assertEqual(
            evidence.conditioning_information_context_contract_errors(context), []
        )
        missing = deepcopy(context)
        contract = missing["conditioning_information_contract"]
        assert isinstance(contract, dict)
        del contract["source_observed_components"]
        errors = evidence.conditioning_information_context_contract_errors(missing)
        self.assertTrue(any("source_observed_components" in error for error in errors))

        payload = self.source_map(context)
        with tempfile.TemporaryDirectory() as tmpdir:
            paper = Path(tmpdir) / "Fixture"
            paper.mkdir()
            (paper / "source.txt").write_text(
                self.source_quote + "\n", encoding="utf-8"
            )
            audit_dir = paper / "audit"
            audit_dir.mkdir()
            map_path = audit_dir / "paper_statement_map.json"
            map_path.write_text(json.dumps(payload), encoding="utf-8")
            findings = evidence.semantic_context_requirement_findings(
                paper, "partially formalized", map_path, payload
            )
        self.assertEqual(findings, [])

    def test_non_opt_in_source_map_gets_no_conditioning_requirement(self) -> None:
        source_map = {
            "items": {
                "ordinary_source_route": {
                    "claim_bearing": True,
                    "source_kind": "proposition",
                    "source_location": "source.txt:1",
                }
            }
        }
        self.assertFalse(AUDIT.source_map_uses_conditioning_information_context(source_map))
        item: dict[str, object] = {
            "row": "opaque_unrelated_row",
            "qualified_declaration": "Fixture.Interface.opaque_endpoint",
            "dimensions": [],
        }
        items, errors, counts = AUDIT.attach_conditioning_information_requirements(
            [item],
            paper_statement_map=source_map,
            elaborated_signature_sha256_by_qualified={},
        )
        self.assertEqual(errors, [])
        self.assertEqual(counts["conditioning_information_context_count"], 0)
        self.assertEqual(counts["conditioning_information_requirement_count"], 0)
        self.assertEqual(items, [item])
        self.assertEqual(item["dimensions"], [])

    def test_trivial_sigma_algebra_allows_an_explicit_empty_observation_map(
        self,
    ) -> None:
        context = self.context()
        contract = context["conditioning_information_contract"]
        assert isinstance(contract, dict)
        contract["conditional_value_kind"] = "conditional_expectation"
        contract["source_observed_components"] = []
        contract["source_action_selection_stages"] = []
        contract["source_law_population"] = "raw_unselected_source_law"
        contract["conditionalization_scopes"] = ["positive_measurable_event"]
        self.assertEqual(
            evidence.conditioning_information_context_contract_errors(context), []
        )

        dimension = self.generated_dimension(context)
        response = self.direct_response(dimension)
        contract_response = response["conditioning_information_analysis"][
            "contracts"
        ][0]
        self.assertEqual(contract_response["lean_observed_components"], [])
        self.assertEqual(
            projection.conditioning_information_analysis_errors(dimension, response), []
        )

        invented_component = deepcopy(response)
        invented_component["conditioning_information_analysis"]["contracts"][0][
            "lean_observed_components"
        ] = [
            {
                "source_component_id": "invented_observation",
                "description": "An observation not present in the source contract.",
            }
        ]
        errors = projection.conditioning_information_analysis_errors(
            dimension, invented_component
        )
        self.assertTrue(
            any("omits or adds a source observed component" in error for error in errors),
            errors,
        )

    def test_direct_match_rejects_missing_component_or_action_stage(self) -> None:
        dimension = self.generated_dimension()
        response = self.direct_response(dimension)
        self.assertEqual(
            projection.conditioning_information_analysis_errors(dimension, response), []
        )
        semantic_item = {"dimensions": [dimension]}
        semantic_judgment = {
            "classification": "semantic_model_review",
            "semantic_model_dimensions": {"conditioning_information": response},
        }
        self.assertTrue(
            evidence.semantic_model_judgment_is_complete(
                semantic_item, semantic_judgment
            )
        )

        missing_component = deepcopy(response)
        component_entries = missing_component["conditioning_information_analysis"][
            "contracts"
        ][0]["lean_observed_components"]
        assert isinstance(component_entries, list)
        component_entries.pop()
        component_errors = projection.conditioning_information_analysis_errors(
            dimension, missing_component
        )
        self.assertTrue(
            any("omits or adds a source observed component" in error for error in component_errors),
            component_errors,
        )
        missing_component_judgment = deepcopy(semantic_judgment)
        missing_component_judgment["semantic_model_dimensions"][
            "conditioning_information"
        ] = missing_component
        self.assertFalse(
            evidence.semantic_model_judgment_is_complete(
                semantic_item, missing_component_judgment
            )
        )

        missing_stage = deepcopy(response)
        stage_entries = missing_stage["conditioning_information_analysis"][
            "contracts"
        ][0]["lean_action_selection_stages"]
        assert isinstance(stage_entries, list)
        stage_entries.pop()
        stage_errors = projection.conditioning_information_analysis_errors(
            dimension, missing_stage
        )
        self.assertTrue(
            any(
                "omits, adds, or reorders a source action-selection stage" in error
                for error in stage_errors
            ),
            stage_errors,
        )

        raw_law = deepcopy(response)
        raw_law["conditioning_information_analysis"]["contracts"][0][
            "lean_law_population"
        ] = "raw_unselected_source_law"
        raw_law_errors = projection.conditioning_information_analysis_errors(
            dimension, raw_law
        )
        self.assertTrue(
            any("raw-vs-selected law population differs" in error for error in raw_law_errors),
            raw_law_errors,
        )

        pointwise_scope = deepcopy(response)
        pointwise_scope["conditioning_information_analysis"]["contracts"][0][
            "lean_conditionalization_scopes"
        ] = ["pointwise_totalized_observation"]
        pointwise_scope_errors = projection.conditioning_information_analysis_errors(
            dimension, pointwise_scope
        )
        self.assertTrue(
            any(
                "a.e./pointwise conditionalization scope differs" in error
                for error in pointwise_scope_errors
            ),
            pointwise_scope_errors,
        )

        wrong_value_kind = deepcopy(response)
        wrong_value_kind["conditioning_information_analysis"]["contracts"][0][
            "lean_conditional_value_kind"
        ] = "conditional_law"
        wrong_value_kind_errors = projection.conditioning_information_analysis_errors(
            dimension, wrong_value_kind
        )
        self.assertTrue(
            any(
                "conditional-value kind differs from the source" in error
                for error in wrong_value_kind_errors
            ),
            wrong_value_kind_errors,
        )
        wrong_value_kind_judgment = deepcopy(semantic_judgment)
        wrong_value_kind_judgment["semantic_model_dimensions"][
            "conditioning_information"
        ] = wrong_value_kind
        self.assertFalse(
            evidence.semantic_model_judgment_is_complete(
                semantic_item, wrong_value_kind_judgment
            )
        )


if __name__ == "__main__":
    unittest.main()
