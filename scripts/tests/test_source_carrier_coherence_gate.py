#!/usr/bin/env python3
"""Regression tests for source-carrier coherence in joint-law reviews."""

from __future__ import annotations

import sys
import unittest
from copy import deepcopy
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    value = str(import_root)
    if value not in sys.path:
        sys.path.insert(0, value)

import audit_evidence_integrity as integrity  # noqa: E402
import audit_repository as repository  # noqa: E402
from source_record_projection_contract import (  # noqa: E402
    source_carrier_coherence_analysis_errors,
    semantic_model_subanalysis_errors,
)


class SourceCarrierCoherenceGateTests(unittest.TestCase):
    def raw_dimension(self) -> dict[str, object]:
        return {
            "id": "joint_law_and_state_evolution",
            "detected_from_expanded_surface": True,
            "requires_source_carrier_coherence_analysis_when_detected": True,
        }

    def analysis(self) -> dict[str, object]:
        return {
            "verdict": "source_carrier_pushforward_checked",
            "source_random_variable_carrier": (
                "One shared source carrier Omega supplies the endpoint random "
                "variable and every displayed clock coordinate."
            ),
            "lean_random_variable_carrier": (
                "The Lean carrier uses the same joint source outcome before the "
                "observation projection."
            ),
            "stage_identity_or_resampling_evidence": (
                "Each stage is a conditional coordinate of the same joint draw; "
                "no source endpoint is resampled."
            ),
            "joint_law_bridge_evidence": (
                "A checked theorem proves the joint-law pushforward equality from "
                "the source carrier to the Lean observation carrier."
            ),
            "measure_construction": "single_source_carrier_pushforward",
            "measure_transport_evidence": (
                "The checked pushforward maps the source measure through the "
                "observation map; it is not merely a likelihood weight."
            ),
            "source_rate_scope": "rate_free_claim",
            "lean_rate_scope": "rate_indexed_family",
            "rate_family_evidence": (
                "For every rate r, a checked indexed family bridge maps the same "
                "source model P_r to the Lean law."
            ),
        }

    def response(self) -> dict[str, object]:
        return {
            "verdict": "matches_source_model",
            "source_locator": "source.txt:12-24",
            "semantic_comparison": (
                "The source and Lean models are compared on the same joint carrier."
            ),
            "lean_evidence": (
                "The expanded measure/kernel carrier and its observation map are "
                "reviewed structurally."
            ),
            "lean_bridge": "A checked joint-law theorem connects the source carrier.",
            "source_carrier_coherence_analysis": self.analysis(),
        }

    def test_missing_analysis_fails_closed(self) -> None:
        response = self.response()
        del response["source_carrier_coherence_analysis"]

        errors = source_carrier_coherence_analysis_errors(
            self.raw_dimension(), response
        )

        self.assertEqual(
            errors,
            ["needs `source_carrier_coherence_analysis` object"],
        )

    def test_untriggered_dimension_preserves_existing_schema_two_behavior(self) -> None:
        response = self.response()
        del response["source_carrier_coherence_analysis"]
        raw_dimension = self.raw_dimension()
        del raw_dimension["requires_source_carrier_coherence_analysis_when_detected"]

        self.assertEqual(
            source_carrier_coherence_analysis_errors(raw_dimension, response),
            [],
        )

    def test_weighted_measure_cannot_be_labeled_source_pushforward(self) -> None:
        response = self.response()
        analysis = response["source_carrier_coherence_analysis"]
        assert isinstance(analysis, dict)
        analysis["measure_construction"] = "weighted_or_tilted_measure"
        analysis["measure_transport_evidence"] = (
            "This weighted likelihood measure is generated for the proof and is "
            "not a source pushforward."
        )

        errors = source_carrier_coherence_analysis_errors(
            self.raw_dimension(), response
        )

        self.assertTrue(
            any("generated or weighted measure" in error for error in errors), errors
        )
        self.assertTrue(
            any("claims a source pushforward" in error for error in errors), errors
        )

    def test_rate_free_claim_rejects_fixed_rate_witness(self) -> None:
        response = self.response()
        analysis = response["source_carrier_coherence_analysis"]
        assert isinstance(analysis, dict)
        analysis["lean_rate_scope"] = "fixed_rate_instance"
        analysis["rate_family_evidence"] = (
            "The proof chooses one positive rate and checks that selected instance."
        )

        errors = source_carrier_coherence_analysis_errors(
            self.raw_dimension(), response
        )

        self.assertTrue(
            any("must be `rate_indexed_family`" in error for error in errors), errors
        )
        self.assertTrue(
            any("all-rate indexed family bridge" in error for error in errors), errors
        )

    def test_name_only_carrier_or_bridge_evidence_is_rejected(self) -> None:
        response = self.response()
        analysis = response["source_carrier_coherence_analysis"]
        assert isinstance(analysis, dict)
        analysis["joint_law_bridge_evidence"] = "Fixture.sourceLawBridge"

        errors = source_carrier_coherence_analysis_errors(
            self.raw_dimension(), response
        )

        self.assertTrue(any("name-only evidence" in error for error in errors), errors)

    def test_full_repository_gate_reports_missing_analysis(self) -> None:
        response = self.response()
        del response["source_carrier_coherence_analysis"]
        key = "semantic-model::fixture"
        findings = repository.semantic_model_review_findings(
            "Fixture",
            Path("papers/Fixture"),
            Path("papers/Fixture/audit/source_record_match_llm.json"),
            [
                {
                    "judgment_key": key,
                    "row": "fixture",
                    "dimensions": [self.raw_dimension()],
                }
            ],
            {
                key: {
                    "classification": "semantic_model_review",
                    "source_record_audit_sha256": "audit-digest",
                    "source_record_item_sha256": "item-digest",
                    "semantic_model_dimensions": {
                        "joint_law_and_state_evolution": response
                    },
                }
            },
            digest="audit-digest",
            expected_item_digests={key: "item-digest"},
            severity="ERROR",
        )

        self.assertTrue(
            any(
                "needs `source_carrier_coherence_analysis` object" in finding.message
                for finding in findings
            ),
            [finding.message for finding in findings],
        )

    def test_complete_analysis_passes_full_and_fast_gates(self) -> None:
        response = self.response()
        raw_dimension = self.raw_dimension()

        self.assertEqual(
            semantic_model_subanalysis_errors(raw_dimension, response),
            [],
        )
        self.assertTrue(
            integrity.semantic_model_judgment_is_complete(
                {"dimensions": [raw_dimension]},
                {
                    "classification": "semantic_model_review",
                    "semantic_model_dimensions": {
                        "joint_law_and_state_evolution": deepcopy(response)
                    },
                },
            )
        )


if __name__ == "__main__":
    unittest.main()
