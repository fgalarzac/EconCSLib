#!/usr/bin/env python3
"""Regressions for source-model stochastic-process construction obligations."""

from __future__ import annotations

import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
for path in (ROOT, ROOT / "scripts"):
    if str(path) not in sys.path:
        sys.path.insert(0, str(path))

import audit_evidence_integrity as EVIDENCE


REPOSITORY_PATH = ROOT / "scripts" / "audit_repository.py"
REPOSITORY_SPEC = importlib.util.spec_from_file_location(
    "source_model_process_repository", REPOSITORY_PATH
)
assert REPOSITORY_SPEC is not None and REPOSITORY_SPEC.loader is not None
REPOSITORY = importlib.util.module_from_spec(REPOSITORY_SPEC)
sys.modules[REPOSITORY_SPEC.name] = REPOSITORY
REPOSITORY_SPEC.loader.exec_module(REPOSITORY)


def derived_process_item(*, renamed: bool = False) -> dict[str, object]:
    record = "Other.Namespace.Payload" if renamed else "Fixture.CycleRecord"
    sequence = "otherSequence" if renamed else "cycleValue"
    return {
        "judgment_key": "semantic-model::fixture",
        "row": "renamed_row" if renamed else "fixture_row",
        "expanded_lean_surface": {
            "record_roots": [record],
            "record_field_types": [
                {
                    "expanded_type": (
                        "forall n, ProbabilityTheory.IdentDistrib "
                        f"({sequence} n) ({sequence} 0) P P"
                    )
                },
                {
                    "expanded_type": (
                        f"Pairwise ((. \u27c2\u1d62[P] .) on {sequence})"
                    )
                },
                {"expanded_type": f"Integrable ({sequence} 0) P"},
            ],
        },
        "dimensions": [
            {
                "id": "joint_law_and_state_evolution",
                "detected_from_expanded_surface": True,
                "requires_checked_bridge_when_detected": True,
            }
        ],
    }


def ordinary_measure_item() -> dict[str, object]:
    return {
        "judgment_key": "semantic-model::ordinary",
        "row": "ordinary_row",
        "expanded_lean_surface": {
            "record_roots": ["Fixture.MeasureData"],
            "record_field_types": [
                {"expanded_type": "Measure TripLength"},
                {"expanded_type": "Integrable payoff mu"},
            ],
        },
        "dimensions": [
            {
                "id": "joint_law_and_state_evolution",
                "detected_from_expanded_surface": True,
                "requires_checked_bridge_when_detected": True,
            }
        ],
    }


def unrelated_stochastic_facts_item() -> dict[str, object]:
    """A record with all fact kinds, but no one derived process package."""

    return {
        "judgment_key": "semantic-model::unrelated",
        "row": "unrelated_row",
        "expanded_lean_surface": {
            "record_roots": ["Fixture.MixedFacts"],
            "record_field_types": [
                {
                    "expanded_type": (
                        "forall n, ProbabilityTheory.IdentDistrib first n first 0 P P"
                    )
                },
                {
                    "expanded_type": "Pairwise ((. ⟂ᵢ[P] .) on second)",
                },
                {"expanded_type": "Integrable (third 0) P"},
            ],
        },
    }


def endpoint_calculus_item(*, renamed: bool = False) -> dict[str, object]:
    reward = "otherReward" if renamed else "reward"
    response = "otherResponse" if renamed else "response"
    context = "otherSet" if renamed else "context"
    return {
        "judgment_key": "semantic-model::endpoint",
        "row": "endpoint_row",
        "expanded_lean_surface": {
            "record_roots": ["Fixture.EndpointData"],
            "record_field_types": [
                {
                    "expanded_type": (
                        f"∀ ({context} : (Set (ℝ))) (lower upper : ℝ), "
                        "0 ≤ lower → lower < upper → ∃ derivativeValue : ℝ, "
                        f"HasDerivAt (fun x => {reward} ({context} ∪ Set.Ioo lower x)) "
                        f"derivativeValue upper ∧ (0 < derivativeValue ↔ 0 < {response} "
                        f"({context} ∪ Set.Ioo lower upper) upper)"
                    )
                }
            ],
        },
        "dimensions": [
            {
                "id": "joint_law_and_state_evolution",
                "detected_from_expanded_surface": True,
                "requires_checked_bridge_when_detected": True,
            }
        ],
    }


def ordinary_derivative_item() -> dict[str, object]:
    return {
        "judgment_key": "semantic-model::ordinary-derivative",
        "row": "ordinary_derivative_row",
        "expanded_lean_surface": {
            "record_roots": ["Fixture.CalculusData"],
            "record_field_types": [
                {
                    "expanded_type": "HasDerivAt (fun x : ℝ => x * x) 2 1",
                }
            ],
        },
    }


def judgment() -> dict[str, object]:
    return {
        "classification": "semantic_model_review",
        "source_record_audit_sha256": "audit-digest",
        "source_record_item_sha256": "item-digest",
        "semantic_model_dimensions": {
            "joint_law_and_state_evolution": {
                "verdict": "matches_source_model",
                "source_locator": "source.txt:10-20",
                "semantic_comparison": "The source process is compared with the Lean law.",
                "lean_evidence": "The expanded record surface is inspected.",
                "lean_bridge": "A descriptive bridge sentence that is not a constructor.",
            }
        },
    }


class SourceModelProcessObligationTests(unittest.TestCase):
    def test_iid_independence_and_moment_record_is_name_invariant(self) -> None:
        original = derived_process_item()
        renamed = derived_process_item(renamed=True)

        self.assertTrue(EVIDENCE.caller_supplied_derived_process_basis(original))
        self.assertEqual(
            EVIDENCE.caller_supplied_derived_process_basis(original),
            EVIDENCE.caller_supplied_derived_process_basis(renamed),
        )

    def test_ordinary_measure_data_is_not_a_process_construction_obligation(self) -> None:
        self.assertEqual(
            EVIDENCE.caller_supplied_derived_process_basis(ordinary_measure_item()),
            [],
        )

    def test_unrelated_stochastic_facts_are_not_misclassified_as_one_process(self) -> None:
        self.assertEqual(
            EVIDENCE.caller_supplied_derived_process_basis(
                unrelated_stochastic_facts_item()
            ),
            [],
        )

    def test_unscoped_endpoint_calculus_is_name_invariant(self) -> None:
        original = endpoint_calculus_item()
        renamed = endpoint_calculus_item(renamed=True)

        self.assertTrue(
            EVIDENCE.caller_supplied_model_construction_basis(original)
        )
        self.assertEqual(
            EVIDENCE.caller_supplied_model_construction_basis(original),
            EVIDENCE.caller_supplied_model_construction_basis(renamed),
        )

    def test_ordinary_derivative_is_not_an_unscoped_endpoint_package(self) -> None:
        self.assertEqual(
            EVIDENCE.caller_supplied_model_construction_basis(
                ordinary_derivative_item()
            ),
            [],
        )

    def test_process_pattern_is_not_a_completeness_verdict(self) -> None:
        """IID/endpoint detection is diagnostic, not a pass or fail shortcut."""

        self.assertEqual(
            EVIDENCE.semantic_model_judgment_is_complete(
                derived_process_item(), judgment()
            ),
            EVIDENCE.semantic_model_judgment_is_complete(
                ordinary_measure_item(), judgment()
            ),
        )

    def test_repository_keeps_cycle_pattern_diagnostic_only(self) -> None:
        item = derived_process_item()
        findings = REPOSITORY.semantic_model_review_findings(
            "Fixture",
            Path("papers/Fixture"),
            Path("papers/Fixture/audit/source_record_match_llm.json"),
            [item],
            {"semantic-model::fixture": judgment()},
            digest="audit-digest",
            expected_item_digests={"semantic-model::fixture": "item-digest"},
            severity="ERROR",
        )
        messages = [finding.message for finding in findings]

        self.assertFalse(
            any("caller-supplied derived model-construction record" in message for message in messages),
            messages,
        )

    def test_repository_keeps_endpoint_pattern_diagnostic_only(self) -> None:
        item = endpoint_calculus_item()
        findings = REPOSITORY.semantic_model_review_findings(
            "Fixture",
            Path("papers/Fixture"),
            Path("papers/Fixture/audit/source_record_match_llm.json"),
            [item],
            {"semantic-model::endpoint": judgment()},
            digest="audit-digest",
            expected_item_digests={"semantic-model::endpoint": "item-digest"},
            severity="ERROR",
        )
        messages = [finding.message for finding in findings]

        self.assertFalse(
            any("endpoint calculus" in message for message in messages),
            messages,
        )


if __name__ == "__main__":
    unittest.main()
