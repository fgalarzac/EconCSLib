#!/usr/bin/env python3
"""Regression tests for literal source-core / checked-strengthening map splits."""

from __future__ import annotations

from copy import deepcopy
import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
GATE_PATH = ROOT / "scripts" / "audit_evidence_integrity.py"
SPEC = importlib.util.spec_from_file_location(
    "audit_evidence_integrity_source_core_test", GATE_PATH
)
assert SPEC is not None and SPEC.loader is not None
GATE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GATE
SPEC.loader.exec_module(GATE)

SOURCE_MAP_PATH = ROOT / "papers" / "KR21Monoculture" / "audit" / "paper_statement_map.json"
SOURCE_ITEM_KEY = "kr21_lemma2_bottom_probability"


class SourceCoreProjectionValidationTests(unittest.TestCase):
    def source_item(self) -> dict[str, object]:
        payload = json.loads(SOURCE_MAP_PATH.read_text(encoding="utf-8"))
        return deepcopy(payload["items"][SOURCE_ITEM_KEY])

    def test_current_appendix_b_source_core_split_is_well_formed(self) -> None:
        self.assertEqual(
            GATE.source_core_projection_validation_errors(self.source_item()), []
        )

    def test_core_must_bind_exactly_to_the_semantic_contract(self) -> None:
        item = self.source_item()
        projection = item["source_core_projection"]
        assert isinstance(projection, dict)
        projection["classification"] = "name_looks_like_source_core"
        projection["direct_declaration"] = "Arbitrary.Namespace.otherEndpoint"

        errors = GATE.source_core_projection_validation_errors(item)

        self.assertTrue(
            any("classification must be `literal_source_core`" in error for error in errors),
            errors,
        )
        self.assertTrue(
            any("must equal semantic_contract.evidence_declaration" in error for error in errors),
            errors,
        )

    def test_core_direct_and_spec_must_be_qualified_identities(self) -> None:
        item = self.source_item()
        projection = item["source_core_projection"]
        assert isinstance(projection, dict)
        projection["direct_declaration"] = "bareCore"
        projection["spec_declaration"] = "bareCoreSpec"

        errors = GATE.source_core_projection_validation_errors(item)

        self.assertTrue(
            any("direct_declaration must be a nonempty fully-qualified" in error for error in errors),
            errors,
        )
        self.assertTrue(
            any("spec_declaration must be a nonempty fully-qualified" in error for error in errors),
            errors,
        )

    def test_core_direct_is_the_exact_sole_primary_declaration(self) -> None:
        item = self.source_item()
        item["lean_declarations"] = [
            "appendixB_smoothing_source_core",
            "appendixB_smoothing_source_complete",
        ]

        errors = GATE.source_core_projection_validation_errors(item)

        self.assertTrue(
            any("sole lean_declarations entry" in error for error in errors), errors
        )

    def test_source_core_split_requires_a_nonempty_strengthening_list(self) -> None:
        item = self.source_item()
        item["checked_strengthening_declarations"] = []

        errors = GATE.source_core_projection_validation_errors(item)

        self.assertTrue(
            any("must be a nonempty list of objects" in error for error in errors),
            errors,
        )

    def test_strengthening_identities_must_be_fully_qualified(self) -> None:
        item = self.source_item()
        strengthenings = item["checked_strengthening_declarations"]
        assert isinstance(strengthenings, list) and strengthenings
        strengthening = strengthenings[0]
        assert isinstance(strengthening, dict)
        strengthening["declaration"] = "strongerEndpoint"
        strengthening["spec_declaration"] = "strongerEndpointSpec"

        errors = GATE.source_core_projection_validation_errors(item)

        self.assertTrue(
            any(
                "declaration must be a nonempty fully-qualified declaration" in error
                for error in errors
            ),
            errors,
        )
        self.assertTrue(
            any(
                "spec_declaration must be a nonempty fully-qualified declaration" in error
                for error in errors
            ),
            errors,
        )

    def test_strengthenings_cannot_replace_or_leak_into_source_core_coverage(self) -> None:
        item = self.source_item()
        projection = item["source_core_projection"]
        assert isinstance(projection, dict)
        strengthenings = item["checked_strengthening_declarations"]
        assert isinstance(strengthenings, list) and strengthenings
        strengthening = strengthenings[0]
        assert isinstance(strengthening, dict)
        strengthening["classification"] = "source_core_by_name"
        strengthening["declaration"] = projection["direct_declaration"]
        strengthening["spec_declaration"] = projection["spec_declaration"]
        strengthening["description"] = ""
        item["support_lean_declarations"] = []
        item["lean_declarations"] = ["appendixB_smoothing_source_core"]

        errors = GATE.source_core_projection_validation_errors(item)

        self.assertTrue(
            any("checked_strengthening_not_literal_source_coverage" in error for error in errors),
            errors,
        )
        self.assertTrue(
            any("must differ from both source-core" in error for error in errors), errors
        )
        self.assertTrue(
            any("description must be a nonempty string" in error for error in errors), errors
        )
        self.assertTrue(
            any("must occur in support_lean_declarations" in error for error in errors),
            errors,
        )

    def test_inventory_lane_enforces_the_optional_split_when_present(self) -> None:
        item = self.source_item()
        strengthenings = item["checked_strengthening_declarations"]
        assert isinstance(strengthenings, list) and strengthenings
        strengthening = strengthenings[0]
        assert isinstance(strengthening, dict)
        strengthening["declaration"] = "Other.Namespace.strongerEndpoint"
        item["support_lean_declarations"] = ["differentSupportEndpoint"]

        with tempfile.TemporaryDirectory() as temporary:
            paper = Path(temporary) / "FixturePaper"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            (audit / "source_proof_fidelity.json").write_text(
                json.dumps({"defects": []}), encoding="utf-8"
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "semantic_contract_schema": 1,
                        "source_coverage_mode": "named_theoretical_statements",
                        "items": {"opaque_source_key": item},
                    }
                ),
                encoding="utf-8",
            )

            findings = GATE.semantic_contract_inventory_findings(paper, "formalized")

        self.assertTrue(
            any("must occur in support_lean_declarations" in finding.message for finding in findings),
            [finding.message for finding in findings],
        )


if __name__ == "__main__":
    unittest.main()
