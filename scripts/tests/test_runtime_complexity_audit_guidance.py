#!/usr/bin/env python3
"""Regression tests for operational complexity-audit guidance."""

from __future__ import annotations

import importlib.util
import json
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "new_paper_runtime_guidance", ROOT / "scripts" / "new_paper.py"
)
assert SPEC is not None and SPEC.loader is not None
NEW_PAPER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = NEW_PAPER
SPEC.loader.exec_module(NEW_PAPER)


class RuntimeComplexityAuditGuidanceTests(unittest.TestCase):
    def test_generated_audit_prompts_require_operational_evidence(self) -> None:
        for payload_text in (
            NEW_PAPER.statement_match_llm_text("EX00Example"),
            NEW_PAPER.source_record_match_llm_text("EX00Example"),
        ):
            prompt = " ".join(json.loads(payload_text)["prompt_summary"])
            self.assertIn("transitive semantic operational dependency graph", prompt)
            self.assertIn("every reachable branch", prompt)
            self.assertIn("old semantic closure or oracle", prompt)
            self.assertIn("names", prompt.lower())
            self.assertIn("duplicates", prompt)
            self.assertIn("materialization", prompt)
            self.assertIn("representation/container primitives", prompt)
            self.assertIn("exact-rational bit growth", prompt)
            self.assertIn("worst-case recurrence", prompt)
            self.assertIn("missing or excluded_by_claim", prompt.lower())
            self.assertIn("SHA-256", prompt)
            self.assertIn("generated IR/C", prompt)
            self.assertIn("cost-threaded executor", prompt)

    def test_statement_scaffold_has_independently_versioned_runtime_schema(self) -> None:
        payload = json.loads(NEW_PAPER.statement_match_llm_text("EX00Example"))
        self.assertEqual(
            payload["prompt_version"],
            "statement-match-v10-semantic-fidelity-seat-stopping",
        )
        schema = payload["operational_complexity_review_schema"]
        self.assertEqual(
            schema["version"],
            NEW_PAPER.OPERATIONAL_COMPLEXITY_REVIEW_VERSION,
        )
        self.assertIn("judgment=matches", schema["required_when"])
        self.assertIn("polynomial_time", schema["required_when"])
        self.assertIn("dependency_graph", schema["required"])
        self.assertIn("worst_case_recurrence", schema["required"])
        self.assertIn("worst_case_bound", schema["required"])
        self.assertIn(
            "all_reachable_branches_complete",
            schema["dependency_graph_required"],
        )
        self.assertEqual(
            set(schema["work_accounting_required_categories"]),
            {
                "traversal_enumeration_length",
                "duplicate_multiplicity",
                "materialization_rebuilding",
                "representation_container_primitives",
                "exact_rational_bit_growth",
            },
        )
        self.assertNotIn("missing", schema["full_runtime_match_status_values"])
        self.assertNotIn(
            "excluded_by_claim", schema["full_runtime_match_status_values"]
        )
        self.assertIn(
            "symbol_names_used_as_evidence",
            schema["material_closure_elimination_required"],
        )
        self.assertIn("dependency node", schema["charged_category_rule"])

    def test_generated_plan_records_runtime_evidence_and_exclusions(self) -> None:
        plan = NEW_PAPER.formalization_plan_text("Example", "EX00Example")
        self.assertIn("Algorithmic complexity audit, when applicable", plan)
        self.assertIn("Transitive operational dependency graph", plan)
        self.assertIn("every reachable branch", plan)
        self.assertIn("old semantic closure/oracle dependencies", plan)
        self.assertIn("Worst-case recurrence and bound", plan)
        self.assertIn("duplicates, and materialization/rebuild charges", plan)
        self.assertIn("missing/excluded work withholds a runtime match", plan)
        self.assertIn("artifact/source hashes and semantic binding", plan)
        self.assertIn("refinement alone is not cost evidence", plan)

    def test_skill_and_workflow_reject_name_based_runtime_evidence(self) -> None:
        skill = (ROOT / "skills" / "econcs-formalizer" / "SKILL.md").read_text(
            encoding="utf-8"
        )
        workflow = (ROOT / "docs" / "AGENT_FORMALIZATION_WORKFLOW.md").read_text(
            encoding="utf-8"
        )
        for raw_guidance in (skill, workflow):
            guidance = " ".join(raw_guidance.split())
            self.assertIn("transitive semantic operational", guidance)
            self.assertIn("every branch reachable", guidance)
            self.assertIn("old semantic closure or oracle", guidance)
            self.assertIn("function and declaration names", guidance)
            self.assertIn("generated IR/C", guidance)
            self.assertIn("pinned by source and artifact digests", guidance)
            self.assertIn("cost-threaded executor", guidance)

    def test_skills_and_workflow_cover_semantic_fidelity_hazards(self) -> None:
        paths = (
            ROOT / "skills" / "econcs-formalizer" / "SKILL.md",
            ROOT / "skills" / "econcs-prover" / "SKILL.md",
            ROOT / "docs" / "AGENT_FORMALIZATION_WORKFLOW.md",
        )
        for path in paths:
            guidance = " ".join(path.read_text(encoding="utf-8").split()).lower()
            self.assertIn("terminal", guidance, path)
            self.assertIn("nonvacu", guidance, path)
            self.assertIn("coherent", guidance, path)
            self.assertIn("nonempty", guidance, path)
            self.assertIn("surject", guidance, path)

        # The formalizer workflow owns cross-domain execution auditing.  The
        # prover skill remains focused on establishing individual obligations.
        for path in (paths[0], paths[2]):
            guidance = " ".join(path.read_text(encoding="utf-8").split()).lower()
            guidance = guidance.replace("-", " ")
            self.assertIn("input domain", guidance, path)
            self.assertIn("state transition", guidance, path)
            self.assertIn("termination", guidance, path)
            self.assertIn("numeric representation", guidance, path)
            self.assertIn("global bridge", guidance, path)

            # Names are routing only in the workflow that compares source and
            # Lean semantics; they are not a proof-level requirement.
            self.assertIn("names", guidance, path)
            self.assertIn("routing", guidance, path)


if __name__ == "__main__":
    unittest.main()
