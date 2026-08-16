#!/usr/bin/env python3
"""Regression tests for source-pinned model derivation obligations."""

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
    "econcs_source_model_derivation_source_record_audit", HELPER
)
assert SPEC is not None and SPEC.loader is not None
AUDIT = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = AUDIT
SPEC.loader.exec_module(AUDIT)


class SourceModelDerivationContractTests(unittest.TestCase):
    source_lines = (
        "Arrival gaps follow the stated arrival-gap law.",
        "Accepted arrivals use the stated deterministic acceptance rule.",
        "The accepted-cycle stochastic law follows from the arrival-gap and acceptance primitives.",
    )
    source_quote = "\n".join(source_lines)

    def source_anchor(self, line_start: int, line_end: int | None = None) -> dict[str, object]:
        end = line_start if line_end is None else line_end
        quote = "\n".join(self.source_lines[line_start - 1 : end])
        return {
            "path": "source.txt",
            "line_start": line_start,
            "line_end": end,
            "quoted_text": quote,
            "quoted_text_sha256": hashlib.sha256(quote.encode("utf-8")).hexdigest(),
        }

    def context(self) -> dict[str, object]:
        return {
            "kind": "source_model_derivation",
            "source_location": "source.txt:1-3",
            "explanation": (
                "The source gives arrival and acceptance primitives; the accepted-cycle "
                "law is a consequence rather than an independent model assumption."
            ),
            "source_anchor_evidence": [self.source_anchor(1, 3)],
            "source_model_derivation_contract": {
                "schema": 2,
                "source_primitive_components": [
                    {
                        "id": "arrival_gap_law",
                        "description": "The source law for successive arrival gaps.",
                        "source_location": "source.txt:1",
                        "source_anchor_evidence": [self.source_anchor(1)],
                    },
                    {
                        "id": "acceptance_rule",
                        "description": "The source rule selecting accepted arrivals.",
                        "source_location": "source.txt:2",
                        "source_anchor_evidence": [self.source_anchor(2)],
                    },
                ],
                "derived_conclusion": {
                    "description": (
                        "The source accepted-cycle stochastic law produced by the arrival "
                        "and acceptance primitives."
                    ),
                    "source_location": "source.txt:3",
                    "source_anchor_evidence": [self.source_anchor(3)],
                },
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
                # The source storage key and Lean declaration are intentionally
                # semantically unhelpful: the context, not spelling, creates
                # the derivation obligation.
                "neutral_source_route": {
                    "claim_bearing": True,
                    "source_kind": "proposition",
                    "source_location": "source.txt:1",
                    "semantic_context_requirements": [context],
                }
            },
        }

    def generated_dimension(
        self,
        *,
        renamed: bool = False,
        caller_supplied_process: bool = False,
    ) -> dict[str, object]:
        source_map = self.source_map(self.context())
        source_item = source_map["items"]["neutral_source_route"]
        assert isinstance(source_item, dict)
        source_identity = AUDIT.semantic_contract_source_identity(
            "neutral_source_route", source_item
        )
        declaration = "theorem opaque_endpoint (x : Nat) : x = x := by rfl"
        qualified = (
            "Fixture.Other.uninformative" if renamed else "Fixture.Interface.opaque_endpoint"
        )
        declaration_identity = AUDIT.reviewed_declaration_identity(
            qualified, declaration
        )
        assert declaration_identity is not None
        signature_sha = hashlib.sha256(
            ("other surface" if renamed else "opaque elaborated surface").encode("utf-8")
        ).hexdigest()
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
        if caller_supplied_process:
            record = "Other.Namespace.Payload" if renamed else "Fixture.CycleRecord"
            sequence = "otherSequence" if renamed else "cycleValue"
            item["expanded_lean_surface"] = {
                "record_roots": [record],
                "record_field_types": [
                    {
                        "expanded_type": (
                            "forall n, ProbabilityTheory.IdentDistrib "
                            f"({sequence} n) ({sequence} 0) P P"
                        )
                    },
                    {
                        "expanded_type": f"Pairwise ((. ⟂ᵢ[P] .) on {sequence})"
                    },
                    {"expanded_type": f"Integrable ({sequence} 0) P"},
                ],
            }
        items, errors, counts = AUDIT.attach_source_model_derivation_requirements(
            [item],
            paper_statement_map=source_map,
            elaborated_signature_sha256_by_qualified={qualified: signature_sha},
        )
        self.assertEqual(errors, [])
        self.assertEqual(counts["source_model_derivation_context_count"], 1)
        self.assertEqual(counts["source_model_derivation_requirement_count"], 1)
        result = items[0]
        assert isinstance(result, dict)
        return next(
            dimension
            for dimension in result["dimensions"]
            if dimension["id"] == "source_model_derivation"
        )

    def direct_response(self, dimension: dict[str, object]) -> dict[str, object]:
        requirement = dimension["source_model_derivation"]
        assert isinstance(requirement, dict)
        contract = requirement["contracts"][0]
        assert isinstance(contract, dict)
        source_contract = contract["source_model_derivation_contract"]
        assert isinstance(source_contract, dict)
        source_digest = contract["source_semantic_sha256"]
        assert isinstance(source_digest, str)
        primitive_ids = [
            component["id"]
            for component in source_contract["source_primitive_components"]
        ]
        derived = source_contract["derived_conclusion"]
        assert isinstance(derived, dict)
        source_conclusion = derived["description"]
        assert isinstance(source_conclusion, str)
        association = dimension["source_model_derivation_association"]
        assert isinstance(association, dict)
        pin = association["semantic_association_sha256"]
        assert isinstance(pin, str)
        return {
            "verdict": "matches_source_model",
            "source_locator": "source.txt:1",
            "semantic_comparison": (
                "The Lean route starts from the two source primitive roles and derives "
                "the same accepted-cycle law."
            ),
            "lean_evidence": (
                "The expanded Lean surface exposes the primitive laws before the cycle "
                "consequence is established."
            ),
            "source_model_derivation_analysis": {
                "semantic_association_sha256": pin,
                "verdict": "derived_from_source_primitives",
                "contracts": [
                    {
                        "source_semantic_sha256": source_digest,
                        "source_primitive_component_ids": primitive_ids,
                        "lean_primitive_components": [
                            {
                                "source_primitive_component_id": primitive_id,
                                "description": (
                                    "The expanded Lean primitive role realizes source "
                                    f"component `{primitive_id}`."
                                ),
                            }
                            for primitive_id in primitive_ids
                        ],
                        "source_derived_conclusion_description": source_conclusion,
                        "lean_derived_conclusion_description": (
                            "The Lean conclusion is the accepted-cycle law produced after "
                            "combining the primitive arrival and selection mechanisms."
                        ),
                        "derivation_route": (
                            "checked_lean_derivation_from_source_primitives"
                        ),
                        "derivation_evidence": (
                            "The checked Lean derivation constructs the accepted-cycle law "
                            "from the listed source primitives rather than receiving it as "
                            "a record field."
                        ),
                    }
                ],
                "lean_bridge_evidence": (
                    "The checked Lean derivation from the listed source primitives is "
                    "bound to the current elaborated review signature."
                ),
            },
        }

    def test_context_schema_is_source_pinned_and_complete(self) -> None:
        context = self.context()
        self.assertEqual(
            evidence.source_model_derivation_context_contract_errors(context), []
        )
        missing = deepcopy(context)
        contract = missing["source_model_derivation_contract"]
        assert isinstance(contract, dict)
        del contract["source_primitive_components"]
        errors = evidence.source_model_derivation_context_contract_errors(missing)
        self.assertTrue(any("source_primitive_components" in error for error in errors))

        unanchored = deepcopy(context)
        unanchored_contract = unanchored["source_model_derivation_contract"]
        assert isinstance(unanchored_contract, dict)
        primitives = unanchored_contract["source_primitive_components"]
        assert isinstance(primitives, list) and primitives
        primitive = primitives[0]
        assert isinstance(primitive, dict)
        del primitive["source_anchor_evidence"]
        unanchored_errors = evidence.source_model_derivation_context_contract_errors(
            unanchored
        )
        self.assertTrue(
            any("source_anchor_evidence" in error for error in unanchored_errors),
            unanchored_errors,
        )

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

    def test_component_anchor_must_match_its_own_source_span(self) -> None:
        context = self.context()
        contract = context["source_model_derivation_contract"]
        assert isinstance(contract, dict)
        primitives = contract["source_primitive_components"]
        assert isinstance(primitives, list) and primitives
        primitive = primitives[0]
        assert isinstance(primitive, dict)
        # Line 2 is genuine and source-relevant, but it is evidence for the
        # acceptance primitive rather than the arrival-gap primitive on line 1.
        primitive["source_anchor_evidence"] = [self.source_anchor(2)]
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
        self.assertTrue(
            any(
                "source_anchor_evidence is missing declared source anchor" in finding.message
                or "source_anchor_evidence has undeclared or duplicate" in finding.message
                for finding in findings
            ),
            findings,
        )

    def test_component_anchor_content_and_id_change_source_semantic_identity(self) -> None:
        source_map = self.source_map(self.context())
        source_item = source_map["items"]["neutral_source_route"]
        assert isinstance(source_item, dict)
        original = AUDIT.semantic_contract_source_identity(
            "neutral_source_route", source_item
        )

        changed_id = deepcopy(source_item)
        contexts = changed_id["semantic_context_requirements"]
        assert isinstance(contexts, list) and contexts
        context = contexts[0]
        assert isinstance(context, dict)
        contract = context["source_model_derivation_contract"]
        assert isinstance(contract, dict)
        primitives = contract["source_primitive_components"]
        assert isinstance(primitives, list) and primitives
        primitive = primitives[0]
        assert isinstance(primitive, dict)
        primitive["id"] = "changed_arrival_gap_law"
        changed_id_identity = AUDIT.semantic_contract_source_identity(
            "neutral_source_route", changed_id
        )
        self.assertNotEqual(
            original["source_semantic_sha256"],
            changed_id_identity["source_semantic_sha256"],
        )

        changed_anchor = deepcopy(source_item)
        contexts = changed_anchor["semantic_context_requirements"]
        assert isinstance(contexts, list) and contexts
        context = contexts[0]
        assert isinstance(context, dict)
        contract = context["source_model_derivation_contract"]
        assert isinstance(contract, dict)
        conclusion = contract["derived_conclusion"]
        assert isinstance(conclusion, dict)
        anchors = conclusion["source_anchor_evidence"]
        assert isinstance(anchors, list) and anchors
        anchor = anchors[0]
        assert isinstance(anchor, dict)
        anchor["quoted_text"] = "Different claimed source conclusion."
        anchor["quoted_text_sha256"] = hashlib.sha256(
            anchor["quoted_text"].encode("utf-8")
        ).hexdigest()
        changed_anchor_identity = AUDIT.semantic_contract_source_identity(
            "neutral_source_route", changed_anchor
        )
        self.assertNotEqual(
            original["source_semantic_sha256"],
            changed_anchor_identity["source_semantic_sha256"],
        )

    def test_non_opt_in_map_preserves_existing_receipts(self) -> None:
        source_map = {
            "items": {
                "ordinary_source_route": {
                    "claim_bearing": True,
                    "source_kind": "proposition",
                    "source_location": "source.txt:1",
                }
            }
        }
        self.assertFalse(AUDIT.source_map_uses_source_model_derivation_context(source_map))
        item: dict[str, object] = {
            "row": "opaque_unrelated_row",
            "qualified_declaration": "Fixture.Interface.opaque_endpoint",
            "dimensions": [],
        }
        items, errors, counts = AUDIT.attach_source_model_derivation_requirements(
            [item],
            paper_statement_map=source_map,
            elaborated_signature_sha256_by_qualified={},
        )
        self.assertEqual(errors, [])
        self.assertEqual(counts["source_model_derivation_context_count"], 0)
        self.assertEqual(counts["source_model_derivation_requirement_count"], 0)
        self.assertEqual(items, [item])

    def test_extension_requires_generated_marker_and_preserves_base_schema(self) -> None:
        derivation_dimension = self.generated_dimension()
        dimensions = [
            *[
                {"id": dimension_id}
                for dimension_id in evidence.SEMANTIC_MODEL_REVIEW_DIMENSIONS
            ],
            derivation_dimension,
        ]
        self.assertEqual(evidence.semantic_model_item_dimension_ids_error(dimensions), "")

        unmarked = deepcopy(dimensions)
        for dimension in unmarked:
            if dimension["id"] == "source_model_derivation":
                del dimension["requires_source_model_derivation_analysis"]
        self.assertIn(
            "explicitly generated source-pinned",
            evidence.semantic_model_item_dimension_ids_error(unmarked),
        )

        unsupported = [*dimensions, {"id": "unrelated_extension"}]
        self.assertIn(
            "unsupported non-base extension",
            evidence.semantic_model_item_dimension_ids_error(unsupported),
        )

    def test_checked_route_is_name_invariant_but_not_name_satisfiable(self) -> None:
        dimension = self.generated_dimension()
        renamed_dimension = self.generated_dimension(renamed=True)
        response = self.direct_response(dimension)
        self.assertEqual(
            projection.source_model_derivation_analysis_errors(dimension, response), []
        )
        semantic_item = {"dimensions": [dimension]}
        semantic_judgment = {
            "classification": "semantic_model_review",
            "semantic_model_dimensions": {"source_model_derivation": response},
        }
        self.assertTrue(
            evidence.semantic_model_judgment_is_complete(
                semantic_item, semantic_judgment
            )
        )

        renamed_response = self.direct_response(renamed_dimension)
        self.assertEqual(
            projection.source_model_derivation_analysis_errors(
                renamed_dimension, renamed_response
            ),
            [],
        )

        bare_name = deepcopy(response)
        analysis = bare_name["source_model_derivation_analysis"]
        assert isinstance(analysis, dict)
        analysis["lean_bridge_evidence"] = "Fixture.DeriveCycle"
        errors = projection.source_model_derivation_analysis_errors(dimension, bare_name)
        self.assertTrue(any("name-only evidence" in error for error in errors), errors)

    def test_caller_supplied_process_surface_is_fail_closed_name_invariant(self) -> None:
        dimension = self.generated_dimension(caller_supplied_process=True)
        renamed_dimension = self.generated_dimension(
            renamed=True,
            caller_supplied_process=True,
        )
        basis = dimension["caller_supplied_model_construction_basis"]
        renamed_basis = renamed_dimension["caller_supplied_model_construction_basis"]
        self.assertIsInstance(basis, list)
        self.assertTrue(basis)
        self.assertEqual(basis, renamed_basis)

        for current_dimension in (dimension, renamed_dimension):
            safe_response = self.direct_response(current_dimension)
            safe_errors = projection.source_model_derivation_analysis_errors(
                current_dimension,
                safe_response,
            )
            self.assertTrue(
                any("only documented_partial_boundary is allowed" in error for error in safe_errors),
                safe_errors,
            )
            semantic_item = {"dimensions": [current_dimension]}
            safe_judgment = {
                "classification": "semantic_model_review",
                "semantic_model_dimensions": {
                    "source_model_derivation": safe_response,
                },
            }
            self.assertFalse(
                evidence.semantic_model_judgment_is_complete(
                    semantic_item,
                    safe_judgment,
                )
            )

        documented_open = self.direct_response(dimension)
        documented_open["verdict"] = "documented_partial_boundary"
        documented_open["semantic_comparison"] = (
            "The theorem input supplies the cycle package, while the source declares "
            "that package as a consequence of the arrival and acceptance primitives."
        )
        documented_open["lean_evidence"] = (
            "The expanded record surface contains the IID, independence, and "
            "integrability package for one sequence."
        )
        analysis = documented_open["source_model_derivation_analysis"]
        assert isinstance(analysis, dict)
        analysis["verdict"] = "documented_partial_boundary"
        analysis["lean_bridge_evidence"] = (
            "The expanded input has a caller-supplied construction package and no "
            "separate machine-generated primitive-level derivation receipt."
        )
        contracts = analysis["contracts"]
        assert isinstance(contracts, list) and contracts
        contract = contracts[0]
        assert isinstance(contract, dict)
        contract["derivation_route"] = "caller_supplied_derived_conclusion"
        contract["derivation_evidence"] = (
            "The record supplies the declared conclusion, so this review documents "
            "the unresolved primitive-to-conclusion boundary."
        )
        self.assertEqual(
            projection.source_model_derivation_analysis_errors(
                dimension,
                documented_open,
            ),
            [],
        )

    def test_caller_supplied_conclusion_and_missing_primitive_are_open(self) -> None:
        dimension = self.generated_dimension()
        response = self.direct_response(dimension)
        caller_supplied = deepcopy(response)
        analysis = caller_supplied["source_model_derivation_analysis"]
        assert isinstance(analysis, dict)
        contracts = analysis["contracts"]
        assert isinstance(contracts, list) and contracts
        contract = contracts[0]
        assert isinstance(contract, dict)
        contract["derivation_route"] = "caller_supplied_derived_conclusion"
        caller_errors = projection.source_model_derivation_analysis_errors(
            dimension, caller_supplied
        )
        self.assertTrue(
            any("caller-supplied or lacks a checked derivation" in error for error in caller_errors),
            caller_errors,
        )
        semantic_item = {"dimensions": [dimension]}
        caller_judgment = {
            "classification": "semantic_model_review",
            "semantic_model_dimensions": {"source_model_derivation": caller_supplied},
        }
        self.assertFalse(
            evidence.semantic_model_judgment_is_complete(
                semantic_item, caller_judgment
            )
        )

        documented_open = deepcopy(caller_supplied)
        documented_analysis = documented_open["source_model_derivation_analysis"]
        assert isinstance(documented_analysis, dict)
        documented_analysis["verdict"] = "documented_partial_boundary"
        documented_errors = projection.source_model_derivation_analysis_errors(
            dimension, documented_open
        )
        self.assertTrue(
            any(
                "unresolved source-model derivation" in error
                for error in documented_errors
            ),
            documented_errors,
        )

        missing_primitive = deepcopy(response)
        missing_analysis = missing_primitive["source_model_derivation_analysis"]
        assert isinstance(missing_analysis, dict)
        missing_contracts = missing_analysis["contracts"]
        assert isinstance(missing_contracts, list) and missing_contracts
        missing_contract = missing_contracts[0]
        assert isinstance(missing_contract, dict)
        lean_primitives = missing_contract["lean_primitive_components"]
        assert isinstance(lean_primitives, list)
        lean_primitives.pop()
        missing_errors = projection.source_model_derivation_analysis_errors(
            dimension, missing_primitive
        )
        self.assertTrue(
            any("Lean omits, adds, or reorders a source primitive" in error for error in missing_errors),
            missing_errors,
        )


if __name__ == "__main__":
    unittest.main()
