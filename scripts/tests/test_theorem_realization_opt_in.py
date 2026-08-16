#!/usr/bin/env python3
"""Regressions for explicit v11 theorem-realization activation."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    if str(import_root) not in sys.path:
        sys.path.insert(0, str(import_root))

from scripts import audit_conclusion_provenance as GATE  # noqa: E402
from scripts.source_coverage_scope import (  # noqa: E402
    source_record_source_item_semantic_sha256,
)
from scripts.source_record_target_disposition import (  # noqa: E402
    source_contract_association_record_digest,
)


PAPER = "Fixture"


def component_payload(*, schema: object = 1) -> dict[str, object]:
    association: dict[str, object] = {
        "schema": 2,
        "association_mode": "semantic_contract_group_member",
        "semantic_contract_member_role": "transparent_spec",
        "semantic_model_judgment_key": "semantic-model::fixture",
        "source_item_identities": [],
    }
    association["association_sha256"] = source_contract_association_record_digest(
        association
    )
    return {
        "theorem_realization_contract_schema": schema,
        "theorem_facing_input_items": [
            {
                "row": "reviewed_row",
                "binder": "arbitrary_parameter",
                "judgment_key": "fixture.component",
                "structural_type_sha256": "b" * 64,
                "type": "FixtureCarrier",
            }
        ],
        "theorem_realization_component_items": [
            {
                "row": "reviewed_row",
                "binder": "arbitrary_parameter",
                "judgment_key": "fixture.component",
                "source_judgment_key": "fixture.component",
                "source_component_section": "theorem_facing_input_items",
                "source_claim_component_role": "material",
                "source_claim_component_sha256": "a" * 64,
                "structural_type_sha256": "b" * 64,
                "source_claim_component_occurrence": {
                    "schema": 1,
                    "surface": "theorem_facing_input_items",
                    "traversal_slot": 0,
                },
                "type": "FixtureCarrier",
                "source_contract_association": association,
            }
        ],
    }


def recursive_field_component_payload() -> dict[str, object]:
    """One generated recursive source-model field occurrence fixture."""

    source_identity = {
        "source_key": "source-item",
        "source_map_item_sha256": "c" * 64,
        "source_semantic_sha256": "d" * 64,
    }
    parent_identity = {
        "qualified_declaration": "Fixture.paperTheorem",
        "declaration_sha256": "e" * 64,
    }
    parent_signature = {
        "qualified_declaration": "Fixture.paperTheorem",
        "elaborated_signature_sha256": "f" * 64,
    }
    route = {
        "schema": 1,
        "inheritance_mode": "explicit_parent_route_and_field_scope",
        "association_sha256": "0" * 64,
        "source_item": "source-item",
        "source_item_identities": [source_identity],
        "root_record": "Fixture.Model",
        "root_input_type_canonical": "Fixture.Model",
        "field_chain": [{"structure": "Fixture.Model", "field": "rate"}],
        "source_locator": "source.tex:10",
        "permitted_classifications": ["validated_source_assumption"],
        "convention_id": "fixture-model-convention",
        "convention_sha256": "1" * 64,
        "field_scope_sha256": "2" * 64,
        "parent_association_field": "semantic_contract_source_association",
        "parent_semantic_model_judgment_key": "semantic-model::paperTheorem",
        "parent_source_association_role": "direct_evidence",
        "parent_source_association_origin": "",
        "parent_reviewed_declaration_identity": parent_identity,
        "parent_elaborated_signature_identity": parent_signature,
        "parent_source_association_sha256": "3" * 64,
    }
    field = {
        "judgment_key": "Fixture.Model.rate",
        "structure": "Fixture.Model",
        "field": "rate",
        "path": "Fixture.Model -> Fixture.Model.rate",
        "nested_structures": [],
        "structural_type_sha256": "b" * 64,
        "type": "Category -> Real",
        "recursive_field_explicit_parent_route": route,
    }
    component = {
        **field,
        "judgment_key": "theorem-realization::fixture-rate",
        "source_judgment_key": "Fixture.Model.rate",
        "source_component_section": "recursive_field_items",
        "source_claim_component_role": "material",
        "source_claim_component_kind": "recursive_record_field",
        "source_claim_component_sha256": "a" * 64,
        "source_claim_component_occurrence": {
            "schema": 1,
            "surface": "recursive_field_items",
            "traversal_slot": 0,
        },
    }
    return {
        "theorem_realization_contract_schema": 1,
        "recursive_field_items": [field],
        "theorem_realization_component_items": [component],
    }


class TheoremRealizationOptInTests(unittest.TestCase):
    def findings(
        self,
        *,
        status_review_surface: dict[str, object] | None = None,
        statement_map: dict[str, object] | None = None,
        judgments: dict[str, dict[str, object]] | None = None,
        schema: object = 1,
        terminal_receipts: tuple[
            GATE.SemanticContractExecutableTerminalComponentReceipt, ...
        ] = (),
        recursive_field_receipts: tuple[
            GATE.RecursiveFieldExplicitParentComponentReceipt, ...
        ] = (),
        payload_override: dict[str, object] | None = None,
    ) -> list[GATE.Finding]:
        old_papers = GATE.PAPERS
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            folder = root / PAPER
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "status": "formalized",
                        "review_surface": status_review_surface or {},
                    }
                ),
                encoding="utf-8",
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(statement_map or {"items": {}}), encoding="utf-8"
            )
            try:
                GATE.PAPERS = root
                return GATE.theorem_realization_component_contract_findings(
                    PAPER,
                    payload_override or component_payload(schema=schema),
                    judgments or {},
                    semantic_contract_executable_terminal_component_receipts=(
                        terminal_receipts
                    ),
                    recursive_field_explicit_parent_component_receipts=(
                        recursive_field_receipts
                    ),
                )
            finally:
                GATE.PAPERS = old_papers

    def test_unrequested_v10_paper_does_not_activate_from_generated_ledger(self) -> None:
        # The raw generator emits schema 1 for structural discovery on every
        # paper. That availability cannot silently change the paper's audit
        # policy or invalidate its established v10 evidence.
        # Automatic new/material-closeout selection is tested by the
        # transition suite.  Hold that independent decision false here to
        # prove that the generated ledger alone still is not activation.
        with mock.patch.object(
            GATE, "source_spec_correspondence_requested", return_value=False
        ):
            self.assertEqual(self.findings(), [])

    def test_status_opt_in_enforces_component_contracts(self) -> None:
        findings = self.findings(
            status_review_surface={"require_source_spec_correspondence": True}
        )
        self.assertTrue(findings)
        self.assertIn("no source-claim semantic contract", findings[0].message)

    def test_source_map_opt_in_enforces_component_contracts(self) -> None:
        findings = self.findings(
            statement_map={
                "source_spec_correspondence_schema": 1,
                "items": {},
            }
        )
        self.assertTrue(findings)

    def test_boolean_source_map_marker_does_not_activate_the_strict_lane(self) -> None:
        with mock.patch.object(
            GATE, "source_spec_correspondence_requested", return_value=False
        ):
            self.assertEqual(
                self.findings(
                    statement_map={
                        "source_spec_correspondence_schema": True,
                        "items": {},
                    }
                ),
                [],
            )

    def test_explicit_opt_in_rejects_a_missing_ledger_schema(self) -> None:
        findings = self.findings(
            status_review_surface={"require_source_spec_correspondence": True},
            schema=None,
        )
        self.assertEqual(len(findings), 1)
        self.assertIn("ledger is missing schema 1", findings[0].message)

    def test_exact_terminal_component_receipt_closes_only_its_bound_occurrence(
        self,
    ) -> None:
        payload = component_payload()
        component = payload["theorem_realization_component_items"][0]
        assert isinstance(component, dict)
        association = component["source_contract_association"]
        assert isinstance(association, dict)
        receipt = GATE.SemanticContractExecutableTerminalComponentReceipt(
            component_key="fixture.component",
            source_judgment_key="fixture.component",
            component_sha256="a" * 64,
            structural_type_sha256="b" * 64,
            semantic_model_judgment_key="semantic-model::fixture",
            component_source_contract_association_sha256=str(
                association["association_sha256"]
            ),
            source_item_key="source-formula",
            source_item_semantic_sha256="c" * 64,
            source_map_item_sha256="d" * 64,
            spec_declaration="Fixture.theoremSpec",
            evidence_declaration="Fixture.theorem",
            evidence_elaborated_signature_sha256="e" * 64,
            evidence_semantic_dependency_sha256="f" * 64,
            terminal_receipt_sha256="0" * 64,
        )
        self.assertEqual(
            self.findings(
                status_review_surface={"require_source_spec_correspondence": True},
                terminal_receipts=(receipt,),
            ),
            [],
        )

        for field, value in (
            ("component_sha256", "1" * 64),
            ("structural_type_sha256", "2" * 64),
            ("component_source_contract_association_sha256", "3" * 64),
        ):
            with self.subTest(field=field):
                altered = GATE.SemanticContractExecutableTerminalComponentReceipt(
                    **{**receipt.__dict__, field: value}
                )
                rejected = self.findings(
                    status_review_surface={
                        "require_source_spec_correspondence": True
                    },
                    terminal_receipts=(altered,),
                )
                self.assertEqual(len(rejected), 1)
                self.assertIn(
                    "no source-claim semantic contract", rejected[0].message
                )

    def test_recursive_field_receipt_binds_every_structural_parent_pin(self) -> None:
        payload = recursive_field_component_payload()
        receipt = GATE.RecursiveFieldExplicitParentComponentReceipt(
            component_key="theorem-realization::fixture-rate",
            source_judgment_key="Fixture.Model.rate",
            component_sha256="a" * 64,
            structural_type_sha256="b" * 64,
            recursive_field_parent_route_sha256="0" * 64,
            source_item_key="source-item",
            source_item_semantic_sha256="d" * 64,
            source_map_item_sha256="c" * 64,
            root_record="Fixture.Model",
            field_scope_sha256="2" * 64,
            convention_id="fixture-model-convention",
            convention_sha256="1" * 64,
            parent_semantic_model_judgment_key="semantic-model::paperTheorem",
            parent_qualified_declaration="Fixture.paperTheorem",
            parent_declaration_sha256="e" * 64,
            parent_elaborated_signature_sha256="f" * 64,
            parent_source_association_sha256="3" * 64,
        )
        closed = self.findings(
            status_review_surface={"require_source_spec_correspondence": True},
            payload_override=payload,
            recursive_field_receipts=(receipt,),
        )
        self.assertEqual(closed, [])

        for field, value in (
            ("component_sha256", "4" * 64),
            ("source_item_semantic_sha256", "5" * 64),
            ("parent_elaborated_signature_sha256", "6" * 64),
            ("parent_source_association_sha256", "7" * 64),
            ("parent_semantic_model_judgment_key", "semantic-model::other"),
        ):
            with self.subTest(field=field):
                altered = GATE.RecursiveFieldExplicitParentComponentReceipt(
                    **{**receipt.__dict__, field: value}
                )
                rejected = self.findings(
                    status_review_surface={
                        "require_source_spec_correspondence": True
                    },
                    payload_override=payload,
                    recursive_field_receipts=(altered,),
                )
                self.assertEqual(len(rejected), 1)
                self.assertIn(
                    "no source-claim semantic contract", rejected[0].message
                )

    def test_occurrence_contract_not_reviewer_classification_is_disposition(
        self,
    ) -> None:
        source_item = {
            "source_location": "source.tex:10",
            "source_text": "The source fixes the carrier used by the result.",
        }
        source_sha = source_record_source_item_semantic_sha256(source_item, "")
        contract = {
            "schema": 1,
            "route": "exact_source_claim",
            "component_sha256": "a" * 64,
            "structural_type_sha256": "b" * 64,
            "source_anchor": {
                "source_item_key": "source-item",
                "source_item_semantic_sha256": source_sha,
                "source_locator": "source.tex:10",
                "source_formula": "The source domain contains this carrier parameter.",
                "semantic_match": "The generated component is that same carrier domain.",
            },
        }
        statement_map = {"items": {"source-item": source_item}}

        for classification in (
            "semantic_model_review",
            "proved_from_primitives",
            "validated_source_assumption",
            "renamed_reviewer_label",
        ):
            with self.subTest(classification=classification):
                self.assertEqual(
                    self.findings(
                        status_review_surface={
                            "require_source_spec_correspondence": True
                        },
                        statement_map=statement_map,
                        judgments={
                            "fixture.component": {
                                "classification": classification,
                                "source_claim_semantic_contract": contract,
                            }
                        },
                    ),
                    [],
                )

    def test_affirmative_disposition_predicate_is_classification_generic(self) -> None:
        kwargs = {
            "statement_map": {},
            "source_proof_fidelity": {},
            "status": "formalized",
            "administrative_projection_rebind": None,
        }
        with mock.patch.object(
            GATE, "source_input_target_disposition_errors", return_value=[]
        ):
            for classification in (
                "semantic_model_review",
                "container_recursively_audited",
                "nonpropositional_witness_data",
                "approved_formalization_regularity",
                "arbitrary_reviewer_label",
                "",
            ):
                with self.subTest(classification=classification):
                    self.assertFalse(
                        GATE.source_input_has_current_target_disposition(
                            {}, {"classification": classification}, **kwargs
                        )
                    )
            for classification in GATE.INPUT_SOURCE_CREDIT_CLASSIFICATIONS:
                with self.subTest(classification=classification):
                    self.assertTrue(
                        GATE.source_input_has_current_target_disposition(
                            {}, {"classification": classification}, **kwargs
                        )
                    )


if __name__ == "__main__":
    unittest.main()
