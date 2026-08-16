#!/usr/bin/env python3
"""Regression tests for normal/deep source-map integrity boundaries."""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    value = str(import_root)
    if value not in sys.path:
        sys.path.insert(0, value)

import audit_evidence_integrity as integrity  # noqa: E402


class EvidenceIntegrityScopeTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.previous_root = integrity.ROOT
        integrity.ROOT = self.root
        self.addCleanup(setattr, integrity, "ROOT", self.previous_root)
        self.paper = self.root / "papers" / "FixturePaper"
        self.audit = self.paper / "audit"
        self.audit.mkdir(parents=True)
        self.source = self.paper / "source.txt"
        self.source.write_text(
            "Theorem 1. Gives the named result.\n"
            "\n"
            "Figure 1 reports a numerical illustration.\n",
            encoding="utf-8",
        )

    def quote(self, line: int, end_line: int | None = None) -> dict[str, object]:
        final_line = end_line or line
        text = "\n".join(
            self.source.read_text(encoding="utf-8").splitlines()[
                line - 1 : final_line
            ]
        )
        return {
            "path": self.source.name,
            "line_start": line,
            "line_end": final_line,
            "quoted_text": text,
            "quoted_text_sha256": hashlib.sha256(text.encode("utf-8")).hexdigest(),
        }

    def write_map(
        self,
        items: dict[str, object],
        *,
        mode: str | None = "named_theoretical_statements",
        semantic_contract_schema: bool = False,
        named_result_review_overrides: dict[str, object] | None = None,
    ) -> None:
        digest = hashlib.sha256(self.source.read_bytes()).hexdigest()
        effective_mode = mode or "named_theoretical_statements"
        presentations = integrity.extract_named_result_presentations(
            self.source.read_text(encoding="utf-8"),
            source_format="text",
        )
        receipt_presentations = [
            presentation
            for presentation in presentations
            if integrity.source_named_presentation_in_coverage_scope(
                presentation.kind, effective_mode
            )
        ]
        payload: dict[str, object] = {
            "source_artifact_path": self.source.name,
            "source_artifact_sha256": digest,
            "source_anchor_evidence_required": True,
            "source_named_result_inventory_review": {
                "schema": 1,
                "complete": True,
                "validator": "fixture-reviewer",
                "validated_at": "2026-07-26",
                "method": "fixture named-result source scan",
                "source_artifact_sha256": digest,
                "discovered_named_result_sha256": (
                    integrity.named_result_presentations_sha256(receipt_presentations)
                ),
                "prose_definition_presentations": [],
                "discovered_prose_definition_sha256": hashlib.sha256(
                    b"[]"
                ).hexdigest(),
            },
            "items": items,
        }
        if mode is not None:
            payload["source_coverage_mode"] = mode
        if named_result_review_overrides:
            review = payload["source_named_result_inventory_review"]
            assert isinstance(review, dict)
            review.update(named_result_review_overrides)
        if mode == "deep_paper_with_all_prose_claims":
            payload["source_prose_inventory_review"] = {
                "complete": True,
                "validator": "fixture-reviewer",
                "validated_at": "2026-07-26",
                "method": "fixture source screened in full",
                "source_artifact_sha256": digest,
            }
        if semantic_contract_schema:
            payload["semantic_contract_schema"] = 1
        (self.audit / "paper_statement_map.json").write_text(
            json.dumps(payload), encoding="utf-8"
        )

    def named_contract_item(self) -> dict[str, object]:
        return {
            "source_kind": "theorem",
            "claim_bearing": True,
            "source_location": "source.txt:1",
            "source_anchor_evidence": [self.quote(1)],
            "semantic_contract": {
                "spec_declaration": "Fixture.sourceSpec",
                "evidence_declaration": "Fixture.sourceProof",
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            },
        }

    def test_normal_scope_skips_deep_only_anchor_and_contract_obligations(self) -> None:
        self.write_map(
            {
                "renamable_named_item": self.named_contract_item(),
                "renamable_figure_item": {
                    "source_kind": "figure",
                    "claim_bearing": True,
                    "source_location": "source.txt:3",
                    # Deliberately no anchor or semantic contract: a normal
                    # named-theory closeout must not become all-prose review.
                },
            },
            semantic_contract_schema=True,
        )

        self.assertEqual(
            integrity.check_source_manifest(self.paper, "formalized"), []
        )
        self.assertEqual(
            integrity.semantic_contract_inventory_findings(self.paper, "formalized"),
            [],
        )

    def test_repaired_defect_route_is_validated_without_expanding_paper_coverage(self) -> None:
        """A repair route cannot disappear behind normal presentation scope."""

        supporting_display = {
            "source_kind": "figure",
            "claim_bearing": True,
            "source_location": "source.txt:3",
            "source_anchor_evidence": [self.quote(3)],
            "source_defect_ids": ["FIX-REPAIR-1"],
            "semantic_contract": {
                "spec_declaration": "Fixture.repairSpec",
                "evidence_declaration": "Fixture.repairProof",
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            },
        }
        self.write_map(
            {"non_named_repair_support": supporting_display},
            semantic_contract_schema=True,
        )
        (self.audit / "source_proof_fidelity.json").write_text(
            json.dumps(
                {
                    "defects": [
                        {
                            "id": "FIX-REPAIR-1",
                            "resolution": "repaired_in_lean",
                        }
                    ]
                }
            ),
            encoding="utf-8",
        )

        payload = json.loads(
            (self.audit / "paper_statement_map.json").read_text(encoding="utf-8")
        )
        ordinary = integrity.filter_source_map_items_for_coverage(
            payload["items"], "named_theoretical_statements"
        )
        _scoped, integrity_items = integrity.scoped_source_map_payload(
            payload,
            "named_theoretical_statements",
            folder=self.paper,
            repository_root=integrity.ROOT,
        )

        self.assertNotIn("non_named_repair_support", ordinary)
        self.assertIn("non_named_repair_support", integrity_items)
        self.assertEqual(
            integrity.semantic_contract_inventory_findings(self.paper, "formalized"),
            [],
        )

    def test_approved_scope_exclusion_is_not_a_direct_route_obligation(self) -> None:
        """Its dedicated source validator remains responsible for the exclusion."""

        excluded_quote = self.quote(3)
        self.write_map(
            {
                "renamable_named_item": self.named_contract_item(),
                "approved_nonproof_item": {
                    "source_kind": "remark",
                    "claim_bearing": True,
                    "source_location": "source.txt:3",
                    "source_anchor_evidence": [excluded_quote],
                    "user_approved_scope_exclusion": {
                        "schema": 1,
                        "approval_kind": "explicit_user_instruction",
                        "approval_reference": "fixture scope decision",
                        "approved_at": "2026-08-14",
                        "reason": "The finite illustration is outside the requested theorem proofs.",
                        "source_locator": "source.txt:3",
                        "source_evidence": "The exact caption remains source-pinned.",
                        "source_anchor_quote_sha256": excluded_quote[
                            "quoted_text_sha256"
                        ],
                    },
                },
            },
            semantic_contract_schema=True,
        )
        payload = json.loads(
            (self.audit / "paper_statement_map.json").read_text(encoding="utf-8")
        )

        _scoped, integrity_items = integrity.scoped_source_map_payload(
            payload,
            "named_theoretical_statements",
            folder=self.paper,
            repository_root=integrity.ROOT,
        )

        self.assertEqual(set(integrity_items), {"renamable_named_item"})
        self.assertEqual(
            integrity.user_approved_scope_exclusion_map_findings(
                self.paper,
                "formalized",
                self.audit / "paper_statement_map.json",
                payload,
            ),
            [],
        )

    def test_deep_scope_applies_anchor_and_contract_obligations_to_figure(self) -> None:
        self.write_map(
            {
                "renamable_named_item": self.named_contract_item(),
                "renamable_figure_item": {
                    "source_kind": "figure",
                    "claim_bearing": True,
                    "source_location": "source.txt:3",
                },
            },
            mode="deep_paper_with_all_prose_claims",
            semantic_contract_schema=True,
        )

        anchor_messages = [
            finding.message
            for finding in integrity.check_source_manifest(self.paper, "formalized")
        ]
        contract_messages = [
            finding.message
            for finding in integrity.semantic_contract_inventory_findings(
                self.paper, "formalized"
            )
        ]
        self.assertTrue(
            any("source_anchor_evidence must be a nonempty list" in message for message in anchor_messages),
            anchor_messages,
        )
        self.assertTrue(
            any("lacks semantic_contract" in message for message in contract_messages),
            contract_messages,
        )

    def test_raw_nonobject_is_never_filtered_out(self) -> None:
        self.write_map({"renamable_bad_item": "not an object"})

        messages = [
            finding.message
            for finding in integrity.check_source_manifest(self.paper, "formalized")
        ]
        self.assertTrue(any("not an object" in message for message in messages), messages)

    def test_source_presentation_conflict_is_never_filtered_out(self) -> None:
        self.write_map(
            {
                "renamable_conflict": {
                    "source_kind": "figure",
                    "claim_bearing": False,
                    "statement": "Theorem 1 gives the named result.",
                    "source_location": "source.txt:1",
                    "source_anchor_evidence": [self.quote(1)],
                }
            }
        )

        messages = [
            finding.message
            for finding in integrity.check_source_manifest(self.paper, "formalized")
        ]
        self.assertTrue(
            any("conflicts with a named theoretical source presentation" in message for message in messages),
            messages,
        )

    def test_independent_named_result_index_rejects_an_omitted_theorem(self) -> None:
        self.source.write_text(
            "Theorem 1. Every admissible input has a witness.\n"
            "Figure 1 reports a numerical illustration.\n",
            encoding="utf-8",
        )
        self.write_map(
            {
                # A source location on an out-of-scope presentation is not
                # allowed to make a discovered theorem disappear. Map/Lean
                # names are intentionally irrelevant to this assertion.
                "misleading_theorem_navigation": {
                    "source_kind": "figure",
                    "claim_bearing": True,
                    "source_location": "source.txt:1",
                }
            }
        )

        messages = [
            finding.message
            for finding in integrity.check_source_manifest(self.paper, "formalized")
        ]

        self.assertTrue(
            any("independent source named-result index found an uncovered theorem" in message for message in messages),
            messages,
        )

    def test_source_index_anchor_selection_ignores_map_metadata_and_location(self) -> None:
        self.source.write_text(
            "Theorem 1. Every admissible input has a witness.\n"
            "Theorem 2. Every witness has the stated property.\n",
            encoding="utf-8",
        )
        self.write_map(
            {
                # The map key, source kind, prose summary, and Lean route are
                # all deliberately non-theorem-like. Only the current exact
                # anchor may select this row for Theorem 1.
                "figure_navigation_key": {
                    "source_kind": "remark",
                    "claim_bearing": True,
                    "statement": "Every admissible input has a witness.",
                    "lean_declarations": ["Fixture.figureCaption"],
                    "source_location": "source.txt:1-2",
                    "source_anchor_evidence": [self.quote(1)],
                }
            }
        )

        messages = [
            finding.message
            for finding in integrity.check_source_manifest(self.paper, "formalized")
        ]

        self.assertFalse(
            any("uncovered theorem presentation `Theorem 1`" in message for message in messages),
            messages,
        )
        self.assertTrue(
            any("uncovered theorem presentation `Theorem 2`" in message for message in messages),
            messages,
        )

    def test_named_result_core_reconciliation_is_byte_pinned_and_source_only(self) -> None:
        self.source.write_text(
            "Theorem 1. Assume every input is admissible.\n"
            "Then every input has a witness.\n"
            "This paragraph gives intuition for the theorem.\n"
            "Theorem 2. Every witness is unique.\n",
            encoding="utf-8",
        )
        self.write_map(
            {
                # Map key and Lean route deliberately conflict with the
                # presentation. The core's current source bytes decide it.
                "figure_navigation": {
                    "source_kind": "remark",
                    "claim_bearing": True,
                    "source_location": "source.txt:1-3",
                    "source_anchor_evidence": [self.quote(1, 3)],
                    "lean_declarations": ["Fixture.unrelatedFigureRoute"],
                    "source_presentation_reconciliation": {
                        "schema": 1,
                        "relation": "conservative_text_span_core",
                        "presentation_kind": "theorem",
                        "presentation_label": "Theorem 1",
                        "core_anchor": self.quote(1, 2),
                        "boundary_reason": "completed_statement_then_explanation",
                        "semantic_basis": (
                            "The pinned multiline core contains the displayed "
                            "hypothesis and conclusion; line 3 is explanation."
                        ),
                        "validator": "fixture source-only reviewer",
                        "validated_at": "2026-07-28T12:00:00Z",
                    },
                },
                "second_navigation": {
                    "source_kind": "theorem",
                    "claim_bearing": True,
                    "source_location": "source.txt:4",
                    "source_anchor_evidence": [self.quote(4)],
                },
            }
        )
        map_path = self.audit / "paper_statement_map.json"
        payload = json.loads(map_path.read_text(encoding="utf-8"))

        self.assertEqual(
            integrity.source_named_result_inventory_findings(
                self.paper, "formalized", map_path, payload
            ),
            [],
        )

        invalid = json.loads(json.dumps(payload))
        invalid["items"]["figure_navigation"][
            "source_presentation_reconciliation"
        ]["core_anchor"] = self.quote(1)
        messages = [
            finding.message
            for finding in integrity.source_named_result_inventory_findings(
                self.paper, "formalized", map_path, invalid
            )
        ]
        self.assertTrue(
            any("nonblank continuation" in message for message in messages),
            messages,
        )

    def test_normal_receipt_skips_standalone_display_but_reports_unclassified_named_presentation(
        self,
    ) -> None:
        self.source.write_text(
            "Theorem 1. Gives the named result.\n"
            "Formula 2. Gives a standalone display identity.\n"
            "Algorithm 3. Gives a standalone update procedure.\n"
            "Property 3. Requires source-specific presentation classification.\n",
            encoding="utf-8",
        )
        self.write_map({"named": self.named_contract_item()})

        messages = [
            finding.message
            for finding in integrity.check_source_manifest(self.paper, "formalized")
        ]

        self.assertFalse(
            any("discovered_named_result_sha256 does not match" in message for message in messages),
            messages,
        )
        self.assertFalse(
            any("uncovered formula presentation" in message for message in messages),
            messages,
        )
        self.assertFalse(
            any("uncovered algorithm presentation" in message for message in messages),
            messages,
        )
        self.assertTrue(
            any("unclassified named presentation `Property 3`" in message for message in messages),
            messages,
        )

    def test_deep_receipt_reconciles_standalone_formula(self) -> None:
        self.source.write_text(
            "Theorem 1. Gives the named result.\n"
            "Formula 2. Gives a standalone display identity.\n",
            encoding="utf-8",
        )
        self.write_map(
            {"named": self.named_contract_item()},
            mode="deep_paper_with_all_prose_claims",
        )

        uncovered_messages = [
            finding.message
            for finding in integrity.check_source_manifest(self.paper, "formalized")
        ]
        self.assertTrue(
            any("uncovered formula presentation" in message for message in uncovered_messages),
            uncovered_messages,
        )

        self.write_map(
            {
                "named": self.named_contract_item(),
                "formula": {
                    "source_kind": "formula",
                    "claim_bearing": True,
                    "source_location": "source.txt:2",
                    "source_anchor_evidence": [self.quote(2)],
                },
            },
            mode="deep_paper_with_all_prose_claims",
        )
        reconciled_messages = [
            finding.message
            for finding in integrity.check_source_manifest(self.paper, "formalized")
        ]
        self.assertFalse(
            any("uncovered formula presentation" in message for message in reconciled_messages),
            reconciled_messages,
        )

    def test_explicit_corrected_target_remains_anchor_mandatory_in_normal_scope(self) -> None:
        self.write_map(
            {
                "renamable_correction": {
                    "source_kind": "remark",
                    "claim_bearing": True,
                    "coverage_status": "corrected_source_statement",
                    "source_location": "source.txt:3",
                    "corrected_target": {},
                }
            }
        )

        messages = [
            finding.message
            for finding in integrity.check_source_manifest(self.paper, "formalized")
        ]
        self.assertTrue(
            any("source_anchor_evidence must be a nonempty list" in message for message in messages),
            messages,
        )

    def test_closeout_requires_explicit_coverage_mode(self) -> None:
        self.write_map(
            {"renamable_named_item": self.named_contract_item()}, mode=None
        )

        closeout_messages = [
            finding.message
            for finding in integrity.check_source_manifest(self.paper, "formalized")
        ]
        draft_messages = [
            finding.message
            for finding in integrity.check_source_manifest(self.paper, "paper draft")
        ]
        self.assertTrue(
            any("must explicitly set source_coverage_mode" in message for message in closeout_messages),
            closeout_messages,
        )
        self.assertFalse(
            any("must explicitly set source_coverage_mode" in message for message in draft_messages),
            draft_messages,
        )

    def test_named_result_receipt_error_is_not_reported_twice(self) -> None:
        self.write_map({"renamable_named_item": self.named_contract_item()})
        map_path = self.audit / "paper_statement_map.json"
        payload = json.loads(map_path.read_text(encoding="utf-8"))
        payload.pop("source_named_result_inventory_review")
        map_path.write_text(json.dumps(payload), encoding="utf-8")

        messages = [
            finding.message
            for finding in integrity.check_source_manifest(self.paper, "formalized")
        ]
        receipt_messages = [
            message
            for message in messages
            if "source_named_result_inventory_review" in message
        ]
        self.assertEqual(len(receipt_messages), 1, messages)

    def test_partial_or_conditional_status_can_defer_named_result_receipt(self) -> None:
        """Only a full closeout claims a complete named-result inventory."""

        self.write_map({"renamable_named_item": self.named_contract_item()})
        map_path = self.audit / "paper_statement_map.json"
        payload = json.loads(map_path.read_text(encoding="utf-8"))
        payload.pop("source_named_result_inventory_review")
        map_path.write_text(json.dumps(payload), encoding="utf-8")

        for status in ("partially formalized", "conditional"):
            with self.subTest(status=status):
                self.assertEqual(
                    integrity.source_named_result_inventory_findings(
                        self.paper,
                        status,
                        map_path,
                        payload,
                    ),
                    [],
                )

        full_messages = [
            finding.message
            for finding in integrity.source_named_result_inventory_findings(
                self.paper,
                "formalized",
                map_path,
                payload,
            )
        ]
        self.assertTrue(
            any("source_named_result_inventory_review" in message for message in full_messages),
            full_messages,
        )

    def test_receipt_environment_alias_is_source_pinned_and_parser_validated(self) -> None:
        self.source = self.paper / "source.tex"
        self.source.write_text(
            "\\begin{customresult}\\label{custom:main}\n"
            "Every admissible input has a witness.\n"
            "\\end{customresult}\n",
            encoding="utf-8",
        )
        self.write_map(
            {
                "opaque_navigation_key": {
                    "source_kind": "claim",
                    "claim_bearing": True,
                    "source_location": "source.tex:1-3",
                    "source_anchor_evidence": [self.quote(1, 3)],
                }
            },
            named_result_review_overrides={
                "environment_kinds": {"customresult": "claim"},
            },
        )
        # Updating the alias table changes the source-only index, so refresh
        # the receipt with the resulting presentation digest.
        map_path = self.audit / "paper_statement_map.json"
        payload = json.loads(map_path.read_text(encoding="utf-8"))
        review = payload["source_named_result_inventory_review"]
        assert isinstance(review, dict)
        review["discovered_named_result_sha256"] = (
            integrity.named_result_presentations_sha256(
                integrity.extract_named_result_presentations(
                    self.source.read_text(encoding="utf-8"),
                    source_format="tex",
                    environment_kinds={"customresult": "claim"},
                )
            )
        )
        map_path.write_text(json.dumps(payload), encoding="utf-8")

        self.assertEqual(
            integrity.source_named_result_inventory_findings(
                self.paper,
                "formalized",
                map_path,
                payload,
            ),
            [],
        )

        review["environment_kinds"] = {"customresult": "not_a_source_kind"}
        map_path.write_text(json.dumps(payload), encoding="utf-8")
        messages = [
            finding.message
            for finding in integrity.source_named_result_inventory_findings(
                self.paper,
                "formalized",
                map_path,
                payload,
            )
        ]
        self.assertEqual(
            len(
                [
                    message
                    for message in messages
                    if "presentation classification is invalid" in message
                ]
            ),
            1,
            messages,
        )

    def test_repeated_presentation_alias_requires_distinct_matching_source_pins(
        self,
    ) -> None:
        """Aliases reconcile source presentations, but cannot hide a new claim."""

        self.source.write_text(
            "Theorem 1. Every admissible input has a witness.\n"
            "Theorem 1. Every admissible input has a witness.\n"
            "Theorem 2. Every admissible input has two witnesses.\n",
            encoding="utf-8",
        )
        alias = {
            "source_kind": "theorem",
            "claim_bearing": True,
            "source_location": "source.txt:2",
            "source_anchor_evidence": [self.quote(2)],
            "source_presentation_alias": {
                "schema": 1,
                "relation": "repeated_source_presentation",
                "canonical_source_item": "canonical_theorem_one",
                "semantic_basis": (
                    "The two pinned presentations have the same displayed "
                    "hypotheses, scope, and conclusion."
                ),
                "validator": "fixture source-only reconciliation",
                "validated_at": "2026-07-27T12:00:00Z",
            },
        }
        items = {
            "canonical_theorem_one": {
                "source_kind": "theorem",
                "claim_bearing": True,
                "source_location": "source.txt:1",
                "source_anchor_evidence": [self.quote(1)],
            },
            "theorem_two": {
                "source_kind": "theorem",
                "claim_bearing": True,
                "source_location": "source.txt:3",
                "source_anchor_evidence": [self.quote(3)],
            },
            "appendix_restatement": alias,
        }
        self.write_map(items)
        map_path = self.audit / "paper_statement_map.json"
        payload = json.loads(map_path.read_text(encoding="utf-8"))

        self.assertEqual(
            integrity.source_named_result_inventory_findings(
                self.paper, "formalized", map_path, payload
            ),
            [],
        )

        with self.subTest("same_source_span_is_not_a_repeated_presentation"):
            invalid = json.loads(json.dumps(payload))
            invalid["items"]["appendix_restatement"]["source_anchor_evidence"] = [
                self.quote(1)
            ]
            messages = [
                finding.message
                for finding in integrity.source_named_result_inventory_findings(
                    self.paper, "formalized", map_path, invalid
                )
            ]
            self.assertTrue(
                any("must anchor a distinct source presentation" in message for message in messages),
                messages,
            )

        with self.subTest("cross_result_canonical_pin_is_rejected"):
            invalid = json.loads(json.dumps(payload))
            invalid["items"]["appendix_restatement"]["source_presentation_alias"][
                "canonical_source_item"
            ] = "theorem_two"
            messages = [
                finding.message
                for finding in integrity.source_named_result_inventory_findings(
                    self.paper, "formalized", map_path, invalid
                )
            ]
            self.assertTrue(
                any("does not preserve the canonical visible source result label" in message for message in messages),
                messages,
            )

    def test_explicitly_renumbered_restatement_requires_source_relation_evidence(
        self,
    ) -> None:
        """A different visible label is reusable only when source text says so."""

        self.source.write_text(
            "Theorem 1. Every admissible input has a witness.\n"
            "We restate Theorem 1 formally as Theorem 2.\n"
            "Theorem 2. Every admissible input has a witness.\n",
            encoding="utf-8",
        )
        items = {
            "canonical_result": {
                "source_kind": "theorem",
                "claim_bearing": True,
                "source_location": "source.txt:3",
                "source_anchor_evidence": [self.quote(3)],
            },
            "renumbered_restatement": {
                "source_kind": "theorem",
                "claim_bearing": True,
                "source_location": "source.txt:1-2",
                "source_anchor_evidence": [self.quote(1, 2)],
                "source_presentation_alias": {
                    "schema": 1,
                    "relation": "repeated_source_presentation",
                    "canonical_source_item": "canonical_result",
                    "label_relation": "source_explicit_renumbered_restatement",
                    "source_restatement_evidence": self.quote(2),
                    "semantic_basis": (
                        "The source itself says that Theorem 2 restates Theorem 1."
                    ),
                    "validator": "fixture source-only reconciliation",
                    "validated_at": "2026-07-27T12:00:00Z",
                },
            },
        }
        self.write_map(items)
        map_path = self.audit / "paper_statement_map.json"
        payload = json.loads(map_path.read_text(encoding="utf-8"))

        self.assertEqual(
            integrity.source_named_result_inventory_findings(
                self.paper, "formalized", map_path, payload
            ),
            [],
        )

        invalid = json.loads(json.dumps(payload))
        invalid["items"]["renumbered_restatement"][
            "source_presentation_alias"
        ]["source_restatement_evidence"] = self.quote(1)
        messages = [
            finding.message
            for finding in integrity.source_named_result_inventory_findings(
                self.paper, "formalized", map_path, invalid
            )
        ]
        self.assertTrue(
            any("does not materially state a restatement" in message for message in messages),
            messages,
        )

    def test_named_open_problem_requires_explicit_nonproof_disposition(self) -> None:
        self.source.write_text(
            "Conjecture 1. Every admissible input has a witness.\n",
            encoding="utf-8",
        )
        self.write_map(
            {
                "opaque_source_navigation": {
                    "source_kind": "open_problem",
                    "claim_bearing": False,
                    "source_location": "source.txt:1",
                    "source_anchor_evidence": [self.quote(1)],
                    "source_scope_classification": (
                        "source_declared_open_nonresult_observation"
                    ),
                    "coverage_status": "source_declared_open",
                    "protocol_role": "source_declared_open",
                    "scope_reason": "The paper presents this as an open conjecture.",
                    "source_evidence": "Conjecture 1 in the source text.",
                }
            }
        )

        self.assertEqual(
            integrity.check_source_manifest(self.paper, "formalized"), []
        )

        map_path = self.audit / "paper_statement_map.json"
        payload = json.loads(map_path.read_text(encoding="utf-8"))
        item = payload["items"]["opaque_source_navigation"]
        assert isinstance(item, dict)
        item["claim_bearing"] = True
        map_path.write_text(json.dumps(payload), encoding="utf-8")
        messages = [
            finding.message
            for finding in integrity.check_source_manifest(self.paper, "formalized")
        ]
        self.assertTrue(
            any("named open presentation" in message for message in messages),
            messages,
        )


if __name__ == "__main__":
    unittest.main()
