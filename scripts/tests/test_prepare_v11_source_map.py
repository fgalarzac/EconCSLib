from __future__ import annotations

import hashlib
import tempfile
import unittest
from pathlib import Path

from scripts import prepare_v11_source_map as preparer


class PrepareV11SourceMapTests(unittest.TestCase):
    def test_presentation_alias_cannot_retain_a_second_direct_route(self) -> None:
        source_map = {
            "paper": "Fixture",
            "items": {
                "canonical": {
                    "source_kind": "theorem",
                    "source_location": "source.tex:1",
                    "lean_declarations": ["Fixture.PaperInterface.claim"],
                },
                "repeat": {
                    "source_kind": "theorem",
                    "source_location": "source.tex:4",
                    "lean_declarations": ["Fixture.PaperInterface.old_duplicate"],
                    "proof_lean_declarations": ["Fixture.PaperInterface.old_duplicate"],
                    "support_lean_declarations": ["Fixture.PaperInterface.oldDuplicateSpec"],
                },
            },
        }
        prepared = preparer.prepare(
            source_map,
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["claim"],
                "presentation_aliases": {
                    "repeat": {
                        "canonical_source_item": "canonical",
                        "semantic_basis": "Both exact source presentations state the same theorem.",
                    }
                },
            },
        )
        alias = prepared["items"]["repeat"]
        self.assertNotIn("lean_declarations", alias)
        self.assertNotIn("proof_lean_declarations", alias)
        self.assertNotIn("support_lean_declarations", alias)
        self.assertNotIn("semantic_contract", alias)
        self.assertFalse(alias["claim_bearing"])
        self.assertEqual(alias["inventory_role"], "source_presentation_alias")
        self.assertEqual(
            alias["source_presentation_alias"]["validated_at"],
            "2026-08-18T00:00:00Z",
        )
        self.assertEqual(prepared["source_spec_correspondence_schema"], 1)

    def test_corrected_target_preserves_archival_statement_and_pins_basis(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            source = folder / "source.tex"
            source.write_text("Archival proposition.\n", encoding="utf-8")
            basis = folder / "docs.md"
            basis.write_text("Approved correction.\n", encoding="utf-8")
            prepared = preparer.prepare(
                {
                    "paper": "Fixture",
                    "items": {
                        "claim": {
                            "source_kind": "theorem",
                            "source_location": "source.tex:1",
                            "lean_declarations": ["Fixture.PaperInterface.claim"],
                        }
                    },
                },
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "include_specs": ["claim"],
                    "corrected_targets": {
                        "claim": {
                            "statement": "Approved corrected proposition.",
                            "archival_statement": "Archival proposition.",
                            "governing_defect_ids": ["FIXTURE-01"],
                            "archival_source_locator": "source.tex:1",
                            "source_note": "The archival wording is not equivalent to the approved target.",
                            "approval": {
                                "kind": "documented_source_correction",
                                "recorded_at": "2026-08-18",
                                "reference": "Fixture correction note.",
                                "artifact_path": "docs.md",
                            },
                        }
                    },
                },
                folder=folder,
            )
        item = prepared["items"]["claim"]
        target = item["corrected_target"]
        self.assertEqual(item["statement"], "Archival proposition.")
        self.assertEqual(item["coverage_status"], "corrected_source_statement")
        self.assertIs(target["archival_equivalence_claimed"], False)
        self.assertEqual(
            target["archival_source_quote_sha256"],
            hashlib.sha256(b"Archival proposition.").hexdigest(),
        )
        self.assertEqual(
            target["approval"]["artifact_sha256"],
            hashlib.sha256(b"Approved correction.\n").hexdigest(),
        )

    def test_explicit_realization_endpoint_is_recorded_in_contract(self) -> None:
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "definition": {
                        "source_kind": "definition",
                        "source_location": "source.tex:1",
                        "lean_declarations": ["Fixture.PaperInterface.definition"],
                    }
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["definition"],
                "evidence_declaration_for_spec": {
                    "definition": "definition_realizes_spec"
                },
            },
        )
        self.assertEqual(
            prepared["items"]["definition"]["semantic_contract"]["evidence_declaration"],
            "Fixture.PaperInterface.definition_realizes_spec",
        )

    def test_explicit_atomization_splits_a_compound_source_definition(self) -> None:
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "compound_definition": {
                        "source_kind": "definition",
                        "source_location": "source.tex:1-4",
                        "source_anchor_evidence": [{"path": "source.tex"}],
                        "lean_declarations": [
                            "Fixture.PaperInterface.first",
                            "Fixture.PaperInterface.second",
                        ],
                        "claim_bearing": True,
                    }
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["first", "second"],
                "atomize_source_items": {
                    "compound_definition": {
                        "reason": "The source defines the two model branches in one display.",
                        "items": {
                            "first_definition": {
                                "statement": "First branch.",
                                "source_note": "The first branch has its own semantic target.",
                                "lean_declarations": ["Fixture.PaperInterface.first"],
                            },
                            "second_definition": {
                                "statement": "Second branch.",
                                "source_note": "The second branch has its own semantic target.",
                                "lean_declarations": ["Fixture.PaperInterface.second"],
                            },
                        },
                    }
                },
            },
        )
        self.assertNotIn("compound_definition", prepared["items"])
        self.assertEqual(
            prepared["items"]["first_definition"]["semantic_contract"]["spec_declaration"],
            "Fixture.PaperInterface.firstSpec",
        )
        self.assertEqual(
            prepared["items"]["second_definition"]["source_atomization"]["parent_source_item"],
            "compound_definition",
        )

    def test_consolidation_restores_one_source_definition_and_exact_anchor(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.tex").write_text(
                "Definition: both branches are one claim.\n", encoding="utf-8"
            )
            prepared = preparer.prepare(
                {
                    "paper": "Fixture",
                    "items": {
                        "first_branch": {
                            "source_kind": "definition",
                            "source_location": "source.tex:1",
                            "lean_declarations": ["Fixture.PaperInterface.first"],
                        },
                        "second_branch": {
                            "source_kind": "definition",
                            "source_location": "source.tex:1",
                            "lean_declarations": ["Fixture.PaperInterface.second"],
                        },
                    },
                },
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "include_specs": ["definition"],
                    "evidence_declaration_for_spec": {
                        "definition": "definition_realizes_spec"
                    },
                    "evidence_mode_for_spec": {
                        "definition": "definitionally_realizes"
                    },
                    "consolidate_source_items": {
                        "definition": {
                            "source_items": ["first_branch", "second_branch"],
                            "statement": "Definition: both branches are one claim.",
                            "source_note": "The source has one definition with two semantic branches.",
                            "source_kind": "definition",
                            "source_location": "source.tex:1",
                            "lean_declarations": ["Fixture.PaperInterface.definition"],
                            "source_claim_atom": {
                                "id": "definition.combined",
                                "source_locator": "source.tex:1",
                                "semantic_claim": "The source definition contains both branches.",
                            },
                        }
                    },
                },
                folder=folder,
            )
        self.assertNotIn("first_branch", prepared["items"])
        self.assertNotIn("second_branch", prepared["items"])
        item = prepared["items"]["definition"]
        self.assertEqual(item["semantic_contract"]["evidence_mode"], "definitionally_realizes")
        self.assertEqual(item["source_anchor_evidence"][0]["quoted_text"], "Definition: both branches are one claim.")
        self.assertEqual(
            item["source_claim_atoms"][0]["reviewed_lean_route"],
            "Fixture.PaperInterface.definitionSpec",
        )


if __name__ == "__main__":
    unittest.main()
