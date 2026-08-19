from __future__ import annotations

import hashlib
import tempfile
import unittest
from pathlib import Path

from scripts import prepare_v11_source_map as preparer
from scripts.source_coverage_scope import source_item_scope_classification_errors


class PrepareV11SourceMapTests(unittest.TestCase):
    def test_anchor_replacement_uses_the_configured_exact_source_span(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.tex").write_text("Context.\nLemma: claim.\n", encoding="utf-8")
            prepared = preparer.prepare(
                {
                    "paper": "Fixture",
                    "items": {
                        "claim": {
                            "source_kind": "lemma",
                            "source_location": "source.tex:1-2",
                            "lean_declarations": ["Fixture.PaperInterface.claim"],
                        }
                    },
                },
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "include_specs": ["claim"],
                    "replace_source_item_anchors": {"claim": "source.tex:2"},
                },
                folder=folder,
            )
        anchor = prepared["items"]["claim"]["source_anchor_evidence"][0]
        self.assertEqual((anchor["line_start"], anchor["line_end"]), (2, 2))

    def test_add_source_item_pins_the_configured_source_span(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.tex").write_text("Lemma: source support.\n", encoding="utf-8")
            prepared = preparer.prepare(
                {"paper": "Fixture", "items": {}},
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "include_specs": [],
                    "add_source_items": {
                        "support_lemma": {
                            "statement": "Lemma: source support.",
                            "source_kind": "lemma",
                            "source_location": "source.tex:1",
                            "source_note": "This named lemma is recorded as source proof support.",
                            "source_status": "support_only",
                            "support_lean_declarations": ["Fixture.support"],
                        }
                    },
                },
                folder=folder,
            )
        item = prepared["items"]["support_lemma"]
        self.assertTrue(item["claim_bearing"])
        self.assertEqual(item["source_status"], "support_only")
        self.assertEqual(item["source_anchor_evidence"][0]["line_start"], 1)

    def test_support_only_unnamed_context_remains_nonclaim(self) -> None:
        """A local proof observation is not promoted merely by support status."""
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.tex").write_text(
                "A local proof observation.\n", encoding="utf-8"
            )
            prepared = preparer.prepare(
                {"paper": "Fixture", "items": {}},
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "include_specs": [],
                    "add_source_items": {
                        "local_observation": {
                            "statement": "A local proof observation.",
                            "source_kind": "remark",
                            "source_location": "source.tex:1",
                            "source_note": "This is local proof support rather than a source claim.",
                            "source_status": "support_only",
                            "claim_bearing": False,
                            "support_lean_declarations": ["Fixture.local_observation"],
                        }
                    },
                },
                folder=folder,
            )
        item = prepared["items"]["local_observation"]
        self.assertFalse(item["claim_bearing"])
        self.assertEqual(item["inventory_role"], "proof_support")

    def test_merge_source_items_is_idempotent(self) -> None:
        """A rerun does not append the same merged-source note again."""
        config = {
            "paper": "Fixture",
            "namespace": "Fixture",
            "include_specs": ["claim"],
            "merge_source_items": {"claim": ["context"]},
        }
        first = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "claim": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:1",
                        "lean_declarations": ["Fixture.PaperInterface.claim"],
                    },
                    "context": {
                        "source_kind": "definition",
                        "source_location": "source.tex:2",
                    },
                },
            },
            config,
        )
        second = preparer.prepare(first, config)
        note = second["items"]["claim"].get("source_note", "")
        self.assertEqual(note.count("The raw source bundle also includes"), 1)

    def test_retired_non_source_bridge_requires_a_retained_source_item(self) -> None:
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "source_claim": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:1",
                        "lean_declarations": ["Fixture.PaperInterface.claim"],
                    },
                    "implementation_bridge": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:2",
                        "lean_declarations": ["Fixture.PaperInterface.bridge"],
                    },
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["claim"],
                "retire_non_source_items": {
                    "implementation_bridge": {
                        "kind": "formalization_bridge",
                        "replacement_source_item": "source_claim",
                        "reason": "The bridge is an implementation lemma, not a source presentation.",
                    }
                },
            },
        )
        self.assertNotIn("implementation_bridge", prepared["items"])
        self.assertIn("source_claim", prepared["items"])

    def test_unselected_source_claims_and_scope_exclusions_remain_claim_bearing(self) -> None:
        """A v11 disposition is an audit obligation, not a semantic suppression."""
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "selected": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:1",
                        "lean_declarations": ["Fixture.PaperInterface.selected"],
                    },
                    "named_result": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:4",
                        # Simulate a previously contaminated v11 map: the
                        # source text itself still makes this a named result.
                        "statement": "Theorem 1. Every feasible input has an allocation.",
                        "claim_bearing": False,
                    },
                    "retained_source_claim": {
                        "source_kind": "prose_assertion",
                        "source_location": "source.tex:8",
                        "statement": "The source asserts a visible model conclusion.",
                        "claim_bearing": True,
                    },
                    "approved_exclusion": {
                        "source_kind": "example",
                        "source_location": "source.tex:12",
                        "statement": "The paper reports this numerical example.",
                        "claim_bearing": False,
                    },
                    "context_only": {
                        "source_kind": "remark",
                        "source_location": "source.tex:16",
                        "statement": "This is contextual background only.",
                        "claim_bearing": False,
                    },
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["selected"],
                "unselected_item_dispositions": {
                    "named_result": {
                        "inventory_role": "pending_v11_surface_migration",
                        "scope_disposition": "requires_dedicated_v11_spec",
                        "reason": "A dedicated Spec remains required.",
                    },
                    "retained_source_claim": {
                        "inventory_role": "pending_v11_surface_migration",
                        "scope_disposition": "requires_dedicated_v11_spec",
                        "reason": "A dedicated Spec remains required.",
                    },
                    "approved_exclusion": {
                        "inventory_role": "source_scope_exclusion",
                        "scope_disposition": "user_approved_scope_exclusion",
                        "reason": "The source claim is explicitly out of scope.",
                    },
                    "context_only": {
                        "inventory_role": "source_context_observation",
                        "scope_disposition": "not_a_paper_theorem_target",
                        "reason": "This row is context rather than a claim.",
                    },
                },
            },
        )

        items = prepared["items"]
        self.assertTrue(items["named_result"]["claim_bearing"])
        self.assertEqual(
            source_item_scope_classification_errors(items["named_result"]), []
        )
        self.assertTrue(items["retained_source_claim"]["claim_bearing"])
        self.assertTrue(items["approved_exclusion"]["claim_bearing"])
        self.assertFalse(items["context_only"]["claim_bearing"])

    def test_unselected_reconciled_prose_definition_remains_claim_bearing(self) -> None:
        """A source-only prose-definition record cannot disappear in v11 prep."""

        statement = "For each S, r_t(S) is the type-t count divided by |S|."
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "selected": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:1",
                        "lean_declarations": ["Fixture.PaperInterface.selected"],
                    },
                    "prose_definition": {
                        "source_kind": "definition",
                        "source_location": "source.tex:8",
                        "statement": statement,
                        "claim_bearing": False,
                        "source_prose_definition_reconciliation": {
                            "schema": 2,
                            "relation": "source_item_represents_prose_definition",
                            "presentation_sha256": "a" * 64,
                            "source_item_statement_sha256": hashlib.sha256(
                                " ".join(statement.split()).encode("utf-8")
                            ).hexdigest(),
                            "judgment": "semantically_equivalent",
                            "semantic_basis": "The source prose defines this exact ratio.",
                            "validator": "independent source-only definition review",
                            "validator_type": "human",
                            "validated_at": "2026-08-18T00:00:00Z",
                        },
                    },
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["selected"],
                "unselected_item_dispositions": {
                    "prose_definition": {
                        "inventory_role": "pending_v11_surface_migration",
                        "scope_disposition": "requires_dedicated_v11_spec",
                        "reason": "A transparent Spec remains required.",
                    }
                },
            },
        )

        self.assertTrue(prepared["items"]["prose_definition"]["claim_bearing"])

    def test_presentation_alias_drops_stale_source_spec_correspondence(self) -> None:
        """A repeated presentation cannot retain a second claim-level binding."""

        prepared = preparer.prepare(
            {
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
                        "source_spec_correspondence": {
                            "schema": 1,
                            "source_claim_atoms": [],
                            "direct_declaration": "Fixture.PaperInterface.old_duplicateSpec",
                        },
                    },
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["claim"],
                "presentation_aliases": {
                    "repeat": {
                        "canonical_source_item": "canonical",
                        "semantic_basis": "Both source presentations state the same theorem.",
                    }
                },
            },
        )

        self.assertNotIn(
            "source_spec_correspondence", prepared["items"]["repeat"]
        )

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

    def test_definition_reconciliation_is_preserved_by_preparation(self) -> None:
        statement = "The source predicate is exactly the displayed relation."
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "definition": {
                        "statement": statement,
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
                "prose_definition_reconciliations": {
                    "definition": {
                        "presentation_sha256": "a" * 64,
                        "semantic_basis": (
                            "The literal source definition is represented by the "
                            "selected source-map statement."
                        ),
                        "validator": "independent definition reviewer",
                        "validator_type": "agent",
                        "validated_at": "2026-08-19T00:00:00Z",
                    }
                },
            },
        )
        reconciliation = prepared["items"]["definition"][
            "source_prose_definition_reconciliation"
        ]
        self.assertEqual(reconciliation["presentation_sha256"], "a" * 64)
        self.assertEqual(
            reconciliation["source_item_statement_sha256"],
            hashlib.sha256(statement.encode("utf-8")).hexdigest(),
        )

    def test_existing_v11_proof_endpoint_is_preserved_without_reconfiguration(self) -> None:
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "claim": {
                        "source_kind": "theorem",
                        "source_location": "source.tex:1",
                        "lean_declarations": ["Fixture.PaperInterface.claim"],
                        "semantic_contract": {
                            "spec_declaration": "Fixture.PaperInterface.claimSpec",
                            "evidence_declaration": "Fixture.PaperInterface.claimSpec_proof",
                        },
                    }
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "include_specs": ["claim"],
            },
        )
        self.assertEqual(
            prepared["items"]["claim"]["semantic_contract"]["evidence_declaration"],
            "Fixture.PaperInterface.claimSpec_proof",
        )

    def test_root_interface_contract_and_initialized_atom_keep_the_exact_anchor(self) -> None:
        prepared = preparer.prepare(
            {
                "paper": "Fixture",
                "items": {
                    "claim": {
                        "statement": "The source predicate is exactly the displayed relation.",
                        "source_kind": "definition",
                        "source_location": "source.txt:4-5",
                        "source_anchor_evidence": [
                            {
                                "path": "source.txt",
                                "line_start": 4,
                                "line_end": 5,
                                "quoted_text": "Source relation.",
                                "quoted_text_sha256": hashlib.sha256(
                                    b"Source relation."
                                ).hexdigest(),
                            }
                        ],
                        "lean_declarations": ["Fixture.claim"],
                    }
                },
            },
            {
                "paper": "Fixture",
                "namespace": "Fixture",
                "paper_interface_module": "",
                "include_specs": ["claim"],
                "evidence_declaration_for_spec": {"claim": "claimSpec_proof"},
                "initialize_selected_source_claim_atoms": True,
            },
        )
        item = prepared["items"]["claim"]
        self.assertEqual(item["semantic_contract"]["spec_declaration"], "Fixture.claimSpec")
        self.assertEqual(
            item["semantic_contract"]["evidence_declaration"], "Fixture.claimSpec_proof"
        )
        self.assertEqual(item["source_claim_atoms"][0]["source_locator"], "source.txt:4-5")
        self.assertEqual(
            item["source_claim_atoms"][0]["reviewed_lean_route"],
            "Fixture.claimSpec_proof",
        )

    def test_explicit_atom_selects_statement_anchor_from_multi_span_source_item(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary)
            (folder / "source.tex").write_text(
                "Statement span.\nProof support span.\n", encoding="utf-8"
            )
            prepared = preparer.prepare(
                {
                    "paper": "Fixture",
                    "items": {
                        "claim": {
                            "statement": "The displayed statement is the source claim.",
                            "source_kind": "theorem",
                            "source_location": "source.tex:1; source.tex:2",
                            "lean_declarations": ["Fixture.claim"],
                            "source_anchor_evidence": [
                                {"path": "source.tex"},
                                {"path": "source.tex"},
                            ],
                        }
                    },
                },
                {
                    "paper": "Fixture",
                    "namespace": "Fixture",
                    "paper_interface_module": "",
                    "include_specs": ["claim"],
                    "evidence_declaration_for_spec": {"claim": "claimSpec_proof"},
                    "explicit_source_claim_atoms": {
                        "claim": {
                            "id": "claim",
                            "source_locator": "source.tex:1",
                            "semantic_claim": "The displayed statement is the source claim.",
                        }
                    },
                    "initialize_selected_source_claim_atoms": True,
                },
                folder=folder,
            )
        atom = prepared["items"]["claim"]["source_claim_atoms"][0]
        self.assertEqual(atom["source_locator"], "source.tex:1")
        self.assertEqual(atom["semantic_claim"], "The displayed statement is the source claim.")
        self.assertEqual(atom["reviewed_lean_route"], "Fixture.claimSpec_proof")

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
