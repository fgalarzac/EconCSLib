#!/usr/bin/env python3
"""Regressions for automatic v11 closeout reissue selection."""

from __future__ import annotations

import copy
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any, Callable, Mapping


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    if str(import_root) not in sys.path:
        sys.path.insert(0, str(import_root))

from theorem_realization_transition import (  # noqa: E402
    MATERIAL_ARTIFACT_PATHS,
    SOURCE_PROOF_FIDELITY_PATH,
    SOURCE_RECORD_PATH,
    STATEMENT_MAP_PATH,
    STATEMENT_REVIEW_PATH,
    STATUS_PATH,
    theorem_realization_reissue_requirement,
)
from formalization_protocol import (  # noqa: E402
    EXPECTED_LEGACY_V10_TRANSITION_BASELINE_COMMIT,
    EXPECTED_LEGACY_V10_TRANSITION_TRUSTED_REF,
    load_formalization_protocol,
)


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def trusted_git_test_protocol() -> dict[str, Any]:
    """Pin fixtures to the Git authority they exercise, independent of checkout."""

    payload = copy.deepcopy(load_formalization_protocol())
    payload["audit_versions"]["theorem_realization"][
        "legacy_v10_transition_baseline"
    ] = {
        "authority": "trusted_git_tree",
        "git_commit": EXPECTED_LEGACY_V10_TRANSITION_BASELINE_COMMIT,
        "trusted_ref": EXPECTED_LEGACY_V10_TRANSITION_TRUSTED_REF,
        "material_identity_schema": 1,
        "rule": "Test-only trusted Git baseline.",
    }
    return payload


def artifact_payloads() -> dict[str, dict[str, Any]]:
    quote = "Theorem 1: every fixture satisfies the advertised property."
    return {
        STATUS_PATH: {
            "status": "formalized",
            "formalization_scope": {
                "scope": "full named-theory paper",
                "whole_paper_closeout_claimed": True,
            },
        },
        STATEMENT_MAP_PATH: {
            "source_coverage_mode": "named_theoretical_statements",
            "items": {
                "theorem_one_navigation_key": {
                    "statement": quote,
                    "source_kind": "theorem",
                    "claim_bearing": True,
                    "source_status": "exact",
                    "lean_declarations": ["Fixture.theorem_one"],
                    "source_location": "paper.txt:1-1",
                    "source_anchor_evidence": [
                        {
                            "path": "paper.txt",
                            "line_start": 1,
                            "line_end": 1,
                            "quoted_text": quote,
                            "quoted_text_sha256": digest(quote),
                        }
                    ],
                }
            },
        },
        STATEMENT_REVIEW_PATH: {
            "items": {
                "theorem_one": {
                    "lean_signature_sha256": "a" * 64,
                    "paper_statement_sha256": digest(quote),
                    "source_routes": [
                        {
                            "source_item": "theorem_one_navigation_key",
                            "source_statement_sha256": digest(quote),
                            "semantic_relation": "equivalent",
                        }
                    ],
                }
            }
        },
        SOURCE_RECORD_PATH: {
            "boundary_input_items": [
                {
                    "row": "theorem_one",
                    "judgment_key": "theorem_one.hModel",
                    "expanded_input_type": "FixtureModel",
                    "kind": "semantic_unknown_nondata_premise",
                    "reviewed_elaborated_signature_identities": [
                        {
                            "qualified_declaration": "Fixture.theorem_one",
                            "elaborated_signature_sha256": "a" * 64,
                        }
                    ],
                    "source_contract_association": {
                        "source_item_identities": [
                            {"source_semantic_sha256": "b" * 64}
                        ]
                    },
                }
            ],
            "conclusion_dependency_items": [],
            "recursive_field_items": [],
            "semantic_model_items": [
                {
                    "row": "theorem_one",
                    "qualified_declaration": "Fixture.theorem_one",
                    "reviewed_elaborated_signature_identities": [
                        {
                            "qualified_declaration": "Fixture.theorem_one",
                            "elaborated_signature_sha256": "a" * 64,
                        }
                    ],
                    "expanded_lean_surface": {
                        "binder_domains": [
                            {
                                "names": "model",
                                "expanded_type": "FixtureModel",
                                "alpha_normalized_type": "FixtureModel",
                            }
                        ],
                        "terminal_result": {
                            "expanded_type": "AdvertisedProperty model",
                            "alpha_normalized_type": "AdvertisedProperty _b0",
                        },
                        "terminal_term_dependency_surface": {
                            "scan_complete": True,
                            "transparent_definitions": [
                                {
                                    "declaration": "Fixture.advertisedProperty",
                                    "body_sha256": "d" * 64,
                                    "parameter_types": [
                                        {
                                            "names": "model",
                                            "expanded_type": "FixtureModel",
                                            "alpha_normalized_type": "FixtureModel",
                                        }
                                    ],
                                    "result_type": {
                                        "expanded_type": "Prop",
                                        "alpha_normalized_type": "Prop",
                                    },
                                }
                            ],
                        },
                    },
                    "semantic_shape_flags": {"model_semantics": True},
                }
            ],
            "type_valued_certificate_result_items": [],
        },
        SOURCE_PROOF_FIDELITY_PATH: {
            "schema": 2,
            "model_conventions": [],
            "defects": [],
            "checked_proof_steps": [],
        },
    }


def two_item_artifact_payloads() -> dict[str, dict[str, Any]]:
    payloads = artifact_payloads()
    quote = "Theorem 2: every second fixture satisfies a different property."
    payloads[STATEMENT_MAP_PATH]["items"]["theorem_two_navigation_key"] = {
        "statement": quote,
        "source_kind": "theorem",
        "claim_bearing": True,
        "source_status": "exact",
        "lean_declarations": ["Fixture.theorem_two"],
        "source_location": "paper.txt:2-2",
        "source_anchor_evidence": [
            {
                "path": "paper.txt",
                "line_start": 2,
                "line_end": 2,
                "quoted_text": quote,
                "quoted_text_sha256": digest(quote),
            }
        ],
    }
    payloads[STATEMENT_REVIEW_PATH]["items"]["theorem_two"] = {
        "lean_signature_sha256": "c" * 64,
        "paper_statement_sha256": digest(quote),
        "source_routes": [
            {
                "source_item": "theorem_two_navigation_key",
                "source_statement_sha256": digest(quote),
                "semantic_relation": "equivalent",
            }
        ],
    }
    payloads[SOURCE_RECORD_PATH]["boundary_input_items"].append(
        {
            "row": "theorem_two",
            "judgment_key": "theorem_two.hModel",
            "expanded_input_type": "SecondFixtureModel",
            "kind": "semantic_unknown_nondata_premise",
            "reviewed_elaborated_signature_identities": [
                {
                    "qualified_declaration": "Fixture.theorem_two",
                    "elaborated_signature_sha256": "c" * 64,
                }
            ],
            "source_contract_association": {
                "source_item_identities": [
                    {"source_semantic_sha256": "e" * 64}
                ]
            },
        }
    )
    payloads[SOURCE_RECORD_PATH]["semantic_model_items"].append(
        {
            "row": "theorem_two",
            "qualified_declaration": "Fixture.theorem_two",
            "reviewed_elaborated_signature_identities": [
                {
                    "qualified_declaration": "Fixture.theorem_two",
                    "elaborated_signature_sha256": "c" * 64,
                }
            ],
            "record_input_bindings": [
                {
                    "alpha_normalized_type": "SecondFixtureModel",
                    "expanded_type": "SecondFixtureModel",
                    "record_roots": ["Fixture.SecondFixtureModel"],
                }
            ],
            "expanded_lean_surface": {
                "binder_domains": [
                    {
                        "names": "model",
                        "expanded_type": "SecondFixtureModel",
                        "alpha_normalized_type": "SecondFixtureModel",
                    }
                ],
                "terminal_result": {
                    "expanded_type": "SecondAdvertisedProperty model",
                    "alpha_normalized_type": "SecondAdvertisedProperty _b0",
                },
            },
        }
    )
    return payloads


class TheoremRealizationTransitionTests(unittest.TestCase):
    def write_artifacts(
        self, folder: Path, payloads: Mapping[str, Mapping[str, Any]]
    ) -> None:
        for relative in MATERIAL_ARTIFACT_PATHS:
            path = folder / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(
                json.dumps(payloads[relative], indent=2), encoding="utf-8"
            )

    def requirement(
        self,
        current: Mapping[str, Mapping[str, Any]],
        baseline: Mapping[str, Mapping[str, Any]] | None,
        *,
        mutate_folder: Callable[[Path], None] | None = None,
    ):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            folder = root / "papers" / "Fixture"
            self.write_artifacts(folder, current)
            if mutate_folder is not None:
                mutate_folder(folder)

            encoded_baseline = (
                {
                    relative: json.dumps(baseline[relative]).encode("utf-8")
                    for relative in MATERIAL_ARTIFACT_PATHS
                }
                if baseline is not None
                else {}
            )

            def reader(_commit: str, relative: str) -> bytes | None:
                return encoded_baseline.get(relative)

            return theorem_realization_reissue_requirement(
                root,
                folder,
                current[STATUS_PATH],
                git_blob_reader=reader,
                baseline_ancestor_verifier=lambda _commit, _ref: True,
                protocol=trusted_git_test_protocol(),
            )

    def test_unchanged_trusted_v10_closeout_does_not_require_v11(self) -> None:
        payloads = artifact_payloads()
        result = self.requirement(payloads, copy.deepcopy(payloads))

        self.assertFalse(result.required)
        self.assertEqual(
            result.current_material_identity_sha256,
            result.baseline_material_identity_sha256,
        )

    def test_paper_absent_from_transition_baseline_is_new_closeout(self) -> None:
        result = self.requirement(artifact_payloads(), None)

        self.assertTrue(result.required)
        self.assertIn("no completed closeout", result.reason)

    def test_raw_model_surface_change_does_not_alone_require_v11(self) -> None:
        baseline = artifact_payloads()
        current = copy.deepcopy(baseline)
        current[SOURCE_RECORD_PATH]["boundary_input_items"][0][
            "expanded_input_type"
        ] = "StrictlyDifferentFixtureModel"

        result = self.requirement(current, baseline)

        self.assertFalse(result.required)
        self.assertNotEqual(
            result.current_material_identity_sha256,
            result.baseline_material_identity_sha256,
        )
        self.assertIn("ordinary current raw-evidence gate remains mandatory", result.reason)

    def test_statement_semantic_change_requires_current_v10_not_v11(self) -> None:
        baseline = artifact_payloads()
        current = copy.deepcopy(baseline)
        current[STATEMENT_REVIEW_PATH]["items"]["theorem_one"][
            "lean_signature_sha256"
        ] = "c" * 64

        result = self.requirement(current, baseline)

        self.assertFalse(result.required)
        self.assertIn("current item-level v10", result.reason)

    def test_raw_transitive_model_surface_change_does_not_alone_require_v11(self) -> None:
        baseline = artifact_payloads()
        current = copy.deepcopy(baseline)
        current[SOURCE_RECORD_PATH]["semantic_model_items"][0][
            "expanded_lean_surface"
        ]["terminal_term_dependency_surface"]["transparent_definitions"][0][
            "body_sha256"
        ] = "e" * 64

        result = self.requirement(current, baseline)

        self.assertFalse(result.required)
        self.assertIn("ordinary current raw-evidence gate remains mandatory", result.reason)

    def test_cross_item_source_swap_requires_current_v10_not_v11(self) -> None:
        baseline = two_item_artifact_payloads()
        current = copy.deepcopy(baseline)
        first = current[STATEMENT_REVIEW_PATH]["items"]["theorem_one"]
        second = current[STATEMENT_REVIEW_PATH]["items"]["theorem_two"]
        first["source_routes"], second["source_routes"] = (
            second["source_routes"],
            first["source_routes"],
        )

        result = self.requirement(current, baseline)

        self.assertFalse(result.required)
        self.assertIn("current item-level v10", result.reason)

    def test_cross_item_raw_model_swap_does_not_alone_require_v11(self) -> None:
        baseline = two_item_artifact_payloads()
        current = copy.deepcopy(baseline)
        first, second = current[SOURCE_RECORD_PATH]["boundary_input_items"]
        first["expanded_input_type"], second["expanded_input_type"] = (
            second["expanded_input_type"],
            first["expanded_input_type"],
        )

        result = self.requirement(current, baseline)
        self.assertFalse(result.required)
        self.assertIn("ordinary current raw-evidence gate remains mandatory", result.reason)

    def test_cross_item_raw_statement_swap_does_not_alone_require_v11(self) -> None:
        baseline = two_item_artifact_payloads()
        current = copy.deepcopy(baseline)
        first, second = current[SOURCE_RECORD_PATH]["boundary_input_items"]
        first["reviewed_elaborated_signature_identities"], second[
            "reviewed_elaborated_signature_identities"
        ] = (
            second["reviewed_elaborated_signature_identities"],
            first["reviewed_elaborated_signature_identities"],
        )

        result = self.requirement(current, baseline)
        self.assertFalse(result.required)
        self.assertIn("ordinary current raw-evidence gate remains mandatory", result.reason)

    def test_proof_body_and_unrelated_docs_do_not_require_v11(self) -> None:
        payloads = artifact_payloads()

        def mutate(folder: Path) -> None:
            (folder / "PaperInterface.lean").write_text(
                "theorem theorem_one : True := by\n  exact True.intro\n",
                encoding="utf-8",
            )
            (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                "Audit prose changed without changing mathematics.\n",
                encoding="utf-8",
            )

        result = self.requirement(
            payloads, copy.deepcopy(payloads), mutate_folder=mutate
        )

        self.assertFalse(result.required)

    def test_navigation_renames_do_not_require_v11(self) -> None:
        baseline = artifact_payloads()
        current = copy.deepcopy(baseline)
        source_item = current[STATEMENT_MAP_PATH]["items"].pop(
            "theorem_one_navigation_key"
        )
        source_item["lean_declarations"] = ["Fixture.renamed_theorem"]
        current[STATEMENT_MAP_PATH]["items"]["renamed_source_key"] = source_item
        statement_item = current[STATEMENT_REVIEW_PATH]["items"].pop("theorem_one")
        current[STATEMENT_REVIEW_PATH]["items"]["renamed_theorem"] = statement_item
        statement_item["source_routes"][0]["source_item"] = "renamed_source_key"
        for item in current[SOURCE_RECORD_PATH]["boundary_input_items"]:
            item["row"] = "renamed_theorem"
            item["judgment_key"] = "renamed_theorem.hModel"
            item["reviewed_elaborated_signature_identities"][0][
                "qualified_declaration"
            ] = "Fixture.renamed_theorem"
        for item in current[SOURCE_RECORD_PATH]["semantic_model_items"]:
            item["row"] = "renamed_theorem"
            item["qualified_declaration"] = "Fixture.renamed_theorem"
            item["reviewed_elaborated_signature_identities"][0][
                "qualified_declaration"
            ] = "Fixture.renamed_theorem"

        result = self.requirement(current, baseline)

        self.assertFalse(result.required)

    def test_scope_target_declaration_rename_is_inert(self) -> None:
        baseline = artifact_payloads()
        baseline[STATUS_PATH]["formalization_scope"][
            "target_result_declarations"
        ] = ["Fixture.theorem_one"]
        current = copy.deepcopy(baseline)
        current[STATUS_PATH]["formalization_scope"][
            "target_result_declarations"
        ] = ["Fixture.renamed_theorem"]
        for item in current[SOURCE_RECORD_PATH]["boundary_input_items"]:
            item["reviewed_elaborated_signature_identities"][0][
                "qualified_declaration"
            ] = "Fixture.renamed_theorem"
        for item in current[SOURCE_RECORD_PATH]["semantic_model_items"]:
            item["qualified_declaration"] = "Fixture.renamed_theorem"
            item["reviewed_elaborated_signature_identities"][0][
                "qualified_declaration"
            ] = "Fixture.renamed_theorem"

        self.assertFalse(self.requirement(current, baseline).required)

    def test_material_scope_change_requires_current_v10_not_v11(self) -> None:
        baseline = artifact_payloads()
        current = copy.deepcopy(baseline)
        current[STATUS_PATH]["formalization_scope"]["scope"] = (
            "component-only named-theory evidence"
        )

        self.assertFalse(self.requirement(current, baseline).required)

    def test_legacy_implicit_whole_paper_scope_equals_explicit_role(self) -> None:
        baseline = artifact_payloads()
        baseline[STATUS_PATH]["formalization_scope"].pop(
            "whole_paper_closeout_claimed"
        )
        current = copy.deepcopy(baseline)
        current[STATUS_PATH]["formalization_scope"].update(
            {
                "scope_role": "whole_paper_closeout",
                "whole_paper_closeout_claimed": True,
            }
        )

        self.assertFalse(self.requirement(current, baseline).required)

        component = copy.deepcopy(current)
        component[STATUS_PATH]["formalization_scope"].update(
            {
                "scope_role": "component_evidence",
                "whole_paper_closeout_claimed": False,
            }
        )
        self.assertFalse(self.requirement(component, baseline).required)

    def test_selected_scope_target_change_requires_current_v10_not_v11(self) -> None:
        baseline = two_item_artifact_payloads()
        baseline[STATUS_PATH]["formalization_scope"][
            "target_result_declarations"
        ] = ["Fixture.theorem_one"]
        current = copy.deepcopy(baseline)
        current[STATUS_PATH]["formalization_scope"][
            "target_result_declarations"
        ] = ["Fixture.theorem_two"]

        self.assertFalse(self.requirement(current, baseline).required)

    def test_governing_correction_change_requires_current_v10_but_id_rename_is_inert(
        self,
    ) -> None:
        baseline = artifact_payloads()
        baseline[STATUS_PATH]["formalization_scope"].update(
            {
                "kind": "author_approved_corrected_model",
                "scope_id": "old-scope-id",
                "correction_ids": ["old-correction-id"],
            }
        )
        baseline[STATUS_PATH]["governing_corrections"] = [
            {
                "id": "old-correction-id",
                "clause": "The model parameter is strictly positive.",
                "relation": "Makes the source domain explicit.",
                "does_not_claim_archive_derivation": True,
            }
        ]

        renamed = copy.deepcopy(baseline)
        renamed[STATUS_PATH]["formalization_scope"]["scope_id"] = (
            "renamed-scope-id"
        )
        renamed[STATUS_PATH]["formalization_scope"]["correction_ids"] = [
            "renamed-correction-id"
        ]
        renamed[STATUS_PATH]["governing_corrections"][0]["id"] = (
            "renamed-correction-id"
        )
        self.assertFalse(self.requirement(renamed, baseline).required)

        changed = copy.deepcopy(renamed)
        changed[STATUS_PATH]["governing_corrections"][0]["clause"] = (
            "The model parameter is merely nonnegative."
        )
        self.assertFalse(self.requirement(changed, baseline).required)

    def test_audit_bookkeeping_changes_do_not_require_v11(self) -> None:
        baseline = artifact_payloads()
        current = copy.deepcopy(baseline)
        source_item = current[STATEMENT_MAP_PATH]["items"][
            "theorem_one_navigation_key"
        ]
        source_item["source_kind_validator"] = "new audit implementation"
        source_item["source_kind_validated_at"] = "2026-08-01T00:00:00Z"
        source_item["audit_note"] = "Rechecked without changing the source claim."
        current[STATEMENT_REVIEW_PATH]["validator"] = "replacement reviewer"
        current[SOURCE_RECORD_PATH]["semantic_model_items"][0][
            "semantic_shape_flags"
        ] = {"model_semantics": True, "new_detector": True}
        current[STATUS_PATH]["human_summary"] = "Updated closeout prose."

        result = self.requirement(current, baseline)

        self.assertFalse(result.required)

    def test_theorem_source_semantic_change_requires_current_v10_not_v11(self) -> None:
        baseline = artifact_payloads()
        current = copy.deepcopy(baseline)
        current[STATEMENT_MAP_PATH]["items"]["theorem_one_navigation_key"][
            "statement"
        ] = "Theorem 1: every fixture satisfies a materially different property."

        result = self.requirement(current, baseline)

        self.assertFalse(result.required)
        self.assertIn("current item-level v10", result.reason)

    def test_definition_only_review_change_does_not_require_v11(self) -> None:
        baseline = artifact_payloads()
        current = copy.deepcopy(baseline)
        current[STATEMENT_MAP_PATH]["items"]["definition_navigation_key"] = {
            "statement": "Definition 2: an auxiliary relation is well formed.",
            "source_kind": "definition",
            "source_status": "exact",
            "lean_declarations": ["Fixture.auxiliaryRelation"],
            "source_location": "paper.txt:2-2",
        }
        current[STATEMENT_REVIEW_PATH]["items"]["auxiliary_definition"] = {
            "lean_signature_sha256": "f" * 64,
            "paper_statement_sha256": digest(
                "Definition 2: an auxiliary relation is well formed."
            ),
        }

        result = self.requirement(current, baseline)

        self.assertFalse(result.required)
        self.assertIn("current item-level v10", result.reason)

    def test_route_incomplete_legacy_maps_use_full_statement_fallback(self) -> None:
        baseline = artifact_payloads()
        del baseline[STATEMENT_REVIEW_PATH]["items"]["theorem_one"][
            "source_routes"
        ]
        current = copy.deepcopy(baseline)
        current[STATEMENT_REVIEW_PATH]["items"]["theorem_one"][
            "lean_signature_sha256"
        ] = "f" * 64

        result = self.requirement(current, baseline)

        self.assertFalse(result.required)
        self.assertIn("current item-level v10", result.reason)

    def test_ledger_record_renames_are_semantically_inert(self) -> None:
        baseline = artifact_payloads()
        source_item = baseline[STATEMENT_MAP_PATH]["items"][
            "theorem_one_navigation_key"
        ]
        source_item["model_convention_ids"] = ["old-convention"]
        source_item["source_defect_id"] = "old-defect"
        fidelity = baseline[SOURCE_PROOF_FIDELITY_PATH]
        fidelity["model_conventions"] = [
            {
                "id": "old-convention",
                "classification": "source_model_clarification",
                "formal_meaning": "The parameter is positive.",
                "why_needed": "Needed for division.",
                "checked_scope": "OldNames.lean",
            }
        ]
        fidelity["defects"] = [
            {
                "id": "old-defect",
                "source_claim": "The printed weak inequality is a typo.",
                "resolution": "corrected_source_statement",
                "repair_obligation": "Use the strict inequality.",
            }
        ]
        current = copy.deepcopy(baseline)
        item = current[STATEMENT_MAP_PATH]["items"]["theorem_one_navigation_key"]
        item["model_convention_ids"] = ["renamed-convention"]
        item["source_defect_id"] = "renamed-defect"
        records = current[SOURCE_PROOF_FIDELITY_PATH]
        records["model_conventions"][0]["id"] = "renamed-convention"
        records["defects"][0]["id"] = "renamed-defect"

        self.assertFalse(self.requirement(current, baseline).required)

    def test_model_explanation_and_checked_route_edits_are_not_material(self) -> None:
        baseline = artifact_payloads()
        baseline[STATEMENT_MAP_PATH]["items"]["theorem_one_navigation_key"][
            "model_convention_ids"
        ] = ["convention"]
        baseline[SOURCE_PROOF_FIDELITY_PATH]["model_conventions"] = [
            {
                "id": "convention",
                "classification": "source_model_clarification",
                "formal_meaning": "The parameter is positive.",
                "why_needed": "Old explanation.",
                "checked_scope": "OldFile.oldName",
            }
        ]
        current = copy.deepcopy(baseline)
        record = current[SOURCE_PROOF_FIDELITY_PATH]["model_conventions"][0]
        record["why_needed"] = "Clearer explanation with the same meaning."
        record["checked_scope"] = "RenamedFile.renamedName"

        self.assertFalse(self.requirement(current, baseline).required)

        changed = copy.deepcopy(current)
        changed[SOURCE_PROOF_FIDELITY_PATH]["model_conventions"][0][
            "formal_meaning"
        ] = "The parameter is at least zero."
        self.assertFalse(self.requirement(changed, baseline).required)

    def test_untrusted_local_baseline_object_fails_closed(self) -> None:
        payloads = artifact_payloads()
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            folder = root / "papers" / "Fixture"
            self.write_artifacts(folder, payloads)
            encoded = {
                relative: json.dumps(payloads[relative]).encode("utf-8")
                for relative in MATERIAL_ARTIFACT_PATHS
            }
            result = theorem_realization_reissue_requirement(
                root,
                folder,
                payloads[STATUS_PATH],
                git_blob_reader=lambda _commit, relative: encoded.get(relative),
                baseline_ancestor_verifier=lambda _commit, _ref: False,
                protocol=trusted_git_test_protocol(),
            )

        self.assertTrue(result.required)
        self.assertIn("not an ancestor", result.reason)


if __name__ == "__main__":
    unittest.main()
