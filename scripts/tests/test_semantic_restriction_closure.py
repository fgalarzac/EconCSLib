#!/usr/bin/env python3
"""Regression tests for occurrence-bound source-claim contracts."""

from __future__ import annotations

import copy
import importlib.util
import sys
import unittest
from dataclasses import replace
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
for path in (ROOT, ROOT / "scripts"):
    if str(path) not in sys.path:
        sys.path.insert(0, str(path))

import source_record_operational_prop_obligations as CONTRACT  # noqa: E402


SOURCE_ITEM = "fixture-source-item"
SOURCE_SHA = "a" * 64
STRUCTURAL_SHA = "b" * 64
SIGNATURE_SHA = "c" * 64
SOURCE_JUDGMENT = "fixture.source-model-input"


def component(
    *,
    component_sha: str,
    surface: str,
    source_key: str = SOURCE_JUDGMENT,
    role: str = "material",
) -> dict[str, object]:
    return {
        "judgment_key": "theorem-realization::input::" + component_sha,
        "source_judgment_key": source_key,
        "source_claim_component_role": role,
        "source_claim_component_sha256": component_sha,
        "structural_type_sha256": STRUCTURAL_SHA,
        "elaborated_signature_sha256": SIGNATURE_SHA,
        "type": surface,
        "proposition_sort": "false",
    }


def exact_contract(item: dict[str, object]) -> dict[str, object]:
    return {
        "schema": CONTRACT.SOURCE_CLAIM_SEMANTIC_CONTRACT_SCHEMA,
        "route": CONTRACT.EXACT_SOURCE_CLAIM_ROUTE,
        "component_sha256": str(item["source_claim_component_sha256"]),
        "structural_type_sha256": STRUCTURAL_SHA,
        "source_anchor": {
            "source_item_key": SOURCE_ITEM,
            "source_item_semantic_sha256": SOURCE_SHA,
            "source_locator": "source.tex:101",
            "source_formula": "The source fixes this exact component domain.",
            "semantic_match": "The generated component has the same source domain and role.",
        },
    }


def exact_judgment(item: dict[str, object]) -> dict[str, object]:
    return {
        "classification": "validated_source_assumption",
        "source_target_disposition": "literal_source_match",
        "source_claim_semantic_contract": exact_contract(item),
    }


def contract_errors(
    item: dict[str, object], judgment: dict[str, object], *, atom: bool = False
) -> list[str]:
    source_key = str(item["source_judgment_key"])
    component_sha = str(item["source_claim_component_sha256"])
    kwargs: dict[str, object] = {
        "source_item_semantic_sha256_by_key": {SOURCE_ITEM: SOURCE_SHA},
        "current_component_sha256s_by_source_judgment_key": {
            source_key: {component_sha}
        },
        "current_explicit_source_assumption_keys": {source_key},
    }
    if atom:
        contract = judgment["source_claim_semantic_contract"]
        assert isinstance(contract, dict)
        contract["source_claim_atom"] = {
            "source_item_key": SOURCE_ITEM,
            "id": "exact-domain-clause",
            "source_claim_atom_semantic_sha256": "d" * 64,
            "source_locator": "source.tex:101",
        }
        kwargs["require_source_claim_atom"] = True
        kwargs["current_source_claim_atom_receipts"] = {
            CONTRACT.SourceClaimAtomReceipt(
                source_item_key=SOURCE_ITEM,
                atom_id="exact-domain-clause",
                atom_semantic_sha256="d" * 64,
                source_locator="source.tex:101",
            )
        }
    return CONTRACT.complete_source_claim_semantic_contract_errors(
        item, judgment, **kwargs  # type: ignore[arg-type]
    )


def strict_occurrence_contract_errors(
    item: dict[str, object],
    contract: dict[str, object],
    *,
    current_correction_identity: dict[str, object] | None,
    classification: str = "proved_from_primitives",
) -> list[str]:
    atom = {
        "source_item_key": SOURCE_ITEM,
        "id": "source-clause",
        "source_claim_atom_semantic_sha256": "d" * 64,
        "source_locator": "source.tex:101",
    }
    contract["source_claim_atom"] = atom
    return CONTRACT.complete_source_claim_semantic_contract_errors(
        item,
        {
            "classification": classification,
            "source_claim_semantic_contract": contract,
        },
        source_item_semantic_sha256_by_key={SOURCE_ITEM: SOURCE_SHA},
        current_component_sha256s_by_source_judgment_key={
            str(item["source_judgment_key"]): {
                str(item["source_claim_component_sha256"])
            }
        },
        current_source_claim_atom_receipts={
            CONTRACT.SourceClaimAtomReceipt(
                source_item_key=SOURCE_ITEM,
                atom_id="source-clause",
                atom_semantic_sha256="d" * 64,
                source_locator="source.tex:101",
            )
        },
        require_source_claim_atom=True,
        current_source_correction_identity_by_key={
            SOURCE_ITEM: current_correction_identity
        },
    )


class SourceClaimSemanticContractTests(unittest.TestCase):
    def test_nonproposition_domains_require_a_contract(self) -> None:
        surfaces = (
            "Fin n",
            "CustomCarrier",
            "CustomCarrier -> Real",
            "CustomCarrier -> Prop",
            "Fintype CustomCarrier",
        )
        for index, surface in enumerate(surfaces):
            item = component(component_sha=f"{index + 1:064x}", surface=surface)
            bare = {
                "classification": "nonpropositional_witness_data",
                "source_location": "source.tex:101",
            }
            with self.subTest(surface=surface):
                self.assertTrue(contract_errors(item, bare))
                self.assertEqual(contract_errors(item, exact_judgment(item)), [])

    def test_schema_one_source_routes_do_not_depend_on_classification_labels(self) -> None:
        item = component(component_sha="f" * 64, surface="CustomCarrier -> Prop")
        source_key = str(item["source_judgment_key"])
        exact = exact_contract(item)
        correction = {
            **exact,
            "route": CONTRACT.APPROVED_SOURCE_CORRECTION_ROUTE,
            "additional_assumption": {
                "statement": "The endpoint is evaluated under the stated regularity condition.",
                "justification": "This condition is explicit in the post-formalization report.",
                "report_locator": "POST_FORMALIZATION_AUDIT.md:12",
            },
        }
        for contract in (exact, correction):
            for classification in (
                "validated_source_assumption",
                "approved_corrected_condition",
                "approved_formalization_regularity",
                "arbitrary_reviewer_label",
                "",
            ):
                judgment = {
                    "classification": classification,
                    "source_claim_semantic_contract": contract,
                }
                with self.subTest(route=contract["route"], classification=classification):
                    self.assertEqual(
                        CONTRACT.complete_source_claim_semantic_contract_errors(
                            item,
                            judgment,
                            source_item_semantic_sha256_by_key={SOURCE_ITEM: SOURCE_SHA},
                            current_component_sha256s_by_source_judgment_key={
                                source_key: {"f" * 64}
                            },
                            current_source_disposition_keys={source_key},
                        ),
                        [],
                    )

    def test_strict_exact_contract_is_the_constructed_output_disposition(self) -> None:
        item = component(component_sha="6" * 64, surface="ConstructedCarrier")
        item["source_component_section"] = "opaque_generated_surface"
        for classification in (
            "proved_from_primitives",
            "semantic_model_review",
            "renamed_reviewer_label",
            "",
        ):
            with self.subTest(classification=classification):
                self.assertEqual(
                    strict_occurrence_contract_errors(
                        item,
                        exact_contract(item),
                        current_correction_identity=None,
                        classification=classification,
                    ),
                    [],
                )

    def test_strict_corrected_output_pins_current_source_correction(self) -> None:
        item = component(component_sha="7" * 64, surface="ConstructedCarrier")
        current_identity = {
            "corrected_target_sha256": "e" * 64,
            "governing_defect_ids": ("DEFECT-A",),
        }
        contract = exact_contract(item)
        contract.update(
            {
                "route": CONTRACT.APPROVED_SOURCE_CORRECTION_ROUTE,
                "source_correction": {
                    "corrected_target_sha256": "e" * 64,
                    "governing_defect_ids": ["DEFECT-A"],
                },
                "additional_assumption": {
                    "statement": "The corrected endpoint uses the repaired source domain.",
                    "justification": "The current correction ledger authorizes this target.",
                    "report_locator": "POST_FORMALIZATION_AUDIT.md:12",
                },
            }
        )
        self.assertEqual(
            strict_occurrence_contract_errors(
                item, contract, current_correction_identity=current_identity
            ),
            [],
        )

        for field, stale_value in (
            ("corrected_target_sha256", "f" * 64),
            ("governing_defect_ids", ["DEFECT-OTHER"]),
        ):
            stale = copy.deepcopy(contract)
            source_correction = stale["source_correction"]
            assert isinstance(source_correction, dict)
            source_correction[field] = stale_value
            with self.subTest(field=field):
                self.assertTrue(
                    strict_occurrence_contract_errors(
                        item,
                        stale,
                        current_correction_identity=current_identity,
                    )
                )

    def test_exact_clause_inside_corrected_item_requires_unaffected_receipt(
        self,
    ) -> None:
        item = component(component_sha="8" * 64, surface="LiteralPremise")
        current_identity = {
            "corrected_target_sha256": "e" * 64,
            "governing_defect_ids": ("DEFECT-A",),
        }
        missing = exact_contract(item)
        errors = strict_occurrence_contract_errors(
            item, missing, current_correction_identity=current_identity
        )
        self.assertTrue(
            any("unaffected_by_source_correction" in error for error in errors),
            errors,
        )

        exact = exact_contract(item)
        exact["unaffected_by_source_correction"] = {
            "corrected_target_sha256": "e" * 64,
            "governing_defect_ids": ["DEFECT-A"],
            "statement": "This quantified premise is literal source content.",
            "justification": (
                "The correction changes the conclusion domain, not this premise."
            ),
            "report_locator": "POST_FORMALIZATION_AUDIT.md:19",
        }
        self.assertEqual(
            strict_occurrence_contract_errors(
                item, exact, current_correction_identity=current_identity
            ),
            [],
        )

        for field, stale_value in (
            ("corrected_target_sha256", "f" * 64),
            ("governing_defect_ids", ["DEFECT-OTHER"]),
            ("statement", "Fixture.Route.name"),
            ("report_locator", "not an exact locator"),
        ):
            stale = copy.deepcopy(exact)
            unaffected = stale["unaffected_by_source_correction"]
            assert isinstance(unaffected, dict)
            unaffected[field] = stale_value
            with self.subTest(field=field):
                self.assertTrue(
                    strict_occurrence_contract_errors(
                        item,
                        stale,
                        current_correction_identity=current_identity,
                    )
                )

    def test_strict_source_correction_route_swaps_fail_closed(self) -> None:
        item = component(component_sha="9" * 64, surface="OccurrencePayload")
        current_identity = {
            "corrected_target_sha256": "e" * 64,
            "governing_defect_ids": ("DEFECT-A",),
        }
        exact = exact_contract(item)
        exact["unaffected_by_source_correction"] = {
            "corrected_target_sha256": "e" * 64,
            "governing_defect_ids": ["DEFECT-A"],
            "statement": "This premise remains literal source content.",
            "justification": "The governing defect changes a different clause.",
            "report_locator": "POST_FORMALIZATION_AUDIT.md:23",
        }
        exact_swapped = copy.deepcopy(exact)
        exact_swapped["route"] = CONTRACT.APPROVED_SOURCE_CORRECTION_ROUTE
        exact_swapped["additional_assumption"] = {
            "statement": "A repaired target.",
            "justification": "Recorded in the report.",
            "report_locator": "POST_FORMALIZATION_AUDIT.md:23",
        }
        self.assertTrue(
            strict_occurrence_contract_errors(
                item,
                exact_swapped,
                current_correction_identity=current_identity,
            )
        )

        correction = exact_contract(item)
        correction.update(
            {
                "route": CONTRACT.APPROVED_SOURCE_CORRECTION_ROUTE,
                "source_correction": {
                    "corrected_target_sha256": "e" * 64,
                    "governing_defect_ids": ["DEFECT-A"],
                },
                "additional_assumption": {
                    "statement": "A repaired target.",
                    "justification": "Recorded in the report.",
                    "report_locator": "POST_FORMALIZATION_AUDIT.md:23",
                },
            }
        )
        correction_swapped = copy.deepcopy(correction)
        correction_swapped["route"] = CONTRACT.EXACT_SOURCE_CLAIM_ROUTE
        self.assertTrue(
            strict_occurrence_contract_errors(
                item,
                correction_swapped,
                current_correction_identity=current_identity,
            )
        )
        self.assertTrue(
            strict_occurrence_contract_errors(
                item, correction, current_correction_identity=None
            )
        )

    def test_source_domain_receipt_closes_a_model_component(self) -> None:
        item = component(component_sha="1" * 64, surface="Fin n -> Real")
        source_key = str(item["source_judgment_key"])
        judgment = {
            "classification": "semantic_model_review",
            "source_claim_semantic_contract": {
                "schema": 1,
                "route": CONTRACT.SOURCE_DOMAIN_CORRESPONDENCE_ROUTE,
                "component_sha256": "1" * 64,
                "structural_type_sha256": STRUCTURAL_SHA,
                "source_domain_correspondence": {
                    "component_sha256": "1" * 64,
                    "source_model_judgment_key": "semantic-model::fixture",
                },
            },
        }
        receipt = CONTRACT.SourceDomainCorrespondenceReceipt(
            component_key=str(item["judgment_key"]),
            component_sha256="1" * 64,
            source_model_judgment_key="semantic-model::fixture",
        )
        self.assertEqual(
            CONTRACT.complete_source_claim_semantic_contract_errors(
                item,
                judgment,
                current_component_sha256s_by_source_judgment_key={
                    source_key: {"1" * 64}
                },
                source_domain_correspondence_receipts={receipt},
            ),
            [],
        )

    def test_transparent_spec_full_surface_receipt_is_occurrence_bound(self) -> None:
        """A current root receipt closes only its exact generated occurrence."""

        item = component(component_sha="8" * 64, surface="Fixture.Carrier")
        source_key = str(item["source_judgment_key"])
        receipt = CONTRACT.TransparentSpecFullSurfaceCorrespondenceReceipt(
            component_key=str(item["judgment_key"]),
            source_judgment_key=source_key,
            component_sha256="8" * 64,
            structural_type_sha256=STRUCTURAL_SHA,
            semantic_model_judgment_key="semantic-model::fixture",
            source_item_keys=("strict-source-root",),
            source_spec_correspondence_item_identity_sha256s=(
                ("strict-source-root", "a" * 64),
            ),
            source_spec_correspondence_closure_sha256s=(
                ("strict-source-root", "b" * 64),
            ),
            source_spec_correspondence_surface_sha256s=(
                ("strict-source-root", "c" * 64),
            ),
            source_spec_correspondence_environment_sha256s=(
                ("strict-source-root", "d" * 64),
            ),
            parent_semantic_association_sha256="e" * 64,
            parent_source_claim_atom_association_sha256="f" * 64,
            parent_source_claim_atom_semantic_association_sha256="0" * 64,
            component_source_contract_association_sha256="1" * 64,
        )
        kwargs = {
            "current_component_sha256s_by_source_judgment_key": {
                source_key: {"8" * 64}
            },
            "transparent_spec_full_surface_correspondence_receipts": {receipt},
        }
        self.assertEqual(
            CONTRACT.complete_source_claim_semantic_contract_errors(item, {}, **kwargs),
            [],
        )
        for changed in (
            replace(receipt, component_key="different-occurrence"),
            replace(receipt, source_judgment_key="different-source-key"),
            replace(receipt, component_sha256="9" * 64),
            replace(receipt, structural_type_sha256="2" * 64),
        ):
            with self.subTest(changed=changed):
                mismatch_kwargs = dict(kwargs)
                mismatch_kwargs[
                    "transparent_spec_full_surface_correspondence_receipts"
                ] = {changed}
                self.assertTrue(
                    CONTRACT.complete_source_claim_semantic_contract_errors(
                        item, {}, **mismatch_kwargs
                    )
                )

    def test_source_domain_shared_parent_list_accepts_each_current_parent(self) -> None:
        item = component(component_sha="7" * 64, surface="Fin n -> Real")
        source_key = str(item["source_judgment_key"])
        parents = ("semantic-model::first", "semantic-model::second")
        judgment = {
            "classification": "semantic_model_review",
            "source_claim_semantic_contract": {
                "schema": 1,
                "route": CONTRACT.SOURCE_DOMAIN_CORRESPONDENCE_ROUTE,
                "component_sha256": "7" * 64,
                "structural_type_sha256": STRUCTURAL_SHA,
                "source_domain_correspondence": {
                    "component_sha256": "7" * 64,
                    "source_model_judgment_keys": list(parents),
                },
            },
        }
        for parent in parents:
            receipt = CONTRACT.SourceDomainCorrespondenceReceipt(
                component_key=str(item["judgment_key"]),
                component_sha256="7" * 64,
                source_model_judgment_key=parent,
            )
            with self.subTest(parent=parent):
                self.assertEqual(
                    CONTRACT.complete_source_claim_semantic_contract_errors(
                        item,
                        judgment,
                        current_component_sha256s_by_source_judgment_key={
                            source_key: {"7" * 64}
                        },
                        source_domain_correspondence_receipts={receipt},
                    ),
                    [],
                )

    def test_source_domain_shared_parent_list_rejects_wrong_parent(self) -> None:
        item = component(component_sha="8" * 64, surface="Fin n -> Real")
        source_key = str(item["source_judgment_key"])
        judgment = {
            "source_claim_semantic_contract": {
                "schema": 1,
                "route": CONTRACT.SOURCE_DOMAIN_CORRESPONDENCE_ROUTE,
                "component_sha256": "8" * 64,
                "structural_type_sha256": STRUCTURAL_SHA,
                "source_domain_correspondence": {
                    "component_sha256": "8" * 64,
                    "source_model_judgment_keys": [
                        "semantic-model::first",
                        "semantic-model::second",
                    ],
                },
            }
        }
        wrong_receipt = CONTRACT.SourceDomainCorrespondenceReceipt(
            component_key=str(item["judgment_key"]),
            component_sha256="8" * 64,
            source_model_judgment_key="semantic-model::unlisted",
        )
        errors = CONTRACT.complete_source_claim_semantic_contract_errors(
            item,
            judgment,
            current_component_sha256s_by_source_judgment_key={
                source_key: {"8" * 64}
            },
            source_domain_correspondence_receipts={wrong_receipt},
        )
        self.assertTrue(any("listed parent" in error for error in errors))

    def test_source_domain_parent_list_is_strictly_validated(self) -> None:
        item = component(component_sha="9" * 64, surface="Fin n -> Real")
        source_key = str(item["source_judgment_key"])
        malformed_parent_lists: tuple[object, ...] = (
            [],
            ["semantic-model::same", "semantic-model::same"],
            ["semantic-model::valid", 3],
            [""],
            "semantic-model::not-a-list",
        )
        for raw_parents in malformed_parent_lists:
            judgment = {
                "source_claim_semantic_contract": {
                    "schema": 1,
                    "route": CONTRACT.SOURCE_DOMAIN_CORRESPONDENCE_ROUTE,
                    "component_sha256": "9" * 64,
                    "structural_type_sha256": STRUCTURAL_SHA,
                    "source_domain_correspondence": {
                        "component_sha256": "9" * 64,
                        "source_model_judgment_keys": raw_parents,
                    },
                }
            }
            with self.subTest(raw_parents=raw_parents):
                self.assertTrue(
                    CONTRACT.complete_source_claim_semantic_contract_errors(
                        item,
                        judgment,
                        current_component_sha256s_by_source_judgment_key={
                            source_key: {"9" * 64}
                        },
                    )
                )

        both_forms = {
            "source_claim_semantic_contract": {
                "schema": 1,
                "route": CONTRACT.SOURCE_DOMAIN_CORRESPONDENCE_ROUTE,
                "component_sha256": "9" * 64,
                "structural_type_sha256": STRUCTURAL_SHA,
                "source_domain_correspondence": {
                    "component_sha256": "9" * 64,
                    "source_model_judgment_key": "semantic-model::first",
                    "source_model_judgment_keys": ["semantic-model::second"],
                },
            }
        }
        self.assertTrue(
            CONTRACT.complete_source_claim_semantic_contract_errors(
                item,
                both_forms,
                current_component_sha256s_by_source_judgment_key={
                    source_key: {"9" * 64}
                },
            )
        )

    def test_source_domain_parent_list_ignores_classification_labels(self) -> None:
        item = component(component_sha="a" * 64, surface="Fin n -> Real")
        source_key = str(item["source_judgment_key"])
        contract = {
            "schema": 1,
            "route": CONTRACT.SOURCE_DOMAIN_CORRESPONDENCE_ROUTE,
            "component_sha256": "a" * 64,
            "structural_type_sha256": STRUCTURAL_SHA,
            "source_domain_correspondence": {
                "component_sha256": "a" * 64,
                "source_model_judgment_keys": [
                    "semantic-model::first",
                    "semantic-model::second",
                ],
            },
        }
        receipt = CONTRACT.SourceDomainCorrespondenceReceipt(
            component_key=str(item["judgment_key"]),
            component_sha256="a" * 64,
            source_model_judgment_key="semantic-model::second",
        )
        for classification in (
            "semantic_model_review",
            "approved_source_convention",
            "renamed_reviewer_label",
            "",
        ):
            with self.subTest(classification=classification):
                self.assertEqual(
                    CONTRACT.complete_source_claim_semantic_contract_errors(
                        item,
                        {
                            "classification": classification,
                            "source_claim_semantic_contract": contract,
                        },
                        current_component_sha256s_by_source_judgment_key={
                            source_key: {"a" * 64}
                        },
                        source_domain_correspondence_receipts={receipt},
                    ),
                    [],
                )

    def test_source_domain_parent_list_remains_component_and_type_bound(self) -> None:
        item = component(component_sha="e" * 64, surface="Fin n -> Real")
        source_key = str(item["source_judgment_key"])
        contract = {
            "schema": 1,
            "route": CONTRACT.SOURCE_DOMAIN_CORRESPONDENCE_ROUTE,
            "component_sha256": "e" * 64,
            "structural_type_sha256": STRUCTURAL_SHA,
            "source_domain_correspondence": {
                "component_sha256": "e" * 64,
                "source_model_judgment_keys": ["semantic-model::current"],
            },
        }
        receipt = CONTRACT.SourceDomainCorrespondenceReceipt(
            component_key=str(item["judgment_key"]),
            component_sha256="e" * 64,
            source_model_judgment_key="semantic-model::current",
        )
        kwargs = {
            "current_component_sha256s_by_source_judgment_key": {
                source_key: {"e" * 64}
            },
            "source_domain_correspondence_receipts": {receipt},
        }
        malformed_contracts = []
        wrong_component = copy.deepcopy(contract)
        wrong_component["component_sha256"] = "f" * 64
        malformed_contracts.append(wrong_component)
        wrong_correspondence_component = copy.deepcopy(contract)
        wrong_correspondence_component["source_domain_correspondence"][
            "component_sha256"
        ] = "f" * 64
        malformed_contracts.append(wrong_correspondence_component)
        wrong_type = copy.deepcopy(contract)
        wrong_type["structural_type_sha256"] = "f" * 64
        malformed_contracts.append(wrong_type)
        for malformed in malformed_contracts:
            with self.subTest(contract=malformed):
                self.assertTrue(
                    CONTRACT.complete_source_claim_semantic_contract_errors(
                        item,
                        {"source_claim_semantic_contract": malformed},
                        **kwargs,
                    )
                )

    def test_locator_convention_and_prose_derivation_cannot_pass(self) -> None:
        item = component(component_sha="2" * 64, surface="CustomCarrier")
        for judgment in (
            {
                "classification": "approved_source_convention",
                "source_location": "source.tex:101",
                "source_target_disposition": "approved_source_convention",
            },
            {
                "classification": "proved_from_primitives",
                "lean_derivation": "The intended construction is immediate.",
            },
            {
                "classification": "proved_from_primitives",
                "source_claim_semantic_contract": {
                    "schema": 1,
                    "route": CONTRACT.CHECKED_LEAN_DERIVATION_ROUTE,
                    "component_sha256": "2" * 64,
                    "structural_type_sha256": STRUCTURAL_SHA,
                    "bridge": {
                        "declaration": "Fixture.bridge",
                        "component_sha256": "2" * 64,
                        "field_type_sha256": STRUCTURAL_SHA,
                        "source_antecedent_keys": ["fixture.assumption"],
                        "lean_derivation": "prose is not a receipt",
                    },
                },
            },
        ):
            with self.subTest(judgment=judgment["classification"]):
                self.assertTrue(contract_errors(item, judgment))

    def test_scalar_contract_is_rejected_for_two_occurrences(self) -> None:
        first = component(component_sha="3" * 64, surface="Nat")
        second = component(component_sha="4" * 64, surface="Nat")
        judgment = exact_judgment(first)
        source_key = str(first["source_judgment_key"])
        kwargs = {
            "source_item_semantic_sha256_by_key": {SOURCE_ITEM: SOURCE_SHA},
            "current_component_sha256s_by_source_judgment_key": {
                source_key: {"3" * 64, "4" * 64}
            },
            "current_explicit_source_assumption_keys": {source_key},
        }
        self.assertTrue(
            CONTRACT.complete_source_claim_semantic_contract_errors(
                first, judgment, **kwargs
            )
        )
        first_contract = exact_contract(first)
        second_contract = exact_contract(second)
        judgment["source_claim_semantic_contract"] = None
        judgment["source_claim_semantic_contracts"] = {
            "3" * 64: first_contract,
            "4" * 64: second_contract,
        }
        self.assertEqual(
            CONTRACT.complete_source_claim_semantic_contract_errors(
                first, judgment, **kwargs
            ),
            [],
        )
        self.assertEqual(
            CONTRACT.complete_source_claim_semantic_contract_errors(
                second, judgment, **kwargs
            ),
            [],
        )

    def test_atom_binding_is_required_when_atom_policy_is_active(self) -> None:
        item = component(component_sha="5" * 64, surface="Fin n")
        judgment = exact_judgment(item)
        self.assertTrue(
            CONTRACT.complete_source_claim_semantic_contract_errors(
                item,
                judgment,
                source_item_semantic_sha256_by_key={SOURCE_ITEM: SOURCE_SHA},
                current_component_sha256s_by_source_judgment_key={
                    SOURCE_JUDGMENT: {"5" * 64}
                },
                current_explicit_source_assumption_keys={SOURCE_JUDGMENT},
                require_source_claim_atom=True,
            )
        )
        self.assertEqual(contract_errors(item, judgment, atom=True), [])

    def test_trusted_scaffolding_needs_registered_occurrence(self) -> None:
        item = component(
            component_sha="6" * 64,
            surface="Nat",
            role="trusted_external_scaffolding",
        )
        judgment = {
            "source_claim_semantic_contract": {
                "schema": 1,
                "route": CONTRACT.TRUSTED_EXTERNAL_SCAFFOLDING_ROUTE,
                "component_sha256": "6" * 64,
                "structural_type_sha256": STRUCTURAL_SHA,
            }
        }
        kwargs = {
            "current_component_sha256s_by_source_judgment_key": {
                SOURCE_JUDGMENT: {"6" * 64}
            }
        }
        self.assertTrue(
            CONTRACT.complete_source_claim_semantic_contract_errors(
                item, judgment, **kwargs
            )
        )
        self.assertEqual(
            CONTRACT.complete_source_claim_semantic_contract_errors(
                item,
                judgment,
                current_trusted_external_scaffolding_component_sha256s={"6" * 64},
                **kwargs,
            ),
            [],
        )

    def test_ledger_distinguishes_two_same_typed_binders_and_ignores_names(self) -> None:
        helper_path = ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
        spec = importlib.util.spec_from_file_location("component_ledger_fixture", helper_path)
        assert spec is not None and spec.loader is not None
        helper = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = helper
        spec.loader.exec_module(helper)
        inputs = [
            {
                "judgment_key": SOURCE_JUDGMENT,
                "source_judgment_key": SOURCE_JUDGMENT,
                "structural_type_sha256": STRUCTURAL_SHA,
                "elaborated_signature_sha256": SIGNATURE_SHA,
                "lean_outer_binder_indices": [0],
                "input_origin": "header_binder",
                "input_section": "header",
                "type": "Nat",
                "binder": "first",
            },
            {
                "judgment_key": SOURCE_JUDGMENT,
                "source_judgment_key": SOURCE_JUDGMENT,
                "structural_type_sha256": STRUCTURAL_SHA,
                "elaborated_signature_sha256": SIGNATURE_SHA,
                "lean_outer_binder_indices": [1],
                "input_origin": "header_binder",
                "input_section": "header",
                "type": "Nat",
                "binder": "second",
            },
        ]
        ledger = helper.theorem_realization_component_ledger(
            theorem_inputs=inputs,
            recursive_fields=[],
            conclusion_dependencies=[],
            type_certificates=[],
            semantic_model_items=[],
        )
        self.assertEqual(len(ledger), 2)
        self.assertNotEqual(
            ledger[0]["source_claim_component_sha256"],
            ledger[1]["source_claim_component_sha256"],
        )
        renamed = [dict(inputs[0], binder="renamed"), inputs[1]]
        renamed_ledger = helper.theorem_realization_component_ledger(
            theorem_inputs=renamed,
            recursive_fields=[],
            conclusion_dependencies=[],
            type_certificates=[],
            semantic_model_items=[],
        )
        self.assertEqual(
            ledger[0]["source_claim_component_sha256"],
            renamed_ledger[0]["source_claim_component_sha256"],
        )

    def test_ledger_retains_dependency_occurrence_sharing_an_input_source_key(
        self,
    ) -> None:
        helper_path = ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
        spec = importlib.util.spec_from_file_location("component_ledger_dependency_fixture", helper_path)
        assert spec is not None and spec.loader is not None
        helper = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = helper
        spec.loader.exec_module(helper)
        input_item = {
            "judgment_key": SOURCE_JUDGMENT,
            "structural_type_sha256": STRUCTURAL_SHA,
            "elaborated_signature_sha256": SIGNATURE_SHA,
            "lean_outer_binder_indices": [0],
            "input_origin": "header_binder",
            "input_section": "header",
            "type": "Nat",
        }
        dependency_item = {
            "judgment_key": SOURCE_JUDGMENT,
            "structural_type_sha256": STRUCTURAL_SHA,
            "elaborated_signature_sha256": SIGNATURE_SHA,
            "type": "Nat",
        }
        ledger = helper.theorem_realization_component_ledger(
            theorem_inputs=[input_item],
            recursive_fields=[],
            conclusion_dependencies=[dependency_item],
            type_certificates=[],
            semantic_model_items=[],
        )
        self.assertEqual(len(ledger), 2)
        self.assertEqual(
            {entry["source_judgment_key"] for entry in ledger}, {SOURCE_JUDGMENT}
        )
        self.assertNotEqual(
            ledger[0]["source_claim_component_sha256"],
            ledger[1]["source_claim_component_sha256"],
        )
        self.assertEqual(
            len(
                CONTRACT.theorem_facing_obligation_items(
                    {"theorem_realization_component_items": ledger}
                )
            ),
            2,
        )

    def test_ledger_does_not_duplicate_lean_owned_local_dependency_graph(
        self,
    ) -> None:
        helper_path = ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
        spec = importlib.util.spec_from_file_location(
            "component_ledger_lean_graph_fixture", helper_path
        )
        assert spec is not None and spec.loader is not None
        helper = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = helper
        spec.loader.exec_module(helper)
        semantic_model = {
            "judgment_key": "semantic-model::fixture",
            "expanded_lean_surface": {
                "terminal_term_dependency_surface": {
                    "unexpanded_local_term_heads": [
                        {
                            "declaration": "Fixture.Internal",
                            "structural_type_sha256": STRUCTURAL_SHA,
                        }
                    ],
                    "unexpanded_local_type_heads": [],
                }
            },
        }

        self.assertEqual(
            helper.theorem_realization_component_ledger(
                theorem_inputs=[],
                recursive_fields=[],
                conclusion_dependencies=[],
                type_certificates=[],
                semantic_model_items=[semantic_model],
            ),
            [],
        )


if __name__ == "__main__":
    unittest.main()
