#!/usr/bin/env python3
"""Focused regressions for atom-pinned operational outcome-domain receipts."""

from __future__ import annotations

import hashlib
import json
import sys
import unittest
from copy import deepcopy
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import audit_repository as REPOSITORY  # noqa: E402


QUALIFIED = "Fixture.PaperInterface.endpoint"
SPEC_QUALIFIED = "Fixture.PaperInterface.endpointSpec"
BRIDGE = "Fixture.PaperInterface.endpoint_outcome_domain_nonempty"
MODEL_ROOT = "Fixture.Model"
TRANSITION_ROOT = "Fixture.Step"
DECLARATION_SHA = "a" * 64
SPEC_DECLARATION_SHA = "c" * 64
SIGNATURE_SHA = "b" * 64


def atom(index: int, role: str, label: str) -> dict[str, str]:
    return {
        "ref": f"b/{index}",
        "role": role,
        "signature_atom_sha256": hashlib.sha256(label.encode("utf-8")).hexdigest(),
    }


def result_path() -> dict[str, object]:
    path: dict[str, object] = {
        "schema": 1,
        "manifest_signature_sha256": SIGNATURE_SHA,
        "input_section": "result",
        "connective": "arrow",
        "result_input_ordinal": 1,
        "binder_atoms": [atom(2, "assumption", "run")],
        "preceding_result_binder_atoms": [atom(1, "parameter", "terminal")],
        "following_result_binder_atoms": [
            atom(3, "assumption", "terminal-predicate")
        ],
        "terminal_conclusion_atom": {
            "ref": "result",
            "role": "conclusion",
            "signature_atom_sha256": hashlib.sha256(
                b"conclusion"
            ).hexdigest(),
        },
    }
    path["path_sha256"] = hashlib.sha256(
        json.dumps(path, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    return path


def semantic_item(path: dict[str, object]) -> dict[str, object]:
    model_atom = atom(0, "parameter", "model")
    run_atom = path["binder_atoms"][0]
    assert isinstance(run_atom, dict)
    return {
        "reviewed_declaration_identity": {
            "qualified_declaration": QUALIFIED,
            "declaration_sha256": DECLARATION_SHA,
        },
        "reviewed_elaborated_signature_identities": [
            {
                "qualified_declaration": QUALIFIED,
                "elaborated_signature_sha256": SIGNATURE_SHA,
            }
        ],
        "operational_outcome_transition_bindings": [
            {
                "schema": 1,
                "reviewed_declaration_identity": {
                    "qualified_declaration": QUALIFIED,
                    "declaration_sha256": DECLARATION_SHA,
                },
                "reviewed_elaborated_signature_identity": {
                    "qualified_declaration": QUALIFIED,
                    "elaborated_signature_sha256": SIGNATURE_SHA,
                },
                "model_header_atom": model_atom,
                "model_root": MODEL_ROOT,
                "result_path_sha256": path["path_sha256"],
                "run_atom": run_atom,
                "transition_root": TRANSITION_ROOT,
            }
        ],
    }


def direct_spec_semantic_item(path: dict[str, object]) -> dict[str, object]:
    """One direct-proof/transparent-Spec semantic row with a direct receipt."""

    item = semantic_item(path)
    source_identity = {
        "source_key": "source-result",
        "source_kind": "proposition",
        "source_location": "source.tex:10-12",
        "source_map_item_sha256": "d" * 64,
        "source_semantic_sha256": "e" * 64,
        "semantic_contract": {
            "evidence_declaration": QUALIFIED,
            "spec_declaration": SPEC_QUALIFIED,
            "evidence_mode": "proves",
            "semantic_shape": "plain",
        },
    }
    structural_surface = {"alpha_normalized_result": "Fixture.canonical"}
    item.update(
        {
            "semantic_surface_origin": {
                "kind": "transparent_spec_body",
                "qualified_declaration": SPEC_QUALIFIED,
            },
            "semantic_contract_group": {
                "schema": 1,
                "structural_alpha_normalized_equal": True,
                "member_rows": [
                    {
                        "role": "direct_evidence",
                        "qualified_declaration": QUALIFIED,
                        "reviewed_declaration_identity": {
                            "qualified_declaration": QUALIFIED,
                            "declaration_sha256": DECLARATION_SHA,
                        },
                    },
                    {
                        "role": "transparent_spec",
                        "qualified_declaration": SPEC_QUALIFIED,
                        "reviewed_declaration_identity": {
                            "qualified_declaration": SPEC_QUALIFIED,
                            "declaration_sha256": SPEC_DECLARATION_SHA,
                        },
                    },
                ],
                "direct_evidence_type": {
                    "qualified_declaration": QUALIFIED,
                    "structural_alpha_normalized_surface": structural_surface,
                },
                "surface_root": {
                    "kind": "transparent_spec_body",
                    "qualified_declaration": SPEC_QUALIFIED,
                    "structural_alpha_normalized_surface": structural_surface,
                },
                "source_item_identities": [source_identity],
            },
            "semantic_contract_source_association": {
                "schema": 2,
                "role": "direct_evidence",
                "review_scope": "individual_row_only",
                "structural_pairing": "not_asserted_by_source_association",
                "paired_qualified_declaration": SPEC_QUALIFIED,
                "reviewed_declaration_identity": {
                    "qualified_declaration": QUALIFIED,
                    "declaration_sha256": DECLARATION_SHA,
                },
                "reviewed_elaborated_signature_identity": {
                    "qualified_declaration": QUALIFIED,
                    "elaborated_signature_sha256": SIGNATURE_SHA,
                },
                "semantic_association_sha256": "f" * 64,
                "source_item_identities": [source_identity],
            },
        }
    )
    return item


def semantic_judgment(path: dict[str, object]) -> dict[str, object]:
    return {
        REPOSITORY.OPERATIONAL_OUTCOME_DOMAIN_RECEIPT_FIELD: [
            {
                "schema": 1,
                "target_declaration_sha256": DECLARATION_SHA,
                "target_signature_sha256": SIGNATURE_SHA,
                "result_path_sha256": path["path_sha256"],
                "model_header_atom": atom(0, "parameter", "model"),
                "model_root": MODEL_ROOT,
                "run_atom": path["binder_atoms"][0],
                "transition_root": TRANSITION_ROOT,
                "bridge_declaration": BRIDGE,
            }
        ]
    }


@unittest.skip(
    "archived bespoke domain receipt; canonical audit uses the general Lean dependency graph"
)
class OperationalOutcomeDomainReceiptTests(unittest.TestCase):
    def route(
        self,
        item: dict[str, object],
        judgment: dict[str, object],
        path: dict[str, object],
    ) -> tuple[str, int, int, int, int, str, str] | None:
        return REPOSITORY.operational_outcome_domain_bridge_route(
            item,
            judgment,
            qualified_declaration=QUALIFIED,
            raw_path=path,
        )

    def test_exact_atom_pinned_result_path_and_bridge_are_accepted(self) -> None:
        path = result_path()
        route = self.route(semantic_item(path), semantic_judgment(path), path)

        self.assertEqual(
            route,
            (BRIDGE, 0, 1, 2, 3, MODEL_ROOT, TRANSITION_ROOT),
        )

    def test_direct_spec_semantic_surface_keeps_direct_proof_receipt(self) -> None:
        path = result_path()
        item = direct_spec_semantic_item(path)

        self.assertEqual(
            self.route(item, semantic_judgment(path), path),
            (BRIDGE, 0, 1, 2, 3, MODEL_ROOT, TRANSITION_ROOT),
        )

        # The transparent Spec supplies the semantic body but must never
        # replace the direct theorem as the result-path receipt target.
        spec_owned = deepcopy(item)
        spec_owned["reviewed_declaration_identity"] = {
            "qualified_declaration": SPEC_QUALIFIED,
            "declaration_sha256": SPEC_DECLARATION_SHA,
        }
        self.assertIsNone(self.route(spec_owned, semantic_judgment(path), path))

    def test_non_result_path_and_wrong_atom_or_root_are_rejected(self) -> None:
        path = result_path()
        item = semantic_item(path)
        judgment = semantic_judgment(path)

        non_result = deepcopy(path)
        non_result["input_section"] = "header"
        non_result["path_sha256"] = hashlib.sha256(
            json.dumps(
                {key: value for key, value in non_result.items() if key != "path_sha256"},
                sort_keys=True,
                separators=(",", ":"),
            ).encode("utf-8")
        ).hexdigest()
        self.assertIsNone(self.route(item, judgment, non_result))

        wrong_atom_judgment = deepcopy(judgment)
        receipts = wrong_atom_judgment[
            REPOSITORY.OPERATIONAL_OUTCOME_DOMAIN_RECEIPT_FIELD
        ]
        assert isinstance(receipts, list) and isinstance(receipts[0], dict)
        receipts[0]["model_header_atom"] = atom(4, "parameter", "other-model")
        self.assertIsNone(self.route(item, wrong_atom_judgment, path))

        wrong_root_judgment = deepcopy(judgment)
        receipts = wrong_root_judgment[
            REPOSITORY.OPERATIONAL_OUTCOME_DOMAIN_RECEIPT_FIELD
        ]
        assert isinstance(receipts, list) and isinstance(receipts[0], dict)
        receipts[0]["transition_root"] = "Fixture.OtherStep"
        self.assertIsNone(self.route(item, wrong_root_judgment, path))

    def test_malformed_or_unqualified_bridge_receipt_is_rejected(self) -> None:
        path = result_path()
        item = semantic_item(path)
        judgment = semantic_judgment(path)
        receipts = judgment[REPOSITORY.OPERATIONAL_OUTCOME_DOMAIN_RECEIPT_FIELD]
        assert isinstance(receipts, list) and isinstance(receipts[0], dict)
        receipts[0]["bridge_declaration"] = "not a qualified declaration"

        self.assertIsNone(self.route(item, judgment, path))

    def test_missing_receipt_schema_is_rejected(self) -> None:
        path = result_path()
        item = semantic_item(path)
        judgment = semantic_judgment(path)
        receipts = judgment[REPOSITORY.OPERATIONAL_OUTCOME_DOMAIN_RECEIPT_FIELD]
        assert isinstance(receipts, list) and isinstance(receipts[0], dict)
        del receipts[0]["schema"]

        self.assertIsNone(self.route(item, judgment, path))

    def test_boolean_schema_markers_are_rejected_at_each_receipt_boundary(self) -> None:
        path = result_path()

        boolean_path = deepcopy(path)
        boolean_path["schema"] = True
        boolean_path["path_sha256"] = hashlib.sha256(
            json.dumps(
                {
                    key: value
                    for key, value in boolean_path.items()
                    if key != "path_sha256"
                },
                sort_keys=True,
                separators=(",", ":"),
            ).encode("utf-8")
        ).hexdigest()
        self.assertIsNone(
            self.route(semantic_item(path), semantic_judgment(path), boolean_path)
        )

        boolean_binding_item = semantic_item(path)
        bindings = boolean_binding_item["operational_outcome_transition_bindings"]
        assert isinstance(bindings, list) and isinstance(bindings[0], dict)
        bindings[0]["schema"] = True
        self.assertIsNone(
            self.route(boolean_binding_item, semantic_judgment(path), path)
        )

        boolean_receipt = semantic_judgment(path)
        receipts = boolean_receipt[
            REPOSITORY.OPERATIONAL_OUTCOME_DOMAIN_RECEIPT_FIELD
        ]
        assert isinstance(receipts, list) and isinstance(receipts[0], dict)
        receipts[0]["schema"] = True
        self.assertIsNone(self.route(semantic_item(path), boolean_receipt, path))


class OperationalOutcomeBridgeAxiomClosureTests(unittest.TestCase):
    def test_sorry_and_unapproved_axioms_are_rejected(self) -> None:
        with patch.object(
            REPOSITORY.subprocess,
            "run",
            side_effect=[
                SimpleNamespace(returncode=0, stdout="", stderr=""),
                SimpleNamespace(
                    returncode=0,
                    stdout=(
                        "'Fixture.PaperInterface.bridge' depends on axioms: "
                        "[sorryAx, Fixture.unprovedBridge]\n"
                    ),
                    stderr="",
                ),
            ],
        ):
            self.assertFalse(
                REPOSITORY.operational_outcome_bridge_axiom_closure_is_approved(
                    "Fixture.PaperInterface", "Fixture.PaperInterface.bridge"
                )
            )

    def test_standard_foundations_only_are_accepted(self) -> None:
        with patch.object(
            REPOSITORY.subprocess,
            "run",
            side_effect=[
                SimpleNamespace(returncode=0, stdout="", stderr=""),
                SimpleNamespace(
                    returncode=0,
                    stdout=(
                        "'Fixture.PaperInterface.bridge' depends on axioms: "
                        "[propext, Classical.choice, Quot.sound]\n"
                    ),
                    stderr="",
                ),
            ],
        ):
            self.assertTrue(
                REPOSITORY.operational_outcome_bridge_axiom_closure_is_approved(
                    "Fixture.PaperInterface", "Fixture.PaperInterface.bridge"
                )
            )


if __name__ == "__main__":
    unittest.main()
