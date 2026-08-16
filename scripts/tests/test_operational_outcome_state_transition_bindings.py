#!/usr/bin/env python3
"""Focused regressions for result-local operational state/transition routes."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import sys
import tempfile
import unittest
from copy import deepcopy
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    if str(import_root) not in sys.path:
        sys.path.insert(0, str(import_root))

from scripts import audit_repository as REPOSITORY  # noqa: E402
from scripts import audit_conclusion_provenance as GATE  # noqa: E402
from scripts.lean_signature_manifest import (  # noqa: E402
    run_lean_operational_outcome_state_transition_bridges_for_source,
)


HELPER = ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
SPEC = importlib.util.spec_from_file_location("outcome_state_transition_audit", HELPER)
assert SPEC is not None and SPEC.loader is not None
AUDIT = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = AUDIT
SPEC.loader.exec_module(AUDIT)


QUALIFIED = "Fixture.PaperInterface.reviewed"
BRIDGE = "Fixture.PaperInterface.nonempty"
INITIAL_WITNESS = "Fixture.PaperInterface.initialExists"
MODEL_ROOT = "Fixture.HeaderModel"
STATE_ROOT = "Fixture.OperationalState"
TRANSITION_ROOT = "Fixture.Advance"
DECLARATION_SHA = "a" * 64
SIGNATURE_SHA = "b" * 64


def atom(index: int, role: str, label: str) -> dict[str, str]:
    return {
        "ref": f"b/{index}",
        "role": role,
        "signature_atom_sha256": hashlib.sha256(label.encode("utf-8")).hexdigest(),
    }


def stamp_path(path: dict[str, object]) -> dict[str, object]:
    path["path_sha256"] = hashlib.sha256(
        json.dumps(path, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    return path


def conclusion_atom() -> dict[str, str]:
    return {
        "ref": "result",
        "role": "conclusion",
        "signature_atom_sha256": hashlib.sha256(b"conclusion").hexdigest(),
    }


def state_path() -> dict[str, object]:
    return stamp_path(
        {
            "schema": 1,
            "manifest_signature_sha256": SIGNATURE_SHA,
            "input_section": "result",
            "connective": "forall",
            "result_input_ordinal": 0,
            "binder_atoms": [atom(1, "parameter", "state")],
            "preceding_result_binder_atoms": [],
            "following_result_binder_atoms": [
                atom(2, "assumption", "initial"),
                atom(3, "parameter", "terminal"),
                atom(4, "assumption", "run"),
                atom(5, "assumption", "terminal-predicate"),
                atom(6, "parameter", "later-result-parameter"),
                atom(7, "assumption", "later-pav-predicate"),
            ],
            "terminal_conclusion_atom": conclusion_atom(),
        }
    )


def run_path(state: dict[str, object]) -> dict[str, object]:
    following = state["following_result_binder_atoms"]
    assert isinstance(following, list)
    return stamp_path(
        {
            "schema": 1,
            "manifest_signature_sha256": SIGNATURE_SHA,
            "input_section": "result",
            "connective": "arrow",
            "result_input_ordinal": 3,
            "binder_atoms": [following[2]],
            "preceding_result_binder_atoms": [
                state["binder_atoms"][0],
                following[0],
                following[1],
            ],
            "following_result_binder_atoms": following[3:],
            "terminal_conclusion_atom": conclusion_atom(),
        }
    )


def result_assumption_path(
    state: dict[str, object], *, index: int
) -> dict[str, object]:
    following = state["following_result_binder_atoms"]
    state_atoms = state["binder_atoms"]
    assert isinstance(following, list) and isinstance(state_atoms, list)
    target = following[index]
    assert isinstance(target, dict)
    return stamp_path(
        {
            "schema": 1,
            "manifest_signature_sha256": SIGNATURE_SHA,
            "input_section": "result",
            "connective": "arrow",
            "result_input_ordinal": index + 1,
            "binder_atoms": [target],
            "preceding_result_binder_atoms": [*state_atoms, *following[:index]],
            "following_result_binder_atoms": following[index + 1 :],
            "terminal_conclusion_atom": conclusion_atom(),
        }
    )


def declaration_identity() -> dict[str, str]:
    return {
        "qualified_declaration": QUALIFIED,
        "declaration_sha256": DECLARATION_SHA,
    }


def signature_identity() -> dict[str, str]:
    return {
        "qualified_declaration": QUALIFIED,
        "elaborated_signature_sha256": SIGNATURE_SHA,
    }


def dependencies(
    state: dict[str, object], run: dict[str, object]
) -> tuple[dict[str, object], dict[str, object]]:
    common = {
        "kind": "record_conclusion_input",
        "reviewed_declaration_identity": declaration_identity(),
        "reviewed_elaborated_signature_identities": [signature_identity()],
        "elaborated_signature_sha256": SIGNATURE_SHA,
    }
    return (
        {
            **common,
            "judgment_key": "generated-state-item",
            "record": STATE_ROOT,
            "elaborated_result_path": state,
        },
        {
            **common,
            "judgment_key": "generated-run-item",
            "record": TRANSITION_ROOT,
            "elaborated_result_path": run,
        },
    )


def theorem_facing_inputs(
    state: dict[str, object],
) -> tuple[dict[str, object], dict[str, object], dict[str, object]]:
    common = {
        "kind": "theorem_facing_input",
        "reviewed_declaration_identity": declaration_identity(),
        "reviewed_elaborated_signature_identities": [signature_identity()],
        "elaborated_signature_sha256": SIGNATURE_SHA,
    }
    return (
        {
            **common,
            "judgment_key": "generated-initial-predicate",
            "elaborated_result_path": result_assumption_path(state, index=0),
        },
        {
            **common,
            "judgment_key": "generated-terminal-predicate",
            "elaborated_result_path": result_assumption_path(state, index=3),
        },
        {
            **common,
            "judgment_key": "generated-later-pav-predicate",
            "elaborated_result_path": result_assumption_path(state, index=5),
        },
    )


def semantic_item() -> dict[str, object]:
    return {
        "judgment_key": "semantic-model::fixture",
        "reviewed_declaration_identity": declaration_identity(),
        "reviewed_elaborated_signature_identities": [signature_identity()],
        "record_input_bindings": [
            {
                "record_roots": [MODEL_ROOT],
                "elaborated_outer_binder_atoms": [atom(0, "parameter", "model")],
            }
        ],
    }


def attach_binding(
    item: dict[str, object], state: dict[str, object], run: dict[str, object]
) -> tuple[dict[str, object], dict[str, object]]:
    state_item, run_item = dependencies(state, run)
    AUDIT.attach_operational_outcome_state_transition_bindings(
        [item],
        [state_item, run_item],
        elaborated_signature_sha256_by_qualified={QUALIFIED: SIGNATURE_SHA},
    )
    return state_item, run_item


def semantic_judgment(item: dict[str, object]) -> dict[str, object]:
    bindings = item.get("operational_outcome_state_transition_bindings")
    assert isinstance(bindings, list) and len(bindings) == 1
    binding = bindings[0]
    assert isinstance(binding, dict)
    return {
        REPOSITORY.OPERATIONAL_OUTCOME_STATE_TRANSITION_RECEIPT_FIELD: [
            {
                "schema": 2,
                "target_declaration_sha256": DECLARATION_SHA,
                "target_signature_sha256": SIGNATURE_SHA,
                "model_header_atom": binding["model_header_atom"],
                "model_root": binding["model_root"],
                "state_result_path_sha256": binding["state_result_path_sha256"],
                "state_atom": binding["state_atom"],
                "state_root": binding["state_root"],
                "initial_predicate_atom": binding["initial_predicate_atom"],
                "run_result_path_sha256": binding["run_result_path_sha256"],
                "terminal_atom": binding["terminal_atom"],
                "run_atom": binding["run_atom"],
                "terminal_predicate_atom": binding["terminal_predicate_atom"],
                "transition_root": binding["transition_root"],
                "bridge_declaration": BRIDGE,
                "initial_state_witness_declaration": INITIAL_WITNESS,
            }
        ]
    }


@unittest.skip(
    "archived bespoke receipt diagnostic; canonical audit uses the Lean dependency graph"
)
class OperationalOutcomeStateTransitionBindingTests(unittest.TestCase):
    def test_direct_execution_window_ignores_later_result_obligations(self) -> None:
        """A later selector premise cannot erase or inherit the run route."""

        path = stamp_path(
            {
                "schema": 1,
                "manifest_signature_sha256": SIGNATURE_SHA,
                "input_section": "result",
                "connective": "arrow",
                "result_input_ordinal": 2,
                "binder_atoms": [atom(2, "assumption", "run")],
                "preceding_result_binder_atoms": [atom(1, "parameter", "terminal")],
                "following_result_binder_atoms": [
                    atom(3, "assumption", "terminal-predicate"),
                    atom(4, "parameter", "later-selector"),
                    atom(5, "assumption", "later-selector-condition"),
                ],
                "terminal_conclusion_atom": conclusion_atom(),
            }
        )

        expected = (
            {"ref": "b/1", "role": "parameter", "signature_atom_sha256": atom(1, "parameter", "terminal")["signature_atom_sha256"]},
            {"ref": "b/2", "role": "assumption", "signature_atom_sha256": atom(2, "assumption", "run")["signature_atom_sha256"]},
            {"ref": "b/3", "role": "assumption", "signature_atom_sha256": atom(3, "assumption", "terminal-predicate")["signature_atom_sha256"]},
        )
        self.assertEqual(
            AUDIT.operational_outcome_result_path_atoms(
                path, expected_signature_sha256=SIGNATURE_SHA
            ),
            expected,
        )
        self.assertEqual(
            REPOSITORY.operational_outcome_result_path_atoms(
                path, expected_signature_sha256=SIGNATURE_SHA
            ),
            tuple((int(atom_value["ref"].split("/", 1)[1]), atom_value) for atom_value in expected),
        )

    def route(
        self,
        item: dict[str, object],
        judgment: dict[str, object],
        state_item: dict[str, object],
        run_item: dict[str, object],
    ) -> tuple[str, str, int, int, int, int, int, int, str, str, str] | None:
        return REPOSITORY.operational_outcome_state_transition_bridge_route(
            item,
            judgment,
            qualified_declaration=QUALIFIED,
            state_item=state_item,
            run_item=run_item,
        )

    def test_generator_emits_only_manifest_pinned_state_transition_join(self) -> None:
        state = state_path()
        run = run_path(state)
        item = semantic_item()
        state_item, run_item = attach_binding(item, state, run)

        bindings = item.get("operational_outcome_state_transition_bindings")
        self.assertIsInstance(bindings, list)
        assert isinstance(bindings, list) and len(bindings) == 1
        binding = bindings[0]
        assert isinstance(binding, dict)
        self.assertEqual(binding["model_root"], MODEL_ROOT)
        self.assertEqual(binding["state_root"], STATE_ROOT)
        self.assertEqual(binding["transition_root"], TRANSITION_ROOT)
        self.assertEqual(binding["state_atom"], atom(1, "parameter", "state"))
        self.assertEqual(binding["run_atom"], atom(4, "assumption", "run"))
        self.assertEqual(binding["state_result_path_sha256"], state["path_sha256"])
        self.assertEqual(binding["run_result_path_sha256"], run["path_sha256"])

        # The transition must occur in the exact same result telescope window;
        # matching a similarly typed run from another branch is not enough.
        broken_run = deepcopy(run)
        broken_run["preceding_result_binder_atoms"] = [
            atom(1, "parameter", "other-state"),
            atom(2, "assumption", "initial"),
            atom(3, "parameter", "terminal"),
        ]
        stamp_path(broken_run)
        broken_item = semantic_item()
        attach_binding(broken_item, state, broken_run)
        self.assertNotIn("operational_outcome_state_transition_bindings", broken_item)

        # The dependencies themselves retain exact declaration/signature pins.
        self.assertEqual(
            state_item["reviewed_declaration_identity"], run_item["reviewed_declaration_identity"]
        )

    def test_receipt_rejects_changed_atoms_roots_and_path_coordinates(self) -> None:
        state = state_path()
        run = run_path(state)
        item = semantic_item()
        state_item, run_item = attach_binding(item, state, run)
        judgment = semantic_judgment(item)
        expected = (
            BRIDGE,
            INITIAL_WITNESS,
            0,
            1,
            2,
            3,
            4,
            5,
            MODEL_ROOT,
            STATE_ROOT,
            TRANSITION_ROOT,
        )
        self.assertEqual(self.route(item, judgment, state_item, run_item), expected)

        for field, value in (
            ("state_root", "Fixture.OtherState"),
            ("transition_root", "Fixture.OtherTransition"),
            ("state_result_path_sha256", "c" * 64),
            ("run_result_path_sha256", "d" * 64),
            ("initial_predicate_atom", atom(2, "assumption", "other-initial")),
            ("terminal_atom", atom(3, "parameter", "other-terminal")),
        ):
            altered = deepcopy(judgment)
            receipts = altered[
                REPOSITORY.OPERATIONAL_OUTCOME_STATE_TRANSITION_RECEIPT_FIELD
            ]
            assert isinstance(receipts, list) and isinstance(receipts[0], dict)
            receipts[0][field] = value
            self.assertIsNone(self.route(item, altered, state_item, run_item), field)

        malformed = deepcopy(judgment)
        receipts = malformed[
            REPOSITORY.OPERATIONAL_OUTCOME_STATE_TRANSITION_RECEIPT_FIELD
        ]
        assert isinstance(receipts, list) and isinstance(receipts[0], dict)
        receipts[0]["schema"] = True
        self.assertIsNone(self.route(item, malformed, state_item, run_item))


@unittest.skip(
    "retired correspondence-credit route; special receipts cannot grant audit credit"
)
class OperationalOutcomeStateTransitionCorrespondenceTests(unittest.TestCase):
    paper = "Fixture"

    @staticmethod
    def _component(
        source_key: str, section: str, suffix: str
    ) -> dict[str, object]:
        return {
            "judgment_key": f"theorem-realization::{suffix}",
            "source_judgment_key": source_key,
            "source_component_section": section,
            "source_claim_component_sha256": hashlib.sha256(
                suffix.encode("utf-8")
            ).hexdigest(),
            "structural_type_sha256": hashlib.sha256(
                (suffix + "-type").encode("utf-8")
            ).hexdigest(),
        }

    def _payload_and_judgments(
        self,
    ) -> tuple[dict[str, object], dict[str, dict[str, object]]]:
        state = state_path()
        run = run_path(state)
        item = semantic_item()
        association_sha = hashlib.sha256(b"semantic association").hexdigest()
        item["source_statement_association"] = {
            "schema": 2,
            "role": "direct_source_route",
            "semantic_association_sha256": association_sha,
            "reviewed_declaration_identity": declaration_identity(),
            "reviewed_elaborated_signature_identity": signature_identity(),
            "source_item_identities": [
                {
                    "source_key": "source-theorem",
                    "source_location": "source.tex:10-14",
                    "source_map_item_sha256": "c" * 64,
                    "source_semantic_sha256": "d" * 64,
                }
            ],
        }
        state_item, run_item = attach_binding(item, state, run)
        state_key = str(state_item["judgment_key"])
        run_key = str(run_item["judgment_key"])
        initial_item, terminal_item, later_pav_item = theorem_facing_inputs(state)
        initial_key = str(initial_item["judgment_key"])
        terminal_key = str(terminal_item["judgment_key"])
        later_pav_key = str(later_pav_item["judgment_key"])
        state_field_key = f"{STATE_ROOT}.invariant"
        transition_field_key = f"{TRANSITION_ROOT}.step_rule"
        payload: dict[str, object] = {
            "theorem_realization_contract_schema": 1,
            "source_record_audit_sha256": "e" * 64,
            "source_proof_fidelity": {},
            "expected_field_judgment_keys": [state_field_key, transition_field_key],
            "recursive_field_items": [
                {
                    "judgment_key": state_field_key,
                    "structure": STATE_ROOT,
                    "nested_structures": [],
                    "type": "Fixture.StateField",
                },
                {
                    "judgment_key": transition_field_key,
                    "structure": TRANSITION_ROOT,
                    "nested_structures": [],
                    "type": "Fixture.TransitionField",
                },
            ],
            "semantic_model_items": [item],
            "conclusion_dependency_items": [state_item, run_item],
            "theorem_facing_input_items": [
                initial_item,
                terminal_item,
                later_pav_item,
            ],
            "theorem_realization_component_items": [
                self._component(state_field_key, "recursive_field_items", "state-field"),
                self._component(
                    transition_field_key, "recursive_field_items", "transition-field"
                ),
                self._component(state_key, "conclusion_dependency_items", "state-node"),
                self._component(run_key, "conclusion_dependency_items", "run-node"),
                self._component(
                    initial_key, "theorem_facing_input_items", "initial-predicate"
                ),
                self._component(
                    terminal_key, "theorem_facing_input_items", "terminal-predicate"
                ),
                self._component(
                    later_pav_key,
                    "theorem_facing_input_items",
                    "later-pav-predicate",
                ),
                # This shares the semantic row but must not receive receipt
                # credit because it is not the generated state/run pair.
                self._component("unrelated", "conclusion_dependency_items", "unrelated"),
            ],
        }
        judgments = {
            "semantic-model::fixture": semantic_judgment(item),
            state_field_key: {},
            transition_field_key: {},
            initial_key: {},
            terminal_key: {},
            later_pav_key: {},
        }
        return payload, judgments

    def _receipts(
        self,
        payload: dict[str, object],
        judgments: dict[str, dict[str, object]],
        *,
        safe_fields: bool = True,
        checked_route: bool = True,
        safety_checker: object | None = None,
    ) -> tuple[object, ...]:
        old_papers = GATE.PAPERS
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            audit = root / self.paper / "audit"
            audit.mkdir(parents=True)
            (audit / "paper_statement_map.json").write_text(
                json.dumps({"items": {}}), encoding="utf-8"
            )
            (root / self.paper / "status.json").write_text(
                json.dumps(
                    {
                        "status": "formalized",
                        "review_surface": {"require_source_spec_correspondence": True},
                    }
                ),
                encoding="utf-8",
            )
            try:
                GATE.PAPERS = root
                with (
                    patch.object(GATE, "semantic_model_review_findings", return_value=[]),
                    patch.object(GATE, "source_record_expected_item_digests", return_value={}),
                    patch.object(
                        GATE, "source_record_expected_item_digest_pins", return_value={}
                    ),
                    patch.object(
                        GATE,
                        "result_domain_has_checked_operational_outcome_route",
                        return_value=checked_route,
                    ),
                    patch.object(
                        GATE,
                        "_current_semantic_model_field_is_safe",
                        side_effect=(
                            safety_checker
                            if safety_checker is not None
                            else lambda *_args, **_kwargs: safe_fields
                        ),
                    ),
                ):
                    return GATE.current_source_domain_correspondence_receipts(
                        self.paper, payload, judgments
                    )
            finally:
                GATE.PAPERS = old_papers

    def test_v11_receipts_are_component_bound_to_checked_state_run_route(self) -> None:
        payload, judgments = self._payload_and_judgments()
        receipts = self._receipts(payload, judgments)
        keys = {receipt.component_key for receipt in receipts}
        self.assertEqual(
            keys,
            {
                "theorem-realization::state-field",
                "theorem-realization::transition-field",
                "theorem-realization::state-node",
                "theorem-realization::initial-predicate",
                "theorem-realization::run-node",
                "theorem-realization::terminal-predicate",
            },
        )
        self.assertTrue(
            all(receipt.source_model_judgment_key == "semantic-model::fixture" for receipt in receipts)
        )

        # A semantic sidecar cannot use the state-transition receipt to attach
        # unrelated occurrence credit, including later PAV premises that lie
        # outside its exact execution window.
        self.assertNotIn("theorem-realization::unrelated", keys)
        self.assertNotIn("theorem-realization::later-pav-predicate", keys)

    def test_v11_predicate_contracts_use_generated_occurrences(self) -> None:
        payload, judgments = self._payload_and_judgments()
        inspected: list[dict[str, object]] = []

        def generated_component_only(
            item: object, _judgment: object, **_kwargs: object
        ) -> bool:
            if isinstance(item, dict):
                inspected.append(item)
                return isinstance(item.get("source_claim_component_sha256"), str)
            return False

        receipts = self._receipts(
            payload, judgments, safety_checker=generated_component_only
        )
        self.assertTrue(receipts)
        predicate_sections = {
            str(item.get("source_component_section") or "")
            for item in inspected
            if str(item.get("source_judgment_key") or "")
            in {
                "generated-initial-predicate",
                "generated-terminal-predicate",
            }
        }
        self.assertEqual(predicate_sections, {"theorem_facing_input_items"})

    def test_v11_allows_forall_premise_syntax_without_crediting_later_pav(self) -> None:
        payload, judgments = self._payload_and_judgments()
        inputs = payload["theorem_facing_input_items"]
        assert isinstance(inputs, list) and isinstance(inputs[0], dict)
        path = inputs[0]["elaborated_result_path"]
        assert isinstance(path, dict)
        path["connective"] = "forall"
        stamp_path(path)
        receipts = self._receipts(payload, judgments)
        keys = {receipt.component_key for receipt in receipts}
        self.assertTrue(receipts)
        self.assertNotIn("theorem-realization::later-pav-predicate", keys)

    def test_v11_gate_fails_closed_for_unchecked_route_or_field_contract(self) -> None:
        payload, judgments = self._payload_and_judgments()
        self.assertEqual(self._receipts(payload, judgments, checked_route=False), ())
        self.assertEqual(self._receipts(payload, judgments, safe_fields=False), ())

        payload, judgments = self._payload_and_judgments()
        semantic = payload["semantic_model_items"][0]
        assert isinstance(semantic, dict)
        bindings = semantic["operational_outcome_state_transition_bindings"]
        assert isinstance(bindings, list) and isinstance(bindings[0], dict)
        bindings[0]["state_root"] = "Fixture.OtherState"
        self.assertEqual(self._receipts(payload, judgments), ())

        payload, judgments = self._payload_and_judgments()
        payload["theorem_facing_input_items"] = []
        self.assertEqual(self._receipts(payload, judgments), ())

        payload, judgments = self._payload_and_judgments()
        inputs = payload["theorem_facing_input_items"]
        assert isinstance(inputs, list)
        payload["theorem_facing_input_items"] = inputs[:1]
        self.assertEqual(self._receipts(payload, judgments), ())

        payload, judgments = self._payload_and_judgments()
        inputs = payload["theorem_facing_input_items"]
        assert isinstance(inputs, list)
        payload["theorem_facing_input_items"] = inputs[1:]
        self.assertEqual(self._receipts(payload, judgments), ())

        payload, judgments = self._payload_and_judgments()
        inputs = payload["theorem_facing_input_items"]
        assert isinstance(inputs, list)
        payload["theorem_facing_input_items"] = inputs[:2]
        self.assertTrue(self._receipts(payload, judgments))

    def test_v11_route_requires_current_source_model_association(self) -> None:
        payload, judgments = self._payload_and_judgments()
        semantic = payload["semantic_model_items"][0]
        assert isinstance(semantic, dict)
        semantic.pop("source_statement_association")
        self.assertEqual(self._receipts(payload, judgments), ())


@unittest.skip(
    "archived fixed-telescope checker; canonical closure uses the general Lean dependency graph"
)
class OperationalOutcomeStateTransitionLeanTests(unittest.TestCase):
    def test_meta_checker_requires_exact_state_initial_run_bridge(self) -> None:
        source = """
import Mathlib
namespace StateBridgeFixture
inductive Header where | mk
inductive Snapshot : Header -> Type where | origin (header : Header) : Snapshot header
inductive Advance : (header : Header) -> Snapshot header -> Snapshot header -> Prop where
  | stay (header : Header) (snapshot : Snapshot header) : Advance header snapshot snapshot
def admitted {header : Header} (snapshot : Snapshot header) : Prop := snapshot = snapshot
def stopped {header : Header} (snapshot : Snapshot header) : Prop := snapshot = snapshot

theorem reviewed (header : Header) :
    forall initial : Snapshot header, admitted initial ->
      forall terminal : Snapshot header,
        Relation.ReflTransGen (Advance header) initial terminal ->
        stopped terminal -> terminal = terminal := by
  intro _ _ _ _ _
  rfl

theorem nonempty (header : Header) (initial : Snapshot header) (h : admitted initial) :
    exists terminal : Snapshot header,
      And (Relation.ReflTransGen (Advance header) initial terminal) (stopped terminal) := by
  exact Exists.intro initial (And.intro Relation.ReflTransGen.refl rfl)

theorem initialExists (header : Header) :
    exists initial : Snapshot header, admitted initial := by
  exact Exists.intro (Snapshot.origin header) rfl

theorem initialWithExtra (header : Header) (extra : Nat) :
    exists initial : Snapshot header, admitted initial := by
  exact Exists.intro (Snapshot.origin header) rfl

theorem initialFixed :
    exists initial : Snapshot Header.mk, admitted initial := by
  exact Exists.intro (Snapshot.origin Header.mk) rfl

theorem unrelatedInitial (header : Header) :
    forall initial : Snapshot header, True ->
      forall terminal : Snapshot header,
        Relation.ReflTransGen (Advance header) initial terminal ->
        stopped terminal -> terminal = terminal := by
  intro _ _ _ _ _
  rfl

theorem nonemptyForTrue (header : Header) (initial : Snapshot header) (h : True) :
    exists terminal : Snapshot header,
      And (Relation.ReflTransGen (Advance header) initial terminal) (stopped terminal) := by
  exact Exists.intro initial (And.intro Relation.ReflTransGen.refl rfl)

theorem initialForTrue (header : Header) :
    exists initial : Snapshot header, True :=
  Exists.intro (Snapshot.origin header) True.intro

def impossible {header : Header} (snapshot : Snapshot header) : Prop := snapshot ≠ snapshot

theorem reviewedImpossible (header : Header) :
    forall initial : Snapshot header, impossible initial ->
      forall terminal : Snapshot header,
        Relation.ReflTransGen (Advance header) initial terminal ->
        stopped terminal -> terminal = terminal := by
  intro _ _ _ _ _
  rfl

theorem nonemptyImpossible (header : Header) (initial : Snapshot header) (h : impossible initial) :
    exists terminal : Snapshot header,
      And (Relation.ReflTransGen (Advance header) initial terminal) (stopped terminal) := by
  exact False.elim (h rfl)

theorem ignoredState (header : Header) :
    forall initial : Snapshot header, admitted initial ->
      forall terminal : Snapshot header,
        Relation.ReflTransGen (Advance header) (Snapshot.origin header) terminal ->
        stopped terminal -> terminal = terminal := by
  intro _ _ _ _ _
  rfl

theorem originNonempty (header : Header) (initial : Snapshot header) (h : admitted initial) :
    exists terminal : Snapshot header,
      And (Relation.ReflTransGen (Advance header) (Snapshot.origin header) terminal)
        (stopped terminal) := by
  exact Exists.intro (Snapshot.origin header) (And.intro Relation.ReflTransGen.refl rfl)

theorem bridgeWithExtra (header : Header) (initial : Snapshot header) (h : admitted initial)
    (extra : Nat) : exists terminal : Snapshot header,
      And (Relation.ReflTransGen (Advance header) initial terminal) (stopped terminal) := by
  exact Exists.intro initial (And.intro Relation.ReflTransGen.refl rfl)
end StateBridgeFixture
"""
        roots = (
            "StateBridgeFixture.Header",
            "StateBridgeFixture.Snapshot",
            "StateBridgeFixture.Advance",
        )
        valid = (
            "StateBridgeFixture.reviewed",
            "StateBridgeFixture.nonempty",
            "StateBridgeFixture.initialExists",
            0,
            1,
            2,
            3,
            4,
            5,
            *roots,
        )
        routes = [
            valid,
            (
                "StateBridgeFixture.unrelatedInitial",
                "StateBridgeFixture.nonemptyForTrue",
                "StateBridgeFixture.initialForTrue",
                0,
                1,
                2,
                3,
                4,
                5,
                *roots,
            ),
            (
                "StateBridgeFixture.ignoredState",
                "StateBridgeFixture.originNonempty",
                "StateBridgeFixture.initialExists",
                0,
                1,
                2,
                3,
                4,
                5,
                *roots,
            ),
            (
                "StateBridgeFixture.reviewed",
                "StateBridgeFixture.bridgeWithExtra",
                "StateBridgeFixture.initialExists",
                0,
                1,
                2,
                3,
                4,
                5,
                *roots,
            ),
            (
                "StateBridgeFixture.reviewed",
                "StateBridgeFixture.nonempty",
                "StateBridgeFixture.initialExists",
                0,
                1,
                2,
                3,
                4,
                5,
                roots[0],
                "StateBridgeFixture.OtherSnapshot",
                roots[2],
            ),
            (
                "StateBridgeFixture.reviewedImpossible",
                "StateBridgeFixture.nonemptyImpossible",
                "StateBridgeFixture.initialExists",
                0,
                1,
                2,
                3,
                4,
                5,
                *roots,
            ),
            (
                "StateBridgeFixture.reviewed",
                "StateBridgeFixture.nonempty",
                "StateBridgeFixture.initialWithExtra",
                0,
                1,
                2,
                3,
                4,
                5,
                *roots,
            ),
            (
                "StateBridgeFixture.reviewed",
                "StateBridgeFixture.nonempty",
                "StateBridgeFixture.initialFixed",
                0,
                1,
                2,
                3,
                4,
                5,
                *roots,
            ),
        ]
        matches = run_lean_operational_outcome_state_transition_bridges_for_source(
            ROOT, source, routes
        )
        self.assertEqual(set(matches), set(routes))
        self.assertTrue(matches[valid])
        self.assertFalse(matches[routes[1]])
        self.assertFalse(matches[routes[2]])
        self.assertFalse(matches[routes[3]])
        self.assertFalse(matches[routes[4]])
        self.assertFalse(matches[routes[5]])
        self.assertFalse(matches[routes[6]])
        self.assertFalse(matches[routes[7]])


class LegacyOperationalAcceptanceRetirementTests(unittest.TestCase):
    def test_special_classification_is_not_an_approved_boundary_route(self) -> None:
        self.assertNotIn(
            "validated_source_outcome_domain",
            REPOSITORY.APPROVED_SOURCE_RECORD_CLASSIFICATIONS,
        )

    def test_conclusion_credit_hook_is_absent_and_compatibility_fails_closed(
        self,
    ) -> None:
        self.assertFalse(
            hasattr(GATE, "result_domain_has_checked_operational_outcome_route")
        )
        self.assertEqual(
            GATE.current_complete_operational_outcome_state_transition_bindings(
                "AnyPaper", {}, {}
            ),
            (),
        )


if __name__ == "__main__":
    unittest.main()
