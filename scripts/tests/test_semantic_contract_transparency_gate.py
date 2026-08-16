#!/usr/bin/env python3
"""Focused regressions for transitive semantic-contract Spec transparency."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    value = str(import_root)
    if value not in sys.path:
        sys.path.insert(0, value)

from lean_signature_manifest import (  # noqa: E402
    parse_semantic_contract_transparency_output,
    run_lean_semantic_contract_transparency_checks_for_source,
)


class SemanticContractTransparencyGateTests(unittest.TestCase):
    def check(self, source: str, *specifications: str, fuel: int = 32) -> dict[str, dict]:
        result = run_lean_semantic_contract_transparency_checks_for_source(
            ROOT,
            source,
            list(specifications),
            max_expansions=fuel,
        )
        self.assertEqual(set(result), set(specifications))
        return result

    def test_imported_opaque_payoff_wrapper_fails_transitively(self) -> None:
        source = """
namespace ImportedPayoffFixture
opaque payoff : Nat -> Nat
end ImportedPayoffFixture

namespace PaperContractFixture
def sourceFacingSpec (budget : Nat) : Prop :=
  ImportedPayoffFixture.payoff budget = budget
end PaperContractFixture
"""
        result = self.check(source, "PaperContractFixture.sourceFacingSpec")
        verdict = result["PaperContractFixture.sourceFacingSpec"]
        self.assertFalse(verdict["passes"])
        self.assertEqual(verdict["failure_tag"], "opaque_local_dependency")
        self.assertEqual(
            verdict["failure_declaration"], "ImportedPayoffFixture.payoff"
        )

    def test_transparent_imported_payoff_expands_and_passes(self) -> None:
        source = """
namespace ImportedPayoffFixture
def payoff (budget : Nat) : Nat := budget + 1
end ImportedPayoffFixture

namespace PaperContractFixture
def sourceFacingSpec (budget : Nat) : Prop :=
  ImportedPayoffFixture.payoff budget = budget + 1
end PaperContractFixture
"""
        result = self.check(source, "PaperContractFixture.sourceFacingSpec")
        verdict = result["PaperContractFixture.sourceFacingSpec"]
        self.assertTrue(verdict["passes"])
        self.assertEqual(verdict["failure_tag"], "")
        self.assertGreaterEqual(verdict["expanded"], 1)

    def test_axiom_boundary_fails(self) -> None:
        source = """
namespace PaperContractFixture
axiom payoff : Nat -> Nat
def sourceFacingSpec (budget : Nat) : Prop := payoff budget = budget
end PaperContractFixture
"""
        result = self.check(source, "PaperContractFixture.sourceFacingSpec")
        verdict = result["PaperContractFixture.sourceFacingSpec"]
        self.assertFalse(verdict["passes"])
        self.assertEqual(verdict["failure_tag"], "axiom_local_dependency")

    def test_spec_proof_arguments_are_audited_by_exact_proposition_type(self) -> None:
        """Proof decomposition does not change the reviewed proposition.

        The canonical surface embeds the exact existential type used by
        ``Classical.choose``. The walker therefore audits that type and ignores
        only the proof implementation; this keeps the statement independent of
        a helper theorem's name while retaining the witness restriction.
        """

        source = """
namespace Fixture
theorem localWitness : ∃ n : Nat, n = 37 := ⟨37, rfl⟩
def ChosenSpec : Prop :=
  let n := Classical.choose localWitness
  n = 37
theorem Chosen : ChosenSpec := by
  exact Classical.choose_spec localWitness
end Fixture
"""
        result = self.check(source, "Fixture.ChosenSpec")
        verdict = result["Fixture.ChosenSpec"]
        self.assertTrue(verdict["passes"])
        self.assertEqual(verdict["failure_tag"], "")

    def test_constructor_proof_fields_do_not_create_semantic_dependencies(self) -> None:
        """Proof-only fields are audited by type and erased as implementations.

        The source-facing proposition reads the data field of a structure.  A
        local theorem supplies only the constructor's `Prop` field, so it
        cannot select or alter the value being reviewed; the exact invariant
        proposition remains present in the canonical surface.
        """

        source = """
namespace ConstructorProofFixture
structure State where
  value : Nat
  valid : value = 0
theorem initialValid : (0 : Nat) = 0 := rfl
def initial : State := { value := 0, valid := initialValid }
def sourceFacingSpec : Prop := initial.value = 0
end ConstructorProofFixture
"""
        result = self.check(source, "ConstructorProofFixture.sourceFacingSpec")
        verdict = result["ConstructorProofFixture.sourceFacingSpec"]
        self.assertTrue(verdict["passes"])
        self.assertEqual(verdict["failure_tag"], "")

    def test_fuel_exhaustion_is_fail_closed(self) -> None:
        source = """
namespace PaperContractFixture
def primitivePayoff (budget : Nat) : Nat := budget + 1
def wrappedPayoff (budget : Nat) : Nat :=
  if budget = 0 then primitivePayoff budget else primitivePayoff budget
def sourceFacingSpec (budget : Nat) : Prop := wrappedPayoff budget = budget + 1
end PaperContractFixture
"""
        result = self.check(
            source,
            "PaperContractFixture.sourceFacingSpec",
            fuel=1,
        )
        verdict = result["PaperContractFixture.sourceFacingSpec"]
        self.assertFalse(verdict["passes"])
        self.assertEqual(verdict["failure_tag"], "fuel_exhausted")

    def test_fully_applied_recursive_data_executor_is_a_terminal_candidate(self) -> None:
        """Data recursion remains visible and cannot become a generic pass."""

        source = """
namespace ExecutorFixture
def firstZero? : List Nat -> Option Nat
  | [] => none
  | value :: rest => if value = 0 then some value else firstZero? rest

def sourceFacingSpec (values : List Nat) : Prop :=
  firstZero? values = none \\/ firstZero? values = some 0
end ExecutorFixture
"""
        result = self.check(source, "ExecutorFixture.sourceFacingSpec")
        verdict = result["ExecutorFixture.sourceFacingSpec"]
        self.assertFalse(verdict["passes"])
        self.assertEqual(verdict["failure_tag"], "recursive_executable_terminal")
        terminals = verdict["recursive_executable_terminals"]
        self.assertEqual(len(terminals), 2)
        self.assertEqual(
            {terminal["declaration"] for terminal in terminals},
            {"ExecutorFixture.firstZero?"},
        )
        self.assertEqual(
            {terminal["application_arity"] for terminal in terminals}, {1}
        )
        self.assertEqual(
            {terminal["application_result_type"] for terminal in terminals},
            {"Option Nat"},
        )
        self.assertEqual(
            {terminal["normalized_result_type"] for terminal in terminals},
            {"Option Nat"},
        )
        paths = [tuple(terminal["occurrence_path"]) for terminal in terminals]
        self.assertEqual(len(paths), len(set(paths)))
        self.assertTrue(all(path and path[0] == "spec_body" for path in paths))

    def test_recursive_prop_wrapper_remains_a_transparency_failure(self) -> None:
        """The terminal path cannot turn a recursive predicate into model data."""

        source = """
namespace PredicateFixture
def recursivePredicate : Nat -> Prop
  | 0 => True
  | value + 1 => recursivePredicate value

def sourceFacingSpec (value : Nat) : Prop := recursivePredicate value
end PredicateFixture
"""
        result = self.check(source, "PredicateFixture.sourceFacingSpec")
        verdict = result["PredicateFixture.sourceFacingSpec"]
        self.assertFalse(verdict["passes"])
        self.assertEqual(verdict["failure_tag"], "recursive_local_definition")
        self.assertEqual(verdict["recursive_executable_terminals"], [])

    def test_terminal_protocol_rejects_malformed_or_unpaired_receipts(self) -> None:
        sentinel = "LEAN_SEMANTIC_CONTRACT_TRANSPARENCY:"
        terminal = (
            '{"declaration":"Fixture.executor","occurrence_path":["spec_body"],'
            '"application_arity":"1","application_result_type":"Nat",'
            '"normalized_result_type":"Nat"}'
        )
        valid = (
            sentinel
            + '{"spec":"Fixture.Spec","passes":false,'
            + '"failure_tag":"recursive_executable_terminal",'
            + '"failure_declaration":"Fixture.executor",'
            + '"recursive_executable_terminal_schema":"1",'
            + '"recursive_executable_terminals":[' + terminal + '],'
            + '"expanded":"4"}'
        )
        parsed = parse_semantic_contract_transparency_output(valid)["Fixture.Spec"]
        self.assertEqual(parsed["recursive_executable_terminals"][0]["declaration"], "Fixture.executor")
        self.assertEqual(parsed["recursive_executable_terminals"][0]["application_arity"], 1)
        for malformed in (
            valid.replace('"occurrence_path":["spec_body"]', '"occurrence_path":[]'),
            valid.replace('"failure_declaration":"Fixture.executor"', '"failure_declaration":"Fixture.other"'),
            valid.replace('"passes":false', '"passes":true'),
            valid.replace('"application_arity":"1"', '"application_arity":"0"'),
            valid.replace('"recursive_executable_terminal_schema":"1"', '"recursive_executable_terminal_schema":"2"'),
            valid.replace('"recursive_executable_terminals":[' + terminal + ']', '"recursive_executable_terminals":"Fixture.executor"'),
        ):
            with self.subTest(malformed=malformed):
                self.assertEqual(parse_semantic_contract_transparency_output(malformed), {})


if __name__ == "__main__":
    unittest.main()
