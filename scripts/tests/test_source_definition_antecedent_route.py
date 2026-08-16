#!/usr/bin/env python3
"""Focused tests for direct-definition source-antecedent receipt reissue."""

from __future__ import annotations

import copy
import importlib.util
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import source_definition_antecedent_route as ROUTE
from scripts import audit_conclusion_provenance as CONCLUSION


PAPER = "KR21Monoculture"
TARGET_KEY = (
    "lemma3_source_arbitraryFinite_iid_delta_le_top_delta_semantic_complete.hf "
    ": StrictlyWellOrderedNoise f"
)
LEMMA_SOURCE_KEY = "kr21_lemma3_middle_gain_bound"
DEFINITION_SOURCE_KEY = "kr21_definition4_strict_well_ordered_noise"
OTHER_DEFINITION_SOURCE_KEY = "kr21_definition1_noisy_permutation_family"
LEMMA_RECORD_KEY = "lemma3_source_arbitraryFinite_iid_delta_le_top_delta_semantic_complete"
DEFINITION_RECORD_KEY = "definition4_strictlyWellOrderedNoise_iff"
OTHER_DEFINITION_RECORD_KEY = "source_definition1_iff"
SOURCE_RECORD_AUDIT_HELPER = (
    ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
)


def load_source_record_audit_helper() -> object:
    spec = importlib.util.spec_from_file_location(
        "source_definition_antecedent_route_source_record_audit_helper",
        SOURCE_RECORD_AUDIT_HELPER,
    )
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


@unittest.skip(
    "archived definition-specific transport; canonical audit uses generic source and Lean graph evidence"
)
class SourceDefinitionAntecedentRouteTests(unittest.TestCase):
    """Exercise the narrow route using current pinned KR21 fixture surfaces."""

    def test_overlay_runtime_dir_resolves_relative_tmpdir_under_repository_root(
        self,
    ) -> None:
        with mock.patch.dict(
            os.environ,
            {"TMPDIR": ".scratch/source-definition-route-test"},
            clear=False,
        ):
            self.assertEqual(
                ROUTE._lean_overlay_temp_dir(),
                ROOT / ".scratch" / "source-definition-route-test",
            )

    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.paper_dir = self.root / "papers" / PAPER
        self.audit_dir = self.paper_dir / "audit"
        self.audit_dir.mkdir(parents=True)

        fixture_dir = ROOT / "papers" / PAPER
        source_map = json.loads(
            (fixture_dir / "audit" / "paper_statement_map.json").read_text(
                encoding="utf-8"
            )
        )
        raw_audit = json.loads(
            (fixture_dir / "audit" / "source_record_audit.json").read_text(
                encoding="utf-8"
            )
        )
        statement_matches = json.loads(
            (fixture_dir / "audit" / "statement_match_llm.json").read_text(
                encoding="utf-8"
            )
        )
        ordinary_sidecar = json.loads(
            (fixture_dir / "audit" / "source_record_match_llm.json").read_text(
                encoding="utf-8"
            )
        )

        source_rel = Path(str(source_map["source_artifact_path"]))
        source_dst = self.paper_dir / source_rel
        source_dst.parent.mkdir(parents=True)
        source_dst.write_bytes((fixture_dir / source_rel).read_bytes())
        (self.paper_dir / "PaperInterface.lean").write_bytes(
            (fixture_dir / "PaperInterface.lean").read_bytes()
        )

        self.statement_map = {
            key: copy.deepcopy(value)
            for key, value in source_map.items()
            if key != "items"
        }
        self.statement_map["items"] = {
            LEMMA_SOURCE_KEY: copy.deepcopy(source_map["items"][LEMMA_SOURCE_KEY]),
            DEFINITION_SOURCE_KEY: copy.deepcopy(
                source_map["items"][DEFINITION_SOURCE_KEY]
            ),
        }
        self.raw_audit = {
            key: copy.deepcopy(value)
            for key, value in raw_audit.items()
            if key not in {"boundary_input_items", "conclusion_dependency_items"}
        }
        for section in ("boundary_input_items", "conclusion_dependency_items"):
            self.raw_audit[section] = [
                copy.deepcopy(item)
                for item in raw_audit.get(section, [])
                if isinstance(item, dict) and item.get("judgment_key") == TARGET_KEY
            ]
        self.statement_matches = {
            key: copy.deepcopy(value)
            for key, value in statement_matches.items()
            if key != "items"
        }
        self.statement_matches["items"] = {
            LEMMA_RECORD_KEY: copy.deepcopy(statement_matches["items"][LEMMA_RECORD_KEY]),
            DEFINITION_RECORD_KEY: copy.deepcopy(
                statement_matches["items"][DEFINITION_RECORD_KEY]
            ),
        }
        self.other_definition_item = copy.deepcopy(
            source_map["items"][OTHER_DEFINITION_SOURCE_KEY]
        )
        self.other_definition_record = copy.deepcopy(
            statement_matches["items"][OTHER_DEFINITION_RECORD_KEY]
        )
        self.sidecar = {
            "schema": 1,
            "paper": PAPER,
            "prompt_version": self.raw_audit["prompt_version"],
            # The materializer must not make unrelated ordinary entries current.
            "source_record_audit_sha256": "0" * 64,
            "items": {
                TARGET_KEY: copy.deepcopy(ordinary_sidecar["items"][TARGET_KEY]),
                "unrelated stale row": {
                    "classification": "validated_source_assumption",
                    "source_target_disposition": "literal_source_match",
                    "source_record_audit_sha256": "1" * 64,
                },
            },
        }
        self.receipt_path = self.audit_dir / ROUTE.RECEIPT_FILENAME

    def build(self) -> dict[str, object]:
        return ROUTE.build_source_definition_antecedent_receipt(
            paper=PAPER,
            paper_dir=self.paper_dir,
            raw_audit=self.raw_audit,
            statement_map=self.statement_map,
            statement_matches=self.statement_matches,
        )

    def fresh_build(
        self,
        *,
        raw_audit: dict[str, object] | None = None,
        statement_map: dict[str, object] | None = None,
        statement_matches: dict[str, object] | None = None,
    ) -> dict[str, object]:
        """Exercise current evidence rather than replaying an old receipt."""

        return ROUTE.build_source_definition_antecedent_receipt(
            paper=PAPER,
            paper_dir=self.paper_dir,
            raw_audit=raw_audit or self.raw_audit,
            statement_map=statement_map or self.statement_map,
            statement_matches=statement_matches or self.statement_matches,
        )

    @staticmethod
    def definition_review_entry(payload: dict[str, object]) -> dict[str, object]:
        entries = payload["items"][DEFINITION_RECORD_KEY]["semantic_scope_review"][
            "named_definition_review"
        ]["items"]
        for entry in entries:
            if entry.get("used_as_source_conclusion_evidence") is True:
                assert isinstance(entry, dict)
                return entry
        raise AssertionError("KR21 v10 definition record no longer exposes its IFF")

    def assert_fresh_build_rejects(
        self,
        *,
        raw_audit: dict[str, object] | None = None,
        statement_matches: dict[str, object] | None = None,
    ) -> None:
        """A fresh semantic route must fail closed, not reuse old evidence."""

        try:
            rebuilt = self.fresh_build(
                raw_audit=raw_audit,
                statement_matches=statement_matches,
            )
        except ROUTE.SourceDefinitionAntecedentRouteError:
            return
        self.assertEqual(rebuilt["routes"], [])

    def write_receipt(self, receipt: dict[str, object]) -> None:
        self.receipt_path.write_text(
            json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )

    def validate_receipt(
        self,
        receipt: dict[str, object],
        *,
        raw_audit: dict[str, object] | None = None,
        statement_map: dict[str, object] | None = None,
        statement_matches: dict[str, object] | None = None,
    ) -> dict[str, dict[str, object]]:
        return ROUTE.validate_source_definition_antecedent_receipt(
            receipt,
            paper=PAPER,
            paper_dir=self.paper_dir,
            raw_audit=raw_audit or self.raw_audit,
            statement_map=statement_map or self.statement_map,
            statement_matches=statement_matches or self.statement_matches,
        )

    def materialize(self, receipt: dict[str, object]) -> dict[str, object]:
        return ROUTE.materialize_source_definition_antecedent_route(
            receipt,
            self.sidecar,
            paper=PAPER,
            paper_dir=self.paper_dir,
            receipt_path=self.receipt_path,
            raw_audit=self.raw_audit,
            statement_map=self.statement_map,
            statement_matches=self.statement_matches,
            validator="focused receipt test",
            validated_at="2026-07-28T00:00:00Z",
        )

    def write_loader_inputs(self) -> None:
        (self.audit_dir / "paper_statement_map.json").write_text(
            json.dumps(self.statement_map, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
        (self.audit_dir / "statement_match_llm.json").write_text(
            json.dumps(self.statement_matches, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

    def maps_with_other_iff_definition(
        self,
    ) -> tuple[dict[str, object], dict[str, object]]:
        """Add KR21 Definition 1, an unrelated current IFF candidate."""

        statement_map = copy.deepcopy(self.statement_map)
        statement_matches = copy.deepcopy(self.statement_matches)
        statement_map["items"][OTHER_DEFINITION_SOURCE_KEY] = copy.deepcopy(
            self.other_definition_item
        )
        statement_matches["items"][OTHER_DEFINITION_RECORD_KEY] = copy.deepcopy(
            self.other_definition_record
        )
        return statement_map, statement_matches

    def raw_audit_with_expansion(self, expansion: str) -> dict[str, object]:
        """Replace every generated presentation of this raw expansion."""

        mutated = copy.deepcopy(self.raw_audit)
        for section in ("boundary_input_items", "conclusion_dependency_items"):
            for item in mutated[section]:
                for field in ("expanded_input_type", "expanded_binder_type"):
                    if isinstance(item.get(field), str):
                        item[field] = expansion
                alias = item.get("proposition_alias_expansion")
                if isinstance(alias, dict):
                    alias["expanded_type"] = expansion
        return mutated

    def append_opaque_review_predicate(self) -> str:
        """Declare a type-correct opaque spoof only in this test overlay."""

        declaration = "sourceDefinitionRouteOpaquePredicate"
        interface = self.paper_dir / "PaperInterface.lean"
        interface.write_text(
            interface.read_text(encoding="utf-8")
            + "\nnamespace KR21Monoculture.PaperInterface\n"
            + f"opaque {declaration} (f : ℝ → ℝ) : Prop\n"
            + "end KR21Monoculture.PaperInterface\n",
            encoding="utf-8",
        )
        return f"KR21Monoculture.PaperInterface.{declaration}"

    def synthetic_semantic_bridge_verdict(
        self,
        declarations: str,
        *,
        lemma: str,
        binder_index: int,
        definition: str,
        raw_expansion: str,
        review_surface: str,
    ) -> dict[str, object]:
        """Run the helper directly on a tiny declaration-coordinate fixture."""

        helper = ROUTE.LEAN_META_HELPER_PATH.read_text(encoding="utf-8")
        script = (
            "import Lean\n\n"
            + declarations
            + "\n\n"
            + helper
            + "\n\n#source_definition_antecedent_semantic_bridge "
            + json.dumps(lemma, ensure_ascii=False)
            + " "
            + json.dumps(str(binder_index), ensure_ascii=False)
            + " "
            + json.dumps(definition, ensure_ascii=False)
            + " "
            + json.dumps(raw_expansion, ensure_ascii=False)
            + " "
            + json.dumps(review_surface, ensure_ascii=False)
            + "\n"
        )
        temporary: Path | None = None
        try:
            with tempfile.NamedTemporaryFile(
                dir=ROUTE._lean_overlay_temp_dir(),
                prefix=".source_definition_antecedent_telescope_",
                suffix=".lean",
                delete=False,
                mode="w",
                encoding="utf-8",
            ) as handle:
                handle.write(script)
                temporary = Path(handle.name)
            completed = ROUTE.subprocess.run(
                ["lake", "env", "lean", str(temporary)],
                cwd=ROOT,
                check=False,
                capture_output=True,
                text=True,
                timeout=ROUTE.LEAN_BRIDGE_TIMEOUT_SECONDS,
            )
            self.assertEqual(
                completed.returncode,
                0,
                completed.stderr + "\n" + completed.stdout,
            )
            verdict_lines = [
                line[len(ROUTE.LEAN_META_BRIDGE_SENTINEL) :]
                for line in completed.stdout.splitlines()
                if line.startswith(ROUTE.LEAN_META_BRIDGE_SENTINEL)
            ]
            self.assertEqual(len(verdict_lines), 1, completed.stdout)
            verdict = json.loads(verdict_lines[0])
            self.assertIsInstance(verdict, dict)
            return verdict
        finally:
            if temporary is not None and temporary.exists():
                temporary.unlink()

    def test_materialized_item_replays_all_current_member_pins(self) -> None:
        receipt = self.build()
        self.assertEqual(len(receipt["routes"]), 1)
        route = receipt["routes"][0]
        pins = route["raw_input"]["full_member_pins"]
        self.assertEqual(
            {(pin["section"], pin["kind"]) for pin in pins},
            {
                ("boundary_input_items", "semantic_proposition_premise"),
                ("conclusion_dependency_items", "aliased_conclusion_bridge_input"),
            },
        )
        self.write_receipt(receipt)
        materialized = self.materialize(receipt)

        # Only the selected item changes. A stale root aggregate and sibling
        # remain untouched, so this cannot accidentally refresh the sidecar.
        self.assertEqual(
            materialized["source_record_audit_sha256"],
            self.sidecar["source_record_audit_sha256"],
        )
        self.assertEqual(
            materialized["items"]["unrelated stale row"],
            self.sidecar["items"]["unrelated stale row"],
        )
        item = materialized["items"][TARGET_KEY]
        self.assertEqual(
            item["source_record_audit_sha256"],
            self.raw_audit["source_record_audit_sha256"],
        )
        self.assertEqual(item["source_record_item_sha256s"], pins)
        self.assertEqual(
            item[ROUTE.MATERIALIZATION_FIELD]["full_member_pins_sha256"],
            route["raw_input"]["full_member_pins_sha256"],
        )
        self.assertEqual(
            ROUTE.validate_current_source_definition_antecedent_reissue_item(
                item,
                judgment_key=TARGET_KEY,
                paper=PAPER,
                paper_dir=self.paper_dir,
                raw_audit=self.raw_audit,
                statement_map=self.statement_map,
                statement_matches=self.statement_matches,
            ),
            item,
        )

    def test_receipt_rejects_same_terminal_in_a_different_namespace(self) -> None:
        receipt = self.build()
        mutated = copy.deepcopy(self.statement_matches)
        entries = mutated["items"][LEMMA_RECORD_KEY]["semantic_scope_review"][
            "named_definition_review"
        ]["items"]
        for entry in entries:
            if entry.get("surface_expression") == "KR21Monoculture.StrictlyWellOrderedNoise f":
                entry["surface_expression"] = "OtherNamespace.StrictlyWellOrderedNoise f"
                break
        else:  # The test fixture must retain the reviewed input surface.
            self.fail("KR21 v10 record no longer exposes the strict-order input atom")
        with self.assertRaises(ROUTE.SourceDefinitionAntecedentRouteError):
            self.validate_receipt(receipt, statement_matches=mutated)

    def test_receipt_rejects_a_mutated_definition_inequality(self) -> None:
        receipt = self.build()
        mutated = copy.deepcopy(self.statement_matches)
        entries = mutated["items"][DEFINITION_RECORD_KEY]["semantic_scope_review"][
            "named_definition_review"
        ]["items"]
        for entry in entries:
            surface = entry.get("surface_expression")
            if isinstance(surface, str) and " ↔ " in surface:
                entry["surface_expression"] = surface.replace(" > ", " ≥ ", 1)
                break
        else:
            self.fail("KR21 v10 definition record no longer exposes an IFF surface")
        with self.assertRaises(ROUTE.SourceDefinitionAntecedentRouteError):
            self.validate_receipt(receipt, statement_matches=mutated)

    def test_fresh_semantic_definition_mutations_fail_closed(self) -> None:
        """Fresh route construction rejects semantic IFF changes in Lean.

        These are deliberately not receipt-replay tests: each altered review
        surface must reach the current semantic bridge rather than merely
        mismatch an old textual receipt pin.
        """

        original = self.definition_review_entry(self.statement_matches)[
            "surface_expression"
        ]
        assert isinstance(original, str)
        left, right = original.split(" ↔ ", 1)

        mutations = {
            "inequality": original.replace(" > ", " ≥ ", 1),
            "reversed_iff": f"{right} ↔ {left}",
        }
        for label, surface in mutations.items():
            with self.subTest(label=label):
                mutated = copy.deepcopy(self.statement_matches)
                self.definition_review_entry(mutated)["surface_expression"] = surface
                original_bridge = ROUTE._run_source_overlay_meta_bridge
                with mock.patch.object(
                    ROUTE,
                    "_run_source_overlay_meta_bridge",
                    wraps=original_bridge,
                ) as bridge:
                    self.assert_fresh_build_rejects(statement_matches=mutated)
                self.assertGreater(
                    bridge.call_count,
                    0,
                    "the malformed review must be rejected by the semantic bridge",
                )

        # A type-correct opaque replacement is the critical non-textual spoof:
        # it can elaborate but must not be accepted as the definition's actual
        # IFF side.
        opaque = self.append_opaque_review_predicate()
        mutated = copy.deepcopy(self.statement_matches)
        self.definition_review_entry(mutated)["surface_expression"] = original.replace(
            "KR21Monoculture.PaperInterface.strictlyWellOrderedNoise", opaque, 1
        )
        original_bridge = ROUTE._run_source_overlay_meta_bridge
        with mock.patch.object(
            ROUTE,
            "_run_source_overlay_meta_bridge",
            wraps=original_bridge,
        ) as bridge:
            self.assert_fresh_build_rejects(statement_matches=mutated)
        self.assertGreater(
            bridge.call_count,
            0,
            "an opaque spoof must be rejected by the semantic bridge",
        )

    def test_fresh_raw_sorry_expansion_fails_closed(self) -> None:
        """A raw expansion containing ``sorry`` cannot enter a new receipt."""

        original_bridge = ROUTE._run_source_overlay_meta_bridge
        with mock.patch.object(
            ROUTE,
            "_run_source_overlay_meta_bridge",
            wraps=original_bridge,
        ) as bridge:
            self.assert_fresh_build_rejects(
                raw_audit=self.raw_audit_with_expansion("sorry")
            )
        self.assertGreater(
            bridge.call_count,
            0,
            "a raw sorry must reach the semantic bridge rather than a receipt check",
        )

    def test_fresh_alpha_renaming_and_parentheses_are_accepted(self) -> None:
        """Alpha-equivalent reviewed formulas do not depend on display text."""

        mutated = copy.deepcopy(self.statement_matches)
        self.definition_review_entry(mutated)["surface_expression"] = (
            "(KR21Monoculture.PaperInterface.strictlyWellOrderedNoise f) ↔ "
            "((∀ ⦃x y z w : ℝ⦄, y < x → w < z → "
            "f (x - z) * f (y - w) > f (x - w) * f (y - z)))"
        )
        rebuilt = self.fresh_build(statement_matches=mutated)
        self.assertEqual(len(rebuilt["routes"]), 1)
        endpoint = rebuilt["routes"][0]["definition"]["endpoint"]
        self.assertEqual(endpoint["formula_iff_side"], "right")

    def test_reordered_same_name_telescope_cannot_rebind_raw_text(self) -> None:
        """A shared spelling cannot silently mean different binder coordinates."""

        verdict = self.synthetic_semantic_bridge_verdict(
            """
namespace SyntheticTelescope
axiom reorderedLemma (x y : Nat) (h : x < y) : True
axiom reorderedDefinition (y x : Nat) : (x < y) ↔ (y < x)
end SyntheticTelescope
""",
            lemma="SyntheticTelescope.reorderedLemma",
            binder_index=2,
            definition="SyntheticTelescope.reorderedDefinition",
            raw_expansion="x < y",
            review_surface="x < y ↔ y < x",
        )
        self.assertEqual(verdict["schema"], "3")
        self.assertTrue(verdict["raw_expansion_matches_lemma_binder"])
        self.assertFalse(verdict["parameter_correspondence_established"])
        self.assertTrue(
            str(verdict["failure_tag"]),
            "a reordered same-name telescope must fail instead of selecting an IFF side",
        )

    def test_renamed_definition_binders_use_coordinate_correspondence(self) -> None:
        """A valid bridge is independent of presentation binder spellings."""

        verdict = self.synthetic_semantic_bridge_verdict(
            """
namespace SyntheticTelescope
abbrev renamedPredicate (a b : Nat) : Prop := a < b
axiom renamedLemma (x y : Nat) (h : x < y) : True
axiom renamedDefinition (a b : Nat) : renamedPredicate a b ↔ a < b
end SyntheticTelescope
""",
            lemma="SyntheticTelescope.renamedLemma",
            binder_index=2,
            definition="SyntheticTelescope.renamedDefinition",
            raw_expansion="x < y",
            review_surface="SyntheticTelescope.renamedPredicate a b ↔ a < b",
        )
        self.assertEqual(verdict["schema"], "3")
        self.assertTrue(verdict["parameter_correspondence_established"])
        self.assertEqual(
            verdict["parameter_correspondence_method"],
            "unique_type_checked_coordinate_bijection",
        )
        self.assertEqual(verdict["review_formula_iff_side"], "right")
        self.assertEqual(
            verdict["parameter_correspondence"],
            [
                {"definition_binder_index": "0", "lemma_binder_index": "0"},
                {"definition_binder_index": "1", "lemma_binder_index": "1"},
            ],
        )

    def test_formula_preserves_whitespace_inside_string_literals(self) -> None:
        """Formula hashing/elaboration must retain literal bytes verbatim."""

        spaced = 'Tag "a  b"'
        compact = 'Tag "a b"'
        self.assertEqual(ROUTE._formula(f"  {spaced}  "), spaced)
        self.assertNotEqual(ROUTE._formula(spaced), ROUTE._formula(compact))
        self.assertNotEqual(
            ROUTE._formula_digest(spaced), ROUTE._formula_digest(compact)
        )

    def test_receipt_rejects_an_unrelated_definition_with_the_same_expansion(self) -> None:
        receipt = self.build()
        mutated = copy.deepcopy(self.statement_matches)
        entries = mutated["items"][DEFINITION_RECORD_KEY]["semantic_scope_review"][
            "named_definition_review"
        ]["items"]
        for entry in entries:
            surface = entry.get("surface_expression")
            if isinstance(surface, str) and " ↔ " in surface:
                left, right = surface.split(" ↔ ", 1)
                self.assertEqual(
                    left, "KR21Monoculture.PaperInterface.strictlyWellOrderedNoise f"
                )
                entry["surface_expression"] = (
                    "KR21Monoculture.PaperInterface.unrelatedPredicate f ↔ " + right
                )
                break
        else:
            self.fail("KR21 v10 definition record no longer exposes an IFF surface")
        with self.assertRaises(ROUTE.SourceDefinitionAntecedentRouteError):
            self.validate_receipt(receipt, statement_matches=mutated)

    def test_receipt_rejects_an_ambiguous_definition_route(self) -> None:
        receipt = self.build()
        mutated = copy.deepcopy(self.statement_map)
        mutated["items"]["another_definition_copy"] = copy.deepcopy(
            mutated["items"][DEFINITION_SOURCE_KEY]
        )
        with self.assertRaises(ROUTE.SourceDefinitionAntecedentRouteError):
            self.validate_receipt(receipt, statement_map=mutated)

    def test_receipt_identity_does_not_depend_on_map_or_record_storage_names(self) -> None:
        receipt = self.build()
        renamed_map = copy.deepcopy(self.statement_map)
        renamed_map["items"] = {
            "unrelated_map_slot_for_result": renamed_map["items"].pop(LEMMA_SOURCE_KEY),
            "unrelated_map_slot_for_definition": renamed_map["items"].pop(
                DEFINITION_SOURCE_KEY
            ),
        }
        renamed_matches = copy.deepcopy(self.statement_matches)
        renamed_matches["items"] = {
            "unrelated_statement_record_a": renamed_matches["items"].pop(
                LEMMA_RECORD_KEY
            ),
            "unrelated_statement_record_b": renamed_matches["items"].pop(
                DEFINITION_RECORD_KEY
            ),
        }
        rebuilt = ROUTE.build_source_definition_antecedent_receipt(
            paper=PAPER,
            paper_dir=self.paper_dir,
            raw_audit=self.raw_audit,
            statement_map=renamed_map,
            statement_matches=renamed_matches,
        )
        self.assertEqual(len(rebuilt["routes"]), 1)
        self.assertEqual(
            rebuilt["routes"][0]["route_identity_sha256"],
            receipt["routes"][0]["route_identity_sha256"],
        )

    def test_gate_rejects_a_tampered_or_unreceipted_materialization(self) -> None:
        receipt = self.build()
        self.write_receipt(receipt)
        materialized = self.materialize(receipt)
        tampered = copy.deepcopy(materialized["items"][TARGET_KEY])
        tampered["source_record_item_sha256s"] = tampered[
            "source_record_item_sha256s"
        ][:-1]
        with self.assertRaises(ROUTE.SourceDefinitionAntecedentRouteError):
            ROUTE.validate_current_source_definition_antecedent_reissue_item(
                tampered,
                judgment_key=TARGET_KEY,
                paper=PAPER,
                paper_dir=self.paper_dir,
                raw_audit=self.raw_audit,
                statement_map=self.statement_map,
                statement_matches=self.statement_matches,
            )
        unreceipted = copy.deepcopy(materialized["items"][TARGET_KEY])
        del unreceipted[ROUTE.MATERIALIZATION_FIELD]
        with self.assertRaises(ROUTE.SourceDefinitionAntecedentRouteError):
            ROUTE.validate_current_source_definition_antecedent_reissue_item(
                unreceipted,
                judgment_key=TARGET_KEY,
                paper=PAPER,
                paper_dir=self.paper_dir,
                raw_audit=self.raw_audit,
                statement_map=self.statement_map,
                statement_matches=self.statement_matches,
            )

    def test_loader_requires_route_receipt_for_a_multisurface_item_reissue(self) -> None:
        receipt = self.build()
        self.write_receipt(receipt)
        self.write_loader_inputs()
        materialized = self.materialize(receipt)
        helper = load_source_record_audit_helper()

        accepted = helper.current_source_record_judgments_from_payload(
            materialized,
            PAPER,
            self.raw_audit,
            paper_dir=self.paper_dir,
        )
        self.assertIn(TARGET_KEY, accepted)

        # Rewriting only the item aggregate under a stale root must not work:
        # a two-surface group needs the independently replayed route receipt.
        unreceipted = copy.deepcopy(materialized)
        del unreceipted["items"][TARGET_KEY][ROUTE.MATERIALIZATION_FIELD]
        self.assertNotIn(
            TARGET_KEY,
            helper.current_source_record_judgments_from_payload(
                unreceipted,
                PAPER,
                self.raw_audit,
                paper_dir=self.paper_dir,
            ),
        )
        malformed = copy.deepcopy(materialized)
        malformed["items"][TARGET_KEY][ROUTE.MATERIALIZATION_FIELD][
            "full_member_pins_sha256"
        ] = "f" * 64
        self.assertNotIn(
            TARGET_KEY,
            helper.current_source_record_judgments_from_payload(
                malformed,
                PAPER,
                self.raw_audit,
                paper_dir=self.paper_dir,
            ),
        )

        # A wholly current ordinary sidecar keeps its existing compatibility
        # path; this guard is specific to partial per-item aggregate rewrites.
        root_current = copy.deepcopy(unreceipted)
        root_current["source_record_audit_sha256"] = self.raw_audit[
            "source_record_audit_sha256"
        ]
        self.assertIn(
            TARGET_KEY,
            helper.current_source_record_judgments_from_payload(
                root_current,
                PAPER,
                self.raw_audit,
                paper_dir=self.paper_dir,
            ),
        )

        conclusion_accepted = CONCLUSION._current_judgments_from_payload(
            PAPER,
            self.raw_audit,
            materialized,
            paper_dir=self.paper_dir,
        )
        self.assertIn(TARGET_KEY, conclusion_accepted)
        self.assertNotIn(
            TARGET_KEY,
            CONCLUSION._current_judgments_from_payload(
                PAPER,
                self.raw_audit,
                malformed,
                paper_dir=self.paper_dir,
            ),
        )
        self.assertNotIn(
            TARGET_KEY,
            CONCLUSION._current_judgments_from_payload(
                PAPER,
                self.raw_audit,
                unreceipted,
                paper_dir=self.paper_dir,
            ),
        )

    def test_both_loaders_replay_materialized_receipt_with_fresh_bridge(self) -> None:
        """Consumers revalidate a receipt through focused current overlays only."""

        receipt = self.build()
        self.write_receipt(receipt)
        self.write_loader_inputs()
        materialized = self.materialize(receipt)
        helper = load_source_record_audit_helper()
        observed: list[list[str]] = []
        real_run = ROUTE.subprocess.run

        def guarded_run(command: object, *args: object, **kwargs: object) -> object:
            assert isinstance(command, list)
            rendered = [str(part) for part in command]
            observed.append(rendered)
            return real_run(command, *args, **kwargs)

        original_bridge = ROUTE._run_source_overlay_meta_bridge
        with mock.patch.object(ROUTE.subprocess, "run", side_effect=guarded_run), mock.patch.object(
            ROUTE,
            "_run_source_overlay_meta_bridge",
            wraps=original_bridge,
        ) as bridge:
            ROUTE._LEAN_CHECKER_IDENTITY_CACHE = None
            accepted = helper.current_source_record_judgments_from_payload(
                materialized,
                PAPER,
                self.raw_audit,
                paper_dir=self.paper_dir,
            )
            self.assertIn(TARGET_KEY, accepted)
            source_loader_bridge_calls = bridge.call_count
            self.assertGreater(
                source_loader_bridge_calls,
                0,
                "source-record loading must freshly reconstruct the route",
            )

            # A second consumer is independent: it must replay the receipt
            # through its own current source-overlay validation rather than
            # inherit a prior bridge outcome.
            ROUTE._LEAN_CHECKER_IDENTITY_CACHE = None
            conclusion_accepted = CONCLUSION._current_judgments_from_payload(
                PAPER,
                self.raw_audit,
                materialized,
                paper_dir=self.paper_dir,
            )
            self.assertIn(TARGET_KEY, conclusion_accepted)
            self.assertGreater(
                bridge.call_count,
                source_loader_bridge_calls,
                "conclusion provenance must independently replay the route",
            )

        self.assertGreaterEqual(
            observed.count(["lake", "build", f"{PAPER}.PaperInterface"]),
            2,
            "each cold consumer must retain the mandatory incremental paper build",
        )
        self.assertGreaterEqual(
            observed.count(["lake", "env", "lean", "--version"]),
            2,
            "each cold consumer must recompute its checker identity",
        )
        temporary_overlays = [
            command
            for command in observed
            if command[:3] == ["lake", "env", "lean"]
            and len(command) == 4
            and command[3] != "--version"
        ]
        self.assertGreaterEqual(
            len(temporary_overlays),
            2,
            "both consumers must use fresh narrow overlays rather than a sealed cache",
        )
        self.assertTrue(
            all(command and command[0] == "lake" for command in observed),
            "loader validation must not launch a raw-audit regeneration command",
        )


class SourceDefinitionSpecialRouteRetirementTests(unittest.TestCase):
    def test_conclusion_loader_exposes_no_definition_specific_acceptance_hook(
        self,
    ) -> None:
        self.assertFalse(
            hasattr(CONCLUSION, "_current_definition_antecedent_route_context")
        )
        self.assertFalse(
            hasattr(CONCLUSION, "_sealed_definition_route_receipts_from_sidecar")
        )


if __name__ == "__main__":
    unittest.main()
