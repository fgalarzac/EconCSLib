#!/usr/bin/env python3
"""Tests for name-independent accepted-assumption source parents."""

from __future__ import annotations

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

from scripts import review_dashboard as DASHBOARD  # noqa: E402
from scripts import semantic_audit_reuse as REUSE  # noqa: E402
from scripts import audit_conclusion_provenance as CONCLUSION  # noqa: E402
from scripts import source_record_target_disposition as TARGET  # noqa: E402
from scripts.formalization_protocol import (  # noqa: E402
    formalization_review_protocol_digest,
)
from scripts.lean_signature_manifest import (  # noqa: E402
    run_lean_signature_manifests_for_source,
)
from scripts.source_record_assumption_association import (  # noqa: E402
    SOURCE_ASSUMPTION_ASSOCIATION_FIELD,
    SOURCE_ASSUMPTION_REVIEW_IDENTITY_FIELD,
    build_source_assumption_association,
    outer_assumption_atom_partition,
    source_assumption_alias_group_digest,
    source_assumption_effective_semantic_pin,
    source_assumption_premise_review_digest,
    transparent_conclusion_component_partition,
    transparent_type_carrier_partition,
)


HELPER = ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
SPEC = importlib.util.spec_from_file_location(
    "econcs_source_record_assumption_test_audit", HELPER
)
assert SPEC is not None and SPEC.loader is not None
AUDIT = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = AUDIT
SPEC.loader.exec_module(AUDIT)


def sha(character: str) -> str:
    return character * 64


def valid_association(
    *,
    declaration_name: str = "Fixture.SourceCondition",
    source_key: str = "fixture_source_condition",
) -> dict[str, object]:
    route_sha = sha("7")
    partition, partition_error = outer_assumption_atom_partition([sha("3")])
    assert partition is not None, partition_error
    component_sha = partition["components"][0]["component_occurrence_sha256"]
    premise: dict[str, object] = {
        "lean_component_occurrence_sha256s": [component_sha],
        "judgment": "paper_condition",
        "reason": "The displayed source model states this domain condition.",
        "source_route_semantic_sha256s": [route_sha],
        "presentation_count": 1,
    }
    premise["premise_review_sha256"] = source_assumption_premise_review_digest(
        premise
    )
    source_pin = {
        "schema": 2,
        "source_item_semantic_sha256": sha("4"),
        "source_anchor_quote_identity_sha256": sha("5"),
        "source_target_sha256": sha("6"),
        "source_target_disposition": {"kind": "ordinary_or_convention"},
    }
    review_semantic_payload = {
        "schema": 1,
        "judgment": "paper_condition",
        "lean_semantic_partition_sha256": partition["partition_sha256"],
        "premise_reviews": [
            {
                "premise_review_sha256": premise["premise_review_sha256"],
                "presentation_count": 1,
            }
        ],
        "premise_alias_group_sha256s": [],
        "source_route_semantic_sha256s": [route_sha],
    }
    review_identity = {
        "schema": 1,
        "declaration_content_sha256": sha("1"),
        "elaborated_signature_sha256": sha("2"),
        "manifest_structure_sha256": sha("8"),
        "semantic_dependency_sha256": sha("9"),
        "review_validator_identity_sha256": sha("a"),
        "review_protocol_sha256": sha("b"),
        "assumption_review_semantic_sha256": AUDIT.stable_digest(
            review_semantic_payload
        ),
        "judgment": "paper_condition",
        "lean_semantic_partition": partition,
        "premise_receipts": [premise],
        "premise_alias_group_receipts": [],
        "source_route_receipts": [
            {
                "route_semantic_sha256": route_sha,
                "source_reuse_pin": source_pin,
                "source_reuse_pin_sha256": AUDIT.stable_digest(source_pin),
                "source_parent_semantic_sha256": sha("4"),
            }
        ],
    }
    association, error = build_source_assumption_association(
        reviewed_declaration_identity={
            "qualified_declaration": declaration_name,
            "declaration_sha256": sha("1"),
        },
        reviewed_signature_identity={
            "qualified_declaration": declaration_name,
            "elaborated_signature_sha256": sha("2"),
        },
        source_item_identities=[
            {
                "source_key": source_key,
                "source_location": "source.txt:10-12",
                "source_map_item_sha256": sha("c"),
                "source_semantic_sha256": sha("4"),
            }
        ],
        review_identity=review_identity,
    )
    assert association is not None, error
    return association


def association_for_partition(
    partition: dict[str, object],
    premise_receipts: list[dict[str, object]],
    alias_group_receipts: list[dict[str, object]] | None = None,
) -> dict[str, object]:
    """Build a complete association around a supplied Lean partition."""

    aliases = alias_group_receipts or []
    for receipt in premise_receipts:
        receipt["premise_review_sha256"] = source_assumption_premise_review_digest(
            receipt
        )
    for receipt in aliases:
        receipt["alias_group_sha256"] = source_assumption_alias_group_digest(
            receipt
        )
    route_sha = sha("7")
    source_pin = {
        "schema": 2,
        "source_item_semantic_sha256": sha("4"),
        "source_anchor_quote_identity_sha256": sha("5"),
        "source_target_sha256": sha("6"),
        "source_target_disposition": {"kind": "ordinary_or_convention"},
    }
    review_semantic_payload = {
        "schema": 1,
        "judgment": "paper_condition",
        "lean_semantic_partition_sha256": partition["partition_sha256"],
        "premise_reviews": sorted(
            (
                {
                    "premise_review_sha256": receipt["premise_review_sha256"],
                    "presentation_count": receipt["presentation_count"],
                }
                for receipt in premise_receipts
            ),
            key=lambda value: value["premise_review_sha256"],
        ),
        "premise_alias_group_sha256s": sorted(
            receipt["alias_group_sha256"] for receipt in aliases
        ),
        "source_route_semantic_sha256s": [route_sha],
    }
    review_identity = {
        "schema": 1,
        "declaration_content_sha256": sha("1"),
        "elaborated_signature_sha256": sha("2"),
        "manifest_structure_sha256": sha("8"),
        "semantic_dependency_sha256": sha("9"),
        "review_validator_identity_sha256": sha("a"),
        "review_protocol_sha256": sha("b"),
        "assumption_review_semantic_sha256": AUDIT.stable_digest(
            review_semantic_payload
        ),
        "judgment": "paper_condition",
        "lean_semantic_partition": partition,
        "premise_receipts": premise_receipts,
        "premise_alias_group_receipts": aliases,
        "source_route_receipts": [
            {
                "route_semantic_sha256": route_sha,
                "source_reuse_pin": source_pin,
                "source_reuse_pin_sha256": AUDIT.stable_digest(source_pin),
                "source_parent_semantic_sha256": sha("4"),
            }
        ],
    }
    association, error = build_source_assumption_association(
        reviewed_declaration_identity={
            "qualified_declaration": "Fixture.SourceCondition",
            "declaration_sha256": sha("1"),
        },
        reviewed_signature_identity={
            "qualified_declaration": "Fixture.SourceCondition",
            "elaborated_signature_sha256": sha("2"),
        },
        source_item_identities=[
            {
                "source_key": "fixture_source_condition",
                "source_location": "source.txt:10-12",
                "source_map_item_sha256": sha("c"),
                "source_semantic_sha256": sha("4"),
            }
        ],
        review_identity=review_identity,
    )
    assert association is not None, error
    return association


class SourceAssumptionAssociationTests(unittest.TestCase):
    def test_effective_pin_does_not_depend_on_declaration_or_source_key_names(self) -> None:
        first = valid_association()
        renamed = valid_association(
            declaration_name="Renamed.UnrelatedCoordinate",
            source_key="renamed_navigation_coordinate",
        )
        first_pin, first_error = source_assumption_effective_semantic_pin(first)
        renamed_pin, renamed_error = source_assumption_effective_semantic_pin(renamed)
        self.assertEqual(first_error, "")
        self.assertEqual(renamed_error, "")
        self.assertEqual(first_pin, renamed_pin)
        self.assertNotEqual(first["association_sha256"], renamed["association_sha256"])

    def test_stale_declaration_signature_or_premise_receipt_fails_closed(self) -> None:
        for mutate in (
            lambda value: value["reviewed_declaration_identity"].__setitem__(
                "declaration_sha256", sha("d")
            ),
            lambda value: value["reviewed_elaborated_signature_identity"].__setitem__(
                "elaborated_signature_sha256", sha("e")
            ),
            lambda value: value[SOURCE_ASSUMPTION_REVIEW_IDENTITY_FIELD][
                "premise_receipts"
            ][0].__setitem__("reason", "Changed semantic judgment."),
        ):
            association = deepcopy(valid_association())
            mutate(association)
            _pin, error = source_assumption_effective_semantic_pin(association)
            self.assertTrue(error)

    def test_partial_or_additional_judgment_cannot_become_source_parent(self) -> None:
        association = deepcopy(valid_association())
        association[SOURCE_ASSUMPTION_REVIEW_IDENTITY_FIELD]["judgment"] = (
            "documented_additional_assumption"
        )
        _pin, error = source_assumption_effective_semantic_pin(association)
        self.assertIn("accepted source judgment", error)

    def test_source_record_and_conclusion_consumers_recompute_assumption_pin(self) -> None:
        association = valid_association()
        expected_pin, error = source_assumption_effective_semantic_pin(association)
        self.assertEqual(error, "")
        projected_pin, schema_two, projection_error = (
            TARGET._source_record_projection_association_pin(
                association, field=SOURCE_ASSUMPTION_ASSOCIATION_FIELD
            )
        )
        self.assertTrue(schema_two)
        self.assertEqual(projection_error, "")
        self.assertEqual(projected_pin, expected_pin)
        self.assertEqual(
            CONCLUSION._semantic_model_source_association(
                {SOURCE_ASSUMPTION_ASSOCIATION_FIELD: association}
            ),
            (association, expected_pin),
        )

        stale = deepcopy(association)
        stale[SOURCE_ASSUMPTION_REVIEW_IDENTITY_FIELD]["premise_receipts"][0][
            "reason"
        ] = "Unreviewed replacement semantics."
        self.assertIsNone(
            CONCLUSION._semantic_model_source_association(
                {SOURCE_ASSUMPTION_ASSOCIATION_FIELD: stale}
            )
        )


class TransparentAssumptionPartitionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        source = """
abbrev conjunctive (a b c : Nat) : Prop := a = 0 ∧ b = 0 ∧ c = 0
abbrev renamedConjunctive (first second third : Nat) : Prop :=
  first = 0 ∧ second = 0 ∧ third = 0
abbrev reorderedConjunctive (a b c : Nat) : Prop := c = 0 ∧ a = 0 ∧ b = 0
abbrev atomic (a : Nat) : Prop := a = 0
opaque hiddenProposition (a b : Prop) : Prop := a ∧ b
abbrev TypeCarrier (T : Type) : Type := T × T
opaque HiddenTypeCarrier (T : Type) : Type := T × T
"""
        cls.manifests = run_lean_signature_manifests_for_source(
            ROOT,
            source,
            [
                "conjunctive",
                "renamedConjunctive",
                "reorderedConjunctive",
                "atomic",
                "hiddenProposition",
                "TypeCarrier",
                "HiddenTypeCarrier",
            ],
        )
        if len(cls.manifests) != 7:
            raise AssertionError("Lean did not emit all partition test manifests")

    @staticmethod
    def premise(
        components: list[str], reason: str, *, presentation_count: int = 1
    ) -> dict[str, object]:
        return {
            "lean_component_occurrence_sha256s": components,
            "judgment": "paper_condition",
            "reason": reason,
            "source_route_semantic_sha256s": [sha("7")],
            "presentation_count": presentation_count,
        }

    def test_conjunctive_transparent_value_has_complete_lean_partition(self) -> None:
        partition, error = transparent_conclusion_component_partition(
            self.manifests["conjunctive"]
        )
        self.assertEqual(error, "")
        self.assertIsNotNone(partition)
        self.assertEqual(len(partition["components"]), 3)

    def test_names_do_not_change_partition_and_reorder_retains_component_multiset(self) -> None:
        original, _ = transparent_conclusion_component_partition(
            self.manifests["conjunctive"]
        )
        renamed, _ = transparent_conclusion_component_partition(
            self.manifests["renamedConjunctive"]
        )
        reordered, _ = transparent_conclusion_component_partition(
            self.manifests["reorderedConjunctive"]
        )
        self.assertEqual(original, renamed)
        original_components = {
            item["component_occurrence_sha256"] for item in original["components"]
        }
        reordered_components = {
            item["component_occurrence_sha256"] for item in reordered["components"]
        }
        self.assertEqual(original_components, reordered_components)
        self.assertNotEqual(
            original["proposition_graph_sha256"],
            reordered["proposition_graph_sha256"],
        )

    def test_dropped_component_and_unaliased_duplicate_fail_closed(self) -> None:
        partition, _ = transparent_conclusion_component_partition(
            self.manifests["conjunctive"]
        )
        component_shas = [
            item["component_occurrence_sha256"] for item in partition["components"]
        ]
        with self.assertRaises(AssertionError):
            association_for_partition(
                partition,
                [self.premise(component_shas[:-1], "Incomplete source coverage.")],
            )

        atomic_partition, _ = transparent_conclusion_component_partition(
            self.manifests["atomic"]
        )
        atomic_component = atomic_partition["components"][0][
            "component_occurrence_sha256"
        ]
        with self.assertRaises(AssertionError):
            association_for_partition(
                atomic_partition,
                [
                    self.premise([atomic_component], "First reviewed presentation."),
                    self.premise([atomic_component], "Second reviewed presentation."),
                ],
            )

    def test_explicit_alias_group_allows_distinct_review_presentations(self) -> None:
        partition, _ = transparent_conclusion_component_partition(
            self.manifests["atomic"]
        )
        component = partition["components"][0]["component_occurrence_sha256"]
        premises = [
            self.premise([component], "First source-use presentation."),
            self.premise([component], "Different source-use presentation."),
        ]
        for premise in premises:
            premise["premise_review_sha256"] = source_assumption_premise_review_digest(
                premise
            )
        alias = {
            "lean_component_occurrence_sha256s": [component],
            "members": [
                {
                    "premise_review_sha256": premise["premise_review_sha256"],
                    "presentation_count": 1,
                }
                for premise in premises
            ],
            "presentation_count": 2,
        }
        association = association_for_partition(partition, premises, [alias])
        _pin, error = source_assumption_effective_semantic_pin(association)
        self.assertEqual(error, "")

    def test_opaque_and_incomplete_carriers_fail_while_complete_type_carrier_passes(self) -> None:
        hidden_prop, hidden_prop_error = transparent_conclusion_component_partition(
            self.manifests["hiddenProposition"]
        )
        self.assertIsNone(hidden_prop)
        self.assertIn("not a transparent", hidden_prop_error)

        carrier, carrier_error = transparent_type_carrier_partition(
            self.manifests["TypeCarrier"]
        )
        self.assertEqual(carrier_error, "")
        self.assertIsNotNone(carrier)
        hidden_carrier, _ = transparent_type_carrier_partition(
            self.manifests["HiddenTypeCarrier"]
        )
        self.assertIsNone(hidden_carrier)
        incomplete = deepcopy(self.manifests["TypeCarrier"])
        incomplete["semantic_dependency_environment_identities"] = []
        incomplete_carrier, incomplete_error = transparent_type_carrier_partition(
            incomplete
        )
        self.assertIsNone(incomplete_carrier)
        self.assertIn("complete semantic dependency", incomplete_error)


class SourceAssumptionGeneratorTests(unittest.TestCase):
    def _fixture(
        self, paper_dir: Path
    ) -> tuple[list[dict[str, object]], dict[str, object], dict[str, object], str]:
        audit_dir = paper_dir / "audit"
        audit_dir.mkdir(parents=True, exist_ok=True)
        declaration_sha = sha("1")
        signature_sha = sha("2")
        premise_text = "h : SourceDomain x"
        atom = {
            "ref": "arg:0",
            "role": "assumption",
            "binder_info": "explicit",
            "canonical": {"tag": "const", "name": "SourceDomain"},
        }
        atom_sha = DASHBOARD.signature_manifest_atom_digest(atom)
        lean_partition, partition_error = outer_assumption_atom_partition(
            [atom_sha]
        )
        assert lean_partition is not None, partition_error
        component_sha = lean_partition["components"][0][
            "component_occurrence_sha256"
        ]
        route = {
            "source_item": "navigation_only_key",
            "route_kind": "direct",
            "source_statement_sha256": sha("6"),
            "source_location": "source.txt:10-12",
            "semantic_relation": "equivalent",
            "source_support_scope": (
                "This route states the complete displayed source-domain condition "
                "used by the reviewed Lean assumption declaration."
            ),
            "lean_evidence_ids": ["conclusion"],
        }
        route_sha = REUSE.route_semantic_sha256(route)
        source_pin = {"schema": 2, "semantic": sha("4")}
        envelope = {
            "schema": 1,
            "paper": "Fixture",
            "prompt_version": DASHBOARD.REQUIRED_LLM_ASSUMPTION_PROMPT_VERSION,
            "validator": "fixture semantic reviewer",
            "validator_type": "agent",
            "validated_at": "2026-08-03T00:00:00Z",
            "items": {},
        }
        validator_sha = REUSE.review_validator_identities(
            {**envelope, "items": {"opaque-storage-key": {}}},
            expected_prompt_version=DASHBOARD.REQUIRED_LLM_ASSUMPTION_PROMPT_VERSION,
        )[0]["opaque-storage-key"]
        entry = {
            "judgment": "paper_condition",
            "lean_signature_sha256": signature_sha,
            "premises": [premise_text],
            "premise_judgments": {
                premise_text: {
                    "judgment": "source_text_model_primitive",
                    "reason": "The source explicitly states this model-domain condition.",
                    "source_location": "source.txt:10-12",
                    "source_route_semantic_sha256s": [route_sha],
                }
            },
            "source_routes": [route],
            "source_record_semantic_parent_v1": {
                "schema": 1,
                "raw_lean_declaration_sha256": declaration_sha,
                "lean_signature_sha256": signature_sha,
                "manifest_structure_sha256": sha("8"),
                "semantic_dependency_sha256": sha("9"),
                "review_validator_identity_sha256": validator_sha,
                "formalization_review_protocol_sha256": (
                    formalization_review_protocol_digest()
                ),
                "lean_semantic_partition": lean_partition,
                "premise_component_occurrence_sha256s_by_premise": {
                    premise_text: [component_sha]
                },
                "premise_alias_groups": [],
                "reviewed_source_route_semantic_sha256s": [route_sha],
                "source_route_receipts": [
                    {
                        "route_semantic_sha256": route_sha,
                        "source_reuse_pin": source_pin,
                    }
                ],
            },
        }
        envelope["items"] = {"opaque-storage-key": entry}
        (audit_dir / "assumption_match_llm.json").write_text(
            json.dumps(envelope), encoding="utf-8"
        )
        item = {
            "row": "UnrelatedDisplayName",
            "judgment_key": "semantic-model::unrelated-display-name",
            "reviewed_declaration_identity": {
                "qualified_declaration": "Fixture.CurrentCoordinate",
                "declaration_sha256": declaration_sha,
            },
        }
        manifest = {"schema": 2, "atoms": [atom]}
        statement_map = {
            "schema": 5,
            "source_coverage_mode": "named_theory",
            "items": {"source-parent": {}},
        }
        return [item], manifest, statement_map, route_sha

    def test_generator_joins_by_content_and_requires_complete_premise_routes(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            paper_dir = Path(tmpdir) / "papers" / "Fixture"
            items, manifest, statement_map, route_sha = self._fixture(paper_dir)
            source_identity = {
                "source_key": "source-parent",
                "source_location": "source.txt:10-12",
                "source_map_item_sha256": sha("c"),
                "source_semantic_sha256": sha("4"),
            }
            source_pin = {"schema": 2, "semantic": sha("4")}
            bound_routes = [
                {
                    "route_semantic_sha256": route_sha,
                    "source_reuse_pin": source_pin,
                    "source_reuse_pin_sha256": AUDIT.stable_digest(source_pin),
                    "source_parent_semantic_sha256": sha("4"),
                }
            ]
            with (
                patch.object(AUDIT, "source_coverage_mode_from_map", return_value=("named_theory", "")),
                patch.object(AUDIT, "signature_manifest_digest", return_value=sha("2")),
                patch.object(REUSE, "manifest_structure_sha256", return_value=sha("8")),
                patch.object(REUSE, "semantic_dependency_sha256", return_value=(sha("9"), "")),
                patch.object(DASHBOARD, "paper_statement_inventory", return_value={}),
                patch.object(DASHBOARD, "paper_source_component_route_inventory", return_value={}),
                patch.object(DASHBOARD, "paper_source_definition_component_route_inventory", return_value={}),
                patch.object(
                    AUDIT,
                    "_assumption_source_parent_receipts",
                    return_value=([source_identity], bound_routes, ""),
                ),
                patch.object(AUDIT, "explicit_direct_source_route_anchor_errors", return_value=[]),
            ):
                output, errors, counts = AUDIT.attach_assumption_source_review_associations(
                    items,
                    paper_dir=paper_dir,
                    paper_statement_map=statement_map,
                    source_proof_fidelity=None,
                    elaborated_signature_manifests_by_qualified={
                        "Fixture.CurrentCoordinate": manifest
                    },
                    elaborated_signature_sha256_by_qualified={
                        "Fixture.CurrentCoordinate": sha("2")
                    },
                )
            self.assertEqual(errors, [])
            self.assertEqual(counts["assumption_source_review_association_count"], 1)
            self.assertIn(SOURCE_ASSUMPTION_ASSOCIATION_FIELD, output[0])

            # Removing one exact premise-to-route binding must fail.  No name
            # or source locator fallback is allowed.
            sidecar_path = paper_dir / "audit" / "assumption_match_llm.json"
            sidecar = json.loads(sidecar_path.read_text(encoding="utf-8"))
            sidecar["items"]["opaque-storage-key"]["premise_judgments"][
                "h : SourceDomain x"
            ].pop("source_route_semantic_sha256s")
            sidecar_path.write_text(json.dumps(sidecar), encoding="utf-8")
            fresh_items, _, _, _ = self._fixture(paper_dir)
            # _fixture rewrites the sidecar, so remove it again after creating
            # the independent item object.
            sidecar = json.loads(sidecar_path.read_text(encoding="utf-8"))
            sidecar["items"]["opaque-storage-key"]["premise_judgments"][
                "h : SourceDomain x"
            ].pop("source_route_semantic_sha256s")
            sidecar_path.write_text(json.dumps(sidecar), encoding="utf-8")
            with (
                patch.object(AUDIT, "source_coverage_mode_from_map", return_value=("named_theory", "")),
                patch.object(AUDIT, "signature_manifest_digest", return_value=sha("2")),
                patch.object(REUSE, "manifest_structure_sha256", return_value=sha("8")),
                patch.object(REUSE, "semantic_dependency_sha256", return_value=(sha("9"), "")),
                patch.object(DASHBOARD, "paper_statement_inventory", return_value={}),
                patch.object(DASHBOARD, "paper_source_component_route_inventory", return_value={}),
                patch.object(DASHBOARD, "paper_source_definition_component_route_inventory", return_value={}),
            ):
                _output, errors, counts = AUDIT.attach_assumption_source_review_associations(
                    fresh_items,
                    paper_dir=paper_dir,
                    paper_statement_map=statement_map,
                    source_proof_fidelity=None,
                    elaborated_signature_manifests_by_qualified={
                        "Fixture.CurrentCoordinate": manifest
                    },
                    elaborated_signature_sha256_by_qualified={
                        "Fixture.CurrentCoordinate": sha("2")
                    },
                )
            self.assertTrue(errors)
            self.assertEqual(counts["assumption_source_review_association_count"], 0)

    def test_duplicate_content_candidates_are_rejected_even_with_distinct_names(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            paper_dir = Path(tmpdir) / "papers" / "Fixture"
            items, manifest, statement_map, _route_sha = self._fixture(paper_dir)
            sidecar_path = paper_dir / "audit" / "assumption_match_llm.json"
            sidecar = json.loads(sidecar_path.read_text(encoding="utf-8"))
            sidecar["items"]["completely-different-name"] = deepcopy(
                sidecar["items"]["opaque-storage-key"]
            )
            sidecar_path.write_text(json.dumps(sidecar), encoding="utf-8")
            with (
                patch.object(AUDIT, "source_coverage_mode_from_map", return_value=("named_theory", "")),
                patch.object(DASHBOARD, "paper_statement_inventory", return_value={}),
                patch.object(DASHBOARD, "paper_source_component_route_inventory", return_value={}),
                patch.object(DASHBOARD, "paper_source_definition_component_route_inventory", return_value={}),
            ):
                output, errors, counts = AUDIT.attach_assumption_source_review_associations(
                    items,
                    paper_dir=paper_dir,
                    paper_statement_map=statement_map,
                    source_proof_fidelity=None,
                    elaborated_signature_manifests_by_qualified={
                        "Fixture.CurrentCoordinate": manifest
                    },
                    elaborated_signature_sha256_by_qualified={
                        "Fixture.CurrentCoordinate": sha("2")
                    },
                )
            self.assertTrue(any("ambiguous" in error for error in errors))
            self.assertNotIn(SOURCE_ASSUMPTION_ASSOCIATION_FIELD, output[0])
            self.assertEqual(counts["assumption_source_review_association_count"], 0)

    def test_opt_in_cache_projection_excludes_storage_keys_and_timestamps(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            paper_dir = Path(tmpdir) / "papers" / "Fixture"
            self._fixture(paper_dir)
            first = AUDIT.assumption_semantic_parent_sidecar_projection(paper_dir)
            self.assertIsNotNone(first)
            sidecar_path = paper_dir / "audit" / "assumption_match_llm.json"
            sidecar = json.loads(sidecar_path.read_text(encoding="utf-8"))
            entry = sidecar["items"].pop("opaque-storage-key")
            sidecar["items"]["renamed-navigation-key"] = entry
            sidecar["validated_at"] = "2099-01-01T00:00:00Z"
            sidecar_path.write_text(json.dumps(sidecar), encoding="utf-8")
            renamed = AUDIT.assumption_semantic_parent_sidecar_projection(paper_dir)
            self.assertEqual(first, renamed)

            entry["premise_judgments"]["h : SourceDomain x"]["reason"] = (
                "A mathematically different premise review."
            )
            sidecar_path.write_text(json.dumps(sidecar), encoding="utf-8")
            changed = AUDIT.assumption_semantic_parent_sidecar_projection(paper_dir)
            self.assertNotEqual(first, changed)


if __name__ == "__main__":
    unittest.main()
