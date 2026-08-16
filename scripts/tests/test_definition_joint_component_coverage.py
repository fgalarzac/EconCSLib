#!/usr/bin/env python3
"""Regression tests for semantic joint coverage of source definitions."""

from __future__ import annotations

import copy
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    text = str(import_root)
    if text not in sys.path:
        sys.path.insert(0, text)

import review_dashboard as DASHBOARD  # noqa: E402


PARENT_KEY = "definition-source-navigation"


def definition_item() -> dict[str, object]:
    statement = "A valid object has both a legal domain and the stated output behavior."
    statement_sha256 = DASHBOARD.statement_digest(statement)
    quote = "An object is valid on the legal domain and returns the stated output there."
    quote_sha256 = hashlib.sha256(quote.encode("utf-8")).hexdigest()
    components = []
    for clause in (
        "The object is evaluated only on inputs in the source legal domain.",
        "On every legal input, the object returns the output specified by the source.",
    ):
        components.append(
            {
                "semantic_clause": clause,
                "semantic_clause_sha256": DASHBOARD.statement_digest(clause),
                "source_location": "source.txt:10-12",
                "source_anchor_evidence": [
                    {
                        "path": "source.txt",
                        "line_start": 10,
                        "line_end": 12,
                        "quoted_text": quote,
                        "quoted_text_sha256": quote_sha256,
                    }
                ],
            }
        )
    return {
        "statement": statement,
        "statement_sha256": statement_sha256,
        "source_location": "source.txt:10-12",
        "source_kind": "definition",
        "lean_declarations": [],
        DASHBOARD.SOURCE_DEFINITION_PARTITION_FIELD: {
            "schema": 1,
            "source_statement_sha256": statement_sha256,
            "semantic_relation": DASHBOARD.SOURCE_DEFINITION_PARTITION_RELATION,
            "complete": True,
            "components_semantically_disjoint": True,
            "completeness_basis": (
                "The source definition consists exactly of its legal-domain clause "
                "and its output-on-that-domain clause, with no residual assertion."
            ),
            "nonoverlap_basis": (
                "One clause restricts admissible inputs while the other determines "
                "outputs on those inputs, so neither clause restates the other."
            ),
            "components": components,
        },
    }


def definition_item_with_discontiguous_component() -> dict[str, object]:
    item = definition_item()
    component = item[DASHBOARD.SOURCE_DEFINITION_PARTITION_FIELD]["components"][0]
    quotes = [
        ("source.txt", 10, "The first exact source span."),
        ("source.txt", 12, "The second exact source span."),
    ]
    component["source_location"] = "source.txt:10; source.txt:12"
    component["source_anchor_evidence"] = [
        {
            "path": path,
            "line_start": line,
            "line_end": line,
            "quoted_text": quote,
            "quoted_text_sha256": hashlib.sha256(quote.encode("utf-8")).hexdigest(),
        }
        for path, line, quote in quotes
    ]
    return item


def component_inventory(
    source_item: dict[str, object],
) -> dict[str, dict[str, object]]:
    partition, errors = DASHBOARD.source_definition_partition_record(source_item)
    assert partition is not None and not errors
    inventory: dict[str, dict[str, object]] = {}
    for component in partition["components"]:
        key = DASHBOARD.source_definition_component_route_key(
            PARENT_KEY,
            component["semantic_clause_sha256"],
            component["source_anchor_sha256"],
        )
        inventory[key] = {
            "statement": component["semantic_clause"],
            "statement_sha256": component["semantic_clause_sha256"],
            "source_location": component["source_location"],
            "source_kind": "definition",
            "source_component_of": PARENT_KEY,
            "source_definition_component": True,
            "source_component_anchor_sha256": component[
                "source_anchor_sha256"
            ],
            "source_definition_partition_sha256": partition[
                "source_definition_partition_sha256"
            ],
            "source_definition_component_sha256": component[
                "source_definition_component_sha256"
            ],
        }
    return inventory


def component_route(key: str, item: dict[str, object]) -> dict[str, object]:
    return {
        "source_item": key,
        "source_statement_sha256": item["statement_sha256"],
        "source_location": item["source_location"],
        "route_kind": "source_component",
        "semantic_relation": DASHBOARD.SOURCE_DEFINITION_COMPONENT_RELATION,
        "source_support_scope": (
            "This Lean conclusion realizes exactly this semantic source clause "
            "without claiming the remaining clauses of the parent definition."
        ),
        "lean_evidence_ids": ["lean-conclusion"],
        "source_component_anchor_sha256": item[
            "source_component_anchor_sha256"
        ],
        "source_definition_partition_sha256": item[
            "source_definition_partition_sha256"
        ],
        "source_definition_component_sha256": item[
            "source_definition_component_sha256"
        ],
    }


def row(name: str, routes: list[dict[str, object]]) -> DASHBOARD.ReviewItem:
    return DASHBOARD.ReviewItem(
        name=name,
        kind="theorem",
        lean_statement="P",
        paper_statement="P",
        agent_statement="P",
        llm_match_source_routes=routes,
    )


class JointDefinitionCoverageTests(unittest.TestCase):
    def _mixed_convention_item(self) -> dict[str, object]:
        item = definition_item()
        item["source_status"] = "exact"
        item["model_convention_ids"] = ["FIXTURE-CONVENTION-01"]
        components = item[DASHBOARD.SOURCE_DEFINITION_PARTITION_FIELD][
            "components"
        ]
        components[0]["source_status"] = "exact"
        components[1]["source_status"] = "documented_source_model_convention"
        components[1]["model_convention_ids"] = ["FIXTURE-CONVENTION-01"]
        return item

    def test_component_digest_is_exact_row_audit_target(self) -> None:
        source_item = definition_item()
        inventory = component_inventory(source_item)
        component_key, component = next(iter(inventory.items()))
        target = str(component["statement_sha256"])
        candidate = row(
            "component-row-navigation",
            [component_route(component_key, component)],
        )
        candidate.paper_statement = str(source_item["statement"])
        candidate.llm_match_paper_statement_sha256 = target
        candidate.llm_match_component_target_sha256 = target

        record = DASHBOARD._row_statement_match_record(
            PARENT_KEY,
            source_item,
            "covered",
            candidate.name,
            candidate,
        )

        self.assertNotEqual(
            record["review_row_paper_statement_sha256"], target
        )
        self.assertEqual(
            record["review_row_statement_audit_target_sha256"], target
        )
        self.assertTrue(
            record["row_correctness_matches_review_row_statement"]
        )

        candidate.llm_match_component_target_sha256 = ""
        self.assertFalse(
            DASHBOARD._row_statement_match_record(
                PARENT_KEY,
                source_item,
                "covered",
                candidate.name,
                candidate,
            )["row_correctness_matches_review_row_statement"]
        )

    def test_mixed_convention_partition_requires_explicit_component_scope(
        self,
    ) -> None:
        item = self._mixed_convention_item()
        partition, errors = DASHBOARD.source_definition_partition_record(item)
        self.assertEqual(errors, [])
        self.assertIsNotNone(partition)
        exact = next(
            component
            for component in partition["components"]
            if component["source_status"] == "exact"
        )
        governed = next(
            component
            for component in partition["components"]
            if component["source_status"]
            == "documented_source_model_convention"
        )
        self.assertNotIn("model_convention_ids", exact)
        self.assertEqual(
            governed["model_convention_ids"], ["FIXTURE-CONVENTION-01"]
        )

        missing_scope = copy.deepcopy(item)
        del missing_scope[DASHBOARD.SOURCE_DEFINITION_PARTITION_FIELD][
            "components"
        ][0]["source_status"]
        rejected, rejected_errors = DASHBOARD.source_definition_partition_record(
            missing_scope
        )
        self.assertIsNone(rejected)
        self.assertTrue(
            any("explicit component convention scope" in error for error in rejected_errors)
        )

    def test_component_convention_scope_must_exactly_partition_parent_ids(
        self,
    ) -> None:
        cases: list[tuple[str, dict[str, object], str]] = []

        missing_ids = self._mixed_convention_item()
        del missing_ids[DASHBOARD.SOURCE_DEFINITION_PARTITION_FIELD]["components"][
            1
        ]["model_convention_ids"]
        cases.append(("missing ids", missing_ids, "requires nonempty"))

        exact_with_ids = self._mixed_convention_item()
        exact_with_ids[DASHBOARD.SOURCE_DEFINITION_PARTITION_FIELD]["components"][
            0
        ]["model_convention_ids"] = ["FIXTURE-CONVENTION-01"]
        cases.append(("exact cites ids", exact_with_ids, "exact scope must omit"))

        duplicate_ids = self._mixed_convention_item()
        duplicate_ids[DASHBOARD.SOURCE_DEFINITION_PARTITION_FIELD]["components"][
            1
        ]["model_convention_ids"] = [
            "FIXTURE-CONVENTION-01",
            "FIXTURE-CONVENTION-01",
        ]
        cases.append(("duplicate ids", duplicate_ids, "unique model_convention_ids"))

        scalar_ids = self._mixed_convention_item()
        scalar_ids[DASHBOARD.SOURCE_DEFINITION_PARTITION_FIELD]["components"][1][
            "model_convention_ids"
        ] = "FIXTURE-CONVENTION-01"
        cases.append(("scalar ids", scalar_ids, "requires nonempty"))

        unknown_to_parent = self._mixed_convention_item()
        unknown_to_parent[DASHBOARD.SOURCE_DEFINITION_PARTITION_FIELD]["components"][
            1
        ]["model_convention_ids"] = ["FIXTURE-CONVENTION-02"]
        cases.append(("id absent from parent", unknown_to_parent, "absent from its parent"))

        missing_union = self._mixed_convention_item()
        missing_union["model_convention_ids"].append("FIXTURE-CONVENTION-02")
        cases.append(("incomplete union", missing_union, "exactly cover"))

        for label, item, expected in cases:
            with self.subTest(case=label):
                partition, errors = DASHBOARD.source_definition_partition_record(item)
                self.assertIsNone(partition)
                self.assertTrue(any(expected in error for error in errors), errors)

    def test_distinct_component_convention_sets_may_cover_one_parent(self) -> None:
        item = self._mixed_convention_item()
        item["model_convention_ids"].append("FIXTURE-CONVENTION-02")
        components = item[DASHBOARD.SOURCE_DEFINITION_PARTITION_FIELD]["components"]
        components[0]["source_status"] = "documented_source_model_convention"
        components[0]["model_convention_ids"] = ["FIXTURE-CONVENTION-02"]

        partition, errors = DASHBOARD.source_definition_partition_record(item)

        self.assertEqual(errors, [])
        self.assertIsNotNone(partition)
        convention_sets = {
            tuple(component["model_convention_ids"])
            for component in partition["components"]
        }
        self.assertEqual(
            convention_sets,
            {("FIXTURE-CONVENTION-01",), ("FIXTURE-CONVENTION-02",)},
        )

    def test_component_scope_change_does_not_churn_partition_or_exact_sibling(
        self,
    ) -> None:
        item = self._mixed_convention_item()
        first, first_errors = DASHBOARD.source_definition_partition_record(item)
        self.assertEqual(first_errors, [])
        self.assertIsNotNone(first)

        changed = copy.deepcopy(item)
        changed["model_convention_ids"].append("FIXTURE-CONVENTION-02")
        governed = changed[DASHBOARD.SOURCE_DEFINITION_PARTITION_FIELD]["components"][
            1
        ]
        governed["model_convention_ids"].append("FIXTURE-CONVENTION-02")
        second, second_errors = DASHBOARD.source_definition_partition_record(changed)
        self.assertEqual(second_errors, [])
        self.assertIsNotNone(second)

        self.assertEqual(
            first["source_definition_partition_sha256"],
            second["source_definition_partition_sha256"],
        )
        first_exact = next(
            component
            for component in first["components"]
            if component["source_status"] == "exact"
        )
        second_exact = next(
            component
            for component in second["components"]
            if component["source_status"] == "exact"
        )
        self.assertEqual(
            first_exact["source_definition_component_sha256"],
            second_exact["source_definition_component_sha256"],
        )
        first_governed = next(
            component
            for component in first["components"]
            if component["source_status"] != "exact"
        )
        second_governed = next(
            component
            for component in second["components"]
            if component["source_status"] != "exact"
        )
        self.assertNotEqual(
            first_governed["source_definition_component_sha256"],
            second_governed["source_definition_component_sha256"],
        )

    def test_discontiguous_exact_anchor_set_is_accepted(self) -> None:
        source_item = definition_item_with_discontiguous_component()
        partition, errors = DASHBOARD.source_definition_partition_record(source_item)
        self.assertEqual(errors, [])
        self.assertIsNotNone(partition)
        component = next(
            candidate
            for candidate in partition["components"]
            if candidate["source_location"] == "source.txt:10; source.txt:12"
        )
        self.assertEqual(len(component["source_anchor_evidence"]), 2)
        self.assertRegex(component["source_anchor_sha256"], r"^[0-9a-f]{64}$")

    def test_anchor_set_identity_is_canonical_and_single_quote_compatible(self) -> None:
        source_item = definition_item_with_discontiguous_component()
        partition, errors = DASHBOARD.source_definition_partition_record(source_item)
        self.assertEqual(errors, [])
        self.assertIsNotNone(partition)
        component = next(
            candidate
            for candidate in partition["components"]
            if candidate["source_location"] == "source.txt:10; source.txt:12"
        )
        anchors = component["source_anchor_evidence"]
        expected = hashlib.sha256(
            json.dumps(
                {
                    "schema": 1,
                    "kind": "source_definition_component_anchor_set",
                    "anchors": [
                        {
                            "path": anchor["path"],
                            "line_start": anchor["line_start"],
                            "line_end": anchor["line_end"],
                            "quoted_text_sha256": anchor["quoted_text_sha256"],
                        }
                        for anchor in anchors
                    ],
                },
                ensure_ascii=True,
                sort_keys=True,
                separators=(",", ":"),
            ).encode("utf-8")
        ).hexdigest()
        self.assertEqual(component["source_anchor_sha256"], expected)

        reordered = copy.deepcopy(source_item)
        reordered_component = reordered[
            DASHBOARD.SOURCE_DEFINITION_PARTITION_FIELD
        ]["components"][0]
        reordered_component["source_anchor_evidence"].reverse()
        reordered_partition, reordered_errors = (
            DASHBOARD.source_definition_partition_record(reordered)
        )
        self.assertEqual(reordered_errors, [])
        self.assertEqual(reordered_partition, partition)

        single_item = definition_item()
        single_partition, single_errors = (
            DASHBOARD.source_definition_partition_record(single_item)
        )
        self.assertEqual(single_errors, [])
        raw_single_anchor = single_item[
            DASHBOARD.SOURCE_DEFINITION_PARTITION_FIELD
        ]["components"][0]["source_anchor_evidence"][0]
        matching_single = next(
            candidate
            for candidate in single_partition["components"]
            if candidate["semantic_clause_sha256"]
            == single_item[DASHBOARD.SOURCE_DEFINITION_PARTITION_FIELD][
                "components"
            ][0]["semantic_clause_sha256"]
        )
        self.assertEqual(
            matching_single["source_anchor_sha256"],
            raw_single_anchor["quoted_text_sha256"],
        )

    def test_anchor_set_requires_exact_declared_spans(self) -> None:
        source_item = definition_item_with_discontiguous_component()
        component = source_item[DASHBOARD.SOURCE_DEFINITION_PARTITION_FIELD][
            "components"
        ][0]
        malformed_components = []

        missing = copy.deepcopy(component)
        missing["source_anchor_evidence"].pop()
        malformed_components.append(missing)

        extra = copy.deepcopy(component)
        extra_quote = "An undeclared source span."
        extra["source_anchor_evidence"].append(
            {
                "path": "source.txt",
                "line_start": 13,
                "line_end": 13,
                "quoted_text": extra_quote,
                "quoted_text_sha256": hashlib.sha256(
                    extra_quote.encode("utf-8")
                ).hexdigest(),
            }
        )
        malformed_components.append(extra)

        duplicate = copy.deepcopy(component)
        duplicate["source_anchor_evidence"].append(
            copy.deepcopy(duplicate["source_anchor_evidence"][0])
        )
        malformed_components.append(duplicate)

        for malformed in malformed_components:
            with self.subTest(anchor_count=len(malformed["source_anchor_evidence"])):
                candidate = copy.deepcopy(source_item)
                candidate[DASHBOARD.SOURCE_DEFINITION_PARTITION_FIELD][
                    "components"
                ][0] = malformed
                partition, errors = DASHBOARD.source_definition_partition_record(
                    candidate
                )
                self.assertIsNone(partition)
                self.assertTrue(errors)

    def test_each_discontiguous_quote_participates_in_route_identity(self) -> None:
        source_item = definition_item_with_discontiguous_component()
        partition, errors = DASHBOARD.source_definition_partition_record(source_item)
        self.assertEqual(errors, [])
        self.assertIsNotNone(partition)
        original = next(
            candidate
            for candidate in partition["components"]
            if candidate["source_location"] == "source.txt:10; source.txt:12"
        )

        changed_item = copy.deepcopy(source_item)
        changed_anchor = changed_item[DASHBOARD.SOURCE_DEFINITION_PARTITION_FIELD][
            "components"
        ][0]["source_anchor_evidence"][1]
        changed_anchor["quoted_text"] = "A changed second exact source span."
        changed_anchor["quoted_text_sha256"] = hashlib.sha256(
            changed_anchor["quoted_text"].encode("utf-8")
        ).hexdigest()
        changed_partition, changed_errors = (
            DASHBOARD.source_definition_partition_record(changed_item)
        )
        self.assertEqual(changed_errors, [])
        changed = next(
            candidate
            for candidate in changed_partition["components"]
            if candidate["source_location"] == "source.txt:10; source.txt:12"
        )
        self.assertNotEqual(
            changed["source_anchor_sha256"], original["source_anchor_sha256"]
        )
        self.assertNotEqual(
            changed_partition["source_definition_partition_sha256"],
            partition["source_definition_partition_sha256"],
        )
        self.assertNotEqual(
            changed["source_definition_component_sha256"],
            original["source_definition_component_sha256"],
        )
        self.assertNotEqual(
            DASHBOARD.source_definition_component_route_key(
                PARENT_KEY,
                changed["semantic_clause_sha256"],
                changed["source_anchor_sha256"],
            ),
            DASHBOARD.source_definition_component_route_key(
                PARENT_KEY,
                original["semantic_clause_sha256"],
                original["source_anchor_sha256"],
            ),
        )

    def test_structural_partition_change_reopens_every_component_pin(self) -> None:
        item = definition_item()
        first, first_errors = DASHBOARD.source_definition_partition_record(item)
        self.assertEqual(first_errors, [])
        self.assertIsNotNone(first)

        changed = copy.deepcopy(item)
        changed[DASHBOARD.SOURCE_DEFINITION_PARTITION_FIELD][
            "completeness_basis"
        ] = (
            "A fresh source-first review again establishes that these two clauses "
            "jointly exhaust the definition, with no third mathematical condition."
        )
        second, second_errors = DASHBOARD.source_definition_partition_record(changed)
        self.assertEqual(second_errors, [])
        self.assertIsNotNone(second)

        self.assertNotEqual(
            first["source_definition_partition_sha256"],
            second["source_definition_partition_sha256"],
        )
        first_components = {
            component["semantic_clause_sha256"]: component[
                "source_definition_component_sha256"
            ]
            for component in first["components"]
        }
        second_components = {
            component["semantic_clause_sha256"]: component[
                "source_definition_component_sha256"
            ]
            for component in second["components"]
        }
        self.assertEqual(set(first_components), set(second_components))
        self.assertTrue(
            all(
                first_components[key] != second_components[key]
                for key in first_components
            )
        )

    def test_complete_shared_quote_partition_is_accepted(self) -> None:
        source_item = definition_item()
        inventory = component_inventory(source_item)
        rows = [
            row(f"row-{index}", [component_route(key, item)])
            for index, (key, item) in enumerate(inventory.items())
        ]
        self.assertEqual(len(inventory), 2)
        for candidate in rows:
            self.assertEqual(
                DASHBOARD._coverage_route_error(
                    PARENT_KEY,
                    source_item,
                    candidate,
                    source_route_inventory=inventory,
                ),
                "",
            )
        self.assertEqual(
            DASHBOARD.definition_joint_component_coverage_error(
                PARENT_KEY,
                source_item,
                rows,
                source_route_inventory=inventory,
            ),
            "",
        )

    def test_missing_clause_is_rejected(self) -> None:
        source_item = definition_item()
        inventory = component_inventory(source_item)
        key, item = next(iter(inventory.items()))
        error = DASHBOARD.definition_joint_component_coverage_error(
            PARENT_KEY,
            source_item,
            [row("only-one-clause", [component_route(key, item)])],
            source_route_inventory=inventory,
        )
        self.assertIn("not the exact complete partition", error)

    def test_component_cannot_masquerade_as_whole_item(self) -> None:
        source_item = definition_item()
        route = {
            "source_item": PARENT_KEY,
            "source_statement_sha256": source_item["statement_sha256"],
            "source_location": source_item["source_location"],
            "route_kind": "source_component",
            "semantic_relation": "equivalent_source_component",
        }
        error = DASHBOARD._coverage_route_error(
            PARENT_KEY,
            source_item,
            row("masquerade", [route]),
            source_route_inventory={},
        )
        self.assertIn("cannot masquerade", error)

    def test_unrelated_result_route_behavior_is_preserved(self) -> None:
        statement = "The source theorem conclusion holds."
        source_item = {
            "statement": statement,
            "statement_sha256": DASHBOARD.statement_digest(statement),
            "source_location": "source.txt:20-21",
            "source_kind": "theorem",
            "lean_declarations": [],
        }
        direct = {
            "source_item": "theorem-navigation",
            "source_statement_sha256": source_item["statement_sha256"],
            "source_location": source_item["source_location"],
            "route_kind": "direct",
        }
        candidate = row("theorem-row", [direct])
        self.assertEqual(
            DASHBOARD._coverage_route_error(
                "theorem-navigation", source_item, candidate
            ),
            "",
        )
        self.assertEqual(
            DASHBOARD.definition_joint_component_coverage_error(
                "theorem-navigation",
                source_item,
                [candidate],
                source_route_inventory={},
            ),
            "",
        )

    def test_clause_route_requires_exact_partition_and_endpoint_pins(self) -> None:
        source_item = definition_item()
        inventory = component_inventory(source_item)
        key, component = next(iter(inventory.items()))
        route = component_route(key, component)
        judgment = {
            "source_routes": [route],
            "source_obligations": [
                {
                    "id": "source-clause",
                    "kind": "conclusion",
                    "source_item": key,
                    "source_statement_sha256": component["statement_sha256"],
                    "source_location": component["source_location"],
                    "statement": component["statement"],
                }
            ],
            "lean_obligations": [
                {"id": "lean-conclusion", "kind": "conclusion"}
            ],
            "obligation_alignment": [
                {
                    "source_id": "source-clause",
                    "lean_id": "lean-conclusion",
                    "relation": "equivalent",
                }
            ],
        }
        self.assertEqual(
            DASHBOARD.source_route_pin_error(judgment, inventory=inventory), ""
        )
        route.pop("source_component_anchor_sha256")
        self.assertIn(
            "stale source_component_anchor_sha256",
            DASHBOARD.source_route_pin_error(judgment, inventory=inventory),
        )
        route["source_component_anchor_sha256"] = component[
            "source_component_anchor_sha256"
        ]
        route["source_definition_partition_sha256"] = "0" * 64
        self.assertIn(
            "stale source_definition_partition_sha256",
            DASHBOARD.source_route_pin_error(judgment, inventory=inventory),
        )

    def test_status_display_route_uses_clause_and_partition_identity(self) -> None:
        source_item = definition_item()
        inventory = component_inventory(source_item)
        key, component = next(iter(inventory.items()))
        route = {
            "row": "review-row-navigation",
            "source_item": PARENT_KEY,
            "semantic_clause_sha256": component["statement_sha256"],
            "source_component_anchor_sha256": key.rsplit("::", 1)[-1],
            "source_location": component["source_location"],
            "source_definition_partition_sha256": component[
                "source_definition_partition_sha256"
            ],
            "source_definition_component_sha256": component[
                "source_definition_component_sha256"
            ],
        }
        with (
            mock.patch.object(
                DASHBOARD,
                "load_review_slice_payload",
                return_value={"source_component_statement_routes": [route]},
            ),
            mock.patch.object(
                DASHBOARD,
                "paper_source_component_route_inventory",
                return_value={},
            ),
            mock.patch.object(
                DASHBOARD,
                "paper_source_definition_component_route_inventory",
                return_value=inventory,
            ),
        ):
            resolved = DASHBOARD.review_source_component_statement_routes(
                Path("unused")
            )
        self.assertEqual(
            resolved["review-row-navigation"]["statement"],
            component["statement"],
        )

    def test_component_display_resolves_only_unambiguous_full_row(self) -> None:
        component = {"statement": "The exact semantic source clause."}
        colliding_rows = [
            ("theorem", "endpoint", "First.endpoint", "P", None, 1, Path("a")),
            ("theorem", "endpoint", "Second.endpoint", "Q", None, 2, Path("b")),
        ]
        with mock.patch.object(
            DASHBOARD,
            "review_source_component_statement_routes",
            return_value={"endpoint": component},
        ):
            self.assertEqual(
                DASHBOARD.resolved_review_source_component_statement_routes(
                    Path("unused"), colliding_rows
                ),
                {},
            )
        with mock.patch.object(
            DASHBOARD,
            "review_source_component_statement_routes",
            return_value={"First.endpoint": component},
        ):
            self.assertEqual(
                DASHBOARD.resolved_review_source_component_statement_routes(
                    Path("unused"), colliding_rows
                ),
                {"First.endpoint": component},
            )

    def test_component_display_precedes_parent_full_name_in_both_paths(self) -> None:
        component = {"statement": "The exact semantic source clause."}
        self.assertEqual(
            DASHBOARD.paper_statement_for_review_row(
                {
                    "Example.endpoint": "The parent whole-item statement.",
                    "endpoint": "A heuristic short-name statement.",
                },
                {"Example.endpoint": component},
                "endpoint",
                "Example.endpoint",
            ),
            component["statement"],
        )

    def test_cache_hash_default_owns_and_finalizes_lean_provider(self) -> None:
        class FakeProvider:
            def __init__(self, root: Path) -> None:
                self.root = Path(root).resolve()
                self.requests: list[str] = []
                self.finalized = False

            def snapshot(self, module: str) -> str:
                self.requests.append(module)
                return hashlib.sha256(module.encode("utf-8")).hexdigest()

            def finalize_unchanged(self) -> bool:
                self.finalized = True
                return True

        with tempfile.TemporaryDirectory() as tmpdir:
            folder = Path(tmpdir) / "FixturePaper"
            folder.mkdir()
            (folder / "PaperInterface.lean").write_text(
                "namespace FixturePaper\ntheorem endpoint : True := by trivial\nend FixturePaper\n",
                encoding="utf-8",
            )
            (folder / "status.json").write_text(
                '{"review_surface":{"source_file":"PaperInterface.lean"}}',
                encoding="utf-8",
            )
            provider = FakeProvider(DASHBOARD.ROOT)
            with mock.patch.object(
                DASHBOARD,
                "RepositoryBuildInputSnapshotProvider",
                return_value=provider,
            ):
                hashes = DASHBOARD._cache_source_hashes(folder)
        self.assertTrue(provider.finalized)
        self.assertEqual(provider.requests, ["FixturePaper.PaperInterface"])
        self.assertRegex(hashes["lean_source_closure_sha256"], r"^[0-9a-f]{64}$")

    def test_cached_display_rebind_applies_component_without_lean(self) -> None:
        source_path = Path("PaperInterface.lean")
        parsed = [
            (
                "theorem",
                "endpoint",
                "Example.endpoint",
                "theorem endpoint : True := by trivial",
                None,
                1,
                source_path,
            )
        ]
        item = DASHBOARD.ReviewItem(
            name="endpoint",
            full_name="Example.endpoint",
            kind="theorem",
            lean_statement="True",
            paper_statement="The parent whole-item statement.",
            agent_statement="True.",
            interface_source="theorem endpoint : True := by trivial",
        )
        component = {"statement": "The exact semantic source clause."}
        with (
            mock.patch.object(
                DASHBOARD,
                "collected_paper_statements",
                return_value={
                    "Example.endpoint": "The parent whole-item statement.",
                    "endpoint": component["statement"],
                },
            ),
            mock.patch.object(
                DASHBOARD,
                "parse_review_source_declarations",
                return_value=parsed,
            ),
            mock.patch.object(
                DASHBOARD,
                "review_source_component_statement_routes",
                return_value={"endpoint": component},
            ),
            mock.patch.object(
                DASHBOARD, "review_source_file", return_value=source_path
            ),
            mock.patch.object(
                DASHBOARD, "review_assumption_names", return_value=set()
            ),
            mock.patch.object(
                DASHBOARD, "assumption_source_file", return_value=source_path
            ),
        ):
            self.assertTrue(
                DASHBOARD.rebind_cached_report_statements(
                    Path("unused"), [item]
                )
            )
        self.assertEqual(item.paper_statement, component["statement"])


if __name__ == "__main__":
    unittest.main()
