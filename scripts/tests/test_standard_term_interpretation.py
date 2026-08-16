#!/usr/bin/env python3
"""Regression tests for source-standard-term vocabulary interpretations."""

from __future__ import annotations

from copy import deepcopy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.source_coverage_scope import (  # noqa: E402
    NAMED_THEORETICAL_STATEMENTS,
    SOURCE_PROSE_DEFINITION_PRESENTATIONS_FIELD,
    SOURCE_PROSE_DEFINITION_PRESENTATIONS_SHA256_FIELD,
    SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD,
    SOURCE_STANDARD_TERM_INTERPRETATION_FIELD,
    SOURCE_STANDARD_TERM_INTERPRETATION_JUDGMENT,
    SOURCE_STANDARD_TERM_INTERPRETATION_RELATION,
    SOURCE_STANDARD_TERM_INTERPRETATION_SCHEMA,
    source_index_byte_pinned_anchor_item_ids,
    source_item_coverage_sha256,
    source_map_cache_semantic_sha256,
    source_map_structural_errors,
    source_prose_definition_inventory_errors,
    source_prose_definition_presentations_sha256,
    source_vocabulary_definition_binding_item_ids,
    source_item_statement_sha256,
)


class StandardTermInterpretationTests(unittest.TestCase):
    SOURCE_TEXT = (
        "Throughout, M is a stable matching in the finite market.\n"
        "The market contains finitely many agents.\n"
    )

    @staticmethod
    def _anchor(source_text: str, line_start: int, line_end: int) -> dict[str, object]:
        lines = source_text.rstrip("\n").split("\n")
        quote = "\n".join(lines[line_start - 1 : line_end])
        return {
            "path": "source.txt",
            "line_start": line_start,
            "line_end": line_end,
            "quoted_text": quote,
            "quoted_text_sha256": hashlib.sha256(quote.encode("utf-8")).hexdigest(),
        }

    def _payload(self) -> dict[str, object]:
        anchor = self._anchor(self.SOURCE_TEXT, 1, 1)
        statement = (
            "The paper uses stable matching in the standard blocking-pair sense."
        )
        presentations: list[dict[str, object]] = []
        source_digest = hashlib.sha256(self.SOURCE_TEXT.encode("utf-8")).hexdigest()
        return {
            "schema": 1,
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": source_digest,
            "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
            "source_named_result_inventory_review": {
                "schema": 1,
                "complete": True,
                "validator": "independent source-only inventory fixture",
                "validated_at": "2026-08-15T12:00:00Z",
                "method": "Independent source-byte inventory extraction.",
                "source_artifact_sha256": source_digest,
                "discovered_named_result_sha256": "0" * 64,
                SOURCE_PROSE_DEFINITION_PRESENTATIONS_FIELD: presentations,
                SOURCE_PROSE_DEFINITION_PRESENTATIONS_SHA256_FIELD: (
                    source_prose_definition_presentations_sha256(presentations)
                ),
            },
            "items": {
                "opaque_vocabulary_coordinate": {
                    "source_kind": "predicate_vocabulary",
                    "claim_bearing": True,
                    "statement": statement,
                    "source_location": "source.txt:1",
                    "source_anchor_evidence": [anchor],
                    # Navigation must not affect this semantic source route.
                    "lean_declarations": ["Fixture.UnrelatedSpelling"],
                    SOURCE_STANDARD_TERM_INTERPRETATION_FIELD: {
                        "schema": SOURCE_STANDARD_TERM_INTERPRETATION_SCHEMA,
                        "relation": SOURCE_STANDARD_TERM_INTERPRETATION_RELATION,
                        "source_term": "stable matching",
                        "source_provided_definition": False,
                        "source_term_use_anchor": anchor,
                        "source_item_statement_sha256": (
                            source_item_statement_sha256(
                                {"statement": statement}
                            )
                        ),
                        "standard_interpretation": (
                            "A matching is stable exactly when no feasible agent pair "
                            "forms a blocking pair under the reported preferences."
                        ),
                        "judgment": SOURCE_STANDARD_TERM_INTERPRETATION_JUDGMENT,
                        "semantic_basis": (
                            "The source uses the established term without defining it; "
                            "the standard blocking-pair predicate supplies its meaning."
                        ),
                        "validator": "independent standard-term semantic reviewer",
                        "validator_type": "agent",
                        "validated_at": "2026-08-15T12:01:00Z",
                    },
                }
            },
        }

    def _paper(self, root: Path, payload: dict[str, object]) -> Path:
        paper = root / "papers" / "FixturePaper"
        (paper / "audit").mkdir(parents=True)
        (paper / "source.txt").write_text(self.SOURCE_TEXT, encoding="utf-8")
        (paper / "audit" / "paper_statement_map.json").write_text(
            json.dumps(payload, indent=2) + "\n", encoding="utf-8"
        )
        return paper

    @staticmethod
    def _row(payload: dict[str, object]) -> dict[str, object]:
        items = payload["items"]
        assert isinstance(items, dict)
        row = items["opaque_vocabulary_coordinate"]
        assert isinstance(row, dict)
        return row

    @staticmethod
    def _interpretation(row: dict[str, object]) -> dict[str, object]:
        interpretation = row[SOURCE_STANDARD_TERM_INTERPRETATION_FIELD]
        assert isinstance(interpretation, dict)
        return interpretation

    def test_valid_standard_term_interpretation_selects_vocabulary_row(self) -> None:
        payload = self._payload()
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paper = self._paper(root, payload)
            self.assertEqual(
                source_prose_definition_inventory_errors(
                    paper, payload, repository_root=root
                ),
                [],
            )
            self.assertEqual(
                source_vocabulary_definition_binding_item_ids(
                    paper, payload, repository_root=root
                ),
                ({"opaque_vocabulary_coordinate"}, []),
            )
            self.assertEqual(
                source_index_byte_pinned_anchor_item_ids(
                    paper,
                    payload,
                    NAMED_THEORETICAL_STATEMENTS,
                    repository_root=root,
                ),
                {"opaque_vocabulary_coordinate"},
            )

    def test_term_must_be_in_this_rows_current_source_anchor(self) -> None:
        payload = self._payload()
        row = self._row(payload)
        row["source_anchor_evidence"] = [self._anchor(self.SOURCE_TEXT, 2, 2)]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paper = self._paper(root, payload)
            errors = source_prose_definition_inventory_errors(
                paper, payload, repository_root=root
            )
            self.assertTrue(
                any("not contained in this item's exact current" in error for error in errors),
                errors,
            )
            self.assertTrue(
                any("occur in this item's exact current" in error for error in errors),
                errors,
            )
            self.assertEqual(
                source_index_byte_pinned_anchor_item_ids(
                    paper,
                    payload,
                    NAMED_THEORETICAL_STATEMENTS,
                    repository_root=root,
                ),
                set(),
            )

    def test_only_valid_vocabulary_rows_receive_the_exception(self) -> None:
        payload = self._payload()
        row = self._row(payload)
        row["source_kind"] = "theorem"
        interpretation = self._interpretation(row)
        interpretation["source_provided_definition"] = True
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paper = self._paper(root, payload)
            errors = source_prose_definition_inventory_errors(
                paper, payload, repository_root=root
            )
            self.assertTrue(
                any("must be false" in error for error in errors), errors)
            self.assertTrue(
                any("only a source_kind definition or predicate_vocabulary" in error for error in errors),
                errors,
            )
            self.assertEqual(
                source_index_byte_pinned_anchor_item_ids(
                    paper,
                    payload,
                    NAMED_THEORETICAL_STATEMENTS,
                    repository_root=root,
                ),
                set(),
            )

    def test_interpretation_is_mutually_exclusive_with_prose_reconciliation(self) -> None:
        payload = self._payload()
        row = self._row(payload)
        row[SOURCE_PROSE_DEFINITION_RECONCILIATION_FIELD] = None
        structural_errors = source_map_structural_errors(payload["items"])
        self.assertTrue(
            any("cannot coexist" in error for error in structural_errors),
            structural_errors,
        )
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paper = self._paper(root, payload)
            errors = source_prose_definition_inventory_errors(
                paper, payload, repository_root=root
            )
            self.assertTrue(any("cannot coexist" in error for error in errors), errors)

    def test_validator_must_be_independent_and_semantic_pins_drive_cache(self) -> None:
        payload = self._payload()
        row = self._row(payload)
        interpretation = self._interpretation(row)
        review = payload["source_named_result_inventory_review"]
        assert isinstance(review, dict)
        interpretation["validator"] = review["validator"]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paper = self._paper(root, payload)
            errors = source_prose_definition_inventory_errors(
                paper, payload, repository_root=root
            )
            self.assertTrue(any("independent" in error for error in errors), errors)

        first = self._payload()
        reviewer_refresh = deepcopy(first)
        refreshed_interpretation = self._interpretation(self._row(reviewer_refresh))
        refreshed_interpretation["semantic_basis"] = (
            "A different reviewer explanation of the same source-term use and "
            "standard blocking-pair interpretation."
        )
        refreshed_interpretation["validator"] = "replacement independent reviewer"
        refreshed_interpretation["validator_type"] = "human"
        refreshed_interpretation["validated_at"] = "2026-08-16T12:01:00Z"
        self.assertEqual(
            source_item_coverage_sha256(
                self._row(first), NAMED_THEORETICAL_STATEMENTS
            ),
            source_item_coverage_sha256(
                self._row(reviewer_refresh), NAMED_THEORETICAL_STATEMENTS
            ),
        )
        self.assertEqual(
            source_map_cache_semantic_sha256(first),
            source_map_cache_semantic_sha256(reviewer_refresh),
        )

        changed_interpretation = deepcopy(first)
        changed = self._interpretation(self._row(changed_interpretation))
        changed["standard_interpretation"] = (
            "A matching is stable exactly when every agent receives their first "
            "choice, which is a materially different mathematical predicate."
        )
        self.assertNotEqual(
            source_item_coverage_sha256(
                self._row(first), NAMED_THEORETICAL_STATEMENTS
            ),
            source_item_coverage_sha256(
                self._row(changed_interpretation), NAMED_THEORETICAL_STATEMENTS
            ),
        )
        self.assertNotEqual(
            source_map_cache_semantic_sha256(first),
            source_map_cache_semantic_sha256(changed_interpretation),
        )


if __name__ == "__main__":
    unittest.main()
