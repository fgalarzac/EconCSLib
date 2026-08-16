#!/usr/bin/env python3
"""Focused regressions for name-independent semantic review indexing."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import review_dashboard as dashboard


class SemanticReviewIndexTests(unittest.TestCase):
    def _write_statement_sidecar(self, folder: Path, signature: str) -> None:
        audit = folder / "audit"
        audit.mkdir()
        (audit / "statement_match_llm.json").write_text(
            json.dumps(
                {
                    "schema": 1,
                    "paper": folder.name,
                    "prompt_version": dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION,
                    "validator": "fixture-reviewer",
                    "validated_at": "2026-07-31T00:00:00Z",
                    "items": {
                        "renamed_navigation": {
                            "judgment": "matches",
                            "lean_signature_sha256": signature,
                            "paper_statement_sha256": "b" * 64,
                            "tex_statement_sha256": "c" * 64,
                        }
                    },
                }
            ),
            encoding="utf-8",
        )

    def test_short_and_qualified_aliases_are_one_manifest_candidate(self) -> None:
        signature = "a" * 64
        manifest = {"sha256": signature}
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            self._write_statement_sidecar(folder, signature)
            with mock.patch.object(
                dashboard,
                "semantic_obligation_ledger_error",
                side_effect=lambda _entry, candidate, **_kwargs: (
                    "" if candidate is manifest else "manifest was not uniquely rebound"
                ),
            ):
                judgments = dashboard.load_llm_statement_judgments(
                    folder,
                    {
                        "short": manifest,
                        "Fixture.short": manifest,
                    },
                )

        self.assertEqual(
            judgments["renamed_navigation"]["obligation_ledger_error"], ""
        )

    def test_distinct_equal_signature_manifests_remain_ambiguous(self) -> None:
        signature = "a" * 64
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            self._write_statement_sidecar(folder, signature)
            with mock.patch.object(
                dashboard,
                "semantic_obligation_ledger_error",
                side_effect=lambda _entry, candidate, **_kwargs: (
                    "" if candidate is not None else "manifest is ambiguous"
                ),
            ):
                judgments = dashboard.load_llm_statement_judgments(
                    folder,
                    {
                        "first": {"sha256": signature},
                        "second": {"sha256": signature},
                    },
                )

        self.assertEqual(
            judgments["renamed_navigation"]["obligation_ledger_error"],
            "manifest is ambiguous",
        )

    def test_preindexed_item_lookup_does_not_rescan_all_judgments(self) -> None:
        signature = "a" * 64
        paper = "Paper statement"
        translation = "Translated statement"
        judgment = {
            "lean_signature_sha256": signature,
            "paper_statement_sha256": dashboard.statement_digest(paper),
            "tex_statement_sha256": dashboard.statement_digest(translation),
        }
        judgments = {"stored_navigation": judgment}
        index = dashboard._semantic_statement_judgment_index(judgments)

        class NoRescanDict(dict[str, dict[str, object]]):
            def items(self):  # type: ignore[override]
                raise AssertionError("semantic lookup rescanned the complete judgment map")

        item = dashboard.ReviewItem(
            name="current_navigation",
            kind="theorem",
            lean_statement="theorem current_navigation : True",
            paper_statement=paper,
            agent_statement=translation,
            lean_signature_sha256=signature,
        )
        key, rebound, ambiguous = (
            dashboard._current_semantic_statement_judgment_for_item(
                item,
                NoRescanDict(judgments),
                identity_index=index,
            )
        )

        self.assertEqual(key, "stored_navigation")
        self.assertIs(rebound, judgment)
        self.assertFalse(ambiguous)

    def test_cached_row_rebind_uses_unique_semantics_not_storage_name(self) -> None:
        signature = "a" * 64
        paper = "Paper statement"
        translation = "Translated statement"
        judgment = {
            "judgment": "matches",
            "reason": "Same source and elaborated proposition.",
            "lean_signature_sha256": signature,
            "paper_statement_sha256": dashboard.statement_digest(paper),
            "tex_statement_sha256": dashboard.statement_digest(translation),
        }
        item = dashboard.ReviewItem(
            name="current_navigation",
            kind="theorem",
            lean_statement="theorem current_navigation : True",
            paper_statement=paper,
            agent_statement=translation,
            lean_signature_manifest={"sha256": signature},
            lean_signature_sha256=signature,
        )
        with (
            mock.patch.object(dashboard, "load_llm_lean_to_tex_drafts", return_value={}),
            mock.patch.object(
                dashboard,
                "load_llm_statement_judgments",
                return_value={"old_storage_navigation": judgment},
            ),
            mock.patch.object(dashboard, "load_llm_assumption_judgments", return_value={}),
        ):
            dashboard.rebind_cached_review_sidecars(Path("/fixture"), [item])

        self.assertEqual(item.llm_match_judgment, "matches")
        self.assertFalse(item.llm_match_stale)

        duplicate = dict(judgment)
        with (
            mock.patch.object(dashboard, "load_llm_lean_to_tex_drafts", return_value={}),
            mock.patch.object(
                dashboard,
                "load_llm_statement_judgments",
                return_value={
                    "old_storage_navigation": judgment,
                    "ambiguous_storage_navigation": duplicate,
                },
            ),
            mock.patch.object(dashboard, "load_llm_assumption_judgments", return_value={}),
        ):
            dashboard.rebind_cached_review_sidecars(Path("/fixture"), [item])
        self.assertEqual(item.llm_match_judgment, "")


if __name__ == "__main__":
    unittest.main()
