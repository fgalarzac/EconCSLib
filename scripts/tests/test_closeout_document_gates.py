#!/usr/bin/env python3
"""Regression tests for shared strict/planner closeout document gates."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from scripts.closeout_document_gates import closeout_document_hard_errors


class CloseoutDocumentGateTests(unittest.TestCase):
    def _write_valid_source_audit(self, folder: Path) -> None:
        docs = folder / "docs"
        docs.mkdir(parents=True, exist_ok=True)
        (docs / "AGENT_SOURCE_AUDIT.md").write_text(
            "## Overall status: PASS\n"
            "This independent source-first review does not merely summarize existing "
            "sidecars. It builds a source inventory from the source itself and compares "
            "the Lean interface for omissions, hidden strengthening/weakening, and "
            "semantic mismatches.\n",
            encoding="utf-8",
        )

    def test_missing_or_incomplete_source_audit_is_a_hard_error(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            missing = closeout_document_hard_errors(
                folder, corrected_scope_current=False
            )
            self.assertEqual(len(missing), 1)
            self.assertIn("missing `docs/AGENT_SOURCE_AUDIT.md`", missing[0].message)

            self._write_valid_source_audit(folder)
            source_audit = folder / "docs" / "AGENT_SOURCE_AUDIT.md"
            source_audit.write_text(
                "## Overall status: NEEDS REVIEW\n", encoding="utf-8"
            )
            incomplete = closeout_document_hard_errors(
                folder, corrected_scope_current=False
            )
            self.assertTrue(
                any("Overall status: PASS" in error.message for error in incomplete)
            )
            self.assertTrue(
                any("must document an independent" in error.message for error in incomplete)
            )

            source_audit.write_text(
                "## Overall status: PASS\n"
                "NEEDS AGENT REVIEW: scaffold has not performed the source read.\n",
                encoding="utf-8",
            )
            scaffold = closeout_document_hard_errors(
                folder, corrected_scope_current=False
            )
            self.assertTrue(any("still a scaffold" in error.message for error in scaffold))

    def test_current_corrected_scope_exempts_only_source_audit_requirement(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                "TODO\n", encoding="utf-8"
            )

            errors = closeout_document_hard_errors(
                folder, corrected_scope_current=True
            )

            self.assertEqual(len(errors), 1)
            self.assertEqual(errors[0].path, folder / "FINAL_VALIDATION_REPORT.md")
            self.assertIn("stale placeholder", errors[0].message)

    def test_post_audit_placeholder_is_a_hard_error(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            self._write_valid_source_audit(folder)
            (folder / "docs" / "POST_FORMALIZATION_AUDIT.md").write_text(
                "- Not run.\n", encoding="utf-8"
            )

            errors = closeout_document_hard_errors(
                folder, corrected_scope_current=False
            )

            self.assertEqual(len(errors), 1)
            self.assertIn("post-formalization audit", errors[0].message)

    def test_strict_can_supply_a_legacy_post_audit_path(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            self._write_valid_source_audit(folder)
            legacy_post_audit = folder / "POST_FORMALIZATION_AUDIT.md"
            legacy_post_audit.write_text("TODO\n", encoding="utf-8")

            errors = closeout_document_hard_errors(
                folder,
                corrected_scope_current=False,
                post_formalization_audit=legacy_post_audit,
            )

            self.assertEqual(len(errors), 1)
            self.assertEqual(errors[0].path, legacy_post_audit)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
