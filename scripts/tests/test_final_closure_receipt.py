#!/usr/bin/env python3
"""Regression tests for the canonical final-closure receipt."""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    if str(import_root) not in sys.path:
        sys.path.insert(0, str(import_root))

import final_closure_receipt as receipt  # noqa: E402


class FinalClosureReceiptTests(unittest.TestCase):
    def make_paper(self, root: Path, paper: str = "Fixture") -> Path:
        folder = root / "papers" / paper
        audit = folder / "audit"
        audit.mkdir(parents=True)
        (folder / "source.txt").write_text("Theorem 1. True.\n", encoding="utf-8")
        (folder / "FINAL_VALIDATION_REPORT.md").write_text(
            "# Direct row review\n\n"
            "## 1. Human Verdict\n\n"
            "Formalized.\n\n"
            "## 12. Detailed Formalization Evidence\n\n"
            "Every selected source row was reviewed.\n",
            encoding="utf-8",
        )
        (folder / "PaperInterface.lean").write_text(
            "namespace Fixture\nend Fixture\n", encoding="utf-8"
        )
        source_sha = hashlib.sha256((folder / "source.txt").read_bytes()).hexdigest()
        (audit / "paper_statement_map.json").write_text(
            json.dumps(
                {
                    "source_artifact_path": "source.txt",
                    "source_artifact_sha256": source_sha,
                    "items": {},
                }
            ),
            encoding="utf-8",
        )
        (folder / "status.json").write_text(
            json.dumps({"build_target": "true"}), encoding="utf-8"
        )
        return folder

    def test_issue_and_validate_direct_review_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = self.make_paper(root)
            with (
                mock.patch.object(receipt, "_git_head", return_value="c" * 40),
                mock.patch.object(
                    receipt, "_current_interface_closure", return_value="a" * 64
                ),
                mock.patch.object(
                    receipt,
                    "formalization_review_protocol_digest",
                    return_value="b" * 64,
                ),
            ):
                path = receipt.issue_final_closure_receipt(
                    root,
                    "Fixture",
                    evidence_lane=receipt.DIRECT_SOURCE_ROW_REVIEW_LANE,
                    review_ledger_path="FINAL_VALIDATION_REPORT.md",
                    run_build=True,
                )
                self.assertTrue(path.is_file())
                self.assertTrue(path.read_text(encoding="utf-8").startswith("+++\n"))
                current = receipt.validate_final_closure_receipt(
                    root,
                    "Fixture",
                    required_lane=receipt.DIRECT_SOURCE_ROW_REVIEW_LANE,
                )
            self.assertEqual(current.payload["paper"], "Fixture")

    def test_direct_receipt_fails_after_a_pinned_ledger_change(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = self.make_paper(root)
            with (
                mock.patch.object(receipt, "_git_head", return_value="c" * 40),
                mock.patch.object(
                    receipt, "_current_interface_closure", return_value="a" * 64
                ),
                mock.patch.object(
                    receipt,
                    "formalization_review_protocol_digest",
                    return_value="b" * 64,
                ),
            ):
                receipt.issue_final_closure_receipt(
                    root,
                    "Fixture",
                    evidence_lane=receipt.DIRECT_SOURCE_ROW_REVIEW_LANE,
                    review_ledger_path="FINAL_VALIDATION_REPORT.md",
                    run_build=True,
                )
                (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                    "# Direct row review\n\n"
                    "## 1. Human Verdict\n\n"
                    "Formalized.\n\n"
                    "## 12. Detailed Formalization Evidence\n\n"
                    "Changed direct row review.\n",
                    encoding="utf-8",
                )
                with self.assertRaisesRegex(
                    receipt.FinalClosureReceiptError, "review_ledger.*stale"
                ):
                    receipt.validate_final_closure_receipt(
                        root,
                        "Fixture",
                        required_lane=receipt.DIRECT_SOURCE_ROW_REVIEW_LANE,
                    )

    def test_final_receipt_can_reuse_a_current_pinned_build_record(self) -> None:
        """A split run remains strict when the build record pins every input."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            self.make_paper(root)
            with (
                mock.patch.object(receipt, "_git_head", return_value="c" * 40),
                mock.patch.object(
                    receipt, "_current_interface_closure", return_value="a" * 64
                ),
                mock.patch.object(
                    receipt,
                    "formalization_review_protocol_digest",
                    return_value="b" * 64,
                ),
            ):
                build_record = receipt.record_focused_build_receipt(root, "Fixture")
                self.assertTrue(build_record.is_file())
                path = receipt.issue_final_closure_receipt(
                    root,
                    "Fixture",
                    evidence_lane=receipt.DIRECT_SOURCE_ROW_REVIEW_LANE,
                    review_ledger_path="FINAL_VALIDATION_REPORT.md",
                    run_build=False,
                    reuse_focused_build_receipt=True,
                )
                current = receipt.validate_final_closure_receipt(root, "Fixture")

            self.assertTrue(path.is_file())
            self.assertEqual(current.payload["schema"], 3)
            self.assertIn("focused_build_receipt", current.payload)

    def test_v11_direct_lane_refuses_a_report_in_place_of_its_screening_ledger(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = self.make_paper(root)
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "build_target": "true",
                        "review_surface": {
                            "require_source_spec_correspondence": True
                        },
                    }
                ),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                receipt.FinalClosureReceiptError,
                "must bind `audit/v11_raw_source_spec_screening.json`",
            ):
                receipt.issue_final_closure_receipt(
                    root,
                    "Fixture",
                    evidence_lane=receipt.DIRECT_SOURCE_ROW_REVIEW_LANE,
                    review_ledger_path="FINAL_VALIDATION_REPORT.md",
                    run_build=True,
                )

    def test_direct_receipt_allows_only_structural_source_absence(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = self.make_paper(root)
            with (
                mock.patch.object(receipt, "_git_head", return_value="c" * 40),
                mock.patch.object(
                    receipt,
                    "_current_interface_closure",
                    return_value="a" * 64,
                ),
                mock.patch.object(
                    receipt,
                    "formalization_review_protocol_digest",
                    return_value="b" * 64,
                ),
            ):
                receipt.issue_final_closure_receipt(
                    root,
                    "Fixture",
                    evidence_lane=receipt.DIRECT_SOURCE_ROW_REVIEW_LANE,
                    review_ledger_path="FINAL_VALIDATION_REPORT.md",
                    run_build=True,
                )
                (folder / "source.txt").unlink()
                with self.assertRaisesRegex(
                    receipt.FinalClosureReceiptError, "canonical source bytes"
                ):
                    receipt.validate_final_closure_receipt(root, "Fixture")
                receipt.validate_final_closure_receipt(
                    root,
                    "Fixture",
                    allow_missing_source_bytes=True,
                )

    def test_report_front_matter_change_does_not_stale_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = self.make_paper(root)
            with (
                mock.patch.object(receipt, "_git_head", return_value="c" * 40),
                mock.patch.object(
                    receipt, "_current_interface_closure", return_value="a" * 64
                ),
                mock.patch.object(
                    receipt,
                    "formalization_review_protocol_digest",
                    return_value="b" * 64,
                ),
            ):
                receipt.issue_final_closure_receipt(
                    root,
                    "Fixture",
                    evidence_lane=receipt.DIRECT_SOURCE_ROW_REVIEW_LANE,
                    review_ledger_path="FINAL_VALIDATION_REPORT.md",
                    run_build=True,
                )
                report = folder / "FINAL_VALIDATION_REPORT.md"
                report.write_text(
                    report.read_text(encoding="utf-8").replace(
                        "Formalized.", "Formalized without caveat."
                    ),
                    encoding="utf-8",
                )
                receipt.validate_final_closure_receipt(
                    root,
                    "Fixture",
                    required_lane=receipt.DIRECT_SOURCE_ROW_REVIEW_LANE,
                )


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
