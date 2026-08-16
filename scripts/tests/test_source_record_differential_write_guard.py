#!/usr/bin/env python3
"""Focused protection tests for differential-overlay provenance writes."""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import source_record_differential_revalidation as DIFFERENTIAL  # noqa: E402


PAPER = "FixtureDifferentialWriteGuard"


class DifferentialWriteGuardTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        root_override = patch.object(DIFFERENTIAL, "ROOT", self.root)
        root_override.start()
        self.addCleanup(root_override.stop)
        self.paper_dir = self.root / "papers" / PAPER
        self.audit_dir = self.paper_dir / "audit"
        self.audit_dir.mkdir(parents=True)
        self.overlay_path = DIFFERENTIAL.source_record_differential_revalidation_overlay_path(
            self.paper_dir
        )
        self.original_bytes = b'{"historical": true}\n'
        self.overlay_path.write_bytes(self.original_bytes)

    def _write_json(self, name: str, value: object) -> Path:
        path = self.audit_dir / name
        path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        return path

    def _selected_pin(self, *, sha256: str | None = None) -> Path:
        return self._write_json(
            "selected_receipt.json",
            {
                "current_selected_semantic_revalidation": {
                    "differential_overlay_path": (
                        "audit/source_record_differential_revalidation.json"
                    ),
                    "differential_overlay_sha256": sha256
                    or hashlib.sha256(self.original_bytes).hexdigest(),
                }
            },
        )

    def _historical_composition_pin(self, name: str = "historical_composition.json") -> Path:
        return self._write_json(
            name,
            {
                "historical_authenticated_composition": {
                    "differential_overlay": {
                        "path": "audit/source_record_differential_revalidation.json",
                        "file_sha256": hashlib.sha256(self.original_bytes).hexdigest(),
                    }
                }
            },
        )

    @staticmethod
    def _replacement_bytes() -> bytes:
        return b'{"replacement": true}\n'

    def test_selected_receipt_pin_blocks_changed_write(self) -> None:
        self._selected_pin()

        pins = DIFFERENTIAL.source_record_differential_write_pins(
            paper_dir=self.paper_dir,
            output_path=self.overlay_path,
            proposed_bytes=self._replacement_bytes(),
        )

        self.assertEqual(len(pins), 1)
        self.assertEqual(pins[0]["kind"], "selected_or_composed_overlay")
        self.assertEqual(pins[0]["evidence_path"], "audit/selected_receipt.json")
        self.assertIn("--replace-byte-pinned-overlay", DIFFERENTIAL._byte_pinned_overlay_write_error(pins))

    def test_historical_composition_snapshot_pin_blocks_changed_write(self) -> None:
        self._historical_composition_pin("before_any_reissue.json")

        pins = DIFFERENTIAL.source_record_differential_write_pins(
            paper_dir=self.paper_dir,
            output_path=self.overlay_path,
            proposed_bytes=self._replacement_bytes(),
        )

        self.assertEqual(len(pins), 1)
        self.assertEqual(pins[0]["kind"], "historical_composition_overlay")
        self.assertEqual(pins[0]["evidence_path"], "audit/before_any_reissue.json")

    def test_explicit_non_evidence_scaffold_does_not_block_changed_write(self) -> None:
        self._write_json(
            "draft_with_a_real_shaped_pin.json",
            {
                "non_evidence_scaffold": True,
                "current_selected_semantic_revalidation": {
                    "differential_overlay_path": (
                        "audit/source_record_differential_revalidation.json"
                    ),
                    "differential_overlay_sha256": hashlib.sha256(
                        self.original_bytes
                    ).hexdigest(),
                },
            },
        )

        self.assertEqual(
            DIFFERENTIAL.source_record_differential_write_pins(
                paper_dir=self.paper_dir,
                output_path=self.overlay_path,
                proposed_bytes=self._replacement_bytes(),
            ),
            [],
        )

    def test_nested_non_evidence_scaffold_does_not_block_changed_write(self) -> None:
        self._write_json(
            "live_wrapper_with_embedded_template.json",
            {
                "artifact_kind": "current evidence wrapper",
                "embedded_template": {
                    "non_evidence_scaffold": True,
                    "differential_overlay_path": (
                        "audit/source_record_differential_revalidation.json"
                    ),
                    "differential_overlay_sha256": hashlib.sha256(
                        self.original_bytes
                    ).hexdigest(),
                },
            },
        )

        self.assertEqual(
            DIFFERENTIAL.source_record_differential_write_pins(
                paper_dir=self.paper_dir,
                output_path=self.overlay_path,
                proposed_bytes=self._replacement_bytes(),
            ),
            [],
        )

    def test_stale_or_byte_identical_reference_does_not_block(self) -> None:
        self._selected_pin(sha256="a" * 64)

        self.assertEqual(
            DIFFERENTIAL.source_record_differential_write_pins(
                paper_dir=self.paper_dir,
                output_path=self.overlay_path,
                proposed_bytes=self._replacement_bytes(),
            ),
            [],
        )

    def test_symlinked_overlay_reference_cannot_escape_paper(self) -> None:
        external = self.root / "external_overlay.json"
        external.write_bytes(self.original_bytes)
        (self.audit_dir / "escape").symlink_to(external)
        self._write_json(
            "escaped_pin.json",
            {
                "current_selected_semantic_revalidation": {
                    "differential_overlay_path": "audit/escape",
                    "differential_overlay_sha256": hashlib.sha256(
                        self.original_bytes
                    ).hexdigest(),
                }
            },
        )

        pins = DIFFERENTIAL.source_record_differential_write_pins(
            paper_dir=self.paper_dir,
            output_path=external,
            proposed_bytes=self._replacement_bytes(),
        )

        self.assertEqual(pins, [])
        self.assertEqual(
            DIFFERENTIAL.source_record_differential_write_pins(
                paper_dir=self.paper_dir,
                output_path=self.overlay_path,
                proposed_bytes=self.original_bytes,
            ),
            [],
        )

    def test_cli_requires_explicit_override_and_allows_unpinned_out(self) -> None:
        self._selected_pin()
        prior_path = self.root / "prior.json"
        judgments_path = self.root / "judgments.json"
        current_path = self.audit_dir / "source_record_audit.json"
        for path in (prior_path, judgments_path, current_path):
            path.write_text("{}\n", encoding="utf-8")
        replacement = {"items": [], "manual_review_required": []}

        def run(*extra: str) -> int:
            argv = [
                "source_record_differential_revalidation.py",
                "--root",
                str(self.root),
                "--paper",
                PAPER,
                "--prior-raw-audit",
                str(prior_path),
                "--prior-judgments",
                str(judgments_path),
                "--write",
                *extra,
            ]
            with patch.object(sys, "argv", argv), patch.object(
                DIFFERENTIAL,
                "build_source_record_differential_revalidation",
                return_value=replacement,
            ):
                return DIFFERENTIAL.main()

        self.assertEqual(run(), 1)
        self.assertEqual(self.overlay_path.read_bytes(), self.original_bytes)

        exploratory = self.audit_dir / "source_record_differential_revalidation.exploratory.json"
        self.assertEqual(run("--out", str(exploratory)), 0)
        self.assertTrue(exploratory.is_file())
        self.assertEqual(self.overlay_path.read_bytes(), self.original_bytes)

        self.assertEqual(run("--replace-byte-pinned-overlay"), 0)
        self.assertEqual(
            self.overlay_path.read_bytes(),
            (json.dumps(replacement, indent=2, sort_keys=True) + "\n").encode("utf-8"),
        )


if __name__ == "__main__":
    unittest.main()
