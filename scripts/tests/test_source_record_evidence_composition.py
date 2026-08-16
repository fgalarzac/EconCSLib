#!/usr/bin/env python3
"""Tests for live-versus-archived evidence-composition context selection."""

from __future__ import annotations

import argparse
from pathlib import Path
from unittest.mock import patch
import unittest


ROOT = Path(__file__).resolve().parents[2]

import sys

if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import source_record_evidence_composition as COMPOSITION


class EvidenceCompositionContextTests(unittest.TestCase):
    def setUp(self) -> None:
        self.paper_dir = ROOT / ".scratch" / "composition-context-fixture"
        self.canonical_raw = self.paper_dir / "audit" / "source_record_audit.json"
        self.archived_raw = self.paper_dir / "audit" / "source_record_audit.archived.json"
        self.archived_provenance = self.paper_dir / "audit" / "source_record_audit.provenance.json"

    def test_canonical_raw_uses_live_target_context_without_explicit_archive(self) -> None:
        self.assertIsNone(
            COMPOSITION._archived_replay_provenance_path(
                self.canonical_raw,
                self.canonical_raw,
                canonical_raw_path=self.canonical_raw,
                provenance_was_explicit=False,
            )
        )

    def test_distinct_raw_receipt_stays_in_archived_target_context(self) -> None:
        self.assertEqual(
            COMPOSITION._archived_replay_provenance_path(
                self.archived_raw,
                self.canonical_raw,
                canonical_raw_path=self.canonical_raw,
                provenance_was_explicit=False,
            ),
            self.canonical_raw,
        )

    def test_explicit_provenance_preserves_archived_replay_mode(self) -> None:
        self.assertEqual(
            COMPOSITION._archived_replay_provenance_path(
                self.canonical_raw,
                self.archived_provenance,
                canonical_raw_path=self.canonical_raw,
                provenance_was_explicit=True,
            ),
            self.archived_provenance,
        )

    def _main_args(self, *, historical_provenance_path: Path | None) -> argparse.Namespace:
        root = ROOT / ".scratch" / "composition-command-fixture"
        paper_dir = root / "papers" / "FixturePaper"
        audit_dir = paper_dir / "audit"
        return argparse.Namespace(
            root=root,
            paper="FixturePaper",
            historical_raw_audit=audit_dir / "source_record_audit.json",
            selected_current_sidecar=audit_dir / "selected.json",
            differential_overlay=audit_dir / "overlay.json",
            differential_overlay_provenance_path=None,
            historical_provenance_path=historical_provenance_path,
            out=audit_dir / "out.json",
            write=False,
        )

    def _main_replay_provenance(self, args: argparse.Namespace) -> tuple[object, object]:
        raw_audit = {"paper": "FixturePaper"}
        selected = {"paper": "FixturePaper", "items": {}}
        with patch.object(COMPOSITION, "parse_args", return_value=args), patch.object(
            COMPOSITION,
            "_load_json_object",
            side_effect=[raw_audit, selected],
        ), patch.object(
            COMPOSITION.REVALIDATION,
            "materialize_authenticated_selected_evidence",
            return_value={"items": {}},
        ) as materialize, patch.object(
            COMPOSITION.REVALIDATION,
            "materialized_authenticated_selected_evidence_errors",
            return_value=[],
        ) as validate:
            self.assertEqual(COMPOSITION.main(), 0)
        return (
            materialize.call_args.kwargs["raw_audit_provenance_path"],
            validate.call_args.kwargs["raw_audit_provenance_path"],
        )

    def test_main_uses_live_context_for_the_canonical_raw_receipt(self) -> None:
        args = self._main_args(historical_provenance_path=None)
        materialize_path, validate_path = self._main_replay_provenance(args)
        self.assertIsNone(materialize_path)
        self.assertIsNone(validate_path)

    def test_main_preserves_explicit_archived_context(self) -> None:
        root = ROOT / ".scratch" / "composition-command-fixture"
        explicit = root / "papers" / "FixturePaper" / "audit" / "archived.json"
        args = self._main_args(historical_provenance_path=explicit)
        materialize_path, validate_path = self._main_replay_provenance(args)
        self.assertEqual(materialize_path, explicit.resolve())
        self.assertEqual(validate_path, explicit.resolve())


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
