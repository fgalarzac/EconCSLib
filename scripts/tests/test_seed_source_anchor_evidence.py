#!/usr/bin/env python3
"""Regression tests for deterministic source-anchor evidence seeding."""

from __future__ import annotations

import hashlib
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    if str(import_root) not in sys.path:
        sys.path.insert(0, str(import_root))

import seed_source_anchor_evidence as seed  # noqa: E402


class SourceAnchorEvidenceSeedTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.folder = Path(self.temporary.name) / "FixturePaper"
        self.folder.mkdir()
        self.source = self.folder / "source.txt"
        self.source.write_text("alpha\nbeta\ngamma\n", encoding="utf-8")
        self.payload = {
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": hashlib.sha256(self.source.read_bytes()).hexdigest(),
            "items": {
                "renamable_catalog_key": {
                    "source_location": "source.txt:2-3",
                }
            },
        }

    def test_seed_uses_exact_line_slice_and_hash(self) -> None:
        changed = seed.seed_payload(self.payload, self.folder, replace=False)
        self.assertEqual(changed, 1)
        entry = self.payload["items"]["renamable_catalog_key"][
            "source_anchor_evidence"
        ][0]
        self.assertEqual(entry["path"], "source.txt")
        self.assertEqual(entry["line_start"], 2)
        self.assertEqual(entry["line_end"], 3)
        self.assertEqual(entry["quoted_text"], "beta\ngamma")
        self.assertEqual(
            entry["quoted_text_sha256"],
            hashlib.sha256(b"beta\ngamma").hexdigest(),
        )
        self.assertEqual(seed.seed_payload(self.payload, self.folder, replace=False), 0)

    def test_seed_emits_each_discontiguous_exact_span(self) -> None:
        item = self.payload["items"]["renamable_catalog_key"]
        item["source_location"] = "source.txt:1; source.txt:3"

        changed = seed.seed_payload(self.payload, self.folder, replace=False)

        self.assertEqual(changed, 1)
        self.assertEqual(
            item["source_anchor_evidence"],
            [
                {
                    "path": "source.txt",
                    "line_start": 1,
                    "line_end": 1,
                    "quoted_text": "alpha",
                    "quoted_text_sha256": hashlib.sha256(b"alpha").hexdigest(),
                },
                {
                    "path": "source.txt",
                    "line_start": 3,
                    "line_end": 3,
                    "quoted_text": "gamma",
                    "quoted_text_sha256": hashlib.sha256(b"gamma").hexdigest(),
                },
            ],
        )

    def test_refuses_to_overwrite_different_reviewed_evidence(self) -> None:
        item = self.payload["items"]["renamable_catalog_key"]
        item["source_anchor_evidence"] = [{"quoted_text": "not a source slice"}]
        with self.assertRaisesRegex(ValueError, "existing source_anchor_evidence"):
            seed.seed_payload(self.payload, self.folder, replace=False)

    def test_rejects_noncanonical_source_anchor(self) -> None:
        self.payload["items"]["renamable_catalog_key"][
            "source_location"
        ] = "other.txt:1"
        with self.assertRaisesRegex(ValueError, "does not name the canonical artifact"):
            seed.seed_payload(self.payload, self.folder, replace=False)

    def test_selected_item_refresh_leaves_other_items_untouched(self) -> None:
        self.payload["items"]["other_navigation_key"] = {
            "source_location": "source.txt:1",
        }

        changed = seed.seed_payload(
            self.payload,
            self.folder,
            replace=False,
            item_key="renamable_catalog_key",
        )

        self.assertEqual(changed, 1)
        self.assertIn(
            "source_anchor_evidence",
            self.payload["items"]["renamable_catalog_key"],
        )
        self.assertNotIn(
            "source_anchor_evidence",
            self.payload["items"]["other_navigation_key"],
        )

    def test_selected_item_requires_an_object_map_item(self) -> None:
        with self.assertRaisesRegex(ValueError, "no object item"):
            seed.seed_payload(
                self.payload,
                self.folder,
                replace=False,
                item_key="missing_navigation_key",
            )


if __name__ == "__main__":
    unittest.main()
