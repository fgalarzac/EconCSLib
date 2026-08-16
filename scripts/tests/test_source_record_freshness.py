#!/usr/bin/env python3
"""Regression tests for schema-gated source-record judgment reuse."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    import_root_text = str(import_root)
    if import_root_text not in sys.path:
        sys.path.insert(0, import_root_text)

from source_record_freshness import (  # noqa: E402
    SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
    source_record_item_judgment_current,
)


class SourceRecordFreshnessTests(unittest.TestCase):
    def test_current_aggregate_accepts_historical_item_metadata(self) -> None:
        self.assertTrue(
            source_record_item_judgment_current(
                aggregate_current=True,
                expected_item_digest="current-item-digest",
                judgment_item_digest="old-item-digest",
                judgment_item_digest_schema=None,
            )
        )

    def test_unchanged_schema_two_item_reuses_after_unrelated_aggregate_change(
        self,
    ) -> None:
        self.assertTrue(
            source_record_item_judgment_current(
                aggregate_current=False,
                expected_item_digest="current-item-digest",
                judgment_item_digest="current-item-digest",
                judgment_item_digest_schema=SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
            )
        )

    def test_legacy_or_mismatched_item_digest_fails_closed(self) -> None:
        for schema, digest in (
            (None, "current-item-digest"),
            (SOURCE_RECORD_ITEM_DIGEST_SCHEMA - 1, "current-item-digest"),
            (SOURCE_RECORD_ITEM_DIGEST_SCHEMA, "stale-item-digest"),
            (SOURCE_RECORD_ITEM_DIGEST_SCHEMA, ""),
        ):
            with self.subTest(schema=schema, digest=digest):
                self.assertFalse(
                    source_record_item_judgment_current(
                        aggregate_current=False,
                        expected_item_digest="current-item-digest",
                        judgment_item_digest=digest,
                        judgment_item_digest_schema=schema,
                    )
                )


if __name__ == "__main__":
    unittest.main()
