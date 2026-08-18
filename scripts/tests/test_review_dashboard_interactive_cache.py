from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import review_dashboard


class ReviewDashboardInteractiveCacheTests(unittest.TestCase):
    def test_interactive_cache_skips_full_lean_closure_walk(self) -> None:
        """The browser can reuse already-elaborated closeout-era review rows."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "CachedPaper"
            folder.mkdir()
            (folder / "PaperInterface.lean").write_text(
                "theorem endpoint : True := by trivial\n", encoding="utf-8"
            )
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "status": "formalized",
                        "review_surface": {"include_names": ["endpoint"]},
                    }
                ),
                encoding="utf-8",
            )
            cache_path = folder / ".review_traces" / "paper_interface_cache.json"
            cache_path.parent.mkdir()
            hashes = review_dashboard._cache_nonlean_source_hashes(folder)
            hashes["lean_source_closure_sha256"] = "a" * 64
            row = review_dashboard.ReviewItem(
                name="endpoint",
                kind="theorem",
                lean_statement="True",
                paper_statement="",
                agent_statement="",
                full_name="CachedPaper.endpoint",
                interface_source="theorem endpoint : True := by trivial",
            )
            cache_path.write_text(
                json.dumps(
                    {
                        "schema": review_dashboard.PAPER_INTERFACE_CACHE_SCHEMA,
                        "paper": folder.name,
                        "hashes": hashes,
                        "rows": [row.__dict__],
                    }
                ),
                encoding="utf-8",
            )

            with (
                mock.patch.object(
                    review_dashboard,
                    "paper_interface_cache_file",
                    return_value=cache_path,
                ),
                mock.patch.object(
                    review_dashboard,
                    "repository_build_input_snapshot",
                    side_effect=AssertionError("interactive cache must not walk Lean imports"),
                ),
            ):
                rows = review_dashboard.review_items_for_paper(
                    folder, render_images=False
                )

        self.assertEqual([item.name for item in rows], ["endpoint"])
