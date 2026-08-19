from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from scripts import public_source_display_projection as projection
from scripts.public_release_projection import project_bytes


def _sha256(value: str | bytes) -> str:
    raw = value.encode("utf-8") if isinstance(value, str) else value
    return hashlib.sha256(raw).hexdigest()


class PublicSourceDisplayProjectionTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary_directory = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary_directory.name)
        self.papers = self.root / "papers"
        self.folder = self.papers / "Fixture"
        (self.folder / "audit").mkdir(parents=True)
        self.source_text = (
            "Definition 1. A fixture object has one named property.\n"
            "Theorem 1. Every fixture object has that property.\n"
            "Equation (1). This standalone formula is not a named theorem.\n"
        )
        (self.folder / "source.txt").write_text(self.source_text, encoding="utf-8")
        self._write_map()

    def tearDown(self) -> None:
        self.temporary_directory.cleanup()

    @property
    def map_path(self) -> Path:
        return self.folder / "audit" / "paper_statement_map.json"

    def _anchor(self, line_start: int, line_end: int) -> dict[str, object]:
        quote = "\n".join(self.source_text.splitlines()[line_start - 1 : line_end])
        return {
            "path": "source.txt",
            "line_start": line_start,
            "line_end": line_end,
            "quoted_text": quote,
            "quoted_text_sha256": _sha256(quote),
        }

    def _write_map(self, *, stale_anchor_hash: bool = False) -> None:
        theorem_anchor = self._anchor(2, 2)
        if stale_anchor_hash:
            theorem_anchor["quoted_text_sha256"] = "0" * 64
        payload = {
            "paper": "Fixture",
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": _sha256(self.source_text),
            "source_coverage_mode": "named_theoretical_statements",
            "items": {
                "fixture_definition": {
                    "source_kind": "definition",
                    "statement": "Definition 1 defines the fixture object.",
                    "source_location": "source.txt:1",
                    "source_anchor_evidence": [self._anchor(1, 1)],
                },
                "fixture_theorem": {
                    "source_kind": "theorem",
                    "statement": "Theorem 1 gives the fixture property.",
                    "source_location": "source.txt:2",
                    "source_anchor_evidence": [theorem_anchor],
                    "semantic_context_requirements": [
                        {
                            "semantic_role": "definition",
                            "source_anchor_evidence": [self._anchor(1, 1)],
                        }
                    ],
                },
                "standalone_formula": {
                    "source_kind": "formula",
                    "statement": "Equation (1) is a standalone formula.",
                    "source_location": "source.txt:3",
                    "source_anchor_evidence": [self._anchor(3, 3)],
                },
            },
        }
        self.map_path.write_text(
            json.dumps(payload, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )

    def test_build_freezes_current_coverage_surface_without_full_raw_source(self) -> None:
        first = projection.build_public_source_display_projection(self.folder)
        second = projection.build_public_source_display_projection(self.folder)
        self.assertEqual(first, second)
        self.assertEqual(
            first["selected_source_item_ids"],
            ["fixture_definition", "fixture_theorem"],
        )
        self.assertEqual(first["source_coverage_mode"], "named_theoretical_statements")
        self.assertEqual(
            first["private_source_map_sha256"], _sha256(self.map_path.read_bytes())
        )
        self.assertEqual(
            first["public_source_map_sha256"],
            _sha256(
                project_bytes(
                    "papers/Fixture/audit/paper_statement_map.json",
                    self.map_path.read_bytes(),
                    include_source_display_marker=True,
                )
            ),
        )
        self.assertEqual(first["source_artifact_sha256"], _sha256(self.source_text))
        self.assertEqual(
            first["public_manifest_path"],
            "papers/Fixture/audit/public_source_display_projection.json",
        )
        self.assertFalse(first["raw_source_artifact_included"])
        self.assertEqual(
            first["raw_source_display_material"],
            "selected_byte_pinned_source_anchor_quotes",
        )
        serialized = projection.public_source_display_projection_bytes(self.folder)
        self.assertNotIn(b"This standalone formula", serialized)
        self.assertNotIn(b'"path"', serialized)
        theorem = first["selected_source_items"]["fixture_theorem"]
        self.assertEqual(
            theorem["source_anchors"][0]["quoted_text_sha256"],
            _sha256("Theorem 1. Every fixture object has that property."),
        )
        self.assertEqual(
            theorem["semantic_context"][0]["semantic_role"], "definition"
        )

    def test_write_and_validation_detect_a_changed_displayed_anchor(self) -> None:
        output = projection.write_public_source_display_projection(self.folder)
        self.assertEqual(output, self.folder / "audit/public_source_display_projection.json")
        self.assertEqual(projection.validate_public_source_display_projection(self.folder), [])

        payload = json.loads(output.read_text(encoding="utf-8"))
        payload["selected_source_items"]["fixture_theorem"]["source_anchors"][0][
            "quoted_text_sha256"
        ] = "f" * 64
        output.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        issues = projection.validate_public_source_display_projection(self.folder)
        self.assertTrue(any("quoted_text_sha256" in issue for issue in issues))
        self.assertTrue(any("deterministic serialization" in issue for issue in issues))

    def test_generation_fails_closed_on_stale_private_anchor_or_source_pin(self) -> None:
        payload = json.loads(self.map_path.read_text(encoding="utf-8"))
        second_anchor = dict(
            payload["items"]["fixture_theorem"]["source_anchor_evidence"][0]
        )
        second_anchor["quoted_text_sha256"] = "0" * 64
        # The first anchor retains the existing selector's theorem presentation;
        # the second proves that every anchor on a selected item is checked.
        payload["items"]["fixture_theorem"]["source_anchor_evidence"].append(
            second_anchor
        )
        self.map_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
        with self.assertRaisesRegex(
            projection.PublicSourceDisplayProjectionError, "bound source record"
        ):
            projection.build_public_source_display_projection(self.folder)

        self._write_map()
        payload = json.loads(self.map_path.read_text(encoding="utf-8"))
        payload["source_artifact_sha256"] = "1" * 64
        self.map_path.write_text(json.dumps(payload) + "\n", encoding="utf-8")
        with self.assertRaisesRegex(
            projection.PublicSourceDisplayProjectionError,
            "current byte-pinned canonical source artifact",
        ):
            projection.build_public_source_display_projection(self.folder)

    def test_cli_write_and_check_use_the_fixed_paper_local_target(self) -> None:
        original_papers_dir = projection.PAPERS_DIR
        projection.PAPERS_DIR = self.papers
        try:
            self.assertEqual(projection.main(["--paper", "Fixture", "--write"]), 0)
            self.assertEqual(projection.main(["--paper", "Fixture", "--check"]), 0)
            output = projection.public_source_display_projection_path(self.folder)
            payload = json.loads(output.read_text(encoding="utf-8"))
            payload["selected_source_item_ids"] = ["fixture_definition"]
            output.write_text(json.dumps(payload) + "\n", encoding="utf-8")
            self.assertEqual(projection.main(["--paper", "Fixture", "--check"]), 1)
        finally:
            projection.PAPERS_DIR = original_papers_dir


if __name__ == "__main__":
    unittest.main()
