#!/usr/bin/env python3
"""Focused regressions for the deterministic TeX audit transcript builder."""

from __future__ import annotations

import contextlib
import io
import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "build_tex_audit_transcript.py"
SPEC = importlib.util.spec_from_file_location("tex_audit_transcript_test", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
TRANSCRIPT = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = TRANSCRIPT
SPEC.loader.exec_module(TRANSCRIPT)


def profile_payload(*, include_input: bool = True) -> dict[str, object]:
    reads: dict[str, str] = {
        "include": "render",
        "CatchFileDef": "read_not_rendered",
    }
    if include_input:
        reads["input"] = "render"
    return {
        "schema": 1,
        "entrypoint": "main.tex",
        "path_resolution": "source_root_tex_extension",
        "file_reads": reads,
        "redlines": {
            "commands": {
                "DIFadd": "keep_argument",
                "DIFdel": "drop_argument",
            },
            "spans": {"DIFadd": "keep", "DIFdel": "drop"},
        },
        "unknown_file_read": "error",
        "unknown_redline": "error",
    }


class TeXAuditTranscriptTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name) / "source"
        self.root.mkdir(parents=True)
        self.profile = Path(self.temporary.name) / "profile.json"
        self.write_profile()

    def write_profile(self, *, include_input: bool = True) -> None:
        self.profile.write_text(
            json.dumps(profile_payload(include_input=include_input), indent=2),
            encoding="utf-8",
        )

    def write(self, relative: str, text: str) -> None:
        path = self.root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def test_build_resolves_active_literal_inputs_and_intended_redlines(self) -> None:
        self.write(
            "main.tex",
            """% \\input{commented-out}
before \\DIFdel{deleted command} \\DIFadd{kept command}
\\input{child}
\\CatchFileDef{\\saved}{hidden}{ }
\\DIFdelbegin
deleted span
\\DIFdelend
\\DIFaddbegin
kept span
\\DIFaddend
""",
        )
        self.write("child.tex", "child semantic text\n")
        self.write("hidden.tex", "SECRET NON-RENDERED CONTENT\n")

        built = TRANSCRIPT.build_transcript(self.root, self.profile)

        self.assertIn("kept command", built.text)
        self.assertIn("child semantic text", built.text)
        self.assertIn("kept span", built.text)
        self.assertNotIn("deleted command", built.text)
        self.assertNotIn("deleted span", built.text)
        self.assertNotIn("SECRET NON-RENDERED CONTENT", built.text)
        self.assertIn("READ NOT RENDERED", built.text)
        files = {item.path: item for item in built.source_files}
        self.assertEqual(set(files), {"main.tex", "child.tex", "hidden.tex"})
        self.assertTrue(files["main.tex"].rendered)
        self.assertTrue(files["child.tex"].rendered)
        self.assertFalse(files["hidden.tex"].rendered)
        self.assertEqual(
            [(edge.command, edge.target, edge.behavior) for edge in built.file_reads],
            [
                ("input", "child.tex", "render"),
                ("CatchFileDef", "hidden.tex", "read_not_rendered"),
            ],
        )
        self.assertTrue(
            any(
                event.command == "DIFdel" and event.behavior == "drop_argument"
                for event in built.redline_events
            )
        )
        self.assertTrue(
            any(
                any(origin.get("source_path") == "child.tex" for origin in row["origins"])
                for row in built.line_provenance
            )
        )

    def test_build_verify_and_snapshot_are_deterministic(self) -> None:
        self.write("main.tex", "root\n\\input{child}\n")
        self.write("child.tex", "child\n")
        transcript = Path(self.temporary.name) / "out" / "audit.tex"
        manifest = Path(self.temporary.name) / "out" / "audit.manifest.json"
        build_args = SimpleNamespace(
            source_root=self.root,
            profile=self.profile,
            transcript=transcript,
            manifest=manifest,
        )
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(TRANSCRIPT.command_build(build_args), 0)
        verify_args = SimpleNamespace(
            source_root=self.root,
            profile=self.profile,
            transcript=transcript,
            manifest=manifest,
        )
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(TRANSCRIPT.command_verify(verify_args), 0)

        snapshot = Path(self.temporary.name) / "raw"
        snapshot_args = SimpleNamespace(
            source_root=self.root,
            profile=self.profile,
            destination=snapshot,
            source_revision="fixture-revision",
            overwrite=False,
        )
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(TRANSCRIPT.command_snapshot(snapshot_args), 0)
        graph = json.loads((snapshot / "source_graph_manifest.json").read_text())
        self.assertEqual(graph["source_revision"], "fixture-revision")
        self.assertEqual(
            [item["path"] for item in graph["source_files"]], ["child.tex", "main.tex"]
        )
        self.assertEqual((snapshot / "child.tex").read_text(encoding="utf-8"), "child\n")
        (snapshot / "stale.tex").write_text("stale\n", encoding="utf-8")
        snapshot_args.overwrite = True
        with self.assertRaisesRegex(TRANSCRIPT.TranscriptError, "stale/unconfigured"):
            TRANSCRIPT.command_snapshot(snapshot_args)

    def test_verify_rejects_source_drift(self) -> None:
        self.write("main.tex", "root\n")
        transcript = Path(self.temporary.name) / "audit.tex"
        manifest = Path(self.temporary.name) / "audit.manifest.json"
        with contextlib.redirect_stdout(io.StringIO()):
            TRANSCRIPT.command_build(
                SimpleNamespace(
                    source_root=self.root,
                    profile=self.profile,
                    transcript=transcript,
                    manifest=manifest,
                )
            )
        self.write("main.tex", "changed root\n")
        with self.assertRaisesRegex(TRANSCRIPT.TranscriptError, "deterministic rebuild"):
            TRANSCRIPT.command_verify(
                SimpleNamespace(
                    source_root=self.root,
                    profile=self.profile,
                    transcript=transcript,
                    manifest=manifest,
                )
            )

    def test_unknown_live_redline_and_unconfigured_read_fail_closed(self) -> None:
        self.write("main.tex", "\\DIFmystery{unreviewed}\n")
        with self.assertRaisesRegex(TRANSCRIPT.TranscriptError, "unknown live redline"):
            TRANSCRIPT.build_transcript(self.root, self.profile)

        self.write("main.tex", "\\input{child}\n")
        self.write("child.tex", "child\n")
        self.write_profile(include_input=False)
        with self.assertRaisesRegex(TRANSCRIPT.TranscriptError, "no configured file-read behavior"):
            TRANSCRIPT.build_transcript(self.root, self.profile)

    def test_unknown_profile_behavior_and_verb_percent_fail_or_preserve_correctly(self) -> None:
        payload = profile_payload()
        file_reads = payload["file_reads"]
        assert isinstance(file_reads, dict)
        file_reads["input"] = "guess"
        self.profile.write_text(json.dumps(payload), encoding="utf-8")
        with self.assertRaisesRegex(TRANSCRIPT.TranscriptError, "unknown behavior"):
            TRANSCRIPT.load_profile(self.profile)

        self.write_profile()
        self.write("main.tex", r"\verb|100% literal| % ordinary comment" + "\n")
        built = TRANSCRIPT.build_transcript(self.root, self.profile)
        self.assertIn(r"\verb|100% literal|", built.text)
        self.assertNotIn("ordinary comment", built.text)

    def test_unknown_file_read_form_is_not_approximated(self) -> None:
        self.write("main.tex", "\\InputIfFileExists{child}{}{}\n")
        with self.assertRaisesRegex(TRANSCRIPT.TranscriptError, "unsupported file-read command"):
            TRANSCRIPT.build_transcript(self.root, self.profile)


if __name__ == "__main__":
    unittest.main()
