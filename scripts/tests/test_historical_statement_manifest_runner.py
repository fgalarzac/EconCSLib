#!/usr/bin/env python3
"""Focused tests for the pinned historical statement-manifest runner."""

from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Mapping, Sequence
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    text = str(import_root)
    if text not in sys.path:
        sys.path.insert(0, text)

from scripts import historical_statement_manifest_runner as RUNNER  # noqa: E402
from scripts.tests.test_historical_statement_manifest_replay import (  # noqa: E402
    current_manifest,
    historic_manifest,
    recipe as base_recipe,
    sha,
    target,
)


SERIALIZER_BYTES = b'''from __future__ import annotations

import json
from pathlib import Path


def run_lean_signature_manifests(
    root: Path,
    import_module: str,
    declaration_names: list[str],
    *,
    timeout_seconds: int,
    build_timeout_seconds: int,
) -> dict[str, dict[str, object]]:
    del root, import_module, timeout_seconds, build_timeout_seconds
    return {name: {"schema": 2, "name": name} for name in declaration_names}
'''
HELPER_BYTES = b"old helper"
COMMIT = "a" * 40
SERIALIZER_BLOB = "b" * 40
HELPER_BLOB = "c" * 40


class FakeGit:
    """Small injected Git boundary that exposes only pinned-object commands."""

    def __init__(self, *, serializer_bytes: bytes = SERIALIZER_BYTES) -> None:
        self.serializer_bytes = serializer_bytes
        self.calls: list[tuple[str, ...]] = []

    def __call__(
        self, argv: Sequence[str], cwd: Path
    ) -> subprocess.CompletedProcess[bytes]:
        del cwd
        command = tuple(argv)
        self.calls.append(command)
        stdout: bytes | None = None
        if command == ("git", "rev-parse", "--verify", f"{COMMIT}^{{commit}}"):
            stdout = f"{COMMIT}\n".encode("ascii")
        elif command == (
            "git",
            "rev-parse",
            "--verify",
            f"{COMMIT}:scripts/lean_signature_manifest.py",
        ):
            stdout = f"{SERIALIZER_BLOB}\n".encode("ascii")
        elif command == (
            "git",
            "rev-parse",
            "--verify",
            f"{COMMIT}:scripts/lean_signature_manifest_helper.lean",
        ):
            stdout = f"{HELPER_BLOB}\n".encode("ascii")
        elif command == ("git", "cat-file", "blob", SERIALIZER_BLOB):
            stdout = self.serializer_bytes
        elif command == ("git", "cat-file", "blob", HELPER_BLOB):
            stdout = HELPER_BYTES
        if stdout is None:
            return subprocess.CompletedProcess(command, 1, b"", b"unexpected command")
        return subprocess.CompletedProcess(command, 0, stdout, b"")


class HistoricalStatementManifestRunnerTests(unittest.TestCase):
    def _closure(self, root: Path) -> tuple[dict[str, object], bytes]:
        interface = root / "papers/Fixture/PaperInterface.lean"
        toolchain = root / "lean-toolchain"
        lake_manifest = root / "lake-manifest.json"
        closure: dict[str, object] = {
            "schema": RUNNER.lean_import_closure.WORKTREE_IDENTITY_SCHEMA,
            "entrypoint": "papers/Fixture/PaperInterface.lean",
            "entry_module": "Fixture.PaperInterface",
            "lean_loaded_modules": ["Fixture.PaperInterface"],
            "sources": [
                {
                    "module": "Fixture.PaperInterface",
                    "path": "papers/Fixture/PaperInterface.lean",
                    "byte_length": len(interface.read_bytes()),
                    "sha256": hashlib.sha256(interface.read_bytes()).hexdigest(),
                }
            ],
            "external_import_modules": [],
            "external_module_artifacts_sha256": "d" * 64,
            "build_controls": [
                {
                    "path": "lean-toolchain",
                    "tracked_in_index": True,
                    "untracked": False,
                    "path_kind": "file",
                    "byte_length": len(toolchain.read_bytes()),
                    "sha256": hashlib.sha256(toolchain.read_bytes()).hexdigest(),
                },
                {
                    "path": "lake-manifest.json",
                    "tracked_in_index": True,
                    "untracked": False,
                    "path_kind": "file",
                    "byte_length": len(lake_manifest.read_bytes()),
                    "sha256": hashlib.sha256(lake_manifest.read_bytes()).hexdigest(),
                },
            ],
            "lake_routing": {
                "schema": RUNNER.lean_import_closure.LAKE_ROUTING_SCHEMA,
                "kind": "toml",
                "package_configuration": {"name": "Fixture"},
                "lean_library": {"name": "Fixture"},
            },
        }
        return closure, RUNNER.current_lean_import_closure_canonical_bytes(closure)

    def _recipe(self, root: Path) -> dict[str, object]:
        value = base_recipe()
        execution = value["current_execution_inputs"]
        assert isinstance(execution, dict)
        execution["paper_interface_bytes_sha256"] = hashlib.sha256(
            (root / "papers/Fixture/PaperInterface.lean").read_bytes()
        ).hexdigest()
        execution["lean_toolchain_bytes_sha256"] = hashlib.sha256(
            (root / "lean-toolchain").read_bytes()
        ).hexdigest()
        execution["lake_manifest_bytes_sha256"] = hashlib.sha256(
            (root / "lake-manifest.json").read_bytes()
        ).hexdigest()
        closure, _ = self._closure(root)
        execution["lean_import_closure_sha256"] = (
            RUNNER.current_lean_import_closure_payload_sha256(closure)
        )
        serializer_blob = value["historical_serializer_blob"]
        assert isinstance(serializer_blob, dict)
        serializer_blob["bytes_sha256"] = hashlib.sha256(SERIALIZER_BYTES).hexdigest()
        value["runner_identity_sha256"] = sha("fixture production runner")
        return value

    def _fixture_root(self) -> tempfile.TemporaryDirectory[str]:
        temporary = tempfile.TemporaryDirectory()
        root = Path(temporary.name)
        interface = root / "papers/Fixture/PaperInterface.lean"
        interface.parent.mkdir(parents=True)
        interface.write_text("import Mathlib\n", encoding="utf-8")
        (root / "lean-toolchain").write_text("leanprover/lean4:v4.19.0\n", encoding="utf-8")
        (root / "lake-manifest.json").write_text("{}\n", encoding="utf-8")
        return temporary

    def _runner(
        self,
        root: Path,
        fake_git: FakeGit,
        executor,
    ) -> RUNNER.HistoricalStatementManifestRunner:
        closure, closure_bytes = self._closure(root)
        config = RUNNER.HistoricalStatementManifestRunnerConfig(
            root=root,
            import_module="Fixture.PaperInterface",
            paper_interface_path="papers/Fixture/PaperInterface.lean",
            current_lean_import_closure=closure,
            current_lean_import_closure_bytes=closure_bytes,
            runner_identity_sha256=sha("fixture production runner"),
        )
        return RUNNER.make_historical_statement_manifest_runner(
            config,
            command_runner=fake_git,
            serializer_executor=executor,
            current_lean_import_closure_verifier=lambda _root, _path, _closure: None,
        )

    def test_runs_once_and_returns_navigation_free_observations(self) -> None:
        with self._fixture_root() as temporary:
            root = Path(temporary)
            current = current_manifest()
            historical = historic_manifest()
            input_target = target(current, navigation="Fixture.Current.route")
            input_target["sidecar_key"] = "old-sidecar-navigation"
            input_target["source_map_key"] = "paper-facing-map-key"
            calls: list[tuple[object, ...]] = []

            def executor(
                serializer_bytes: bytes,
                helper_bytes: bytes,
                execution_root: Path,
                import_module: str,
                declarations: Sequence[str],
                timeout_seconds: int,
                build_timeout_seconds: int,
            ) -> Mapping[str, Mapping[str, object]]:
                calls.append(
                    (
                        serializer_bytes,
                        helper_bytes,
                        execution_root,
                        import_module,
                        tuple(declarations),
                        timeout_seconds,
                        build_timeout_seconds,
                    )
                )
                return {"Fixture.Current.route": historical}

            fake_git = FakeGit()
            runner = self._runner(root, fake_git, executor)
            result = runner(self._recipe(root), [input_target])

            self.assertEqual(len(calls), 1)
            self.assertEqual(calls[0][0], SERIALIZER_BYTES)
            self.assertEqual(calls[0][1], HELPER_BYTES)
            self.assertEqual(calls[0][3], "Fixture.PaperInterface")
            self.assertEqual(calls[0][4], ("Fixture.Current.route",))
            self.assertEqual(
                set(result),
                {
                    "historical_serializer_recipe_sha256",
                    "verified_historical_git_blobs",
                    "current_execution_inputs",
                    "observations",
                },
            )
            observations = result["observations"]
            assert isinstance(observations, list)
            self.assertEqual(len(observations), 1)
            observation = observations[0]
            self.assertNotIn("declaration", observation)
            self.assertNotIn("Fixture.Current.route", json.dumps(result, sort_keys=True))
            self.assertNotIn("old-sidecar-navigation", json.dumps(result, sort_keys=True))
            self.assertNotIn("paper-facing-map-key", json.dumps(result, sort_keys=True))
            self.assertEqual(
                observation["historical_manifest_signature_sha256"], historical["sha256"]
            )
            historical_surface = observation["historical_manifest"]
            assert isinstance(historical_surface, dict)
            self.assertNotIn("semantic_dependency_graph", historical_surface)
            self.assertEqual(
                fake_git.calls,
                [
                    ("git", "rev-parse", "--verify", f"{COMMIT}^{{commit}}"),
                    (
                        "git",
                        "rev-parse",
                        "--verify",
                        f"{COMMIT}:scripts/lean_signature_manifest.py",
                    ),
                    ("git", "cat-file", "blob", SERIALIZER_BLOB),
                    (
                        "git",
                        "rev-parse",
                        "--verify",
                        f"{COMMIT}:scripts/lean_signature_manifest_helper.lean",
                    ),
                    ("git", "cat-file", "blob", HELPER_BLOB),
                ],
            )

    def test_cached_verification_avoids_a_second_git_read_but_not_a_serializer_run(
        self,
    ) -> None:
        with self._fixture_root() as temporary:
            root = Path(temporary)
            current = current_manifest()
            historical = historic_manifest()
            input_target = target(current, navigation="Fixture.Current.route")
            calls: list[tuple[str, ...]] = []

            def executor(*args: object) -> Mapping[str, Mapping[str, object]]:
                declarations = args[4]
                assert isinstance(declarations, tuple)
                calls.append(declarations)
                return {"Fixture.Current.route": historical}

            fake_git = FakeGit()
            runner = self._runner(root, fake_git, executor)
            current_recipe = self._recipe(root)
            self.assertIsNone(runner.verify_recipe(current_recipe))
            git_after_verify = list(fake_git.calls)
            runner(current_recipe, [input_target])
            self.assertEqual(fake_git.calls, git_after_verify)
            self.assertEqual(calls, [("Fixture.Current.route",)])

    def test_rejects_blob_bytes_before_serializer_execution(self) -> None:
        with self._fixture_root() as temporary:
            root = Path(temporary)
            current = current_manifest()
            input_target = target(current, navigation="Fixture.Current.route")
            executions: list[object] = []

            def executor(*args: object) -> Mapping[str, Mapping[str, object]]:
                executions.append(args)
                return {}

            runner = self._runner(root, FakeGit(serializer_bytes=b"wrong bytes"), executor)
            with self.assertRaisesRegex(
                RUNNER.HistoricalStatementManifestRunnerError,
                "historical historical_serializer_blob bytes do not match",
            ):
                runner(self._recipe(root), [input_target])
            self.assertEqual(executions, [])

    def test_rejects_changed_current_environment_before_serializer_execution(self) -> None:
        with self._fixture_root() as temporary:
            root = Path(temporary)
            current = current_manifest()
            input_target = target(current, navigation="Fixture.Current.route")
            executions: list[object] = []

            def executor(*args: object) -> Mapping[str, Mapping[str, object]]:
                executions.append(args)
                return {}

            runner = self._runner(root, FakeGit(), executor)
            current_recipe = self._recipe(root)
            (root / "lean-toolchain").write_text("different toolchain\n", encoding="utf-8")
            with self.assertRaisesRegex(
                RUNNER.HistoricalStatementManifestRunnerError,
                "current lean-toolchain bytes do not match",
            ):
                runner(current_recipe, [input_target])
            self.assertEqual(executions, [])

    def test_rechecks_current_environment_after_serializer_execution(self) -> None:
        with self._fixture_root() as temporary:
            root = Path(temporary)
            current = current_manifest()
            historical = historic_manifest()
            input_target = target(current, navigation="Fixture.Current.route")

            def executor(*args: object) -> Mapping[str, Mapping[str, object]]:
                del args
                (root / "lake-manifest.json").write_text(
                    "{\"changed\":true}\n", encoding="utf-8"
                )
                return {"Fixture.Current.route": historical}

            runner = self._runner(root, FakeGit(), executor)
            with self.assertRaisesRegex(
                RUNNER.HistoricalStatementManifestRunnerError,
                "current lake-manifest bytes do not match",
            ):
                runner(self._recipe(root), [input_target])

    def test_rejects_missing_or_extra_historic_manifest_routes(self) -> None:
        with self._fixture_root() as temporary:
            root = Path(temporary)
            current = current_manifest()
            input_target = target(current, navigation="Fixture.Current.route")

            def executor(*args: object) -> Mapping[str, Mapping[str, object]]:
                del args
                return {"unexpected.route": historic_manifest()}

            runner = self._runner(root, FakeGit(), executor)
            with self.assertRaisesRegex(
                RUNNER.HistoricalStatementManifestRunnerError,
                "did not return exactly the requested",
            ):
                runner(self._recipe(root), [input_target])

    def test_rejects_recipe_for_a_different_runner_identity(self) -> None:
        with self._fixture_root() as temporary:
            root = Path(temporary)
            current = current_manifest()
            input_target = target(current, navigation="Fixture.Current.route")

            def executor(*args: object) -> Mapping[str, Mapping[str, object]]:
                del args
                return {"Fixture.Current.route": historic_manifest()}

            runner = self._runner(root, FakeGit(), executor)
            current_recipe = copy.deepcopy(self._recipe(root))
            current_recipe["runner_identity_sha256"] = sha("different runner")
            with self.assertRaisesRegex(
                RUNNER.HistoricalStatementManifestRunnerError,
                "different runner implementation",
            ):
                runner(current_recipe, [input_target])

    def test_rejects_non_self_contained_historical_python_before_execution(self) -> None:
        with self._fixture_root() as temporary:
            root = Path(temporary)
            current = current_manifest()
            input_target = target(current, navigation="Fixture.Current.route")
            executions: list[object] = []
            serializer = b'''def run_lean_signature_manifests(*args, **kwargs):
    import scripts.mutable_current_dependency
    return {}
'''

            def executor(*args: object) -> Mapping[str, Mapping[str, object]]:
                executions.append(args)
                return {}

            recipe = self._recipe(root)
            blob = recipe["historical_serializer_blob"]
            assert isinstance(blob, dict)
            blob["bytes_sha256"] = hashlib.sha256(serializer).hexdigest()
            runner = self._runner(root, FakeGit(serializer_bytes=serializer), executor)
            with self.assertRaisesRegex(
                RUNNER.HistoricalStatementManifestRunnerError,
                "non-self-contained module: scripts",
            ):
                runner(recipe, [input_target])
            self.assertEqual(executions, [])

    def test_dependency_gate_rejects_dynamic_import_and_path_mutation(self) -> None:
        self.assertIn(
            "dynamic code/import primitive",
            RUNNER.historical_serializer_dependency_error(b"__import__('scripts.x')\n")
            or "",
        )
        self.assertEqual(
            RUNNER.historical_serializer_dependency_error(
                b"import sys\nsys.path.append('mutable')\n"
            ),
            "historical serializer mutates sys.path",
        )
        self.assertIsNone(RUNNER.historical_serializer_dependency_error(SERIALIZER_BYTES))

    def test_default_executor_uses_isolated_python_and_single_json_result(self) -> None:
        with self._fixture_root() as temporary:
            root = Path(temporary)
            captured: dict[str, object] = {}

            def fake_run(argv: Sequence[str], **kwargs: object) -> subprocess.CompletedProcess[bytes]:
                captured["argv"] = tuple(argv)
                captured["kwargs"] = kwargs
                bootstrap = Path(str(argv[2]))
                captured["bootstrap"] = bootstrap.read_text(encoding="utf-8")
                return subprocess.CompletedProcess(
                    list(argv),
                    0,
                    (
                        RUNNER.ISOLATED_SERIALIZER_RESULT_SENTINEL
                        + '{"Fixture.Current.route":{"schema":2}}\n'
                    ).encode("utf-8"),
                    b"",
                )

            with mock.patch.object(RUNNER.subprocess, "run", side_effect=fake_run):
                result = RUNNER._default_historical_serializer_executor(
                    SERIALIZER_BYTES,
                    HELPER_BYTES,
                    root,
                    "Fixture.PaperInterface",
                    ("Fixture.Current.route",),
                    7,
                    11,
                )

            self.assertEqual(
                captured["argv"],
                (sys.executable, "-I", captured["argv"][2]),
            )
            kwargs = captured["kwargs"]
            assert isinstance(kwargs, dict)
            self.assertEqual(kwargs["cwd"], str(root))
            request = json.loads(bytes(kwargs["input"]).decode("utf-8"))
            self.assertEqual(request["declarations"], ["Fixture.Current.route"])
            self.assertIn("spec_from_file_location", str(captured["bootstrap"]))
            self.assertIn("sys.flags.isolated", str(captured["bootstrap"]))
            self.assertEqual(result, {"Fixture.Current.route": {"schema": 2}})

    def test_default_executor_runs_a_real_isolated_child(self) -> None:
        with self._fixture_root() as temporary:
            root = Path(temporary)
            result = RUNNER._default_historical_serializer_executor(
                SERIALIZER_BYTES,
                HELPER_BYTES,
                root,
                "Fixture.PaperInterface",
                ("Fixture.Current.route",),
                7,
                11,
            )
        self.assertEqual(
            result,
            {"Fixture.Current.route": {"name": "Fixture.Current.route", "schema": 2}},
        )

    def test_rejects_closure_digest_mismatch_before_serializer_execution(self) -> None:
        with self._fixture_root() as temporary:
            root = Path(temporary)
            current = current_manifest()
            input_target = target(current, navigation="Fixture.Current.route")
            executions: list[object] = []

            def executor(*args: object) -> Mapping[str, Mapping[str, object]]:
                executions.append(args)
                return {}

            recipe = self._recipe(root)
            execution = recipe["current_execution_inputs"]
            assert isinstance(execution, dict)
            execution["lean_import_closure_sha256"] = sha("different closure")
            runner = self._runner(root, FakeGit(), executor)
            with self.assertRaisesRegex(
                RUNNER.HistoricalStatementManifestRunnerError,
                "import-closure payload does not match",
            ):
                runner(recipe, [input_target])
            self.assertEqual(executions, [])


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
