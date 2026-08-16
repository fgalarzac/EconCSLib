#!/usr/bin/env python3
"""Tests for target-scoped operational closeout plan receipts."""

from __future__ import annotations

import copy
import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts.closeout_plan_receipt import (
    CloseoutPlanReceiptError,
    build_lean_closure_operational_projection,
    build_closeout_plan_receipt,
    closeout_plan_receipt_path,
    compiled_input_snapshot,
    content_input_snapshot,
    validated_closeout_plan_receipt,
)
from scripts.python_import_closure import repository_python_import_closure


def routing_v1(_root: Path, entry_module: str) -> tuple[object, str]:
    return {"schema": 1, "entry_module": entry_module, "srcDir": "papers"}, ""


def routing_v2(_root: Path, entry_module: str) -> tuple[object, str]:
    return {"schema": 2, "entry_module": entry_module, "srcDir": "papers"}, ""


class CloseoutPlanReceiptTests(unittest.TestCase):
    @staticmethod
    def _lean_closure_payload(root: Path) -> dict[str, object]:
        source = root / "papers" / "Fixture.lean"
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text("def fixture : Nat := 1\n", encoding="utf-8")
        controls = []
        for relative in (
            "lean-toolchain",
            "lake-manifest.json",
        ):
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(f"{relative}\n", encoding="utf-8")
            content = path.read_bytes()
            controls.append(
                {
                    "path": relative,
                    "tracked_in_index": True,
                    "untracked": False,
                    "path_kind": "file",
                    "byte_length": len(content),
                    "sha256": hashlib.sha256(content).hexdigest(),
                }
            )
        content = source.read_bytes()
        return {
            "schema": "econcslib.lean-loaded-import-closure/v2",
            "entrypoint": "papers/Fixture.lean",
            "entry_module": "Fixture",
            "lean_loaded_modules": ["Fixture", "Init"],
            "sources": [
                {
                    "module": "Fixture",
                    "path": "papers/Fixture.lean",
                    "byte_length": len(content),
                    "sha256": hashlib.sha256(content).hexdigest(),
                }
            ],
            "external_import_modules": ["Init"],
            "external_module_artifacts_sha256": "a" * 64,
            "build_controls": controls,
            "lake_routing": {
                "schema": "econcslib.entry-module-lake-routing/v2",
                "kind": "toml",
                "package_configuration": {"name": "FixturePackage"},
                "lean_library": {"name": "Fixture"},
            },
        }

    def _fixture(self, root: Path) -> tuple[Path, Path, Path]:
        folder = root / "papers" / "Fixture"
        folder.mkdir(parents=True)
        report = folder / "FINAL_VALIDATION_REPORT.md"
        source = folder / "MainTheorems.lean"
        artifact = root / ".lake" / "build" / "Fixture.olean"
        report.write_text("ready\n", encoding="utf-8")
        source.write_text("theorem ready : True := by trivial\n", encoding="utf-8")
        artifact.parent.mkdir(parents=True)
        artifact.write_bytes(b"olean")
        return report, source, artifact

    def test_receipt_ignores_ambient_files_but_rejects_material_change(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            report, source, artifact = self._fixture(root)
            audit_config = root / "papers" / "audit_config.json"
            audit_config.write_text(
                json.dumps({"schema": 1, "active_papers": ["Other"]}),
                encoding="utf-8",
            )
            receipt = build_closeout_plan_receipt(
                root,
                paper="Fixture",
                deep_paper_prose=False,
                content_paths=[report],
                stat_paths=[],
                source_ledger={str(source): list(source.stat())},
                compiled_ledger={str(artifact): list(artifact.stat())},
                routing_projection_loader=routing_v1,
            )
            identity = receipt["plan_identity_sha256"]
            unrelated = root / "EconCSLib" / "Unrelated.lean"
            unrelated.parent.mkdir()
            unrelated.write_text("def unrelated := 1\n", encoding="utf-8")
            audit_config.write_text(
                json.dumps({"schema": 1, "active_papers": ["Different"]}),
                encoding="utf-8",
            )
            validated_closeout_plan_receipt(
                root,
                receipt,
                paper="Fixture",
                deep_paper_prose=False,
                expected_plan_identity=identity,
                routing_projection_loader=routing_v1,
            )

            audit_config.write_text(
                json.dumps({"schema": 1, "active_papers": ["Fixture"]}),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                CloseoutPlanReceiptError, "target audit configuration"
            ):
                validated_closeout_plan_receipt(
                    root,
                    receipt,
                    paper="Fixture",
                    deep_paper_prose=False,
                    expected_plan_identity=identity,
                    routing_projection_loader=routing_v1,
                )

            audit_config.write_text(
                json.dumps({"schema": 1, "active_papers": ["Other"]}),
                encoding="utf-8",
            )
            report.write_text("changed\n", encoding="utf-8")
            with self.assertRaisesRegex(
                CloseoutPlanReceiptError, "content inputs changed"
            ):
                validated_closeout_plan_receipt(
                    root,
                    receipt,
                    paper="Fixture",
                    deep_paper_prose=False,
                    expected_plan_identity=identity,
                    routing_projection_loader=routing_v1,
                )

    def test_receipt_rejects_lean_ledger_and_target_routing_changes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            report, source, artifact = self._fixture(root)
            receipt = build_closeout_plan_receipt(
                root,
                paper="Fixture",
                deep_paper_prose=False,
                content_paths=[report],
                stat_paths=[],
                source_ledger={str(source): None},
                compiled_ledger={str(artifact): None},
                routing_projection_loader=routing_v1,
            )
            identity = receipt["plan_identity_sha256"]
            source.write_text("theorem changed : False := by contradiction\n")
            with self.assertRaisesRegex(
                CloseoutPlanReceiptError, "content inputs changed"
            ):
                validated_closeout_plan_receipt(
                    root,
                    receipt,
                    paper="Fixture",
                    deep_paper_prose=False,
                    expected_plan_identity=identity,
                    routing_projection_loader=routing_v1,
                )

            source.write_text("theorem ready : True := by trivial\n")
            refreshed = build_closeout_plan_receipt(
                root,
                paper="Fixture",
                deep_paper_prose=False,
                content_paths=[report],
                stat_paths=[],
                source_ledger={str(source): None},
                compiled_ledger={str(artifact): None},
                routing_projection_loader=routing_v1,
            )
            with self.assertRaisesRegex(CloseoutPlanReceiptError, "Lake routing"):
                validated_closeout_plan_receipt(
                    root,
                    refreshed,
                    paper="Fixture",
                    deep_paper_prose=False,
                    expected_plan_identity=refreshed["plan_identity_sha256"],
                    routing_projection_loader=routing_v2,
                )

    def test_same_byte_rewrite_is_neutral_but_symlink_retarget_is_not(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            report, source, artifact = self._fixture(root)
            logical = report.parent / "CURRENT_REPORT.md"
            alternate = report.parent / "ALTERNATE_REPORT.md"
            alternate.write_text("ready\n", encoding="utf-8")
            logical.symlink_to(report.name)
            receipt = build_closeout_plan_receipt(
                root,
                paper="Fixture",
                deep_paper_prose=False,
                content_paths=[logical],
                stat_paths=[],
                source_ledger={str(source): None},
                compiled_ledger={str(artifact): None},
                routing_projection_loader=routing_v1,
            )
            identity = receipt["plan_identity_sha256"]

            source.write_text(source.read_text(encoding="utf-8"), encoding="utf-8")
            validated_closeout_plan_receipt(
                root,
                receipt,
                paper="Fixture",
                deep_paper_prose=False,
                expected_plan_identity=identity,
                routing_projection_loader=routing_v1,
            )

            logical.unlink()
            logical.symlink_to(alternate.name)
            with self.assertRaisesRegex(
                CloseoutPlanReceiptError, "content inputs changed"
            ):
                validated_closeout_plan_receipt(
                    root,
                    receipt,
                    paper="Fixture",
                    deep_paper_prose=False,
                    expected_plan_identity=identity,
                    routing_projection_loader=routing_v1,
                )

    def test_compiled_rebuild_uses_bytes_not_stat_metadata_for_identity(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            report, source, artifact = self._fixture(root)
            first = build_closeout_plan_receipt(
                root,
                paper="Fixture",
                deep_paper_prose=False,
                content_paths=[report],
                stat_paths=[],
                source_ledger={str(source): None},
                compiled_ledger={str(artifact): None},
                routing_projection_loader=routing_v1,
            )
            artifact.write_bytes(b"olean")
            second = build_closeout_plan_receipt(
                root,
                paper="Fixture",
                deep_paper_prose=False,
                content_paths=[report],
                stat_paths=[],
                source_ledger={str(source): None},
                compiled_ledger={str(artifact): None},
                reusable_compiled_inputs=first["compiled_inputs"],
                routing_projection_loader=routing_v1,
            )

            self.assertEqual(
                first["plan_identity_sha256"], second["plan_identity_sha256"]
            )
            self.assertNotEqual(
                first["receipt_integrity_sha256"], second["receipt_integrity_sha256"]
            )
            validated_closeout_plan_receipt(
                root,
                first,
                paper="Fixture",
                deep_paper_prose=False,
                expected_plan_identity=first["plan_identity_sha256"],
                routing_projection_loader=routing_v1,
            )

            artifact.write_bytes(b"other")
            with self.assertRaisesRegex(
                CloseoutPlanReceiptError, "compiled inputs changed"
            ):
                validated_closeout_plan_receipt(
                    root,
                    first,
                    paper="Fixture",
                    deep_paper_prose=False,
                    expected_plan_identity=first["plan_identity_sha256"],
                    routing_projection_loader=routing_v1,
                )

    def test_compiled_snapshot_hashes_only_after_guard_change(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            _report, _source, artifact = self._fixture(root)
            first = compiled_input_snapshot(root, [artifact])

            with mock.patch.object(
                Path, "open", side_effect=AssertionError("unchanged guard reread bytes")
            ):
                self.assertEqual(
                    compiled_input_snapshot(root, [artifact], reusable=first), first
                )

            artifact.write_bytes(b"olean")
            original_open = Path.open
            reads: list[Path] = []

            def counting_open(path: Path, *args, **kwargs):
                reads.append(path)
                return original_open(path, *args, **kwargs)

            with mock.patch.object(Path, "open", new=counting_open):
                refreshed = compiled_input_snapshot(
                    root, [artifact], reusable=first
                )
            self.assertEqual(reads, [artifact])
            with mock.patch.object(
                Path, "open", side_effect=AssertionError("refreshed guard reread bytes")
            ):
                self.assertEqual(
                    compiled_input_snapshot(root, [artifact], reusable=refreshed),
                    refreshed,
                )

    def test_content_snapshot_hashes_only_the_changed_guard(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            report, source, _artifact = self._fixture(root)
            first = content_input_snapshot(root, [report, source])

            with mock.patch.object(
                Path, "open", side_effect=AssertionError("unchanged content reread")
            ):
                self.assertEqual(
                    content_input_snapshot(
                        root, [report, source], reusable=first
                    ),
                    first,
                )

            report.write_bytes(report.read_bytes())
            original_open = Path.open
            reads: list[Path] = []

            def counting_open(path: Path, *args, **kwargs):
                reads.append(path)
                return original_open(path, *args, **kwargs)

            with mock.patch.object(Path, "open", new=counting_open):
                refreshed = content_input_snapshot(
                    root, [report, source], reusable=first
                )
            self.assertEqual(reads, [report])
            with mock.patch.object(
                Path, "open", side_effect=AssertionError("refreshed content reread")
            ):
                self.assertEqual(
                    content_input_snapshot(
                        root, [report, source], reusable=refreshed
                    ),
                    refreshed,
                )

    def test_external_rebuild_uses_exact_aggregate_after_stat_change(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            report, source, artifact = self._fixture(root)
            payload = self._lean_closure_payload(root)

            def external_stat(generation: int):
                def load(
                    _root: Path, modules: tuple[str, ...]
                ) -> tuple[object, str]:
                    return {
                        "modules": [
                            {
                                "module": module,
                                "candidates": [
                                    {
                                        "absolute_path": f"/external/{module}.olean",
                                        "state": "present",
                                        "target_stat": [generation] * 5,
                                    }
                                ],
                            }
                            for module in modules
                        ]
                    }, ""

                return load

            projection = build_lean_closure_operational_projection(
                root, payload, external_projection_loader=external_stat(1)
            )
            first = build_closeout_plan_receipt(
                root,
                paper="Fixture",
                deep_paper_prose=False,
                content_paths=[report],
                stat_paths=[],
                source_ledger={str(source): None},
                compiled_ledger={str(artifact): None},
                lean_import_closure_projection=projection,
                lean_import_closure_projection_validated=True,
                routing_projection_loader=routing_v1,
            )
            second_projection = build_lean_closure_operational_projection(
                root, payload, external_projection_loader=external_stat(2)
            )
            second = build_closeout_plan_receipt(
                root,
                paper="Fixture",
                deep_paper_prose=False,
                content_paths=[report],
                stat_paths=[],
                source_ledger={str(source): None},
                compiled_ledger={str(artifact): None},
                lean_import_closure_projection=second_projection,
                lean_import_closure_projection_validated=True,
                routing_projection_loader=routing_v1,
            )
            self.assertEqual(
                first["plan_identity_sha256"], second["plan_identity_sha256"]
            )

            validated_closeout_plan_receipt(
                root,
                first,
                paper="Fixture",
                deep_paper_prose=False,
                expected_plan_identity=first["plan_identity_sha256"],
                routing_projection_loader=routing_v1,
                external_projection_loader=external_stat(2),
                external_content_identity_loader=lambda *_args: ("a" * 64, ""),
            )
            with self.assertRaisesRegex(
                CloseoutPlanReceiptError, "external artifact bytes changed"
            ):
                validated_closeout_plan_receipt(
                    root,
                    first,
                    paper="Fixture",
                    deep_paper_prose=False,
                    expected_plan_identity=first["plan_identity_sha256"],
                    routing_projection_loader=routing_v1,
                    external_projection_loader=external_stat(2),
                    external_content_identity_loader=lambda *_args: ("b" * 64, ""),
                )

    def test_new_target_lean_file_invalidates_inventory(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            report, source, artifact = self._fixture(root)
            receipt = build_closeout_plan_receipt(
                root,
                paper="Fixture",
                deep_paper_prose=False,
                content_paths=[report],
                stat_paths=[],
                source_ledger={str(source): None},
                compiled_ledger={str(artifact): None},
                routing_projection_loader=routing_v1,
            )
            (report.parent / "Scratch.lean").write_text(
                "theorem scratch : True := by trivial\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(
                CloseoutPlanReceiptError, "Lean-file inventory"
            ):
                validated_closeout_plan_receipt(
                    root,
                    receipt,
                    paper="Fixture",
                    deep_paper_prose=False,
                    expected_plan_identity=receipt["plan_identity_sha256"],
                    routing_projection_loader=routing_v1,
                )

    def test_lean_graph_projection_rejects_new_ownership_and_artifact_change(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            report, source, artifact = self._fixture(root)
            payload = self._lean_closure_payload(root)
            external_v1_calls = 0

            def external_v1(
                _root: Path, modules: tuple[str, ...]
            ) -> tuple[object, str]:
                nonlocal external_v1_calls
                external_v1_calls += 1
                return {"modules": list(modules), "stat_generation": 1}, ""

            def external_v2(
                _root: Path, modules: tuple[str, ...]
            ) -> tuple[object, str]:
                return {"modules": list(modules), "stat_generation": 2}, ""

            projection = build_lean_closure_operational_projection(
                root,
                payload,
                external_projection_loader=external_v1,
            )
            wrong_root = copy.deepcopy(projection)
            wrong_root["lean_import_closure"]["entry_module"] = "Other"
            wrong_root["lean_import_closure"]["entrypoint"] = "papers/Other.lean"
            with self.assertRaisesRegex(
                CloseoutPlanReceiptError, "selected paper target"
            ):
                build_closeout_plan_receipt(
                    root,
                    paper="Fixture",
                    deep_paper_prose=False,
                    content_paths=[report],
                    stat_paths=[],
                    source_ledger={str(source): None},
                    compiled_ledger={str(artifact): None},
                    lean_import_closure_projection=wrong_root,
                    lean_import_closure_projection_validated=True,
                    routing_projection_loader=routing_v1,
                    external_projection_loader=external_v1,
                )
            receipt = build_closeout_plan_receipt(
                root,
                paper="Fixture",
                deep_paper_prose=False,
                content_paths=[report],
                stat_paths=[],
                source_ledger={str(source): None},
                compiled_ledger={str(artifact): None},
                lean_import_closure_projection=projection,
                lean_import_closure_projection_validated=True,
                routing_projection_loader=routing_v1,
                external_projection_loader=external_v1,
            )
            self.assertEqual(external_v1_calls, 1)
            identity = receipt["plan_identity_sha256"]
            validated_closeout_plan_receipt(
                root,
                receipt,
                paper="Fixture",
                deep_paper_prose=False,
                expected_plan_identity=identity,
                routing_projection_loader=routing_v1,
                external_projection_loader=external_v1,
            )
            self.assertEqual(external_v1_calls, 2)

            (root / "Init.lean").write_text("def initShadow := 1\n", encoding="utf-8")
            with self.assertRaisesRegex(
                CloseoutPlanReceiptError, "gained repository source ownership"
            ):
                validated_closeout_plan_receipt(
                    root,
                    receipt,
                    paper="Fixture",
                    deep_paper_prose=False,
                    expected_plan_identity=identity,
                    routing_projection_loader=routing_v1,
                    external_projection_loader=external_v1,
                )
            (root / "Init.lean").unlink()
            (root / "Init.lean").write_text("def initShadow := 1\n", encoding="utf-8")
            (root / "papers").mkdir(exist_ok=True)
            (root / "papers" / "Init.lean").write_text(
                "def secondInitShadow := 1\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(
                CloseoutPlanReceiptError, "ambiguous repository source ownership"
            ):
                validated_closeout_plan_receipt(
                    root,
                    receipt,
                    paper="Fixture",
                    deep_paper_prose=False,
                    expected_plan_identity=identity,
                    routing_projection_loader=routing_v1,
                    external_projection_loader=external_v1,
                )
            (root / "Init.lean").unlink()
            (root / "papers" / "Init.lean").unlink()
            with self.assertRaisesRegex(
                CloseoutPlanReceiptError, "external artifacts changed"
            ):
                validated_closeout_plan_receipt(
                    root,
                    receipt,
                    paper="Fixture",
                    deep_paper_prose=False,
                    expected_plan_identity=identity,
                    routing_projection_loader=routing_v1,
                    external_projection_loader=external_v2,
                )

    def test_legacy_graph_helper_control_is_not_a_plan_input(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            report, source, artifact = self._fixture(root)
            payload = self._lean_closure_payload(root)
            helper = root / "scripts" / "lean_import_graph_helper.lean"
            helper.parent.mkdir(parents=True)
            helper.write_text("-- legacy reporter\n", encoding="utf-8")
            helper_content = helper.read_bytes()
            payload["build_controls"].append(
                {
                    "path": "scripts/lean_import_graph_helper.lean",
                    "tracked_in_index": True,
                    "untracked": False,
                    "path_kind": "file",
                    "byte_length": len(helper_content),
                    "sha256": hashlib.sha256(helper_content).hexdigest(),
                }
            )

            def external(
                _root: Path, modules: tuple[str, ...]
            ) -> tuple[object, str]:
                return {"modules": list(modules)}, ""

            projection = build_lean_closure_operational_projection(
                root,
                payload,
                external_projection_loader=external,
            )
            helper.write_text("-- refactored reporter\n", encoding="utf-8")
            receipt = build_closeout_plan_receipt(
                root,
                paper="Fixture",
                deep_paper_prose=False,
                content_paths=[report],
                stat_paths=[],
                source_ledger={str(source): None},
                compiled_ledger={str(artifact): None},
                lean_import_closure_projection=projection,
                lean_import_closure_projection_validated=True,
                routing_projection_loader=routing_v1,
                external_projection_loader=external,
            )

            self.assertNotIn(
                "scripts/lean_import_graph_helper.lean", receipt["content_inputs"]
            )
            validated_closeout_plan_receipt(
                root,
                receipt,
                paper="Fixture",
                deep_paper_prose=False,
                expected_plan_identity=receipt["plan_identity_sha256"],
                routing_projection_loader=routing_v1,
                external_projection_loader=external,
            )

    def test_identity_addressed_receipts_do_not_share_a_path(self) -> None:
        root = Path("/tmp/fixture-root")
        first = closeout_plan_receipt_path(root, "Fixture", "a" * 64)
        second = closeout_plan_receipt_path(root, "Fixture", "b" * 64)
        self.assertNotEqual(first, second)

    def test_protocol_prose_is_neutral_but_compatibility_version_is_not(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            report, source, artifact = self._fixture(root)
            protocol = root / "config" / "formalization_audit_protocol.json"
            protocol.parent.mkdir()
            repository_root = Path(__file__).resolve().parents[2]
            base = json.loads(
                (
                    repository_root / "config" / "formalization_audit_protocol.json"
                ).read_text(encoding="utf-8")
            )
            base["description"] = "first wording"
            protocol.write_text(json.dumps(base), encoding="utf-8")
            receipt = build_closeout_plan_receipt(
                root,
                paper="Fixture",
                deep_paper_prose=False,
                content_paths=[report],
                stat_paths=[],
                source_ledger={str(source): None},
                compiled_ledger={str(artifact): None},
                routing_projection_loader=routing_v1,
            )
            identity = receipt["plan_identity_sha256"]
            protocol.write_text(
                json.dumps({**base, "description": "reworded only"}), encoding="utf-8"
            )
            validated_closeout_plan_receipt(
                root,
                receipt,
                paper="Fixture",
                deep_paper_prose=False,
                expected_plan_identity=identity,
                routing_projection_loader=routing_v1,
            )
            changed = copy.deepcopy(base)
            changed["coverage"]["deep_mode"]["id"] = (
                "deep_paper_with_all_prose_claims_v2"
            )
            protocol.write_text(json.dumps(changed), encoding="utf-8")
            with self.assertRaisesRegex(
                CloseoutPlanReceiptError, "protocol compatibility"
            ):
                validated_closeout_plan_receipt(
                    root,
                    receipt,
                    paper="Fixture",
                    deep_paper_prose=False,
                    expected_plan_identity=identity,
                    routing_projection_loader=routing_v1,
                )

    def test_local_python_import_closure_is_transitive_and_scoped(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            scripts = root / "scripts"
            scripts.mkdir()
            package_init = scripts / "__init__.py"
            entry = scripts / "entry.py"
            direct = scripts / "direct.py"
            transitive = scripts / "transitive.py"
            unrelated = scripts / "unrelated.py"
            package_init.write_text("PACKAGE_VALUE = 0\n", encoding="utf-8")
            entry.write_text("from scripts import direct\n", encoding="utf-8")
            direct.write_text("import transitive\n", encoding="utf-8")
            transitive.write_text("VALUE = 1\n", encoding="utf-8")
            unrelated.write_text("VALUE = 2\n", encoding="utf-8")
            closure = repository_python_import_closure(root, [entry])
            self.assertEqual(set(closure), {package_init, entry, direct, transitive})

    def test_package_initializer_relative_import_is_included(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            package = root / "scripts" / "pkg"
            package.mkdir(parents=True)
            (root / "scripts" / "__init__.py").write_text("", encoding="utf-8")
            package_init = package / "__init__.py"
            dependency = package / "dependency.py"
            package_init.write_text("from . import dependency\n", encoding="utf-8")
            dependency.write_text("VALUE = 1\n", encoding="utf-8")
            self.assertEqual(
                set(repository_python_import_closure(root, [package_init])),
                {root / "scripts" / "__init__.py", package_init, dependency},
            )


if __name__ == "__main__":
    unittest.main()
