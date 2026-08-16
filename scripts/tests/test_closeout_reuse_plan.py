#!/usr/bin/env python3
"""Tests for the advisory, fail-closed paper closeout reuse planner."""

from __future__ import annotations

import contextlib
import hashlib
import io
import json
import os
import sys
import tempfile
import types
import unittest
from pathlib import Path
from unittest import mock

from scripts import closeout_reuse_plan as planner


class CloseoutReusePlanTests(unittest.TestCase):
    @staticmethod
    def wave_snapshot() -> dict[str, object]:
        return {
            "wave_id": "fixture-wave",
            "engine_registration": {
                "engine_tree_sha256": "a" * 64,
                "review_semantic_class_sha256": "b" * 64,
                "revision_sequence": 1,
                "relation_to_previous": "initial",
                "engine_file_count": 1,
            },
        }

    def semantic_contract_replay_fixture(
        self, root: Path, *, match_digest: str
    ) -> tuple[Path, types.SimpleNamespace]:
        """Create a canonical raw with a replayable producer diagnostic."""

        folder = root / "papers" / "Fixture"
        audit = folder / "audit"
        audit.mkdir(parents=True)
        (folder / "status.json").write_text("{}\n", encoding="utf-8")
        (audit / "paper_statement_map.json").write_text("{}\n", encoding="utf-8")
        (audit / "source_record_audit.json").write_text(
            json.dumps(
                {
                    "source_record_audit_sha256": "a" * 64,
                    "source_record_input_fingerprint": {"schema": 10},
                    "source_contract_association_errors": [
                        "structural replay candidate"
                    ],
                }
            ),
            encoding="utf-8",
        )
        (audit / "source_record_match_llm.json").write_text(
            json.dumps({"source_record_audit_sha256": match_digest}),
            encoding="utf-8",
        )
        # The gate context below authenticates its content. The planner only
        # considers this exceptional branch when the canonical artifact exists.
        (audit / "source_record_semantic_contract_revalidation.json").write_text(
            "{}\n", encoding="utf-8"
        )
        return (
            folder,
            types.SimpleNamespace(
                returncode=1,
                stdout=json.dumps(
                    {
                        "current": False,
                        "reason": "generated source-contract association diagnostics are nonempty",
                        "observed_source_record_audit_sha256": "a" * 64,
                        "observed_source_record_fingerprint_schema": 10,
                    }
                ),
                stderr="",
            ),
        )

    def signature_context(self, *, schema: int = 2) -> dict[str, object]:
        target = ("a" * 64, 10)
        helper = ("b" * 64, 20)
        modules = ("Fixture.Dependency", "Fixture.PaperInterface")
        context: dict[str, object] = {
            "schema": schema,
            "import_module": "Fixture.PaperInterface",
            "olean_fingerprint": list(target),
            "helper_fingerprint": list(helper),
            "audit_modules": list(modules),
            "semantic_module_fingerprints": [
                ["Fixture.Dependency", ["c" * 64, 30]],
                ["Fixture.PaperInterface", list(target)],
            ],
            "audit_scope_fingerprint": planner.lean_manifest._audit_scope_fingerprint(  # noqa: SLF001
                "Fixture.PaperInterface", target, modules
            ),
        }
        if schema == 3:
            context.update(
                {
                    "canonical_representation": "lean_compact_canonical_v2",
                    "semantic_hash_tool_identity": {
                        "schema": "1",
                        "resolved_path": "/usr/bin/sha256sum",
                        "executable_sha256": "d" * 64,
                    },
                }
            )
        return context

    def test_signature_context_checks_complete_exact_artifact_closure(self) -> None:
        context = self.signature_context()
        with (
            mock.patch.object(
                planner.lean_manifest,
                "_file_content_fingerprint",
                return_value=("b" * 64, 20),
            ),
            mock.patch.object(
                planner.lean_manifest,
                "_built_olean_fingerprint",
                side_effect=lambda _root, module: {
                    "Fixture.Dependency": ("c" * 64, 30),
                    "Fixture.PaperInterface": ("a" * 64, 10),
                }[module],
            ),
        ):
            digest, errors = planner._signature_context_snapshot(
                Path("/fixture"), {"PaperInterface.lean": context}
            )
        self.assertRegex(digest, r"^[0-9a-f]{64}$")
        self.assertEqual(errors, [])

        with (
            mock.patch.object(
                planner.lean_manifest,
                "_file_content_fingerprint",
                return_value=("b" * 64, 20),
            ),
            mock.patch.object(
                planner.lean_manifest,
                "_built_olean_fingerprint",
                side_effect=lambda _root, module: (
                    ("d" * 64, 30) if module == "Fixture.Dependency" else ("a" * 64, 10)
                ),
            ),
        ):
            digest, errors = planner._signature_context_snapshot(
                Path("/fixture"), {"PaperInterface.lean": context}
            )
        self.assertEqual(digest, "")
        self.assertIn("Fixture.Dependency", errors[0])

    def test_signature_context_schema_three_revalidates_hash_tool_and_format(
        self,
    ) -> None:
        context = self.signature_context(schema=3)
        hash_tool_identity = dict(context["semantic_hash_tool_identity"])
        with (
            mock.patch.object(
                planner.lean_manifest,
                "_semantic_contract_closure_hash_tool_identity",
                return_value=hash_tool_identity,
            ),
            mock.patch.object(
                planner.lean_manifest,
                "_file_content_fingerprint",
                return_value=("b" * 64, 20),
            ),
            mock.patch.object(
                planner.lean_manifest,
                "_built_olean_fingerprint",
                side_effect=lambda _root, module: {
                    "Fixture.Dependency": ("c" * 64, 30),
                    "Fixture.PaperInterface": ("a" * 64, 10),
                }[module],
            ),
        ):
            digest, errors = planner._signature_context_snapshot(
                Path("/fixture"), {"PaperInterface.lean": context}
            )
        self.assertRegex(digest, r"^[0-9a-f]{64}$")
        self.assertEqual(errors, [])

        stale_tool = dict(context)
        stale_tool["semantic_hash_tool_identity"] = {
            **hash_tool_identity,
            "executable_sha256": "e" * 64,
        }
        with mock.patch.object(
            planner.lean_manifest,
            "_semantic_contract_closure_hash_tool_identity",
            return_value=hash_tool_identity,
        ):
            digest, errors = planner._signature_context_snapshot(
                Path("/fixture"), {"PaperInterface.lean": stale_tool}
            )
        self.assertEqual(digest, "")
        self.assertIn("SHA-256 tool identity changed", errors[0])

        stale_format = dict(context)
        stale_format["canonical_representation"] = "lean_compact_canonical_v1"
        digest, errors = planner._signature_context_snapshot(
            Path("/fixture"), {"PaperInterface.lean": stale_format}
        )
        self.assertEqual(digest, "")
        self.assertIn("canonical representation", errors[0])

    def test_operational_compiled_ledger_partitions_only_declared_tool_guard(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir) / "repository"
            root.mkdir()
            compiled = root / "Artifact.olean"
            compiled.write_bytes(b"olean")
            tool = Path(temp_dir) / "sha256sum"
            tool.write_bytes(b"tool")
            stat = compiled.stat()
            identity = (
                stat.st_dev,
                stat.st_ino,
                stat.st_size,
                stat.st_mtime_ns,
                stat.st_ctime_ns,
            )
            contexts = self.signature_context(schema=3)
            contexts["semantic_hash_tool_identity"] = {
                "schema": "1",
                "resolved_path": str(tool),
                "executable_sha256": "d" * 64,
            }
            repository, external, error = planner._partition_operational_compiled_ledger(
                root,
                {str(compiled): identity, str(tool): identity},
                signature_contexts={"PaperInterface.lean": contexts},
            )

            self.assertEqual(error, "")
            self.assertEqual(set(repository), {str(compiled.resolve())})
            self.assertEqual(set(external), {str(tool.resolve())})

            _repository, _external, error = (
                planner._partition_operational_compiled_ledger(
                    root,
                    {str(Path(temp_dir) / "undeclared"): identity},
                    signature_contexts={"PaperInterface.lean": contexts},
                )
            )
            self.assertIn("undeclared external path", error)

            _repository, _external, error = (
                planner._partition_operational_compiled_ledger(
                    root,
                    {str(root / "nested" / ".." / "Artifact.olean"): identity},
                    signature_contexts={"PaperInterface.lean": contexts},
                )
            )
            self.assertIn("noncanonical path key", error)

    def test_signature_context_hashes_shared_artifacts_once(self) -> None:
        context = self.signature_context()
        with (
            mock.patch.object(
                planner.lean_manifest,
                "_file_content_fingerprint",
                return_value=("b" * 64, 20),
            ) as helper_hash,
            mock.patch.object(
                planner.lean_manifest,
                "_built_olean_fingerprint",
                side_effect=lambda _root, module: {
                    "Fixture.Dependency": ("c" * 64, 30),
                    "Fixture.PaperInterface": ("a" * 64, 10),
                }[module],
            ) as module_hash,
        ):
            digest, errors = planner._signature_context_snapshot(
                Path("/fixture"),
                {"first": context, "second": dict(context)},
            )
        self.assertRegex(digest, r"^[0-9a-f]{64}$")
        self.assertEqual(errors, [])
        self.assertEqual(helper_hash.call_count, 1)
        self.assertEqual(module_hash.call_count, 2)

    def test_cached_snapshot_is_read_only_and_mutation_guarded(self) -> None:
        context = self.signature_context()
        payload = {
            "schema": 20,
            "paper": "Fixture",
            "signature_contexts": {"PaperInterface.lean": context},
        }
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            cache = folder / "paper_interface_cache.json"
            cache.write_text(json.dumps(payload), encoding="utf-8")
            before = cache.read_bytes()
            with (
                mock.patch.object(
                    planner.review_dashboard,
                    "paper_interface_cache_file",
                    return_value=cache,
                ),
                mock.patch.object(
                    planner.review_dashboard,
                    "_cache_source_hashes",
                    return_value={"material": "a"},
                ) as source_hashes,
                mock.patch.object(
                    planner.review_dashboard,
                    "load_cached_review_rows",
                    return_value=[object()],
                ) as load_rows,
                mock.patch.object(
                    planner,
                    "_signature_context_snapshot",
                    return_value=("f" * 64, []),
                ),
                mock.patch.object(
                    planner,
                    "_root_import_closure_mutation_snapshots",
                    return_value=({}, {}, [], {"schema": "fixture"}),
                ),
                mock.patch.object(
                    planner,
                    "build_lean_closure_operational_projection",
                    return_value={"state": "present"},
                ),
            ):
                snapshot, errors = planner.cached_review_snapshot(
                    folder, verify_compiled_content=True
                )

            self.assertIsNotNone(snapshot)
            self.assertEqual(errors, [])
            self.assertEqual(cache.read_bytes(), before)
            self.assertEqual(source_hashes.call_count, 1)
            self.assertFalse(load_rows.call_args.kwargs["persist_rebind"])

            assert snapshot is not None
            snapshot.compiled_artifact_mutation_snapshot["artifact"] = (
                1,
                2,
                3,
                4,
                5,
            )
            errors = planner.cached_snapshot_invalidation_reasons(folder, snapshot)
            self.assertIn("compiled Lean material changed", errors[0])

    def test_cache_guard_skips_reread_when_dashboard_stat_is_unchanged(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            cache = folder / "paper_interface_cache.json"
            cache.write_bytes(b'{"cached": true}')
            snapshot = planner.CachedReviewSnapshot(
                rows=[],
                source_material_sha256="a" * 64,
                compiled_material_sha256="b" * 64,
                compiled_artifacts_ready=True,
                compiled_validation_mode="metadata_preflight",
                compiled_invalidation_reasons=(),
                source_hashes={},
                signature_contexts={},
                source_artifact_mutation_snapshot={},
                compiled_artifact_mutation_snapshot={},
                lean_import_closure_projection={"state": "present"},
                cache_path=cache,
                cache_mutation_snapshot=planner._stat_identity(cache.stat()),
                cache_sha256=hashlib.sha256(cache.read_bytes()).hexdigest(),
            )
            with mock.patch.object(
                Path,
                "read_bytes",
                side_effect=AssertionError("unchanged dashboard cache was reread"),
            ):
                errors = planner.cached_snapshot_invalidation_reasons(folder, snapshot)

        self.assertEqual(errors, [])

    def test_cache_guard_rehashes_when_dashboard_stat_changes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "Fixture"
            folder.mkdir()
            cache = folder / "paper_interface_cache.json"
            cache.write_bytes(b'{"cached": true}')
            snapshot = planner.CachedReviewSnapshot(
                rows=[],
                source_material_sha256="a" * 64,
                compiled_material_sha256="b" * 64,
                compiled_artifacts_ready=True,
                compiled_validation_mode="metadata_preflight",
                compiled_invalidation_reasons=(),
                source_hashes={},
                signature_contexts={},
                source_artifact_mutation_snapshot={},
                compiled_artifact_mutation_snapshot={},
                lean_import_closure_projection={"state": "present"},
                cache_path=cache,
                cache_mutation_snapshot=planner._stat_identity(cache.stat()),
                cache_sha256=hashlib.sha256(cache.read_bytes()).hexdigest(),
            )
            cache.write_bytes(b'{"cached": false}')
            errors = planner.cached_snapshot_invalidation_reasons(folder, snapshot)

        self.assertEqual(errors, ["dashboard cache changed during planning"])

    def test_advisory_graph_loader_never_requests_a_build(self) -> None:
        with mock.patch.object(
            planner,
            "lean_loaded_module_closure",
            return_value=(("Fixture",), ""),
        ) as graph:
            modules, error = planner._advisory_lean_graph_loader(
                Path("/fixture"), "Fixture", 19
            )

        self.assertEqual(modules, ("Fixture",))
        self.assertEqual(error, "")
        graph.assert_called_once_with(
            Path("/fixture"),
            "Fixture",
            19,
            build_entry_module=False,
        )

    def test_item_plan_reports_missing_and_malformed_decisions(self) -> None:
        plan = planner._item_plan(
            {
                "reusable": {"judgment": "matches"},
                "rejected": {"judgment": "matches"},
                "malformed": None,
            },
            {
                "reusable": {"accepted": True, "current_row": "renamed"},
                "rejected": {"accepted": False, "reason": "ambiguous identity"},
            },
            reusable_action="reuse",
            invalid_action="review",
        )

        self.assertTrue(plan["reusable"]["reusable"])
        self.assertEqual(plan["reusable"]["current_row"], "renamed")
        self.assertFalse(plan["rejected"]["reusable"])
        self.assertIn("ambiguous", plan["rejected"]["reason"])
        self.assertFalse(plan["malformed"]["reusable"])
        self.assertIn("not an object", plan["malformed"]["reason"])

    def test_compact_output_keeps_only_repair_obligations(self) -> None:
        compact = planner.compact_plan_for_output(
            {
                "statement": {
                    "ready": {"reusable": True},
                    "repair": {"reusable": False, "reason": "changed"},
                },
                "coverage": {"ready": {"reusable": True}},
                "summary": {"statement_requires_review": 1},
            },
            "Fixture",
        )

        self.assertEqual(
            compact["statement"], {"repair": {"reusable": False, "reason": "changed"}}
        )
        self.assertEqual(compact["coverage"], {})
        self.assertEqual(
            compact["reusable_items_omitted_from_output"],
            {"statement": 1, "coverage": 1},
        )
        self.assertIn("--all-items", compact["full_item_plan_command"])

    def test_item_plan_exposes_new_and_retired_obligations(self) -> None:
        plan = planner._item_plan(
            {
                "unchanged": {"judgment": "matches"},
                "removed": {"judgment": "matches"},
            },
            {
                "unchanged": {
                    "accepted": True,
                    "current_row": "renamed-current",
                },
                "removed": {
                    "accepted": False,
                    "reason": "no current semantic candidate",
                },
            },
            reusable_action="reuse",
            invalid_action="fresh",
            current_keys={"renamed-current", "brand-new"},
            current_navigation_field="current_row",
        )

        self.assertTrue(plan["unchanged"]["reusable"])
        self.assertTrue(plan["removed"]["retirement_candidate"])
        self.assertEqual(
            plan["removed"]["action"],
            "retire_or_rebind_obsolete_review_item",
        )
        self.assertTrue(plan["brand-new"]["new_current_obligation"])
        self.assertEqual(plan["brand-new"]["action"], "fresh")

    def test_item_plan_keeps_unsealed_current_review_closeout_reusable(self) -> None:
        plan = planner._item_plan(
            {"legacy-key": {"judgment": "matches"}},
            {
                "legacy-key": {
                    "accepted": True,
                    "current_row": "current-row",
                    "bootstrap_current": True,
                }
            },
            reusable_action="reuse",
            invalid_action="fresh",
            current_keys={"current-row"},
            current_navigation_field="current_row",
        )

        self.assertTrue(plan["legacy-key"]["reusable"])
        self.assertTrue(plan["legacy-key"]["future_reuse_pin_missing"])
        self.assertEqual(plan["legacy-key"]["action"], "reuse")

    def test_cache_miss_schedules_manifest_without_erasing_human_review(self) -> None:
        schedule = planner.closeout_action_schedule(
            "Fixture",
            cache_reusable=False,
        )

        self.assertFalse(schedule["semantic_review_reuse_ready"])
        self.assertEqual(
            [action["id"] for action in schedule["actions"]],
            ["paper_build", "fresh_manifest_batch", "replan_after_manifest"],
        )
        self.assertEqual(
            schedule["actions"][1]["argv"],
            [
                "python3",
                "scripts/refresh_closeout_manifest_cache.py",
                "--paper",
                "Fixture",
            ],
        )
        self.assertIn(
            "exact roots reuse the raw batch", schedule["actions"][1]["reason"]
        )
        self.assertEqual(schedule["next_action"]["id"], "paper_build")
        self.assertEqual(schedule["actions"][1]["state"], "after_paper_build")

    def test_cache_miss_main_path_emits_executable_dependency_chain(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            paths = [
                audit / "statement_match_llm.json",
                audit / "paper_coverage_llm.json",
                audit / "paper_statement_map.json",
                audit / "source_proof_fidelity.json",
            ]
            payloads = {path: {} for path in paths}
            material = {
                str(path): {"state": "present", "sha256": "a" * 64} for path in paths
            }
            output = io.StringIO()
            with (
                mock.patch.object(
                    sys, "argv", ["closeout_reuse_plan.py", "--paper", "Fixture"]
                ),
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "resolve_paper_folder", return_value=folder),
                mock.patch.object(
                    planner, "running_execution_summary", return_value=None
                ),
                mock.patch.object(
                    planner, "runtime_engine_registration_error", return_value=""
                ),
                mock.patch.object(
                    planner,
                    "static_closeout_readiness",
                    return_value={"ready": True, "blockers": []},
                ) as readiness,
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("formalized", ""),
                ),
                mock.patch.object(
                    planner,
                    "fast_saved_source_record_preflight",
                    return_value={"state": "current_raw_judgment_bound"},
                ),
                mock.patch.object(
                    planner,
                    "_captured_json_payloads",
                    return_value=(payloads, material, []),
                ),
                mock.patch.object(
                    planner,
                    "source_coverage_mode_from_map",
                    return_value=("named_theoretical_statements", ""),
                ),
                mock.patch.object(
                    planner, "inventory_from_source_map", return_value={}
                ),
                mock.patch.object(
                    planner,
                    "canonical_coverage_inventory_projection",
                    return_value=({}, ""),
                ),
                mock.patch.object(
                    planner,
                    "_advisory_plan_input_identity",
                    return_value=("b" * 64, {}),
                ),
                mock.patch.object(
                    planner, "_read_advisory_plan_cache", return_value=None
                ),
                mock.patch.object(
                    planner,
                    "cached_review_snapshot",
                    return_value=(None, ["dashboard cache is unavailable"]),
                ),
                contextlib.redirect_stdout(output),
            ):
                result = planner.main()
            self.assertEqual(result, 0)
            emitted = json.loads(output.getvalue())
            self.assertEqual(emitted["next_action"]["id"], "paper_build")
            self.assertEqual(
                [action["id"] for action in emitted["actions"]],
                ["paper_build", "fresh_manifest_batch", "replan_after_manifest"],
            )
            readiness.assert_called_once_with(folder)

    def test_invalid_fresh_semantic_plan_stops_before_strict_snapshot_or_receipt(
        self,
    ) -> None:
        """An unresolved item is a worklist, not a strict-closeout candidate."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            paths = [
                audit / "statement_match_llm.json",
                audit / "paper_coverage_llm.json",
                audit / "paper_statement_map.json",
                audit / "source_proof_fidelity.json",
            ]
            payloads = {path: {} for path in paths}
            material = {
                str(path): {"state": "present", "sha256": "a" * 64}
                for path in paths
            }
            cached = planner.CachedReviewSnapshot(
                rows=[],
                source_material_sha256="a" * 64,
                compiled_material_sha256="b" * 64,
                compiled_artifacts_ready=True,
                compiled_validation_mode="metadata_preflight",
                compiled_invalidation_reasons=(),
                source_hashes={},
                signature_contexts={},
                source_artifact_mutation_snapshot={},
                compiled_artifact_mutation_snapshot={},
                lean_import_closure_projection={"state": "present"},
                cache_path=root / "dashboard.json",
                cache_mutation_snapshot=(1, 2, 3, 4, 5),
                cache_sha256="c" * 64,
            )
            semantic_plan = {
                "acceptance_credential": False,
                "requires_fresh_strict_closeout": True,
                "statement": {
                    "source-result": {
                        "reusable": False,
                        "action": "fresh_human_semantic_review",
                    }
                },
                "coverage": {},
                "summary": {
                    "statement_requires_review": 1,
                    "coverage_requires_review": 0,
                },
                "validator_identity_errors": {"statement": [], "coverage": []},
            }
            output = io.StringIO()
            with contextlib.ExitStack() as stack:
                stack.enter_context(
                    mock.patch.object(
                        sys,
                        "argv",
                        ["closeout_reuse_plan.py", "--paper", "Fixture"],
                    )
                )
                stack.enter_context(mock.patch.object(planner, "ROOT", root))
                stack.enter_context(
                    mock.patch.object(
                        planner, "resolve_paper_folder", return_value=folder
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        planner, "running_execution_summary", return_value=None
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        planner,
                        "effective_closeout_execution_state",
                        return_value=(None, "", "worker", folder / "state.json"),
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        planner, "runtime_engine_registration_error", return_value=""
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        planner,
                        "static_closeout_readiness",
                        return_value={"ready": True, "blockers": []},
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        planner,
                        "_paper_closeout_status_preflight",
                        return_value=("formalized", ""),
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        planner,
                        "fast_saved_source_record_preflight",
                        return_value={"state": "current_raw_judgment_bound"},
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        planner,
                        "_captured_json_payloads",
                        return_value=(payloads, material, []),
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        planner,
                        "source_coverage_mode_from_map",
                        return_value=("named_theoretical_statements", ""),
                    )
                )
                stack.enter_context(
                    mock.patch.object(planner, "inventory_from_source_map", return_value={})
                )
                stack.enter_context(
                    mock.patch.object(
                        planner,
                        "canonical_coverage_inventory_projection",
                        return_value=({}, ""),
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        planner,
                        "_advisory_plan_input_identity",
                        return_value=("d" * 64, {"_mutation_snapshot": {}}),
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        planner, "_read_advisory_plan_cache", return_value=None
                    )
                )
                stack.enter_context(
                    mock.patch.object(planner, "cached_review_snapshot", return_value=(cached, []))
                )
                stack.enter_context(
                    mock.patch.object(
                        planner.review_dashboard,
                        "paper_source_component_route_inventory",
                        return_value={},
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        planner.review_dashboard,
                        "paper_source_definition_component_route_inventory",
                        return_value={},
                    )
                )
                stack.enter_context(
                    mock.patch.object(planner, "_current_anchor_errors", return_value={})
                )
                stack.enter_context(
                    mock.patch.object(planner, "row_snapshots_from_dashboard", return_value=[])
                )
                stack.enter_context(
                    mock.patch.object(
                        planner, "_direct_expression_review_required", return_value=False
                    )
                )
                stack.enter_context(
                    mock.patch.object(planner, "semantic_reuse_plan", return_value=semantic_plan)
                )
                stack.enter_context(
                    mock.patch.object(
                        planner, "cached_snapshot_invalidation_reasons", return_value=[]
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        planner, "_file_material_snapshot", return_value=material
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        planner.review_dashboard,
                        "review_surface_digest",
                        return_value="e" * 64,
                    )
                )
                stack.enter_context(
                    mock.patch.object(
                        planner, "_advisory_input_material_is_current", return_value=True
                    )
                )
                strict_snapshot = stack.enter_context(
                    mock.patch.object(planner, "_strict_transaction_content_snapshot")
                )
                write_cache = stack.enter_context(
                    mock.patch.object(planner, "_write_advisory_plan_cache")
                )
                write_receipt = stack.enter_context(
                    mock.patch.object(planner, "_write_current_closeout_plan_receipt")
                )
                stack.enter_context(contextlib.redirect_stdout(output))
                result = planner.main()

            self.assertEqual(result, 0)
            emitted = json.loads(output.getvalue())
            self.assertEqual(emitted["next_action"]["id"], "inspect_invalid_semantic_items")
            strict_snapshot.assert_not_called()
            write_cache.assert_not_called()
            write_receipt.assert_not_called()

    def test_semantic_ready_compiled_miss_stops_before_operational_receipt(
        self,
    ) -> None:
        """A build/replan transition cannot use a pre-build strict receipt."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            plan = {
                "acceptance_credential": False,
                "requires_fresh_strict_closeout": True,
                "cache_reusable": True,
                "compiled_artifacts_ready": False,
                "summary": {
                    "statement_requires_review": 0,
                    "coverage_requires_review": 0,
                },
                "validator_identity_errors": {"statement": [], "coverage": []},
            }
            with mock.patch.object(
                planner,
                "_write_current_closeout_plan_receipt",
                side_effect=AssertionError("a pre-build receipt must not be published"),
            ) as write_receipt:
                finalized = planner.finalize_operational_plan(
                    plan,
                    folder=folder,
                    source_coverage_mode="named_theoretical_statements",
                    execution_path=folder / ".review_traces" / "worker.json",
                    static_readiness={"ready": True, "blockers": []},
                )

            self.assertEqual(finalized["next_action"]["id"], "paper_build")
            self.assertEqual(
                [action["id"] for action in finalized["actions"]],
                ["paper_build", "replan_after_build"],
            )
            self.assertNotIn("plan_identity_sha256", finalized)
            write_receipt.assert_not_called()

    def test_receipt_publication_disposition_controls_replan_retryability(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            base_plan = {
                "cache_reusable": True,
                "compiled_artifacts_ready": True,
                "summary": {
                    "statement_requires_review": 0,
                    "coverage_requires_review": 0,
                },
                "validator_identity_errors": {"statement": [], "coverage": []},
            }
            for disposition, retryable in (
                ("source_race", True),
                ("compiled_race", True),
                ("deterministic_input", False),
                ("publication_io", False),
            ):
                with self.subTest(disposition=disposition):
                    publication = planner.CloseoutPlanReceiptPublication(
                        receipt=None,
                        error="fixture publication failure",
                        disposition=disposition,
                        input_identity_sha256="a" * 64,
                    )
                    with mock.patch.object(
                        planner,
                        "_write_current_closeout_plan_receipt",
                        return_value=publication,
                    ):
                        finalized = planner.finalize_operational_plan(
                            dict(base_plan),
                            folder=folder,
                            source_coverage_mode="named_theoretical_statements",
                            execution_path=folder / ".review_traces" / "worker.json",
                            static_readiness={"ready": True, "blockers": []},
                        )

                    action = finalized["next_action"]
                    self.assertEqual(action["id"], "replan_current_inputs")
                    self.assertEqual(action["publication_disposition"], disposition)
                    self.assertEqual(action["retryable"], retryable)
                    self.assertEqual(action["input_identity_sha256"], "a" * 64)

    def test_invalid_advisory_plan_stops_before_operational_receipt(self) -> None:
        """A cached semantic worklist must not freeze a strict receipt either."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            paths = [
                audit / "statement_match_llm.json",
                audit / "paper_coverage_llm.json",
                audit / "paper_statement_map.json",
                audit / "source_proof_fidelity.json",
            ]
            payloads = {path: {} for path in paths}
            material = {
                str(path): {"state": "present", "sha256": "a" * 64}
                for path in paths
            }
            advisory_plan = {
                "acceptance_credential": False,
                "requires_fresh_strict_closeout": True,
                "cache_reusable": True,
                "statement": {
                    "source-result": {
                        "reusable": False,
                        "action": "fresh_human_semantic_review",
                    }
                },
                "coverage": {},
                "summary": {
                    "statement_requires_review": 1,
                    "coverage_requires_review": 0,
                },
                "validator_identity_errors": {"statement": [], "coverage": []},
            }
            output = io.StringIO()
            with (
                mock.patch.object(
                    sys, "argv", ["closeout_reuse_plan.py", "--paper", "Fixture"]
                ),
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "resolve_paper_folder", return_value=folder),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(
                    planner, "runtime_engine_registration_error", return_value=""
                ),
                mock.patch.object(
                    planner,
                    "static_closeout_readiness",
                    return_value={"ready": True, "blockers": []},
                ),
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("formalized", ""),
                ),
                mock.patch.object(
                    planner,
                    "fast_saved_source_record_preflight",
                    return_value={"state": "current_raw_judgment_bound"},
                ),
                mock.patch.object(
                    planner,
                    "_captured_json_payloads",
                    return_value=(payloads, material, []),
                ),
                mock.patch.object(
                    planner,
                    "source_coverage_mode_from_map",
                    return_value=("named_theoretical_statements", ""),
                ),
                mock.patch.object(planner, "inventory_from_source_map", return_value={}),
                mock.patch.object(
                    planner,
                    "canonical_coverage_inventory_projection",
                    return_value=({}, ""),
                ),
                mock.patch.object(
                    planner,
                    "_advisory_plan_input_identity",
                    return_value=("d" * 64, {"_mutation_snapshot": {}}),
                ),
                mock.patch.object(
                    planner, "_read_advisory_plan_cache", return_value=advisory_plan
                ),
                mock.patch.object(
                    planner, "_advisory_input_material_is_current", return_value=True
                ),
                mock.patch.object(planner, "cached_review_snapshot") as cached_snapshot,
                mock.patch.object(
                    planner, "_write_current_closeout_plan_receipt"
                ) as write_receipt,
                contextlib.redirect_stdout(output),
            ):
                result = planner.main()

            self.assertEqual(result, 0)
            emitted = json.loads(output.getvalue())
            self.assertEqual(emitted["next_action"]["id"], "inspect_invalid_semantic_items")
            cached_snapshot.assert_not_called()
            write_receipt.assert_not_called()

    def test_invalid_advisory_cache_skips_strict_snapshot_validation(self) -> None:
        """Legacy cached worklists do not reopen their strict input bundle."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            trace = folder / ".review_traces"
            trace.mkdir(parents=True)
            cache_path = trace / planner.ADVISORY_PLAN_CACHE_FILE
            cache_path.write_text(
                json.dumps(
                    {
                        "schema": planner.ADVISORY_PLAN_CACHE_SCHEMA,
                        "acceptance_credential": False,
                        "decision_contract": planner.ADVISORY_PLAN_DECISION_CONTRACT,
                        "input_identity_sha256": "a" * 64,
                        "semantic_plan": {
                            "acceptance_credential": False,
                            "requires_fresh_strict_closeout": True,
                            "statement": {
                                "unresolved-item": {"reusable": False}
                            },
                            "coverage": {},
                            "summary": {
                                "statement_requires_review": 1,
                                "coverage_requires_review": 0,
                            },
                            "validator_identity_errors": {
                                "statement": [],
                                "coverage": [],
                            },
                        },
                        # This intentionally cannot validate.  A semantic
                        # worklist must return before it becomes relevant.
                        "strict_transaction_content_snapshot": None,
                    }
                ),
                encoding="utf-8",
            )
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "validate_content_input_snapshot",
                    side_effect=AssertionError("strict snapshot must not be read"),
                ) as strict_snapshot,
            ):
                loaded = planner._read_advisory_plan_cache(folder, "a" * 64)

            self.assertIsNotNone(loaded)
            assert loaded is not None
            self.assertTrue(loaded["cache_reusable"])
            self.assertTrue(
                loaded["advisory_plan_cache"]
                ["strict_input_validation_deferred_for_semantic_repair"]
            )
            strict_snapshot.assert_not_called()

    def test_malformed_advisory_semantic_plan_is_not_an_empty_worklist(self) -> None:
        """A truncated cache cannot default missing review items to zero."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            trace = folder / ".review_traces"
            trace.mkdir(parents=True)
            cache_path = trace / planner.ADVISORY_PLAN_CACHE_FILE
            cache_path.write_text(
                json.dumps(
                    {
                        "schema": planner.ADVISORY_PLAN_CACHE_SCHEMA,
                        "acceptance_credential": False,
                        "decision_contract": planner.ADVISORY_PLAN_DECISION_CONTRACT,
                        "input_identity_sha256": "a" * 64,
                        "semantic_plan": {
                            "acceptance_credential": False,
                            "requires_fresh_strict_closeout": True,
                            "statement": {
                                "opaque-cache-entry": {"reusable": False}
                            },
                            "coverage": {},
                            # This lies about the structural worklist.  It
                            # must be a cache miss before strict state is read.
                            "summary": {
                                "statement_requires_review": 0,
                                "coverage_requires_review": 0,
                            },
                            "validator_identity_errors": {
                                "statement": [],
                                "coverage": [],
                            },
                        },
                        "strict_transaction_content_snapshot": None,
                    }
                ),
                encoding="utf-8",
            )
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "validate_content_input_snapshot",
                    side_effect=AssertionError("strict snapshot must not be read"),
                ) as strict_snapshot,
            ):
                loaded = planner._read_advisory_plan_cache(folder, "a" * 64)

            self.assertIsNone(loaded)
            strict_snapshot.assert_not_called()

    def test_prebuild_advisory_cache_skips_strict_snapshot_validation(self) -> None:
        """A cached pre-build plan must rebuild before it can validate strict state."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            trace = folder / ".review_traces"
            trace.mkdir(parents=True)
            cache_path = trace / planner.ADVISORY_PLAN_CACHE_FILE
            cache_path.write_text(
                json.dumps(
                    {
                        "schema": planner.ADVISORY_PLAN_CACHE_SCHEMA,
                        "acceptance_credential": False,
                        "decision_contract": planner.ADVISORY_PLAN_DECISION_CONTRACT,
                        "input_identity_sha256": "a" * 64,
                        "semantic_plan": {
                            "acceptance_credential": False,
                            "requires_fresh_strict_closeout": True,
                            "compiled_artifacts_ready": False,
                            "statement": {},
                            "coverage": {},
                            "summary": {
                                "statement_requires_review": 0,
                                "coverage_requires_review": 0,
                            },
                            "validator_identity_errors": {
                                "statement": [],
                                "coverage": [],
                            },
                        },
                        # A pre-build cache must not need a historical strict
                        # snapshot merely to issue its build/replan action.
                        "strict_transaction_content_snapshot": None,
                    }
                ),
                encoding="utf-8",
            )
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "validate_content_input_snapshot",
                    side_effect=AssertionError("strict snapshot must not be read"),
                ) as strict_snapshot,
            ):
                loaded = planner._read_advisory_plan_cache(folder, "a" * 64)

            self.assertIsNotNone(loaded)
            assert loaded is not None
            self.assertTrue(loaded["cache_reusable"])
            self.assertTrue(
                loaded["advisory_plan_cache"]
                ["strict_input_validation_deferred_for_compiled_rebuild"]
            )
            strict_snapshot.assert_not_called()

    def test_recovery_error_stops_before_static_or_manifest_planning(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            state_path = folder / ".review_traces" / "paper_closeout_worker.json"
            folder.mkdir(parents=True)
            output = io.StringIO()
            with (
                mock.patch.object(
                    sys, "argv", ["closeout_reuse_plan.py", "--paper", "Fixture"]
                ),
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "resolve_paper_folder", return_value=folder),
                mock.patch.object(
                    planner, "running_execution_summary", return_value=None
                ),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(
                        None,
                        "abandoned worker has no correlated child",
                        "worker_recovery_required",
                        state_path,
                    ),
                ),
                mock.patch.object(planner, "static_closeout_readiness") as readiness,
                mock.patch.object(planner, "cached_review_snapshot") as cached,
                contextlib.redirect_stdout(output),
            ):
                result = planner.main()
            self.assertEqual(result, 0)
            emitted = json.loads(output.getvalue())
            self.assertTrue(emitted["expensive_planning_deferred"])
            self.assertEqual(emitted["next_action"]["id"], "inspect_closeout_recovery")
            readiness.assert_not_called()
            cached.assert_not_called()

    def test_unregistered_engine_stops_before_static_or_manifest_planning(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            output = io.StringIO()
            with (
                mock.patch.object(
                    sys, "argv", ["closeout_reuse_plan.py", "--paper", "Fixture"]
                ),
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "resolve_paper_folder", return_value=folder),
                mock.patch.object(
                    planner, "running_execution_summary", return_value=None
                ),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(
                    planner,
                    "runtime_engine_registration_error",
                    return_value="engine source differs from clean HEAD",
                ),
                mock.patch.object(planner, "static_closeout_readiness") as readiness,
                mock.patch.object(planner, "cached_review_snapshot") as cached,
                contextlib.redirect_stdout(output),
            ):
                result = planner.main()
            self.assertEqual(result, 2)
            emitted = json.loads(output.getvalue())
            self.assertTrue(emitted["expensive_planning_deferred"])
            self.assertEqual(
                emitted["next_action"]["id"], "inspect_engine_registration"
            )
            readiness.assert_not_called()
            cached.assert_not_called()

    def test_ineligible_status_stops_before_exact_intake_readiness(self) -> None:
        """Partial papers do not pay a source-artifact scan before the stop."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            output = io.StringIO()
            readiness_payload = {"ready": True, "blockers": []}
            with (
                mock.patch.object(
                    sys, "argv", ["closeout_reuse_plan.py", "--paper", "Fixture"]
                ),
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "resolve_paper_folder", return_value=folder),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(planner, "runtime_engine_registration_error", return_value=""),
                mock.patch.object(
                    planner, "static_closeout_readiness", return_value=readiness_payload
                ) as readiness,
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("partially formalized", "not eligible"),
                ),
                mock.patch.object(planner, "fast_saved_source_record_preflight") as raw,
                contextlib.redirect_stdout(output),
            ):
                result = planner.main()

            self.assertEqual(result, 0)
            emitted = json.loads(output.getvalue())
            self.assertEqual(
                emitted["next_action"]["id"], "resolve_paper_closeout_eligibility"
            )
            readiness.assert_called_once_with(folder, include_intake=False)
            raw.assert_not_called()

    def test_diagnose_reports_static_readiness_for_unregistered_engine(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            output = io.StringIO()
            readiness_payload = {"ready": False, "blockers": ["missing map"]}
            with (
                mock.patch.object(
                    sys,
                    "argv",
                    ["closeout_reuse_plan.py", "--paper", "Fixture", "--diagnose"],
                ),
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "resolve_paper_folder", return_value=folder),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(
                    planner,
                    "runtime_engine_registration_error",
                    return_value="engine source differs from clean HEAD",
                ),
                mock.patch.object(
                    planner, "static_closeout_readiness", return_value=readiness_payload
                ) as readiness,
                mock.patch.object(planner, "cached_review_snapshot") as cached,
                contextlib.redirect_stdout(output),
            ):
                result = planner.main()
            self.assertEqual(result, 0)
            emitted = json.loads(output.getvalue())
            self.assertTrue(emitted["diagnostic_only"])
            self.assertEqual(
                emitted["next_action"]["id"], "commit_registered_engine_transition"
            )
            self.assertEqual(emitted["readiness_matrix"], readiness_payload)
            readiness.assert_called_once_with(folder, include_intake=False)
            cached.assert_not_called()

    def test_diagnose_aggregates_engine_and_status_blockers(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            (folder / "status.json").write_text(
                '{"status": "partially formalized"}\n', encoding="utf-8"
            )
            output = io.StringIO()
            with (
                mock.patch.object(
                    sys,
                    "argv",
                    ["closeout_reuse_plan.py", "--paper", "Fixture", "--diagnose"],
                ),
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "resolve_paper_folder", return_value=folder),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(
                    planner,
                    "runtime_engine_registration_error",
                    return_value="engine source differs from clean HEAD",
                ),
                mock.patch.object(
                    planner,
                    "static_closeout_readiness",
                    return_value={"ready": True, "blockers": []},
                ),
                mock.patch.object(planner, "fast_saved_source_record_preflight") as raw,
                mock.patch.object(planner, "cached_review_snapshot") as cached,
                contextlib.redirect_stdout(output),
            ):
                result = planner.main()

            self.assertEqual(result, 0)
            emitted = json.loads(output.getvalue())
            self.assertTrue(emitted["diagnostic_only"])
            self.assertEqual(emitted["paper_status"], "partially formalized")
            self.assertEqual(
                [action["id"] for action in emitted["actions"]],
                [
                    "commit_registered_engine_transition",
                    "resolve_paper_closeout_eligibility",
                ],
            )
            raw.assert_not_called()
            cached.assert_not_called()

    def test_diagnose_keeps_execution_disposition_and_static_blockers(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            (folder / "status.json").write_text(
                '{"status": "partially formalized"}\n', encoding="utf-8"
            )
            output = io.StringIO()
            with (
                mock.patch.object(
                    sys,
                    "argv",
                    ["closeout_reuse_plan.py", "--paper", "Fixture", "--diagnose"],
                ),
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "resolve_paper_folder", return_value=folder),
                mock.patch.object(
                    planner,
                    "running_execution_summary",
                    return_value={"state": "running"},
                ),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(
                        None,
                        "abandoned worker has no correlated child",
                        "worker_recovery_required",
                        folder / ".review_traces" / "worker.json",
                    ),
                ),
                mock.patch.object(
                    planner,
                    "runtime_engine_registration_error",
                    return_value="engine source differs from clean HEAD",
                ),
                mock.patch.object(
                    planner,
                    "static_closeout_readiness",
                    return_value={"ready": True, "blockers": []},
                ),
                mock.patch.object(planner, "fast_saved_source_record_preflight") as raw,
                mock.patch.object(planner, "cached_review_snapshot") as cached,
                contextlib.redirect_stdout(output),
            ):
                result = planner.main()

            self.assertEqual(result, 0)
            emitted = json.loads(output.getvalue())
            self.assertTrue(emitted["diagnostic_only"])
            self.assertEqual(emitted["closeout_start_disposition"], "already_running")
            self.assertEqual(
                [action["id"] for action in emitted["actions"]],
                [
                    "inspect_active_closeout",
                    "inspect_closeout_recovery",
                    "commit_registered_engine_transition",
                    "resolve_paper_closeout_eligibility",
                ],
            )
            raw.assert_not_called()
            cached.assert_not_called()

    def test_diagnose_never_falls_through_to_semantic_planning(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            output = io.StringIO()
            readiness_payload = {"ready": True, "blockers": []}
            with (
                mock.patch.object(
                    sys,
                    "argv",
                    ["closeout_reuse_plan.py", "--paper", "Fixture", "--diagnose"],
                ),
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "resolve_paper_folder", return_value=folder),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(planner, "runtime_engine_registration_error", return_value=""),
                mock.patch.object(
                    planner, "static_closeout_readiness", return_value=readiness_payload
                ) as readiness,
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("formalized", ""),
                ),
                mock.patch.object(planner, "fast_saved_source_record_preflight") as raw,
                mock.patch.object(planner, "cached_review_snapshot") as cached,
                contextlib.redirect_stdout(output),
            ):
                result = planner.main()
            self.assertEqual(result, 0)
            emitted = json.loads(output.getvalue())
            self.assertTrue(emitted["diagnostic_only"])
            self.assertEqual(emitted["next_action"]["id"], "run_frozen_closeout_planner")
            readiness.assert_called_once_with(folder, include_intake=False)
            raw.assert_not_called()
            cached.assert_not_called()

    def test_source_record_preflight_actions_are_dependency_ordered(self) -> None:
        current_delta = planner.source_record_preflight_action(
            "Fixture",
            {"state": "current_raw_judgment_delta", "reason": "different digest"},
        )
        assert current_delta is not None
        self.assertEqual(current_delta["id"], "review_current_source_record_delta")

        rebuild = planner.source_record_preflight_action(
            "Fixture",
            {
                "state": "current_raw_judgment_rebuild_required",
                "reason": "judgment sidecar is malformed",
            },
        )
        assert rebuild is not None
        self.assertEqual(rebuild["id"], "rebuild_current_source_record_judgments")
        self.assertNotIn("argv", rebuild)

        semantic_repair = planner.source_record_preflight_action(
            "Fixture",
            {
                "state": "current_raw_semantic_repair_required",
                "reason": "current generated semantic surface is invalid",
            },
        )
        assert semantic_repair is not None
        self.assertEqual(
            semantic_repair["id"], "repair_current_source_record_semantic_surface"
        )
        self.assertNotIn("argv", semantic_repair)

        with (
            mock.patch.object(
                planner, "closeout_wave_engine_action", return_value=None
            ),
            mock.patch.object(
                planner, "source_record_reissue_lock_action", return_value=None
            ),
        ):
            stale_raw = planner.source_record_preflight_action(
                "Fixture",
                {"state": "raw_reissue_required", "reason": "source changed"},
            )
        assert stale_raw is not None
        self.assertEqual(stale_raw["id"], "freeze_then_raw_reissue")
        self.assertIn("freeze", stale_raw["reason"])
        self.assertEqual(
            stale_raw["argv"],
            [
                "python3",
                "scripts/closeout_reuse_plan.py",
                "--paper",
                "Fixture",
                "--execute-freeze-raw-reissue",
            ],
        )
        self.assertEqual(stale_raw["after_success"]["id"], "replan_after_raw_reissue")

        inspection = planner.source_record_preflight_action(
            "Fixture",
            {"state": "identity_inspection_required", "reason": "structural replay"},
        )
        assert inspection is not None
        self.assertEqual(inspection["id"], "inspect_saved_source_record_identity")

    def test_semantic_repair_state_requires_complete_structured_dimensions(
        self,
    ) -> None:
        identity = {
            "current": False,
            "identity_scope": "repository_sources_and_configuration_only",
            "observed_source_record_fingerprint_schema": 10,
            "validation_dimensions": {
                "raw_receipt_integrity": {"state": "valid"},
                "generated_semantic_surface": {
                    "state": "invalid",
                    "reason": "a semantic graph mismatch",
                },
                "raw_scan_completeness": {"state": "valid"},
                "reusable_item_metadata": {"state": "valid"},
                "raw_bytes": {"state": "stable"},
                "source_configuration_identity": {"state": "current"},
            },
        }
        self.assertTrue(planner.current_raw_semantic_repair_required(identity))

        text_lookalike = {
            "current": False,
            "identity_scope": "repository_sources_and_configuration_only",
            "observed_source_record_fingerprint_schema": 10,
            "reason": "source/configuration identity differs",
        }
        self.assertFalse(planner.current_raw_semantic_repair_required(text_lookalike))

        invalid_transport = dict(identity)
        invalid_transport["validation_dimensions"] = {
            **identity["validation_dimensions"],
            "raw_scan_completeness": {"state": "invalid", "reason": "missing"},
        }
        self.assertFalse(planner.current_raw_semantic_repair_required(invalid_transport))

    def test_source_record_reissue_action_waits_for_active_scan(self) -> None:
        wait_action = {
            "id": "wait_for_source_record_scan",
            "state": "waiting",
            "required": True,
        }
        with (
            mock.patch.object(
                planner, "closeout_wave_engine_action", return_value=None
            ),
            mock.patch.object(
                planner, "source_record_reissue_lock_action", return_value=wait_action
            ),
        ):
            action = planner.source_record_preflight_action(
                "Fixture",
                {"state": "raw_reissue_required", "reason": "source changed"},
            )

        self.assertEqual(action, wait_action)

    def test_source_record_preflight_waits_for_wrapper_before_producer_scan(
        self,
    ) -> None:
        """A normal wrapper lease is the first raw-reissue dependency."""

        wait_action = {
            "id": "wait_for_closeout_raw_reissue",
            "state": "waiting",
            "required": True,
        }
        with (
            mock.patch.object(
                planner, "closeout_wave_engine_action", return_value=None
            ),
            mock.patch.object(
                planner, "closeout_raw_reissue_lock_action", return_value=wait_action
            ),
            mock.patch.object(planner, "source_record_reissue_lock_action") as producer,
        ):
            action = planner.source_record_preflight_action(
                "Fixture",
                {"state": "raw_reissue_required", "reason": "source changed"},
            )

        self.assertEqual(action, wait_action)
        producer.assert_not_called()

    def test_source_record_preflight_stops_at_engine_wave_before_raw_locks(self) -> None:
        reset_action = {
            "id": "reset_closeout_wave_engine_snapshot",
            "state": "ready_now",
            "required": True,
        }
        with (
            mock.patch.object(
                planner, "closeout_wave_engine_action", return_value=reset_action
            ),
            mock.patch.object(planner, "raw_reissue_transition_lock_action") as locks,
        ):
            action = planner.source_record_preflight_action(
                "Fixture", {"state": "raw_reissue_required", "reason": "stale raw"}
            )

        self.assertEqual(action, reset_action)
        locks.assert_not_called()

    def test_closeout_raw_reissue_lock_action_waits_for_active_wrapper(self) -> None:
        """The advisory lease prevents a second wrapper transition, not evidence."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            with mock.patch.object(planner, "ROOT", root):
                handle, error = planner._try_acquire_closeout_raw_reissue_lock("Other")
                self.assertEqual(error, "")
                assert handle is not None
                try:
                    action = planner.closeout_raw_reissue_lock_action("Fixture")
                finally:
                    planner._release_closeout_raw_reissue_lock(handle)

        assert action is not None
        self.assertEqual(action["id"], "wait_for_closeout_raw_reissue")
        self.assertEqual(action["closeout_raw_reissue_lock"]["state"], "held")
        self.assertEqual(
            action["closeout_raw_reissue_lock"]["owner"]["paper"], "Other"
        )

    def test_source_record_reissue_lock_action_inspects_unreadable_observer(self) -> None:
        with mock.patch.object(
            planner,
            "source_record_scan_lock_observation",
            return_value=(None, "source-record lock observer returned invalid JSON"),
        ):
            action = planner.source_record_reissue_lock_action("Fixture")

        assert action is not None
        self.assertEqual(action["id"], "inspect_source_record_scan_lock")
        self.assertIn("invalid JSON", action["reason"])

    def test_source_record_scan_lock_observation_rejects_unavailable_state(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            helper = root / "source_record_audit.py"
            helper.write_text("# fixture\n", encoding="utf-8")
            proc = types.SimpleNamespace(
                returncode=0,
                stdout=json.dumps(
                    {"schema": 1, "held": False, "state": "unreadable"}
                ),
                stderr="",
            )
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "FAST_SAVED_SOURCE_RECORD_HELPER_RELATIVE",
                    helper.relative_to(root),
                ),
                mock.patch.object(planner.subprocess, "run", return_value=proc),
            ):
                observation, error = planner.source_record_scan_lock_observation()

        self.assertIsNone(observation)
        self.assertIn("unavailable lock state", error)

    def test_raw_reissue_wrapper_is_idempotent_when_raw_is_already_current(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            output = io.StringIO()
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(planner, "runtime_engine_registration_error", return_value=""),
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("formalized", ""),
                ),
                mock.patch.object(
                    planner, "static_closeout_readiness", return_value={"ready": True}
                ),
                mock.patch.object(planner, "_raw_reissue_material_errors", return_value=[]),
                mock.patch.object(
                    planner,
                    "fast_saved_source_record_preflight",
                    return_value={"state": "current_raw_judgment_bound"},
                ),
                mock.patch.object(planner.subprocess, "run") as run,
                contextlib.redirect_stdout(output),
            ):
                result = planner.execute_freeze_then_raw_reissue(folder)

            self.assertEqual(result, 0)
            emitted = json.loads(output.getvalue())
            self.assertEqual(emitted["state"], "already_current")
            self.assertFalse(emitted["raw_scan_started"])
            run.assert_not_called()

    def test_raw_reissue_wrapper_preserves_predecessor_then_stops_at_delta(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            raw = audit / "source_record_audit.json"
            judgment = audit / "source_record_match_llm.json"
            raw.write_text('{"old": "raw"}\n', encoding="utf-8")
            judgment.write_text('{"old": "judgment"}\n', encoding="utf-8")
            preflight = {
                "state": "raw_reissue_required",
                "reason": "legacy fingerprint",
                "raw_path": str(raw.relative_to(root)),
                "judgment_path": str(judgment.relative_to(root)),
            }
            postflight = {
                "state": "current_raw_judgment_delta",
                "reason": "new raw requires semantic delta",
            }
            output = io.StringIO()
            proc = types.SimpleNamespace(returncode=0, stdout='{"scanned": true}\n', stderr="")
            helper = root / "source_record_audit.py"
            helper.write_text("# fixture\n", encoding="utf-8")
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "FAST_SAVED_SOURCE_RECORD_HELPER_RELATIVE",
                    helper.relative_to(root),
                ),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(planner, "runtime_engine_registration_error", return_value=""),
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("formalized", ""),
                ),
                mock.patch.object(
                    planner, "static_closeout_readiness", return_value={"ready": True}
                ),
                mock.patch.object(planner, "_raw_reissue_material_errors", return_value=[]),
                mock.patch.object(
                    planner,
                    "fast_saved_source_record_preflight",
                    side_effect=[preflight, preflight, postflight],
                ),
                mock.patch.object(
                    planner, "source_record_reissue_lock_action", return_value=None
                ),
                mock.patch.object(
                    planner,
                    "ensure_closeout_wave_engine_snapshot",
                    return_value=(self.wave_snapshot(), True, ""),
                ),
                mock.patch.object(
                    planner,
                    "closeout_wave_engine_snapshot_state",
                    return_value={"state": "current", "snapshot": self.wave_snapshot()},
                ),
                mock.patch.object(planner.subprocess, "run", return_value=proc) as run,
                contextlib.redirect_stdout(output),
            ):
                result = planner.execute_freeze_then_raw_reissue(folder)

            self.assertEqual(result, 0)
            emitted = json.loads(output.getvalue())
            self.assertEqual(emitted["state"], "raw_reissue_completed")
            self.assertEqual(
                emitted["next_action"]["id"], "review_current_source_record_delta"
            )
            command = run.call_args.args[0]
            self.assertIn("--closeout-raw-reissue", command)
            self.assertIn("--closeout-raw-reissue-operation-id", command)
            snapshot = root / emitted["predecessor_snapshot"]
            self.assertTrue(snapshot.is_file())
            self.assertEqual(raw.read_text(encoding="utf-8"), '{"old": "raw"}\n')
            operation_path = root / emitted["operation_receipt"]
            operation = json.loads(operation_path.read_text(encoding="utf-8"))
            self.assertEqual(operation["state"], "completed")
            self.assertFalse(operation["acceptance_credential"])
            self.assertTrue(operation["operational_recovery_only"])
            self.assertEqual(
                operation["operation_id"],
                command[command.index("--closeout-raw-reissue-operation-id") + 1],
            )
            self.assertEqual(
                operation["next_action"]["id"],
                "review_current_source_record_delta",
            )
            self.assertNotIn("scanned", json.dumps(operation))

    def test_raw_reissue_checks_helper_before_binding_an_engine_wave(self) -> None:
        """An unavailable producer cannot create an otherwise empty wave."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            preflight = {"state": "raw_reissue_required", "reason": "stale raw"}
            output = io.StringIO()
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(planner, "runtime_engine_registration_error", return_value=""),
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("formalized", ""),
                ),
                mock.patch.object(
                    planner, "static_closeout_readiness", return_value={"ready": True}
                ),
                mock.patch.object(planner, "_raw_reissue_material_errors", return_value=[]),
                mock.patch.object(
                    planner, "fast_saved_source_record_preflight", return_value=preflight
                ),
                mock.patch.object(
                    planner, "closeout_wave_engine_snapshot_state", return_value={"state": "not_started"}
                ),
                mock.patch.object(
                    planner, "source_record_reissue_lock_action", return_value=None
                ),
                mock.patch.object(
                    planner, "ensure_closeout_wave_engine_snapshot"
                ) as ensure,
                contextlib.redirect_stdout(output),
            ):
                result = planner.execute_freeze_then_raw_reissue(folder)

            self.assertEqual(result, 2)
            emitted = json.loads(output.getvalue())
            self.assertEqual(emitted["state"], "raw_reissue_helper_unavailable")
            ensure.assert_not_called()

    def test_raw_reissue_replans_when_preflight_changes_under_lease(self) -> None:
        """A stale decision never archives its predecessor after the lease race."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            helper = root / "source_record_audit.py"
            helper.write_text("# fixture\n", encoding="utf-8")
            preflight = {"state": "raw_reissue_required", "identity": {"source": "old"}}
            changed = {"state": "raw_reissue_required", "identity": {"source": "new"}}
            output = io.StringIO()
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "FAST_SAVED_SOURCE_RECORD_HELPER_RELATIVE",
                    helper.relative_to(root),
                ),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(planner, "runtime_engine_registration_error", return_value=""),
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("formalized", ""),
                ),
                mock.patch.object(
                    planner, "static_closeout_readiness", return_value={"ready": True}
                ),
                mock.patch.object(planner, "_raw_reissue_material_errors", return_value=[]),
                mock.patch.object(
                    planner,
                    "fast_saved_source_record_preflight",
                    side_effect=[preflight, changed],
                ),
                mock.patch.object(
                    planner, "closeout_wave_engine_snapshot_state", return_value={"state": "not_started"}
                ),
                mock.patch.object(
                    planner, "source_record_reissue_lock_action", return_value=None
                ),
                mock.patch.object(
                    planner, "ensure_closeout_wave_engine_snapshot"
                ) as ensure,
                mock.patch.object(planner, "_archive_raw_reissue_predecessors") as archive,
                mock.patch.object(planner.subprocess, "run") as run,
                contextlib.redirect_stdout(output),
            ):
                result = planner.execute_freeze_then_raw_reissue(folder)

            self.assertEqual(result, 2)
            emitted = json.loads(output.getvalue())
            self.assertEqual(emitted["state"], "raw_reissue_preflight_changed")
            self.assertEqual(
                emitted["next_action"]["id"], "replan_after_closeout_raw_reissue"
            )
            ensure.assert_not_called()
            archive.assert_not_called()
            run.assert_not_called()

    def test_raw_reissue_requires_recovery_for_prior_running_receipt(self) -> None:
        """A lost terminal stream cannot be silently overwritten by a new wave."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            helper = root / "source_record_audit.py"
            helper.write_text("# fixture\n", encoding="utf-8")
            preflight = {"state": "raw_reissue_required", "identity": {"source": "old"}}
            output = io.StringIO()
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "FAST_SAVED_SOURCE_RECORD_HELPER_RELATIVE",
                    helper.relative_to(root),
                ),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(planner, "runtime_engine_registration_error", return_value=""),
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("formalized", ""),
                ),
                mock.patch.object(
                    planner, "static_closeout_readiness", return_value={"ready": True}
                ),
                mock.patch.object(planner, "_raw_reissue_material_errors", return_value=[]),
                mock.patch.object(
                    planner, "fast_saved_source_record_preflight", return_value=preflight
                ),
                mock.patch.object(
                    planner, "closeout_wave_engine_snapshot_state", return_value={"state": "not_started"}
                ),
                mock.patch.object(
                    planner, "source_record_reissue_lock_action", return_value=None
                ),
                mock.patch.object(
                    planner,
                    "closeout_raw_reissue_operation_receipt_state",
                    return_value={"state": "running", "receipt": {"operation_id": "old"}},
                ),
                mock.patch.object(
                    planner, "ensure_closeout_wave_engine_snapshot"
                ) as ensure,
                mock.patch.object(planner, "_archive_raw_reissue_predecessors") as archive,
                mock.patch.object(planner.subprocess, "run") as run,
                contextlib.redirect_stdout(output),
            ):
                result = planner.execute_freeze_then_raw_reissue(folder)

            self.assertEqual(result, 2)
            emitted = json.loads(output.getvalue())
            self.assertEqual(
                emitted["state"], "raw_reissue_operation_recovery_required"
            )
            self.assertEqual(
                emitted["next_action"]["id"], "recover_raw_reissue_operation"
            )
            ensure.assert_not_called()
            archive.assert_not_called()
            run.assert_not_called()

    def test_raw_reissue_status_distinguishes_an_orphaned_running_receipt(self) -> None:
        """Status exposes the lock observations needed for lost-stream recovery."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "papers" / "Fixture"
            folder.mkdir(parents=True)
            output = io.StringIO()
            with (
                mock.patch.object(
                    planner,
                    "closeout_raw_reissue_operation_receipt_state",
                    return_value={"state": "running", "receipt": {"operation_id": "old"}},
                ),
                mock.patch.object(
                    planner,
                    "closeout_raw_reissue_lock_observation",
                    return_value=({"held": False, "state": "available"}, ""),
                ),
                mock.patch.object(
                    planner,
                    "source_record_scan_lock_observation",
                    return_value=({"held": False, "state": "available"}, ""),
                ),
                mock.patch.object(
                    planner,
                    "closeout_wave_engine_snapshot_state",
                    return_value={"state": "current"},
                ),
                contextlib.redirect_stdout(output),
            ):
                result = planner.raw_reissue_operation_status(folder)

            self.assertEqual(result, 2)
            emitted = json.loads(output.getvalue())
            self.assertEqual(
                emitted["state"], "raw_reissue_operation_recovery_required"
            )
            self.assertEqual(
                emitted["wrapper_lease"]["state"], "available"
            )
            self.assertEqual(
                emitted["source_record_lock"]["state"], "available"
            )

    def test_wave_reset_defers_while_the_source_record_lock_is_held(self) -> None:
        """An explicit reset cannot cut across a repository-wide raw scan."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            wait_action = {"id": "wait_for_source_record_scan", "required": True}
            output = io.StringIO()
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(planner, "runtime_engine_registration_error", return_value=""),
                mock.patch.object(
                    planner, "closeout_raw_reissue_lock_action", return_value=None
                ),
                mock.patch.object(
                    planner, "_try_acquire_closeout_raw_reissue_lock", return_value=(object(), "")
                ),
                mock.patch.object(
                    planner, "source_record_reissue_lock_action", return_value=wait_action
                ),
                mock.patch.object(
                    planner, "reset_closeout_wave_engine_snapshot"
                ) as reset,
                contextlib.redirect_stdout(output),
            ):
                result = planner.reset_closeout_wave_engine_snapshot_for_paper(folder)

            self.assertEqual(result, 2)
            emitted = json.loads(output.getvalue())
            self.assertEqual(emitted["state"], "closeout_wave_engine_reset_deferred")
            self.assertEqual(emitted["next_action"], wait_action)
            reset.assert_not_called()

    def test_explicit_recovery_terminalizes_only_an_idle_running_receipt(self) -> None:
        """Recovery never reissues raw work and leaves a durable stopped record."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            with mock.patch.object(planner, "ROOT", root):
                receipt_path = planner.raw_reissue_operation_receipt_path(folder)
                receipt_path.parent.mkdir(parents=True)
                receipt_path.write_text(
                    json.dumps(
                        {
                            "schema": planner.RAW_REISSUE_OPERATION_TRACE_SCHEMA,
                            "kind": "source_record_raw_reissue_operation",
                            "acceptance_credential": False,
                            "operational_recovery_only": True,
                            "state": "running",
                            "paper": "Fixture",
                            "operation_id": "old-operation",
                        }
                    ),
                    encoding="utf-8",
                )
                output = io.StringIO()
                with (
                    mock.patch.object(
                        planner, "closeout_raw_reissue_lock_action", return_value=None
                    ),
                    mock.patch.object(
                        planner, "source_record_reissue_lock_action", return_value=None
                    ),
                    mock.patch.object(
                        planner,
                        "fast_saved_source_record_preflight",
                        return_value={"state": "raw_reissue_required"},
                    ),
                    contextlib.redirect_stdout(output),
                ):
                    result = planner.acknowledge_stale_raw_reissue_operation(folder)

                self.assertEqual(result, 0)
                emitted = json.loads(output.getvalue())
                self.assertEqual(
                    emitted["state"], "raw_reissue_operation_recovery_acknowledged"
                )
                recovered = json.loads(receipt_path.read_text(encoding="utf-8"))
                self.assertEqual(recovered["state"], "stopped")
                self.assertEqual(
                    recovered["wrapper_state"],
                    "raw_reissue_recovery_acknowledged",
                )
                self.assertIn("recovery_preflight", recovered)

    def test_terminal_operation_receipt_bounds_failure_detail(self) -> None:
        """Operational recovery receipts cannot duplicate multi-megabyte logs."""

        with tempfile.TemporaryDirectory() as temp_dir:
            path = Path(temp_dir) / "operation.json"
            payload = {
                "schema": planner.RAW_REISSUE_OPERATION_TRACE_SCHEMA,
                "state": "running",
            }
            planner._finish_raw_reissue_operation_receipt(
                path,
                payload,
                {
                    "state": "raw_reissue_failed",
                    "raw_scan_started": True,
                    "producer_detail": "x" * 10000,
                },
            )
            terminal = json.loads(path.read_text(encoding="utf-8"))
            self.assertEqual(terminal["state"], "failed")
            self.assertLessEqual(len(terminal["producer_detail"]), 4096)
            self.assertTrue(terminal["producer_detail"].endswith("[truncated]"))

    def test_raw_reissue_wrapper_completes_at_current_semantic_repair(self) -> None:
        """A successful producer is not a failure when only repair remains."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            helper = root / "source_record_audit.py"
            helper.write_text("# fixture\n", encoding="utf-8")
            preflight = {"state": "raw_reissue_required", "reason": "stale raw"}
            postflight = {
                "state": "current_raw_semantic_repair_required",
                "reason": "current semantic surface needs a graph repair",
            }
            proc = types.SimpleNamespace(returncode=0, stdout='{"scanned": true}\n', stderr="")
            output = io.StringIO()
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "FAST_SAVED_SOURCE_RECORD_HELPER_RELATIVE",
                    helper.relative_to(root),
                ),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(planner, "runtime_engine_registration_error", return_value=""),
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("formalized", ""),
                ),
                mock.patch.object(
                    planner, "static_closeout_readiness", return_value={"ready": True}
                ),
                mock.patch.object(planner, "_raw_reissue_material_errors", return_value=[]),
                mock.patch.object(
                    planner,
                    "fast_saved_source_record_preflight",
                    side_effect=[preflight, preflight, postflight],
                ),
                mock.patch.object(
                    planner, "source_record_reissue_lock_action", return_value=None
                ),
                mock.patch.object(
                    planner,
                    "ensure_closeout_wave_engine_snapshot",
                    return_value=(self.wave_snapshot(), True, ""),
                ),
                mock.patch.object(
                    planner,
                    "closeout_wave_engine_snapshot_state",
                    return_value={"state": "current", "snapshot": self.wave_snapshot()},
                ),
                mock.patch.object(
                    planner,
                    "_archive_raw_reissue_predecessors",
                    return_value=(folder / "trace.json", {"entries": []}),
                ),
                mock.patch.object(planner.subprocess, "run", return_value=proc),
                contextlib.redirect_stdout(output),
            ):
                result = planner.execute_freeze_then_raw_reissue(folder)

            self.assertEqual(result, 0)
            emitted = json.loads(output.getvalue())
            self.assertEqual(emitted["state"], "raw_reissue_completed")
            self.assertEqual(
                emitted["next_action"]["id"],
                "repair_current_source_record_semantic_surface",
            )

    def test_raw_reissue_replans_when_same_engine_wave_is_replaced(self) -> None:
        """A manual same-engine reset cannot hide a crossed raw-reissue wave."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            helper = root / "source_record_audit.py"
            helper.write_text("# fixture\n", encoding="utf-8")
            preflight = {"state": "raw_reissue_required", "identity": {"source": "old"}}
            captured = self.wave_snapshot()
            replaced = self.wave_snapshot()
            replaced["wave_id"] = "replacement-wave"
            proc = types.SimpleNamespace(returncode=0, stdout="ok\n", stderr="")
            output = io.StringIO()
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "FAST_SAVED_SOURCE_RECORD_HELPER_RELATIVE",
                    helper.relative_to(root),
                ),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(planner, "runtime_engine_registration_error", return_value=""),
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("formalized", ""),
                ),
                mock.patch.object(
                    planner, "static_closeout_readiness", return_value={"ready": True}
                ),
                mock.patch.object(planner, "_raw_reissue_material_errors", return_value=[]),
                mock.patch.object(
                    planner,
                    "fast_saved_source_record_preflight",
                    side_effect=[preflight, preflight],
                ),
                mock.patch.object(
                    planner, "source_record_reissue_lock_action", return_value=None
                ),
                mock.patch.object(
                    planner,
                    "ensure_closeout_wave_engine_snapshot",
                    return_value=(captured, True, ""),
                ),
                mock.patch.object(
                    planner,
                    "closeout_wave_engine_snapshot_state",
                    side_effect=[
                        {"state": "not_started"},
                        {"state": "current", "snapshot": replaced},
                        {"state": "current", "snapshot": replaced},
                    ],
                ),
                mock.patch.object(
                    planner,
                    "_archive_raw_reissue_predecessors",
                    return_value=(folder / "trace.json", {"entries": []}),
                ),
                mock.patch.object(planner.subprocess, "run", return_value=proc) as run,
                contextlib.redirect_stdout(output),
            ):
                result = planner.execute_freeze_then_raw_reissue(folder)

            self.assertEqual(result, 2)
            emitted = json.loads(output.getvalue())
            self.assertEqual(
                emitted["state"], "raw_reissue_engine_transitioned_during_scan"
            )
            self.assertEqual(
                emitted["next_action"]["id"], "replan_after_closeout_raw_reissue"
            )
            run.assert_called_once()

    def test_raw_reissue_wrapper_stops_after_engine_transition_without_retry(self) -> None:
        """A producer success is non-accepting when its engine wave changed."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            raw = audit / "source_record_audit.json"
            judgment = audit / "source_record_match_llm.json"
            raw.write_text('{"old": "raw"}\n', encoding="utf-8")
            judgment.write_text('{"old": "judgment"}\n', encoding="utf-8")
            helper = root / "source_record_audit.py"
            helper.write_text("# fixture\n", encoding="utf-8")
            preflight = {
                "state": "raw_reissue_required",
                "reason": "stale raw",
                "raw_path": str(raw.relative_to(root)),
                "judgment_path": str(judgment.relative_to(root)),
            }
            reset_state = {
                "state": "reset_required",
                "reason": "registered engine changed",
            }
            proc = types.SimpleNamespace(returncode=0, stdout="ok\n", stderr="")
            output = io.StringIO()
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "FAST_SAVED_SOURCE_RECORD_HELPER_RELATIVE",
                    helper.relative_to(root),
                ),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(planner, "runtime_engine_registration_error", return_value=""),
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("formalized", ""),
                ),
                mock.patch.object(
                    planner, "static_closeout_readiness", return_value={"ready": True}
                ),
                mock.patch.object(planner, "_raw_reissue_material_errors", return_value=[]),
                mock.patch.object(
                    planner,
                    "fast_saved_source_record_preflight",
                    return_value=preflight,
                ) as preflight_check,
                mock.patch.object(
                    planner, "source_record_reissue_lock_action", return_value=None
                ),
                mock.patch.object(
                    planner,
                    "ensure_closeout_wave_engine_snapshot",
                    return_value=(self.wave_snapshot(), True, ""),
                ),
                mock.patch.object(
                    planner,
                    "closeout_wave_engine_snapshot_state",
                    side_effect=[{"state": "not_started"}, reset_state, reset_state],
                ),
                mock.patch.object(planner.subprocess, "run", return_value=proc) as run,
                contextlib.redirect_stdout(output),
            ):
                result = planner.execute_freeze_then_raw_reissue(folder)

            self.assertEqual(result, 2)
            emitted = json.loads(output.getvalue())
            self.assertEqual(
                emitted["state"], "raw_reissue_engine_transitioned_during_scan"
            )
            self.assertEqual(
                emitted["next_action"]["id"], "reset_closeout_wave_engine_snapshot"
            )
            run.assert_called_once()
            self.assertEqual(preflight_check.call_count, 2)
            self.assertEqual(preflight_check.call_args.args, (folder,))
            operation = json.loads(
                (root / emitted["operation_receipt"]).read_text(encoding="utf-8")
            )
            self.assertEqual(operation["state"], "failed")
            self.assertTrue(operation["raw_scan_started"])

    def test_predecessor_archive_normalizes_relative_paper_folder(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            raw = audit / "source_record_audit.json"
            judgment = audit / "source_record_match_llm.json"
            raw.write_text('{"raw": true}\n', encoding="utf-8")
            judgment.write_text('{"judgment": true}\n', encoding="utf-8")
            preflight = {
                "raw_path": str(raw.relative_to(root)),
                "judgment_path": str(judgment.relative_to(root)),
            }
            with mock.patch.object(planner, "ROOT", root):
                receipt_path, receipt = planner._archive_raw_reissue_predecessors(
                    Path("papers/Fixture"), preflight
                )

            self.assertTrue(receipt_path.is_file())
            self.assertEqual(len(receipt["entries"]), 2)
            self.assertTrue(
                all(entry["state"] == "preserved" for entry in receipt["entries"])
            )

    def test_predecessor_archive_removes_new_snapshots_when_receipt_write_fails(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            raw = audit / "source_record_audit.json"
            raw.write_text('{"raw": true}\n', encoding="utf-8")
            preflight = {"raw_path": str(raw.relative_to(root))}
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "atomic_write_json", side_effect=OSError("disk")),
            ):
                with self.assertRaises(OSError):
                    planner._archive_raw_reissue_predecessors(
                        Path("papers/Fixture"), preflight
                    )

            trace_dir = folder / ".review_traces" / planner.RAW_REISSUE_TRACE_DIRECTORY
            self.assertEqual(list(trace_dir.glob("raw-*.json")), [])
            self.assertEqual(list(trace_dir.glob("predecessor-*.json")), [])

    def test_predecessor_archive_removes_partial_copy_after_link_fallback_failure(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            raw = audit / "source_record_audit.json"
            raw.write_text('{"raw": true}\n', encoding="utf-8")
            preflight = {"raw_path": str(raw.relative_to(root))}

            def partial_copy(_source: Path, destination: Path) -> None:
                destination.write_text("partial\n", encoding="utf-8")
                raise OSError("copy interrupted")

            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner.os, "link", side_effect=OSError("cross device")),
                mock.patch.object(planner.shutil, "copyfile", side_effect=partial_copy),
            ):
                with self.assertRaisesRegex(OSError, "copy interrupted"):
                    planner._archive_raw_reissue_predecessors(
                        Path("papers/Fixture"), preflight
                    )

            trace_dir = folder / ".review_traces" / planner.RAW_REISSUE_TRACE_DIRECTORY
            self.assertEqual(list(trace_dir.glob("raw-*.json")), [])
            self.assertEqual(list(trace_dir.glob("predecessor-*.json")), [])

    def test_raw_reissue_wrapper_waits_without_preserving_or_starting_scan(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            preflight = {"state": "raw_reissue_required", "reason": "stale raw"}
            wait_action = {
                "id": "wait_for_source_record_scan",
                "state": "waiting",
                "required": True,
            }
            output = io.StringIO()
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(planner, "runtime_engine_registration_error", return_value=""),
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("formalized", ""),
                ),
                mock.patch.object(
                    planner, "static_closeout_readiness", return_value={"ready": True}
                ),
                mock.patch.object(planner, "_raw_reissue_material_errors", return_value=[]),
                mock.patch.object(
                    planner,
                    "fast_saved_source_record_preflight",
                    return_value=preflight,
                ),
                mock.patch.object(
                    planner,
                    "source_record_reissue_lock_action",
                    return_value=wait_action,
                ),
                mock.patch.object(planner, "_archive_raw_reissue_predecessors") as archive,
                mock.patch.object(planner.subprocess, "run") as run,
                contextlib.redirect_stdout(output),
            ):
                result = planner.execute_freeze_then_raw_reissue(folder)

            self.assertEqual(result, 2)
            emitted = json.loads(output.getvalue())
            self.assertEqual(
                emitted["state"], "raw_reissue_deferred_by_source_record_scan"
            )
            self.assertFalse(emitted["raw_scan_started"])
            self.assertEqual(emitted["next_action"], wait_action)
            archive.assert_not_called()
            run.assert_not_called()

    def test_raw_reissue_wrapper_waits_for_another_wrapper_without_archiving(
        self,
    ) -> None:
        """A concurrent normal wrapper cannot create a redundant predecessor."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            preflight = {"state": "raw_reissue_required", "reason": "stale raw"}
            output = io.StringIO()
            with mock.patch.object(planner, "ROOT", root):
                handle, error = planner._try_acquire_closeout_raw_reissue_lock("Other")
                self.assertEqual(error, "")
                assert handle is not None
                try:
                    with (
                        mock.patch.object(
                            planner, "running_execution_summary", return_value=None
                        ),
                        mock.patch.object(
                            planner,
                            "effective_closeout_execution_state",
                            return_value=(None, "", "worker", folder / "state.json"),
                        ),
                        mock.patch.object(
                            planner, "runtime_engine_registration_error", return_value=""
                        ),
                        mock.patch.object(
                            planner,
                            "_paper_closeout_status_preflight",
                            return_value=("formalized", ""),
                        ),
                        mock.patch.object(
                            planner, "static_closeout_readiness", return_value={"ready": True}
                        ),
                        mock.patch.object(
                            planner, "_raw_reissue_material_errors", return_value=[]
                        ),
                        mock.patch.object(
                            planner,
                            "fast_saved_source_record_preflight",
                            return_value=preflight,
                        ),
                        mock.patch.object(
                            planner, "_archive_raw_reissue_predecessors"
                        ) as archive,
                        mock.patch.object(planner.subprocess, "run") as run,
                        contextlib.redirect_stdout(output),
                    ):
                        result = planner.execute_freeze_then_raw_reissue(folder)
                finally:
                    planner._release_closeout_raw_reissue_lock(handle)

            self.assertEqual(result, 2)
            emitted = json.loads(output.getvalue())
            self.assertEqual(
                emitted["state"], "raw_reissue_deferred_by_closeout_raw_reissue"
            )
            self.assertFalse(emitted["raw_scan_started"])
            self.assertEqual(
                emitted["next_action"]["id"], "wait_for_closeout_raw_reissue"
            )
            archive.assert_not_called()
            run.assert_not_called()

    def test_raw_reissue_wrapper_replans_when_lease_releases_during_race(
        self,
    ) -> None:
        """A raced wrapper lease never leaves an actionless deferred result."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            preflight = {"state": "raw_reissue_required", "reason": "stale raw"}
            output = io.StringIO()
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(planner, "runtime_engine_registration_error", return_value=""),
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("formalized", ""),
                ),
                mock.patch.object(
                    planner, "static_closeout_readiness", return_value={"ready": True}
                ),
                mock.patch.object(planner, "_raw_reissue_material_errors", return_value=[]),
                mock.patch.object(
                    planner,
                    "fast_saved_source_record_preflight",
                    return_value=preflight,
                ),
                mock.patch.object(
                    planner,
                    "closeout_raw_reissue_lock_action",
                    side_effect=[None, None],
                ),
                mock.patch.object(
                    planner,
                    "_try_acquire_closeout_raw_reissue_lock",
                    return_value=(None, ""),
                ),
                mock.patch.object(planner, "_archive_raw_reissue_predecessors") as archive,
                mock.patch.object(planner.subprocess, "run") as run,
                contextlib.redirect_stdout(output),
            ):
                result = planner.execute_freeze_then_raw_reissue(folder)

            self.assertEqual(result, 2)
            emitted = json.loads(output.getvalue())
            self.assertEqual(
                emitted["state"], "raw_reissue_deferred_by_closeout_raw_reissue"
            )
            self.assertEqual(
                emitted["next_action"]["id"], "replan_after_closeout_raw_reissue"
            )
            archive.assert_not_called()
            run.assert_not_called()

    def test_raw_reissue_wrapper_inspects_unavailable_transition_lease(
        self,
    ) -> None:
        """A broken wrapper lease is an explicit stop before any snapshot."""

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            preflight = {"state": "raw_reissue_required", "reason": "stale raw"}
            output = io.StringIO()
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(planner, "runtime_engine_registration_error", return_value=""),
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("formalized", ""),
                ),
                mock.patch.object(
                    planner, "static_closeout_readiness", return_value={"ready": True}
                ),
                mock.patch.object(planner, "_raw_reissue_material_errors", return_value=[]),
                mock.patch.object(
                    planner,
                    "fast_saved_source_record_preflight",
                    return_value=preflight,
                ),
                mock.patch.object(
                    planner, "closeout_raw_reissue_lock_action", return_value=None
                ),
                mock.patch.object(
                    planner,
                    "_try_acquire_closeout_raw_reissue_lock",
                    return_value=(None, "transition lock unreadable"),
                ),
                mock.patch.object(planner, "_archive_raw_reissue_predecessors") as archive,
                mock.patch.object(planner.subprocess, "run") as run,
                contextlib.redirect_stdout(output),
            ):
                result = planner.execute_freeze_then_raw_reissue(folder)

            self.assertEqual(result, 2)
            emitted = json.loads(output.getvalue())
            self.assertEqual(
                emitted["state"], "closeout_raw_reissue_lock_inspection_required"
            )
            self.assertEqual(
                emitted["next_action"]["id"],
                "inspect_closeout_raw_reissue_transition_lock",
            )
            archive.assert_not_called()
            run.assert_not_called()

    def test_raw_reissue_wrapper_reclassifies_lock_race_after_launch(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            raw = audit / "source_record_audit.json"
            judgment = audit / "source_record_match_llm.json"
            raw.write_text('{"old": "raw"}\n', encoding="utf-8")
            judgment.write_text('{"old": "judgment"}\n', encoding="utf-8")
            preflight = {
                "state": "raw_reissue_required",
                "reason": "stale raw",
                "raw_path": str(raw.relative_to(root)),
                "judgment_path": str(judgment.relative_to(root)),
            }
            helper = root / "source_record_audit.py"
            helper.write_text("# fixture\n", encoding="utf-8")
            wait_action = {
                "id": "wait_for_source_record_scan",
                "state": "waiting",
                "required": True,
            }
            proc = types.SimpleNamespace(
                returncode=4,
                stdout="",
                stderr="another source-record audit is already running",
            )
            output = io.StringIO()
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "FAST_SAVED_SOURCE_RECORD_HELPER_RELATIVE",
                    helper.relative_to(root),
                ),
                mock.patch.object(planner, "running_execution_summary", return_value=None),
                mock.patch.object(
                    planner,
                    "effective_closeout_execution_state",
                    return_value=(None, "", "worker", folder / "state.json"),
                ),
                mock.patch.object(planner, "runtime_engine_registration_error", return_value=""),
                mock.patch.object(
                    planner,
                    "_paper_closeout_status_preflight",
                    return_value=("formalized", ""),
                ),
                mock.patch.object(
                    planner, "static_closeout_readiness", return_value={"ready": True}
                ),
                mock.patch.object(planner, "_raw_reissue_material_errors", return_value=[]),
                mock.patch.object(
                    planner,
                    "fast_saved_source_record_preflight",
                    return_value=preflight,
                ),
                mock.patch.object(
                    planner,
                    "source_record_reissue_lock_action",
                    side_effect=[None, wait_action],
                ),
                mock.patch.object(
                    planner,
                    "ensure_closeout_wave_engine_snapshot",
                    return_value=(self.wave_snapshot(), True, ""),
                ),
                mock.patch.object(planner.subprocess, "run", return_value=proc),
                contextlib.redirect_stdout(output),
            ):
                result = planner.execute_freeze_then_raw_reissue(folder)

            self.assertEqual(result, 2)
            emitted = json.loads(output.getvalue())
            self.assertEqual(
                emitted["state"], "raw_reissue_deferred_by_source_record_scan"
            )
            self.assertFalse(emitted["raw_scan_started"])
            self.assertEqual(emitted["next_action"], wait_action)

    def test_closeout_status_preflight_rejects_unrecognized_favorable_prefix(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir)
            (folder / "status.json").write_text(
                '{"status": "formalized-but-unverified"}\n', encoding="utf-8"
            )
            status, error = planner._paper_closeout_status_preflight(folder)
        self.assertEqual(status, "formalized-but-unverified")
        self.assertIn("not eligible", error)

    def test_source_record_preflight_does_not_apply_canonical_helper_to_configured_raw(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (folder / "status.json").write_text("{}\n", encoding="utf-8")
            raw = audit / "noncanonical_raw.json"
            judgment = audit / "configured_judgment.json"
            raw.write_text(
                json.dumps({"source_record_audit_sha256": "a" * 64}),
                encoding="utf-8",
            )
            judgment.write_text(
                json.dumps({"source_record_audit_sha256": "a" * 64}),
                encoding="utf-8",
            )

            def resolve_sidecar(
                _folder: Path,
                _status: dict[str, object],
                *,
                config_field: str,
                default_basename: str,
            ) -> tuple[Path, str]:
                del default_basename
                return (
                    raw if config_field == "source_record_audit_file" else judgment,
                    "",
                )

            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch(
                    "scripts.audit_evidence_integrity.source_record_review_sidecar_path",
                    side_effect=resolve_sidecar,
                ),
                mock.patch.object(planner.subprocess, "run") as run,
            ):
                preflight = planner.fast_saved_source_record_preflight(folder)

            self.assertEqual(preflight["state"], "identity_inspection_required")
            self.assertFalse(preflight["configured_raw_is_canonical"])
            self.assertIn("noncanonical", preflight["reason"])
            run.assert_not_called()

    def test_source_record_preflight_does_not_parse_current_canonical_raw(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (folder / "status.json").write_text("{}\n", encoding="utf-8")
            # The helper owns canonical raw validation. Invalid JSON here proves
            # the planner does not redundantly parse it after helper success.
            (audit / "source_record_audit.json").write_text(
                "this is not planner JSON\n", encoding="utf-8"
            )
            (audit / "source_record_match_llm.json").write_text(
                json.dumps({"source_record_audit_sha256": "a" * 64}),
                encoding="utf-8",
            )
            helper = root / "fast_saved_identity_helper.py"
            helper.write_text("# mocked subprocess target\n", encoding="utf-8")
            proc = types.SimpleNamespace(
                returncode=0,
                stdout=json.dumps(
                    {
                        "current": True,
                        "source_record_audit_sha256": "a" * 64,
                    }
                ),
                stderr="",
            )

            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "FAST_SAVED_SOURCE_RECORD_HELPER_RELATIVE",
                    helper.relative_to(root),
                ),
                mock.patch.object(planner.subprocess, "run", return_value=proc) as run,
            ):
                preflight = planner.fast_saved_source_record_preflight(folder)

            self.assertEqual(preflight["state"], "current_raw_judgment_bound")
            self.assertEqual(preflight["raw_audit_sha256"], "a" * 64)
            self.assertEqual(preflight["judgment_audit_sha256"], "a" * 64)
            self.assertEqual(preflight["raw_fingerprint_schema"], 10)
            run.assert_called_once()

    def test_stale_helper_observation_avoids_a_second_raw_json_parse(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (folder / "status.json").write_text("{}\n", encoding="utf-8")
            # The helper is authoritative for this observed stale raw.  If the
            # planner rereads it, JSON parsing would fail and the test fails.
            (audit / "source_record_audit.json").write_text(
                "not planner JSON\n", encoding="utf-8"
            )
            (audit / "source_record_match_llm.json").write_text(
                json.dumps({"source_record_audit_sha256": "a" * 64}),
                encoding="utf-8",
            )
            helper = root / "fast_saved_identity_helper.py"
            helper.write_text("# mocked subprocess target\n", encoding="utf-8")
            proc = types.SimpleNamespace(
                returncode=1,
                stdout=json.dumps(
                    {
                        "current": False,
                        "identity_scope": "repository_sources_and_configuration_only",
                        "reason": "saved source-record source/configuration identity differs from the current repository",
                        "observed_source_record_audit_sha256": "a" * 64,
                        "observed_source_record_fingerprint_schema": 10,
                        "validation_dimensions": {
                            "source_configuration_identity": {
                                "state": "stale",
                                "reason": "fixture source changed",
                            }
                        },
                    }
                ),
                stderr="",
            )

            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "FAST_SAVED_SOURCE_RECORD_HELPER_RELATIVE",
                    helper.relative_to(root),
                ),
                mock.patch.object(planner.subprocess, "run", return_value=proc),
            ):
                preflight = planner.fast_saved_source_record_preflight(folder)

            self.assertEqual(preflight["state"], "raw_reissue_required")
            self.assertEqual(preflight["raw_audit_sha256"], "a" * 64)
            self.assertEqual(preflight["raw_fingerprint_schema"], 10)

    def test_changed_saved_lean_closure_routes_to_raw_reissue(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (folder / "status.json").write_text("{}\n", encoding="utf-8")
            (audit / "source_record_audit.json").write_text(
                "not planner JSON\n", encoding="utf-8"
            )
            (audit / "source_record_match_llm.json").write_text(
                json.dumps({"source_record_audit_sha256": "a" * 64}),
                encoding="utf-8",
            )
            helper = root / "fast_saved_identity_helper.py"
            helper.write_text("# mocked subprocess target\n", encoding="utf-8")
            proc = types.SimpleNamespace(
                returncode=1,
                stdout=json.dumps(
                    {
                        "current": False,
                        "identity_scope": "repository_sources_and_configuration_only",
                        "reason": (
                            "saved Lean import closure is not current: "
                            "Lean import-closure source bytes changed: "
                            "papers/Fixture/PaperInterface.lean"
                        ),
                        "observed_source_record_audit_sha256": "a" * 64,
                        "observed_source_record_fingerprint_schema": 10,
                        "validation_dimensions": {
                            "raw_receipt_integrity": {"state": "valid"},
                            "generated_semantic_surface": {"state": "valid"},
                            "raw_scan_completeness": {"state": "valid"},
                            "reusable_item_metadata": {"state": "valid"},
                            "raw_bytes": {"state": "unavailable"},
                            "source_configuration_identity": {
                                "state": "stale",
                                "reason": "Lean import-closure source bytes changed",
                            },
                        },
                    }
                ),
                stderr="",
            )

            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "FAST_SAVED_SOURCE_RECORD_HELPER_RELATIVE",
                    helper.relative_to(root),
                ),
                mock.patch.object(planner.subprocess, "run", return_value=proc),
            ):
                preflight = planner.fast_saved_source_record_preflight(folder)

            self.assertEqual(preflight["state"], "raw_reissue_required")
            with (
                mock.patch.object(
                    planner, "closeout_wave_engine_action", return_value=None
                ),
                mock.patch.object(
                    planner, "raw_reissue_transition_lock_action", return_value=None
                ),
            ):
                action = planner.source_record_preflight_action("Fixture", preflight)
            assert action is not None
            self.assertEqual(action["id"], "freeze_then_raw_reissue")

    def test_authenticated_semantic_contract_replay_matches_evidence_gate_identity(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder, proc = self.semantic_contract_replay_fixture(
                root, match_digest="b" * 64
            )
            helper = root / "fast_saved_identity_helper.py"
            helper.write_text("# mocked subprocess target\n", encoding="utf-8")
            projection = object()
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "FAST_SAVED_SOURCE_RECORD_HELPER_RELATIVE",
                    helper.relative_to(root),
                ),
                mock.patch.object(planner.subprocess, "run", return_value=proc),
                mock.patch(
                    "scripts.audit_evidence_integrity.source_record_semantic_contract_revalidation_context",
                    return_value=(projection, ""),
                ) as replay_context,
                mock.patch(
                    "scripts.audit_evidence_integrity.source_record_audit_identity_error",
                    return_value="",
                ) as identity_error,
            ):
                preflight = planner.fast_saved_source_record_preflight(folder)

            self.assertEqual(preflight["state"], "current_raw_judgment_delta")
            self.assertEqual(
                preflight["semantic_contract_revalidation"]["state"], "validated"
            )
            replay_context.assert_called_once()
            identity_error.assert_called_once()
            self.assertIs(
                identity_error.call_args.kwargs["semantic_contract_revalidation"],
                projection,
            )
            self.assertEqual(
                identity_error.call_args.kwargs["expected_paper_statement_map_sha256"],
                hashlib.sha256(b"{}\n").hexdigest(),
            )

    def test_semantic_contract_replay_keeps_stale_identity_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder, proc = self.semantic_contract_replay_fixture(
                root, match_digest="a" * 64
            )
            proc.stdout = json.dumps(
                {
                    "current": False,
                    "identity_scope": "repository_sources_and_configuration_only",
                    "reason": "saved source-record source/configuration identity differs from the current repository",
                    "observed_source_record_audit_sha256": "a" * 64,
                    "observed_source_record_fingerprint_schema": 10,
                    "validation_dimensions": {
                        "source_configuration_identity": {
                            "state": "stale",
                            "reason": "fixture source changed",
                        }
                    },
                }
            )
            helper = root / "fast_saved_identity_helper.py"
            helper.write_text("# mocked subprocess target\n", encoding="utf-8")
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "FAST_SAVED_SOURCE_RECORD_HELPER_RELATIVE",
                    helper.relative_to(root),
                ),
                mock.patch.object(planner.subprocess, "run", return_value=proc),
                mock.patch(
                    "scripts.audit_evidence_integrity.source_record_semantic_contract_revalidation_context",
                    return_value=(object(), ""),
                ),
                mock.patch(
                    "scripts.audit_evidence_integrity.source_record_audit_identity_error",
                    return_value="source_record_input_fingerprint is stale for current source or audit-engine inputs",
                ),
            ):
                preflight = planner.fast_saved_source_record_preflight(folder)

            self.assertEqual(preflight["state"], "raw_reissue_required")
            self.assertEqual(
                preflight["semantic_contract_revalidation"]["state"], "rejected"
            )
            self.assertIn(
                "source_record_input_fingerprint is stale",
                preflight["semantic_contract_revalidation"]["reason"],
            )

    def test_current_raw_with_unreadable_judgment_never_reissues_raw(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (folder / "status.json").write_text("{}\n", encoding="utf-8")
            (audit / "source_record_audit.json").write_text(
                "this raw is deliberately not read by the planner\n", encoding="utf-8"
            )
            (audit / "source_record_match_llm.json").write_text(
                "not JSON\n", encoding="utf-8"
            )
            helper = root / "fast_saved_identity_helper.py"
            helper.write_text("# mocked subprocess target\n", encoding="utf-8")
            proc = types.SimpleNamespace(
                returncode=0,
                stdout=json.dumps(
                    {
                        "current": True,
                        "source_record_audit_sha256": "a" * 64,
                    }
                ),
                stderr="",
            )

            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "FAST_SAVED_SOURCE_RECORD_HELPER_RELATIVE",
                    helper.relative_to(root),
                ),
                mock.patch.object(planner.subprocess, "run", return_value=proc),
            ):
                first = planner.fast_saved_source_record_preflight(folder)
                second = planner.fast_saved_source_record_preflight(folder)

            self.assertEqual(first["state"], "current_raw_judgment_rebuild_required")
            self.assertEqual(second, first)
            action = planner.source_record_preflight_action("Fixture", first)
            assert action is not None
            self.assertEqual(action["id"], "rebuild_current_source_record_judgments")
            self.assertNotIn("argv", action)

    def test_current_raw_with_nonobject_judgment_never_reissues_raw(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (folder / "status.json").write_text("{}\n", encoding="utf-8")
            (audit / "source_record_audit.json").write_text(
                "this raw is deliberately not read by the planner\n", encoding="utf-8"
            )
            (audit / "source_record_match_llm.json").write_text(
                "[]\n", encoding="utf-8"
            )
            helper = root / "fast_saved_identity_helper.py"
            helper.write_text("# mocked subprocess target\n", encoding="utf-8")
            proc = types.SimpleNamespace(
                returncode=0,
                stdout=json.dumps(
                    {
                        "current": True,
                        "source_record_audit_sha256": "a" * 64,
                    }
                ),
                stderr="",
            )

            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "FAST_SAVED_SOURCE_RECORD_HELPER_RELATIVE",
                    helper.relative_to(root),
                ),
                mock.patch.object(planner.subprocess, "run", return_value=proc),
            ):
                preflight = planner.fast_saved_source_record_preflight(folder)

            self.assertEqual(preflight["state"], "current_raw_judgment_rebuild_required")
            action = planner.source_record_preflight_action("Fixture", preflight)
            assert action is not None
            self.assertEqual(action["id"], "rebuild_current_source_record_judgments")
            self.assertNotIn("argv", action)

    def test_all_reuse_schedule_skips_redundant_build_then_runs_closeout(self) -> None:
        schedule = planner.closeout_action_schedule(
            "Fixture",
            cache_reusable=True,
            summary={
                "statement_requires_review": 0,
                "coverage_requires_review": 0,
            },
            validator_identity_errors={"statement": [], "coverage": []},
        )

        self.assertTrue(schedule["semantic_review_reuse_ready"])
        self.assertEqual(
            [action["id"] for action in schedule["actions"]],
            ["strict_closeout"],
        )
        self.assertTrue(all(action["required"] for action in schedule["actions"]))
        self.assertEqual(schedule["next_action"]["id"], "strict_closeout")
        self.assertIn("run_paper_closeout.py", schedule["actions"][-1]["command"])

    def test_unsealed_current_items_do_not_block_existing_paper_closeout(self) -> None:
        schedule = planner.closeout_action_schedule(
            "Fixture",
            cache_reusable=True,
            summary={
                "statement_requires_review": 0,
                "coverage_requires_review": 0,
                "statement_future_reuse_pin_missing": 3,
                "coverage_future_reuse_pin_missing": 1,
            },
            validator_identity_errors={"statement": [], "coverage": []},
        )

        self.assertTrue(schedule["semantic_review_reuse_ready"])
        self.assertFalse(
            schedule["future_reuse_pin_maintenance"]["required_for_this_closeout"]
        )
        self.assertEqual(schedule["future_reuse_pin_maintenance"]["statement_items"], 3)
        self.assertNotIn(
            "refresh_invalid_semantic_items",
            [action["id"] for action in schedule["actions"]],
        )

    def test_same_operational_plan_is_inspected_instead_of_rerun(self) -> None:
        plan_identity = "f" * 64
        prior = {
            "state": "complete",
            "exit_code": 0,
            "result": {
                "operational_plan_identity": plan_identity,
                "operational_plan_identity_schema": (
                    planner.OPERATIONAL_PLAN_IDENTITY_SCHEMA
                ),
                "semantic_closeout_passed": True,
            },
        }
        schedule = planner.closeout_action_schedule(
            "Fixture",
            cache_reusable=True,
            summary={"statement_requires_review": 0, "coverage_requires_review": 0},
            validator_identity_errors={"statement": [], "coverage": []},
            plan_identity=plan_identity,
            prior_execution=prior,
        )
        self.assertEqual(schedule["next_action"]["id"], "inspect_existing_closeout")
        self.assertIn("--status", schedule["next_action"]["argv"])
        self.assertEqual(
            [action["id"] for action in schedule["actions"]],
            ["inspect_existing_closeout"],
        )

        failed_prior = {
            **prior,
            "exit_code": 1,
            "result": {**prior["result"], "semantic_closeout_passed": False},
        }
        failed = planner.closeout_action_schedule(
            "Fixture",
            cache_reusable=True,
            summary={"statement_requires_review": 0, "coverage_requires_review": 0},
            validator_identity_errors={"statement": [], "coverage": []},
            plan_identity=plan_identity,
            prior_execution=failed_prior,
        )
        self.assertEqual(
            [action["id"] for action in failed["actions"]],
            [
                "inspect_existing_closeout",
                "strict_closeout_after_failure_confirmation",
            ],
        )
        self.assertEqual(
            failed["actions"][1]["state"],
            "after_operator_confirms_retry_required",
        )
        self.assertIn("--new-run", failed["actions"][1]["argv"])

        changed = planner.closeout_action_schedule(
            "Fixture",
            cache_reusable=True,
            summary={"statement_requires_review": 0, "coverage_requires_review": 0},
            validator_identity_errors={"statement": [], "coverage": []},
            plan_identity="e" * 64,
            prior_execution=prior,
        )
        self.assertEqual(changed["next_action"]["id"], "strict_closeout")
        self.assertIn("--new-run", changed["next_action"]["argv"])

        recovered = {
            **prior,
            "recovered_from_worker_state": True,
            "request": {
                "operational_plan_identity": plan_identity,
                "operational_plan_identity_schema": (
                    planner.OPERATIONAL_PLAN_IDENTITY_SCHEMA
                ),
            },
        }
        recovered_same = planner.closeout_action_schedule(
            "Fixture",
            cache_reusable=True,
            summary={"statement_requires_review": 0, "coverage_requires_review": 0},
            validator_identity_errors={"statement": [], "coverage": []},
            plan_identity=plan_identity,
            prior_execution=recovered,
        )
        self.assertEqual(
            recovered_same["next_action"]["id"], "inspect_existing_closeout"
        )
        recovered_changed = planner.closeout_action_schedule(
            "Fixture",
            cache_reusable=True,
            summary={"statement_requires_review": 0, "coverage_requires_review": 0},
            validator_identity_errors={"statement": [], "coverage": []},
            plan_identity="d" * 64,
            prior_execution=recovered,
        )
        self.assertEqual(recovered_changed["next_action"]["id"], "strict_closeout")
        self.assertIn("--new-run", recovered_changed["next_action"]["argv"])

        legacy = planner.closeout_action_schedule(
            "Fixture",
            cache_reusable=True,
            summary={"statement_requires_review": 0, "coverage_requires_review": 0},
            validator_identity_errors={"statement": [], "coverage": []},
            plan_identity=plan_identity,
            prior_execution={
                "state": "complete",
                "result": {"operational_plan_identity": plan_identity},
            },
        )
        self.assertEqual(legacy["next_action"]["id"], "inspect_legacy_closeout")
        self.assertNotIn("--new-run", legacy["next_action"]["argv"])

        adopted_change = planner.closeout_action_schedule(
            "Fixture",
            cache_reusable=True,
            summary={"statement_requires_review": 0, "coverage_requires_review": 0},
            validator_identity_errors={"statement": [], "coverage": []},
            plan_identity="e" * 64,
            prior_execution={
                "state": "complete",
                "exit_code": 0,
                "result": {"semantic_closeout_passed": True},
            },
            legacy_adoption={"state": "material_changed"},
        )
        self.assertEqual(adopted_change["next_action"]["id"], "strict_closeout")
        self.assertIn("--new-run", adopted_change["next_action"]["argv"])

        adopted_current = planner.closeout_action_schedule(
            "Fixture",
            cache_reusable=True,
            summary={"statement_requires_review": 0, "coverage_requires_review": 0},
            validator_identity_errors={"statement": [], "coverage": []},
            plan_identity=plan_identity,
            prior_execution={
                "state": "complete",
                "exit_code": 0,
                "result": {"semantic_closeout_passed": True},
            },
            legacy_adoption={"state": "current"},
        )
        self.assertEqual(
            [action["id"] for action in adopted_current["actions"]],
            ["inspect_legacy_closeout"],
        )

    def test_compiled_rebuild_requires_replan_before_closeout(self) -> None:
        schedule = planner.closeout_action_schedule(
            "Fixture",
            cache_reusable=True,
            compiled_artifacts_ready=False,
            summary={"statement_requires_review": 0, "coverage_requires_review": 0},
            validator_identity_errors={"statement": [], "coverage": []},
        )
        self.assertEqual(
            [action["id"] for action in schedule["actions"]],
            ["paper_build", "replan_after_build"],
        )
        self.assertEqual(schedule["next_action"]["id"], "paper_build")

    def test_deep_mode_is_preserved_in_strict_closeout_argv(self) -> None:
        schedule = planner.closeout_action_schedule(
            "Fixture",
            cache_reusable=True,
            compiled_artifacts_ready=True,
            summary={"statement_requires_review": 0, "coverage_requires_review": 0},
            validator_identity_errors={"statement": [], "coverage": []},
            deep_paper_prose=True,
        )
        self.assertIn("--deep-paper-prose", schedule["next_action"]["argv"])

    def test_static_readiness_stops_before_expensive_work_and_is_legacy_safe(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "docs").mkdir()
            for relative in (
                "status.json",
                "audit/paper_statement_map.json",
                "FINAL_VALIDATION_REPORT.md",
                "docs/DependencyDAG.tex",
                "docs/DependencyDAG.pdf",
            ):
                (folder / relative).write_text("{}", encoding="utf-8")
            (folder / "docs" / "AGENT_SOURCE_AUDIT.md").write_text(
                "## Overall status: PASS\n"
                "This is an independent source-first audit and does not merely "
                "summarize existing sidecars.\n"
                "It constructs a source inventory from the source itself and compares "
                "the Lean interface for omissions, hidden strengthening/weakening, "
                "and semantic mismatches.\n",
                encoding="utf-8",
            )
            (folder / "PaperInterface.lean").write_text(
                "/- sorry in a comment -/\ntheorem ready : True := by trivial\n",
                encoding="utf-8",
            )
            (root / "papers" / "Fixture.lean").write_text(
                "import Fixture.PaperInterface\n", encoding="utf-8"
            )
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "_paper_predates_intake_freeze_baseline",
                    return_value=True,
                ),
            ):
                readiness = planner.static_closeout_readiness(folder)
            self.assertTrue(readiness["ready"])
            self.assertEqual(
                readiness["lanes"]["prospective_intake_freeze"]["state"],
                "legacy_not_configured",
            )

            (folder / "PaperInterface.lean").write_text(
                "theorem blocked : True := by sorry\n", encoding="utf-8"
            )
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "_paper_predates_intake_freeze_baseline",
                    return_value=True,
                ),
            ):
                readiness = planner.static_closeout_readiness(folder)
            self.assertFalse(readiness["ready"])
            self.assertTrue(
                any("Lean placeholder" in blocker for blocker in readiness["blockers"])
            )

    def test_static_readiness_stops_before_intake_for_strict_document_error(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "docs").mkdir()
            for relative in (
                "status.json",
                "audit/paper_statement_map.json",
                "FINAL_VALIDATION_REPORT.md",
                "docs/DependencyDAG.tex",
                "docs/DependencyDAG.pdf",
            ):
                (folder / relative).write_text("{}", encoding="utf-8")
            (folder / "PaperInterface.lean").write_text(
                "theorem ready : True := by trivial\n", encoding="utf-8"
            )
            (root / "papers" / "Fixture.lean").write_text(
                "import Fixture.PaperInterface\n", encoding="utf-8"
            )
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "intake_freeze_readiness",
                    return_value={"ready": True, "errors": []},
                ) as intake,
            ):
                readiness = planner.static_closeout_readiness(folder)

            self.assertFalse(readiness["ready"])
            self.assertEqual(
                readiness["lanes"]["prospective_intake_freeze"]["state"],
                "deferred_due_to_static_blocker",
            )
            self.assertTrue(
                any("AGENT_SOURCE_AUDIT.md" in blocker for blocker in readiness["blockers"])
            )
            intake.assert_not_called()

    def test_static_readiness_uses_corrected_scope_only_for_source_audit_exception(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "docs").mkdir()
            for relative, contents in (
                ("status.json", '{"status": "formalized"}\n'),
                ("audit/paper_statement_map.json", "{}\n"),
                (
                    "FINAL_VALIDATION_REPORT.md",
                    "## Closeout Status\n- Completion status: formalized.\n",
                ),
                ("docs/DependencyDAG.tex", "% fixture\n"),
            ):
                (folder / relative).write_text(contents, encoding="utf-8")
            (folder / "docs" / "DependencyDAG.pdf").write_bytes(b"fixture")
            (folder / "PaperInterface.lean").write_text(
                "theorem ready : True := by trivial\n", encoding="utf-8"
            )
            (root / "papers" / "Fixture.lean").write_text(
                "import Fixture.PaperInterface\n", encoding="utf-8"
            )
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner, "_planner_corrected_scope_current", return_value=True
                ) as corrected_scope,
                mock.patch.object(
                    planner,
                    "intake_freeze_readiness",
                    return_value={"ready": True, "errors": []},
                ) as intake,
            ):
                readiness = planner.static_closeout_readiness(folder)

            self.assertTrue(readiness["ready"])
            corrected_scope.assert_called_once()
            intake.assert_called_once_with(folder)

    def test_static_readiness_blocks_controlled_report_status_mismatch(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            (folder / "audit").mkdir(parents=True)
            (folder / "docs").mkdir()
            (folder / "PaperInterface.lean").write_text(
                "theorem ready : True := by trivial\n", encoding="utf-8"
            )
            (folder / "status.json").write_text(
                '{"status": "formalized"}\n', encoding="utf-8"
            )
            (folder / "audit" / "paper_statement_map.json").write_text(
                "{}\n", encoding="utf-8"
            )
            (folder / "FINAL_VALIDATION_REPORT.md").write_text(
                "## 2. Closeout Status\n"
                "- Completion status: partially formalized.\n",
                encoding="utf-8",
            )
            (folder / "docs" / "DependencyDAG.tex").write_text(
                "% fixture\n", encoding="utf-8"
            )
            (folder / "docs" / "DependencyDAG.pdf").write_bytes(b"fixture")
            (root / "papers" / "Fixture.lean").write_text(
                "import Fixture.PaperInterface\n", encoding="utf-8"
            )
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner, "intake_freeze_readiness", return_value={"errors": []}
                ) as intake,
            ):
                readiness = planner.static_closeout_readiness(folder)

            self.assertFalse(readiness["ready"])
            errors = readiness["lanes"]["final_validation_report_status"]["errors"]
            self.assertEqual(len(errors), 1)
            self.assertIn("declares `partially formalized`", errors[0])
            self.assertTrue(
                any(
                    "final validation report/status alignment" in blocker
                    for blocker in readiness["blockers"]
                )
            )
            intake.assert_not_called()

    def test_intake_marker_grandfathers_only_status_files_without_the_field(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            folder.mkdir(parents=True)
            status = folder / "status.json"
            status.write_text("{}", encoding="utf-8")
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "_paper_predates_intake_freeze_baseline",
                    return_value=True,
                ),
            ):
                legacy = planner._intake_freeze_readiness(folder)
            self.assertTrue(legacy["ready"])
            self.assertEqual(legacy["state"], "legacy_not_configured")

            status.write_text(
                json.dumps({"intake_freeze_required": True}), encoding="utf-8"
            )
            with mock.patch.object(planner, "ROOT", root):
                missing = planner._intake_freeze_readiness(folder)
            self.assertFalse(missing["ready"])
            self.assertEqual(missing["state"], "missing")

            status.write_text(
                json.dumps({"intake_freeze_required": False}), encoding="utf-8"
            )
            with mock.patch.object(planner, "ROOT", root):
                disabled = planner._intake_freeze_readiness(folder)
            self.assertFalse(disabled["ready"])
            self.assertTrue(
                any("exactly true" in error for error in disabled["errors"])
            )

    def test_new_scaffold_cannot_downgrade_by_deleting_its_intake_seal(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (folder / "status.json").write_text("{}", encoding="utf-8")
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "_paper_predates_intake_freeze_baseline",
                    return_value=False,
                ),
            ):
                readiness = planner._intake_freeze_readiness(folder)
            self.assertFalse(readiness["ready"])
            self.assertEqual(readiness["state"], "prospective_marker_missing")

    def test_prospective_intake_atoms_are_bound_to_current_source_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            artifact = folder / "source.txt"
            artifact_bytes = b"prefix Theorem X. suffix"
            artifact.write_bytes(artifact_bytes)
            statement = "Theorem X."
            mapped_statement = "Theorem   X.\n"
            artifact_digest = hashlib.sha256(artifact_bytes).hexdigest()
            (folder / "status.json").write_text(
                json.dumps({"intake_freeze_required": True}), encoding="utf-8"
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_artifact_path": "papers/Fixture/source.txt",
                        "source_artifact_sha256": artifact_digest,
                        "items": {
                            "opaque_map_key": {
                                "source_item": "A label that need not match",
                                "source_location": "line 1",
                                "statement": mapped_statement,
                            }
                        },
                    }
                )
            )
            start = artifact_bytes.index(statement.encode())
            payload = {
                "schema": 1,
                "paper": "Fixture",
                "state": "sealed",
                "inventory_complete": True,
                "source_item_identity": planner.INTAKE_SOURCE_IDENTITY,
                "source_artifact_path": "papers/Fixture/source.txt",
                "source_artifact_sha256": artifact_digest,
                "items": [
                    {
                        "source_item": "Unrelated navigation label",
                        "source_location": "line 1",
                        "source_statement_sha256": hashlib.sha256(
                            statement.encode()
                        ).hexdigest(),
                        "dependency_order": 1,
                        "owner": "proof-agent",
                        "acceptance_conditions": ["prove the exact target"],
                        "source_atoms": [
                            {
                                "source_location": "line 1",
                                "quoted_text": "invented",
                                "quoted_text_sha256": hashlib.sha256(
                                    b"invented"
                                ).hexdigest(),
                                "byte_start": start,
                                "byte_end": start + len(statement),
                            }
                        ],
                    }
                ],
            }
            freeze = audit / "intake_freeze.json"
            freeze.write_text(json.dumps(payload))
            with mock.patch.object(planner, "ROOT", root):
                rejected = planner._intake_freeze_readiness(folder)
            self.assertFalse(rejected["ready"])

            payload["items"][0]["source_atoms"][0].update(
                {
                    "quoted_text": statement,
                    "quoted_text_sha256": hashlib.sha256(
                        statement.encode()
                    ).hexdigest(),
                }
            )
            freeze.write_text(json.dumps(payload))
            with mock.patch.object(planner, "ROOT", root):
                accepted = planner._intake_freeze_readiness(folder)
            self.assertTrue(accepted["ready"], accepted["errors"])

            payload["items"][0]["acceptance_conditions"] = []
            freeze.write_text(json.dumps(payload))
            with mock.patch.object(planner, "ROOT", root):
                empty_acceptance = planner._intake_freeze_readiness(folder)
            self.assertFalse(empty_acceptance["ready"])
            self.assertTrue(
                any(
                    "incomplete acceptance conditions" in error
                    for error in empty_acceptance["errors"]
                )
            )
            payload["items"][0]["acceptance_conditions"] = ["prove the exact target"]
            freeze.write_text(json.dumps(payload))

            source_map_path = audit / "paper_statement_map.json"
            current_map = json.loads(source_map_path.read_text(encoding="utf-8"))
            current_map["items"]["second"] = {
                "source_item": "Theorem Y",
                "source_location": "line 2",
                "statement": "Theorem Y.",
            }
            source_map_path.write_text(json.dumps(current_map), encoding="utf-8")
            with mock.patch.object(planner, "ROOT", root):
                incomplete_inventory = planner._intake_freeze_readiness(folder)
            self.assertFalse(incomplete_inventory["ready"])
            self.assertTrue(
                any(
                    "exactly equal the current source-map inventory" in error
                    for error in incomplete_inventory["errors"]
                )
            )
            del current_map["items"]["second"]
            source_map_path.write_text(json.dumps(current_map), encoding="utf-8")

            payload["source_artifact_path"] = "papers/Fixture/not-canonical.txt"
            freeze.write_text(json.dumps(payload))
            with mock.patch.object(planner, "ROOT", root):
                wrong_artifact = planner._intake_freeze_readiness(folder)
            self.assertFalse(wrong_artifact["ready"])
            self.assertTrue(
                any(
                    "canonical source-map identity" in error
                    for error in wrong_artifact["errors"]
                )
            )

            payload["source_artifact_path"] = "papers/Fixture/source.txt"
            payload["items"][0]["source_location"] = "line 2"
            freeze.write_text(json.dumps(payload))
            with mock.patch.object(planner, "ROOT", root):
                wrong_location = planner._intake_freeze_readiness(folder)
            self.assertFalse(wrong_location["ready"])
            self.assertTrue(
                any(
                    "location and normalized statement" in error
                    for error in wrong_location["errors"]
                )
            )

    def test_pdf_intake_atoms_use_bound_normalized_text_not_pdf_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            pdf_bytes = b"%PDF-1.7 compressed bytes without the theorem"
            text_bytes = b"prefix Theorem X. suffix\n"
            pdf = folder / "source.pdf"
            text_artifact = folder / "source.txt"
            pdf.write_bytes(pdf_bytes)
            text_artifact.write_bytes(text_bytes)
            pdf_digest = hashlib.sha256(pdf_bytes).hexdigest()
            text_digest = hashlib.sha256(text_bytes).hexdigest()
            statement = "Theorem X."
            statement_digest = planner.review_dashboard.statement_digest(statement)
            (folder / "status.json").write_text(
                json.dumps({"intake_freeze_required": True}), encoding="utf-8"
            )
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_artifact_path": "papers/Fixture/source.pdf",
                        "source_artifact_sha256": pdf_digest,
                        "items": {
                            "x": {
                                "source_location": "Theorem 1, p. 2",
                                "statement": statement,
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            start = text_bytes.index(statement.encode("utf-8"))
            payload = {
                "schema": 1,
                "paper": "Fixture",
                "state": "sealed",
                "inventory_complete": True,
                "source_item_identity": planner.INTAKE_SOURCE_IDENTITY,
                "source_artifact_path": "papers/Fixture/source.pdf",
                "source_artifact_sha256": pdf_digest,
                "source_text_artifact": {
                    "schema": 1,
                    "path": "papers/Fixture/source.txt",
                    "sha256": text_digest,
                    "normalization": "utf8-lf-v1",
                    "extraction": {
                        "schema": 1,
                        "source_artifact_path": "papers/Fixture/source.pdf",
                        "source_artifact_sha256": pdf_digest,
                        "tool": "pdftotext",
                        "options": [],
                    },
                },
                "items": [
                    {
                        "source_item": "navigation-only label",
                        "source_location": "Theorem 1, p. 2",
                        "source_statement_sha256": statement_digest,
                        "dependency_order": 1,
                        "owner": "proof-agent",
                        "acceptance_conditions": ["prove the exact target"],
                        "source_atoms": [
                            {
                                "source_location": "Theorem 1, p. 2",
                                "quoted_text": statement,
                                "quoted_text_sha256": hashlib.sha256(
                                    statement.encode("utf-8")
                                ).hexdigest(),
                                "byte_start": start,
                                "byte_end": start + len(statement.encode("utf-8")),
                            }
                        ],
                    }
                ],
            }
            freeze = audit / "intake_freeze.json"
            freeze.write_text(json.dumps(payload), encoding="utf-8")
            with mock.patch.object(planner, "ROOT", root):
                accepted = planner._intake_freeze_readiness(folder)
            self.assertTrue(accepted["ready"], accepted["errors"])

            del payload["source_text_artifact"]
            freeze.write_text(json.dumps(payload), encoding="utf-8")
            with mock.patch.object(planner, "ROOT", root):
                missing_receipt = planner._intake_freeze_readiness(folder)
            self.assertFalse(missing_receipt["ready"])
            self.assertTrue(
                any(
                    "normalized source-text" in error
                    for error in missing_receipt["errors"]
                )
            )

    def test_advisory_plan_cache_is_non_authoritative_and_mutation_guarded(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            trace = folder / ".review_traces"
            artifact = root / "Fixture.olean"
            trace.mkdir(parents=True)
            artifact.write_bytes(b"olean")
            stat = artifact.stat()
            artifact_identity = (
                stat.st_dev,
                stat.st_ino,
                stat.st_size,
                stat.st_mtime_ns,
                stat.st_ctime_ns,
            )
            semantic_plan = {
                "acceptance_credential": False,
                "requires_fresh_strict_closeout": True,
                "cache_reusable": True,
                "compiled_artifacts_ready": True,
                "statement": {},
                "coverage": {},
                "summary": {
                    "statement_requires_review": 0,
                    "coverage_requires_review": 0,
                },
                "validator_identity_errors": {"statement": [], "coverage": []},
            }
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "validate_lean_closure_operational_projection",
                    return_value={"state": "present"},
                ),
            ):
                planner._write_advisory_plan_cache(
                    folder,
                    input_identity_sha256="a" * 64,
                    input_material={"schema": 1},
                    semantic_plan=semantic_plan,
                    source_artifact_mutation_snapshot={
                        str(folder / "PaperInterface.lean"): None
                    },
                    compiled_artifact_mutation_snapshot={
                        str(artifact): artifact_identity
                    },
                    strict_transaction_content_snapshot={},
                    lean_import_closure_projection={"state": "present"},
                )
                planner._write_compiled_input_cache(
                    folder,
                    planner.compiled_input_snapshot(root, [artifact]),
                )
                loaded = planner._read_advisory_plan_cache(folder, "a" * 64)
            self.assertIsNotNone(loaded)
            assert loaded is not None
            self.assertTrue(loaded["compiled_artifacts_ready"])
            self.assertFalse(loaded["acceptance_credential"])

            artifact.unlink()
            artifact.write_bytes(b"olean")
            os.utime(
                artifact,
                ns=(artifact.stat().st_atime_ns, artifact_identity[3] + 1_000_000_000),
            )
            with mock.patch.object(planner, "ROOT", root):
                prior_compiled = planner._load_compiled_input_cache(folder)
            self.assertIsNotNone(prior_compiled)
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "compiled_input_snapshot",
                    wraps=planner.compiled_input_snapshot,
                ) as refresh,
                mock.patch.object(
                    planner,
                    "validate_lean_closure_operational_projection",
                    return_value={"state": "present"},
                ),
            ):
                rebuilt_same = planner._read_advisory_plan_cache(folder, "a" * 64)
            refresh.assert_called_once()
            self.assertIsNotNone(rebuilt_same)

            artifact.write_bytes(b"changed")
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "validate_lean_closure_operational_projection",
                    return_value={"state": "present"},
                ),
            ):
                changed = planner._read_advisory_plan_cache(folder, "a" * 64)
            self.assertIsNone(changed)

    def test_advisory_cache_persists_refreshed_external_artifact_guards(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            (folder / ".review_traces").mkdir(parents=True)
            semantic_plan = {
                "acceptance_credential": False,
                "requires_fresh_strict_closeout": True,
                "compiled_artifacts_ready": True,
                "statement": {},
                "coverage": {},
                "summary": {
                    "statement_requires_review": 0,
                    "coverage_requires_review": 0,
                },
                "validator_identity_errors": {"statement": [], "coverage": []},
            }
            old_projection = {
                "state": "present",
                "external_artifact_stats": {"guard": "old"},
            }
            refreshed_projection = {
                "state": "present",
                "external_artifact_stats": {"guard": "current"},
            }
            with mock.patch.object(planner, "ROOT", root):
                planner._write_advisory_plan_cache(
                    folder,
                    input_identity_sha256="a" * 64,
                    input_material={"schema": 1},
                    semantic_plan=semantic_plan,
                    source_artifact_mutation_snapshot={},
                    compiled_artifact_mutation_snapshot={},
                    strict_transaction_content_snapshot={},
                    lean_import_closure_projection=old_projection,
                )

            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "validate_lean_closure_operational_projection",
                    return_value=refreshed_projection,
                ),
            ):
                first = planner._read_advisory_plan_cache(folder, "a" * 64)
            self.assertIsNotNone(first)
            cache_path = planner._advisory_plan_cache_path(folder)
            persisted = json.loads(cache_path.read_text(encoding="utf-8"))
            self.assertEqual(
                persisted["lean_import_closure_projection"], refreshed_projection
            )

            def validate_persisted(_root: Path, recorded: object) -> object:
                self.assertEqual(recorded, refreshed_projection)
                return recorded

            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "validate_lean_closure_operational_projection",
                    side_effect=validate_persisted,
                ) as validate,
            ):
                second = planner._read_advisory_plan_cache(folder, "a" * 64)
            self.assertIsNotNone(second)
            validate.assert_called_once()

    def test_advisory_cache_uses_small_external_tool_projection(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir) / "repository"
            root.mkdir()
            folder = root / "papers" / "Fixture"
            (folder / ".review_traces").mkdir(parents=True)
            tool = Path(temp_dir) / "sha256sum"
            tool.write_bytes(b"tool")
            stat = tool.stat()
            identity = (
                stat.st_dev,
                stat.st_ino,
                stat.st_size,
                stat.st_mtime_ns,
                stat.st_ctime_ns,
            )
            contexts = self.signature_context(schema=3)
            contexts["semantic_hash_tool_identity"] = {
                "schema": "1",
                "resolved_path": str(tool.resolve()),
                "executable_sha256": "d" * 64,
            }
            projection = planner._declared_semantic_hash_tool_projection(
                {"PaperInterface.lean": contexts}
            )
            semantic_plan = {
                "acceptance_credential": False,
                "requires_fresh_strict_closeout": True,
                "compiled_artifacts_ready": True,
                "statement": {},
                "coverage": {},
                "summary": {
                    "statement_requires_review": 0,
                    "coverage_requires_review": 0,
                },
                "validator_identity_errors": {"statement": [], "coverage": []},
            }
            with mock.patch.object(planner, "ROOT", root):
                planner._write_advisory_plan_cache(
                    folder,
                    input_identity_sha256="a" * 64,
                    input_material={"schema": 1},
                    semantic_plan=semantic_plan,
                    source_artifact_mutation_snapshot={},
                    compiled_artifact_mutation_snapshot={str(tool.resolve()): identity},
                    strict_transaction_content_snapshot={},
                    lean_import_closure_projection={"state": "present"},
                    declared_external_tool_projection=projection,
                )
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "validate_lean_closure_operational_projection",
                    return_value={"state": "present"},
                ),
                mock.patch.object(
                    planner,
                    "_dashboard_signature_contexts",
                    side_effect=AssertionError("dashboard body must not be read"),
                ),
            ):
                loaded = planner._read_advisory_plan_cache(folder, "a" * 64)
            self.assertIsNotNone(loaded)
            assert loaded is not None
            self.assertEqual(loaded["_execution_compiled_artifact_mutation_snapshot"], {})

    def test_advisory_cache_persists_current_input_guards_after_same_bytes(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            (folder / ".review_traces").mkdir(parents=True)
            dashboard = root / "dashboard.json"
            dashboard.write_bytes(b"large-cache-fixture")
            original_guard = planner._stat_identity(dashboard.stat())
            dashboard_digest = hashlib.sha256(dashboard.read_bytes()).hexdigest()
            input_material = {
                "schema": 1,
                "dashboard_cache": {
                    str(dashboard): {
                        "state": "present",
                        "sha256": dashboard_digest,
                    }
                },
                "_mutation_snapshot": {str(dashboard): original_guard},
            }
            semantic_plan = {
                "acceptance_credential": False,
                "requires_fresh_strict_closeout": True,
                "compiled_artifacts_ready": True,
                "statement": {},
                "coverage": {},
                "summary": {
                    "statement_requires_review": 0,
                    "coverage_requires_review": 0,
                },
                "validator_identity_errors": {"statement": [], "coverage": []},
            }
            with mock.patch.object(planner, "ROOT", root):
                planner._write_advisory_plan_cache(
                    folder,
                    input_identity_sha256="a" * 64,
                    input_material=input_material,
                    semantic_plan=semantic_plan,
                    source_artifact_mutation_snapshot={},
                    compiled_artifact_mutation_snapshot={},
                    strict_transaction_content_snapshot={},
                    lean_import_closure_projection={"state": "present"},
                )

            os.utime(
                dashboard,
                ns=(
                    dashboard.stat().st_atime_ns,
                    original_guard[3] + 1_000_000_000,
                ),
            )
            current_guard = planner._stat_identity(dashboard.stat())
            self.assertNotEqual(current_guard, original_guard)
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner,
                    "validate_lean_closure_operational_projection",
                    return_value={"state": "present"},
                ),
            ):
                loaded = planner._read_advisory_plan_cache(
                    folder,
                    "a" * 64,
                    current_input_mutation_snapshot={str(dashboard): current_guard},
                )
                reused = planner._reusable_dashboard_material_snapshot(
                    folder, dashboard
                )
            self.assertIsNotNone(loaded)
            self.assertIsNotNone(reused)
            cache_path = planner._advisory_plan_cache_path(folder)
            persisted = json.loads(cache_path.read_text(encoding="utf-8"))
            self.assertEqual(
                persisted["input_mutation_snapshot"][str(dashboard)],
                list(current_guard),
            )

    def test_unchanged_large_dashboard_digest_is_reused_by_stat_guard(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            trace = folder / ".review_traces"
            trace.mkdir(parents=True)
            dashboard = root / "dashboard.json"
            dashboard.write_bytes(b"large-cache-fixture")
            stat = planner._stat_identity(dashboard.stat())
            payload = {
                "schema": planner.ADVISORY_PLAN_CACHE_SCHEMA,
                "decision_contract": planner.ADVISORY_PLAN_DECISION_CONTRACT,
                "input_material": {
                    "dashboard_cache": {
                        str(dashboard): {
                            "state": "present",
                            "sha256": hashlib.sha256(
                                dashboard.read_bytes()
                            ).hexdigest(),
                        }
                    }
                },
                "input_mutation_snapshot": {str(dashboard): list(stat)},
            }
            with mock.patch.object(planner, "ROOT", root):
                planner.atomic_write_json(
                    planner._advisory_plan_cache_path(folder), payload
                )
                reused = planner._reusable_dashboard_material_snapshot(
                    folder, dashboard
                )
            self.assertIsNotNone(reused)
            assert reused is not None
            self.assertEqual(reused[str(dashboard)]["stat"], list(stat))

            dashboard.write_bytes(b"changed-cache")
            with mock.patch.object(planner, "ROOT", root):
                self.assertIsNone(
                    planner._reusable_dashboard_material_snapshot(folder, dashboard)
                )

    def test_closeout_input_selection_does_not_walk_ambient_files(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            (root / "EconCSLib").mkdir()
            (folder / "audit").mkdir(parents=True)
            (folder / "docs").mkdir()
            (folder / "status.json").write_text("{}")
            (folder / "audit" / "paper_statement_map.json").write_text('{"items": {}}')
            (folder / "FINAL_VALIDATION_REPORT.md").write_text("ready\n")
            unrelated = root / "EconCSLib" / "Unrelated.lean"
            unrelated.write_text("def unrelated := 1\n")
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    planner.review_dashboard,
                    "required_dashboard_audit_input_paths",
                    return_value=(),
                ),
            ):
                content_paths, stat_paths = planner._closeout_plan_input_paths(
                    folder,
                    strict_transaction_content_snapshot={},
                )
            self.assertIn(folder / "FINAL_VALIDATION_REPORT.md", content_paths)
            self.assertNotIn(unrelated, content_paths)
            self.assertNotIn(unrelated, stat_paths)

    def test_strict_input_inventory_uses_evidence_roles_for_engine_code(
        self,
    ) -> None:
        from scripts import audit_evidence_integrity

        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            folder = root / "papers" / "Fixture"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            selected = audit / "source_record_audit.json"
            selected.write_text("{}", encoding="utf-8")
            missing_candidate = folder / "source.pdf"
            operational_py = root / "scripts" / "operational.py"
            operational_lean = root / "scripts" / "operational.lean"
            operational_sh = root / "scripts" / "operational.sh"
            raw_producer = (
                root
                / "skills"
                / "econcs-formalizer"
                / "scripts"
                / "raw_producer.py"
            )
            paper_lean = folder / "MainTheorems.lean"
            for candidate in (
                operational_py,
                operational_lean,
                operational_sh,
                raw_producer,
                paper_lean,
            ):
                candidate.parent.mkdir(parents=True, exist_ok=True)
                candidate.write_text("-- fixture\n", encoding="utf-8")
            context = types.SimpleNamespace(
                input_snapshots=(types.SimpleNamespace(path=selected),),
                audit_payload={
                    "source_record_input_fingerprint": {
                        "raw_producer_code_identities": [
                            {
                                "path": (
                                    "skills/econcs-formalizer/scripts/"
                                    "raw_producer.py#fresh-surface"
                                ),
                                "sha256": "a" * 64,
                                "status": "present",
                            }
                        ]
                    }
                },
            )
            with (
                mock.patch.object(planner, "ROOT", root),
                mock.patch.object(
                    audit_evidence_integrity,
                    "build_evidence_run_context",
                    return_value=context,
                ),
                mock.patch.object(
                    audit_evidence_integrity,
                    "_fingerprint_identity_watch_paths",
                    return_value=(
                        {
                            operational_py,
                            operational_lean,
                            operational_sh,
                            raw_producer,
                            paper_lean,
                        },
                        [],
                    ),
                ),
                mock.patch.object(
                    audit_evidence_integrity,
                    "_source_record_identity_declared_watch_paths",
                    return_value=({missing_candidate}, []),
                ),
            ):
                snapshot, error = planner._strict_transaction_content_snapshot(folder)
            self.assertEqual(error, "")
            assert snapshot is not None
            self.assertIn("papers/Fixture/source.pdf", snapshot)
            self.assertIn(
                "skills/econcs-formalizer/scripts/raw_producer.py", snapshot
            )
            self.assertIn("papers/Fixture/MainTheorems.lean", snapshot)
            self.assertNotIn("scripts/operational.py", snapshot)
            self.assertNotIn("scripts/operational.lean", snapshot)
            self.assertNotIn("scripts/operational.sh", snapshot)


if __name__ == "__main__":
    unittest.main()
