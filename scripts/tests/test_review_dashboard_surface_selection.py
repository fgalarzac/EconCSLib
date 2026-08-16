#!/usr/bin/env python3
"""Focused tests for review-surface-aware Lean elaboration."""

from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from collections import Counter
from pathlib import Path
from unittest import mock

from scripts import review_dashboard


class ReviewDashboardSurfaceSelectionTests(unittest.TestCase):
    @staticmethod
    def _manifest(name: str) -> dict[str, object]:
        return {"sha256": f"manifest:{name}"}

    def test_corrected_target_uses_exact_qualified_route_before_short_source_key(self) -> None:
        """A corrected endpoint must not fall back to its archival short-name key."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "CorrectedPaper"
            folder.mkdir()
            interface = folder / "PaperInterface.lean"
            interface.write_text(
                "namespace CorrectedPaper\n"
                "theorem corrected_endpoint : True := by trivial\n"
                "end CorrectedPaper\n",
                encoding="utf-8",
            )
            (folder / "status.json").write_text(
                json.dumps(
                    {"review_surface": {"include_names": ["corrected_endpoint"]}}
                ),
                encoding="utf-8",
            )
            audit = folder / "audit"
            audit.mkdir()
            archival = "The archival statement."
            corrected = "The approved corrected statement."
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "items": {
                            "corrected_endpoint": {
                                "statement": archival,
                                "coverage_status": "corrected_source_statement",
                                "lean_declarations": [
                                    "CorrectedPaper.corrected_endpoint"
                                ],
                                "corrected_target": {"schema": 1, "statement": corrected},
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )

            def check_rows(
                _paper_folder: Path,
                names: list[str],
                _timeout_seconds: int = review_dashboard.AGENT_PREVIEW_CHECK_TIMEOUT,
                source_file: Path | None = None,
            ) -> dict[str, str]:
                del source_file
                return {name: "True" for name in names}

            def manifest_rows(
                _root: Path,
                _import_module: str,
                names: list[str],
                timeout_seconds: int = 120,
                build_timeout_seconds: int = 600,
                *,
                semantic_dependency_modules: tuple[str, ...] | None = None,
                build_input_provider: object | None = None,
                manifest_checkpoint: object | None = None,
            ) -> dict[str, dict[str, object]]:
                del timeout_seconds, build_timeout_seconds, manifest_checkpoint
                self.assertTrue(semantic_dependency_modules)
                self.assertIsNotNone(build_input_provider)
                return {name: self._manifest(name) for name in names}

            cache_key = str(folder.resolve())
            review_dashboard.SIGNATURE_MANIFEST_CACHE.pop(cache_key, None)

            with (
                mock.patch.object(
                    review_dashboard,
                    "run_lean_check_previews",
                    side_effect=check_rows,
                ),
                mock.patch.object(
                    review_dashboard,
                    "run_lean_signature_manifests",
                    side_effect=manifest_rows,
                ),
                mock.patch.object(
                    review_dashboard,
                    "paper_owned_module_names_in_import_closure",
                    side_effect=lambda _root, _folder, module, **_kwargs: (module,),
                ),
            ):
                items = review_dashboard.parse_interface_items(interface, None, folder)

            self.assertEqual(len(items), 1)
            self.assertEqual(items[0].paper_statement, corrected)
            review_dashboard.SIGNATURE_MANIFEST_CACHE.pop(cache_key, None)

    def test_parser_keeps_the_full_theorem_type_after_an_inner_let_assignment(self) -> None:
        """An inner `let :=` must not truncate the declaration reuse binding."""

        with tempfile.TemporaryDirectory() as temp_dir:
            interface = Path(temp_dir) / "PaperInterface.lean"
            interface.write_text(
                "namespace Fixture\n"
                "theorem endpoint (x : Nat) :\n"
                "    (let rho : Nat := x; rho = x) ∧ True := by\n"
                "  simp\n"
                "theorem unparenthesized :\n"
                "    let rho : Nat := 0; rho = 0 ∧ True := by\n"
                "  simp\n"
                "end Fixture\n",
                encoding="utf-8",
            )
            parsed = review_dashboard.parse_review_source_declarations(interface)

        endpoint = next(row for row in parsed if row[1] == "endpoint")
        self.assertIn("let rho : Nat := x; rho = x", endpoint[3])
        self.assertIn("∧ True", endpoint[3])
        self.assertNotIn(":= by", endpoint[3])
        unparenthesized = next(row for row in parsed if row[1] == "unparenthesized")
        self.assertIn("let rho : Nat := 0; rho = 0 ∧ True", unparenthesized[3])
        self.assertNotIn(":= by", unparenthesized[3])

    def test_direct_map_route_rebinds_stale_cache_statement_without_lean_work(self) -> None:
        """A current explicit route repairs an old comment-backed cache row."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "CacheInvariantPaper"
            folder.mkdir()
            interface = folder / "PaperInterface.lean"
            interface.write_text(
                "namespace CacheInvariantPaper\n"
                "/-- Obsolete dashboard comment. -/\n"
                "theorem endpoint : True := by trivial\n"
                "end CacheInvariantPaper\n",
                encoding="utf-8",
            )
            audit = folder / "audit"
            audit.mkdir()
            source_statement = "The source's displayed endpoint has the exact stated form."
            (audit / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "items": {
                            "source_formula": {
                                "statement": source_statement,
                                "source_kind": "formula",
                                "claim_bearing": False,
                                "lean_declarations": [
                                    "CacheInvariantPaper.endpoint"
                                ],
                            }
                        }
                    }
                ),
                encoding="utf-8",
            )
            parsed = review_dashboard.parse_review_source_declarations(interface)
            kind, name, full_name, raw_signature, *_rest = next(
                row for row in parsed if row[1] == "endpoint"
            )
            stale = review_dashboard.ReviewItem(
                name=name,
                kind=kind,
                lean_statement=raw_signature,
                paper_statement="Obsolete dashboard comment.",
                agent_statement="An old draft.",
                full_name=full_name,
                interface_source=raw_signature,
            )
            hashes = {
                "review_source_file": "PaperInterface.lean",
                "interface_sha256": "unchanged-interface",
                "lean_source_closure_sha256": "unchanged-lean-closure",
                "report_sha256": "",
                "tex_sha256": "",
                "text_sha256": "",
                "pdf_sha256": "",
                "paper_statement_map_sha256": "unchanged-map",
                "review_surface_static_sha256": "",
                "review_surface_display_sha256": "",
                "review_surface_rebind_sha256": "",
            }
            cache_path = folder / ".review_traces" / "paper_interface_cache.json"
            cache_path.parent.mkdir()
            cache_path.write_text(
                json.dumps(
                    {
                        "schema": review_dashboard.PAPER_INTERFACE_CACHE_SCHEMA,
                        "paper": folder.name,
                        "hashes": hashes,
                        "rows": [stale.__dict__],
                    }
                ),
                encoding="utf-8",
            )

            with mock.patch.object(
                review_dashboard,
                "run_lean_signature_manifests",
            ) as manifests:
                rows = review_dashboard.load_cached_review_rows(
                    folder,
                    source_hashes=hashes,
                )

            manifests.assert_not_called()
            self.assertIsNotNone(rows)
            assert rows is not None
            self.assertEqual(rows[0].paper_statement, source_statement)
            persisted = json.loads(cache_path.read_text(encoding="utf-8"))
            self.assertEqual(persisted["rows"][0]["paper_statement"], source_statement)

    def test_include_surface_limits_lean_batches_by_full_declaration_name(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "FilteredPaper"
            folder.mkdir()
            interface = folder / "PaperInterface.lean"
            interface.write_text(
                """
namespace First
theorem duplicate : True := by trivial
end First

theorem kept : True := by trivial
theorem auxiliary : True := by trivial
theorem omitted : True := by trivial

namespace Second
theorem duplicate : True := by trivial
end Second
""",
                encoding="utf-8",
            )
            (folder / "Assumptions.lean").write_text(
                "axiom sourcePremise : Prop\n", encoding="utf-8"
            )
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "include_names": [
                                "duplicate",
                                "kept",
                                "auxiliary",
                            ],
                            "assumption_names": ["sourcePremise"],
                            "auxiliary_names": ["auxiliary"],
                        }
                    }
                ),
                encoding="utf-8",
            )

            check_batches: dict[str, list[str]] = {}
            manifest_batches: dict[str, list[str]] = {}

            def check_rows(
                _paper_folder: Path,
                names: list[str],
                _timeout_seconds: int = review_dashboard.AGENT_PREVIEW_CHECK_TIMEOUT,
                source_file: Path | None = None,
            ) -> dict[str, str]:
                self.assertIsNotNone(source_file)
                check_batches[(source_file or Path()).name] = list(names)
                return {name: "True" for name in names}

            def manifest_rows(
                _root: Path,
                import_module: str,
                names: list[str],
                timeout_seconds: int = 120,
                build_timeout_seconds: int = 600,
                *,
                semantic_dependency_modules: tuple[str, ...] | None = None,
                build_input_provider: object | None = None,
                manifest_checkpoint: object | None = None,
            ) -> dict[str, dict[str, object]]:
                del timeout_seconds, build_timeout_seconds, manifest_checkpoint
                self.assertIn(import_module, semantic_dependency_modules or ())
                self.assertIsNotNone(build_input_provider)
                manifest_batches[import_module.rsplit(".", 1)[-1] + ".lean"] = list(
                    names
                )
                return {name: self._manifest(name) for name in names}

            cache_key = str(folder.resolve())
            review_dashboard.SIGNATURE_MANIFEST_CACHE.pop(cache_key, None)
            with (
                mock.patch.object(
                    review_dashboard,
                    "run_lean_check_previews",
                    side_effect=check_rows,
                ),
                mock.patch.object(
                    review_dashboard,
                    "run_lean_signature_manifests",
                    side_effect=manifest_rows,
                ),
                mock.patch.object(
                    review_dashboard,
                    "paper_owned_module_names_in_import_closure",
                    side_effect=lambda _root, _folder, module, **_kwargs: (module,),
                ),
            ):
                items = review_dashboard.parse_interface_items(
                    interface, None, folder
                )

            expected_interface = {
                "First.duplicate",
                "Second.duplicate",
                "kept",
            }
            self.assertEqual(
                set(check_batches["PaperInterface.lean"]), expected_interface
            )
            self.assertEqual(
                set(manifest_batches["PaperInterface.lean"]), expected_interface
            )
            self.assertEqual(
                check_batches["Assumptions.lean"], ["sourcePremise"]
            )
            self.assertEqual(
                manifest_batches["Assumptions.lean"], ["sourcePremise"]
            )
            self.assertEqual(
                Counter(item.name for item in items),
                Counter({"duplicate": 2, "kept": 1, "sourcePremise": 1}),
            )
            source_premise = next(
                item for item in items if item.name == "sourcePremise"
            )
            self.assertTrue(source_premise.is_assumption)

            manifests = review_dashboard.SIGNATURE_MANIFEST_CACHE[cache_key]
            self.assertIn("First.duplicate", manifests)
            self.assertIn("Second.duplicate", manifests)
            self.assertNotIn("duplicate", manifests)
            self.assertEqual(manifests["kept"]["sha256"], "manifest:kept")
            review_dashboard.SIGNATURE_MANIFEST_CACHE.pop(cache_key, None)

    def test_missing_include_names_keeps_all_declarations_in_lean_batch(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "UnfilteredPaper"
            folder.mkdir()
            interface = folder / "PaperInterface.lean"
            interface.write_text(
                """
theorem kept : True := by trivial
theorem auxiliary : True := by trivial
theorem omitted : True := by trivial
""",
                encoding="utf-8",
            )
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "assumption_names": [],
                            "auxiliary_names": ["auxiliary"],
                        }
                    }
                ),
                encoding="utf-8",
            )

            check_batches: list[list[str]] = []
            manifest_batches: list[list[str]] = []

            def check_rows(
                _paper_folder: Path,
                names: list[str],
                _timeout_seconds: int = review_dashboard.AGENT_PREVIEW_CHECK_TIMEOUT,
                source_file: Path | None = None,
            ) -> dict[str, str]:
                del source_file
                check_batches.append(list(names))
                return {name: "True" for name in names}

            def manifest_rows(
                _root: Path,
                _import_module: str,
                names: list[str],
                timeout_seconds: int = 120,
                build_timeout_seconds: int = 600,
                *,
                semantic_dependency_modules: tuple[str, ...] | None = None,
                build_input_provider: object | None = None,
                manifest_checkpoint: object | None = None,
            ) -> dict[str, dict[str, object]]:
                del timeout_seconds, build_timeout_seconds, manifest_checkpoint
                self.assertTrue(semantic_dependency_modules)
                self.assertIsNotNone(build_input_provider)
                manifest_batches.append(list(names))
                return {name: self._manifest(name) for name in names}

            cache_key = str(folder.resolve())
            review_dashboard.SIGNATURE_MANIFEST_CACHE.pop(cache_key, None)
            with (
                mock.patch.object(
                    review_dashboard,
                    "run_lean_check_previews",
                    side_effect=check_rows,
                ),
                mock.patch.object(
                    review_dashboard,
                    "run_lean_signature_manifests",
                    side_effect=manifest_rows,
                ),
                mock.patch.object(
                    review_dashboard,
                    "paper_owned_module_names_in_import_closure",
                    side_effect=lambda _root, _folder, module, **_kwargs: (module,),
                ),
            ):
                items = review_dashboard.parse_interface_items(
                    interface, None, folder
                )

            expected_batch = ["kept", "auxiliary", "omitted"]
            self.assertEqual(check_batches, [expected_batch])
            self.assertEqual(manifest_batches, [expected_batch])
            self.assertEqual([item.name for item in items], ["kept", "omitted"])
            review_dashboard.SIGNATURE_MANIFEST_CACHE.pop(cache_key, None)

    def test_manifest_only_extraction_skips_separate_check_preview_process(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "ManifestOnlyPaper"
            folder.mkdir()
            interface = folder / "PaperInterface.lean"
            source = "theorem reviewed : True := by trivial\n"
            interface.write_text(source, encoding="utf-8")
            (folder / "status.json").write_text(
                json.dumps(
                    {"review_surface": {"include_names": ["reviewed"]}}
                ),
                encoding="utf-8",
            )

            with (
                mock.patch.object(
                    review_dashboard,
                    "run_lean_check_previews",
                ) as previews,
                mock.patch.object(
                    review_dashboard,
                    "run_lean_signature_manifests",
                    return_value={"reviewed": self._manifest("reviewed")},
                ),
                mock.patch.object(
                    review_dashboard,
                    "paper_owned_module_names_in_import_closure",
                    side_effect=lambda _root, _folder, module, **_kwargs: (module,),
                ),
            ):
                rows = review_dashboard.parse_interface_items(
                    interface,
                    None,
                    folder,
                    render_lean_previews=False,
                )

            previews.assert_not_called()
            self.assertEqual(len(rows), 1)
            expected_statement = source.split(":=", 1)[0].strip()
            self.assertEqual(rows[0].interface_source, expected_statement)
            self.assertEqual(rows[0].lean_statement, expected_statement)
            self.assertEqual(rows[0].lean_signature_sha256, "manifest:reviewed")

    def test_external_support_only_definition_does_not_require_redundant_review_row(self) -> None:
        item = {
            "source_kind": "definition",
            "source_status": "support_only",
            "support_lean_declarations": ["Example.Model.isOptimal"],
            "lean_declarations": [],
            "source_note": "Direct source definition retained as support, not a theorem conclusion.",
        }

        self.assertFalse(
            review_dashboard._source_inventory_item_requires_review_row(
                "source_definition", item
            )
        )

        item["source_status"] = ""
        self.assertTrue(
            review_dashboard._source_inventory_item_requires_review_row(
                "source_definition", item
            )
        )

    def test_owned_build_input_transaction_rejects_mutation_before_rows_escape(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "MutationPaper"
            folder.mkdir()
            interface = folder / "PaperInterface.lean"
            interface.write_text(
                "theorem reviewed : True := by trivial\n",
                encoding="utf-8",
            )
            provider = mock.Mock()
            provider.finalize_unchanged.return_value = False
            with (
                mock.patch.object(
                    review_dashboard,
                    "RepositoryBuildInputSnapshotProvider",
                    return_value=provider,
                ),
                mock.patch.object(
                    review_dashboard,
                    "paper_owned_module_names_in_import_closure",
                    return_value=("MutationPaper.PaperInterface",),
                ),
                mock.patch.object(
                    review_dashboard,
                    "run_lean_signature_manifests",
                    return_value={"reviewed": self._manifest("reviewed")},
                ),
                mock.patch.object(
                    review_dashboard,
                    "run_lean_check_previews",
                    return_value={"reviewed": "True"},
                ),
            ):
                with self.assertRaisesRegex(
                    RuntimeError,
                    "repository build inputs changed",
                ):
                    review_dashboard.parse_interface_items(
                        interface,
                        None,
                        folder,
                    )

            provider.finalize_unchanged.assert_called_once_with()

    def test_explanatory_support_only_remark_needs_explicit_non_target_reason(self) -> None:
        item = {
            "source_kind": "remark",
            "source_status": "support_only",
            "support_lean_declarations": ["Example.counterexample"],
            "lean_declarations": [],
            "source_note": (
                "This post-theorem explanatory prose is not a standalone formal "
                "claim, named result, or theorem premise."
            ),
        }
        self.assertFalse(
            review_dashboard._source_inventory_item_requires_review_row(
                "source_explanatory_remark", item
            )
        )

        item["source_note"] = "Post-theorem prose retained for context."
        self.assertTrue(
            review_dashboard._source_inventory_item_requires_review_row(
                "source_explanatory_remark", item
            )
        )

    def test_formula_status_prose_cannot_create_a_model_route(self) -> None:
        """Only a source model/assumption presentation may use a model route."""

        statement = "The likelihood has the displayed domain."
        source_item = {
            "source_kind": "formula",
            "statement": statement,
            "source_location": "source.tex:10-12",
            "source_status": (
                "global-max scope is conditional on an explicit domain convention"
            ),
        }
        row = review_dashboard.ReviewItem(
            name="formula_row",
            kind="theorem",
            lean_statement="True",
            paper_statement=statement,
            agent_statement=statement,
            llm_match_source_routes=[
                {
                    "source_item": "source_formula",
                    "source_statement_sha256": review_dashboard.statement_digest(
                        statement
                    ),
                    "source_location": "source.tex:10-12",
                    "route_kind": "direct",
                }
            ],
        )

        self.assertFalse(
            review_dashboard.source_item_effective_route_policy(source_item)[
                "is_model_convention"
            ]
        )
        self.assertEqual(
            review_dashboard._coverage_route_error(
                "source_formula", source_item, row
            ),
            "",
        )

        source_item["model_convention_ids"] = ["FIXTURE-MODEL-CONVENTION-1"]
        row.llm_match_source_routes[0]["route_kind"] = "source_model_convention"  # type: ignore[index]
        self.assertFalse(
            review_dashboard.source_item_effective_route_policy(source_item)[
                "is_model_convention"
            ]
        )
        self.assertIn(
            "not one of `direct`, `source_component`",
            review_dashboard._coverage_route_error(
                "source_formula", source_item, row
            ),
        )
        row.llm_match_source_routes[0]["route_kind"] = "direct"  # type: ignore[index]
        self.assertEqual(
            review_dashboard._coverage_route_error(
                "source_formula", source_item, row
            ),
            "",
        )

        source_item["source_kind"] = "model"
        row.llm_match_source_routes[0]["route_kind"] = "source_model_convention"  # type: ignore[index]
        self.assertTrue(
            review_dashboard.source_item_effective_route_policy(source_item)[
                "is_model_convention"
            ]
        )
        self.assertEqual(
            review_dashboard._coverage_route_error(
                "source_formula", source_item, row
            ),
            "",
        )

    def test_signature_contexts_accept_mixed_relative_and_absolute_source_paths(self) -> None:
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as temp_dir:
            absolute_folder = Path(temp_dir) / "MixedPathsPaper"
            absolute_folder.mkdir()
            folder = absolute_folder.relative_to(Path.cwd())
            (absolute_folder / "PaperInterface.lean").write_text(
                "theorem reviewed : True := by trivial\n", encoding="utf-8"
            )
            (absolute_folder / "Assumptions.lean").write_text(
                "axiom sourcePremise : Prop\n", encoding="utf-8"
            )
            (absolute_folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "source_file": (
                                f"{folder.as_posix()}/PaperInterface.lean"
                            ),
                            "assumption_source_file": (
                                f"{folder.as_posix()}/Assumptions.lean"
                            ),
                            "assumption_names": ["sourcePremise"],
                        }
                    }
                ),
                encoding="utf-8",
            )

            modules: list[str] = []

            def signature_context(
                _root: Path,
                module: str,
                *,
                semantic_dependency_modules: tuple[str, ...] | None = None,
                build_input_provider: object | None = None,
            ) -> dict[str, object]:
                self.assertEqual(semantic_dependency_modules, (module,))
                self.assertIsNotNone(build_input_provider)
                modules.append(module)
                return {"import_module": module}

            with (
                mock.patch.object(
                    review_dashboard,
                    "signature_manifest_cache_context",
                    side_effect=signature_context,
                ),
                mock.patch.object(
                    review_dashboard,
                    "paper_owned_module_names_in_import_closure",
                    side_effect=lambda _root, _folder, module, **_kwargs: (module,),
                ),
            ):
                contexts = review_dashboard.current_review_signature_contexts(folder)

            self.assertEqual(
                contexts,
                {
                    "Assumptions.lean": {
                        "import_module": "MixedPathsPaper.Assumptions"
                    },
                    "PaperInterface.lean": {
                        "import_module": "MixedPathsPaper.PaperInterface"
                    },
                },
            )
            self.assertEqual(
                modules,
                ["MixedPathsPaper.Assumptions", "MixedPathsPaper.PaperInterface"],
            )

    def test_signature_context_skips_unselected_existing_assumption_module(self) -> None:
        with tempfile.TemporaryDirectory(dir=Path.cwd()) as temp_dir:
            absolute_folder = Path(temp_dir) / "NoAssumptionRowsPaper"
            absolute_folder.mkdir()
            folder = absolute_folder.relative_to(Path.cwd())
            (absolute_folder / "PaperInterface.lean").write_text(
                "theorem reviewed : True := by trivial\n", encoding="utf-8"
            )
            (absolute_folder / "Assumptions.lean").write_text(
                "axiom sourcePremise : Prop\n", encoding="utf-8"
            )
            (absolute_folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "source_file": (
                                f"{folder.as_posix()}/PaperInterface.lean"
                            ),
                            "assumption_source_file": (
                                f"{folder.as_posix()}/Assumptions.lean"
                            ),
                            "assumption_names": [],
                        }
                    }
                ),
                encoding="utf-8",
            )

            with (
                mock.patch.object(
                    review_dashboard,
                    "signature_manifest_cache_context",
                    side_effect=lambda _root, module, **_kwargs: {
                        "import_module": module
                    },
                ) as signature_context,
                mock.patch.object(
                    review_dashboard,
                    "paper_owned_module_names_in_import_closure",
                    side_effect=lambda _root, _folder, module, **_kwargs: (module,),
                ),
            ):
                contexts = review_dashboard.current_review_signature_contexts(folder)

            self.assertEqual(
                contexts,
                {
                    "PaperInterface.lean": {
                        "import_module": "NoAssumptionRowsPaper.PaperInterface"
                    }
                },
            )
            signature_context.assert_called_once()

    def test_only_lean_extraction_fields_invalidate_static_status_digest(self) -> None:
        base_surface = {
            "source_file": "papers/Example/PaperInterface.lean",
            "include_names": ["paperTheorem"],
            "assumption_names": [],
            "auxiliary_names": [],
            "slices": [{"id": "main", "names": ["paperTheorem"]}],
            "source_definition_names": ["sourceCondition"],
            "llm_statement_review": {"path": "audit/statement_match_llm.json"},
        }
        base = json.dumps({"review_surface": base_surface})
        display_edit = json.dumps(
            {
                "review_surface": {
                    **base_surface,
                    "slices": [{"id": "theory", "names": ["paperTheorem"]}],
                    "future_report_metadata": {"schema": 1},
                }
            }
        )
        extraction_edit = json.dumps(
            {
                "review_surface": {
                    **base_surface,
                    "include_names": ["paperTheorem", "paperLemma"],
                }
            }
        )

        self.assertEqual(
            review_dashboard._review_surface_static_status_digest(base),
            review_dashboard._review_surface_static_status_digest(display_edit),
        )
        self.assertNotEqual(
            review_dashboard._review_surface_rebind_status_digest(base),
            review_dashboard._review_surface_rebind_status_digest(display_edit),
        )
        self.assertNotEqual(
            review_dashboard._review_surface_static_status_digest(base),
            review_dashboard._review_surface_static_status_digest(extraction_edit),
        )

    def test_status_rebind_preserves_full_name_proposition_route(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "QualifiedRoutePaper"
            folder.mkdir()
            (folder / "PaperInterface.lean").write_text(
                "namespace Qualified\n"
                "theorem row : True := by trivial\n"
                "end Qualified\n",
                encoding="utf-8",
            )
            (folder / "status.json").write_text(
                json.dumps(
                    {
                        "review_surface": {
                            "include_names": ["row"],
                            "proposition_spec_proofs": {
                                "Qualified.row": "Qualified.rowProof"
                            },
                        }
                    }
                ),
                encoding="utf-8",
            )
            item = review_dashboard.ReviewItem(
                name="row",
                kind="theorem",
                lean_statement="theorem row : True",
                paper_statement="True.",
                agent_statement="True.",
                interface_source="theorem row : True",
                is_proposition_spec=True,
                line_number=2,
            )

            rebound = review_dashboard.rebind_cached_review_status(folder, [item])

            self.assertIsNotNone(rebound)
            assert rebound is not None
            self.assertEqual(rebound[0].full_name, "Qualified.row")
            self.assertEqual(
                rebound[0].proposition_spec_proof, "Qualified.rowProof"
            )
            self.assertEqual(rebound[0].proposition_spec_role, "proof_routed")

    def test_coverage_inventory_uses_current_anchor_not_map_summary_or_routes(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "AnchorSelectedPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            source = folder / "source.txt"
            source_text = (
                "Theorem 1. Every admissible input has a witness.\n"
                "\n"
                "The displayed conclusion is part of the theorem.\n"
                "Proof.\n"
            )
            source.write_text(source_text, encoding="utf-8")
            quote = "\n".join(source_text.splitlines()[:3])
            anchor = {
                "path": "source.txt",
                "line_start": 1,
                "line_end": 3,
                "quoted_text": quote,
                "quoted_text_sha256": hashlib.sha256(
                    quote.encode("utf-8")
                ).hexdigest(),
            }
            payload = {
                "source_artifact_path": "source.txt",
                "source_artifact_sha256": hashlib.sha256(
                    source.read_bytes()
                ).hexdigest(),
                "source_coverage_mode": "named_theoretical_statements",
                "items": {
                    # None of these navigation/classification fields can decide
                    # membership. The prose intentionally omits "Theorem 1".
                    "figure_caption_navigation_key": {
                        "source_kind": "remark",
                        "claim_bearing": True,
                        "statement": "Every admissible input has a witness.",
                        "lean_declarations": ["Fixture.figureCaptionHelper"],
                        "source_anchor_evidence": [anchor],
                    }
                },
            }
            map_path = audit / "paper_statement_map.json"
            map_path.write_text(json.dumps(payload), encoding="utf-8")

            full, selected, mode, error = review_dashboard.paper_coverage_inventory(
                folder
            )

            self.assertEqual(mode, "named_theoretical_statements")
            self.assertEqual(error, "")
            self.assertEqual(set(full), {"figure_caption_navigation_key"})
            self.assertEqual(set(selected), {"figure_caption_navigation_key"})

            # A broad source_location cannot stand in for the verified anchor.
            payload["items"]["figure_caption_navigation_key"].pop(
                "source_anchor_evidence"
            )
            payload["items"]["figure_caption_navigation_key"][
                "source_location"
            ] = "source.txt:1-3"
            map_path.write_text(json.dumps(payload), encoding="utf-8")
            _full, location_only, _mode, _error = (
                review_dashboard.paper_coverage_inventory(folder)
            )
            self.assertEqual(location_only, {})

    def test_coverage_inventory_rejects_anchor_spanning_multiple_presentations(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "AmbiguousAnchorPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            source = folder / "source.txt"
            source_text = (
                "Theorem 1. The first result holds.\n"
                "Lemma 2. The second result holds.\n"
            )
            source.write_text(source_text, encoding="utf-8")
            quote = source_text.rstrip("\n")
            payload = {
                "source_artifact_path": "source.txt",
                "source_artifact_sha256": hashlib.sha256(
                    source.read_bytes()
                ).hexdigest(),
                "source_coverage_mode": "named_theoretical_statements",
                "items": {
                    "misleading_single_row": {
                        "source_kind": "remark",
                        "claim_bearing": True,
                        "statement": "The source has a result.",
                        "proof_lean_declarations": ["Fixture.unrelated"],
                        "source_anchor_evidence": [
                            {
                                "path": "source.txt",
                                "line_start": 1,
                                "line_end": 2,
                                "quoted_text": quote,
                                "quoted_text_sha256": hashlib.sha256(
                                    quote.encode("utf-8")
                                ).hexdigest(),
                            }
                        ],
                    }
                },
            }
            (audit / "paper_statement_map.json").write_text(
                json.dumps(payload), encoding="utf-8"
            )

            _full, selected, _mode, _error = review_dashboard.paper_coverage_inventory(
                folder
            )

            self.assertEqual(selected, {})

    def test_source_anchor_gate_projects_normal_scope_before_validation(self) -> None:
        """Normal scope validates named theory, not every retained deep row."""

        with tempfile.TemporaryDirectory() as temp_dir:
            folder = Path(temp_dir) / "ScopedAnchorPaper"
            audit = folder / "audit"
            audit.mkdir(parents=True)
            source = folder / "source.txt"
            source_text = (
                "Theorem 1. The named conclusion holds.\n"
                "Formula 2. A standalone display identity.\n"
                "Equation 3. A standalone equality.\n"
                "Algorithm 4. A standalone procedure.\n"
                "Figure 5. A numerical illustration.\n"
                "Remark 6. A corrected source-visible claim.\n"
            )
            source.write_text(source_text, encoding="utf-8")
            theorem_quote = source_text.splitlines()[0]
            theorem_anchor = {
                "path": "source.txt",
                "line_start": 1,
                "line_end": 1,
                "quoted_text": theorem_quote,
                "quoted_text_sha256": hashlib.sha256(
                    theorem_quote.encode("utf-8")
                ).hexdigest(),
            }
            payload = {
                "source_artifact_path": "source.txt",
                "source_artifact_sha256": hashlib.sha256(
                    source.read_bytes()
                ).hexdigest(),
                "source_anchor_evidence_required": True,
                "source_coverage_mode": "named_theoretical_statements",
                "items": {
                    "opaque_named_route": {
                        "source_kind": "theorem",
                        "claim_bearing": True,
                        "statement": "Theorem 1. The named conclusion holds.",
                        "source_location": "source.txt:1",
                        "source_anchor_evidence": [theorem_anchor],
                    },
                    # These retained rows intentionally have a source locator
                    # but no quote. They are normal-mode deep material even
                    # though their map keys and textual labels look operative.
                    "formula_navigation": {
                        "source_kind": "formula",
                        "claim_bearing": True,
                        "statement": "A standalone display identity.",
                        "source_location": "source.txt:2",
                    },
                    "equation_navigation": {
                        "source_kind": "equation",
                        "claim_bearing": True,
                        "statement": "A standalone equality.",
                        "source_location": "source.txt:3",
                    },
                    "algorithm_navigation": {
                        "source_kind": "algorithm",
                        "claim_bearing": True,
                        "statement": "A standalone procedure.",
                        "source_location": "source.txt:4",
                    },
                    "caption_navigation": {
                        "source_kind": "figure_caption",
                        "claim_bearing": True,
                        "statement": "A numerical illustration.",
                        "source_location": "source.txt:5",
                    },
                    # Explicit corrected targets remain source obligations in
                    # normal mode even when their presentation is a remark.
                    "explicit_correction": {
                        "source_kind": "remark",
                        "claim_bearing": True,
                        "coverage_status": "corrected_source_statement",
                        "statement": "A corrected source-visible claim.",
                        "source_location": "source.txt:6",
                    },
                },
            }
            map_path = audit / "paper_statement_map.json"
            map_path.write_text(json.dumps(payload), encoding="utf-8")

            normal_errors = review_dashboard._scoped_source_anchor_evidence_errors(
                folder
            )
            self.assertTrue(
                any("items.explicit_correction." in error for error in normal_errors),
                normal_errors,
            )
            normal_precheck = review_dashboard.source_inventory_precheck_summary(
                folder
            )
            self.assertEqual(
                normal_precheck["source_anchor_evidence_errors"], normal_errors
            )
            for deep_item in (
                "formula_navigation",
                "equation_navigation",
                "algorithm_navigation",
                "caption_navigation",
            ):
                self.assertFalse(
                    any(f"items.{deep_item}." in error for error in normal_errors),
                    normal_errors,
                )

            payload["source_coverage_mode"] = "deep_paper_with_all_prose_claims"
            map_path.write_text(json.dumps(payload), encoding="utf-8")
            deep_errors = review_dashboard._scoped_source_anchor_evidence_errors(folder)
            for deep_item in (
                "formula_navigation",
                "equation_navigation",
                "algorithm_navigation",
                "caption_navigation",
            ):
                self.assertTrue(
                    any(f"items.{deep_item}." in error for error in deep_errors),
                    deep_errors,
                )


if __name__ == "__main__":
    unittest.main()
