#!/usr/bin/env python3
"""Regression tests for authority-attested interrupted-refresh reuse."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import review_dashboard as DASHBOARD


class ManifestResumeCacheTests(unittest.TestCase):
    def context(self, identity: str) -> dict[str, object]:
        return {
            "identity": identity,
            "canonical_representation": "lean_compact_canonical_v2",
            "semantic_hash_tool_identity": {"tool": "fixture"},
        }

    @staticmethod
    def digest(manifest: object) -> str:
        return str(manifest.get("sha256") or "") if isinstance(manifest, dict) else ""

    @staticmethod
    def context_digest(context: object) -> str:
        return str(context.get("identity") or "") if isinstance(context, dict) else ""

    def binding(
        self, folder: Path, source: Path, declaration: str, text: str
    ) -> dict[str, str]:
        binding = DASHBOARD._manifest_resume_binding(
            folder,
            qualified_declaration=declaration,
            declaration_kind="theorem",
            lean_source_declaration=text,
            source_path=source,
        )
        self.assertIsNotNone(binding)
        assert binding is not None
        return binding

    def test_resume_records_are_forwarded_only_to_authority_attester(self) -> None:
        current_context = self.context("a" * 64)
        stale_context = self.context("b" * 64)
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            folder.mkdir()
            source = folder / "PaperInterface.lean"
            source.write_text("-- fixture\n", encoding="utf-8")
            first = self.binding(folder, source, "Fixture.first", "theorem first : True")
            second = self.binding(folder, source, "Fixture.second", "theorem second : True")
            old_third = self.binding(folder, source, "Fixture.third", "theorem third : True")
            current_third = self.binding(folder, source, "Fixture.third", "theorem third : False")
            manifests = {
                "Fixture.first": {"sha256": "1" * 64},
                "Fixture.second": {"sha256": "2" * 64},
                "Fixture.third": {"sha256": "3" * 64},
            }
            with mock.patch.object(
                DASHBOARD,
                "signature_manifest_cache_context_sha256",
                side_effect=self.context_digest,
            ), mock.patch.object(
                DASHBOARD, "signature_manifest_digest", side_effect=self.digest
            ):
                DASHBOARD._checkpoint_manifest_resume_cache(
                    folder, {"Fixture.first": first}, current_context,
                    {"Fixture.first": manifests["Fixture.first"]},
                )
                DASHBOARD._checkpoint_manifest_resume_cache(
                    folder, {"Fixture.second": second}, stale_context,
                    {"Fixture.second": manifests["Fixture.second"]},
                )
                DASHBOARD._checkpoint_manifest_resume_cache(
                    folder, {"Fixture.third": old_third}, current_context,
                    {"Fixture.third": manifests["Fixture.third"]},
                )
                attester = mock.Mock(
                    return_value=({"Fixture.first": manifests["Fixture.first"]}, {})
                )
                with mock.patch.object(
                    DASHBOARD,
                    "prime_exact_context_attested_resume_manifests",
                    attester,
                ):
                    seeded = DASHBOARD._prime_manifest_resume_cache(
                        folder,
                        import_module="Fixture.PaperInterface",
                        semantic_dependency_modules=("Fixture.PaperInterface",),
                        context=current_context,
                        bindings={
                            "Fixture.first": first,
                            "Fixture.second": second,
                            "Fixture.third": current_third,
                        },
                    )

        self.assertEqual(seeded, {"Fixture.first"})
        records = attester.call_args.kwargs["resume_records"]
        self.assertEqual(set(records), {"Fixture.first"})
        self.assertEqual(records["Fixture.first"]["binding"], first)
        self.assertEqual(records["Fixture.first"]["manifest"], manifests["Fixture.first"])

    def test_inner_let_conclusion_change_cannot_reuse_a_resume_record(self) -> None:
        """A theorem's local result binder is not its declaration assignment."""

        context = self.context("a" * 64)
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            folder.mkdir()
            source = folder / "PaperInterface.lean"
            source.write_text("-- fixture\n", encoding="utf-8")
            old = self.binding(
                folder,
                source,
                "Fixture.endpoint",
                "theorem endpoint : (let rho : Nat := 0; rho = 0) := by trivial",
            )
            new = self.binding(
                folder,
                source,
                "Fixture.endpoint",
                "theorem endpoint : (let rho : Nat := 0; rho = 0) ∧ True := by trivial",
            )
            self.assertNotEqual(
                DASHBOARD._manifest_resume_binding_digest(old),
                DASHBOARD._manifest_resume_binding_digest(new),
            )
            manifest = {"sha256": "1" * 64}
            with (
                mock.patch.object(
                    DASHBOARD,
                    "signature_manifest_cache_context_sha256",
                    side_effect=self.context_digest,
                ),
                mock.patch.object(
                    DASHBOARD, "signature_manifest_digest", side_effect=self.digest
                ),
            ):
                DASHBOARD._checkpoint_manifest_resume_cache(
                    folder,
                    {"Fixture.endpoint": old},
                    context,
                    {"Fixture.endpoint": manifest},
                )
                current = DASHBOARD.current_manifest_resume_records(
                    folder,
                    context=context,
                    bindings={"Fixture.endpoint": new},
                )

        self.assertEqual(current, {})

    def test_resume_cache_normalizes_a_repository_relative_paper_path(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            papers = root / "papers"
            folder = papers / "Fixture"
            folder.mkdir(parents=True)
            with (
                mock.patch.object(DASHBOARD, "ROOT", root),
                mock.patch.object(DASHBOARD, "PAPERS_DIR", papers),
            ):
                by_id = DASHBOARD.manifest_resume_cache_directory("Fixture")
                by_relative_path = DASHBOARD.manifest_resume_cache_directory(
                    Path("papers/Fixture")
                )
                self.assertEqual(by_id, by_relative_path)
                self.assertEqual(
                    by_id,
                    folder
                    / ".review_traces"
                    / DASHBOARD.MANIFEST_RESUME_CACHE_DIRNAME,
                )
                self.assertEqual(
                    DASHBOARD.manifest_resume_cache_directory(Path("OtherFixture")),
                    papers
                    / "OtherFixture"
                    / ".review_traces"
                    / DASHBOARD.MANIFEST_RESUME_CACHE_DIRNAME,
                )

    def test_public_checkpoint_persists_only_exact_bound_manifest_records(self) -> None:
        """The producer-facing checkpoint writes reusable data without credit."""

        context = self.context("a" * 64)
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            folder.mkdir()
            source = folder / "PaperInterface.lean"
            source.write_text("-- fixture\n", encoding="utf-8")
            binding = self.binding(
                folder,
                source,
                "Fixture.first",
                "theorem first : True",
            )
            manifest = {"sha256": "1" * 64}
            with (
                mock.patch.object(
                    DASHBOARD,
                    "signature_manifest_cache_context_sha256",
                    side_effect=self.context_digest,
                ),
                mock.patch.object(
                    DASHBOARD,
                    "signature_manifest_digest",
                    side_effect=self.digest,
                ),
            ):
                checkpointed = DASHBOARD.checkpoint_manifest_resume_records(
                    folder,
                    {"Fixture.first": binding},
                    context,
                    {
                        "Fixture.first": manifest,
                        "Fixture.unbound": {"sha256": "2" * 64},
                    },
                )
                records = DASHBOARD.current_manifest_resume_records(
                    folder,
                    context=context,
                    bindings={"Fixture.first": binding},
                )

        self.assertEqual(checkpointed, {"Fixture.first"})
        self.assertEqual(set(records), {"Fixture.first"})
        self.assertEqual(records["Fixture.first"]["binding"], binding)
        self.assertEqual(records["Fixture.first"]["manifest"], manifest)

    def test_swapped_or_unattested_resume_record_stays_a_miss_without_revalidation(
        self,
    ) -> None:
        context = self.context("a" * 64)
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            folder.mkdir()
            source = folder / "PaperInterface.lean"
            source.write_text("-- fixture\n", encoding="utf-8")
            binding = self.binding(folder, source, "Fixture.first", "theorem first : True")
            path = DASHBOARD._manifest_resume_cache_entry_path(folder, "a" * 64, binding)
            self.assertIsNotNone(path)
            assert path is not None
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(
                json.dumps(
                    {
                        "schema": DASHBOARD.MANIFEST_RESUME_CACHE_SCHEMA,
                        "paper": folder.name,
                        "non_authoritative_resume_cache": True,
                        "manifest_cache_context_sha256": "a" * 64,
                        "binding": binding,
                        "manifest": {"sha256": "2" * 64, "copied_from": "other"},
                    }
                ),
                encoding="utf-8",
            )
            with mock.patch.object(
                DASHBOARD,
                "signature_manifest_cache_context_sha256",
                side_effect=self.context_digest,
            ), mock.patch.object(
                DASHBOARD, "signature_manifest_digest", side_effect=self.digest
            ), mock.patch.object(
                DASHBOARD,
                "prime_exact_context_attested_resume_manifests",
                return_value=({}, {"store_status": "resume_payload_not_attested"}),
            ) as attester, mock.patch.object(
                DASHBOARD,
                "prime_attested_resume_manifests_with_current_revalidation",
                side_effect=AssertionError(
                    "an unattested exact-context record must remain a cache miss"
                ),
            ) as recovery:
                seeded = DASHBOARD._prime_manifest_resume_cache(
                    folder,
                    import_module="Fixture.PaperInterface",
                    semantic_dependency_modules=("Fixture.PaperInterface",),
                    context=context,
                    bindings={"Fixture.first": binding},
                )

        self.assertEqual(seeded, set())
        recovery.assert_not_called()
        self.assertEqual(set(attester.call_args.kwargs["resume_records"]), {"Fixture.first"})

    def test_interrupted_checkpoint_uses_current_revalidation_after_fast_path_miss(
        self,
    ) -> None:
        context = self.context("a" * 64)
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / "Fixture"
            folder.mkdir()
            source = folder / "PaperInterface.lean"
            source.write_text("-- fixture\n", encoding="utf-8")
            binding = self.binding(folder, source, "Fixture.first", "theorem first : True")
            manifest = {"sha256": "1" * 64}
            progress: list[str] = []
            with mock.patch.object(
                DASHBOARD,
                "signature_manifest_cache_context_sha256",
                side_effect=self.context_digest,
            ), mock.patch.object(
                DASHBOARD, "signature_manifest_digest", side_effect=self.digest
            ):
                DASHBOARD._checkpoint_manifest_resume_cache(
                    folder, {"Fixture.first": binding}, context, {"Fixture.first": manifest}
                )
                fast_path = mock.Mock(return_value=({}, {"seeded_count": 0}))
                recovery = mock.Mock(
                    return_value=(
                        {"Fixture.first": manifest},
                        {"item_revalidation_requested_count": 1},
                    )
                )
                with mock.patch.object(
                    DASHBOARD,
                    "prime_exact_context_attested_resume_manifests",
                    fast_path,
                ), mock.patch.object(
                    DASHBOARD,
                    "prime_attested_resume_manifests_with_current_revalidation",
                    recovery,
                ):
                    seeded = DASHBOARD._prime_manifest_resume_cache(
                        folder,
                        import_module="Fixture.PaperInterface",
                        semantic_dependency_modules=("Fixture.PaperInterface",),
                        context=context,
                        bindings={"Fixture.first": binding},
                        progress=progress.append,
                    )

        self.assertEqual(seeded, {"Fixture.first"})
        fast_path.assert_called_once()
        recovery.assert_called_once()
        records = recovery.call_args.kwargs["resume_records"]
        self.assertEqual(
            records["Fixture.first"]["manifest_cache_context_sha256"], "a" * 64
        )
        self.assertTrue(any("compact-Lean revalidated 1" in line for line in progress))


if __name__ == "__main__":
    unittest.main()
