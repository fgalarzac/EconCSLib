#!/usr/bin/env python3
"""Tests for the operational raw-to-dashboard manifest handoff."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts import refresh_closeout_manifest_cache as handoff


class RefreshCloseoutManifestCacheTests(unittest.TestCase):
    def _folder(self, root: Path) -> Path:
        folder = root / "papers" / "Fixture"
        folder.mkdir(parents=True)
        return folder

    @staticmethod
    def _run_context(
        provider: object,
        configured_rows: tuple[dict[str, object], ...] | None,
    ) -> SimpleNamespace:
        return SimpleNamespace(
            build_input_provider=provider,
            current_configured_review_rows_for_manifest_reuse=mock.Mock(
                return_value=configured_rows
            ),
        )

    def test_current_raw_rows_prime_dashboard_before_any_persistent_write(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = self._folder(Path(temporary))
            provider = mock.Mock()
            evidence_context = object()
            configured_rows = (
                {
                    "qualified_declaration": "Fixture.PaperInterface.reviewed",
                    "elaborated_signature_sha256": "a" * 64,
                },
            )
            run_context = self._run_context(provider, configured_rows)
            items = [mock.sentinel.reviewed]
            contexts = {"PaperInterface.lean": {"context": "current"}}
            hashes = {"interface_sha256": "b" * 64}
            events: list[str] = []

            with (
                mock.patch.object(
                    handoff.audit_repository,
                    "build_paper_closeout_evidence_context",
                    return_value=evidence_context,
                ),
                mock.patch.object(
                    handoff.audit_repository.PaperCloseoutRunContext,
                    "from_exact_evidence_context",
                    return_value=run_context,
                ) as mint,
                mock.patch.object(
                    handoff.audit_repository,
                    "paper_closeout_evidence_context_prebuild_findings",
                    return_value=[],
                ),
                mock.patch.object(
                    handoff.review_dashboard,
                    "review_items_for_paper",
                    return_value=items,
                ) as review,
                mock.patch.object(
                    handoff.review_dashboard,
                    "current_review_signature_contexts",
                    return_value=contexts,
                ),
                mock.patch.object(
                    handoff.review_dashboard,
                    "_cache_source_hashes",
                    return_value=hashes,
                ),
                mock.patch.object(
                    handoff.audit_repository,
                    "paper_closeout_context_mutation_findings",
                    side_effect=lambda *_args, **_kwargs: events.append("mutation") or [],
                ),
                mock.patch.object(
                    handoff.review_dashboard,
                    "write_cached_review_rows",
                    side_effect=lambda *_args, **_kwargs: events.append("write"),
                ) as write,
                mock.patch.object(
                    handoff.review_dashboard,
                    "publish_review_signature_manifest_store",
                    side_effect=lambda *_args, **_kwargs: events.append("publish")
                    or {"Fixture.PaperInterface.reviewed"},
                ) as publish,
            ):
                result = handoff.refresh_closeout_manifest_cache(
                    "Fixture", folder=folder
                )

        self.assertEqual(result["state"], "completed")
        self.assertEqual(result["configured_review_row_count"], 1)
        self.assertEqual(result["dashboard_row_count"], 1)
        self.assertEqual(result["manifest_store_published_count"], 1)
        mint.assert_called_once_with(
            "Fixture", folder.resolve(), evidence_context=evidence_context
        )
        self.assertEqual(events, ["mutation", "write", "publish"])
        review.assert_called_once()
        kwargs = review.call_args.kwargs
        self.assertFalse(kwargs["use_cache"])
        self.assertFalse(kwargs["render_images"])
        self.assertTrue(kwargs["require_current_signatures"])
        self.assertFalse(kwargs["persist_cache_rebind"])
        self.assertFalse(kwargs["publish_manifest_store"])
        self.assertIs(kwargs["build_input_provider"], provider)
        self.assertEqual(kwargs["validated_configured_review_rows"], configured_rows)
        self.assertNotIn("audit_inputs", kwargs)
        write.assert_called_once_with(
            folder.resolve(),
            items,
            signature_contexts=contexts,
            source_hashes=hashes,
        )
        publish.assert_called_once_with(folder.resolve(), items, contexts)

    def test_invalid_raw_context_never_starts_dashboard_extraction(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = self._folder(Path(temporary))
            provider = mock.Mock()
            run_context = self._run_context(provider, ())
            evidence_context = object()
            finding = SimpleNamespace(
                severity="ERROR", message="source-record audit is stale"
            )
            with (
                mock.patch.object(
                    handoff.audit_repository,
                    "build_paper_closeout_evidence_context",
                    return_value=evidence_context,
                ),
                mock.patch.object(
                    handoff.audit_repository.PaperCloseoutRunContext,
                    "from_exact_evidence_context",
                    return_value=run_context,
                ),
                mock.patch.object(
                    handoff.audit_repository,
                    "paper_closeout_evidence_context_prebuild_findings",
                    return_value=[finding],
                ),
                mock.patch.object(
                    handoff.review_dashboard, "review_items_for_paper"
                ) as review,
            ):
                result = handoff.refresh_closeout_manifest_cache(
                    "Fixture", folder=folder
                )

        self.assertEqual(result["state"], "raw_context_invalid")
        self.assertIn("stale", str(result["reason"]))
        review.assert_not_called()
        run_context.current_configured_review_rows_for_manifest_reuse.assert_not_called()

    def test_missing_current_raw_rows_never_start_dashboard_extraction(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = self._folder(Path(temporary))
            provider = mock.Mock()
            run_context = self._run_context(provider, None)
            evidence_context = object()
            with (
                mock.patch.object(
                    handoff.audit_repository,
                    "build_paper_closeout_evidence_context",
                    return_value=evidence_context,
                ),
                mock.patch.object(
                    handoff.audit_repository.PaperCloseoutRunContext,
                    "from_exact_evidence_context",
                    return_value=run_context,
                ),
                mock.patch.object(
                    handoff.audit_repository,
                    "paper_closeout_evidence_context_prebuild_findings",
                    return_value=[],
                ),
                mock.patch.object(
                    handoff.review_dashboard, "review_items_for_paper"
                ) as review,
            ):
                result = handoff.refresh_closeout_manifest_cache(
                    "Fixture", folder=folder
                )

        self.assertEqual(result["state"], "manifest_handoff_unavailable")
        self.assertIn("complete current", str(result["reason"]))
        review.assert_not_called()
        run_context.current_configured_review_rows_for_manifest_reuse.assert_called_once_with()

    def test_input_mutation_blocks_every_persistent_cache_write(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = self._folder(Path(temporary))
            provider = mock.Mock()
            evidence_context = object()
            configured_rows = (
                {
                    "qualified_declaration": "Fixture.PaperInterface.reviewed",
                    "elaborated_signature_sha256": "a" * 64,
                },
            )
            run_context = self._run_context(provider, configured_rows)
            finding = SimpleNamespace(
                severity="ERROR", message="source bytes changed during extraction"
            )
            with (
                mock.patch.object(
                    handoff.audit_repository,
                    "build_paper_closeout_evidence_context",
                    return_value=evidence_context,
                ),
                mock.patch.object(
                    handoff.audit_repository.PaperCloseoutRunContext,
                    "from_exact_evidence_context",
                    return_value=run_context,
                ),
                mock.patch.object(
                    handoff.audit_repository,
                    "paper_closeout_evidence_context_prebuild_findings",
                    return_value=[],
                ),
                mock.patch.object(
                    handoff.review_dashboard,
                    "review_items_for_paper",
                    return_value=[mock.sentinel.reviewed],
                ),
                mock.patch.object(
                    handoff.review_dashboard,
                    "current_review_signature_contexts",
                    return_value={"PaperInterface.lean": {"context": "current"}},
                ),
                mock.patch.object(
                    handoff.review_dashboard,
                    "_cache_source_hashes",
                    return_value={"interface_sha256": "b" * 64},
                ),
                mock.patch.object(
                    handoff.audit_repository,
                    "paper_closeout_context_mutation_findings",
                    return_value=[finding],
                ),
                mock.patch.object(
                    handoff.review_dashboard, "write_cached_review_rows"
                ) as write,
                mock.patch.object(
                    handoff.review_dashboard,
                    "publish_review_signature_manifest_store",
                ) as publish,
            ):
                result = handoff.refresh_closeout_manifest_cache(
                    "Fixture", folder=folder
                )

        self.assertEqual(result["state"], "input_mutation_detected")
        self.assertIn("changed", str(result["reason"]))
        write.assert_not_called()
        publish.assert_not_called()


if __name__ == "__main__":
    unittest.main()
