"""Focused consumer checks for selected-surface provenance rebinds."""

from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import unittest
from contextlib import ExitStack
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import Mock, patch

from scripts import audit_evidence_integrity as EVIDENCE


ROOT = Path(__file__).resolve().parents[2]
HELPER = ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
SPEC = importlib.util.spec_from_file_location(
    "source_record_selected_surface_rebind_integration_audit", HELPER
)
assert SPEC is not None and SPEC.loader is not None
AUDIT = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = AUDIT
SPEC.loader.exec_module(AUDIT)


def fingerprint(*, semantic_map: str) -> dict[str, object]:
    return {
        "schema": 8,
        "paper": "Fixture",
        "max_depth": 4,
        "no_lean": False,
        "paper_statement_map_semantic_sha256": semantic_map,
    }


class SelectedSurfaceRebindConsumerTests(unittest.TestCase):
    def _cache_fixture(
        self,
    ) -> tuple[Path, Path, SimpleNamespace, str, str, dict[str, object]]:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        paper_dir = root / "papers" / "Fixture"
        audit_dir = paper_dir / "audit"
        audit_dir.mkdir(parents=True)
        map_path = audit_dir / "paper_statement_map.json"
        map_path.write_text("{}\n", encoding="utf-8")
        full_map, semantic_map = AUDIT.paper_statement_map_cache_receipts(paper_dir)
        payload: dict[str, object] = {
            "paper": "Fixture",
            "prompt_version": AUDIT.SOURCE_RECORD_PROMPT_VERSION,
            "paper_statement_map_sha256": full_map,
            "source_record_audit_sha256": "a" * 64,
            "lean_check": {"returncode": 0},
        }
        (audit_dir / "source_record_audit.json").write_text(
            json.dumps(payload), encoding="utf-8"
        )
        args = SimpleNamespace(
            paper="Fixture",
            force=False,
            refresh_judgment_summary=False,
            ignore_current_judgments=False,
            no_lean=False,
        )
        return root, paper_dir, args, full_map, semantic_map, payload

    def _cache_patches(
        self,
        *,
        current: dict[str, object],
        selected: Mock,
        transition: Mock,
    ):
        return (
            patch.object(
                AUDIT, "source_record_input_fingerprint", return_value=current
            ),
            patch.object(AUDIT, "source_record_audit_receipt_error", return_value=""),
            patch.object(
                AUDIT, "source_record_raw_reusable_item_metadata_error", return_value=""
            ),
            patch.object(
                AUDIT, "source_record_raw_scan_completeness_error", return_value=""
            ),
            patch.object(
                AUDIT, "direct_route_diagnostic_rebind_error", return_value=""
            ),
            patch.object(
                AUDIT,
                "source_record_saved_statement_ledger_coverages",
                return_value=(set(), set()),
            ),
            patch.object(
                AUDIT,
                "refresh_existing_judgment_summary",
                return_value={"reused": True},
            ),
            patch.object(
                AUDIT,
                "validate_source_record_partial_to_formalized_transition",
                transition,
            ),
            patch.object(AUDIT, "selected_surface_rebind_context", selected),
        )

    def test_cache_does_not_consult_rebind_when_exact_input_is_current(self) -> None:
        root, paper_dir, args, full_map, semantic_map, payload = self._cache_fixture()
        current = fingerprint(semantic_map=semantic_map)
        payload["source_record_input_fingerprint"] = current
        (paper_dir / "audit" / "source_record_audit.json").write_text(
            json.dumps(payload), encoding="utf-8"
        )
        selected = Mock(return_value=({"receipt": True}, Path("receipt"), ""))
        transition = Mock(return_value="transition should not run")
        with ExitStack() as stack:
            for item in self._cache_patches(
                current=current, selected=selected, transition=transition
            ):
                stack.enter_context(item)
            self.assertEqual(
                AUDIT.reusable_source_record_audit(
                    args,
                    root,
                    paper_dir,
                    paper_statement_map_sha256=full_map,
                    paper_statement_map_semantic_sha256=semantic_map,
                ),
                {"reused": True},
            )
        transition.assert_not_called()
        selected.assert_not_called()

    def test_cache_accepts_only_a_valid_rebind_after_normal_paths_fail(self) -> None:
        root, paper_dir, args, full_map, semantic_map, payload = self._cache_fixture()
        payload["source_record_input_fingerprint"] = fingerprint(semantic_map="b" * 64)
        payload["paper_statement_map_sha256"] = "c" * 64
        (paper_dir / "audit" / "source_record_audit.json").write_text(
            json.dumps(payload), encoding="utf-8"
        )
        current = fingerprint(semantic_map=semantic_map)
        selected = Mock(return_value=({"receipt": True}, Path("receipt"), ""))
        transition = Mock(return_value="not an exact status transition")
        with ExitStack() as stack:
            for item in self._cache_patches(
                current=current, selected=selected, transition=transition
            ):
                stack.enter_context(item)
            self.assertEqual(
                AUDIT.reusable_source_record_audit(
                    args,
                    root,
                    paper_dir,
                    paper_statement_map_sha256=full_map,
                    paper_statement_map_semantic_sha256=semantic_map,
                ),
                {"reused": True},
            )
        transition.assert_called_once()
        selected.assert_called_once()

        selected = Mock(
            return_value=(None, Path("receipt"), "selected content changed")
        )
        transition = Mock(return_value="not an exact status transition")
        with ExitStack() as stack:
            for item in self._cache_patches(
                current=current, selected=selected, transition=transition
            ):
                stack.enter_context(item)
            self.assertIsNone(
                AUDIT.reusable_source_record_audit(
                    args,
                    root,
                    paper_dir,
                    paper_statement_map_sha256=full_map,
                    paper_statement_map_semantic_sha256=semantic_map,
                )
            )
        selected.assert_called_once()

    def test_summary_rebind_runs_only_after_nonadministrative_map_failure(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            paper_dir = root / "papers" / "Fixture"
            audit_dir = paper_dir / "audit"
            audit_dir.mkdir(parents=True)
            audit_path = audit_dir / "source_record_audit.json"
            payload = {
                "paper": "Fixture",
                "prompt_version": AUDIT.SOURCE_RECORD_PROMPT_VERSION,
                "source_record_audit_sha256": "a" * 64,
                "paper_statement_map_sha256": "b" * 64,
                "source_record_input_fingerprint": fingerprint(semantic_map="c" * 64),
                "lean_check": {"returncode": 0},
                "conclusion_dependency_items": [],
            }
            audit_path.write_text(json.dumps(payload), encoding="utf-8")
            selected = Mock(return_value=({"receipt": True}, Path("receipt"), ""))
            with (
                patch.object(
                    AUDIT, "source_record_audit_receipt_error", return_value=""
                ),
                patch.object(
                    AUDIT, "direct_route_diagnostic_rebind_error", return_value=""
                ),
                patch.object(AUDIT, "selected_surface_rebind_context", selected),
                patch.object(AUDIT, "current_source_record_judgments", return_value=[]),
                patch.object(
                    AUDIT,
                    "current_approved_source_convention_antecedent_keys",
                    return_value=(set(), set()),
                ),
                patch.object(
                    AUDIT, "partition_conclusion_dependencies", return_value=([], [])
                ),
            ):
                refreshed = AUDIT.refresh_existing_judgment_summary(
                    paper_dir,
                    "Fixture",
                    audit_path,
                    paper_statement_map_sha256="d" * 64,
                    paper_statement_map_semantic_sha256="e" * 64,
                    write=False,
                )
            self.assertEqual(refreshed["resolved_conclusion_dependency_count"], 0)
            selected.assert_called_once()

            selected = Mock(
                return_value=(None, Path("receipt"), "selected content changed")
            )
            with (
                patch.object(
                    AUDIT, "source_record_audit_receipt_error", return_value=""
                ),
                patch.object(
                    AUDIT, "direct_route_diagnostic_rebind_error", return_value=""
                ),
                patch.object(AUDIT, "selected_surface_rebind_context", selected),
            ):
                with self.assertRaisesRegex(
                    SystemExit, "selected-surface rebind rejected"
                ):
                    AUDIT.refresh_existing_judgment_summary(
                        paper_dir,
                        "Fixture",
                        audit_path,
                        paper_statement_map_sha256="d" * 64,
                        paper_statement_map_semantic_sha256="e" * 64,
                        write=False,
                    )

    def test_identity_fallback_and_map_pin_require_the_rebind(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            paper_dir = root / "papers" / "Fixture"
            paper_dir.mkdir(parents=True)
            helper = (
                root
                / "skills"
                / "econcs-formalizer"
                / "scripts"
                / "source_record_audit.py"
            )
            helper.parent.mkdir(parents=True)
            helper.write_text("# identity fixture\n", encoding="utf-8")
            stored = fingerprint(semantic_map="a" * 64)
            audit_payload = {
                "paper": "Fixture",
                "source_record_audit_sha256": "b" * 64,
                "paper_statement_map_sha256": "c" * 64,
                "source_record_input_fingerprint": stored,
            }
            current = fingerprint(semantic_map="d" * 64)
            identity = {
                "paper": "Fixture",
                "paper_statement_map_sha256": "e" * 64,
                "paper_statement_map_semantic_sha256": "d" * 64,
                "source_record_input_fingerprint": current,
            }
            selected = Mock(return_value=({"receipt": True}, Path("receipt"), ""))
            previous_root = EVIDENCE.ROOT
            EVIDENCE.ROOT = root
            self.addCleanup(setattr, EVIDENCE, "ROOT", previous_root)
            exact_selected = Mock(return_value=({"receipt": True}, Path("receipt"), ""))
            exact_identity = {
                "paper": "Fixture",
                "paper_statement_map_sha256": "c" * 64,
                "paper_statement_map_semantic_sha256": "a" * 64,
                "source_record_input_fingerprint": stored,
            }
            with (
                patch.object(
                    EVIDENCE.subprocess,
                    "run",
                    return_value=SimpleNamespace(
                        returncode=0, stdout=json.dumps(exact_identity), stderr=""
                    ),
                ),
                patch.object(
                    EVIDENCE, "selected_surface_rebind_context", exact_selected
                ),
            ):
                self.assertEqual(
                    EVIDENCE.source_record_current_input_fingerprint_error(
                        paper_dir, audit_payload
                    ),
                    "",
                )
            exact_selected.assert_not_called()
            with (
                patch.object(
                    EVIDENCE.subprocess,
                    "run",
                    return_value=SimpleNamespace(
                        returncode=0, stdout=json.dumps(identity), stderr=""
                    ),
                ),
                patch.object(
                    EVIDENCE,
                    "validate_source_record_partial_to_formalized_transition",
                    return_value="not an exact status transition",
                ) as transition,
                patch.object(EVIDENCE, "selected_surface_rebind_context", selected),
            ):
                self.assertEqual(
                    EVIDENCE.source_record_current_input_fingerprint_error(
                        paper_dir, audit_payload
                    ),
                    "",
                )
            transition.assert_called_once()
            selected.assert_called_once()

            selected = Mock(
                return_value=(None, Path("receipt"), "selected content changed")
            )
            with (
                patch.object(
                    EVIDENCE.subprocess,
                    "run",
                    return_value=SimpleNamespace(
                        returncode=0, stdout=json.dumps(identity), stderr=""
                    ),
                ),
                patch.object(
                    EVIDENCE,
                    "validate_source_record_partial_to_formalized_transition",
                    return_value="not an exact status transition",
                ),
                patch.object(EVIDENCE, "selected_surface_rebind_context", selected),
            ):
                self.assertIn(
                    "selected-surface rebind rejected",
                    EVIDENCE.source_record_current_input_fingerprint_error(
                        paper_dir, audit_payload
                    ),
                )

            # The outer identity gate independently revalidates the receipt at
            # its map-pin boundary. It never treats a changed map pin alone as
            # sufficient evidence.
            current_surface_payload = {
                **audit_payload,
                "prompt_version": EVIDENCE.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION,
                "source_record_policy_version": EVIDENCE.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION,
            }
            selected = Mock(return_value=({"receipt": True}, Path("receipt"), ""))
            with (
                patch.object(
                    EVIDENCE, "source_record_audit_receipt_error", return_value=""
                ),
                patch.object(
                    EVIDENCE,
                    "source_record_raw_semantic_surface_error",
                    return_value="",
                ),
                patch.object(
                    EVIDENCE,
                    "source_record_raw_scan_completeness_error",
                    return_value="",
                ),
                patch.object(
                    EVIDENCE,
                    "source_record_raw_reusable_item_metadata_error",
                    return_value="",
                ),
                patch.object(
                    EVIDENCE,
                    "source_record_current_input_fingerprint_error",
                    return_value="",
                ),
                patch.object(
                    EVIDENCE,
                    "current_paper_statement_map_semantic_sha256",
                    return_value="d" * 64,
                ),
                patch.object(
                    EVIDENCE,
                    "current_paper_statement_map_sha256",
                    return_value="e" * 64,
                ),
                patch.object(EVIDENCE, "selected_surface_rebind_context", selected),
            ):
                self.assertEqual(
                    EVIDENCE.source_record_audit_identity_error(
                        current_surface_payload,
                        expected_paper_statement_map_sha256="e" * 64,
                        folder=paper_dir,
                    ),
                    "",
                )
            selected.assert_called_once()


if __name__ == "__main__":
    unittest.main()
