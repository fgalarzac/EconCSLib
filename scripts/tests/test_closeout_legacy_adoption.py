#!/usr/bin/env python3
"""Tests for one-time operational adoption of legacy closeout success."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import closeout_legacy_adoption as legacy_adoption
from scripts.closeout_legacy_adoption import (
    adopt_or_validate_legacy_completion,
    known_success_legacy_completion,
    legacy_adoption_path,
)


class CloseoutLegacyAdoptionTests(unittest.TestCase):
    @staticmethod
    def _legacy_pass() -> dict[str, object]:
        return {
            "state": "complete",
            "paper": "Fixture",
            "command": ["python3", "scripts/audit_repository.py"],
            "request": {"deep_paper_prose": False},
            "exit_code": 0,
            "result": {"semantic_closeout_passed": True},
        }

    def test_one_time_adoption_detects_later_material_change(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            prior = self._legacy_pass()
            adopted = adopt_or_validate_legacy_completion(
                root,
                paper="Fixture",
                plan_identity="a" * 64,
                deep_paper_prose=False,
                prior_execution=prior,
                rollout_baseline={"ready": True},
            )
            self.assertEqual(adopted["state"], "current")

            changed = adopt_or_validate_legacy_completion(
                root,
                paper="Fixture",
                plan_identity="b" * 64,
                deep_paper_prose=False,
                prior_execution=prior,
                rollout_baseline={"ready": True},
            )
            self.assertEqual(changed["state"], "material_changed")
            self.assertEqual(changed["adopted_plan_identity"], "a" * 64)

    def test_unknown_schema_or_incomplete_result_is_not_adopted(self) -> None:
        prior = self._legacy_pass()
        prior["result"] = {
            "semantic_closeout_passed": True,
            "operational_plan_identity_schema": "unknown-v3",
        }
        self.assertFalse(
            known_success_legacy_completion(
                prior, paper="Fixture", deep_paper_prose=False
            )
        )
        prior["result"] = {}
        self.assertFalse(
            known_success_legacy_completion(
                prior, paper="Fixture", deep_paper_prose=False
            )
        )

    def test_wrong_paper_completion_is_not_adopted(self) -> None:
        prior = self._legacy_pass()
        prior["paper"] = "Other"
        self.assertFalse(
            known_success_legacy_completion(
                prior, paper="Fixture", deep_paper_prose=False
            )
        )
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            adoption = adopt_or_validate_legacy_completion(
                root,
                paper="Fixture",
                plan_identity="a" * 64,
                deep_paper_prose=False,
                prior_execution=prior,
                rollout_baseline={"ready": True},
            )
        self.assertEqual(adoption["state"], "not_applicable")

    def test_deleted_adoption_cannot_reset_after_rollout_material_change(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            prior = self._legacy_pass()
            adopted = adopt_or_validate_legacy_completion(
                root,
                paper="Fixture",
                plan_identity="a" * 64,
                deep_paper_prose=False,
                prior_execution=prior,
                rollout_baseline={"ready": True},
            )
            self.assertEqual(adopted["state"], "current")
            legacy_adoption_path(root, "Fixture").unlink()

            changed = adopt_or_validate_legacy_completion(
                root,
                paper="Fixture",
                plan_identity="b" * 64,
                deep_paper_prose=False,
                prior_execution=prior,
                rollout_baseline={
                    "ready": False,
                    "state": "material_changed",
                    "errors": ["paper material differs from rollout"],
                },
            )
            self.assertEqual(changed["state"], "material_changed")
            self.assertIn("differs from rollout", changed["error"])

    def test_normal_profile_completion_is_not_adopted_for_deep_closeout(self) -> None:
        prior = self._legacy_pass()
        self.assertFalse(
            known_success_legacy_completion(
                prior, paper="Fixture", deep_paper_prose=True
            )
        )
        prior["request"] = {"deep_paper_prose": True}
        self.assertTrue(
            known_success_legacy_completion(
                prior, paper="Fixture", deep_paper_prose=True
            )
        )

    def test_normal_and_deep_profiles_have_independent_adoption_records(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            prior = self._legacy_pass()
            prior["request"] = {"deep_paper_prose": True}

            normal = adopt_or_validate_legacy_completion(
                root,
                paper="Fixture",
                plan_identity="a" * 64,
                deep_paper_prose=False,
                prior_execution=prior,
                rollout_baseline={"ready": True},
            )
            deep = adopt_or_validate_legacy_completion(
                root,
                paper="Fixture",
                plan_identity="b" * 64,
                deep_paper_prose=True,
                prior_execution=prior,
                rollout_baseline={"ready": True},
            )

            self.assertEqual(normal["state"], "current")
            self.assertEqual(deep["state"], "current")
            self.assertNotEqual(normal["path"], deep["path"])

    def test_replaced_lock_path_retries_before_adoption(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            (root / "papers" / "Fixture").mkdir(parents=True)
            record_path = legacy_adoption_path(root, "Fixture")
            lock_path = record_path.with_suffix(record_path.suffix + ".lock")
            original_flock = legacy_adoption.fcntl.flock
            replaced = False

            def replace_after_lock(fd: int, operation: int) -> None:
                nonlocal replaced
                original_flock(fd, operation)
                if not replaced:
                    replaced = True
                    lock_path.unlink()
                    lock_path.write_text("replacement", encoding="utf-8")

            with mock.patch.object(
                legacy_adoption.fcntl, "flock", side_effect=replace_after_lock
            ):
                adopted = adopt_or_validate_legacy_completion(
                    root,
                    paper="Fixture",
                    plan_identity="a" * 64,
                    deep_paper_prose=False,
                    prior_execution=self._legacy_pass(),
                    rollout_baseline={"ready": True},
                )

            self.assertTrue(replaced)
            self.assertEqual(adopted["state"], "current")


if __name__ == "__main__":
    unittest.main()
