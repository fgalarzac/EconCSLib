#!/usr/bin/env python3
"""Regression tests for closeout raw-reissue engine-wave admission."""

from __future__ import annotations

import fcntl
import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import closeout_wave_engine as wave


def projection(
    *, engine: str = "a", protocol: str = "b", sequence: int = 1
) -> dict[str, object]:
    return {
        "engine_tree_sha256": engine * 64,
        "review_semantic_class_sha256": protocol * 64,
        "revision_sequence": sequence,
        "relation_to_previous": "initial" if sequence == 1 else "compatible",
        "engine_file_count": 1,
    }


class CloseoutWaveEngineTests(unittest.TestCase):
    def test_first_wave_is_immutable_until_an_explicit_reset(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            current = projection()
            with mock.patch.object(
                wave, "current_registered_engine_projection", return_value=(current, "")
            ):
                first, created, error = wave.ensure_closeout_wave_engine_snapshot(root)
                self.assertEqual(error, "")
                self.assertTrue(created)
                assert first is not None
                snapshot_path = wave.closeout_wave_engine_snapshot_path(root)
                original_bytes = snapshot_path.read_bytes()

                second, created_again, error = wave.ensure_closeout_wave_engine_snapshot(
                    root
                )

            self.assertEqual(error, "")
            self.assertFalse(created_again)
            self.assertEqual(second, first)
            self.assertEqual(snapshot_path.read_bytes(), original_bytes)
            self.assertFalse(first["acceptance_credential"])
            self.assertTrue(first["operational_recovery_only"])

    def test_registered_transition_requires_reset_without_replacing_snapshot(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            first_projection = projection()
            with mock.patch.object(
                wave,
                "current_registered_engine_projection",
                return_value=(first_projection, ""),
            ):
                first, _created, error = wave.ensure_closeout_wave_engine_snapshot(root)
            self.assertEqual(error, "")
            assert first is not None
            snapshot_path = wave.closeout_wave_engine_snapshot_path(root)
            original_bytes = snapshot_path.read_bytes()
            changed_projection = projection(engine="c", sequence=2)
            with mock.patch.object(
                wave,
                "current_registered_engine_projection",
                return_value=(changed_projection, ""),
            ):
                state = wave.closeout_wave_engine_snapshot_state(root)
                rebound, created, error = wave.ensure_closeout_wave_engine_snapshot(root)

            self.assertEqual(state["state"], "reset_required")
            self.assertIsNone(rebound)
            self.assertFalse(created)
            self.assertIn("explicitly reset", error)
            self.assertEqual(snapshot_path.read_bytes(), original_bytes)

    def test_malformed_snapshot_fails_closed_without_mutation(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            path = wave.closeout_wave_engine_snapshot_path(root)
            path.parent.mkdir(parents=True)
            path.write_text("not json\n", encoding="utf-8")
            original_bytes = path.read_bytes()

            state = wave.closeout_wave_engine_snapshot_state(root)

            self.assertEqual(state["state"], "invalid")
            self.assertIn("could not read", str(state["reason"]))
            self.assertEqual(path.read_bytes(), original_bytes)

    def test_operation_receipt_path_rejects_nonpaper_path(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            self.assertIsNone(
                wave.closeout_raw_reissue_operation_receipt_path(
                    Path(temp_dir), "../outside"
                )
            )

    def test_operation_receipt_state_fails_closed_on_malformed_or_running_data(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper = "Fixture"
            path = wave.closeout_raw_reissue_operation_receipt_path(root, paper)
            assert path is not None
            path.parent.mkdir(parents=True)
            path.write_text("not json\n", encoding="utf-8")
            malformed = wave.closeout_raw_reissue_operation_receipt_state(root, paper)
            self.assertEqual(malformed["state"], "invalid")

            path.write_text(
                json.dumps(
                    {
                        "schema": wave.RAW_REISSUE_OPERATION_TRACE_SCHEMA,
                        "kind": "source_record_raw_reissue_operation",
                        "acceptance_credential": False,
                        "operational_recovery_only": True,
                        "state": "running",
                        "paper": paper,
                        "operation_id": "fixture-operation",
                    }
                ),
                encoding="utf-8",
            )
            running = wave.closeout_raw_reissue_operation_receipt_state(root, paper)
            self.assertEqual(running["state"], "running")

    def test_raw_admission_requires_matching_running_wrapper_operation(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper = "Fixture"
            current = projection()
            with mock.patch.object(
                wave, "current_registered_engine_projection", return_value=(current, "")
            ):
                snapshot, _created, error = wave.ensure_closeout_wave_engine_snapshot(root)
                self.assertEqual(error, "")
                assert snapshot is not None
                operation_id = "fixture-operation"
                operation_path = wave.closeout_raw_reissue_operation_receipt_path(
                    root, paper
                )
                assert operation_path is not None
                operation_path.parent.mkdir(parents=True)
                operation_path.write_text(
                    json.dumps(
                        {
                            "schema": wave.RAW_REISSUE_OPERATION_TRACE_SCHEMA,
                            "kind": "source_record_raw_reissue_operation",
                            "acceptance_credential": False,
                            "operational_recovery_only": True,
                            "state": "running",
                            "paper": paper,
                            "operation_id": operation_id,
                            "wave_id": snapshot["wave_id"],
                            "engine_registration": snapshot["engine_registration"],
                        }
                    ),
                    encoding="utf-8",
                )
                lock_path = root / wave.CLOSEOUT_RAW_REISSUE_LOCK_RELATIVE_PATH
                lock_path.parent.mkdir(parents=True, exist_ok=True)
                with lock_path.open("a+", encoding="utf-8") as handle:
                    fcntl.flock(handle.fileno(), fcntl.LOCK_EX)
                    handle.seek(0)
                    handle.truncate()
                    handle.write(
                        json.dumps(
                            {
                                "schema": wave.CLOSEOUT_RAW_REISSUE_LOCK_STATUS_SCHEMA,
                                "paper": paper,
                                "operation": "freeze_then_raw_reissue",
                                "operation_id": operation_id,
                            }
                        )
                    )
                    handle.flush()
                    self.assertEqual(
                        wave.closeout_raw_reissue_admission_error(
                            root, paper, operation_id
                        ),
                        "",
                    )
                    self.assertIn(
                        "wrapper lease",
                        wave.closeout_raw_reissue_admission_error(
                            root, paper, "other-operation"
                        ),
                    )
                    handle.seek(0)
                    handle.truncate()
                    handle.write(
                        json.dumps(
                            {
                                "schema": wave.CLOSEOUT_RAW_REISSUE_LOCK_STATUS_SCHEMA,
                                "paper": paper,
                                "operation": "freeze_then_raw_reissue",
                                "operation_id": "other-operation",
                            }
                        )
                    )
                    handle.flush()
                    self.assertIn(
                        "wrapper lease",
                        wave.closeout_raw_reissue_admission_error(
                            root, paper, operation_id
                        ),
                    )
                    fcntl.flock(handle.fileno(), fcntl.LOCK_UN)


if __name__ == "__main__":
    unittest.main()
