#!/usr/bin/env python3
"""Focused tests for source-record fingerprint replay in the evidence gate."""

from __future__ import annotations

import copy
import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

from scripts import audit_evidence_integrity as evidence
from scripts.source_record_raw_producer_compatibility import (
    RAW_PRODUCER_COMPATIBILITY_INVARIANT,
)


class SourceRecordFingerprintValidationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.paper = self.root / "papers" / "Fixture"
        self.paper.mkdir(parents=True)
        helper = (
            self.root
            / "skills"
            / "econcs-formalizer"
            / "scripts"
            / "source_record_audit.py"
        )
        helper.parent.mkdir(parents=True)
        helper.write_text("# identity helper fixture\n", encoding="utf-8")

    @staticmethod
    def _fingerprint(schema: int, **updates: object) -> dict[str, object]:
        fingerprint: dict[str, object] = {
            "schema": schema,
            "paper": "Fixture",
            "max_depth": 4,
            "no_lean": False,
            "paper_statement_map_semantic_sha256": "c" * 64,
        }
        fingerprint.update(updates)
        return fingerprint

    def test_schema10_uses_direct_identity_and_payload_bound_watch(self) -> None:
        current = self._fingerprint(10)
        raw = {
            "paper_statement_map_sha256": "a" * 64,
            "source_record_input_fingerprint": current,
        }
        identity = {
            "paper": "Fixture",
            "paper_statement_map_sha256": "a" * 64,
            "paper_statement_map_semantic_sha256": "c" * 64,
            "source_record_input_fingerprint": current,
        }
        watch = mock.Mock(return_value="stable-watch")
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence,
                "_source_record_identity_process_watch_digest",
                watch,
            ),
            mock.patch.object(
                evidence.subprocess,
                "run",
                return_value=SimpleNamespace(
                    returncode=0, stdout=json.dumps(identity), stderr=""
                ),
            ) as run,
            mock.patch.object(
                evidence,
                "validate_source_record_partial_to_formalized_transition",
                side_effect=AssertionError(
                    "exact schema-10 identity must not transition"
                ),
            ),
        ):
            error = evidence.source_record_current_input_fingerprint_error(
                self.paper, raw
            )

        self.assertEqual(error, "")
        self.assertNotIn("--include-legacy-fingerprint", run.call_args.args[0])
        self.assertEqual(
            watch.call_args_list,
            [
                mock.call(self.paper, audit_payload=raw),
                mock.call(self.paper, audit_payload=raw),
            ],
        )

    def test_schema10_registered_producer_transition_reuses_only_same_semantics(
        self,
    ) -> None:
        def identities(letter: str) -> list[dict[str, str]]:
            return [
                {
                    "path": "scripts/lean_signature_manifest_helper.lean",
                    "sha256": "a" * 63 + letter,
                    "status": "present",
                },
                {
                    "path": (
                        "skills/econcs-formalizer/scripts/"
                        "source_record_audit.py#fresh-raw-generation"
                    ),
                    "sha256": "b" * 63 + letter,
                    "status": "present",
                },
            ]

        stored = self._fingerprint(
            10,
            audit_engine_identities=[
                {
                    "path": "feature",
                    "surface_semantic_version": "base",
                }
            ],
            raw_producer_code_identity_schema=1,
            raw_producer_code_identities=identities("1"),
        )
        current = copy.deepcopy(stored)
        current["raw_producer_code_identities"] = identities("2")
        raw = {
            "paper_statement_map_sha256": "a" * 64,
            "source_record_input_fingerprint": stored,
        }
        identity = {
            "paper": "Fixture",
            "paper_statement_map_sha256": "a" * 64,
            "paper_statement_map_semantic_sha256": "c" * 64,
            "source_record_input_fingerprint": current,
        }
        ledger = {
            "revisions": [
                {
                    "relation_to_previous": "review_compatible",
                    "raw_producer_compatibility": {
                        "schema": 1,
                        "invariant": RAW_PRODUCER_COMPATIBILITY_INVARIANT,
                        "predecessor_raw_producer_code_identity_sets": [
                            identities("1")
                        ],
                        "successor_raw_producer_code_identities": identities("2"),
                    },
                }
            ]
        }
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence,
                "_source_record_identity_process_watch_digest",
                return_value="stable-watch",
            ),
            mock.patch.object(
                evidence.subprocess,
                "run",
                return_value=SimpleNamespace(
                    returncode=0, stdout=json.dumps(identity), stderr=""
                ),
            ),
            mock.patch.object(
                evidence,
                "validated_runtime_raw_producer_compatibility_ledger",
                return_value=ledger,
            ),
        ):
            self.assertEqual(
                evidence.source_record_current_input_fingerprint_error(
                    self.paper, raw
                ),
                "",
            )

        changed_feature = copy.deepcopy(current)
        changed_feature["audit_engine_identities"] = [
            {
                "path": "feature",
                "surface_semantic_version": "changed",
            }
        ]
        changed_identity = dict(identity)
        changed_identity["source_record_input_fingerprint"] = changed_feature
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence,
                "_source_record_identity_process_watch_digest",
                return_value="stable-watch",
            ),
            mock.patch.object(
                evidence.subprocess,
                "run",
                return_value=SimpleNamespace(
                    returncode=0,
                    stdout=json.dumps(changed_identity),
                    stderr="",
                ),
            ),
            mock.patch.object(
                evidence,
                "validated_runtime_raw_producer_compatibility_ledger",
                return_value=ledger,
            ),
            mock.patch.object(
                evidence,
                "validate_source_record_partial_to_formalized_transition",
                return_value="not a status-only transition",
            ),
            mock.patch.object(
                evidence,
                "selected_surface_rebind_context",
                return_value=(None, None, "not installed"),
            ),
        ):
            self.assertIn(
                "source_record_input_fingerprint is stale",
                evidence.source_record_current_input_fingerprint_error(
                    self.paper, raw
                ),
            )

    def test_schema9_accepts_only_the_emitted_exact_legacy_replay(self) -> None:
        current = self._fingerprint(
            10,
            formalization_coverage_protocol_sha256="d" * 64,
        )
        legacy_v9 = self._fingerprint(
            9,
            formalization_protocol_sha256="e" * 64,
            source_record_policy_version="legacy-review-policy",
        )
        raw = {
            # Schema 9 permits byte-only map drift when its own semantic pin is
            # unchanged, even though schema 10 uses a different projection.
            "paper_statement_map_sha256": "a" * 64,
            "source_record_input_fingerprint": legacy_v9,
        }
        identity = {
            "paper": "Fixture",
            "paper_statement_map_sha256": "b" * 64,
            "paper_statement_map_semantic_sha256": "f" * 64,
            "source_record_input_fingerprint": current,
            "legacy_v9_source_record_input_fingerprint": legacy_v9,
        }
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence,
                "_source_record_identity_process_watch_digest",
                return_value="stable-watch",
            ),
            mock.patch.object(
                evidence.subprocess,
                "run",
                return_value=SimpleNamespace(
                    returncode=0, stdout=json.dumps(identity), stderr=""
                ),
            ) as run,
            mock.patch.object(
                evidence,
                "validate_source_record_partial_to_formalized_transition",
                side_effect=AssertionError(
                    "exact schema-9 replay must not transition"
                ),
            ),
        ):
            error = evidence.source_record_current_input_fingerprint_error(
                self.paper, raw
            )

        self.assertEqual(error, "")
        self.assertIn("--include-legacy-fingerprint", run.call_args.args[0])

    def test_schema9_replay_mismatch_falls_through_to_transition_checks(self) -> None:
        current = self._fingerprint(10)
        emitted_legacy_v9 = self._fingerprint(
            9, formalization_protocol_sha256="d" * 64
        )
        stored_legacy_v9 = copy.deepcopy(emitted_legacy_v9)
        stored_legacy_v9["formalization_protocol_sha256"] = "e" * 64
        raw = {
            "paper_statement_map_sha256": "a" * 64,
            "source_record_input_fingerprint": stored_legacy_v9,
        }
        identity = {
            "paper": "Fixture",
            "paper_statement_map_sha256": "a" * 64,
            "paper_statement_map_semantic_sha256": "c" * 64,
            "source_record_input_fingerprint": current,
            "legacy_v9_source_record_input_fingerprint": emitted_legacy_v9,
        }
        transition = mock.Mock(return_value="not an authorized transition")
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence,
                "_source_record_identity_process_watch_digest",
                return_value="stable-watch",
            ),
            mock.patch.object(
                evidence.subprocess,
                "run",
                return_value=SimpleNamespace(
                    returncode=0, stdout=json.dumps(identity), stderr=""
                ),
            ),
            mock.patch.object(
                evidence,
                "validate_source_record_partial_to_formalized_transition",
                transition,
            ),
            mock.patch.object(
                evidence,
                "selected_surface_rebind_context",
                return_value=(None, None, "not installed"),
            ),
        ):
            error = evidence.source_record_current_input_fingerprint_error(
                self.paper, raw
            )

        self.assertIn("source_record_input_fingerprint is stale", error)
        transition.assert_called_once()

    def test_legacy_v6_replay_via_v7_identity_remains_available(self) -> None:
        current_v7 = self._fingerprint(7)
        stored_v6 = copy.deepcopy(current_v7)
        stored_v6["schema"] = 6
        stored_v6.pop("paper_statement_map_semantic_sha256")
        stored_v6["paper_statement_map_sha256"] = "a" * 64
        raw = {
            "paper_statement_map_sha256": "a" * 64,
            "source_record_input_fingerprint": stored_v6,
        }
        identity = {
            "paper": "Fixture",
            "paper_statement_map_sha256": "a" * 64,
            "paper_statement_map_semantic_sha256": "c" * 64,
            "source_record_input_fingerprint": current_v7,
        }
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence,
                "_source_record_identity_process_watch_digest",
                return_value="stable-watch",
            ),
            mock.patch.object(
                evidence.subprocess,
                "run",
                return_value=SimpleNamespace(
                    returncode=0, stdout=json.dumps(identity), stderr=""
                ),
            ),
            mock.patch.object(
                evidence,
                "validate_source_record_partial_to_formalized_transition",
                side_effect=AssertionError(
                    "exact v6 compatibility must not transition"
                ),
            ),
        ):
            error = evidence.source_record_current_input_fingerprint_error(
                self.paper, raw
            )

        self.assertEqual(error, "")


if __name__ == "__main__":
    unittest.main()
