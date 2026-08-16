#!/usr/bin/env python3
"""Focused regressions for semantic raw-producer provenance compatibility."""

from __future__ import annotations

import copy
import unittest

from scripts.source_record_raw_producer_compatibility import (
    RAW_PRODUCER_COMPATIBILITY_INVARIANT,
    source_record_fingerprint_matches_with_raw_producer_compatibility,
)


def identity_set(label: str) -> list[dict[str, str]]:
    return [
        {
            "path": "scripts/lean_signature_manifest_helper.lean",
            "sha256": "a" * 63 + label,
            "status": "present",
        },
        {
            "path": (
                "skills/econcs-formalizer/scripts/"
                "source_record_audit.py#fresh-raw-generation"
            ),
            "sha256": "b" * 63 + label,
            "status": "present",
        },
    ]


def fingerprint(identity_label: str, *, feature: str = "base") -> dict[str, object]:
    return {
        "schema": 10,
        "paper": "Fixture",
        "paper_statement_map_semantic_sha256": "c" * 64,
        "source_artifact_identities": [
            {"path": "papers/Fixture/source.txt", "sha256": "d" * 64, "status": "present"}
        ],
        "lean_dependency_identities": [
            {"path": "papers/Fixture/PaperInterface.lean", "sha256": "e" * 64, "status": "present"}
        ],
        "audit_engine_identities": [
            {
                "path": "feature",
                "surface_semantic_version": feature,
            }
        ],
        "raw_producer_code_identity_schema": 1,
        "raw_producer_code_identities": identity_set(identity_label),
    }


def compatible_ledger(
    *edges: tuple[str, str],
    semantic_break_before_last: bool = False,
) -> dict[str, object]:
    revisions: list[dict[str, object]] = [
        {"relation_to_previous": "bootstrap"}
    ]
    for index, (predecessor, successor) in enumerate(edges):
        if semantic_break_before_last and index == len(edges) - 1:
            revisions.append({"relation_to_previous": "review_semantics_changed"})
        revisions.append(
            {
                "relation_to_previous": "review_compatible",
                "raw_producer_compatibility": {
                    "schema": 1,
                    "invariant": RAW_PRODUCER_COMPATIBILITY_INVARIANT,
                    "predecessor_raw_producer_code_identity_sets": [
                        identity_set(predecessor)
                    ],
                    "successor_raw_producer_code_identities": identity_set(
                        successor
                    ),
                },
            }
        )
    return {"revisions": revisions}


class RawProducerCompatibilityTests(unittest.TestCase):
    def test_registered_producer_only_transition_reuses_exact_nonproducer_inputs(
        self,
    ) -> None:
        self.assertTrue(
            source_record_fingerprint_matches_with_raw_producer_compatibility(
                fingerprint("1"),
                fingerprint("2"),
                ledger=compatible_ledger(("1", "2")),
            )
        )

    def test_feature_identity_change_cannot_use_provenance_grant(self) -> None:
        self.assertFalse(
            source_record_fingerprint_matches_with_raw_producer_compatibility(
                fingerprint("1", feature="base"),
                fingerprint("2", feature="new-source-route"),
                ledger=compatible_ledger(("1", "2")),
            )
        )

    def test_source_or_lean_input_change_cannot_use_provenance_grant(self) -> None:
        stored = fingerprint("1")
        current = fingerprint("2")
        current["source_artifact_identities"] = [
            {
                "path": "papers/Fixture/source.txt",
                "sha256": "f" * 64,
                "status": "present",
            }
        ]
        self.assertFalse(
            source_record_fingerprint_matches_with_raw_producer_compatibility(
                stored,
                current,
                ledger=compatible_ledger(("1", "2")),
            )
        )

    def test_unknown_or_dirty_current_producer_identity_is_rejected(self) -> None:
        self.assertFalse(
            source_record_fingerprint_matches_with_raw_producer_compatibility(
                fingerprint("1"),
                fingerprint("3"),
                ledger=compatible_ledger(("1", "2")),
            )
        )

    def test_chain_reuses_only_within_one_review_semantic_era(self) -> None:
        self.assertTrue(
            source_record_fingerprint_matches_with_raw_producer_compatibility(
                fingerprint("1"),
                fingerprint("3"),
                ledger=compatible_ledger(("1", "2"), ("2", "3")),
            )
        )
        self.assertFalse(
            source_record_fingerprint_matches_with_raw_producer_compatibility(
                fingerprint("1"),
                fingerprint("3"),
                ledger=compatible_ledger(
                    ("1", "2"),
                    ("2", "3"),
                    semantic_break_before_last=True,
                ),
            )
        )

    def test_exact_current_fingerprint_does_not_need_a_grant(self) -> None:
        current = fingerprint("2")
        self.assertTrue(
            source_record_fingerprint_matches_with_raw_producer_compatibility(
                current,
                copy.deepcopy(current),
                ledger={"revisions": []},
            )
        )


if __name__ == "__main__":
    unittest.main()
