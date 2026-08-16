"""Adversarial tests for the exact coverage schema-4-to-schema-5 transport."""

from __future__ import annotations

import copy
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import paper_coverage_schema4_to5_rebind as REBIND
from scripts import review_dashboard
from scripts.source_coverage_scope import (
    LEGACY_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
    NAMED_THEORETICAL_STATEMENTS,
    SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
    legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded,
    source_item_coverage_sha256,
)
from scripts.source_record_integrity import stamp_source_record_audit_receipts


PAPER = "FixturePaper"


def digest(character: str) -> str:
    return character * 64


class PaperCoverageSchema4To5RebindTests(unittest.TestCase):
    def build_fixture(self) -> dict[str, object]:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name) / "repository"
        folder = root / "papers" / PAPER
        audit = folder / "audit"
        audit.mkdir(parents=True)

        source_statement = "Theorem 1. Every admissible input has the checked property."
        source_text = source_statement + "\n"
        (folder / "source.txt").write_text(source_text, encoding="utf-8")
        source_digest = hashlib.sha256(source_text.encode("utf-8")).hexdigest()
        quote_digest = hashlib.sha256(source_statement.encode("utf-8")).hexdigest()
        interface = folder / "PaperInterface.lean"
        interface.write_text(
            "namespace FixturePaper\n"
            "theorem current_endpoint : True := trivial\n"
            "end FixturePaper\n",
            encoding="utf-8",
        )
        interface_digest = hashlib.sha256(interface.read_bytes()).hexdigest()

        # The source navigation key is intentionally unrelated to either the
        # coverage-sidecar key or the saved review-row name.
        source_key = "current_source_navigation_only"
        statement_map = {
            "source_curated": True,
            "source_inventory_kind": "curated_test",
            "source_coverage_mode": NAMED_THEORETICAL_STATEMENTS,
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": source_digest,
            "items": {
                source_key: {
                    "title": "Theorem 1",
                    "statement": source_statement,
                    "source_kind": "theorem",
                    "claim_bearing": True,
                    "source_url": "https://example.invalid/paper",
                    "source_location": "source.txt:1-1",
                    "source_anchor_evidence": [
                        {
                            "path": "source.txt",
                            "line_start": 1,
                            "line_end": 1,
                            "quoted_text": source_statement,
                            "quoted_text_sha256": quote_digest,
                        }
                    ],
                }
            },
        }
        map_path = audit / "paper_statement_map.json"
        self.write_json(map_path, statement_map)
        map_bytes = map_path.read_bytes()
        _full, inventory, mode, mode_error = review_dashboard.paper_coverage_inventory(
            folder
        )
        self.assertFalse(mode_error)
        self.assertEqual(set(inventory), {source_key})
        source_item = inventory[source_key]
        target_digest = review_dashboard._source_item_coverage_statement(source_item)[1]
        legacy_digest = legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded(
            source_item, mode
        )
        current_digest = source_item_coverage_sha256(source_item, mode)
        legacy_inventory_digest = REBIND._legacy_inventory_digest(
            inventory, mode=mode, statement_map=statement_map
        )

        raw_audit = {
            "paper": PAPER,
            "prompt_version": REBIND.SOURCE_RECORD_V10_PROMPT_VERSION,
            "source_record_policy_version": REBIND.SOURCE_RECORD_V10_PROMPT_VERSION,
            "paper_statement_map_sha256": hashlib.sha256(map_bytes).hexdigest(),
            "source_coverage_mode": mode,
            "review_interface_source": {
                "path": f"papers/{PAPER}/PaperInterface.lean",
                "sha256": interface_digest,
            },
            "fresh_source_elaboration": {
                "returncode": 0,
                "source_sha256": interface_digest,
            },
            "configured_review_row_count": 1,
        }
        stamp_source_record_audit_receipts(raw_audit)
        raw_path = audit / "source_record_audit.json"
        self.write_json(raw_path, raw_audit)

        signature = digest("c")
        statement_audit = {
            "schema": 1,
            "paper": PAPER,
            "prompt_version": review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION,
            "source_record_audit_sha256": raw_audit["source_record_audit_sha256"],
            "validator": "fixture semantic reviewer",
            "validator_type": "manual_semantic_v10",
            "validated_at": "2026-07-28T00:00:00Z",
            # This name deliberately does not occur in the coverage row.
            "items": {
                "current_statement_navigation_only": {
                    "judgment": "matches",
                    "lean_signature_sha256": signature,
                    "lean_statement_sha256": digest("d"),
                    "paper_statement_sha256": target_digest,
                    "prompt_version": review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION,
                    "validator": "fixture semantic reviewer",
                    "validator_type": "manual_semantic_v10",
                    "validated_at": "2026-07-28T00:00:00Z",
                    "reason": "Exact source and Lean semantic judgment.",
                }
            },
        }
        statement_path = audit / "statement_match_llm.json"
        self.write_json(statement_path, statement_audit)

        surface_digest = digest("e")
        surface_audit = {
            "schema": 1,
            "paper": PAPER,
            "prompt_version": review_dashboard.REQUIRED_LLM_REVIEW_SURFACE_PROMPT_VERSION,
            "judgment": "passes",
            "review_rows": 1,
            "review_surface_sha256": surface_digest,
            "validator": "fixture surface reviewer",
            "validator_type": "manual_semantic_v10",
            "validated_at": "2026-07-28T00:00:00Z",
        }
        surface_path = audit / "review_surface_llm.json"
        self.write_json(surface_path, surface_audit)

        saved_row = "old_review_navigation_only"
        coverage = {
            "schema": 1,
            "paper": PAPER,
            "prompt_version": review_dashboard.REQUIRED_LLM_PAPER_COVERAGE_PROMPT_VERSION,
            "audit_kind": "source_to_dashboard_agent",
            "source_grounded": True,
            "validator": "fixture coverage reviewer",
            "validator_type": "manual_semantic_v10",
            "validated_at": "2026-07-28T00:00:00Z",
            "source_coverage_mode": mode,
            "source_artifact_path": "source.txt",
            "source_artifact_sha256": source_digest,
            "paper_statement_inventory_sha256": legacy_inventory_digest,
            "review_surface_sha256": surface_digest,
            "items": {
                "old_coverage_navigation_only": {
                    "coverage": "covered",
                    "review_rows": [saved_row],
                    "review_row_signature_sha256": {saved_row: signature},
                    "reason": "The reviewed theorem establishes the exact source property.",
                    "source_evidence": "Pinned source anchor at source.txt:1-1.",
                    "statement_sha256": target_digest,
                    "source_item_coverage_digest_schema": (
                        LEGACY_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA
                    ),
                    "source_item_coverage_sha256": legacy_digest,
                    "validator": "fixture coverage reviewer",
                    "validator_type": "manual_semantic_v10",
                    "validated_at": "2026-07-28T00:00:00Z",
                }
            },
        }
        coverage_path = audit / "paper_coverage_llm.json"
        self.write_json(coverage_path, coverage)

        return {
            "root": root,
            "folder": folder,
            "audit": audit,
            "coverage_path": coverage_path,
            "map_path": map_path,
            "raw_path": raw_path,
            "statement_path": statement_path,
            "surface_path": surface_path,
            "source_key": source_key,
            "saved_row": saved_row,
            "current_statement_key": "current_statement_navigation_only",
            "legacy_digest": legacy_digest,
            "current_digest": current_digest,
        }

    def add_second_semantic_item(self, fixture: dict[str, object]) -> dict[str, object]:
        """Extend the fixture so a key-based pairing would be observable."""

        folder = fixture["folder"]
        map_path = fixture["map_path"]
        raw_path = fixture["raw_path"]
        statement_path = fixture["statement_path"]
        surface_path = fixture["surface_path"]
        coverage_path = fixture["coverage_path"]
        assert all(
            isinstance(path, Path)
            for path in (
                folder,
                map_path,
                raw_path,
                statement_path,
                surface_path,
                coverage_path,
            )
        )

        second_statement = "Theorem 2. Every checked output has the other property."
        source_path = folder / "source.txt"
        source_text = source_path.read_text(encoding="utf-8").rstrip("\n") + "\n" + second_statement + "\n"
        source_path.write_text(source_text, encoding="utf-8")
        source_digest = hashlib.sha256(source_text.encode("utf-8")).hexdigest()

        statement_map = self.read_json(map_path)
        statement_map["source_artifact_sha256"] = source_digest
        map_items = statement_map["items"]
        assert isinstance(map_items, dict)
        second_source_key = "other_current_source_navigation_only"
        map_items[second_source_key] = {
            "title": "Theorem 2",
            "statement": second_statement,
            "source_kind": "theorem",
            "claim_bearing": True,
            "source_url": "https://example.invalid/paper",
            "source_location": "source.txt:2-2",
            "source_anchor_evidence": [
                {
                    "path": "source.txt",
                    "line_start": 2,
                    "line_end": 2,
                    "quoted_text": second_statement,
                    "quoted_text_sha256": hashlib.sha256(
                        second_statement.encode("utf-8")
                    ).hexdigest(),
                }
            ],
        }
        self.write_json(map_path, statement_map)
        _full, inventory, mode, mode_error = review_dashboard.paper_coverage_inventory(
            folder
        )
        self.assertFalse(mode_error)
        second_item = inventory[second_source_key]
        second_target = review_dashboard._source_item_coverage_statement(second_item)[1]
        second_legacy = legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded(
            second_item, mode
        )
        second_current = source_item_coverage_sha256(second_item, mode)

        raw = self.read_json(raw_path)
        raw["paper_statement_map_sha256"] = hashlib.sha256(map_path.read_bytes()).hexdigest()
        raw["configured_review_row_count"] = 2
        stamp_source_record_audit_receipts(raw)
        self.write_json(raw_path, raw)

        second_signature = digest("b")
        statement_audit = self.read_json(statement_path)
        statement_audit["source_record_audit_sha256"] = raw[
            "source_record_audit_sha256"
        ]
        statement_items = statement_audit["items"]
        assert isinstance(statement_items, dict)
        second_statement_key = "other_current_statement_navigation_only"
        statement_items[second_statement_key] = {
            "judgment": "matches",
            "lean_signature_sha256": second_signature,
            "lean_statement_sha256": digest("a"),
            "paper_statement_sha256": second_target,
            "prompt_version": review_dashboard.REQUIRED_LLM_STATEMENT_PROMPT_VERSION,
            "validator": "fixture semantic reviewer",
            "validator_type": "manual_semantic_v10",
            "validated_at": "2026-07-28T00:00:00Z",
            "reason": "Exact second source and Lean semantic judgment.",
        }
        self.write_json(statement_path, statement_audit)

        surface_audit = self.read_json(surface_path)
        surface_audit["review_rows"] = 2
        self.write_json(surface_path, surface_audit)

        coverage = self.read_json(coverage_path)
        coverage["source_artifact_sha256"] = source_digest
        coverage["paper_statement_inventory_sha256"] = REBIND._legacy_inventory_digest(
            inventory, mode=mode, statement_map=statement_map
        )
        coverage_items = coverage["items"]
        assert isinstance(coverage_items, dict)
        second_coverage_key = "other_old_coverage_navigation_only"
        second_row = "other_old_review_navigation_only"
        coverage_items[second_coverage_key] = {
            "coverage": "covered",
            "review_rows": [second_row],
            "review_row_signature_sha256": {second_row: second_signature},
            "reason": "The reviewed theorem establishes the other exact source property.",
            "source_evidence": "Pinned source anchor at source.txt:2-2.",
            "statement_sha256": second_target,
            "source_item_coverage_digest_schema": LEGACY_SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA,
            "source_item_coverage_sha256": second_legacy,
            "validator": "fixture coverage reviewer",
            "validator_type": "manual_semantic_v10",
            "validated_at": "2026-07-28T00:00:00Z",
        }
        self.write_json(coverage_path, coverage)
        fixture.update(
            {
                "second_source_key": second_source_key,
                "second_statement_key": second_statement_key,
                "second_coverage_key": second_coverage_key,
                "second_saved_row": second_row,
                "second_legacy_digest": second_legacy,
                "second_current_digest": second_current,
            }
        )
        return fixture

    @staticmethod
    def write_json(path: Path, value: object) -> None:
        path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    @staticmethod
    def read_json(path: Path) -> dict[str, object]:
        value = json.loads(path.read_text(encoding="utf-8"))
        assert isinstance(value, dict)
        return value

    def common(self, fixture: dict[str, object], coverage: dict[str, object] | None = None) -> dict[str, object]:
        coverage_path = fixture["coverage_path"]
        map_path = fixture["map_path"]
        raw_path = fixture["raw_path"]
        statement_path = fixture["statement_path"]
        surface_path = fixture["surface_path"]
        assert all(isinstance(path, Path) for path in (coverage_path, map_path, raw_path, statement_path, surface_path))
        return {
            "paper": PAPER,
            "paper_dir": fixture["folder"],
            "root": fixture["root"],
            "coverage": coverage if coverage is not None else self.read_json(coverage_path),
            "coverage_bytes": (
                REBIND._json_bytes(coverage)
                if coverage is not None
                else coverage_path.read_bytes()
            ),
            "coverage_path": coverage_path,
            "statement_map": self.read_json(map_path),
            "statement_map_bytes": map_path.read_bytes(),
            "statement_map_path": map_path,
            "raw_audit": self.read_json(raw_path),
            "raw_audit_bytes": raw_path.read_bytes(),
            "raw_audit_path": raw_path,
            "statement_audit": self.read_json(statement_path),
            "statement_audit_bytes": statement_path.read_bytes(),
            "statement_audit_path": statement_path,
            "review_surface_audit": self.read_json(surface_path),
            "review_surface_audit_bytes": surface_path.read_bytes(),
            "review_surface_audit_path": surface_path,
        }

    def prepare(self, fixture: dict[str, object], coverage: dict[str, object] | None = None) -> REBIND.PreparedRebind:
        return REBIND.prepare_paper_coverage_schema4_to5_rebind(
            **self.common(fixture, coverage)
        )

    def write_prior_coverage_archive(self, fixture: dict[str, object]) -> Path:
        coverage_path = fixture["coverage_path"]
        assert isinstance(coverage_path, Path)
        archive_path = REBIND._default_prior_coverage_archive_path(coverage_path)
        archive_path.write_bytes(coverage_path.read_bytes())
        return archive_path

    def test_transport_is_independent_of_source_and_row_navigation_names(self) -> None:
        # Two semantically distinct source items make it impossible for a
        # passing test to hide an accidental one-item/key-based pairing.
        fixture = self.add_second_semantic_item(self.build_fixture())
        prepared = self.prepare(fixture)
        transformed = prepared.rebound_coverage
        items = transformed["items"]
        assert isinstance(items, dict)
        item = items["old_coverage_navigation_only"]
        assert isinstance(item, dict)
        self.assertEqual(item["source_item_coverage_digest_schema"], SOURCE_ITEM_COVERAGE_DIGEST_SCHEMA)
        self.assertEqual(item["source_item_coverage_sha256"], fixture["current_digest"])
        self.assertEqual(len(prepared.receipt["item_bindings"]), 2)
        serialized_receipt = json.dumps(prepared.receipt, sort_keys=True)
        for navigation_only_name in (
            fixture["source_key"],
            fixture["second_source_key"],
            fixture["saved_row"],
            fixture["second_saved_row"],
            fixture["current_statement_key"],
            fixture["second_statement_key"],
        ):
            self.assertNotIn(str(navigation_only_name), serialized_receipt)

        self.write_prior_coverage_archive(fixture)
        validation_common = self.common(fixture, transformed)
        self.assertEqual(
            REBIND.validate_paper_coverage_schema4_to5_rebind(
                prepared.receipt, **validation_common
            ),
            "",
        )

        # Rename and reverse every navigation layer.  The source-map key,
        # coverage-sidecar slot, statement-ledger slot, and displayed review
        # row labels all change, but source target/legacy/current digest,
        # anchor, and signature evidence do not.  A pairing based on any of
        # those names or their order would fail this adversarial transport.
        map_path = fixture["map_path"]
        raw_path = fixture["raw_path"]
        statement_path = fixture["statement_path"]
        folder = fixture["folder"]
        assert all(
            isinstance(path, Path)
            for path in (map_path, raw_path, statement_path, folder)
        )
        statement_map = self.read_json(map_path)
        source_items = statement_map["items"]
        assert isinstance(source_items, dict)
        first_source = source_items[fixture["source_key"]]
        second_source = source_items[fixture["second_source_key"]]
        statement_map["items"] = {
            "z_unrelated_source_slot": first_source,
            "a_unrelated_source_slot": second_source,
        }
        self.write_json(map_path, statement_map)
        raw_audit = self.read_json(raw_path)
        raw_audit["paper_statement_map_sha256"] = hashlib.sha256(
            map_path.read_bytes()
        ).hexdigest()
        stamp_source_record_audit_receipts(raw_audit)
        self.write_json(raw_path, raw_audit)

        statement_audit = self.read_json(statement_path)
        statement_items = statement_audit["items"]
        assert isinstance(statement_items, dict)
        first_statement = statement_items[fixture["current_statement_key"]]
        second_statement = statement_items[fixture["second_statement_key"]]
        statement_audit["source_record_audit_sha256"] = raw_audit[
            "source_record_audit_sha256"
        ]
        statement_audit["items"] = {
            "z_unrelated_statement_slot": second_statement,
            "a_unrelated_statement_slot": first_statement,
        }
        self.write_json(statement_path, statement_audit)

        renamed = copy.deepcopy(self.read_json(fixture["coverage_path"]))
        coverage_items = renamed["items"]
        assert isinstance(coverage_items, dict)
        first_coverage = copy.deepcopy(coverage_items["old_coverage_navigation_only"])
        second_coverage = copy.deepcopy(coverage_items[fixture["second_coverage_key"]])
        assert isinstance(first_coverage, dict) and isinstance(second_coverage, dict)
        first_coverage["review_rows"] = ["unrelated_review_label_alpha"]
        first_coverage["review_row_signature_sha256"] = {
            "unrelated_review_label_alpha": digest("c")
        }
        second_coverage["review_rows"] = ["unrelated_review_label_beta"]
        second_coverage["review_row_signature_sha256"] = {
            "unrelated_review_label_beta": digest("b")
        }
        renamed["items"] = {
            "z_unrelated_coverage_slot": second_coverage,
            "a_unrelated_coverage_slot": first_coverage,
        }
        _full, inventory, mode, mode_error = review_dashboard.paper_coverage_inventory(
            folder
        )
        self.assertFalse(mode_error)
        renamed["paper_statement_inventory_sha256"] = REBIND._legacy_inventory_digest(
            inventory, mode=mode, statement_map=statement_map
        )
        renamed_prepared = self.prepare(fixture, renamed)
        self.assertEqual(
            prepared.receipt["item_bindings"], renamed_prepared.receipt["item_bindings"]
        )

    def test_missing_or_duplicate_coverage_entries_are_rejected(self) -> None:
        fixture = self.build_fixture()
        missing = self.read_json(fixture["coverage_path"])
        missing["items"] = {}
        with self.assertRaisesRegex(REBIND.PaperCoverageSchema4To5RebindError, "no item ledger"):
            self.prepare(fixture, missing)

        duplicate = self.read_json(fixture["coverage_path"])
        original = duplicate["items"]["old_coverage_navigation_only"]
        duplicate["items"]["duplicate_navigation_slot"] = copy.deepcopy(original)
        with self.assertRaisesRegex(REBIND.PaperCoverageSchema4To5RebindError, "duplicate"):
            self.prepare(fixture, duplicate)

    def test_empty_pins_require_structured_source_side_scope_evidence(self) -> None:
        fixture = self.build_fixture()
        coverage = self.read_json(fixture["coverage_path"])
        items = coverage["items"]
        assert isinstance(items, dict)
        entry = items["old_coverage_navigation_only"]
        assert isinstance(entry, dict)
        # A theorem-shaped source item has no structured user approval.  An
        # arbitrary sidecar label and empty pins cannot turn it into a
        # no-proof obligation; source-side evidence, not map/declaration
        # names, must authorize that disposition.
        entry["coverage"] = review_dashboard.USER_APPROVED_SCOPE_EXCLUSION
        entry["review_rows"] = []
        entry["review_row_signature_sha256"] = {}
        with self.assertRaisesRegex(
            REBIND.PaperCoverageSchema4To5RebindError,
            "no-proof disposition does not match",
        ):
            self.prepare(fixture, coverage)

    def test_completed_rebind_requires_the_exact_prior_schema4_archive(self) -> None:
        fixture = self.build_fixture()
        prepared = self.prepare(fixture)
        transformed = prepared.rebound_coverage
        missing = REBIND.validate_paper_coverage_schema4_to5_rebind(
            prepared.receipt, **self.common(fixture, transformed)
        )
        self.assertIn("could not read prior schema4 coverage archive", missing)
        archive_path = self.write_prior_coverage_archive(fixture)
        self.assertEqual(
            REBIND.validate_paper_coverage_schema4_to5_rebind(
                prepared.receipt, **self.common(fixture, transformed)
            ),
            "",
        )
        archive_path.write_text("not the original sidecar\n", encoding="utf-8")
        drift = REBIND.validate_paper_coverage_schema4_to5_rebind(
            prepared.receipt, **self.common(fixture, transformed)
        )
        self.assertIn("archive bytes differ", drift)

    def test_altered_source_anchor_is_rejected_before_rebind(self) -> None:
        fixture = self.build_fixture()
        map_path = fixture["map_path"]
        raw_path = fixture["raw_path"]
        assert isinstance(map_path, Path) and isinstance(raw_path, Path)
        statement_map = self.read_json(map_path)
        item = statement_map["items"][fixture["source_key"]]
        assert isinstance(item, dict)
        anchors = item["source_anchor_evidence"]
        assert isinstance(anchors, list) and isinstance(anchors[0], dict)
        anchors[0]["line_start"] = 2
        anchors[0]["line_end"] = 2
        self.write_json(map_path, statement_map)

        raw = self.read_json(raw_path)
        raw["paper_statement_map_sha256"] = hashlib.sha256(map_path.read_bytes()).hexdigest()
        stamp_source_record_audit_receipts(raw)
        self.write_json(raw_path, raw)

        with self.assertRaisesRegex(REBIND.PaperCoverageSchema4To5RebindError, "anchors"):
            self.prepare(fixture)

    def test_altered_source_statement_is_rejected_before_rebind(self) -> None:
        fixture = self.build_fixture()
        folder = fixture["folder"]
        map_path = fixture["map_path"]
        raw_path = fixture["raw_path"]
        assert isinstance(folder, Path) and isinstance(map_path, Path) and isinstance(raw_path, Path)
        replacement = "Theorem 1. Every admissible input has a different checked property."
        (folder / "source.txt").write_text(replacement + "\n", encoding="utf-8")
        source_digest = hashlib.sha256((replacement + "\n").encode("utf-8")).hexdigest()
        statement_map = self.read_json(map_path)
        statement_map["source_artifact_sha256"] = source_digest
        item = statement_map["items"][fixture["source_key"]]
        assert isinstance(item, dict)
        item["statement"] = replacement
        anchors = item["source_anchor_evidence"]
        assert isinstance(anchors, list) and isinstance(anchors[0], dict)
        anchors[0]["quoted_text"] = replacement
        anchors[0]["quoted_text_sha256"] = hashlib.sha256(
            replacement.encode("utf-8")
        ).hexdigest()
        self.write_json(map_path, statement_map)
        raw = self.read_json(raw_path)
        raw["paper_statement_map_sha256"] = hashlib.sha256(map_path.read_bytes()).hexdigest()
        stamp_source_record_audit_receipts(raw)
        self.write_json(raw_path, raw)

        _full, inventory, mode, mode_error = review_dashboard.paper_coverage_inventory(
            folder
        )
        self.assertFalse(mode_error)
        coverage = self.read_json(fixture["coverage_path"])
        coverage["source_artifact_sha256"] = source_digest
        coverage["paper_statement_inventory_sha256"] = REBIND._legacy_inventory_digest(
            inventory, mode=mode, statement_map=statement_map
        )
        with self.assertRaisesRegex(
            REBIND.PaperCoverageSchema4To5RebindError,
            "cannot be matched uniquely",
        ):
            self.prepare(fixture, coverage)

    def test_altered_current_row_signature_is_rejected(self) -> None:
        fixture = self.build_fixture()
        statement_path = fixture["statement_path"]
        assert isinstance(statement_path, Path)
        statement_audit = self.read_json(statement_path)
        entries = statement_audit["items"]
        assert isinstance(entries, dict)
        entry = entries[fixture["current_statement_key"]]
        assert isinstance(entry, dict)
        entry["lean_signature_sha256"] = digest("f")
        self.write_json(statement_path, statement_audit)
        with self.assertRaisesRegex(REBIND.PaperCoverageSchema4To5RebindError, "signature absent"):
            self.prepare(fixture)

    def test_receipt_rejects_anchor_drift_after_transport(self) -> None:
        fixture = self.build_fixture()
        prepared = self.prepare(fixture)
        transformed = prepared.rebound_coverage

        map_path = fixture["map_path"]
        raw_path = fixture["raw_path"]
        assert isinstance(map_path, Path) and isinstance(raw_path, Path)
        statement_map = self.read_json(map_path)
        item = statement_map["items"][fixture["source_key"]]
        assert isinstance(item, dict)
        anchors = item["source_anchor_evidence"]
        assert isinstance(anchors, list) and isinstance(anchors[0], dict)
        # Retain a syntactically valid quote digest but move it to an invalid
        # byte range.  Updating the raw map pin isolates the anchor gate.
        anchors[0]["line_start"] = 2
        anchors[0]["line_end"] = 2
        self.write_json(map_path, statement_map)
        raw = self.read_json(raw_path)
        raw["paper_statement_map_sha256"] = hashlib.sha256(map_path.read_bytes()).hexdigest()
        stamp_source_record_audit_receipts(raw)
        self.write_json(raw_path, raw)

        error = REBIND.validate_paper_coverage_schema4_to5_rebind(
            prepared.receipt,
            **self.common(fixture, transformed),
            require_prior_coverage_archive=False,
        )
        # The receipt's immutable statement-map byte pin rejects this before
        # re-running the anchor checker.  The preceding test isolates and
        # checks the anchor validator itself.
        self.assertIn("statement map bytes", error)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
