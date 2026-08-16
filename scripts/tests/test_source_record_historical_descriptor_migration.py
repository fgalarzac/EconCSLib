#!/usr/bin/env python3
"""Regression tests for the one-time v10 historical-descriptor bridge.

These checks exercise the narrow transport boundary rather than a Lean scan.
The KR fixture is deliberate: its Theorem 3 route is the split direct-evidence
and transparent-spec shape that must never be reconstructed from one half.
"""

from __future__ import annotations

import copy
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import source_record_historical_descriptor_migration as MIGRATION  # noqa: E402
from scripts import audit_conclusion_provenance as CONCLUSION  # noqa: E402
from scripts import audit_evidence_integrity as EVIDENCE  # noqa: E402
from scripts import source_record_differential_revalidation as DIFFERENTIAL  # noqa: E402


KR_PAPER_DIR = ROOT / "papers" / "KR21Monoculture"


class HistoricalDescriptorMigrationTests(unittest.TestCase):
    @staticmethod
    def _current_raw() -> dict[str, object]:
        return json.loads(
            (KR_PAPER_DIR / "audit" / "source_record_audit.json").read_text(
                encoding="utf-8"
            )
        )

    @staticmethod
    def _statement_map() -> dict[str, object]:
        return json.loads(
            (KR_PAPER_DIR / "audit" / "paper_statement_map.json").read_text(
                encoding="utf-8"
            )
        )

    @staticmethod
    def _row(
        raw: dict[str, object], key: str
    ) -> dict[str, object]:
        values = raw["boundary_input_items"]
        assert isinstance(values, list)
        return next(
            item
            for item in values
            if isinstance(item, dict) and item.get("judgment_key") == key
        )

    def test_legacy_effective_route_projection_requires_exact_duplicate_and_pin(
        self,
    ) -> None:
        key = (
            "appendixA_theorem5_corrected_source_complete.absolute_continuity : "
            "∀ a b : ℝ, AbsolutelyContinuousOnInterval f a b"
        )
        prior = self._row(
            json.loads(
                (
                    KR_PAPER_DIR
                    / "audit"
                    / "source_record_audit.reissue_archive_before_aggregate_receipt_2026-07-28.json"
                ).read_text(encoding="utf-8")
            ),
            key,
        )
        current = self._row(self._current_raw(), key)
        route = MIGRATION._current_row_route_receipt(current)
        self.assertEqual(
            MIGRATION._effective_route_receipt_projection(prior, current, route),
            ("", True),
        )

        changed_text = copy.deepcopy(current)
        changed_text["effective_lean_source_declaration"] = (
            str(changed_text["effective_lean_source_declaration"]) + " "
        )
        self.assertIn(
            "not byte-identical",
            MIGRATION._effective_route_receipt_projection(
                prior, changed_text, route
            )[0],
        )

        missing_prior_text = copy.deepcopy(prior)
        missing_prior_text["lean_source_declaration"] = None
        self.assertIn(
            "prior raw `lean_source_declaration` is missing",
            MIGRATION._effective_route_receipt_projection(
                missing_prior_text, current, route
            )[0],
        )

        wrong_effective_identity = copy.deepcopy(current)
        wrong_effective_identity["effective_qualified_declaration"] = "Fixture.wrong"
        self.assertIn(
            "does not equal the pinned declaration identity",
            MIGRATION._effective_route_receipt_projection(
                prior, wrong_effective_identity, route
            )[0],
        )

        ambiguous_route = copy.deepcopy(current)
        signatures = ambiguous_route["reviewed_elaborated_signature_identities"]
        assert isinstance(signatures, list) and signatures
        signatures.append(copy.deepcopy(signatures[0]))
        with self.assertRaisesRegex(
            MIGRATION.SourceRecordHistoricalDescriptorMigrationError,
            "ambiguous elaborated-signature ledger",
        ):
            MIGRATION._current_row_route_receipt(ambiguous_route)

        wrong_no_alias = copy.deepcopy(current)
        no_alias = wrong_no_alias["review_alias_expansion"]
        assert isinstance(no_alias, dict)
        no_alias["effective_declaration"] = "Fixture.wrong"
        self.assertIn(
            "does not equal the pinned declaration identity",
            MIGRATION._current_no_alias_receipt_error(no_alias, route),
        )

    def test_forged_historical_marker_cannot_enter_either_gate(self) -> None:
        key = "fixture current judgment"
        audit = {
            "paper": "Fixture",
            "prompt_version": MIGRATION.SOURCE_RECORD_V10_PROMPT_VERSION,
            "source_record_audit_sha256": "a" * 64,
            "boundary_input_items": [],
        }
        forged = {
            "classification": "validated_source_assumption",
            "validator": "forged reviewer",
            "validated_at": "2026-07-28T00:00:00Z",
            "prompt_version": MIGRATION.SOURCE_RECORD_V10_PROMPT_VERSION,
            "source_record_audit_sha256": "a" * 64,
            MIGRATION.SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_ITEM_FIELD: {
                "schema": MIGRATION.SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_SCHEMA
            },
        }
        payload = {"schema": 1, "paper": "Fixture", "items": {key: forged}}
        self.assertTrue(
            MIGRATION.source_record_historical_descriptor_migration_item_has_provenance(
                forged
            )
        )
        self.assertFalse(
            MIGRATION.is_loaded_source_record_historical_descriptor_migration_item(
                forged
            )
        )
        self.assertEqual(CONCLUSION._current_judgments_from_payload("Fixture", audit, payload), {})
        with patch.object(EVIDENCE, "source_record_audit_identity_error", return_value=""):
            self.assertEqual(
                EVIDENCE._current_source_record_judgment_items_from_payload(
                    audit, payload
                ),
                {},
            )

    def test_semantic_rebind_does_not_hide_unrelated_legacy_items(self) -> None:
        """Schema-2 wins only on the same storage address after both checks."""

        semantic_items = {
            "schema2-only": {"transport": "semantic"},
            "shared": {"transport": "semantic-wins"},
        }
        payload = {
            "prior_raw_audit": {"path": "audit/prior.json"},
            "current_raw_audit_snapshot": {"path": "audit/snapshot.json"},
            "paper_statement_map": {"path": "audit/map.json"},
            "items": {
                "legacy-only": {
                    "response": "legacy",
                    MIGRATION.SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_ITEM_FIELD: {
                        "schema": MIGRATION.SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_SCHEMA
                    },
                },
                "shared": {
                    "response": "legacy-loses",
                    MIGRATION.SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_ITEM_FIELD: {
                        "schema": MIGRATION.SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_SCHEMA
                    },
                },
            },
        }
        raw = {
            "paper_statement_map_sha256": "a" * 64,
            "source_record_audit_sha256": "b" * 64,
        }
        group = {"raw_members": []}

        class FakeSemanticRebind:
            @staticmethod
            def load_current_source_record_semantic_rebind_items(
                _paper_dir: Path, _paper: str, _current_raw: dict[str, object]
            ) -> dict[str, dict[str, str]]:
                return semantic_items

        with tempfile.TemporaryDirectory() as directory:
            paper_dir = Path(directory)
            audit_dir = paper_dir / "audit"
            audit_dir.mkdir()
            (audit_dir / MIGRATION.SOURCE_RECORD_HISTORICAL_DESCRIPTOR_MIGRATION_FILENAME).write_text(
                json.dumps(payload), encoding="utf-8"
            )
            with (
                patch.object(
                    MIGRATION,
                    "_semantic_rebind_module",
                    return_value=FakeSemanticRebind,
                ),
                patch.object(
                    MIGRATION,
                    "source_record_historical_descriptor_migration_overlay_error",
                    return_value="",
                ),
                patch.object(
                    MIGRATION,
                    "_resolve_paper_path",
                    side_effect=[
                        audit_dir / "prior.json",
                        audit_dir / "snapshot.json",
                        audit_dir / "map.json",
                    ],
                ),
                patch.object(
                    MIGRATION,
                    "_read_json_object",
                    side_effect=[raw, raw, {"items": {}}],
                ),
                patch.object(MIGRATION, "_valid_raw_audit", return_value=""),
                patch.object(
                    MIGRATION,
                    "_snapshot_groups",
                    side_effect=[
                        {"legacy-only": group, "shared": group},
                        {"legacy-only": group, "shared": group},
                        {"legacy-only": group, "shared": group},
                    ],
                ),
                patch.object(MIGRATION, "_semantic_endpoint_ledger", return_value={}),
                patch.object(MIGRATION, "_migration_item_current", return_value=True),
                patch.object(
                    MIGRATION,
                    "_current_item_from_group",
                    side_effect=lambda value, _group, **_kwargs: dict(value),
                ),
            ):
                loaded = (
                    MIGRATION.load_current_source_record_historical_descriptor_migration_items(
                        paper_dir, "Fixture", raw
                    )
                )
        self.assertEqual(set(loaded), {"legacy-only", "schema2-only", "shared"})
        self.assertEqual(loaded["schema2-only"], semantic_items["schema2-only"])
        self.assertEqual(loaded["shared"], semantic_items["shared"])
        self.assertTrue(
            MIGRATION.is_loaded_source_record_historical_descriptor_migration_item(
                loaded["legacy-only"]
            )
        )

    def test_split_theorem3_endpoint_requires_exact_current_mate(self) -> None:
        raw = self._current_raw()
        values = raw["semantic_model_items"]
        assert isinstance(values, list)
        raw["semantic_model_items"] = [
            item
            for item in values
            if not (
                isinstance(item, dict)
                and item.get("judgment_key")
                == "semantic-model::theorem3_source_complete_semantic_completeSpec"
            )
        ]
        with self.assertRaisesRegex(
            MIGRATION.SourceRecordHistoricalDescriptorMigrationError,
            "paired transparent-spec endpoint",
        ):
            MIGRATION._semantic_endpoint_ledger(
                raw, self._statement_map(), current=True
            )

    def test_current_semantic_association_digest_and_signature_are_rechecked(self) -> None:
        raw = self._current_raw()
        values = raw["semantic_model_items"]
        assert isinstance(values, list)
        target = next(
            item
            for item in values
            if isinstance(item, dict)
            and item.get("judgment_key") == "semantic-model::source_definition1_iff"
        )
        assert isinstance(target, dict)
        association = target["semantic_contract_source_association"]
        assert isinstance(association, dict)

        stale_digest = copy.deepcopy(raw)
        stale_target = next(
            item
            for item in stale_digest["semantic_model_items"]
            if isinstance(item, dict)
            and item.get("judgment_key") == "semantic-model::source_definition1_iff"
        )
        stale_association = stale_target["semantic_contract_source_association"]
        assert isinstance(stale_association, dict)
        stale_association["semantic_association_sha256"] = "0" * 64
        with self.assertRaisesRegex(
            MIGRATION.SourceRecordHistoricalDescriptorMigrationError,
            "semantic-association digest",
        ):
            MIGRATION._semantic_endpoint_ledger(
                stale_digest, self._statement_map(), current=True
            )

        stale_signature = copy.deepcopy(raw)
        signature_target = next(
            item
            for item in stale_signature["semantic_model_items"]
            if isinstance(item, dict)
            and item.get("judgment_key") == "semantic-model::source_definition1_iff"
        )
        signature_association = signature_target["semantic_contract_source_association"]
        assert isinstance(signature_association, dict)
        signature = signature_association[
            "reviewed_elaborated_signature_identity"
        ]
        assert isinstance(signature, dict)
        signature["elaborated_signature_sha256"] = "0" * 64
        with self.assertRaisesRegex(
            MIGRATION.SourceRecordHistoricalDescriptorMigrationError,
            "signature is not in the semantic-row ledger",
        ):
            MIGRATION._semantic_endpoint_ledger(
                stale_signature, self._statement_map(), current=True
            )

    def test_historical_overlay_receives_current_raw_association_pin(self) -> None:
        """Final composition regenerates association pins from live raw members.

        The checked-in schema-1 archive is intentionally immutable and may be
        stale after a later KR raw/map refresh.  Rather than treating that
        archival state as a test fixture, start with one archived response
        behind the private loader token and verify the evidence gate replaces
        an arbitrary serialized association pin with the current raw pin.
        """

        raw = self._current_raw()
        statement_map = self._statement_map()
        selected_key, loaded, expected_pin, _expected_targets = (
            self._synthetic_loaded_historical_item(raw, statement_map)
        )
        self.assertTrue(selected_key)
        with (
            patch.object(
                MIGRATION,
                "load_current_source_record_historical_descriptor_migration_items",
                return_value={selected_key: loaded},
            ),
            # This is a projection test.  KR's checked-in raw is intentionally
            # not a complete current-evidence fixture while its closeout is in
            # flight, so do not conflate its aggregate freshness with the
            # association-pin behavior under test.
            patch.object(EVIDENCE, "source_record_audit_identity_error", return_value=""),
        ):
            current = EVIDENCE.current_source_record_judgment_items(
                raw,
                {"schema": 1, "paper": "KR21Monoculture", "items": {}},
                expected_paper_statement_map_sha256=(
                    EVIDENCE.current_paper_statement_map_sha256(KR_PAPER_DIR)
                ),
                folder=KR_PAPER_DIR,
            )
        judgment = current.get(selected_key)
        self.assertIsNotNone(judgment)
        assert isinstance(judgment, dict)
        self.assertEqual(judgment.get("semantic_association_sha256"), expected_pin)
        self.assertTrue(
            MIGRATION.is_loaded_source_record_historical_descriptor_migration_item(
                judgment
            )
        )
        tampered = MIGRATION._LoadedHistoricalDescriptorMigrationItem(dict(loaded))
        tampered["semantic_association_sha256"] = "0" * 64
        with (
            patch.object(
                MIGRATION,
                "load_current_source_record_historical_descriptor_migration_items",
                return_value={selected_key: tampered},
            ),
            patch.object(EVIDENCE, "source_record_audit_identity_error", return_value=""),
        ):
            rejected = EVIDENCE.current_source_record_judgment_items(
                raw,
                {"schema": 1, "paper": "KR21Monoculture", "items": {}},
                expected_paper_statement_map_sha256=(
                    EVIDENCE.current_paper_statement_map_sha256(KR_PAPER_DIR)
                ),
                folder=KR_PAPER_DIR,
            )
        self.assertNotIn(selected_key, rejected)

    def test_historical_overlay_receives_current_corrected_target_map(self) -> None:
        """A historical response cannot choose a corrected-target digest map."""

        raw = self._current_raw()
        statement_map = self._statement_map()
        selected_key, loaded, _expected_pin, expected_targets = (
            self._synthetic_loaded_historical_item(raw, statement_map)
        )
        self.assertTrue(selected_key)
        self.assertTrue(expected_targets)
        with (
            patch.object(
                MIGRATION,
                "load_current_source_record_historical_descriptor_migration_items",
                return_value={selected_key: loaded},
            ),
            patch.object(EVIDENCE, "source_record_audit_identity_error", return_value=""),
        ):
            current = EVIDENCE.current_source_record_judgment_items(
                raw,
                {"schema": 1, "paper": "KR21Monoculture", "items": {}},
                expected_paper_statement_map_sha256=(
                    EVIDENCE.current_paper_statement_map_sha256(KR_PAPER_DIR)
                ),
                folder=KR_PAPER_DIR,
            )
        judgment = current.get(selected_key)
        self.assertIsNotNone(judgment)
        assert isinstance(judgment, dict)
        self.assertEqual(
            judgment.get("corrected_target_sha256_by_source_semantic_sha256"),
            expected_targets,
        )
        self.assertTrue(
            MIGRATION.is_loaded_source_record_historical_descriptor_migration_item(
                judgment
            )
        )
        tampered = MIGRATION._LoadedHistoricalDescriptorMigrationItem(dict(loaded))
        tampered["corrected_target_sha256_by_source_semantic_sha256"] = {
            semantic: "0" * 64 for semantic in expected_targets
        }
        with (
            patch.object(
                MIGRATION,
                "load_current_source_record_historical_descriptor_migration_items",
                return_value={selected_key: tampered},
            ),
            patch.object(EVIDENCE, "source_record_audit_identity_error", return_value=""),
        ):
            rejected = EVIDENCE.current_source_record_judgment_items(
                raw,
                {"schema": 1, "paper": "KR21Monoculture", "items": {}},
                expected_paper_statement_map_sha256=(
                    EVIDENCE.current_paper_statement_map_sha256(KR_PAPER_DIR)
                ),
                folder=KR_PAPER_DIR,
            )
        self.assertNotIn(selected_key, rejected)

    @staticmethod
    def _synthetic_loaded_historical_item(
        raw: dict[str, object], statement_map: dict[str, object]
    ) -> tuple[str, dict[str, object], str, dict[str, str]]:
        """Return one archived response projected onto a current raw group.

        This is intentionally a loader-token fixture, not a bypass of the
        production loader.  Loader replay/provenance has separate tests.  It
        keeps the projection tests independent of whether the checked-in
        archival overlay remains eligible after unrelated raw/map evolution.
        """

        legacy = json.loads(
            (
                KR_PAPER_DIR
                / "audit"
                / "source_record_historical_descriptor_migration.json"
            ).read_text(encoding="utf-8")
        )
        legacy_items = legacy.get("items")
        source_items = statement_map.get("items")
        assert isinstance(legacy_items, dict)
        assert isinstance(source_items, dict)
        groups, group_errors = DIFFERENTIAL._raw_item_groups(raw)
        assert group_errors == {}
        for raw_key, archived_response in sorted(legacy_items.items()):
            if not isinstance(archived_response, dict):
                continue
            key = str(raw_key)
            group = groups.get(key)
            raw_members = group.get("raw_members") if isinstance(group, dict) else None
            if not isinstance(raw_members, list):
                continue
            expected_pin = ""
            expected_targets: dict[str, str] = {}
            for section, item in raw_members:
                if section not in {
                    "boundary_input_items",
                    "conclusion_dependency_items",
                } or not isinstance(item, dict):
                    continue
                association = item.get("source_contract_association")
                if not isinstance(association, dict):
                    continue
                expected_pin = str(
                    association.get("semantic_association_sha256") or ""
                ).strip()
                identities = association.get("source_item_identities")
                if not isinstance(identities, list):
                    continue
                for identity in identities:
                    if not isinstance(identity, dict):
                        continue
                    source_item = source_items.get(identity.get("source_key"))
                    target = (
                        source_item.get("corrected_target")
                        if isinstance(source_item, dict)
                        and source_item.get("coverage_status")
                        == "corrected_source_statement"
                        else None
                    )
                    semantic = str(
                        identity.get("source_semantic_sha256") or ""
                    ).strip()
                    digest = (
                        str(target.get("corrected_target_sha256") or "").strip()
                        if isinstance(target, dict)
                        else ""
                    )
                    if semantic and digest:
                        expected_targets[semantic] = digest
            if expected_pin and expected_targets:
                projected = MIGRATION._current_item_from_group(
                    archived_response,
                    group,
                    current_raw_digest=str(raw["source_record_audit_sha256"]),
                )
                return (
                    key,
                    MIGRATION._LoadedHistoricalDescriptorMigrationItem(projected),
                    expected_pin,
                    expected_targets,
                )
        raise AssertionError("fixture has no current group with an association and corrected target")

    def test_terminal_projection_retains_and_requires_the_closure_receipt(self) -> None:
        definition: dict[str, object] = {
            "body_sha256": "a" * 64,
            "declaration": "Fixture.endpoint",
            "declaration_sha256": "b" * 64,
            "dependency_chain": ["Fixture.root", "Fixture.endpoint"],
            "direct_local_dependencies": ["Fixture.root"],
            "semantic_construct_flags": {"model_semantics": True},
            "semantic_fragments": ["literal carrier"],
            "source_file": "Fixture.lean",
            "line": 10,
        }
        projected = MIGRATION._terminal_definition_projection(definition)
        self.assertEqual(projected["dependency_chain"], definition["dependency_chain"])
        self.assertEqual(
            projected["direct_local_dependencies"], definition["direct_local_dependencies"]
        )
        malformed = copy.deepcopy(definition)
        malformed.pop("dependency_chain")
        with self.assertRaisesRegex(
            MIGRATION.SourceRecordHistoricalDescriptorMigrationError,
            "body/closure/construct receipt",
        ):
            MIGRATION._terminal_definition_projection(malformed)

    def test_only_enumerated_false_defaults_are_projected(self) -> None:
        self.assertEqual(
            MIGRATION._normalize_explicit_defaults(
                {
                    "requires_source_carrier_coherence_analysis_when_detected": False,
                    "ordinary_false": False,
                }
            ),
            {"ordinary_false": False},
        )
        self.assertEqual(
            MIGRATION._normalize_explicit_defaults(
                {"measure_kernel_carrier_transport_construct": True}
            ),
            {"measure_kernel_carrier_transport_construct": True},
        )

    def test_recursive_rows_and_empty_current_pins_are_not_transportable(self) -> None:
        recursive_group = {
            "raw_members": [("recursive_field_items", {"judgment_key": "field"})],
            "raw_formalization_scope": None,
        }
        with self.assertRaisesRegex(
            MIGRATION.SourceRecordHistoricalDescriptorMigrationError,
            "recursive-field rows",
        ):
            MIGRATION._group_descriptor(
                recursive_group,
                recursive_group,
                prior_endpoints={},
                current_endpoints={},
                statement_map={"items": {}},
            )
        with self.assertRaisesRegex(
            MIGRATION.SourceRecordHistoricalDescriptorMigrationError,
            "no complete independently reusable item pin",
        ):
            MIGRATION._current_group_pins(
                {
                    "raw_members": [
                        (
                            "boundary_input_items",
                            {
                                "kind": "boundary_input",
                                "source_record_item_reuse_eligibility": {
                                    "eligible": False,
                                    "blockers": ["fixture"],
                                },
                            },
                        )
                    ]
                }
            )

    def test_active_prior_transport_cannot_be_replayed(self) -> None:
        error = MIGRATION._prior_judgment_error(
            "fixture",
            {
                "source_record_differential_revalidation": {"schema": 1},
                "prompt_version": MIGRATION.SOURCE_RECORD_V10_PROMPT_VERSION,
            },
            {},
            prior_raw_digest="a" * 64,
        )
        self.assertIn("active historical transport metadata", error)


if __name__ == "__main__":
    unittest.main()
