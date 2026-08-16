#!/usr/bin/env python3
"""Focused regression coverage for the explicit source-record v4-to-v5 bridge."""

from __future__ import annotations

import copy
import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.source_record_integrity import stamp_source_record_audit_receipts  # noqa: E402
from scripts import source_record_schema4_to5_migration as MIGRATION  # noqa: E402
from scripts import audit_conclusion_provenance as CONCLUSION  # noqa: E402
from scripts import audit_evidence_integrity as EVIDENCE  # noqa: E402
from scripts import audit_repository as REPOSITORY  # noqa: E402
from scripts import source_record_target_disposition as DISPOSITION  # noqa: E402


PAPER = "FixturePaper"
SOURCE_RECORD_AUDIT_HELPER = (
    ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
)


def load_source_record_audit_helper() -> object:
    spec = importlib.util.spec_from_file_location(
        "schema4_to5_source_record_audit_helper", SOURCE_RECORD_AUDIT_HELPER
    )
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def digest(char: str) -> str:
    return char * 64


def reusable_item(
    key: str,
    *,
    item_schema: int,
    item_digest: str,
    source_digest: str = digest("a"),
    association_digest: str | None = None,
    declaration_digest: str = digest("c"),
    signature_digest: str = digest("d"),
    context_digest: str = digest("e"),
    fidelity_digest: str = digest("f"),
    expanded_type: str = "forall x : Nat, P x",
    required_check: str = "generated diagnostics wording",
) -> dict[str, object]:
    """Return a raw item with all generated schema-specific receipts present."""

    qualified = "FixturePaper.PaperInterface.named_result"
    signature = {
        "qualified_declaration": qualified,
        "elaborated_signature_sha256": signature_digest,
    }
    if association_digest is None:
        association_digest = DISPOSITION.semantic_association_record_digest(
            [source_digest], signature
        )
    return {
        "judgment_key": key,
        "kind": "boundary_input",
        "row": "named_result",
        "binder": "h",
        "expanded_input_type": expanded_type,
        "expanded_lean_surface": {
            "input_type": expanded_type,
            "result_type": "Conclusion x",
            "semantic_shape": {"is_proposition": True},
        },
        "required_check": required_check,
        "source_contract_association": {
            "schema": 2,
            "association_mode": "explicit_source_map_direct_route",
            "semantic_contract_member_role": "direct_source_route",
            "role": "direct_evidence",
            "review_scope": "individual_row_only",
            "structural_pairing": "not_applicable_direct_source_route",
            "semantic_model_judgment_key": "semantic-model::named_result",
            "paired_qualified_declaration": "FixturePaper.PaperInterface.paired_result",
            "semantic_association_sha256": association_digest,
            "source_item_identities": [
                {"source_semantic_sha256": source_digest}
            ],
            "reviewed_declaration_identity": {
                "qualified_declaration": qualified,
                "declaration_sha256": declaration_digest,
            },
            "reviewed_elaborated_signature_identity": signature,
        },
        "reviewed_declaration_identity": {
            "qualified_declaration": qualified,
            "declaration_sha256": declaration_digest,
        },
        "reviewed_elaborated_signature_identities": [
            {
                "qualified_declaration": qualified,
                "elaborated_signature_sha256": signature_digest,
            }
        ],
        "source_record_item_semantic_context_requirements_sha256": context_digest,
        "source_record_item_source_proof_fidelity_records_sha256": fidelity_digest,
        "source_record_item_reuse_eligibility": {
            "eligible": True,
            "blockers": [],
        },
        "source_record_item_digest_schema": item_schema,
        "source_record_item_semantic_id": digest("1"),
        "source_record_item_context_sha256": digest("2"),
        "source_record_item_sha256": item_digest,
    }


def raw_audit(
    items: list[dict[str, object]], *, paper: str = PAPER
) -> dict[str, object]:
    payload: dict[str, object] = {
        "paper": paper,
        "prompt_version": MIGRATION.SOURCE_RECORD_V10_PROMPT_VERSION,
        "source_record_policy_version": MIGRATION.SOURCE_RECORD_V10_PROMPT_VERSION,
        "boundary_input_items": items,
    }
    stamp_source_record_audit_receipts(payload)
    return payload


def sidecar(
    prior: dict[str, object],
    items: list[dict[str, object]],
    *,
    with_pins: bool = True,
    item_digest_schema: int = 4,
) -> dict[str, object]:
    entries: dict[str, object] = {}
    for item in items:
        key = str(item["judgment_key"])
        value: dict[str, object] = {
            "classification": "validated_source_assumption",
            "reason": "saved v10 review",
            "prompt_version": MIGRATION.SOURCE_RECORD_V10_PROMPT_VERSION,
            "source_record_policy_version": MIGRATION.SOURCE_RECORD_V10_PROMPT_VERSION,
            "source_record_audit_sha256": prior["source_record_audit_sha256"],
            "source_record_item_digest_schema": item_digest_schema,
            "source_record_item_sha256": item["source_record_item_sha256"],
            "validator": "fixture auditor",
            "validated_at": "2026-07-27T00:00:00Z",
        }
        if with_pins:
            value["source_record_item_sha256s"] = [
                {
                    "kind": item["kind"],
                    "source_record_item_digest_schema": item_digest_schema,
                    "source_record_item_sha256": item["source_record_item_sha256"],
                }
            ]
        entries[key] = value
    return {
        "schema": 1,
        "paper": PAPER,
        "prompt_version": MIGRATION.SOURCE_RECORD_V10_PROMPT_VERSION,
        "source_record_policy_version": MIGRATION.SOURCE_RECORD_V10_PROMPT_VERSION,
        "validator": "fixture auditor",
        "validated_at": "2026-07-27T00:00:00Z",
        "items": entries,
    }


class SourceRecordSchema4To5MigrationTests(unittest.TestCase):
    def build_overlay(
        self,
        prior: dict[str, object],
        judgments: dict[str, object],
        current: dict[str, object],
    ) -> tuple[dict[str, object], Path]:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        prior_path = root / "prior_raw.json"
        judgments_path = root / "prior_judgments.json"
        current_path = root / "current_raw.json"
        for path, payload in (
            (prior_path, prior),
            (judgments_path, judgments),
            (current_path, current),
        ):
            path.write_text(json.dumps(payload, sort_keys=True), encoding="utf-8")
        overlay = MIGRATION.build_source_record_schema4_to5_migration(
            paper=PAPER,
            prior_raw_audit=prior,
            prior_judgments=judgments,
            current_raw_audit=current,
            prior_raw_audit_path=prior_path,
            prior_judgments_path=judgments_path,
            current_raw_audit_path=current_path,
        )
        paper_dir = root / "papers" / PAPER
        overlay_path = MIGRATION.source_record_schema4_to5_migration_overlay_path(
            paper_dir
        )
        overlay_path.parent.mkdir(parents=True)
        overlay_path.write_text(json.dumps(overlay, sort_keys=True), encoding="utf-8")
        return overlay, paper_dir

    def matching_inputs(
        self, key: str = "named_result.h : forall x : Nat, P x"
    ) -> tuple[dict[str, object], dict[str, object], dict[str, object]]:
        prior_item = reusable_item(
            key, item_schema=4, item_digest=digest("3")
        )
        current_item = reusable_item(
            key, item_schema=5, item_digest=digest("4")
        )
        prior = raw_audit([prior_item])
        current = raw_audit([current_item])
        return prior, sidecar(prior, [prior_item]), current

    def test_exact_direct_key_descriptor_match_migrates_and_survives_cosmetic_change(self) -> None:
        prior, judgments, current = self.matching_inputs()
        overlay, paper_dir = self.build_overlay(prior, judgments, current)
        self.assertEqual(len(overlay["items"]), 1)
        key = next(iter(overlay["items"]))
        value = overlay["items"][key]
        assert isinstance(value, dict)
        self.assertEqual(value["source_record_item_digest_schema"], 5)
        self.assertTrue(value["source_record_item_sha256s"])
        self.assertEqual(
            value[MIGRATION.SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_ITEM_FIELD][
                "prior_judgment_key"
            ],
            key,
        )
        # ``required_check`` is a generated diagnostic phrase, not the
        # obligation itself.  A later raw-audit refresh with only this audit
        # cosmetic change must retain the earlier direct-key migration.
        old_aggregate = current["source_record_audit_sha256"]
        current_item = current["boundary_input_items"][0]
        assert isinstance(current_item, dict)
        current_item["required_check"] = "new diagnostic phrasing"
        stamp_source_record_audit_receipts(current)
        self.assertNotEqual(current["source_record_audit_sha256"], old_aggregate)
        loaded = MIGRATION.load_current_source_record_schema4_to5_migration_items(
            paper_dir, PAPER, current
        )
        self.assertEqual(set(loaded), {key})

    def test_source_change_denies_only_changed_direct_key(self) -> None:
        first = "first.h : P"
        second = "second.h : Q"
        prior_items = [
            reusable_item(first, item_schema=4, item_digest=digest("3")),
            reusable_item(second, item_schema=4, item_digest=digest("5")),
        ]
        current_items = [
            reusable_item(first, item_schema=5, item_digest=digest("4")),
            reusable_item(second, item_schema=5, item_digest=digest("6")),
        ]
        current_items[1]["source_contract_association"]["source_item_identities"][0][
            "source_semantic_sha256"
        ] = digest("7")
        prior = raw_audit(prior_items)
        current = raw_audit(current_items)

        overlay, _paper_dir = self.build_overlay(prior, sidecar(prior, prior_items), current)
        self.assertEqual(set(overlay["items"]), {first})
        decisions = {entry["judgment_key"]: entry for entry in overlay["decisions"]}
        self.assertEqual(decisions[second]["status"], "not_migrated")
        self.assertIn("full semantic descriptor differs", decisions[second]["reason"])

    def test_lean_context_and_proof_fidelity_changes_each_deny_migration(self) -> None:
        for field, changed in (
            ("expanded_lean_surface", {"input_type": "forall x : Nat, R x"}),
            (
                "reviewed_elaborated_signature_identities",
                [
                    {
                        "qualified_declaration": "FixturePaper.PaperInterface.named_result",
                        "elaborated_signature_sha256": digest("9"),
                    }
                ],
            ),
            ("source_record_item_semantic_context_requirements_sha256", digest("7")),
            ("source_record_item_source_proof_fidelity_records_sha256", digest("8")),
            (
                "source_record_item_future_requirement",
                {"schema": 1, "semantic_constraint": "new obligation"},
            ),
        ):
            with self.subTest(field=field):
                prior, judgments, current = self.matching_inputs()
                current_item = current["boundary_input_items"][0]
                assert isinstance(current_item, dict)
                current_item[field] = copy.deepcopy(changed)
                stamp_source_record_audit_receipts(current)
                overlay, _paper_dir = self.build_overlay(prior, judgments, current)
                self.assertEqual(overlay["items"], {})

    def test_key_remap_is_not_migrated(self) -> None:
        old_key = "old_name.h : P"
        new_key = "renamed_name.h : P"
        prior_item = reusable_item(old_key, item_schema=4, item_digest=digest("3"))
        current_item = reusable_item(new_key, item_schema=5, item_digest=digest("4"))
        prior = raw_audit([prior_item])
        current = raw_audit([current_item])

        overlay, paper_dir = self.build_overlay(prior, sidecar(prior, [prior_item]), current)
        self.assertEqual(overlay["items"], {})
        self.assertEqual(
            MIGRATION.load_current_source_record_schema4_to5_migration_items(
                paper_dir, PAPER, current
            ),
            {},
        )
        decision = next(entry for entry in overlay["decisions"] if entry["judgment_key"] == old_key)
        self.assertIn("key remap is forbidden", decision["reason"])

    def test_association_role_mode_and_pair_scope_changes_deny_migration(self) -> None:
        mutations = (
            ("association_mode", "support_source_route"),
            ("semantic_contract_member_role", "supporting_route"),
            ("paired_qualified_declaration", "FixturePaper.PaperInterface.other_pair"),
        )
        for field, changed in mutations:
            with self.subTest(field=field):
                prior, judgments, current = self.matching_inputs()
                current_item = current["boundary_input_items"][0]
                assert isinstance(current_item, dict)
                association = current_item["source_contract_association"]
                assert isinstance(association, dict)
                # Keep the source-content and elaborated hashes unchanged to
                # exercise the exact gap: only route semantics change.
                association[field] = changed
                stamp_source_record_audit_receipts(current)
                overlay, _paper_dir = self.build_overlay(prior, judgments, current)
                self.assertEqual(overlay["items"], {})

        prior, judgments, current = self.matching_inputs()
        group = {
            "schema": 1,
            "source_item_identities": [{"source_semantic_sha256": digest("a")}],
            "member_rows": [
                {
                    "role": "direct_evidence",
                    "row": "named_result",
                    "qualified_declaration": "FixturePaper.PaperInterface.named_result",
                    "reviewed_declaration_identity": {
                        "qualified_declaration": "FixturePaper.PaperInterface.named_result",
                        "declaration_sha256": digest("c"),
                    },
                },
                {
                    "role": "transparent_spec",
                    "row": "paired_result",
                    "qualified_declaration": "FixturePaper.PaperInterface.paired_result",
                    "reviewed_declaration_identity": {
                        "qualified_declaration": "FixturePaper.PaperInterface.paired_result",
                        "declaration_sha256": digest("9"),
                    },
                },
            ],
            "surface_root": {
                "kind": "transparent_spec_body",
                "qualified_declaration": "FixturePaper.PaperInterface.paired_result",
                "structural_alpha_normalized_surface": "forall x, P x",
            },
            "structural_alpha_normalized_equal": True,
        }
        prior_item = prior["boundary_input_items"][0]
        current_item = current["boundary_input_items"][0]
        assert isinstance(prior_item, dict) and isinstance(current_item, dict)
        prior_item["semantic_contract_group"] = copy.deepcopy(group)
        current_item["semantic_contract_group"] = copy.deepcopy(group)
        current_group = current_item["semantic_contract_group"]
        assert isinstance(current_group, dict)
        members = current_group["member_rows"]
        assert isinstance(members, list) and isinstance(members[1], dict)
        members[1]["role"] = "supporting_spec"
        stamp_source_record_audit_receipts(prior)
        stamp_source_record_audit_receipts(current)
        judgments = sidecar(prior, [prior_item])
        overlay, _paper_dir = self.build_overlay(prior, judgments, current)
        self.assertEqual(overlay["items"], {})

    def test_singleton_bare_scalar_schema4_pin_is_migrated(self) -> None:
        prior, judgments, current = self.matching_inputs()
        judgments_without_pins = sidecar(
            prior, [prior["boundary_input_items"][0]], with_pins=False
        )
        overlay, _paper_dir = self.build_overlay(prior, judgments_without_pins, current)
        self.assertEqual(set(overlay["items"]), set(judgments_without_pins["items"]))

    def test_multi_member_bare_scalar_schema4_pin_is_not_promoted(self) -> None:
        key = "shared.h : P"
        prior_boundary = reusable_item(
            key, item_schema=4, item_digest=digest("3")
        )
        prior_dependency = reusable_item(
            key, item_schema=4, item_digest=digest("5")
        )
        prior_dependency["kind"] = "conclusion_dependency"
        current_boundary = reusable_item(
            key, item_schema=5, item_digest=digest("4")
        )
        current_dependency = reusable_item(
            key, item_schema=5, item_digest=digest("6")
        )
        current_dependency["kind"] = "conclusion_dependency"
        prior = raw_audit([prior_boundary])
        prior["conclusion_dependency_items"] = [prior_dependency]
        stamp_source_record_audit_receipts(prior)
        current = raw_audit([current_boundary])
        current["conclusion_dependency_items"] = [current_dependency]
        stamp_source_record_audit_receipts(current)
        judgments = sidecar(prior, [prior_boundary], with_pins=False)

        overlay, _paper_dir = self.build_overlay(prior, judgments, current)
        self.assertEqual(overlay["items"], {})
        decision = next(entry for entry in overlay["decisions"] if entry["judgment_key"] == key)
        self.assertIn("complete prior schema-4 item group", decision["reason"])

    def test_duplicate_schema4_kind_digest_group_is_not_promoted(self) -> None:
        key = "duplicate.h : P"
        prior_item = reusable_item(key, item_schema=4, item_digest=digest("3"))
        duplicate = copy.deepcopy(prior_item)
        current_item = reusable_item(key, item_schema=5, item_digest=digest("4"))
        prior = raw_audit([prior_item, duplicate])
        current = raw_audit([current_item])
        judgments = sidecar(prior, [prior_item])

        overlay, _paper_dir = self.build_overlay(prior, judgments, current)
        self.assertEqual(overlay["items"], {})
        decision = next(entry for entry in overlay["decisions"] if entry["judgment_key"] == key)
        self.assertIn("duplicate schema-4 (kind, item digest)", decision["reason"])

    def test_migration_inputs_require_exact_paper_identity(self) -> None:
        for target in ("prior_raw", "current_raw", "prior_judgments"):
            for recorded_paper in (None, "OtherPaper"):
                with self.subTest(target=target, recorded_paper=recorded_paper):
                    prior, judgments, current = self.matching_inputs()
                    if target == "prior_raw":
                        prior["paper"] = recorded_paper
                        stamp_source_record_audit_receipts(prior)
                    elif target == "current_raw":
                        current["paper"] = recorded_paper
                        stamp_source_record_audit_receipts(current)
                    else:
                        judgments["paper"] = recorded_paper
                    with self.assertRaises(MIGRATION.SourceRecordSchema4To5MigrationError):
                        self.build_overlay(prior, judgments, current)

    def test_prompt_mismatch_is_not_promoted(self) -> None:
        prior, judgments, current = self.matching_inputs()

        current["prompt_version"] = "source-record-v9-legacy"
        stamp_source_record_audit_receipts(current)
        with self.assertRaises(MIGRATION.SourceRecordSchema4To5MigrationError):
            self.build_overlay(prior, judgments, current)

    def test_loader_rejects_foreign_current_raw_paper(self) -> None:
        prior, judgments, current = self.matching_inputs()
        _overlay, paper_dir = self.build_overlay(prior, judgments, current)
        foreign = copy.deepcopy(current)
        foreign["paper"] = "OtherPaper"
        stamp_source_record_audit_receipts(foreign)
        self.assertEqual(
            MIGRATION.load_current_source_record_schema4_to5_migration_items(
                paper_dir, PAPER, foreign
            ),
            {},
        )

    def test_overlay_is_consumed_only_through_the_loaded_direct_key_path(self) -> None:
        prior, judgments, current = self.matching_inputs()
        _overlay, paper_dir = self.build_overlay(prior, judgments, current)
        key = next(iter(judgments["items"]))
        ordinary_path = paper_dir / "audit" / "source_record_match_llm.json"
        ordinary_path.write_text(
            json.dumps({"schema": 1, "paper": PAPER, "items": {}}),
            encoding="utf-8",
        )

        source_audit = load_source_record_audit_helper()
        self.assertEqual(
            set(source_audit.current_source_record_judgments(paper_dir, PAPER, current)),
            {key},
        )

        repository_items = REPOSITORY.source_record_judgment_items(
            ordinary_path,
            PAPER,
            current_raw_audit=current,
            paper_dir=paper_dir,
        )
        self.assertIn(key, repository_items)
        self.assertTrue(
            REPOSITORY.source_record_judgment_current(
                key,
                repository_items[key],
                digest="",
                expected_item_digests={},
            )
        )

        with patch.object(CONCLUSION, "PAPERS", paper_dir.parent):
            self.assertEqual(set(CONCLUSION.current_judgments(PAPER, current)), {key})
        with patch.object(EVIDENCE, "source_record_audit_identity_error", return_value=""):
            self.assertEqual(
                set(
                    EVIDENCE.current_source_record_judgment_items(
                        current, {}, folder=paper_dir
                    )
                ),
                {key},
            )

    def test_current_ordinary_response_wins_over_schema4_to5_overlay(self) -> None:
        """A current ordinary review is preferred over a loaded migration.

        The collision is exercised through every composition site so no
        consumer can silently reinstate an older migrated response after the
        ordinary current sidecar has been selected.
        """

        prior, judgments, current = self.matching_inputs()
        _overlay, paper_dir = self.build_overlay(prior, judgments, current)
        key = next(iter(judgments["items"]))
        current_item = current["boundary_input_items"][0]
        assert isinstance(current_item, dict)
        ordinary_current = sidecar(
            current,
            [current_item],
            item_digest_schema=5,
        )
        ordinary_entry = ordinary_current["items"][key]
        assert isinstance(ordinary_entry, dict)
        ordinary_entry["classification"] = "ordinary_current_preferred"
        ordinary_path = paper_dir / "audit" / "source_record_match_llm.json"
        ordinary_path.write_text(
            json.dumps(ordinary_current, sort_keys=True), encoding="utf-8"
        )

        source_audit = load_source_record_audit_helper()
        source_audit_items = source_audit.current_source_record_judgments(
            paper_dir, PAPER, current
        )
        self.assertEqual(
            source_audit_items[key]["classification"],
            "ordinary_current_preferred",
        )
        self.assertFalse(
            MIGRATION.is_loaded_source_record_schema4_to5_migration_item(
                source_audit_items[key]
            )
        )

        repository_items = REPOSITORY.source_record_judgment_items(
            ordinary_path,
            PAPER,
            current_raw_audit=current,
            paper_dir=paper_dir,
        )
        self.assertEqual(
            repository_items[key]["classification"],
            "ordinary_current_preferred",
        )
        self.assertFalse(
            MIGRATION.is_loaded_source_record_schema4_to5_migration_item(
                repository_items[key]
            )
        )

        with patch.object(EVIDENCE, "source_record_audit_identity_error", return_value=""):
            evidence_items = EVIDENCE.current_source_record_judgment_items(
                current, ordinary_current, folder=paper_dir
            )
        self.assertEqual(
            evidence_items[key]["classification"],
            "ordinary_current_preferred",
        )
        self.assertFalse(
            MIGRATION.is_loaded_source_record_schema4_to5_migration_item(
                evidence_items[key]
            )
        )

        with patch.object(CONCLUSION, "PAPERS", paper_dir.parent):
            conclusion_items = CONCLUSION.current_judgments(PAPER, current)
        self.assertEqual(
            conclusion_items[key]["classification"],
            "ordinary_current_preferred",
        )
        self.assertFalse(
            MIGRATION.is_loaded_source_record_schema4_to5_migration_item(
                conclusion_items[key]
            )
        )

    def test_serialized_or_forged_overlay_marker_is_not_loader_authenticated(self) -> None:
        prior, judgments, current = self.matching_inputs()
        overlay, paper_dir = self.build_overlay(prior, judgments, current)
        key = next(iter(overlay["items"]))
        loaded = MIGRATION.load_current_source_record_schema4_to5_migration_items(
            paper_dir, PAPER, current
        )
        self.assertTrue(
            MIGRATION.is_loaded_source_record_schema4_to5_migration_item(loaded[key])
        )

        # The private loader token is an attribute of an in-memory dict
        # subclass, so normal JSON transport never contains it.
        serialized = json.dumps(loaded[key], sort_keys=True)
        self.assertNotIn("_source_record_schema4_to5_loaded_overlay", serialized)
        forged = json.loads(serialized)
        forged["_source_record_schema4_to5_loaded_overlay"] = True
        self.assertFalse(
            MIGRATION.is_loaded_source_record_schema4_to5_migration_item(forged)
        )

        source_audit = load_source_record_audit_helper()
        self.assertEqual(
            source_audit.current_source_record_judgments_from_payload(
                {"schema": 1, "paper": PAPER, "items": {key: forged}},
                PAPER,
                current,
                allow_schema4_to5_migration=True,
            ),
            {},
        )
        self.assertFalse(
            REPOSITORY.source_record_judgment_current(
                key,
                forged,
                digest="",
                expected_item_digests={},
            )
        )

        ordinary_path = paper_dir / "audit" / "source_record_match_llm.json"
        ordinary_path.write_text(
            json.dumps({"schema": 1, "paper": PAPER, "items": {key: forged}}),
            encoding="utf-8",
        )
        self.assertEqual(REPOSITORY.source_record_judgment_items(ordinary_path, PAPER), {})

    def test_cli_generator_is_json_only_and_deterministic(self) -> None:
        prior, judgments, current = self.matching_inputs()
        with tempfile.TemporaryDirectory() as tmpdir:
            root = Path(tmpdir)
            prior_path = root / "prior_raw.json"
            judgments_path = root / "prior_judgments.json"
            current_path = root / "current_raw.json"
            output_path = root / "overlay.json"
            for path, payload in (
                (prior_path, prior),
                (judgments_path, judgments),
                (current_path, current),
            ):
                path.write_text(json.dumps(payload, sort_keys=True), encoding="utf-8")
            command = [
                sys.executable,
                str(SOURCE_RECORD_AUDIT_HELPER),
                "--root",
                str(root),
                "--paper",
                PAPER,
                "--generate-schema4-to5-migration",
                "--prior-source-record-audit",
                str(prior_path),
                "--prior-source-record-judgments",
                str(judgments_path),
                "--current-source-record-audit",
                str(current_path),
                "--schema4-to5-migration-out",
                str(output_path),
            ]
            first = subprocess.run(command, text=True, capture_output=True, check=False)
            self.assertEqual(first.returncode, 0, first.stderr)
            first_text = output_path.read_text(encoding="utf-8")
            second = subprocess.run(command, text=True, capture_output=True, check=False)
            self.assertEqual(second.returncode, 0, second.stderr)
            self.assertEqual(output_path.read_text(encoding="utf-8"), first_text)
            generated = json.loads(first_text)
            self.assertEqual(len(generated["items"]), 1)


if __name__ == "__main__":
    unittest.main()
