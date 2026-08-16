#!/usr/bin/env python3
"""Focused tests for historical selected-attestation semantic reuse."""

from __future__ import annotations

import copy
import hashlib
import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import audit_evidence_integrity as EVIDENCE  # noqa: E402
from scripts import audit_conclusion_provenance as CONCLUSION  # noqa: E402
from scripts import audit_repository as REPOSITORY  # noqa: E402
from scripts import source_record_attested_selected_reuse as REUSE  # noqa: E402
from scripts import source_record_current_revalidation as CURRENT  # noqa: E402
from scripts import source_record_differential_revalidation as DIFFERENTIAL  # noqa: E402
from scripts.source_record_integrity import (  # noqa: E402
    stamp_source_record_audit_receipts,
)


PAPER = "FixturePaper"
PROMPT = CURRENT.SOURCE_RECORD_V10_PROMPT_VERSION
SOURCE_RECORD_AUDIT_HELPER = (
    ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
)


def digest(char: str) -> str:
    return char * 64


def raw_item(key: str, *, semantic_tag: str = "same") -> dict[str, object]:
    return {
        "judgment_key": key,
        "kind": "boundary_input",
        "expanded_input_type": "P",
        "expanded_lean_surface": {
            "input_type": "P",
            "result_type": semantic_tag,
        },
        "semantic_obligation_tag": semantic_tag,
        # This is intentionally presentation-only. Changing it proves that
        # the reuse route does not join historical/current items by key/name.
        "reviewed_declaration_identity": {
            "qualified_declaration": f"Fixture.PaperInterface.{key}",
            "declaration_sha256": digest("a"),
        },
        "reviewed_elaborated_signature_identities": [
            {
                "qualified_declaration": "Fixture.PaperInterface.stable_endpoint",
                "elaborated_signature_sha256": digest("9"),
            }
        ],
        "source_record_item_reuse_eligibility": {"eligible": True, "blockers": []},
        "source_record_item_digest_schema": 5,
        "source_record_item_semantic_id": digest("b"),
        "source_record_item_context_sha256": digest("c"),
        "source_record_item_sha256": digest("d"),
    }


def raw_audit(*items: dict[str, object]) -> dict[str, object]:
    payload: dict[str, object] = {
        "paper": PAPER,
        "prompt_version": PROMPT,
        "source_record_policy_version": PROMPT,
        "boundary_input_items": list(items),
        "lean_check": {"returncode": 0},
        "recursion_failure_count": 0,
    }
    stamp_source_record_audit_receipts(payload)
    return payload


def load_source_record_audit_helper() -> object:
    spec = importlib.util.spec_from_file_location(
        "attested_selected_reuse_source_record_audit_helper",
        SOURCE_RECORD_AUDIT_HELPER,
    )
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


class AttestedSelectedReuseTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.paper_dir = self.root / "papers" / PAPER
        self.audit_dir = self.paper_dir / "audit"
        self.audit_dir.mkdir(parents=True)
        (self.paper_dir / "status.json").write_text(
            json.dumps({"status": "formalized", "review_surface": {}}),
            encoding="utf-8",
        )

    def _write(self, name: str, payload: dict[str, object]) -> Path:
        path = self.audit_dir / name
        path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
        return path

    def _fixture(
        self,
        *,
        current_items: list[dict[str, object]] | None = None,
        historical_key: str = "historical_key : P",
        invalid_unrelated_base_item: bool = False,
        invalid_selected_base_item: bool = False,
    ) -> tuple[dict[str, object], dict[str, object], dict[str, object], dict[str, object], Path, Path, Path, Path]:
        """Create a selected review whose historical raw JSON is not retained."""

        historical_raw = raw_audit(raw_item(historical_key))
        current = raw_audit(
            *(current_items or [raw_item("renamed_current_key : P")])
        )
        current_path = self._write("source_record_audit.json", current)
        base = {
            "schema": 1,
            "paper": PAPER,
            "prompt_version": PROMPT,
            "source_record_audit_sha256": digest("e"),
            "validator": "base v10 reviewer",
            "validated_at": "2026-07-26T00:00:00Z",
            "items": {
                historical_key: {
                    "classification": "validated_source_assumption",
                    "reason": "historical base response",
                    "prompt_version": PROMPT,
                    "source_record_audit_sha256": digest("e"),
                    "source_record_item_digest_schema": 4,
                    "source_record_item_semantic_id": digest("f"),
                    "source_record_item_sha256": digest("0"),
                    "validator": "base v10 reviewer",
                    "validated_at": "2026-07-26T00:00:00Z",
                }
            },
        }
        if invalid_selected_base_item:
            base["items"][historical_key]["source_record_audit_sha256"] = digest("f")
        if invalid_unrelated_base_item:
            unrelated_key = "unrelated_rebound_base_key : P"
            unrelated = copy.deepcopy(base["items"][historical_key])
            unrelated["source_record_audit_sha256"] = digest("f")
            base["items"][unrelated_key] = unrelated
        base_path = self._write("source_record_match_llm.base.json", base)
        historical_groups, group_errors = DIFFERENTIAL._raw_item_groups(historical_raw)
        self.assertEqual(group_errors, {})
        descriptor = str(historical_groups[historical_key]["descriptor_sha256"])
        overlay_descriptor = digest("1")
        attestation = {
            "schema": CURRENT.SELECTED_CURRENT_REVALIDATION_SCHEMA,
            "artifact_kind": CURRENT.SELECTED_CURRENT_REVALIDATION_ATTESTATION_KIND,
            "policy_version": CURRENT.SELECTED_CURRENT_REVALIDATION_POLICY_VERSION,
            "paper": PAPER,
            "prior_judgment_sidecar_path": base_path.relative_to(self.paper_dir).as_posix(),
            "prior_judgment_sidecar_sha256": hashlib.sha256(base_path.read_bytes()).hexdigest(),
            "current_source_record_audit_sha256": historical_raw[
                "source_record_audit_sha256"
            ],
            "generated_judgment_keys_sha256": CURRENT.generated_judgment_keys_sha256(
                historical_raw
            ),
            "generated_judgment_surface_sha256": CURRENT.generated_judgment_surface_sha256(
                historical_raw
            ),
            "differential_overlay_path": "audit/source_record_differential_revalidation.json",
            "differential_overlay_sha256": digest("2"),
            "differential_overlay_current_group_descriptors": {
                "historical_overlay_key : Q": overlay_descriptor
            },
            "differential_overlay_current_group_descriptors_sha256": CURRENT._canonical_digest(
                {"historical_overlay_key : Q": overlay_descriptor}
            ),
            "selected_current_group_descriptors": {historical_key: descriptor},
            "selected_current_group_descriptors_sha256": CURRENT._canonical_digest(
                {historical_key: descriptor}
            ),
            "new_judgment_keys_required": [],
            "new_judgments": {},
            "judgment_amendments": {},
            "semantic_model_dimension_amendments": {},
            "review_scope": CURRENT.SELECTED_CURRENT_REVALIDATION_SCOPE,
            "reviewed_current_semantics": True,
            "reviewer": "historical selected semantic reviewer",
            "validated_at": "2026-07-27T00:00:00Z",
        }
        attestation_path = self._write("selected_current_semantic_revalidation.json", attestation)
        base_items = CURRENT._sidecar_items(base, paper=PAPER)
        expected = CURRENT._selected_expected_semantic_items(
            base_items, attestation, selected_keys={historical_key}
        )
        selected_value = copy.deepcopy(expected[historical_key])
        historical_receipt = CURRENT._historical_item_receipt(selected_value)
        if historical_receipt:
            selected_value[CURRENT.PRIOR_ITEM_RECEIPT_FIELD] = historical_receipt
        historical_pins = CURRENT._current_item_pins(
            CURRENT.generated_judgment_items(historical_raw)[historical_key]
        )
        selected_value.update(
            {
                "prompt_version": PROMPT,
                "validator": attestation["reviewer"],
                "validated_at": attestation["validated_at"],
                "source_record_audit_sha256": historical_raw[
                    "source_record_audit_sha256"
                ],
                CURRENT.SELECTED_CURRENT_REVALIDATION_ITEM_FIELD: {
                    "schema": CURRENT.SELECTED_CURRENT_REVALIDATION_SCHEMA,
                    "attestation_sha256": hashlib.sha256(attestation_path.read_bytes()).hexdigest(),
                    "current_group_semantic_descriptor_sha256": descriptor,
                },
            }
        )
        if historical_pins:
            selected_value["source_record_item_digest_schema"] = (
                CURRENT.SOURCE_RECORD_ITEM_DIGEST_SCHEMA
            )
            selected_value["source_record_item_sha256s"] = historical_pins
            selected_value["source_record_item_sha256"] = historical_pins[0][
                "source_record_item_sha256"
            ]
        selected = {
            "schema": 1,
            "paper": PAPER,
            "prompt_version": PROMPT,
            "validator": attestation["reviewer"],
            "validated_at": attestation["validated_at"],
            "source_record_audit_sha256": historical_raw[
                "source_record_audit_sha256"
            ],
            "items": {historical_key: selected_value},
            CURRENT.SELECTED_CURRENT_REVALIDATION_FIELD: {
                "schema": CURRENT.SELECTED_CURRENT_REVALIDATION_SCHEMA,
                "policy_version": CURRENT.SELECTED_CURRENT_REVALIDATION_POLICY_VERSION,
                "attestation_path": attestation_path.relative_to(self.paper_dir).as_posix(),
                "attestation_sha256": hashlib.sha256(attestation_path.read_bytes()).hexdigest(),
                "prior_judgment_sidecar_path": base_path.relative_to(self.paper_dir).as_posix(),
                "prior_judgment_sidecar_sha256": hashlib.sha256(base_path.read_bytes()).hexdigest(),
                "current_judgment_sidecar_path": "audit/source_record_match_llm.json",
                "differential_overlay_path": attestation["differential_overlay_path"],
                "differential_overlay_sha256": attestation["differential_overlay_sha256"],
                "current_source_record_audit_sha256": historical_raw[
                    "source_record_audit_sha256"
                ],
                "generated_judgment_keys_sha256": attestation[
                    "generated_judgment_keys_sha256"
                ],
                "generated_judgment_surface_sha256": attestation[
                    "generated_judgment_surface_sha256"
                ],
                "differential_overlay_current_group_descriptors": attestation[
                    "differential_overlay_current_group_descriptors"
                ],
                "differential_overlay_current_group_descriptors_sha256": attestation[
                    "differential_overlay_current_group_descriptors_sha256"
                ],
                "selected_current_group_descriptors": attestation[
                    "selected_current_group_descriptors"
                ],
                "selected_current_group_descriptors_sha256": attestation[
                    "selected_current_group_descriptors_sha256"
                ],
                "review_scope": CURRENT.SELECTED_CURRENT_REVALIDATION_SCOPE,
                "response_semantic_ledger_sha256": CURRENT._canonical_digest(
                    CURRENT._selected_semantic_judgment_ledger(
                        {historical_key: selected_value}
                    )
                ),
            },
        }
        selected_path = self._write(
            "source_record_match_llm.selected_snapshot.json", selected
        )
        return (
            historical_raw,
            current,
            base,
            selected,
            current_path,
            base_path,
            attestation_path,
            selected_path,
        )

    def _build(
        self,
        current: dict[str, object],
        base: dict[str, object],
        selected: dict[str, object],
        current_path: Path,
        base_path: Path,
        attestation_path: Path,
        selected_path: Path,
    ) -> dict[str, object]:
        attestation = json.loads(attestation_path.read_text(encoding="utf-8"))
        return REUSE.build_attested_selected_semantic_reuse(
            current,
            selected,
            attestation,
            base,
            paper=PAPER,
            paper_dir=self.paper_dir,
            current_raw_audit_path=current_path,
            historical_selected_sidecar_path=selected_path,
            historical_selected_attestation_path=attestation_path,
            historical_base_sidecar_path=base_path,
        )

    def test_reuses_a_unique_exact_descriptor_after_the_key_is_renamed(self) -> None:
        (
            _historical,
            current,
            base,
            selected,
            current_path,
            base_path,
            attestation_path,
            selected_path,
        ) = self._fixture()
        artifact = self._build(
            current,
            base,
            selected,
            current_path,
            base_path,
            attestation_path,
            selected_path,
        )
        self.assertEqual(len(artifact["items"]), 1)
        self.assertEqual(artifact["manual_review_required"], {})
        artifact_path = self._write(
            REUSE.SOURCE_RECORD_ATTESTED_SELECTED_REUSE_FILENAME, artifact
        )
        loaded = REUSE.load_current_attested_selected_semantic_reuse_items(
            self.paper_dir, PAPER, current, path=artifact_path
        )
        self.assertEqual(set(loaded), {"renamed_current_key : P"})
        entry = loaded["renamed_current_key : P"]
        self.assertTrue(
            REUSE.is_loaded_source_record_attested_selected_reuse_item(entry)
        )
        self.assertEqual(
            entry["classification"], "validated_source_assumption"
        )
        with patch.object(EVIDENCE, "source_record_audit_identity_error", return_value=""):
            self.assertEqual(
                set(
                    EVIDENCE.current_source_record_judgment_items(
                        current,
                        {"schema": 1, "paper": PAPER, "items": {}},
                        folder=self.paper_dir,
                    )
                ),
                {"renamed_current_key : P"},
            )

    def test_reuses_after_derived_current_judgment_summary_refresh(self) -> None:
        (
            _historical,
            current,
            base,
            selected,
            current_path,
            base_path,
            attestation_path,
            selected_path,
        ) = self._fixture()
        artifact = self._build(
            current,
            base,
            selected,
            current_path,
            base_path,
            attestation_path,
            selected_path,
        )
        artifact_path = self._write(
            REUSE.SOURCE_RECORD_ATTESTED_SELECTED_REUSE_FILENAME, artifact
        )
        refreshed = copy.deepcopy(current)
        refreshed["current_source_record_judgment_count"] = 1
        refreshed["resolved_conclusion_dependency_count"] = 1
        refreshed["resolved_conclusion_dependency_items"] = [
            {"judgment_key": "renamed_current_key : P"}
        ]
        refreshed["unresolved_conclusion_dependency_count"] = 0
        refreshed["unresolved_conclusion_dependency_items"] = []
        stamp_source_record_audit_receipts(refreshed)
        self.assertEqual(
            refreshed["source_record_audit_sha256"],
            current["source_record_audit_sha256"],
        )
        self.assertEqual(
            refreshed["source_record_audit_integrity_sha256"],
            current["source_record_audit_integrity_sha256"],
        )
        current_path.write_text(
            json.dumps(refreshed, indent=2, sort_keys=True), encoding="utf-8"
        )
        loaded = REUSE.load_current_attested_selected_semantic_reuse_items(
            self.paper_dir, PAPER, refreshed, path=artifact_path
        )
        self.assertEqual(set(loaded), {"renamed_current_key : P"})

    def test_stale_unrelated_base_entry_does_not_block_selected_replay(self) -> None:
        (
            _historical,
            current,
            base,
            selected,
            current_path,
            base_path,
            attestation_path,
            selected_path,
        ) = self._fixture(invalid_unrelated_base_item=True)
        artifact = self._build(
            current,
            base,
            selected,
            current_path,
            base_path,
            attestation_path,
            selected_path,
        )
        self.assertEqual(len(artifact["items"]), 1)
        self.assertEqual(artifact["manual_review_required"], {})
        self.assertEqual(artifact["quarantined_historical_selected_keys"], {})

    def test_stale_selected_base_entry_is_quarantined_and_manual_only(self) -> None:
        (
            _historical,
            current,
            base,
            selected,
            current_path,
            base_path,
            attestation_path,
            selected_path,
        ) = self._fixture(invalid_selected_base_item=True)
        artifact = self._build(
            current,
            base,
            selected,
            current_path,
            base_path,
            attestation_path,
            selected_path,
        )
        self.assertEqual(artifact["items"], {})
        self.assertEqual(len(artifact["manual_review_required"]), 1)
        quarantine = artifact["quarantined_historical_selected_keys"]
        self.assertEqual(set(quarantine), {"historical_key : P"})
        record = quarantine["historical_key : P"]
        self.assertIn(
            record["historical_selected_descriptor_sha256"],
            artifact["manual_review_required"],
        )
        self.assertIn("base judgment is invalid", record["reason"])
        artifact_path = self._write(
            REUSE.SOURCE_RECORD_ATTESTED_SELECTED_REUSE_FILENAME, artifact
        )
        self.assertEqual(
            REUSE.load_current_attested_selected_semantic_reuse_items(
                self.paper_dir, PAPER, current, path=artifact_path
            ),
            {},
        )

    def test_rejects_altered_immutable_attestation_or_base_bytes(self) -> None:
        (
            _historical,
            current,
            base,
            selected,
            current_path,
            base_path,
            attestation_path,
            selected_path,
        ) = self._fixture()
        artifact = self._build(
            current,
            base,
            selected,
            current_path,
            base_path,
            attestation_path,
            selected_path,
        )
        artifact_path = self._write(
            REUSE.SOURCE_RECORD_ATTESTED_SELECTED_REUSE_FILENAME, artifact
        )
        altered_base = copy.deepcopy(base)
        altered_base["items"]["historical_key : P"]["reason"] = "altered"
        base_path.write_text(json.dumps(altered_base), encoding="utf-8")
        self.assertEqual(
            REUSE.load_current_attested_selected_semantic_reuse_items(
                self.paper_dir, PAPER, current, path=artifact_path
            ),
            {},
        )

    def test_rejects_altered_immutable_attestation_bytes(self) -> None:
        (
            _historical,
            current,
            base,
            selected,
            current_path,
            base_path,
            attestation_path,
            selected_path,
        ) = self._fixture()
        artifact = self._build(
            current,
            base,
            selected,
            current_path,
            base_path,
            attestation_path,
            selected_path,
        )
        artifact_path = self._write(
            REUSE.SOURCE_RECORD_ATTESTED_SELECTED_REUSE_FILENAME, artifact
        )
        altered_attestation = json.loads(attestation_path.read_text(encoding="utf-8"))
        altered_attestation["review_notes"] = "altered after authenticated reuse"
        attestation_path.write_text(json.dumps(altered_attestation), encoding="utf-8")
        self.assertEqual(
            REUSE.load_current_attested_selected_semantic_reuse_items(
                self.paper_dir, PAPER, current, path=artifact_path
            ),
            {},
        )

    def test_rejects_altered_immutable_selected_sidecar_bytes(self) -> None:
        (
            _historical,
            current,
            base,
            selected,
            current_path,
            base_path,
            attestation_path,
            selected_path,
        ) = self._fixture()
        artifact = self._build(
            current,
            base,
            selected,
            current_path,
            base_path,
            attestation_path,
            selected_path,
        )
        artifact_path = self._write(
            REUSE.SOURCE_RECORD_ATTESTED_SELECTED_REUSE_FILENAME, artifact
        )
        altered_selected = copy.deepcopy(selected)
        altered_selected["items"]["historical_key : P"]["reason"] = "altered"
        selected_path.write_text(json.dumps(altered_selected), encoding="utf-8")
        self.assertEqual(
            REUSE.load_current_attested_selected_semantic_reuse_items(
                self.paper_dir, PAPER, current, path=artifact_path
            ),
            {},
        )

    def test_deserialized_reuse_provenance_without_loader_token_is_not_evidence(self) -> None:
        (
            _historical,
            current,
            _base,
            selected,
            _current_path,
            _base_path,
            _attestation_path,
            _selected_path,
        ) = self._fixture()
        forged = copy.deepcopy(selected["items"]["historical_key : P"])
        forged["source_record_audit_sha256"] = current["source_record_audit_sha256"]
        forged[REUSE.SOURCE_RECORD_ATTESTED_SELECTED_REUSE_ITEM_FIELD] = {
            "schema": REUSE.SOURCE_RECORD_ATTESTED_SELECTED_REUSE_SCHEMA,
            "artifact_sha256": digest("7"),
            "historical_selected_descriptor_sha256": digest("8"),
            "current_group_semantic_descriptor_sha256": digest("8"),
            "current_source_record_audit_sha256": current["source_record_audit_sha256"],
        }
        # A JSON round trip proves that an on-disk marker cannot forge the
        # private loader token used by the evidence gate.
        forged = json.loads(json.dumps(forged))
        with patch.object(EVIDENCE, "source_record_audit_identity_error", return_value=""):
            self.assertEqual(
                EVIDENCE.current_source_record_judgment_items(
                    current,
                    {
                        "schema": 1,
                        "paper": PAPER,
                        "prompt_version": PROMPT,
                        "source_record_audit_sha256": current[
                            "source_record_audit_sha256"
                        ],
                        "items": {"renamed_current_key : P": forged},
                    },
                    folder=self.paper_dir,
                ),
                {},
            )

    def test_repository_and_conclusion_consumers_load_only_replayed_items(self) -> None:
        (
            _historical,
            current,
            base,
            selected,
            current_path,
            base_path,
            attestation_path,
            selected_path,
        ) = self._fixture()
        artifact = self._build(
            current,
            base,
            selected,
            current_path,
            base_path,
            attestation_path,
            selected_path,
        )
        self._write(REUSE.SOURCE_RECORD_ATTESTED_SELECTED_REUSE_FILENAME, artifact)
        canonical_sidecar = self._write(
            "source_record_match_llm.json",
            {
                "schema": 1,
                "paper": PAPER,
                "prompt_version": PROMPT,
                # This ordinary sidecar intentionally has no direct response:
                # the authenticated selected-reuse overlay supplies the one
                # current raw group.  Make that composition explicit so it
                # cannot be mistaken for an arbitrary empty fragment.
                "manual_current_complement": {
                    "schema": 1,
                    "policy_version": (
                        "source-record-v10-manual-current-complement-v3"
                    ),
                    "completed_template_review_scope": (
                        "all_current_generated_groups_without_authenticated_overlay"
                    ),
                    "current_source_record_audit_sha256": current[
                        "source_record_audit_sha256"
                    ],
                    "generated_judgment_keys_sha256": EVIDENCE.canonical_json_digest(
                        ["renamed_current_key : P"]
                    ),
                    "template_reviewer": "fixture selected-reuse reviewer",
                    "template_validated_at": "2026-08-13T00:00:00Z",
                    "output_sidecar_path": "audit/source_record_match_llm.json",
                },
                "items": {},
            },
        )
        self.assertEqual(
            set(
                REPOSITORY.source_record_judgment_items(
                    canonical_sidecar,
                    PAPER,
                    current_raw_audit=current,
                    paper_dir=self.paper_dir,
                )
            ),
            {"renamed_current_key : P"},
        )
        with patch.object(CONCLUSION, "PAPERS", self.root / "papers"):
            self.assertEqual(
                set(CONCLUSION.current_judgments(PAPER, current)),
                {"renamed_current_key : P"},
            )
        helper = load_source_record_audit_helper()
        self.assertEqual(
            set(helper.current_source_record_judgments(self.paper_dir, PAPER, current)),
            {"renamed_current_key : P"},
        )

    def test_changed_or_ambiguous_current_descriptor_requires_manual_review(self) -> None:
        with self.subTest("changed"):
            (
                _historical,
                current,
                base,
                selected,
                current_path,
                base_path,
                attestation_path,
                selected_path,
            ) = self._fixture(
                current_items=[raw_item("historical_key : P", semantic_tag="changed")]
            )
            artifact = self._build(
                current,
                base,
                selected,
                current_path,
                base_path,
                attestation_path,
                selected_path,
            )
            self.assertEqual(artifact["items"], {})
            self.assertEqual(len(artifact["manual_review_required"]), 1)
        with self.subTest("ambiguous"):
            (
                _historical,
                current,
                base,
                selected,
                current_path,
                base_path,
                attestation_path,
                selected_path,
            ) = self._fixture(
                current_items=[
                    raw_item("renamed_current_key_one : P"),
                    raw_item("renamed_current_key_two : P"),
                ]
            )
            artifact = self._build(
                current,
                base,
                selected,
                current_path,
                base_path,
                attestation_path,
                selected_path,
            )
            self.assertEqual(artifact["items"], {})
            self.assertEqual(len(artifact["manual_review_required"]), 1)


if __name__ == "__main__":
    unittest.main()
