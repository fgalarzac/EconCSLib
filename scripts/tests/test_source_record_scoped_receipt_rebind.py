#!/usr/bin/env python3
"""Focused tests for fail-closed legacy v10 scoped-receipt transport."""

from __future__ import annotations

import copy
import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import source_record_scoped_receipt_rebind as REBIND  # noqa: E402
from scripts import audit_conclusion_provenance as PROVENANCE  # noqa: E402
from scripts import audit_evidence_integrity as EVIDENCE  # noqa: E402
from scripts import (  # noqa: E402
    source_record_historical_association_snapshot_reconciliation as RECONCILIATION,
)
from scripts.source_record_integrity import stamp_source_record_audit_receipts  # noqa: E402
from scripts.formalization_protocol import (  # noqa: E402
    FORMALIZATION_COVERAGE_PROTOCOL_FIELD,
    formalization_coverage_protocol_digest,
)
from scripts.source_record_target_disposition import (  # noqa: E402
    semantic_association_record_digest,
    source_contract_association_record_digest,
    source_map_item_record_digest,
)


PAPER = "FixturePaper"
PROMPT = REBIND.SOURCE_RECORD_V10_PROMPT_VERSION


def _sha(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _write(path: Path, payload: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _file_sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class ScopedReceiptFixture:
    """One current schema-5 row and one visibly legacy predecessor."""

    def __init__(self, root: Path) -> None:
        self.paper_dir = root / PAPER
        self.audit_dir = self.paper_dir / "audit"
        self.archive_dir = self.audit_dir / "archive"
        self.current_key = "current-storage-key"
        self.prior_key = "prior-storage-key"
        self.current_map_path = self.audit_dir / "paper_statement_map.json"
        self.prior_map_path = self.archive_dir / "prior_paper_statement_map.json"
        self.current_raw_path = self.audit_dir / "source_record_audit.json"
        self.prior_raw_path = self.archive_dir / "prior_source_record_audit.json"
        self.prior_sidecar_path = self.archive_dir / "prior_source_record_match_llm.json"
        self.current_map = self._statement_map()
        self.prior_map = copy.deepcopy(self.current_map)
        self.current_raw: dict[str, object] = {}
        self.prior_raw: dict[str, object] = {}
        self.prior_sidecar: dict[str, object] = {}
        self._write_all()

    @staticmethod
    def _source_item() -> dict[str, object]:
        quote = "Theorem A: P follows from the stated model."
        return {
            "statement": "The source theorem has premise P and conclusion Q.",
            "source_location": "sources/paper.txt:10-12",
            "source_kind": "theorem",
            "coverage_status": "covered",
            "claim_bearing": True,
            "source_anchor_evidence": [
                {
                    "path": "sources/paper.txt",
                    "line_start": 10,
                    "line_end": 12,
                    "quoted_text": quote,
                    "quoted_text_sha256": _sha(quote),
                }
            ],
            "semantic_context_requirements": [
                {
                    "kind": "source_model_convention",
                    "source_location": "sources/paper.txt:10-12",
                    "explanation": "The theorem uses the stated source model.",
                    "source_anchor_evidence": [
                        {
                            "path": "sources/paper.txt",
                            "line_start": 10,
                            "line_end": 12,
                            "quoted_text": quote,
                            "quoted_text_sha256": _sha(quote),
                        }
                    ],
                }
            ],
            "model_convention_ids": ["MC-1"],
            "semantic_contract": {
                "evidence_declaration": "Fixture.Paper.evidence",
                "spec_declaration": "Fixture.Paper.spec",
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            },
        }

    @classmethod
    def _statement_map(cls) -> dict[str, object]:
        return {"schema": 1, "items": {"source-address": cls._source_item()}}

    @staticmethod
    def _fidelity() -> dict[str, object]:
        return {
            "schema": 1,
            "paper": PAPER,
            "source_artifact_path": "sources/paper.txt",
            "source_artifact_sha256": _sha("fixture source artifact"),
            "review_status": "reviewed",
            "reviewed_proof_scopes": [],
            "model_conventions": [
                {
                    "id": "MC-1",
                    "source_locator": "sources/paper.txt:10-12",
                    "classification": "source_model_convention",
                    "formal_meaning": "The current source model is fixed.",
                    "why_needed": "It is a premise of the theorem.",
                    "checked_scope": "Fixture.Paper.evidence",
                }
            ],
            "checked_proof_steps": [],
            "defects": [],
        }

    @staticmethod
    def _source_item_for_map(statement_map: dict[str, object]) -> tuple[str, dict[str, object]]:
        items = statement_map["items"]
        assert isinstance(items, dict) and len(items) == 1
        key, value = next(iter(items.items()))
        assert isinstance(key, str) and isinstance(value, dict)
        return key, value

    def _association(self, statement_map: dict[str, object]) -> dict[str, object]:
        source_key, source_item = self._source_item_for_map(statement_map)
        semantic = REBIND.source_item_coverage_sha256(source_item, "")
        signature = {
            "qualified_declaration": "Fixture.Paper.evidence",
            "elaborated_signature_sha256": "a" * 64,
        }
        association: dict[str, object] = {
            "schema": 2,
            "association_mode": "semantic_contract_group_member",
            "semantic_contract_member_role": "direct_evidence",
            "semantic_model_judgment_key": "semantic-model::display-address",
            "reviewed_declaration_identity": {
                "qualified_declaration": "Fixture.Paper.evidence",
                "declaration_sha256": "b" * 64,
            },
            "reviewed_elaborated_signature_identity": signature,
            "source_item_identities": [
                {
                    "source_key": source_key,
                    "source_location": source_item["source_location"],
                    "source_kind": source_item["source_kind"],
                    "source_map_item_sha256": source_map_item_record_digest(source_item),
                    "source_semantic_sha256": semantic,
                    "semantic_contract": copy.deepcopy(source_item["semantic_contract"]),
                }
            ],
        }
        association["semantic_association_sha256"] = semantic_association_record_digest(
            [semantic], signature
        )
        association["association_sha256"] = source_contract_association_record_digest(
            association
        )
        return association

    def _row(
        self, statement_map: dict[str, object], *, key: str, current: bool
    ) -> dict[str, object]:
        row: dict[str, object] = {
            "kind": "boundary_input",
            "judgment_key": key,
            "row": "display-row-name",
            "binder": "hP",
            "input": "hP",
            "lean_source_declaration": "Fixture.Paper.evidence",
            "effective_lean_source_declaration": "Fixture.Paper.evidence",
            "qualified_declaration": "Fixture.Paper.evidence",
            "effective_qualified_declaration": "Fixture.Paper.evidence",
            "reviewed_declaration_identity": {
                "qualified_declaration": "Fixture.Paper.evidence",
                "declaration_sha256": "b" * 64,
            },
            "expanded_input_type": "P",
            "result_relation": "P -> Q",
            "review_alias_expansion": {
                "schema": 1,
                "complete": True,
                "alias_present": False,
                "reviewed_declaration": "Fixture.Paper.evidence",
                "effective_declaration": "Fixture.Paper.evidence",
                "effective_kind": "theorem",
                "steps": [],
                "blocked_routes": [],
            },
            "source_contract_association": self._association(statement_map),
            "reviewed_elaborated_signature_identities": [
                {
                    "qualified_declaration": "Fixture.Paper.evidence",
                    "elaborated_signature_sha256": "a" * 64,
                }
            ],
        }
        if current:
            row.update(
                {
                    "source_record_item_reuse_eligibility": {
                        "eligible": True,
                        "blockers": [],
                    },
                    "source_record_item_digest_schema": REBIND.SOURCE_RECORD_ITEM_DIGEST_SCHEMA,
                    "source_record_item_semantic_id": _sha("current semantic item"),
                    "source_record_item_context_sha256": _sha("current context item"),
                    "source_record_item_sha256": _sha("current context item"),
                }
            )
        return row

    def _raw(
        self, statement_map: dict[str, object], map_path: Path, *, current: bool
    ) -> dict[str, object]:
        row = self._row(
            statement_map,
            key=self.current_key if current else self.prior_key,
            current=current,
        )
        raw: dict[str, object] = {
            "paper": PAPER,
            "prompt_version": PROMPT,
            "source_record_policy_version": PROMPT,
            "paper_statement_map_sha256": _file_sha(map_path),
            "semantic_context_requirements": REBIND.semantic_context_requirements(
                statement_map
            ),
            "semantic_context_requirement_count": 0,
            "semantic_context_requirements_sha256": "",
            "source_proof_fidelity": self._fidelity(),
            "lean_check": {"returncode": 0},
            "recursion_failure_count": 0,
            "formalization_scope": {"kind": "ordinary_named_result_scope"},
            "boundary_input_items": [row],
            "conclusion_dependency_items": [],
            "semantic_model_items": [],
            "recursive_field_items": [],
        }
        contexts = raw["semantic_context_requirements"]
        assert isinstance(contexts, list)
        raw["semantic_context_requirement_count"] = len(contexts)
        raw["semantic_context_requirements_sha256"] = REBIND._load_source_record_audit_helper().stable_digest(contexts)
        if current:
            self._stamp_current_scoped_pins(raw)
        stamp_source_record_audit_receipts(raw)
        return raw

    def _stamp_current_scoped_pins(self, raw: dict[str, object]) -> None:
        items = raw["boundary_input_items"]
        assert isinstance(items, list) and len(items) == 1 and isinstance(items[0], dict)
        helper = REBIND._load_source_record_audit_helper()
        index = helper.source_record_source_map_semantic_index(self.current_map)
        context_pin, fidelity_pin, errors = helper.source_record_item_scoped_context_pins(
            items[0],
            source_map_semantic_index=index,
            source_proof_fidelity=raw["source_proof_fidelity"],
        )
        assert not errors
        if context_pin is not None:
            items[0][REBIND._SCOPED_PIN_FIELDS[0]] = helper.stable_digest(context_pin)
        if fidelity_pin is not None:
            items[0][REBIND._SCOPED_PIN_FIELDS[1]] = helper.stable_digest(fidelity_pin)

    def _refresh_raw(self, *, current: bool, refresh_current_pins: bool = True) -> None:
        raw = self.current_raw if current else self.prior_raw
        statement_map = self.current_map if current else self.prior_map
        map_path = self.current_map_path if current else self.prior_map_path
        raw["paper_statement_map_sha256"] = _file_sha(map_path)
        raw["semantic_context_requirements"] = REBIND.semantic_context_requirements(statement_map)
        contexts = raw["semantic_context_requirements"]
        assert isinstance(contexts, list)
        raw["semantic_context_requirement_count"] = len(contexts)
        raw["semantic_context_requirements_sha256"] = (
            REBIND._load_source_record_audit_helper().stable_digest(contexts)
        )
        raw.pop("source_record_audit_sha256", None)
        raw.pop("source_record_audit_surface_schema", None)
        raw.pop("source_record_audit_surface", None)
        raw.pop("source_record_audit_integrity_schema", None)
        raw.pop("source_record_audit_integrity_sha256", None)
        if current and refresh_current_pins:
            # The scope receipt is generated from the current map and ledger.
            row = self.current_row()
            row.pop(REBIND._SCOPED_PIN_FIELDS[0], None)
            row.pop(REBIND._SCOPED_PIN_FIELDS[1], None)
            self._stamp_current_scoped_pins(raw)
        stamp_source_record_audit_receipts(raw)
        _write(self.current_raw_path if current else self.prior_raw_path, raw)
        if not current and self.prior_sidecar:
            self.prior_sidecar["source_record_audit_sha256"] = raw[
                "source_record_audit_sha256"
            ]
            responses = self.prior_sidecar.get("items")
            if isinstance(responses, dict):
                response = responses.get(self.prior_key)
                if isinstance(response, dict):
                    response["source_record_audit_sha256"] = raw[
                        "source_record_audit_sha256"
                    ]
            self.sync_sidecar()

    def _restamp_raw(self, *, current: bool) -> None:
        """Persist a deliberately malformed global payload with valid raw receipts."""

        raw = self.current_raw if current else self.prior_raw
        for field in (
            "source_record_audit_sha256",
            "source_record_audit_surface_schema",
            "source_record_audit_surface",
            "source_record_audit_integrity_schema",
            "source_record_audit_integrity_sha256",
        ):
            raw.pop(field, None)
        stamp_source_record_audit_receipts(raw)
        _write(self.current_raw_path if current else self.prior_raw_path, raw)
        if not current and self.prior_sidecar:
            self.prior_sidecar["source_record_audit_sha256"] = raw[
                "source_record_audit_sha256"
            ]
            responses = self.prior_sidecar.get("items")
            if isinstance(responses, dict) and isinstance(
                responses.get(self.prior_key), dict
            ):
                responses[self.prior_key]["source_record_audit_sha256"] = raw[
                    "source_record_audit_sha256"
                ]
            self.sync_sidecar()

    def _write_all(self) -> None:
        _write(self.current_map_path, self.current_map)
        _write(self.prior_map_path, self.prior_map)
        self.current_raw = self._raw(self.current_map, self.current_map_path, current=True)
        self.prior_raw = self._raw(self.prior_map, self.prior_map_path, current=False)
        _write(self.current_raw_path, self.current_raw)
        _write(self.prior_raw_path, self.prior_raw)
        self.prior_sidecar = {
            "schema": 1,
            "paper": PAPER,
            "prompt_version": PROMPT,
            "source_record_audit_sha256": self.prior_raw["source_record_audit_sha256"],
            "validator": "fixture reviewer",
            "validated_at": "2026-07-28T00:00:00Z",
            "items": {
                self.prior_key: {
                    "classification": "validated_source_assumption",
                    "reason": "The source-facing premise was reviewed.",
                    "prompt_version": PROMPT,
                    "source_record_audit_sha256": self.prior_raw[
                        "source_record_audit_sha256"
                    ],
                    "validator": "fixture reviewer",
                    "validated_at": "2026-07-28T00:00:00Z",
                }
            },
        }
        _write(self.prior_sidecar_path, self.prior_sidecar)

    def current_row(self) -> dict[str, object]:
        values = self.current_raw["boundary_input_items"]
        assert isinstance(values, list) and values and isinstance(values[0], dict)
        return values[0]

    def prior_row(self) -> dict[str, object]:
        values = self.prior_raw["boundary_input_items"]
        assert isinstance(values, list) and values and isinstance(values[0], dict)
        return values[0]

    def sync_map(self, *, current: bool) -> None:
        _write(self.current_map_path if current else self.prior_map_path, self.current_map if current else self.prior_map)
        self._refresh_raw(current=current)

    def sync_sidecar(self) -> None:
        _write(self.prior_sidecar_path, self.prior_sidecar)

    def build(self) -> dict[str, object]:
        return REBIND.build_source_record_scoped_receipt_rebind(
            paper=PAPER,
            paper_dir=self.paper_dir,
            prior_raw_audit=self.prior_raw,
            current_raw_audit=self.current_raw,
            prior_sidecar=self.prior_sidecar,
            prior_raw_audit_path=self.prior_raw_path,
            current_raw_audit_path=self.current_raw_path,
            prior_sidecar_path=self.prior_sidecar_path,
            prior_statement_map=self.prior_map,
            current_statement_map=self.current_map,
            prior_statement_map_path=self.prior_map_path,
            current_statement_map_path=self.current_map_path,
            prior_judgment_keys=[self.prior_key],
        )

    def write_overlay(self, payload: dict[str, object]) -> Path:
        path = REBIND.source_record_scoped_receipt_rebind_overlay_path(self.paper_dir)
        _write(path, payload)
        return path

    def refresh_current_association(self) -> None:
        row = self.current_row()
        association = row["source_contract_association"]
        assert isinstance(association, dict)
        identities = association["source_item_identities"]
        assert isinstance(identities, list) and len(identities) == 1 and isinstance(identities[0], dict)
        signature = association["reviewed_elaborated_signature_identity"]
        assert isinstance(signature, dict)
        association["semantic_association_sha256"] = semantic_association_record_digest(
            [str(identities[0]["source_semantic_sha256"])], signature
        )
        association["association_sha256"] = source_contract_association_record_digest(
            association
        )


class SourceRecordScopedReceiptRebindTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.fixture = ScopedReceiptFixture(Path(self.temporary.name))

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_success_replays_only_current_receipts(self) -> None:
        artifact = self.fixture.build()
        self.assertEqual(
            REBIND.source_record_scoped_receipt_rebind_overlay_error(
                artifact, paper=PAPER, paper_dir=self.fixture.paper_dir
            ),
            "",
        )
        self.fixture.write_overlay(artifact)
        loaded = REBIND.load_current_source_record_scoped_receipt_rebind_items(
            self.fixture.paper_dir, PAPER, self.fixture.current_raw
        )
        self.assertEqual(set(loaded), {self.fixture.current_key})
        response = loaded[self.fixture.current_key]
        self.assertTrue(REBIND.is_loaded_source_record_scoped_receipt_rebind_item(response))
        self.assertEqual(response["classification"], "validated_source_assumption")
        self.assertEqual(
            response["reason"], "The source-facing premise was reviewed."
        )
        self.assertEqual(
            response["source_record_audit_sha256"],
            self.fixture.current_raw["source_record_audit_sha256"],
        )
        self.assertIn("semantic_association_sha256", response)
        self.assertTrue(
            REBIND.source_record_scoped_receipt_rebind_item_has_provenance(response)
        )

    def test_candidate_payload_is_rejected_by_content(self) -> None:
        response = self.fixture.prior_sidecar["items"]
        assert isinstance(response, dict)
        entry = response[self.fixture.prior_key]
        assert isinstance(entry, dict)
        entry["candidate_only"] = True
        self.fixture.sync_sidecar()
        with self.assertRaisesRegex(REBIND.SourceRecordScopedReceiptRebindError, "candidate/non-evidence"):
            self.fixture.build()

    def test_semantic_recursive_and_multi_member_groups_are_rejected(self) -> None:
        for section, expected in (
            ("semantic_model_items", "forbidden"),
            ("recursive_field_items", "forbidden"),
        ):
            with self.subTest(section=section):
                fixture = ScopedReceiptFixture(Path(self.temporary.name) / section)
                row = fixture.prior_row()
                fixture.prior_raw["boundary_input_items"] = []
                destination = fixture.prior_raw[section]
                assert isinstance(destination, list)
                destination.append(row)
                fixture._refresh_raw(current=False)
                with self.assertRaisesRegex(REBIND.SourceRecordScopedReceiptRebindError, expected):
                    fixture.build()
        fixture = ScopedReceiptFixture(Path(self.temporary.name) / "multi")
        duplicate = copy.deepcopy(fixture.current_row())
        duplicate["kind"] = "conclusion_dependency"
        destination = fixture.current_raw["conclusion_dependency_items"]
        assert isinstance(destination, list)
        destination.append(duplicate)
        fixture._refresh_raw(current=True)
        with self.assertRaises(REBIND.SourceRecordScopedReceiptRebindError):
            fixture.build()

    def test_source_model_route_signature_and_relation_drift_are_rejected(self) -> None:
        # Source content drift is invalid even before comparison because the
        # generated association no longer names the map's source-content SHA.
        fixture = ScopedReceiptFixture(Path(self.temporary.name) / "source")
        _key, source = fixture._source_item_for_map(fixture.current_map)
        source["statement"] = "A materially different source theorem."
        _write(fixture.current_map_path, fixture.current_map)
        fixture._refresh_raw(current=True, refresh_current_pins=False)
        with self.assertRaises(REBIND.SourceRecordScopedReceiptRebindError):
            fixture.build()

        # A formalization-scope/model change must be part of the exact descriptor.
        fixture = ScopedReceiptFixture(Path(self.temporary.name) / "model")
        fixture.current_raw["formalization_scope"] = {"kind": "changed_source_model"}
        fixture._refresh_raw(current=True)
        with self.assertRaisesRegex(REBIND.SourceRecordScopedReceiptRebindError, "exactly one current"):
            fixture.build()

        fixture = ScopedReceiptFixture(Path(self.temporary.name) / "route")
        association = fixture.current_row()["source_contract_association"]
        assert isinstance(association, dict)
        association["association_mode"] = "different_source_route_mode"
        fixture.refresh_current_association()
        fixture._refresh_raw(current=True)
        with self.assertRaisesRegex(REBIND.SourceRecordScopedReceiptRebindError, "exactly one current"):
            fixture.build()

        fixture = ScopedReceiptFixture(Path(self.temporary.name) / "signature")
        association = fixture.current_row()["source_contract_association"]
        signatures = fixture.current_row()["reviewed_elaborated_signature_identities"]
        assert isinstance(association, dict) and isinstance(signatures, list)
        signature = association["reviewed_elaborated_signature_identity"]
        assert isinstance(signature, dict) and isinstance(signatures[0], dict)
        signature["elaborated_signature_sha256"] = "c" * 64
        signatures[0]["elaborated_signature_sha256"] = "c" * 64
        fixture.refresh_current_association()
        fixture._refresh_raw(current=True)
        with self.assertRaisesRegex(REBIND.SourceRecordScopedReceiptRebindError, "exactly one current"):
            fixture.build()

        fixture = ScopedReceiptFixture(Path(self.temporary.name) / "relation")
        fixture.current_row()["result_relation"] = "P -> R"
        fixture._refresh_raw(current=True)
        with self.assertRaisesRegex(REBIND.SourceRecordScopedReceiptRebindError, "exactly one current"):
            fixture.build()

    def test_visibly_legacy_is_distinct_from_partially_modern(self) -> None:
        self.assertIsInstance(self.fixture.build(), dict)
        self.fixture.prior_row()[REBIND._SCOPED_PIN_FIELDS[0]] = "d" * 64
        self.fixture._refresh_raw(current=False)
        with self.assertRaisesRegex(
            REBIND.SourceRecordScopedReceiptRebindError, "partially-modern"
        ):
            self.fixture.build()

    def test_missing_or_invalid_global_payloads_are_rejected(self) -> None:
        self.fixture.prior_raw.pop("semantic_context_requirements", None)
        self.fixture._restamp_raw(current=False)
        with self.assertRaisesRegex(REBIND.SourceRecordScopedReceiptRebindError, "semantic_context_requirements"):
            self.fixture.build()

        fixture = ScopedReceiptFixture(Path(self.temporary.name) / "fidelity")
        fixture.current_raw["source_proof_fidelity"] = None
        fixture._restamp_raw(current=True)
        with self.assertRaisesRegex(REBIND.SourceRecordScopedReceiptRebindError, "source_proof_fidelity"):
            fixture.build()

    def test_scoped_pin_mismatch_is_rejected(self) -> None:
        fidelity = self.fixture.prior_raw["source_proof_fidelity"]
        assert isinstance(fidelity, dict)
        conventions = fidelity["model_conventions"]
        assert isinstance(conventions, list) and isinstance(conventions[0], dict)
        conventions[0]["formal_meaning"] = "A changed archived proof-fidelity convention."
        self.fixture._refresh_raw(current=False)
        with self.assertRaisesRegex(REBIND.SourceRecordScopedReceiptRebindError, "scoped source pins differ"):
            self.fixture.build()

    def test_only_replayed_association_reconciliation_can_witness_a_bad_prior_map_sha(self) -> None:
        """The one exception binds exact archived raw bytes and witness items."""

        self.fixture.prior_map["paper"] = PAPER
        _write(self.fixture.prior_map_path, self.fixture.prior_map)
        self.fixture.prior_raw["paper_statement_map_sha256"] = "f" * 64
        self.fixture._restamp_raw(current=False)
        reconciliation_path = (
            self.fixture.audit_dir
            / RECONCILIATION.SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_FILENAME
        )
        RECONCILIATION.write_historical_association_snapshot_reconciliation(
            paper_dir=self.fixture.paper_dir,
            paper=PAPER,
            raw_audit_path=self.fixture.prior_raw_path,
            witness_map_path=self.fixture.prior_map_path,
            output_path=reconciliation_path,
        )
        artifact = REBIND.build_source_record_scoped_receipt_rebind(
            paper=PAPER,
            paper_dir=self.fixture.paper_dir,
            prior_raw_audit=self.fixture.prior_raw,
            current_raw_audit=self.fixture.current_raw,
            prior_sidecar=self.fixture.prior_sidecar,
            prior_raw_audit_path=self.fixture.prior_raw_path,
            current_raw_audit_path=self.fixture.current_raw_path,
            prior_sidecar_path=self.fixture.prior_sidecar_path,
            prior_statement_map=None,
            current_statement_map=self.fixture.current_map,
            prior_statement_map_path=None,
            current_statement_map_path=self.fixture.current_map_path,
            prior_judgment_keys=[self.fixture.prior_key],
            prior_association_snapshot_reconciliation_path=reconciliation_path,
        )
        validation = artifact["prior_statement_map_validation"]
        assert isinstance(validation, dict)
        self.assertEqual(
            validation["mode"], "historical_association_snapshot_reconciliation"
        )
        self.fixture.write_overlay(artifact)
        loaded = REBIND.load_current_source_record_scoped_receipt_rebind_items(
            self.fixture.paper_dir, PAPER, self.fixture.current_raw
        )
        self.assertIn(self.fixture.current_key, loaded)
        with self.assertRaisesRegex(
            REBIND.SourceRecordScopedReceiptRebindError, "mutually exclusive"
        ):
            REBIND.build_source_record_scoped_receipt_rebind(
                paper=PAPER,
                paper_dir=self.fixture.paper_dir,
                prior_raw_audit=self.fixture.prior_raw,
                current_raw_audit=self.fixture.current_raw,
                prior_sidecar=self.fixture.prior_sidecar,
                prior_raw_audit_path=self.fixture.prior_raw_path,
                current_raw_audit_path=self.fixture.current_raw_path,
                prior_sidecar_path=self.fixture.prior_sidecar_path,
                prior_statement_map=self.fixture.prior_map,
                current_statement_map=self.fixture.current_map,
                prior_statement_map_path=self.fixture.prior_map_path,
                current_statement_map_path=self.fixture.current_map_path,
                prior_judgment_keys=[self.fixture.prior_key],
                prior_association_snapshot_reconciliation_path=reconciliation_path,
            )

    def test_reconciliation_rebinds_renamed_witness_storage_keys_by_full_digest(self) -> None:
        """A loaded reconciliation makes the full map-item digest the selector."""

        items = self.fixture.prior_map["items"]
        assert isinstance(items, dict)
        source_item = items.pop("source-address")
        items["renamed-witness-storage-address"] = source_item
        self.fixture.prior_map["paper"] = PAPER
        _write(self.fixture.prior_map_path, self.fixture.prior_map)
        # Preserve the archived raw's original source key and deliberately bad
        # top-level map receipt. The reconciliation itself proves the witness
        # item through its complete digest, not through either storage key.
        self.fixture.prior_raw["paper_statement_map_sha256"] = "f" * 64
        self.fixture._restamp_raw(current=False)
        reconciliation_path = (
            self.fixture.audit_dir
            / RECONCILIATION.SOURCE_RECORD_HISTORICAL_ASSOCIATION_SNAPSHOT_RECONCILIATION_FILENAME
        )
        RECONCILIATION.write_historical_association_snapshot_reconciliation(
            paper_dir=self.fixture.paper_dir,
            paper=PAPER,
            raw_audit_path=self.fixture.prior_raw_path,
            witness_map_path=self.fixture.prior_map_path,
            output_path=reconciliation_path,
        )
        artifact = REBIND.build_source_record_scoped_receipt_rebind(
            paper=PAPER,
            paper_dir=self.fixture.paper_dir,
            prior_raw_audit=self.fixture.prior_raw,
            current_raw_audit=self.fixture.current_raw,
            prior_sidecar=self.fixture.prior_sidecar,
            prior_raw_audit_path=self.fixture.prior_raw_path,
            current_raw_audit_path=self.fixture.current_raw_path,
            prior_sidecar_path=self.fixture.prior_sidecar_path,
            prior_statement_map=None,
            current_statement_map=self.fixture.current_map,
            prior_statement_map_path=None,
            current_statement_map_path=self.fixture.current_map_path,
            prior_judgment_keys=[self.fixture.prior_key],
            prior_association_snapshot_reconciliation_path=reconciliation_path,
        )
        self.fixture.write_overlay(artifact)
        loaded = REBIND.load_current_source_record_scoped_receipt_rebind_items(
            self.fixture.paper_dir, PAPER, self.fixture.current_raw
        )
        self.assertIn(self.fixture.current_key, loaded)

        # A duplicate full witness record is ambiguous. The reconciliation
        # cannot be rebuilt, and the existing artifact rejects the changed
        # witness bytes before any item can be selected.
        items["ambiguous-witness-storage-address"] = copy.deepcopy(source_item)
        _write(self.fixture.prior_map_path, self.fixture.prior_map)
        with self.assertRaisesRegex(
            RECONCILIATION.SourceRecordHistoricalAssociationSnapshotReconciliationError,
            "multiple witness items",
        ):
            RECONCILIATION.write_historical_association_snapshot_reconciliation(
                paper_dir=self.fixture.paper_dir,
                paper=PAPER,
                raw_audit_path=self.fixture.prior_raw_path,
                witness_map_path=self.fixture.prior_map_path,
                output_path=self.fixture.audit_dir / "ambiguous_reconciliation.json",
            )
        self.assertTrue(
            REBIND.source_record_scoped_receipt_rebind_overlay_error(
                artifact, paper=PAPER, paper_dir=self.fixture.paper_dir
            )
        )
        self.assertEqual(
            REBIND.load_current_source_record_scoped_receipt_rebind_items(
                self.fixture.paper_dir, PAPER, self.fixture.current_raw
            ),
            {},
        )

    def test_exact_archived_map_does_not_gain_digest_lookup_fallback(self) -> None:
        """Only the replayed reconciliation may ignore a changed map key."""

        items = self.fixture.prior_map["items"]
        assert isinstance(items, dict)
        items["renamed-exact-map-address"] = items.pop("source-address")
        self.fixture.sync_map(current=False)
        with self.assertRaisesRegex(
            REBIND.SourceRecordScopedReceiptRebindError,
            "source identity is absent from the statement map",
        ):
            self.fixture.build()

    def test_fqn_and_storage_address_rename_succeeds_when_descriptor_is_exact(self) -> None:
        row = self.fixture.current_row()
        row["judgment_key"] = "current-renamed-storage-key"
        self.fixture.current_key = "current-renamed-storage-key"
        for field in (
            "lean_source_declaration",
            "effective_lean_source_declaration",
            "qualified_declaration",
            "effective_qualified_declaration",
        ):
            row[field] = "Fixture.Renamed.evidence"
        identity = row["reviewed_declaration_identity"]
        signatures = row["reviewed_elaborated_signature_identities"]
        association = row["source_contract_association"]
        assert isinstance(identity, dict) and isinstance(signatures, list)
        assert isinstance(signatures[0], dict) and isinstance(association, dict)
        identity["qualified_declaration"] = "Fixture.Renamed.evidence"
        signatures[0]["qualified_declaration"] = "Fixture.Renamed.evidence"
        association_identity = association["reviewed_declaration_identity"]
        association_signature = association["reviewed_elaborated_signature_identity"]
        assert isinstance(association_identity, dict) and isinstance(association_signature, dict)
        association_identity["qualified_declaration"] = "Fixture.Renamed.evidence"
        association_signature["qualified_declaration"] = "Fixture.Renamed.evidence"
        # Map keys are storage addresses too.  The map content and source
        # semantic SHA remain unchanged while the association validates locally.
        items = self.fixture.current_map["items"]
        assert isinstance(items, dict)
        source = items.pop("source-address")
        items["renamed-source-address"] = source
        source_identities = association["source_item_identities"]
        assert isinstance(source_identities, list) and isinstance(source_identities[0], dict)
        source_identities[0]["source_key"] = "renamed-source-address"
        self.fixture.refresh_current_association()
        self.fixture.sync_map(current=True)
        artifact = self.fixture.build()
        items = artifact["items"]
        assert isinstance(items, dict)
        metadata = items[self.fixture.prior_key]
        assert isinstance(metadata, dict)
        self.assertEqual(metadata["current_judgment_key"], "current-renamed-storage-key")

    def test_serialized_marker_is_not_a_loader_capability(self) -> None:
        forged = {
            "classification": "validated_source_assumption",
            REBIND.SOURCE_RECORD_SCOPED_RECEIPT_REBIND_ITEM_FIELD: {
                "schema": REBIND.SOURCE_RECORD_SCOPED_RECEIPT_REBIND_SCHEMA
            },
        }
        self.assertTrue(REBIND.source_record_scoped_receipt_rebind_item_has_provenance(forged))
        self.assertFalse(REBIND.is_loaded_source_record_scoped_receipt_rebind_item(forged))

    def test_authenticated_receipt_reaches_all_current_consumers(self) -> None:
        """The loader token, not a JSON field, admits this narrow exception."""

        self.fixture.current_raw[FORMALIZATION_COVERAGE_PROTOCOL_FIELD] = (
            formalization_coverage_protocol_digest()
        )
        self.fixture._restamp_raw(current=True)
        self.fixture.write_overlay(self.fixture.build())
        _write(
            self.fixture.audit_dir / "source_record_match_llm.json",
            {"schema": 1, "paper": PAPER, "items": {}},
        )
        loaded = REBIND.load_current_source_record_scoped_receipt_rebind_items(
            self.fixture.paper_dir, PAPER, self.fixture.current_raw
        )
        response = loaded[self.fixture.current_key]

        # The fixture is intentionally minimal.  Its scoped-rebind loader has
        # already replayed both raw audits and maps; bypass only the unrelated
        # full-generator identity metadata required by the broad evidence gate.
        with patch.object(EVIDENCE, "source_record_audit_identity_error", return_value=""):
            evidence = EVIDENCE.current_source_record_judgment_items(
                self.fixture.current_raw,
                {"schema": 1, "paper": PAPER, "items": {}},
                folder=self.fixture.paper_dir,
            )
        self.assertIn(self.fixture.current_key, evidence)
        self.assertTrue(
            REBIND.is_loaded_source_record_scoped_receipt_rebind_item(
                evidence[self.fixture.current_key]
            )
        )

        previous_papers = PROVENANCE.PAPERS
        PROVENANCE.PAPERS = self.fixture.paper_dir.parent
        self.addCleanup(setattr, PROVENANCE, "PAPERS", previous_papers)
        conclusions = PROVENANCE.current_judgments(PAPER, self.fixture.current_raw)
        self.assertIn(self.fixture.current_key, conclusions)
        self.assertTrue(
            REBIND.is_loaded_source_record_scoped_receipt_rebind_item(
                conclusions[self.fixture.current_key]
            )
        )

        # The generator owns the persisted raw-audit judgment summary, so it
        # must consume the same authenticated output rather than reporting a
        # different current count or dependency partition from the gates.
        generator = REBIND._load_source_record_audit_helper()
        summary_judgments = generator.current_source_record_judgments(
            self.fixture.paper_dir, PAPER, self.fixture.current_raw
        )
        self.assertIn(self.fixture.current_key, summary_judgments)
        self.assertTrue(
            REBIND.is_loaded_source_record_scoped_receipt_rebind_item(
                summary_judgments[self.fixture.current_key]
            )
        )

        # Deserializing the same response loses the private loader capability;
        # both parsers must reject it even when their exception flag is set.
        forged_payload = {"schema": 1, "paper": PAPER, "items": {
            self.fixture.current_key: dict(response)
        }}
        with patch.object(EVIDENCE, "source_record_audit_identity_error", return_value=""):
            self.assertEqual(
                EVIDENCE._current_source_record_judgment_items_from_payload(
                    self.fixture.current_raw,
                    forged_payload,
                    folder=self.fixture.paper_dir,
                    allow_scoped_receipt_rebind=True,
                ),
                {},
            )
        self.assertEqual(
            PROVENANCE._current_judgments_from_payload(
                PAPER,
                self.fixture.current_raw,
                forged_payload,
                paper_dir=self.fixture.paper_dir,
                allow_scoped_receipt_rebind=True,
            ),
            {},
        )
        self.assertEqual(
            generator.current_source_record_judgments_from_payload(
                forged_payload,
                PAPER,
                self.fixture.current_raw,
                paper_dir=self.fixture.paper_dir,
                allow_scoped_receipt_rebind=True,
            ),
            {},
        )

    def test_output_protection_rejects_ordinary_artifacts_and_aliases(self) -> None:
        canonical = REBIND.source_record_scoped_receipt_rebind_overlay_path(
            self.fixture.paper_dir
        )
        self.assertEqual(
            REBIND.source_record_scoped_receipt_rebind_output_error(
                canonical, paper_dir=self.fixture.paper_dir
            ),
            "",
        )
        for path in (
            self.fixture.audit_dir / "source_record_match_llm.json",
            self.fixture.audit_dir / "source_record_audit.json",
            self.fixture.audit_dir / "paper_statement_map.json",
            self.fixture.paper_dir / "audit" / ".." / "audit" / REBIND.SOURCE_RECORD_SCOPED_RECEIPT_REBIND_FILENAME,
        ):
            self.assertTrue(
                REBIND.source_record_scoped_receipt_rebind_output_error(
                    path, paper_dir=self.fixture.paper_dir
                )
            )
        alias_dir = self.fixture.audit_dir / "output-alias"
        alias_dir.symlink_to(self.fixture.audit_dir, target_is_directory=True)
        self.assertTrue(
            REBIND.source_record_scoped_receipt_rebind_output_error(
                alias_dir / REBIND.SOURCE_RECORD_SCOPED_RECEIPT_REBIND_FILENAME,
                paper_dir=self.fixture.paper_dir,
            )
        )


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
