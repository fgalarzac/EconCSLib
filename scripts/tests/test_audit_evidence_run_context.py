#!/usr/bin/env python3
"""Tests for run-scoped evidence reuse and exact mutation detection."""

from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path
from unittest import mock

from scripts import audit_evidence_integrity as evidence
from scripts import audit_repository
from scripts import source_record_component_projection as component_projection
from scripts import source_record_schema4_to5_migration as schema_migration
from scripts.configured_assumption_formalization_regularities import (
    CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_STATUS_FIELD,
)


class EvidenceRunContextTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.paper = self.root / "papers" / "Fixture"
        self.audit_dir = self.paper / "audit"
        self.audit_dir.mkdir(parents=True)
        self._write_json(self.paper / "status.json", {"status": "formalized"})
        self._write_json(
            self.audit_dir / "source_record_audit.json",
            {
                "paper": "Fixture",
                "prompt_version": evidence.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION,
                "source_record_audit_sha256": "a" * 64,
                "nested": {"rows": ["content-addressed-obligation"]},
            },
        )
        self._write_json(
            self.audit_dir / "source_record_match_llm.json", {"items": {}}
        )
        self._write_json(
            self.audit_dir / "paper_statement_map.json", {"items": {}}
        )

    @staticmethod
    def _write_json(path: Path, payload: object) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(payload) + "\n", encoding="utf-8")

    def _build_context(
        self,
        diagnostics: dict[str, int] | None = None,
        *,
        identity_error: str = "",
    ) -> tuple[evidence.EvidenceRunContext, tuple[mock.Mock, ...]]:
        identity = mock.Mock(return_value=identity_error)
        corrected = mock.Mock(return_value=[])
        judgments = mock.Mock(
            return_value={
                "content-addressed-obligation": {
                    "classification": "paper_matches",
                }
            }
        )
        watch = mock.Mock(return_value="stable-watch")
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence,
                "_source_record_current_input_fingerprint_error",
                return_value="",
            ),
            mock.patch.object(
                evidence, "_source_record_audit_identity_error", identity
            ),
            mock.patch.object(
                evidence, "_corrected_model_scope_contract_findings", corrected
            ),
            mock.patch.object(
                evidence, "_current_source_record_judgment_items", judgments
            ),
            mock.patch.object(
                evidence, "_source_record_identity_process_watch_digest", watch
            ),
        ):
            context = evidence.build_evidence_run_context(
                self.paper, diagnostics=diagnostics
            )
        return context, (identity, corrected, judgments, watch)

    def _write_strict_receipt_only_source_record(self) -> None:
        """Create one required key omitted from the ordinary sidecar snapshot."""

        self._write_json(
            self.audit_dir / "source_record_audit.json",
            {
                "paper": "Fixture",
                "prompt_version": (
                    evidence.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
                ),
                "source_record_audit_sha256": "a" * 64,
                "expected_field_judgment_keys": ["strict-receipt-only"],
            },
        )

    def _write_current_source_record_with_map_pin(self) -> None:
        """Make the fixture sufficient for the optional structural replay."""

        map_bytes = (self.audit_dir / "paper_statement_map.json").read_bytes()
        self._write_json(
            self.audit_dir / "source_record_audit.json",
            {
                "paper": "Fixture",
                "prompt_version": (
                    evidence.CORRECTED_MODEL_SOURCE_RECORD_PROMPT_VERSION
                ),
                "source_record_audit_sha256": "a" * 64,
                "source_record_audit_integrity_sha256": "b" * 64,
                "paper_statement_map_sha256": hashlib.sha256(map_bytes).hexdigest(),
            },
        )

    def _write_component_projection_envelope(
        self,
        *,
        base_path: str = "audit/opaque-component-base.json",
        valid_receipt: bool = True,
    ) -> Path:
        body: dict[str, object] = {
            "schema": component_projection.SOURCE_RECORD_COMPONENT_PROJECTION_SCHEMA,
            "artifact_kind": (
                component_projection.SOURCE_RECORD_COMPONENT_PROJECTION_ARTIFACT_KIND
            ),
            "policy_version": (
                component_projection.SOURCE_RECORD_COMPONENT_PROJECTION_POLICY_VERSION
            ),
            "paper": "Fixture",
            "base_judgment_sidecar_path": base_path,
            "component_projections": [],
        }
        body[component_projection.SOURCE_RECORD_COMPONENT_PROJECTION_RECEIPT_FIELD] = (
            component_projection._canonical_digest(body)
            if valid_receipt
            else "0" * 64
        )
        path = component_projection.component_projection_artifact_path(self.paper)
        self._write_json(path, body)
        return path

    def test_one_materialization_per_unchanged_transaction(self) -> None:
        diagnostics: dict[str, int] = {}
        context, calls = self._build_context(diagnostics)
        identity, corrected, judgments, watch = calls

        identity.assert_called_once()
        corrected.assert_called_once()
        judgments.assert_called_once()
        watch.assert_called_once()
        self.assertEqual(
            diagnostics,
            {
                evidence.EVIDENCE_DIAGNOSTIC_CONTEXTS: 1,
                evidence.EVIDENCE_DIAGNOSTIC_WATCH_DIGESTS: 1,
                evidence.EVIDENCE_DIAGNOSTIC_IDENTITY_VALIDATIONS: 1,
                evidence.EVIDENCE_DIAGNOSTIC_CORRECTED_SCOPE: 1,
                evidence.EVIDENCE_DIAGNOSTIC_CURRENT_JUDGMENTS: 1,
            },
        )
        self.assertEqual(
            set(context.current_source_record_judgments),
            {"content-addressed-obligation"},
        )

    def test_builder_issues_one_identity_context_for_nested_current_lanes(self) -> None:
        """The strict fingerprint gate is not replayed for each overlay lane."""

        self._write_current_source_record_with_map_pin()
        context, calls = self._build_context()
        identity, _corrected, judgments, _watch = calls
        self.assertIsNotNone(context.source_record_identity_context)
        self.assertFalse(isinstance(context.source_record_identity_context, dict))
        identity.assert_called_once()
        self.assertIs(
            judgments.call_args.kwargs["source_record_identity_context"],
            context.source_record_identity_context,
        )

    def test_stale_identity_skips_all_unusable_derived_materialization(self) -> None:
        diagnostics: dict[str, int] = {}
        identity_error = "source-record input fingerprint is stale"
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence,
                "_source_record_current_input_fingerprint_error",
                return_value=identity_error,
            ),
            mock.patch.object(
                evidence,
                "_source_record_audit_identity_error",
                return_value=identity_error,
            ),
            mock.patch.object(
                evidence,
                "_corrected_model_scope_contract_findings",
            ) as corrected_scope,
            mock.patch.object(
                evidence,
                "load_configured_assumption_formalization_regularity_context",
            ) as regularity,
            mock.patch.object(
                evidence,
                "source_record_administrative_projection_rebind_context",
            ) as administrative_rebind,
            mock.patch.object(
                evidence,
                "_current_source_record_judgment_items",
            ) as judgments,
            mock.patch.object(
                evidence,
                "_source_record_identity_process_watch_digest",
                return_value="stable-watch",
            ),
        ):
            context = evidence.build_evidence_run_context(
                self.paper, diagnostics=diagnostics
            )

        self.assertEqual(context.source_record_identity_error, identity_error)
        self.assertFalse(context.corrected_scope_current)
        self.assertEqual(context.current_source_record_judgments, {})
        regularity.assert_not_called()
        administrative_rebind.assert_not_called()
        judgments.assert_not_called()
        corrected_scope.assert_not_called()
        self.assertNotIn(
            evidence.EVIDENCE_DIAGNOSTIC_CORRECTED_SCOPE,
            diagnostics,
        )
        self.assertNotIn(
            evidence.EVIDENCE_DIAGNOSTIC_CURRENT_JUDGMENTS,
            diagnostics,
        )

    def test_absent_semantic_contract_replay_still_runs_fingerprint(self) -> None:
        """An absent optional replay is not a reason to skip currentness work."""

        self._write_current_source_record_with_map_pin()
        fingerprint = mock.Mock(return_value="")
        watch = mock.Mock(return_value="stable-watch")
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence,
                "_source_record_current_input_fingerprint_error",
                fingerprint,
            ),
            mock.patch.object(
                evidence,
                "_source_record_identity_process_watch_digest",
                watch,
            ),
            mock.patch.object(
                evidence, "_source_record_audit_identity_error", return_value=""
            ),
            mock.patch.object(
                evidence, "_corrected_model_scope_contract_findings", return_value=[]
            ),
            mock.patch.object(
                evidence, "_current_source_record_judgment_items", return_value={}
            ),
        ):
            context = evidence.build_evidence_run_context(self.paper)

        self.assertEqual(context.semantic_contract_revalidation_error, "")
        fingerprint.assert_called_once()
        watch.assert_called_once()

    def test_malformed_semantic_contract_replay_skips_fingerprint(self) -> None:
        """A present invalid replay fails before the costly identity subprocess."""

        self._write_current_source_record_with_map_pin()
        artifact = self.audit_dir / "source_record_semantic_contract_revalidation.json"
        self._write_json(artifact, {"malformed": True})
        fingerprint = mock.Mock(return_value="")
        watch = mock.Mock(return_value="stable-watch")
        identity = mock.Mock(return_value="semantic replay rejected")
        with (
            mock.patch.object(evidence, "ROOT", self.root),
            mock.patch.object(
                evidence,
                "_source_record_current_input_fingerprint_error",
                fingerprint,
            ),
            mock.patch.object(
                evidence,
                "_source_record_identity_process_watch_digest",
                watch,
            ),
            mock.patch.object(evidence, "_source_record_audit_identity_error", identity),
        ):
            context = evidence.build_evidence_run_context(self.paper)

        self.assertIn(
            "semantic-contract revalidation artifact has unsupported fields",
            context.semantic_contract_revalidation_error,
        )
        fingerprint.assert_not_called()
        watch.assert_not_called()
        self.assertEqual(
            identity.call_args.kwargs[
                "prevalidated_semantic_contract_revalidation_error"
            ],
            context.semantic_contract_revalidation_error,
        )

    def test_exact_input_change_fails_closed(self) -> None:
        diagnostics: dict[str, int] = {}
        context, _calls = self._build_context(diagnostics)
        self._write_json(
            self.audit_dir / "source_record_match_llm.json",
            {"items": {"changed": {}}},
        )

        with mock.patch.object(
            evidence,
            "_source_record_identity_process_watch_digest",
            return_value="stable-watch",
        ):
            findings = evidence.evidence_run_context_mutation_findings(
                context, diagnostics=diagnostics
            )

        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].severity, "ERROR")
        self.assertIn("exact inputs changed", findings[0].message)
        self.assertEqual(
            diagnostics[evidence.EVIDENCE_DIAGNOSTIC_INPUT_MUTATIONS], 1
        )

    def test_non_json_evidence_controls_use_the_frozen_bytes(self) -> None:
        assumptions = self.paper / "Assumptions.lean"
        assumptions.write_text(
            "axiom substantive_boundary : Prop\n", encoding="utf-8"
        )
        context, _calls = self._build_context()
        snapshot = context.json_snapshot(assumptions)
        self.assertIsNotNone(snapshot)
        assert snapshot is not None

        assumptions.write_text(
            "def transient_boundary : Prop := True\n", encoding="utf-8"
        )
        frozen_findings = evidence.check_vacuous_assumptions(
            self.paper,
            "formalized",
            source_bytes_override=snapshot.raw_bytes,
        )
        live_findings = evidence.check_vacuous_assumptions(
            self.paper,
            "formalized",
        )

        self.assertEqual(frozen_findings, [])
        self.assertEqual(len(live_findings), 1)
        self.assertIn("transient_boundary", live_findings[0].message)

    def test_configured_noncanonical_sidecar_is_frozen_and_watched(self) -> None:
        configured = self.audit_dir / "alternate" / "statement-review.json"
        configured_payload = {"items": {"opaque-row": {"judgment": "passes"}}}
        self._write_json(configured, configured_payload)
        self._write_json(
            self.paper / "status.json",
            {
                "status": "formalized",
                "review_surface": {
                    "llm_statement_review": {
                        "match_judgment_file": (
                            "papers/Fixture/audit/alternate/statement-review.json"
                        )
                    }
                },
            },
        )

        context, _calls = self._build_context()

        self.assertEqual(context.json_payload(configured), configured_payload)
        self._write_json(configured, {"items": {"replacement": {}}})
        with mock.patch.object(
            evidence,
            "_source_record_identity_process_watch_digest",
            return_value="stable-watch",
        ):
            findings = evidence.evidence_run_context_mutation_findings(context)

        self.assertEqual(len(findings), 1)
        self.assertIn("statement-review.json", findings[0].message)

    def test_default_administrative_rebind_creation_is_watched(self) -> None:
        rebind = (
            self.audit_dir
            / evidence.SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME
        )
        context, _calls = self._build_context()

        self._write_json(rebind, {"schema": "created-after-context"})
        with mock.patch.object(
            evidence,
            "_source_record_identity_process_watch_digest",
            return_value="stable-watch",
        ):
            findings = evidence.evidence_run_context_mutation_findings(context)

        self.assertEqual(len(findings), 1)
        self.assertIn(rebind.name, findings[0].message)

    def test_component_projection_declared_base_is_frozen_and_watched(self) -> None:
        base = self.audit_dir / "opaque-component-base.json"
        base_payload = {"items": {"content-addressed-parent": {}}}
        self._write_json(base, base_payload)
        receipt = self._write_component_projection_envelope()

        context, _calls = self._build_context()
        self.assertEqual(context.json_payload(receipt), json.loads(receipt.read_text()))
        self.assertEqual(context.json_payload(base), base_payload)

        self._write_json(base, {"items": {"changed-parent": {}}})
        with mock.patch.object(
            evidence,
            "_source_record_identity_process_watch_digest",
            return_value="stable-watch",
        ):
            findings = evidence.evidence_run_context_mutation_findings(context)

        self.assertEqual(len(findings), 1)
        self.assertIn(base.name, findings[0].message)

    def test_component_projection_receipt_absence_is_frozen(self) -> None:
        receipt = component_projection.component_projection_artifact_path(self.paper)
        context, _calls = self._build_context()
        snapshot = context.json_snapshot(receipt)
        self.assertIsNotNone(snapshot)
        assert snapshot is not None
        self.assertIsNone(snapshot.raw_bytes)

        self._write_component_projection_envelope()
        with mock.patch.object(
            evidence,
            "_source_record_identity_process_watch_digest",
            return_value="stable-watch",
        ):
            findings = evidence.evidence_run_context_mutation_findings(context)

        self.assertEqual(len(findings), 1)
        self.assertIn(receipt.name, findings[0].message)

    def test_malformed_component_projection_envelope_does_not_expand_inputs(self) -> None:
        base = self.audit_dir / "opaque-component-base.json"
        self._write_json(base, {"must_not_be_followed": True})
        self._write_component_projection_envelope(valid_receipt=False)

        context, _calls = self._build_context()
        self.assertIsNone(context.json_snapshot(base))

    def test_semantic_rebind_authority_is_frozen_and_watched(self) -> None:
        rebind = self.audit_dir / "source_record_semantic_rebind.json"
        self._write_json(rebind, {"schema": "initial-semantic-rebind"})
        context, _calls = self._build_context()
        snapshot = context.json_snapshot(rebind)
        self.assertIsNotNone(snapshot)
        assert snapshot is not None
        self.assertEqual(snapshot.raw_bytes, rebind.read_bytes())

        self._write_json(rebind, {"schema": "changed-semantic-rebind"})
        with mock.patch.object(
            evidence,
            "_source_record_identity_process_watch_digest",
            return_value="stable-watch",
        ):
            findings = evidence.evidence_run_context_mutation_findings(context)

        self.assertEqual(len(findings), 1)
        self.assertIn(rebind.name, findings[0].message)

    def test_semantic_rebind_declared_provenance_graph_is_frozen_and_watched(self) -> None:
        """The indirect source-record authority cannot reread a mutable parent.

        The test deliberately uses opaque filenames and a nested ``bytes_sha256``
        record.  Discovery is therefore through the typed byte-pinned graph,
        not through a sidecar basename or a judgment/function name.
        """

        root = self.audit_dir / "source_record_semantic_rebind.json"
        parent = self.audit_dir / "opaque-parent.json"
        leaf = self.audit_dir / "opaque-leaf.json"
        self._write_json(leaf, {"immutable": "leaf"})
        leaf_digest = hashlib.sha256(leaf.read_bytes()).hexdigest()
        self._write_json(
            parent,
            {
                "nested_provenance": {
                    "path": "audit/opaque-leaf.json",
                    "bytes_sha256": leaf_digest,
                }
            },
        )
        parent_digest = hashlib.sha256(parent.read_bytes()).hexdigest()
        self._write_json(
            root,
            {
                "prior_raw_audit": {
                    "path": "audit/opaque-parent.json",
                    "file_sha256": parent_digest,
                }
            },
        )

        context, _calls = self._build_context()
        self.assertIsNotNone(context.json_snapshot(root))
        self.assertIsNotNone(context.json_snapshot(parent))
        self.assertIsNotNone(context.json_snapshot(leaf))

        self._write_json(leaf, {"immutable": "changed"})
        with mock.patch.object(
            evidence,
            "_source_record_identity_process_watch_digest",
            return_value="stable-watch",
        ):
            findings = evidence.evidence_run_context_mutation_findings(context)

        self.assertEqual(len(findings), 1)
        self.assertIn(leaf.name, findings[0].message)

    def test_administrative_rebind_validator_receives_exact_snapshot_bytes(
        self,
    ) -> None:
        rebind = (
            self.audit_dir
            / evidence.SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME
        )
        self._write_json(rebind, {"schema": "exact-receipt"})

        with mock.patch.object(
            evidence,
            "load_administrative_projection_rebind_context",
            return_value=(None, rebind, ""),
        ) as loader:
            self._build_context()

        kwargs = loader.call_args.kwargs
        self.assertEqual(kwargs["receipt_bytes_override"], rebind.read_bytes())
        self.assertEqual(
            kwargs["raw_audit_bytes_override"],
            (self.audit_dir / "source_record_audit.json").read_bytes(),
        )
        self.assertEqual(
            kwargs["statement_map_bytes_override"],
            (self.audit_dir / "paper_statement_map.json").read_bytes(),
        )

    def test_regularity_validator_receives_exact_snapshot_inputs(self) -> None:
        regularity = (
            self.paper
            / evidence.CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_FILE
        )
        self._write_json(regularity, {"schema": "exact-regularity"})
        source = self.paper / "source.txt"
        source.write_text("source bytes\n", encoding="utf-8")
        self._write_json(
            self.paper / "status.json",
            {
                "status": "formalized",
                CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_STATUS_FIELD: (
                    evidence.CONFIGURED_ASSUMPTION_FORMALIZATION_REGULARITIES_FILE
                ),
            },
        )

        with mock.patch.object(
            evidence,
            "load_configured_assumption_formalization_regularity_context",
            return_value=(None, ""),
        ) as loader:
            self._build_context()

        kwargs = loader.call_args.kwargs
        self.assertEqual(kwargs["ledger_bytes_override"], regularity.read_bytes())
        self.assertEqual(
            kwargs["source_artifact_sha256_override"],
            hashlib.sha256(source.read_bytes()).hexdigest(),
        )

    def test_corrected_scope_reference_artifacts_are_acquired_by_builder(self) -> None:
        approval = self.paper / "docs" / "approval.md"
        archive = self.paper / "source.txt"
        contract = self.audit_dir / "corrected.json"
        approval.parent.mkdir(parents=True)
        approval.write_bytes(b"approved\n")
        archive.write_bytes(b"archived source\n")
        self._write_json(contract, {"schema": "fixture"})
        self._write_json(
            self.paper / "status.json",
            {
                "status": "formalized",
                "formalization_scope": {
                    "kind": evidence.AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE,
                    "approval": {"artifact_path": "docs/approval.md"},
                    "base_archive": {"path": "source.txt"},
                    "semantic_contract": {"path": "audit/corrected.json"},
                },
            },
        )

        context, _calls = self._build_context()

        for path in (approval, archive, contract):
            captured = context.json_snapshot(path)
            self.assertIsNotNone(captured)
            assert captured is not None
            self.assertEqual(captured.raw_bytes, path.read_bytes())

    def test_corrected_scope_validator_uses_frozen_artifact_receipts(self) -> None:
        approval_path = (self.paper / "docs" / "approval.md").resolve()
        archive_path = (self.paper / "source.txt").resolve()
        contract_path = (self.audit_dir / "corrected.json").resolve()
        approval_sha = "1" * 64
        archive_sha = "2" * 64
        contract_sha = "3" * 64
        status = {
            "status": "formalized",
            "formalization_scope": {
                "kind": evidence.AUTHOR_APPROVED_CORRECTED_MODEL_SCOPE,
                "scope_id": "opaque-scope",
                "scope_role": evidence.WHOLE_PAPER_CLOSEOUT_SCOPE_ROLE,
                "whole_paper_closeout_claimed": True,
                "archival_equivalence_claimed": False,
                "target_result_declarations": ["Fixture.result"],
                "model_spec_declarations": ["Fixture.Model"],
                "correction_ids": ["opaque-correction"],
                "approval": {
                    "artifact_path": "docs/approval.md",
                    "artifact_sha256": approval_sha,
                    "recorded_at": "2026-08-02",
                    "statement": "approved corrected target",
                },
                "base_archive": {
                    "path": "source.txt",
                    "sha256": archive_sha,
                },
                "semantic_contract": {
                    "path": "audit/corrected.json",
                    "sha256": contract_sha,
                },
            },
            "governing_corrections": [
                {
                    "id": "opaque-correction",
                    "clause": "corrected clause",
                    "source_anchor": "source.txt:1-1",
                    "relation": "source correction",
                    "model_evidence": "Fixture.result",
                    "does_not_claim_archive_derivation": True,
                }
            ],
        }
        snapshots = {
            approval_path: evidence.EvidenceJSONSnapshot(
                approval_path, approval_sha, None
            ),
            archive_path: evidence.EvidenceJSONSnapshot(
                archive_path, archive_sha, None
            ),
            contract_path: evidence.EvidenceJSONSnapshot(
                contract_path, contract_sha, {"schema": "unsupported"}
            ),
        }

        with (
            mock.patch.object(
                evidence,
                "load_json",
                side_effect=AssertionError("frozen artifact must not be reread"),
            ),
            mock.patch.object(
                evidence,
                "sha256_file",
                side_effect=AssertionError("frozen artifact must not be rehashed"),
            ),
        ):
            findings = evidence._corrected_model_scope_contract_findings(
                self.paper,
                "formalized",
                status,
                audit_payload_override={},
                prevalidated_source_record_identity_error="stale fixture audit",
                artifact_snapshots_override=snapshots,
            )

        messages = [finding.message for finding in findings]
        self.assertFalse(any("artifact_path must name" in item for item in messages))
        self.assertFalse(any("base_archive.path must name" in item for item in messages))
        self.assertFalse(any("does not match its tracked artifact" in item for item in messages))
        self.assertTrue(any("unsupported schema" in item for item in messages))

    def test_watched_producer_change_fails_closed(self) -> None:
        context, _calls = self._build_context()
        with mock.patch.object(
            evidence,
            "_source_record_identity_process_watch_digest",
            return_value="changed-watch",
        ):
            findings = evidence.evidence_run_context_mutation_findings(context)

        self.assertEqual(len(findings), 1)
        self.assertIn("producer/source watch digest changed", findings[0].message)

    def test_watch_ignores_scratch_but_tracks_fingerprint_inputs(self) -> None:
        interface = self.paper / "PaperInterface.lean"
        interface.write_text("theorem result : True := by trivial\n", encoding="utf-8")
        payload = {
            "source_record_input_fingerprint": {
                "review_interface_source": {
                    "path": "papers/Fixture/PaperInterface.lean",
                    "sha256": hashlib.sha256(interface.read_bytes()).hexdigest(),
                }
            }
        }
        with mock.patch.object(evidence, "ROOT", self.root):
            before = evidence._source_record_identity_process_watch_digest(
                self.paper, audit_payload=payload
            )
            scratch = self.paper / ".review_traces" / "interactive-cache.json"
            self._write_json(scratch, {"large": "non-authority"})
            archival = self.audit_dir / ".prior_raw_diagnostic.json"
            self._write_json(archival, {"large": "non-authority"})
            after_scratch = evidence._source_record_identity_process_watch_digest(
                self.paper, audit_payload=payload
            )
            interface.write_text(
                "theorem result : False := by contradiction\n",
                encoding="utf-8",
            )
            after_semantic_change = (
                evidence._source_record_identity_process_watch_digest(
                    self.paper, audit_payload=payload
                )
            )

        self.assertEqual(before, after_scratch)
        self.assertNotEqual(before, after_semantic_change)

    def test_context_payloads_are_recursively_immutable(self) -> None:
        context, _calls = self._build_context()
        assert context.audit_payload is not None
        with self.assertRaises(TypeError):
            context.audit_payload["paper"] = "Renamed"
        nested = context.audit_payload["nested"]
        assert isinstance(nested, dict)
        rows = nested["rows"]
        assert isinstance(rows, list)
        with self.assertRaises(TypeError):
            rows.append("forged-obligation")
        judgment = context.current_source_record_judgments[
            "content-addressed-obligation"
        ]
        with self.assertRaises(TypeError):
            judgment["classification"] = "forged-match"

    def test_final_mutation_check_hashes_bytes_without_reparsing_json(self) -> None:
        context, _calls = self._build_context()
        with (
            mock.patch.object(
                evidence.json,
                "loads",
                side_effect=AssertionError("final check must not parse JSON"),
            ),
            mock.patch.object(
                evidence,
                "_source_record_identity_process_watch_digest",
                return_value="stable-watch",
            ),
        ):
            findings = evidence.evidence_run_context_mutation_findings(context)

        self.assertEqual(findings, [])

    def test_freezing_current_judgments_preserves_loader_authentication(self) -> None:
        loaded = schema_migration._LoadedSourceRecordSchema4To5MigrationItem(
            {
                schema_migration.SOURCE_RECORD_SCHEMA4_TO5_MIGRATION_ITEM_FIELD: {
                    "receipt": "content-addressed"
                }
            }
        )
        frozen = evidence._freeze_json(
            {"obligation": loaded}, preserve_dict_subclasses=True
        )
        item = frozen["obligation"]

        self.assertTrue(
            schema_migration.is_loaded_source_record_schema4_to5_migration_item(
                item
            )
        )
        with self.assertRaises(TypeError):
            item["classification"] = "forged-match"

    def test_primary_closeout_receipt_skips_only_duplicate_missing_count(self) -> None:
        self._write_strict_receipt_only_source_record()
        context, _calls = self._build_context()

        before = evidence.check_source_record_judgments(
            self.paper, "formalized", context=context
        )
        self.assertEqual(len(before), 1)
        self.assertIn("lack current validated judgments", before[0].message)
        self.assertFalse(
            evidence._has_current_primary_closeout_source_record_judgment_receipt(
                context
            )
        )

        closeout = audit_repository.PaperCloseoutRunContext.from_exact_evidence_context(
            "Fixture", self.paper, evidence_context=context
        )
        # Publishing cannot be requested by a caller-provided Boolean or list;
        # it requires the primary source gate's no-argument staged capability.
        self.assertFalse(
            closeout.publish_staged_strict_v11_source_record_judgment_handoff()
        )
        closeout.stage_strict_v11_source_record_judgment_handoff()
        self.assertTrue(
            closeout.publish_staged_strict_v11_source_record_judgment_handoff()
        )
        self.assertTrue(
            evidence._has_current_primary_closeout_source_record_judgment_receipt(
                context
            )
        )

        self.assertEqual(
            evidence.check_source_record_judgments(
                self.paper, "formalized", context=context
            ),
            [],
        )

    def test_primary_closeout_receipt_remains_bound_to_its_issued_context(self) -> None:
        self._write_strict_receipt_only_source_record()
        context, _calls = self._build_context()
        other_context, _other_calls = self._build_context()
        closeout = audit_repository.PaperCloseoutRunContext.from_exact_evidence_context(
            "Fixture", self.paper, evidence_context=context
        )
        closeout.stage_strict_v11_source_record_judgment_handoff()
        self.assertTrue(
            closeout.publish_staged_strict_v11_source_record_judgment_handoff()
        )

        self.assertEqual(
            evidence.check_source_record_judgments(
                self.paper, "formalized", context=context
            ),
            [],
        )
        other = evidence.check_source_record_judgments(
            self.paper, "formalized", context=other_context
        )
        self.assertEqual(len(other), 1)
        self.assertIn("lack current validated judgments", other[0].message)

    def test_primary_closeout_receipt_does_not_suppress_raw_identity_error(self) -> None:
        self._write_strict_receipt_only_source_record()
        context, _calls = self._build_context(
            identity_error="source-record input fingerprint is stale"
        )
        closeout = audit_repository.PaperCloseoutRunContext.from_exact_evidence_context(
            "Fixture", self.paper, evidence_context=context
        )
        closeout.stage_strict_v11_source_record_judgment_handoff()
        self.assertTrue(
            closeout.publish_staged_strict_v11_source_record_judgment_handoff()
        )

        findings = evidence.check_source_record_judgments(
            self.paper, "formalized", context=context
        )
        self.assertEqual(len(findings), 1)
        self.assertIn("cannot support current judgments", findings[0].message)
        self.assertIn("fingerprint is stale", findings[0].message)

    def test_run_rejects_a_context_not_issued_by_the_builder(self) -> None:
        context, _calls = self._build_context()
        forged = replace(context, source_record_identity_error="")
        self.assertTrue(context.issued_by_builder)
        self.assertFalse(forged.issued_by_builder)
        with (
            mock.patch.object(evidence, "paper_dirs", return_value=[self.paper]),
            mock.patch.object(evidence, "check_report_generator", return_value=[]),
            mock.patch.object(evidence, "active_papers", return_value=set()),
            mock.patch.object(evidence, "lake_targets", return_value=(set(), set())),
        ):
            findings = evidence.run("Fixture", False, context=forged)

        self.assertEqual(len(findings), 1)
        self.assertIn("not issued", findings[0].message)


if __name__ == "__main__":
    unittest.main()
