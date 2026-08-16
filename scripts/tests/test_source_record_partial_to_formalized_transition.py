#!/usr/bin/env python3
"""Adversarial checks for the no-op partial-to-formalized reuse receipt."""

from __future__ import annotations

import copy
import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import audit_evidence_integrity as EVIDENCE  # noqa: E402
from scripts import source_record_partial_to_formalized_transition as TRANSITION  # noqa: E402
from scripts.source_record_integrity import stamp_source_record_audit_receipts  # noqa: E402


AUDIT_HELPER = (
    ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
)
AUDIT_SPEC = importlib.util.spec_from_file_location(
    "partial_to_formalized_cache_audit", AUDIT_HELPER
)
assert AUDIT_SPEC is not None and AUDIT_SPEC.loader is not None
AUDIT = importlib.util.module_from_spec(AUDIT_SPEC)
sys.modules[AUDIT_SPEC.name] = AUDIT
AUDIT_SPEC.loader.exec_module(AUDIT)


PAPER = "FixturePaper"
PROMPT = "source-record-v10-semantic-conclusion-boundary-contract"


class PartialToFormalizedTransitionTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.paper_dir = self.root / "papers" / PAPER
        self.audit_dir = self.paper_dir / "audit"
        self.audit_dir.mkdir(parents=True)
        self.status_path = self.paper_dir / "status.json"
        self.raw_path = self.audit_dir / "source_record_audit.json"
        self.receipt_path = (
            self.audit_dir
            / TRANSITION.SOURCE_RECORD_PARTIAL_TO_FORMALIZED_TRANSITION_BASENAME
        )
        self.prior_status = {
            "status": "partially formalized",
            "review_surface": {
                "source_file": f"papers/{PAPER}/PaperInterface.lean",
                "include_names": ["surface"],
            },
            "formalization_scope": {"kind": "fixture", "version": 1},
        }
        self._write_status(self.prior_status)
        self.raw = self._raw()
        self._write_raw(self.raw)
        self.current = copy.deepcopy(self.raw["source_record_input_fingerprint"])
        self.current["relevant_status_sha256"] = "b" * 64
        self.engine_identity = {
            "path": "fixture#partial-to-formalized-empty-precloseout",
            "surface_semantic_version": "fixture-v1",
        }

    def _write_status(self, payload: dict[str, object]) -> None:
        self.status_path.write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )

    def _raw(self) -> dict[str, object]:
        raw: dict[str, object] = {
            "paper": PAPER,
            "prompt_version": PROMPT,
            "source_record_policy_version": PROMPT,
            "paper_statement_map_sha256": "c" * 64,
            "source_record_input_fingerprint": {
                "schema": 7,
                "source_record_policy_version": PROMPT,
                "source_record_item_digest_schema": 5,
                "paper": PAPER,
                "relevant_status_sha256": "a" * 64,
                "review_interface_source": {
                    "path": f"papers/{PAPER}/PaperInterface.lean",
                    "sha256": "d" * 64,
                },
                "review_assumption_source": None,
                "paper_statement_map_semantic_sha256": "e" * 64,
                "source_proof_fidelity_sha256": "f" * 64,
                "lean_dependency_identities": [],
                "audit_engine_identities": [],
                "source_artifact_identities": [],
                "toolchain_identities": [],
                "max_depth": 4,
                "no_lean": False,
            },
            "precloseout_contract_covered_boundary_input_keys": [],
            "statement_ledger_covered_boundary_input_keys": [],
            "precloseout_exact_contract_projection": {
                "schema": 1,
                "status": "partially formalized",
                "paper_statement_map_sha256": "c" * 64,
                "items": [],
                "covered_boundary_input_keys": [],
                "covered_boundary_input_keys_sha256": TRANSITION._payload_sha256([]),
            },
            "lean_check": {"returncode": 0},
        }
        stamp_source_record_audit_receipts(raw)
        return raw

    def _write_raw(self, raw: dict[str, object]) -> None:
        self.raw_path.write_text(
            json.dumps(raw, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )

    def _prepare(self, current_direct_ledger_covered_keys: object = None) -> None:
        receipt, error = TRANSITION.build_source_record_partial_to_formalized_transition(
            paper=PAPER,
            raw_audit=self.raw,
            raw_relative_path="audit/source_record_audit.json",
            prior_status_payload=self.prior_status,
            current_input_fingerprint=self.raw["source_record_input_fingerprint"],
            transition_engine_identity=self.engine_identity,
            current_direct_ledger_covered_keys=current_direct_ledger_covered_keys,
        )
        self.assertEqual(error, "")
        assert receipt is not None
        self.receipt_path.write_text(
            json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )

    def _close_status(self) -> None:
        payload = copy.deepcopy(self.prior_status)
        payload["status"] = "formalized"
        self._write_status(payload)

    def _write_transition_engine(self, *identities: dict[str, str]) -> None:
        helper = (
            self.root
            / "skills"
            / "econcs-formalizer"
            / "scripts"
            / "source_record_audit.py"
        )
        helper.parent.mkdir(parents=True, exist_ok=True)
        helper.write_text(
            "\n".join(
                "PARTIAL_TO_FORMALIZED_STATUS_TRANSITION_ENGINE_IDENTITY = "
                + repr(identity)
                for identity in identities
            )
            + "\n",
            encoding="utf-8",
        )

    def _validate(
        self,
        current: dict[str, object] | None = None,
        current_direct_ledger_covered_keys: object = None,
    ) -> str:
        return TRANSITION.validate_source_record_partial_to_formalized_transition(
            paper=PAPER,
            root=self.root,
            paper_dir=self.paper_dir,
            raw_audit=self.raw,
            current_input_fingerprint=current or self.current,
            transition_engine_identity=self.engine_identity,
            current_direct_ledger_covered_keys=current_direct_ledger_covered_keys,
        )

    def _raw_with_saved_direct_ledger(self) -> tuple[dict[str, object], str]:
        raw = copy.deepcopy(self.raw)
        key = "surface.hypothesis : SourceCondition"
        raw["expected_input_judgment_keys"] = [key]
        raw["statement_ledger_covered_boundary_input_keys"] = [key]
        stamp_source_record_audit_receipts(raw)
        return raw, key

    def test_exact_status_flip_reuses_current_raw(self) -> None:
        self._prepare()
        self._close_status()
        self.assertEqual(self._validate(), "")

    def test_other_status_payload_edit_refuses(self) -> None:
        self._prepare()
        self._close_status()
        payload = json.loads(self.status_path.read_text(encoding="utf-8"))
        payload["review_surface"]["include_names"].append("other")
        self._write_status(payload)
        self.assertIn("exact prior payload", self._validate())

    def test_changed_generator_input_refuses(self) -> None:
        self._prepare()
        self._close_status()
        changed = copy.deepcopy(self.current)
        changed["source_proof_fidelity_sha256"] = "0" * 64
        self.assertIn("beyond the closeout status transition", self._validate(changed))

    def test_changed_status_transition_engine_refuses(self) -> None:
        self._prepare()
        self._close_status()
        changed_engine = dict(self.engine_identity)
        changed_engine["surface_semantic_version"] = "fixture-v2"
        self.assertIn(
            "engine identity changed",
            TRANSITION.validate_source_record_partial_to_formalized_transition(
                paper=PAPER,
                root=self.root,
                paper_dir=self.paper_dir,
                raw_audit=self.raw,
                current_input_fingerprint=self.current,
                transition_engine_identity=changed_engine,
            ),
        )

    def test_duplicate_transition_engine_identity_refuses(self) -> None:
        """The validator must not select an old identity from duplicate assignments."""

        self._prepare()
        self._close_status()
        self._write_transition_engine(
            self.engine_identity,
            {
                "path": "fixture#partial-to-formalized-v2",
                "surface_semantic_version": "fixture-v2",
            },
        )
        self.assertIn(
            "must appear exactly once",
            TRANSITION.validate_source_record_partial_to_formalized_transition(
                paper=PAPER,
                root=self.root,
                paper_dir=self.paper_dir,
                raw_audit=self.raw,
                current_input_fingerprint=self.current,
            ),
        )

    def test_cache_rejects_old_policy_receipt_then_accepts_reissue(self) -> None:
        """The aggregate cache consumes the same fail-closed transition receipt."""

        self._prepare()
        self._close_status()
        current_engine = {
            "path": "fixture#partial-to-formalized-maximal-input-surface",
            "surface_semantic_version": "fixture-v2",
        }
        self._write_transition_engine(current_engine)
        args = SimpleNamespace(
            paper=PAPER,
            force=False,
            refresh_judgment_summary=False,
            ignore_current_judgments=False,
            no_lean=False,
        )

        common_patches = (
            patch.object(
                AUDIT,
                "paper_statement_map_cache_receipts",
                return_value=("c" * 64, "e" * 64),
            ),
            patch.object(AUDIT, "source_record_input_fingerprint", return_value=self.current),
            patch.object(AUDIT, "source_record_raw_scan_completeness_error", return_value=""),
            patch.object(
                AUDIT,
                "source_record_raw_reusable_item_metadata_error",
                return_value="",
            ),
            patch.object(
                AUDIT,
                "source_record_raw_producer_code_identity_matches",
                return_value=True,
            ),
            patch.object(
                AUDIT,
                "configured_review_reference_static_error",
                return_value="",
            ),
        )
        with (
            common_patches[0],
            common_patches[1],
            common_patches[2],
            common_patches[3],
            common_patches[4],
            common_patches[5],
            patch.object(
                AUDIT,
                "refresh_existing_judgment_summary",
                return_value={"reused": True},
            ) as refresh,
        ):
            self.assertIsNone(
                AUDIT.reusable_source_record_audit(
                    args,
                    self.root,
                    self.paper_dir,
                    paper_statement_map_sha256="c" * 64,
                    paper_statement_map_semantic_sha256="e" * 64,
                )
            )
            refresh.assert_not_called()

        self._write_status(self.prior_status)
        receipt, error = TRANSITION.build_source_record_partial_to_formalized_transition(
            paper=PAPER,
            raw_audit=self.raw,
            raw_relative_path="audit/source_record_audit.json",
            prior_status_payload=self.prior_status,
            current_input_fingerprint=self.raw["source_record_input_fingerprint"],
            transition_engine_identity=current_engine,
        )
        self.assertEqual(error, "")
        assert receipt is not None
        self.receipt_path.write_text(
            json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        self._close_status()
        with (
            common_patches[0],
            common_patches[1],
            common_patches[2],
            common_patches[3],
            common_patches[4],
            common_patches[5],
            patch.object(
                AUDIT,
                "refresh_existing_judgment_summary",
                return_value={"reused": True},
            ) as refresh,
        ):
            self.assertEqual(
                AUDIT.reusable_source_record_audit(
                    args,
                    self.root,
                    self.paper_dir,
                    paper_statement_map_sha256="c" * 64,
                    paper_statement_map_semantic_sha256="e" * 64,
                ),
                {"reused": True},
            )
            self.assertEqual(refresh.call_count, 1)

    def test_nonempty_partial_optimization_cannot_be_prepared(self) -> None:
        raw = copy.deepcopy(self.raw)
        raw["precloseout_contract_covered_boundary_input_keys"] = ["opaque judgment"]
        raw["precloseout_exact_contract_projection"]["items"] = [{"opaque": True}]
        raw["precloseout_exact_contract_projection"]["covered_boundary_input_keys"] = [
            "opaque judgment"
        ]
        raw["precloseout_exact_contract_projection"]["covered_boundary_input_keys_sha256"] = (
            TRANSITION._payload_sha256(["opaque judgment"])
        )
        stamp_source_record_audit_receipts(raw)
        receipt, error = TRANSITION.build_source_record_partial_to_formalized_transition(
            paper=PAPER,
            raw_audit=raw,
            raw_relative_path="audit/source_record_audit.json",
            prior_status_payload=self.prior_status,
            current_input_fingerprint=raw["source_record_input_fingerprint"],
            transition_engine_identity=self.engine_identity,
        )
        self.assertIsNone(receipt)
        self.assertIn("empty partial-only", error)

    def test_saved_statement_ledger_requires_static_revalidation(self) -> None:
        """Direct coverage is not reusable merely because the raw says so."""

        raw, _key = self._raw_with_saved_direct_ledger()
        receipt, error = TRANSITION.build_source_record_partial_to_formalized_transition(
            paper=PAPER,
            raw_audit=raw,
            raw_relative_path="audit/source_record_audit.json",
            prior_status_payload=self.prior_status,
            current_input_fingerprint=raw["source_record_input_fingerprint"],
            transition_engine_identity=self.engine_identity,
        )
        self.assertIsNone(receipt)
        self.assertIn("current static direct-ledger coverage is unavailable", error)

    def test_saved_statement_ledger_subset_reuses_after_static_revalidation(self) -> None:
        """Exact retained direct coverage is safe across the status-only change."""

        self.raw, key = self._raw_with_saved_direct_ledger()
        self._write_raw(self.raw)
        self.current = copy.deepcopy(self.raw["source_record_input_fingerprint"])
        self.current["relevant_status_sha256"] = "b" * 64
        self._prepare({key})
        self._close_status()
        self.assertEqual(self._validate(current_direct_ledger_covered_keys={key}), "")

    def test_saved_statement_ledger_loss_refuses_after_preparation(self) -> None:
        """A stale current sidecar cannot retain an older suppressed input."""

        self.raw, key = self._raw_with_saved_direct_ledger()
        self._write_raw(self.raw)
        self.current = copy.deepcopy(self.raw["source_record_input_fingerprint"])
        self.current["relevant_status_sha256"] = "b" * 64
        self._prepare({key})
        self._close_status()
        self.assertIn(
            "no longer covers every saved direct key",
            self._validate(current_direct_ledger_covered_keys=set()),
        )

    def test_saved_statement_ledger_rejects_non_set_static_result(self) -> None:
        """A mapping cannot masquerade as a static direct-ledger key set."""

        self.raw, key = self._raw_with_saved_direct_ledger()
        receipt, error = TRANSITION.build_source_record_partial_to_formalized_transition(
            paper=PAPER,
            raw_audit=self.raw,
            raw_relative_path="audit/source_record_audit.json",
            prior_status_payload=self.prior_status,
            current_input_fingerprint=self.raw["source_record_input_fingerprint"],
            transition_engine_identity=self.engine_identity,
            current_direct_ledger_covered_keys={key: True},
        )
        self.assertIsNone(receipt)
        self.assertIn("current static direct-ledger coverage is malformed", error)

    def test_saved_statement_ledger_mutation_invalidates_prepared_receipt(self) -> None:
        """Restamping a raw cannot broaden a status-transition reuse route."""

        self._prepare()
        self._close_status()
        self.raw["expected_input_judgment_keys"] = [
            "surface.hypothesis : SourceCondition"
        ]
        self.raw["statement_ledger_covered_boundary_input_keys"] = [
            "surface.hypothesis : SourceCondition"
        ]
        stamp_source_record_audit_receipts(self.raw)
        self._write_raw(self.raw)
        self.assertIn("does not bind the current raw receipt", self._validate())

    def test_receipt_tamper_refuses(self) -> None:
        self._prepare()
        self._close_status()
        payload = json.loads(self.receipt_path.read_text(encoding="utf-8"))
        payload["transition"]["to_status"] = "formalized with caveat"
        self.receipt_path.write_text(
            json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        self.assertIn("digest is invalid", self._validate())

    def test_shared_identity_gate_accepts_only_valid_transition(self) -> None:
        self._prepare()
        self._close_status()
        current_payload = {
            "paper": PAPER,
            "paper_statement_map_sha256": "c" * 64,
            "paper_statement_map_semantic_sha256": "e" * 64,
            "source_record_input_fingerprint": self.current,
        }
        completed = SimpleNamespace(
            returncode=0,
            stdout=json.dumps(current_payload),
            stderr="",
        )
        prior_root = EVIDENCE.ROOT
        try:
            EVIDENCE.ROOT = self.root
            helper = (
                self.root
                / "skills"
                / "econcs-formalizer"
                / "scripts"
                / "source_record_audit.py"
            )
            helper.parent.mkdir(parents=True)
            helper.write_text(
                "PARTIAL_TO_FORMALIZED_STATUS_TRANSITION_ENGINE_IDENTITY = "
                + repr(self.engine_identity)
                + "\n",
                encoding="utf-8",
            )
            with patch.object(EVIDENCE.subprocess, "run", return_value=completed):
                self.assertEqual(
                    EVIDENCE.source_record_current_input_fingerprint_error(
                        self.paper_dir, self.raw
                    ),
                    "",
                )
            self.status_path.write_text("{}\n", encoding="utf-8")
            with patch.object(EVIDENCE.subprocess, "run", return_value=completed):
                self.assertIn(
                    "partial-to-formalized transition rejected",
                    EVIDENCE.source_record_current_input_fingerprint_error(
                        self.paper_dir, self.raw
                    ),
                )
        finally:
            EVIDENCE.ROOT = prior_root


if __name__ == "__main__":
    unittest.main()
