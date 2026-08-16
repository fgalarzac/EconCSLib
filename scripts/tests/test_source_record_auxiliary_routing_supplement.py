#!/usr/bin/env python3
"""Adversarial tests for cached reachable-PaperInterface routing evidence."""

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

from scripts import source_record_auxiliary_routing_supplement as SUPPLEMENT
from scripts.source_record_integrity import stamp_source_record_audit_receipts


PAPER = "FixturePaper"
PROMPT = "source-record-v10-semantic-conclusion-boundary-contract"
SOURCE_RECORD_AUDIT_HELPER = (
    ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
)


def sha256_bytes(contents: bytes) -> str:
    return hashlib.sha256(contents).hexdigest()


class AuxiliaryRoutingSupplementTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.paper_dir = self.root / "papers" / PAPER
        self.audit_dir = self.paper_dir / "audit"
        self.audit_dir.mkdir(parents=True)
        self.interface_path = self.paper_dir / "PaperInterface.lean"
        self.unused_source_path = self.paper_dir / "Unused.lean"
        self.status_path = self.paper_dir / "status.json"
        self.map_path = self.audit_dir / "paper_statement_map.json"
        self.fidelity_path = self.audit_dir / "source_proof_fidelity.json"
        self.raw_path = self.audit_dir / "source_record_audit.json"
        self.supplement_path = self.audit_dir / SUPPLEMENT.SUPPLEMENT_BASENAME

        self.interface_path.write_text(
            """namespace FixturePaper.PaperInterface

theorem helper : True := True.intro
theorem selected : True := helper
theorem out_of_mode_helper : True := True.intro
theorem out_of_mode : True := out_of_mode_helper

end FixturePaper.PaperInterface
""",
            encoding="utf-8",
        )
        # The historical generator includes every paper-local Lean file in its
        # closure. This unrelated file proves that consumer validation checks
        # every issued source identity rather than only names on the route.
        self.unused_source_path.write_text(
            "namespace FixturePaper\n theorem unrelated : True := True.intro\nend FixturePaper\n",
            encoding="utf-8",
        )
        self.status_path.write_text(
            json.dumps(
                {
                    "status": "formalized",
                    "review_surface": {
                        "include_names": ["selected"],
                        "auxiliary_names": ["helper"],
                    },
                },
                sort_keys=True,
            ),
            encoding="utf-8",
        )
        self.map_path.write_text(
            json.dumps(
                {
                    "items": {
                        "helper_support": {
                            "source_location": "source.tex:1",
                            "lean_declarations": [
                                "FixturePaper.PaperInterface.helper"
                            ],
                        }
                    }
                },
                sort_keys=True,
            ),
            encoding="utf-8",
        )
        self.fidelity_path.write_text("{}\n", encoding="utf-8")
        self._write_raw()
        self.supplement = SUPPLEMENT.build_auxiliary_routing_supplement(
            root=self.root,
            paper=PAPER,
            verify_current_raw_identity=False,
            helper_path=SOURCE_RECORD_AUDIT_HELPER,
        )
        self._write_supplement(self.supplement)

    def _write_raw(self, *, extra: dict[str, object] | None = None) -> None:
        map_digest = sha256_bytes(self.map_path.read_bytes())
        selected_declaration = "FixturePaper.PaperInterface.selected"
        raw: dict[str, object] = {
            "paper": PAPER,
            "prompt_version": PROMPT,
            "source_record_input_fingerprint": {
                "max_depth": 4,
                "no_lean": False,
                "relevant_status_sha256": sha256_bytes(
                    self.status_path.read_bytes()
                ),
                "source_proof_fidelity_sha256": sha256_bytes(
                    self.fidelity_path.read_bytes()
                ),
                "lean_dependency_identities": [
                    {
                        "path": f"papers/{PAPER}/PaperInterface.lean",
                        "sha256": sha256_bytes(self.interface_path.read_bytes()),
                        "status": "present",
                    },
                    {
                        "path": f"papers/{PAPER}/Unused.lean",
                        "sha256": sha256_bytes(self.unused_source_path.read_bytes()),
                        "status": "present",
                    },
                ],
            },
            "paper_statement_map_sha256": map_digest,
            "review_interface_source": {
                "path": f"papers/{PAPER}/PaperInterface.lean",
                "sha256": sha256_bytes(self.interface_path.read_bytes()),
            },
            "review_assumption_source": None,
            "semantic_model_items": [
                {
                    "qualified_declaration": selected_declaration,
                    "paper_statement_map_sha256": map_digest,
                    "reviewed_declaration_identity": {
                        "qualified_declaration": selected_declaration,
                        "declaration_sha256": "a" * 64,
                    },
                    "source_statement_association": {
                        "schema": 2,
                        "semantic_association_sha256": "b" * 64,
                    },
                }
            ],
            "configured_review_rows": [
                {
                    "row": "selected",
                    "qualified_declaration": selected_declaration
                }
            ],
            "row_visible_inputs": {"selected": []},
        }
        if extra:
            raw.update(extra)
        stamp_source_record_audit_receipts(raw)
        self.raw_path.write_text(
            json.dumps(raw, sort_keys=True, indent=2) + "\n", encoding="utf-8"
        )
        self.raw = raw

    def _write_supplement(self, payload: dict[str, object]) -> None:
        self.supplement_path.write_text(
            json.dumps(payload, sort_keys=True, indent=2) + "\n", encoding="utf-8"
        )

    def _validate(
        self, *, helper_path: Path | None = SOURCE_RECORD_AUDIT_HELPER
    ) -> tuple[SUPPLEMENT.ValidatedAuxiliaryRoutingContext | None, str]:
        return SUPPLEMENT.validate_auxiliary_routing_supplement(
            root=self.root,
            paper_dir=self.paper_dir,
            paper=PAPER,
            audit_payload=self.raw,
            verify_current_raw_identity=False,
            helper_path=helper_path,
        )

    def _change_routing_status(self) -> None:
        payload = json.loads(self.status_path.read_text(encoding="utf-8"))
        review_surface = payload["review_surface"]
        assert isinstance(review_surface, dict)
        review_surface["auxiliary_names"] = ["helper", "different_helper"]
        self.status_path.write_text(
            json.dumps(payload, sort_keys=True), encoding="utf-8"
        )

    def test_valid_manifest_reuses_issued_closure_without_parser(self) -> None:
        """The consumer never loads or traverses the issued Lean closure."""

        with patch.object(
            SUPPLEMENT,
            "_load_routing_helper",
            side_effect=AssertionError("consumer loaded parser"),
        ), patch.object(
            SUPPLEMENT,
            "_live_routing_snapshot",
            side_effect=AssertionError("consumer replayed parser closure"),
        ):
            context, error = self._validate()
        self.assertEqual(error, "")
        self.assertIsNotNone(context)
        assert context is not None
        self.assertEqual(context.provenance, "replayed_auxiliary_routing_supplement")
        self.assertEqual(context.unresolved_auxiliaries(), ())

    def test_context_binds_ledger_only_to_the_authenticated_raw_payload(self) -> None:
        context, error = self._validate()
        self.assertEqual(error, "")
        self.assertIsNotNone(context)
        assert context is not None

        augmented, augmented_error = context.audit_payload_with_authenticated_ledger(
            self.raw
        )
        self.assertEqual(augmented_error, "")
        self.assertIsNotNone(augmented)
        assert augmented is not None
        for key in SUPPLEMENT.LEDGER_KEYS:
            self.assertEqual(augmented[key], self.supplement["routing_ledger"][key])

        changed_raw = copy.deepcopy(self.raw)
        changed_raw["unrelated_runtime_note"] = "not the authenticated receipt"
        rejected, rejected_error = context.audit_payload_with_authenticated_ledger(
            changed_raw
        )
        self.assertIsNone(rejected)
        self.assertIn("exact raw audit payload", rejected_error)

    def test_every_issued_parser_source_is_pinned(self) -> None:
        self.unused_source_path.write_text(
            self.unused_source_path.read_text(encoding="utf-8") + "\n-- changed\n",
            encoding="utf-8",
        )
        _context, error = self._validate()
        self.assertEqual(error, "supplement routing parser-source identity changed")

    def test_unrelated_status_reporting_change_reuses_issued_closure(self) -> None:
        payload = json.loads(self.status_path.read_text(encoding="utf-8"))
        payload["post_formalization_reporting_note"] = {"reviewed": "today"}
        self.status_path.write_text(
            json.dumps(payload, sort_keys=True), encoding="utf-8"
        )
        context, error = self._validate()
        self.assertEqual(error, "")
        self.assertIsNotNone(context)

    def test_out_of_mode_include_cannot_seed_a_routing_obligation(self) -> None:
        """Only raw visible-input review roots seed the issued closure."""

        baseline_ledger = copy.deepcopy(self.supplement["routing_ledger"])
        payload = json.loads(self.status_path.read_text(encoding="utf-8"))
        review_surface = payload["review_surface"]
        assert isinstance(review_surface, dict)
        include_names = review_surface["include_names"]
        assert isinstance(include_names, list)
        include_names.append("out_of_mode")
        self.status_path.write_text(
            json.dumps(payload, sort_keys=True), encoding="utf-8"
        )

        scoped = SUPPLEMENT.build_auxiliary_routing_supplement(
            root=self.root,
            paper=PAPER,
            verify_current_raw_identity=False,
            helper_path=SOURCE_RECORD_AUDIT_HELPER,
        )
        manifest = scoped["routing_closure_manifest"]
        assert isinstance(manifest, dict)
        active_roots = SUPPLEMENT._raw_active_review_roots(self.raw)
        self.assertEqual(manifest["raw_active_review_roots"], active_roots)
        self.assertEqual(
            manifest["selected_review_declarations"],
            [root["qualified_declaration"] for root in active_roots],
        )
        self.assertEqual(scoped["routing_ledger"], baseline_ledger)

        active_rows = {root["row"] for root in active_roots}
        ledger = scoped["routing_ledger"]
        assert isinstance(ledger, dict)
        for dependency in ledger[
            "reachable_paper_interface_auxiliary_dependencies"
        ]:
            assert isinstance(dependency, dict)
            for route in dependency["transitively_referenced_from"]:
                assert isinstance(route, dict)
                self.assertTrue(
                    set(route["selected_review_rows"]).issubset(active_rows)
                )

        self._write_supplement(scoped)
        context, error = self._validate()
        self.assertEqual(error, "")
        self.assertIsNotNone(context)

    def test_current_status_must_retain_every_raw_active_root(self) -> None:
        active_root = SUPPLEMENT._raw_active_review_roots(self.raw)[0]
        payload = json.loads(self.status_path.read_text(encoding="utf-8"))
        review_surface = payload["review_surface"]
        assert isinstance(review_surface, dict)
        include_names = review_surface["include_names"]
        assert isinstance(include_names, list)
        include_names.remove(active_root["row"])
        self.status_path.write_text(
            json.dumps(payload, sort_keys=True), encoding="utf-8"
        )
        _context, error = self._validate()
        self.assertEqual(
            error,
            "current status no longer selects one or more raw active review rows",
        )

    def test_raw_map_interface_assumptions_and_fidelity_changes_refuse(self) -> None:
        assumptions_path = self.paper_dir / "Assumptions.lean"
        baseline_paths = [
            self.status_path,
            self.map_path,
            self.interface_path,
            self.fidelity_path,
            self.raw_path,
            self.supplement_path,
            assumptions_path,
        ]
        baseline = {
            path: path.read_bytes() if path.exists() else None for path in baseline_paths
        }
        baseline_raw = copy.deepcopy(self.raw)
        cases = [
            (
                "routing status",
                self._change_routing_status,
                "supplement routing inputs no longer match current identities",
            ),
            (
                "raw binding",
                lambda: self._write_raw(extra={"issued_note": "changed"}),
                "supplement raw binding does not match the exact current raw receipt",
            ),
            (
                "map",
                lambda: self.map_path.write_text(
                    self.map_path.read_text(encoding="utf-8") + "\n", encoding="utf-8"
                ),
                "paper_statement_map.json no longer matches the raw source-record receipt",
            ),
            (
                "interface",
                lambda: self.interface_path.write_text(
                    self.interface_path.read_text(encoding="utf-8") + "\n-- changed\n",
                    encoding="utf-8",
                ),
                "raw review_interface_source identity changed",
            ),
            (
                "assumptions",
                lambda: assumptions_path.write_text(
                    "namespace FixturePaper\nend FixturePaper\n", encoding="utf-8"
                ),
                "Assumptions.lean appeared after the raw source-record audit",
            ),
            (
                "fidelity",
                lambda: self.fidelity_path.write_text("{\"changed\": true}\n", encoding="utf-8"),
                "source-proof fidelity ledger no longer matches the raw input fingerprint",
            ),
        ]
        for label, mutate, expected in cases:
            with self.subTest(label=label):
                mutate()
                _context, error = self._validate()
                self.assertEqual(error, expected)
                for path, contents in baseline.items():
                    if contents is None:
                        path.unlink(missing_ok=True)
                    else:
                        path.write_bytes(contents)
                self.raw = copy.deepcopy(baseline_raw)

    def test_manifest_and_ledger_tampering_refuse(self) -> None:
        manifest_tamper = copy.deepcopy(self.supplement)
        manifest = manifest_tamper["routing_closure_manifest"]
        assert isinstance(manifest, dict)
        manifest["parsed_declarations_sha256"] = "0" * 64
        self._write_supplement(manifest_tamper)
        _context, error = self._validate()
        self.assertEqual(
            error,
            "supplement routing-closure-manifest receipt does not match its contents",
        )

        ledger_tamper = copy.deepcopy(self.supplement)
        ledger = ledger_tamper["routing_ledger"]
        assert isinstance(ledger, dict)
        ledger["unresolved_reachable_paper_interface_auxiliaries"] = [{"fake": True}]
        ledger_tamper["routing_ledger_sha256"] = SUPPLEMENT._payload_sha256(ledger)
        self._write_supplement(ledger_tamper)
        _context, error = self._validate()
        self.assertEqual(
            error,
            "supplement routing ledger is not bound to its closure manifest",
        )

        association_tamper = copy.deepcopy(self.supplement)
        association_manifest = association_tamper["routing_closure_manifest"]
        assert isinstance(association_manifest, dict)
        association_manifest["selected_root_source_associations"] = []
        association_tamper["routing_closure_manifest_sha256"] = (
            SUPPLEMENT._payload_sha256(association_manifest)
        )
        self._write_supplement(association_tamper)
        _context, error = self._validate()
        self.assertEqual(
            error,
            "supplement source-association projection does not match the raw audit",
        )

    def test_engine_version_is_the_reissue_boundary_not_helper_bytes(self) -> None:
        helper_copy = self.root / "source_record_audit_copy.py"
        helper_copy.write_text(
            SOURCE_RECORD_AUDIT_HELPER.read_text(encoding="utf-8")
            + "\n# Nonsemantic fixture comment.\n",
            encoding="utf-8",
        )
        context, error = self._validate(helper_path=helper_copy)
        self.assertEqual(error, "")
        self.assertIsNotNone(context)

        helper_copy.write_text(
            helper_copy.read_text(encoding="utf-8").replace(
                "reachable-paper-interface-auxiliary-routing-v1",
                "reachable-paper-interface-auxiliary-routing-v2",
                1,
            ),
            encoding="utf-8",
        )
        _context, error = self._validate(helper_path=helper_copy)
        self.assertEqual(
            error, "supplement routing inputs no longer match current identities"
        )

    def test_supplement_producer_version_drift_requires_only_reissue(self) -> None:
        """Replay transport semantics have their own narrow cache boundary."""

        changed_identity = dict(
            SUPPLEMENT.AUXILIARY_ROUTING_SUPPLEMENT_ENGINE_IDENTITY
        )
        changed_identity["surface_semantic_version"] = "auxiliary-routing-supplement-v2"
        with patch.object(
            SUPPLEMENT,
            "AUXILIARY_ROUTING_SUPPLEMENT_ENGINE_IDENTITY",
            changed_identity,
        ):
            _context, error = self._validate()
        self.assertEqual(
            error, "supplement routing inputs no longer match current identities"
        )

    def test_missing_supplement_producer_identity_refuses_on_load(self) -> None:
        malformed = copy.deepcopy(self.supplement)
        inputs = malformed["routing_inputs"]
        assert isinstance(inputs, dict)
        inputs.pop("supplement_engine_identity")
        malformed["routing_inputs_sha256"] = SUPPLEMENT._payload_sha256(inputs)
        self._write_supplement(malformed)
        _context, error = self._validate()
        self.assertEqual(
            error, "supplement routing inputs have a malformed producer identity"
        )


if __name__ == "__main__":
    unittest.main()
