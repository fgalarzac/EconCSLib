"""Focused checks for the direct-route diagnostic-only raw receipt rebind."""

from __future__ import annotations

import copy
import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from scripts import source_record_diagnostic_rebind as REBIND
from scripts.source_record_integrity import (
    attach_source_record_audit_surface,
    source_record_audit_receipt_error,
    stamp_source_record_audit_integrity,
)


PAPER = "Fixture"
EVIDENCE = "Fixture.Paper.evidence"
SPEC = "Fixture.Paper.evidenceSpec"


def _json_bytes(payload: object) -> bytes:
    return json.dumps(payload, indent=2, sort_keys=True).encode("utf-8") + b"\n"


class DirectRouteDiagnosticRebindTests(unittest.TestCase):
    def _fixture(
        self, *, contract_override: dict[str, object] | None = None
    ) -> tuple[dict[str, object], bytes, dict[str, object], bytes]:
        contract: dict[str, object] = {
            "evidence_declaration": EVIDENCE,
            "spec_declaration": SPEC,
            "evidence_mode": "proves",
            "semantic_shape": "plain",
        }
        if contract_override is not None:
            contract = contract_override
        statement_map: dict[str, object] = {
            "semantic_contract_schema": 1,
            "source_coverage_mode": "named_theoretical_statements",
            "items": {
                "source_endpoint": {
                    "source_kind": "theorem",
                    "claim_bearing": True,
                    "source_location": "source.txt:1-2",
                    "statement": "Theorem 1. The endpoint holds.",
                    "semantic_contract": contract,
                }
            },
        }
        map_bytes = _json_bytes(statement_map)
        source_item = statement_map["items"]["source_endpoint"]
        assert isinstance(source_item, dict)
        source_identity = REBIND._source_item_identity("source_endpoint", source_item)
        evidence_declaration = "theorem evidence : True := by trivial"
        spec_declaration = "abbrev evidenceSpec : Prop := True"
        evidence_identity = {
            "qualified_declaration": EVIDENCE,
            "declaration_sha256": hashlib.sha256(
                evidence_declaration.encode("utf-8")
            ).hexdigest(),
        }
        spec_identity = {
            "qualified_declaration": SPEC,
            "declaration_sha256": hashlib.sha256(
                spec_declaration.encode("utf-8")
            ).hexdigest(),
        }
        semantic_item: dict[str, object] = {
            "row": "evidence",
            "judgment_key": "semantic-model::endpoint",
            "qualified_declaration": EVIDENCE,
            "source_record_item_reuse_eligibility": {
                "eligible": True,
                "blockers": [],
            },
            "source_record_item_digest_schema": 5,
            "source_record_item_semantic_id": "a" * 64,
            "source_record_item_context_sha256": "b" * 64,
            "source_record_item_sha256": "c" * 64,
            "reviewed_elaborated_signature_identities": [
                {
                    "qualified_declaration": EVIDENCE,
                    "elaborated_signature_sha256": "d" * 64,
                }
            ],
            "semantic_contract_group": {
                "schema": 1,
                "source_item_identities": [source_identity],
                "member_rows": [
                    {
                        "role": "direct_evidence",
                        "qualified_declaration": EVIDENCE,
                        "reviewed_declaration_identity": evidence_identity,
                    },
                    {
                        "role": "transparent_spec",
                        "qualified_declaration": SPEC,
                        "reviewed_declaration_identity": spec_identity,
                    },
                ],
            },
        }
        raw: dict[str, object] = {
            "paper": PAPER,
            "prompt_version": REBIND.SOURCE_RECORD_V10_PROMPT_VERSION,
            "source_record_policy_version": REBIND.SOURCE_RECORD_V10_PROMPT_VERSION,
            "paper_statement_map_sha256": hashlib.sha256(map_bytes).hexdigest(),
            "source_record_input_fingerprint": {"no_lean": False},
            "source_coverage_selected_source_items": ["source_endpoint"],
            "configured_review_rows": [
                {
                    "row": "evidence",
                    "qualified_declaration": EVIDENCE,
                    "lean_source_declaration": evidence_declaration,
                },
                {
                    "row": "spec",
                    "qualified_declaration": SPEC,
                    "lean_source_declaration": spec_declaration,
                },
            ],
            "boundary_input_items": [],
            "conclusion_dependency_items": [],
            "type_valued_certificate_result_items": [],
            "recursive_field_items": [],
            "semantic_model_items": [semantic_item],
            "source_premise_consistency_items": [],
            "source_contract_association_errors": [
                REBIND._error_for_source_key("source_endpoint")
            ],
            "source_contract_association_error_count": 1,
        }
        self._stamp(raw)
        raw_bytes = _json_bytes(raw)
        return raw, raw_bytes, statement_map, map_bytes

    @staticmethod
    def _stamp(raw: dict[str, object]) -> None:
        surface = {
            "configured_review_rows": copy.deepcopy(raw["configured_review_rows"]),
            "semantic_model_items": copy.deepcopy(raw["semantic_model_items"]),
            "source_coverage_selected_source_items": copy.deepcopy(
                raw["source_coverage_selected_source_items"]
            ),
            "source_contract_association_errors": copy.deepcopy(
                raw["source_contract_association_errors"]
            ),
            "source_contract_association_error_count": raw[
                "source_contract_association_error_count"
            ],
        }
        attach_source_record_audit_surface(raw, surface)
        stamp_source_record_audit_integrity(raw)

    def test_rebinds_only_the_mirrored_false_positive_diagnostics(self) -> None:
        raw, raw_bytes, statement_map, map_bytes = self._fixture()
        candidate, error = REBIND.build_direct_route_diagnostic_rebind(
            paper=PAPER,
            raw_audit=raw,
            raw_audit_bytes=raw_bytes,
            raw_audit_reference="audit/prior.json",
            statement_map=statement_map,
            statement_map_bytes=map_bytes,
            statement_map_reference="audit/paper_statement_map.json",
        )

        self.assertEqual(error, "")
        assert candidate is not None
        self.assertEqual(candidate["source_contract_association_errors"], [])
        self.assertEqual(candidate["source_contract_association_error_count"], 0)
        self.assertEqual(source_record_audit_receipt_error(candidate), "")
        for section in REBIND.SOURCE_RECORD_REUSABLE_ITEM_SECTIONS:
            self.assertEqual(candidate.get(section), raw.get(section), section)
        provenance = candidate[REBIND.DIRECT_ROUTE_DIAGNOSTIC_REBIND_FIELD]
        assert isinstance(provenance, dict)
        self.assertEqual(
            provenance["removed_false_positive_diagnostics"][0]["evidence_declaration"],
            EVIDENCE,
        )
        self.assertEqual(
            provenance["removed_false_positive_diagnostics"][0]["spec_declaration"],
            SPEC,
        )
        self.assertEqual(REBIND._rebind_delta_error(raw, candidate), "")

    def test_rejects_malformed_current_semantic_contract(self) -> None:
        raw, raw_bytes, statement_map, map_bytes = self._fixture(
            contract_override={
                "evidence_declaration": EVIDENCE,
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            }
        )
        candidate, error = REBIND.build_direct_route_diagnostic_rebind(
            paper=PAPER,
            raw_audit=raw,
            raw_audit_bytes=raw_bytes,
            raw_audit_reference="audit/prior.json",
            statement_map=statement_map,
            statement_map_bytes=map_bytes,
            statement_map_reference="audit/paper_statement_map.json",
        )

        self.assertIsNone(candidate)
        self.assertIn("is malformed", error)

    def test_rejects_raw_association_that_does_not_pin_current_source_item(self) -> None:
        raw, _raw_bytes, statement_map, map_bytes = self._fixture()
        semantic_items = raw["semantic_model_items"]
        assert isinstance(semantic_items, list)
        group = semantic_items[0]["semantic_contract_group"]
        assert isinstance(group, dict)
        identities = group["source_item_identities"]
        assert isinstance(identities, list)
        identities[0]["source_semantic_sha256"] = "e" * 64
        self._stamp(raw)
        raw_bytes = _json_bytes(raw)

        candidate, error = REBIND.build_direct_route_diagnostic_rebind(
            paper=PAPER,
            raw_audit=raw,
            raw_audit_bytes=raw_bytes,
            raw_audit_reference="audit/prior.json",
            statement_map=statement_map,
            statement_map_bytes=map_bytes,
            statement_map_reference="audit/paper_statement_map.json",
        )

        self.assertIsNone(candidate)
        self.assertIn("semantic-model items do not contain", error)

    def test_rejects_an_unrelated_source_contract_diagnostic(self) -> None:
        raw, _raw_bytes, statement_map, map_bytes = self._fixture()
        raw["source_contract_association_errors"] = ["unrelated generated error"]
        raw["source_contract_association_error_count"] = 1
        self._stamp(raw)
        raw_bytes = _json_bytes(raw)

        candidate, error = REBIND.build_direct_route_diagnostic_rebind(
            paper=PAPER,
            raw_audit=raw,
            raw_audit_bytes=raw_bytes,
            raw_audit_reference="audit/prior.json",
            statement_map=statement_map,
            statement_map_bytes=map_bytes,
            statement_map_reference="audit/paper_statement_map.json",
        )

        self.assertIsNone(candidate)
        self.assertIn("outside the direct-route false-positive shape", error)

    def test_installed_rebind_is_reproducible_from_archived_bytes(self) -> None:
        raw, raw_bytes, statement_map, map_bytes = self._fixture()
        candidate, error = REBIND.build_direct_route_diagnostic_rebind(
            paper=PAPER,
            raw_audit=raw,
            raw_audit_bytes=raw_bytes,
            raw_audit_reference="audit/prior.json",
            statement_map=statement_map,
            statement_map_bytes=map_bytes,
            statement_map_reference="audit/paper_statement_map.json",
        )
        self.assertEqual(error, "")
        assert candidate is not None
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            paper_dir = root / "papers" / PAPER
            audit = paper_dir / "audit"
            audit.mkdir(parents=True)
            (audit / "prior.json").write_bytes(raw_bytes)
            (audit / "paper_statement_map.json").write_bytes(map_bytes)
            self.assertEqual(
                REBIND.direct_route_diagnostic_rebind_error(
                    root=root,
                    paper=PAPER,
                    paper_dir=paper_dir,
                    raw_audit=candidate,
                ),
                "",
            )
            candidate["semantic_model_items"][0]["tampered"] = True
            self.assertIn(
                "differs from its reproducible candidate",
                REBIND.direct_route_diagnostic_rebind_error(
                    root=root,
                    paper=PAPER,
                    paper_dir=paper_dir,
                    raw_audit=candidate,
                ),
            )


if __name__ == "__main__":
    unittest.main()
