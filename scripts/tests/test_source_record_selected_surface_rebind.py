"""Focused adversarial checks for selected-surface provenance rebinds."""

from __future__ import annotations

import copy
import hashlib
import json
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import Mock, patch

from scripts import source_record_selected_surface_rebind as REBIND
from scripts.source_record_integrity import (
    attach_source_record_audit_surface,
    stamp_source_record_audit_integrity,
)


PAPER = "Fixture"


def _json_bytes(value: object) -> bytes:
    return json.dumps(value, indent=2, sort_keys=True).encode("utf-8") + b"\n"


def _map_semantic_receipt(marker: str) -> str:
    return hashlib.sha256(marker.encode("utf-8")).hexdigest()


class SelectedSurfaceRebindTests(unittest.TestCase):
    def _fixture(
        self,
        *,
        with_context: bool = False,
        direct_ledger: list[str] | None = None,
        raw_roots: list[str] | None = None,
    ) -> tuple[dict[str, object], bytes, dict[str, object], bytes, dict[str, object]]:
        item: dict[str, object] = {
            "source_kind": "theorem",
            "claim_bearing": True,
            "source_location": "source.txt:1-2",
            "statement": "Theorem 1. The source endpoint holds.",
            "lean_declarations": ["Fixture.endpoint"],
        }
        if with_context:
            item["semantic_context_requirements"] = [
                {
                    "kind": "positive_density",
                    "source_location": "source.txt:3-4",
                    "explanation": "The density is positive on the stated support.",
                    "source_anchor_evidence": [
                        {
                            "path": "source.txt",
                            "line_start": 3,
                            "line_end": 4,
                            "quoted_text": "The density is positive.",
                            "quoted_text_sha256": "a" * 64,
                        }
                    ],
                }
            ]
        prior_map: dict[str, object] = {
            "source_coverage_mode": "named_theoretical_statements",
            "items": {"old_inventory_coordinate": item},
        }
        current_map: dict[str, object] = {
            "source_coverage_mode": "named_theoretical_statements",
            # A key-only rename must be positive: selection joins through
            # source content, not either key spelling.
            "items": {"renamed_inventory_coordinate": copy.deepcopy(item)},
        }
        prior_map_bytes = _json_bytes(prior_map)
        current_map_bytes = _json_bytes(current_map)
        descriptor = REBIND._source_descriptor(item)
        raw_contexts: list[dict[str, object]] = []
        if with_context:
            context = item["semantic_context_requirements"][0]
            assert isinstance(context, dict)
            raw_contexts.append(
                {
                    "source_item_key": "old_inventory_coordinate",
                    "requirement_index": 0,
                    "kind": context["kind"],
                    "source_location": context["source_location"],
                    "explanation": context["explanation"],
                    "source_anchor_evidence": context["source_anchor_evidence"],
                }
            )
        raw: dict[str, object] = {
            "paper": PAPER,
            "prompt_version": REBIND.SOURCE_RECORD_V10_PROMPT_VERSION,
            "source_record_policy_version": REBIND.SOURCE_RECORD_V10_PROMPT_VERSION,
            "paper_statement_map_sha256": hashlib.sha256(prior_map_bytes).hexdigest(),
            "source_record_input_fingerprint": {
                "schema": 8,
                "paper": PAPER,
                "no_lean": False,
                "max_depth": 4,
                "paper_statement_map_semantic_sha256": _map_semantic_receipt("old"),
                "source_artifact_identities": [
                    {"path": "papers/Fixture/source.txt", "sha256": "b" * 64, "status": "present"}
                ],
                "audit_engine_identities": [
                    {"path": "generator", "surface_semantic_version": "v1"}
                ],
                "review_interface_source": {"path": "papers/Fixture/PaperInterface.lean", "sha256": "c" * 64},
                "lean_dependency_identities": [],
                "toolchain_identities": [],
            },
            "source_coverage_mode": "named_theoretical_statements",
            "source_coverage_selected_source_items": ["old_inventory_coordinate"],
            "semantic_context_requirements": raw_contexts,
            "source_premise_consistency_scanned_record_roots": raw_roots or [],
            "statement_ledger_covered_boundary_input_keys": direct_ledger or [],
            "precloseout_contract_covered_boundary_input_keys": [],
            "boundary_input_items": [],
            "conclusion_dependency_items": [],
            "type_valued_certificate_result_items": [],
            "recursive_field_items": [],
            "source_premise_consistency_items": [],
            "semantic_model_items": [
                {
                    "judgment_key": "semantic-model::endpoint",
                    "source_statement_association": {
                        "schema": 2,
                        "role": "direct_source_route",
                        "source_item_identities": [
                            {
                                "source_key": "old_inventory_coordinate",
                                **descriptor,
                            }
                        ],
                    },
                }
            ],
            "reachable_paper_interface_auxiliary_dependencies": [],
            "unresolved_reachable_paper_interface_auxiliaries": [],
            "ambiguous_reachable_paper_interface_auxiliary_references": [],
            "reachable_paper_interface_auxiliary_quarantine_configuration_errors": [],
        }
        attach_source_record_audit_surface(raw, {})
        stamp_source_record_audit_integrity(raw)
        fingerprint = copy.deepcopy(raw["source_record_input_fingerprint"])
        assert isinstance(fingerprint, dict)
        fingerprint["paper_statement_map_semantic_sha256"] = _map_semantic_receipt(
            "current"
        )
        return raw, _json_bytes(raw), current_map, current_map_bytes, fingerprint

    def _build(
        self,
        raw: dict[str, object],
        raw_bytes: bytes,
        current_map: dict[str, object],
        current_map_bytes: bytes,
        fingerprint: dict[str, object],
        *,
        roots: list[str] | None = None,
        ledger: set[str] | None = None,
    ) -> tuple[dict[str, object] | None, str]:
        return REBIND.build_selected_surface_rebind(
            paper=PAPER,
            raw_audit=raw,
            raw_audit_bytes=raw_bytes,
            raw_audit_relative_path="audit/source_record_audit.json",
            statement_map=current_map,
            statement_map_bytes=current_map_bytes,
            statement_map_relative_path="audit/paper_statement_map.json",
            current_input_fingerprint=fingerprint,
            current_routing={
                "reachable_paper_interface_auxiliary_dependencies": [],
                "unresolved_reachable_paper_interface_auxiliaries": [],
                "ambiguous_reachable_paper_interface_auxiliary_references": [],
                "reachable_paper_interface_auxiliary_quarantine_configuration_errors": [],
            },
            current_source_premise_roots=roots or [],
            current_direct_ledger_keys=ledger or set(),
        )

    def test_key_rename_rebinds_by_source_content_not_key_or_declaration_name(self) -> None:
        raw, raw_bytes, current_map, current_map_bytes, fingerprint = self._fixture()
        receipt, error = self._build(
            raw, raw_bytes, current_map, current_map_bytes, fingerprint
        )
        self.assertEqual(error, "")
        assert receipt is not None
        self.assertEqual(
            receipt["dependency_manifest"]["selected_source_descriptors"],
            [REBIND._source_descriptor(current_map["items"]["renamed_inventory_coordinate"])],
        )
        self.assertEqual(
            REBIND.validate_selected_surface_rebind(
                receipt,
                paper=PAPER,
                raw_audit=raw,
                raw_audit_bytes=raw_bytes,
                raw_audit_relative_path="audit/source_record_audit.json",
                statement_map=current_map,
                statement_map_bytes=current_map_bytes,
                statement_map_relative_path="audit/paper_statement_map.json",
                current_input_fingerprint=fingerprint,
                current_routing={
                    "reachable_paper_interface_auxiliary_dependencies": [],
                    "unresolved_reachable_paper_interface_auxiliaries": [],
                    "ambiguous_reachable_paper_interface_auxiliary_references": [],
                    "reachable_paper_interface_auxiliary_quarantine_configuration_errors": [],
                },
                current_source_premise_roots=[],
                current_direct_ledger_keys=set(),
            ),
            "",
        )

    def test_rejects_selected_source_content_or_route_retarget(self) -> None:
        raw, raw_bytes, current_map, current_map_bytes, fingerprint = self._fixture()
        item = current_map["items"]["renamed_inventory_coordinate"]
        assert isinstance(item, dict)
        item["statement"] = "Theorem 1. A different endpoint holds."
        receipt, error = self._build(
            raw, raw_bytes, current_map, _json_bytes(current_map), fingerprint
        )
        self.assertIsNone(receipt)
        self.assertIn("selected source content differs", error)

        raw, raw_bytes, current_map, current_map_bytes, fingerprint = self._fixture()
        item = current_map["items"]["renamed_inventory_coordinate"]
        assert isinstance(item, dict)
        item["lean_declarations"] = ["Fixture.otherExistingEndpoint"]
        receipt, error = self._build(
            raw, raw_bytes, current_map, _json_bytes(current_map), fingerprint
        )
        self.assertIsNone(receipt)
        self.assertIn("selected source content differs", error)

    def test_rejects_selector_context_and_duplicate_ambiguity(self) -> None:
        raw, raw_bytes, current_map, _current_map_bytes, fingerprint = self._fixture()
        current_map["source_coverage_mode"] = "deep_paper_with_all_prose_claims"
        receipt, error = self._build(
            raw, raw_bytes, current_map, _json_bytes(current_map), fingerprint
        )
        self.assertIsNone(receipt)
        self.assertIn("selector mode", error)

        raw, raw_bytes, current_map, _current_map_bytes, fingerprint = self._fixture(
            with_context=True
        )
        item = current_map["items"]["renamed_inventory_coordinate"]
        assert isinstance(item, dict)
        contexts = item["semantic_context_requirements"]
        assert isinstance(contexts, list) and isinstance(contexts[0], dict)
        contexts[0]["explanation"] = "A changed semantic context."
        receipt, error = self._build(
            raw, raw_bytes, current_map, _json_bytes(current_map), fingerprint
        )
        self.assertIsNone(receipt)
        self.assertIn("selected source content differs", error)

        raw, raw_bytes, current_map, _current_map_bytes, fingerprint = self._fixture()
        current_map["items"]["duplicate"] = copy.deepcopy(
            current_map["items"]["renamed_inventory_coordinate"]
        )
        receipt, error = self._build(
            raw, raw_bytes, current_map, _json_bytes(current_map), fingerprint
        )
        self.assertIsNone(receipt)
        self.assertIn("ambiguous duplicate", error)

    def test_rejects_non_map_fingerprint_feature_root_and_direct_ledger_changes(self) -> None:
        raw, raw_bytes, current_map, current_map_bytes, fingerprint = self._fixture()
        artifact_fingerprint = copy.deepcopy(fingerprint)
        artifact_fingerprint["source_artifact_identities"] = [
            {"path": "papers/Fixture/source.txt", "sha256": "d" * 64, "status": "present"}
        ]
        receipt, error = self._build(
            raw, raw_bytes, current_map, current_map_bytes, artifact_fingerprint
        )
        self.assertIsNone(receipt)
        self.assertIn("outside map provenance", error)

        feature_fingerprint = copy.deepcopy(fingerprint)
        feature_fingerprint["audit_engine_identities"] = [
            {"path": "generator", "surface_semantic_version": "v2"}
        ]
        receipt, error = self._build(
            raw, raw_bytes, current_map, current_map_bytes, feature_fingerprint
        )
        self.assertIsNone(receipt)
        self.assertIn("outside map provenance", error)

        receipt, error = self._build(
            raw,
            raw_bytes,
            current_map,
            current_map_bytes,
            fingerprint,
            roots=["Fixture.NewSourceMappedModel"],
        )
        self.assertIsNone(receipt)
        self.assertIn("source-premise root set", error)

        raw, raw_bytes, current_map, current_map_bytes, fingerprint = self._fixture(
            raw_roots=["Fixture.RemovedSourceMappedModel"]
        )
        receipt, error = self._build(
            raw,
            raw_bytes,
            current_map,
            current_map_bytes,
            fingerprint,
            roots=[],
        )
        self.assertIsNone(receipt)
        self.assertIn("source-premise root set", error)

        raw, raw_bytes, current_map, current_map_bytes, fingerprint = self._fixture(
            direct_ledger=["boundary::one"]
        )
        receipt, error = self._build(
            raw, raw_bytes, current_map, current_map_bytes, fingerprint, ledger=set()
        )
        self.assertIsNone(receipt)
        self.assertIn("direct statement ledger", error)

    def test_rejects_legacy_schema_from_selected_surface_rebind(self) -> None:
        """A v7 raw can use only its explicit legacy cache path, not a rebind."""

        raw, _raw_bytes, current_map, current_map_bytes, fingerprint = self._fixture()
        raw_fingerprint = raw["source_record_input_fingerprint"]
        assert isinstance(raw_fingerprint, dict)
        raw_fingerprint["schema"] = 7
        attach_source_record_audit_surface(raw, {})
        stamp_source_record_audit_integrity(raw)
        receipt, error = self._build(
            raw, _json_bytes(raw), current_map, current_map_bytes, fingerprint
        )
        self.assertIsNone(receipt)
        self.assertIn("outside map provenance", error)

    def test_rejects_tampered_receipt(self) -> None:
        raw, raw_bytes, current_map, current_map_bytes, fingerprint = self._fixture()
        receipt, error = self._build(
            raw, raw_bytes, current_map, current_map_bytes, fingerprint
        )
        self.assertEqual(error, "")
        assert receipt is not None
        manifest = receipt["dependency_manifest"]
        assert isinstance(manifest, dict)
        manifest["source_mapped_premise_roots"] = ["tampered"]
        self.assertIn(
            "stale receipt_sha256",
            REBIND.validate_selected_surface_rebind(
                receipt,
                paper=PAPER,
                raw_audit=raw,
                raw_audit_bytes=raw_bytes,
                raw_audit_relative_path="audit/source_record_audit.json",
                statement_map=current_map,
                statement_map_bytes=current_map_bytes,
                statement_map_relative_path="audit/paper_statement_map.json",
                current_input_fingerprint=fingerprint,
                current_routing={
                    "reachable_paper_interface_auxiliary_dependencies": [],
                    "unresolved_reachable_paper_interface_auxiliaries": [],
                    "ambiguous_reachable_paper_interface_auxiliary_references": [],
                    "reachable_paper_interface_auxiliary_quarantine_configuration_errors": [],
                },
                current_source_premise_roots=[],
                current_direct_ledger_keys=set(),
            ),
        )

    def test_summary_refresh_keeps_external_receipt_current(self) -> None:
        raw, raw_bytes, current_map, current_map_bytes, fingerprint = self._fixture()
        receipt, error = self._build(
            raw, raw_bytes, current_map, current_map_bytes, fingerprint
        )
        self.assertEqual(error, "")
        assert receipt is not None
        # These are the raw artifact's sanctioned derived-summary fields. A
        # real refresh restamps integrity after writing them; the semantic raw
        # evidence projection and aggregate digest remain unchanged.
        raw["current_source_record_judgment_count"] = 7
        raw["resolved_conclusion_dependency_count"] = 3
        raw["resolved_conclusion_dependency_items"] = [{"key": "derived"}]
        stamp_source_record_audit_integrity(raw)
        refreshed_bytes = _json_bytes(raw)
        self.assertEqual(
            REBIND.validate_selected_surface_rebind(
                receipt,
                paper=PAPER,
                raw_audit=raw,
                raw_audit_bytes=refreshed_bytes,
                raw_audit_relative_path="audit/source_record_audit.json",
                statement_map=current_map,
                statement_map_bytes=current_map_bytes,
                statement_map_relative_path="audit/paper_statement_map.json",
                current_input_fingerprint=fingerprint,
                current_routing={
                    "reachable_paper_interface_auxiliary_dependencies": [],
                    "unresolved_reachable_paper_interface_auxiliaries": [],
                    "ambiguous_reachable_paper_interface_auxiliary_references": [],
                    "reachable_paper_interface_auxiliary_quarantine_configuration_errors": [],
                },
                current_source_premise_roots=[],
                current_direct_ledger_keys=set(),
            ),
            "",
        )


class SelectedSurfaceRebindRuntimeTests(unittest.TestCase):
    def test_runtime_requires_a_revalidated_lean_owned_closure(self) -> None:
        root = Path("/fixture-repository")
        paper_dir = root / "papers" / PAPER
        interface = paper_dir / "PaperInterface.lean"
        closure = SimpleNamespace(sha256="a" * 64)
        provider = object()
        module = SimpleNamespace(
            review_source_path=Mock(return_value=interface),
            WorktreeImportClosureProvider=Mock(return_value=provider),
            source_record_lean_import_closure_for_paper=Mock(
                return_value=(closure, "")
            ),
        )
        raw = {
            "source_record_input_fingerprint": {
                "lean_import_closure_sha256": "a" * 64,
            }
        }
        with patch.object(REBIND, "_source_record_runtime_module", return_value=module):
            (
                actual_module,
                actual_interface,
                actual_closure,
                actual_provider,
                error,
            ) = REBIND._current_lean_import_closure_from_raw(
                root=root, paper_dir=paper_dir, raw_audit=raw
            )
        self.assertEqual(error, "")
        self.assertIs(actual_module, module)
        self.assertEqual(actual_interface, interface)
        self.assertIs(actual_closure, closure)
        self.assertIs(actual_provider, provider)
        module.source_record_lean_import_closure_for_paper.assert_called_once_with(
            root,
            paper_dir,
            provider=provider,
            saved_payload=raw,
            allow_live_lean_graph=False,
        )

    def test_canonical_closure_projection_has_no_text_import_fallback(self) -> None:
        root = Path("/fixture-repository")
        interface = root / "papers" / PAPER / "PaperInterface.lean"
        closure = object()
        module = SimpleNamespace(
            paper_interface_import_closure_lean_files=Mock(return_value=[interface]),
            source_record_lean_import_closure_source_text=Mock(
                return_value={interface.resolve(): "namespace Fixture"}
            ),
        )
        files, text, error = REBIND._canonical_lean_files_from_validated_closure(
            module,
            root=root,
            interface_path=interface,
            lean_import_closure=closure,
        )
        self.assertEqual(error, "")
        self.assertEqual(files, [interface.resolve()])
        self.assertEqual(text, {interface.resolve(): "namespace Fixture"})
        self.assertFalse(hasattr(module, "imported_paper_lean_files"))

        unavailable = SimpleNamespace(
            source_record_lean_import_closure_source_text=Mock(return_value={})
        )
        _files, _text, unavailable_error = (
            REBIND._canonical_lean_files_from_validated_closure(
                unavailable,
                root=root,
                interface_path=interface,
                lean_import_closure=closure,
            )
        )
        self.assertIn("could not project the validated Lean import closure", unavailable_error)

    def test_current_fingerprint_is_bound_to_the_validated_closure(self) -> None:
        root = Path("/fixture-repository")
        paper_dir = root / "papers" / PAPER
        closure = object()
        expected = {"paper": PAPER, "lean_import_closure_sha256": "a" * 64}
        module = SimpleNamespace(
            paper_statement_map_cache_receipts=Mock(
                return_value=("b" * 64, "c" * 64)
            ),
            source_record_input_fingerprint=Mock(return_value=expected),
        )
        fingerprint, error = REBIND._current_input_fingerprint(
            root=root,
            paper_dir=paper_dir,
            paper=PAPER,
            raw_audit={"source_record_input_fingerprint": {"max_depth": 4, "no_lean": False}},
            module=module,
            lean_import_closure=closure,
        )
        self.assertEqual(error, "")
        self.assertEqual(fingerprint, expected)
        self.assertIs(
            module.source_record_input_fingerprint.call_args.kwargs[
                "lean_import_closure"
            ],
            closure,
        )

    def test_auxiliary_routes_reuse_the_raw_elaborated_ledger(self) -> None:
        module = SimpleNamespace(
            explicitly_qualified_source_map_routes=Mock(
                return_value={
                    "Fixture.Auxiliary": [
                        {
                            "source_key": "renamed_inventory_coordinate",
                            "route_field": "support_lean_declarations",
                            "source_location": "source.txt:1-2",
                        }
                    ]
                }
            )
        )
        raw = {
            "reachable_paper_interface_auxiliary_dependencies": [
                {
                    "declaration": "Fixture.Auxiliary",
                    "transitively_referenced_from": [
                        {
                            "selected_declaration": "Fixture.endpoint",
                            "selected_review_rows": ["endpoint"],
                            "dependency_chain": ["Fixture.endpoint", "Fixture.Auxiliary"],
                        }
                    ],
                    "source_map_routes": [
                        {
                            "source_key": "old_inventory_coordinate",
                            "route_field": "support_lean_declarations",
                            "source_location": "source.txt:1-2",
                        }
                    ],
                    "quarantined": False,
                    "quarantine_source_reason": "",
                    "disposition": "explicit_source_map_route_or_support",
                }
            ],
            "unresolved_reachable_paper_interface_auxiliaries": [],
            "ambiguous_reachable_paper_interface_auxiliary_references": [],
            "reachable_paper_interface_auxiliary_quarantine_configuration_errors": [],
        }
        routing, error = REBIND._current_auxiliary_routing_from_validated_raw(
            module=module,
            paper_dir=Path("/fixture-repository") / "papers" / PAPER,
            raw_audit=raw,
        )
        self.assertEqual(error, "")
        dependency = routing["reachable_paper_interface_auxiliary_dependencies"][0]
        self.assertEqual(
            dependency["transitively_referenced_from"],
            raw["reachable_paper_interface_auxiliary_dependencies"][0][
                "transitively_referenced_from"
            ],
        )
        self.assertEqual(
            dependency["source_map_routes"][0]["source_key"],
            "renamed_inventory_coordinate",
        )
        self.assertFalse(hasattr(module, "reachable_paper_interface_auxiliary_routing"))


if __name__ == "__main__":
    unittest.main()
