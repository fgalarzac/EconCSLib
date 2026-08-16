#!/usr/bin/env python3
"""Regression tests for the narrow internal-derivational helper route."""

from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from typing import Any

from scripts.internal_derivational_auxiliary import (
    _DERIVATIONAL_AUXILIARY_RECEIPT_FILE,
    _DERIVATIONAL_AUXILIARY_RECEIPT_KIND,
    _DERIVATIONAL_AUXILIARY_RECEIPT_SCHEMA,
    _LEGACY_AUXILIARY_RECEIPT_SCHEMA,
    _TRANSPARENT_TERMINAL_RECEIPT_KIND,
    _TRANSPARENT_TERMINAL_RECEIPT_SCHEMA,
    _derivational_root_path_identity,
    _normalized_declaration_identity,
    _receipt_source_association,
    _terminal_route_identity,
    _transparent_terminal_record_identity,
    auxiliary_receipt_semantic_raw_binding,
    derivational_auxiliary_local_closure,
    derivational_auxiliary_local_closure_sha256,
    internal_derivational_auxiliary_resolution,
)
from scripts.source_record_integrity import stamp_source_record_audit_receipts
from scripts.source_record_target_disposition import (
    semantic_association_record_digest,
    source_contract_association_record_digest,
    source_map_item_record_digest,
)


def sha256(value: bytes | str) -> str:
    raw = value.encode("utf-8") if isinstance(value, str) else value
    return hashlib.sha256(raw).hexdigest()


class InternalDerivationalAuxiliaryTests(unittest.TestCase):
    def _fixture(
        self,
        directory: Path,
        *,
        helper_result: str = "0 ≤ 1",
        helper_extra_input: str = "",
        helper_condition_type: str = "∀ x, 0 ≤ density x",
        ambiguous_locator: bool = False,
        independently_selected: bool = False,
        source_association_schema: int = 2,
        schema1_outer_is_evidence: bool = False,
        schema2_outer_is_spec: bool = False,
        transparent_type_alias: bool = False,
    ) -> tuple[Path, dict[str, Any], dict[str, dict[str, Any]], dict[str, Any]]:
        folder = directory / "papers" / "Fixture"
        audit = folder / "audit"
        audit.mkdir(parents=True)
        if transparent_type_alias:
            (folder / "Carrier.lean").write_text(
                "namespace Fixture\n"
                "abbrev Carrier (n : ℕ) := Fin (n + 2)\n"
                "end Fixture\n",
                encoding="utf-8",
            )
        helper_inputs = (
            "(rate : ℝ) (density : ℝ → ℝ) "
            f"(density_nonneg : {helper_condition_type})"
            + helper_extra_input
        )
        root_prefix = "{n : ℕ} (carrier : Carrier n) " if transparent_type_alias else ""
        alias_import = "import Fixture.Carrier\n" if transparent_type_alias else ""
        extra_declaration = (
            "\nnamespace Other\ntheorem Helper : 0 ≤ 1 := by trivial\nend Other\n"
            if ambiguous_locator
            else ""
        )
        source = alias_import + (
            "namespace Fixture\n"
            f"theorem Root {root_prefix}(density : ℝ → ℝ) "
            "(density_nonneg : ∀ x, 0 ≤ density x) : True := by\n"
            "  trivial\n"
            f"abbrev RootSpec {root_prefix}(density : ℝ → ℝ) "
            "(density_nonneg : ∀ x, 0 ≤ density x) : Prop := True\n"
            f"theorem Helper {helper_inputs} : {helper_result} := by\n"
            "  trivial\n"
            "end Fixture\n"
        ) + extra_declaration
        interface = folder / "PaperInterface.lean"
        interface.write_text(source, encoding="utf-8")
        (folder / "status.json").write_text(
            json.dumps({"status": "formalized", "review_surface": {"auxiliary_names": ["Helper"]}}),
            encoding="utf-8",
        )

        # The resolver deliberately uses the production declaration parser,
        # but only on this one fixture interface file.
        from scripts.internal_derivational_auxiliary import _source_parser

        parser, error = _source_parser()
        assert parser is not None, error
        declarations = parser.parse_local_declarations(directory, [interface])
        by_name = {declaration.name: declaration for declaration in declarations}
        root = by_name["Fixture.Root"]
        root_spec = by_name["Fixture.RootSpec"]
        helper = by_name["Fixture.Helper"]
        root_inputs = parser.visible_inputs_from_declaration(root.source)
        root_names = {
            name
            for visible in root_inputs
            for name in parser.binder_names(visible["names"])
        }
        signature = {
            "qualified_declaration": root.name,
            "elaborated_signature_sha256": "b" * 64,
        }
        root_identity = {
            "qualified_declaration": root.name,
            "declaration_sha256": sha256(root.source),
        }
        root_spec_identity = {
            "qualified_declaration": root_spec.name,
            "declaration_sha256": sha256(root_spec.source),
        }
        map_payload: dict[str, Any] = {
            "items": {
                "source_claim": {
                    "source_kind": "theorem",
                    "source_location": "source.txt:10",
                    "source_status": "formalized source claim",
                    "lean_declarations": [root.name],
                    "semantic_contract": {
                        "evidence_declaration": root.name,
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                        "spec_declaration": f"{root.name}Spec",
                    },
                }
            }
        }
        map_path = audit / "paper_statement_map.json"
        map_path.write_text(json.dumps(map_payload, indent=2), encoding="utf-8")
        source_identity = parser.semantic_contract_source_identity(
            "source_claim", map_payload["items"]["source_claim"]
        )
        semantic_digest = semantic_association_record_digest(
            [source_identity["source_semantic_sha256"]], signature
        )
        if source_association_schema == 2:
            parent_association: dict[str, Any] = {
                "schema": 2,
                "role": (
                    "direct_evidence" if schema2_outer_is_spec else "direct_source_route"
                ),
                "semantic_association_sha256": semantic_digest,
                "reviewed_declaration_identity": root_identity,
                "reviewed_elaborated_signature_identity": signature,
                "source_item_identities": [source_identity],
            }
            if schema2_outer_is_spec:
                parent_association.update(
                    {
                        "review_scope": "individual_row_only",
                        "paired_qualified_declaration": root_spec.name,
                    }
                )
            boundary_association: dict[str, Any] = {
                "schema": 2,
                "association_mode": (
                    "semantic_contract_group_member"
                    if schema2_outer_is_spec
                    else "explicit_source_map_direct_route"
                ),
                "semantic_association_sha256": semantic_digest,
                "reviewed_declaration_identity": root_identity,
                "reviewed_elaborated_signature_identity": signature,
                "source_item_identities": [source_identity],
                "source_map_item_keys": ["source_claim"],
                "source_map_item_sha256_by_key": {
                    "source_claim": source_identity["source_map_item_sha256"]
                },
                "semantic_model_judgment_key": "semantic-model::root_row",
            }
            if schema2_outer_is_spec:
                boundary_association["semantic_contract_member_role"] = "direct_evidence"
        elif source_association_schema == 1:
            legacy_source_identity = {
                key: source_identity[key]
                for key in (
                    "source_key",
                    "source_location",
                    "source_kind",
                    "source_map_item_sha256",
                    "semantic_contract",
                )
            }
            parent_association = {
                "schema": 1,
                "role": "direct_evidence",
                "review_scope": "individual_row_only",
                "paired_qualified_declaration": f"{root.name}Spec",
                "reviewed_declaration_identity": root_identity,
                "source_item_identities": [legacy_source_identity],
            }
            boundary_association = {
                "schema": 1,
                "association_mode": "semantic_contract_group_member",
                "semantic_contract_member_role": "direct_evidence",
                "reviewed_declaration_identity": root_identity,
                "source_item_identities": [legacy_source_identity],
                "source_map_item_keys": ["source_claim"],
                "source_map_item_sha256_by_key": {
                    "source_claim": source_identity["source_map_item_sha256"]
                },
                "semantic_model_judgment_key": "semantic-model::root_row",
            }
        else:
            raise ValueError("unsupported source association schema")
        boundary_association["source_map_item_keys_sha256"] = (
            source_map_item_record_digest(["source_claim"])
        )
        boundary_association["association_sha256"] = source_contract_association_record_digest(
            boundary_association
        )
        condition = next(
            raw_input
            for raw_input in root_inputs
            if raw_input["type"].startswith("∀")
        )
        condition_key = f"root_row.{condition['names']} : {condition['type']}"
        target_item: dict[str, Any] = {
            "configuration": "configured_auxiliary",
            "declaration": helper.name,
            "disposition": "missing_source_map_route_or_quarantine",
            "kind": helper.kind,
            "line": helper.line,
            "quarantined": False,
            "quarantine_source_reason": "",
            "source_file": "papers/Fixture/PaperInterface.lean",
            "source_map_routes": [],
            "transitively_referenced_from": [
                {
                    "selected_declaration": root.name,
                    "selected_review_rows": ["root_row"],
                    "dependency_chain": [root.name, helper.name],
                }
            ],
        }
        parent_item: dict[str, Any] = {
            "row": "root_row",
            "qualified_declaration": root.name,
            "reviewed_declaration_identity": (
                root_identity
                if (
                    (source_association_schema == 1 and schema1_outer_is_evidence)
                    or (source_association_schema == 2 and not schema2_outer_is_spec)
                )
                else root_spec_identity
            ),
            "expanded_lean_surface": {
                "binder_domains": [
                    {
                        "alpha_normalized_type": parser.abstract_free_identifiers(
                            raw_input["type"], root_names
                        )
                    }
                    for raw_input in root_inputs
                ]
            },
        }
        if source_association_schema == 2:
            parent_item["source_statement_association"] = parent_association
        else:
            parent_item["semantic_contract_source_association"] = parent_association
        if transparent_type_alias:
            carrier_input = next(
                raw_input for raw_input in root_inputs if raw_input["names"] == "carrier"
            )
            carrier_domain = next(
                domain
                for domain in parent_item["expanded_lean_surface"]["binder_domains"]
                if domain["alpha_normalized_type"]
                == parser.abstract_free_identifiers(carrier_input["type"], root_names)
            )
            carrier_domain["alpha_normalized_type"] = parser.abstract_free_identifiers(
                "Fin (n + 2)", root_names
            )
        semantic_items = [parent_item]
        if independently_selected:
            semantic_items.append({"row": "helper_row", "qualified_declaration": helper.name})
        payload: dict[str, Any] = {
            "paper": "Fixture",
            "prompt_version": "source-record-v10-semantic-conclusion-boundary-contract",
            "paper_statement_map_sha256": sha256(map_path.read_bytes()),
            "review_interface_source": {
                "path": "papers/Fixture/PaperInterface.lean",
                "sha256": sha256(interface.read_bytes()),
            },
            "available_local_lean_declarations": [declaration.name for declaration in declarations],
            "configured_review_rows": [{"row": "root_row"}],
            "reachable_paper_interface_auxiliary_dependencies": [target_item],
            "unresolved_reachable_paper_interface_auxiliaries": [target_item],
            "semantic_model_items": semantic_items,
            "row_visible_inputs": {"root_row": root_inputs},
            "boundary_input_items": [
                {
                    "row": "root_row",
                    "input": condition,
                    "judgment_key": condition_key,
                    "source_contract_association": boundary_association,
                }
            ],
            "source_proof_fidelity": {"schema": 2, "model_conventions": []},
        }
        judgments = {
            condition_key: {
                "classification": "validated_source_assumption",
                "source_location": "source.txt:10",
                "source_target_disposition": "literal_source_match",
                "semantic_association_sha256": semantic_digest,
                "source_contract_association_sha256": boundary_association[
                    "association_sha256"
                ],
                "source_map_item_keys": ["source_claim"],
                "source_map_item_sha256_by_key": {
                    "source_claim": source_identity["source_map_item_sha256"]
                },
            }
        }
        return folder, payload, judgments, target_item

    def _resolution(self, folder: Path, payload: dict[str, Any], judgments: dict[str, dict[str, Any]], item: dict[str, Any]):
        return internal_derivational_auxiliary_resolution(
            "Fixture",
            folder,
            payload,
            item,
            judgments,
            current_judgment_keys=set(judgments),
        )

    @staticmethod
    def _write_authenticated_raw_audit(
        folder: Path, payload: dict[str, Any]
    ) -> dict[str, Any]:
        """Write a raw fixture with the production aggregate/integrity receipts."""

        stored = {
            key: value for key, value in payload.items() if key != "_other_terminal"
        }
        stamp_source_record_audit_receipts(stored)
        payload.update(stored)
        raw_path = folder / "audit" / "source_record_audit.json"
        raw_path.write_text(
            json.dumps(stored, indent=2, sort_keys=True), encoding="utf-8"
        )
        return stored

    def _install_current_root_semantic_review(
        self, payload: dict[str, Any], judgments: dict[str, dict[str, Any]]
    ) -> str:
        """Install one content-pinned root review without using its storage key as proof."""

        parent = payload["semantic_model_items"][0]
        assert isinstance(parent, dict)
        association = parent.pop("source_statement_association")
        assert isinstance(association, dict)
        source_identity = association["source_item_identities"][0]
        assert isinstance(source_identity, dict)
        association.update(
            {
                "role": "direct_evidence",
                "review_scope": "individual_row_only",
                "paired_qualified_declaration": "Fixture.RootSpec",
            }
        )
        parent["semantic_contract_source_association"] = association

        review_key = "opaque-root-review-storage-coordinate"
        item_digest = sha256("fixture root semantic item")
        parent.update(
            {
                "judgment_key": review_key,
                "kind": "semantic_model_comparison",
                "dimensions": [
                    {
                        "id": "expanded_binders_and_domain",
                        "detected_from_expanded_surface": True,
                        "expanded_shape_basis": ["fixture expanded binder surface"],
                        "required_check": "compare every visible root binder",
                    }
                ],
                "source_record_item_reuse_eligibility": {
                    "eligible": True,
                    "blockers": [],
                },
                "source_record_item_digest_schema": 5,
                "source_record_item_semantic_id": sha256("fixture root semantic id"),
                "source_record_item_context_sha256": sha256("fixture root context"),
                "source_record_item_sha256": item_digest,
                "reviewed_elaborated_signature_identities": [
                    association["reviewed_elaborated_signature_identity"]
                ],
            }
        )
        payload["source_record_audit_sha256"] = sha256("fixture current raw audit")
        judgments[review_key] = {
            "classification": "semantic_model_review",
            "prompt_version": payload["prompt_version"],
            "source_record_audit_sha256": payload["source_record_audit_sha256"],
            "source_record_item_digest_schema": 5,
            "source_record_item_sha256": item_digest,
            "source_record_item_sha256s": [
                {
                    "kind": "semantic_model_comparison",
                    "source_record_item_digest_schema": 5,
                    "source_record_item_sha256": item_digest,
                }
            ],
            "semantic_model_dimensions": {
                "expanded_binders_and_domain": {
                    "verdict": "matches_literal_source",
                    "source_locator": "source.txt:10",
                    "semantic_comparison": (
                        "The reviewed source premise and expanded root binder agree."
                    ),
                    "lean_evidence": "PaperInterface.lean:3 exposes the binder.",
                    "source_target_disposition": "literal_source_match",
                    "semantic_association_sha256": association[
                        "semantic_association_sha256"
                    ],
                    "source_map_item_keys": [source_identity["source_key"]],
                }
            },
        }
        return review_key

    @staticmethod
    def _remove_boundary_judgment(
        payload: dict[str, Any], judgments: dict[str, dict[str, Any]]
    ) -> None:
        boundary = payload["boundary_input_items"][0]
        assert isinstance(boundary, dict)
        key = boundary["judgment_key"]
        assert isinstance(key, str)
        judgments.pop(key)

    def _terminal_fixture(
        self, directory: Path
    ) -> tuple[Path, dict[str, Any], dict[str, dict[str, Any]], dict[str, Any], Path]:
        """Build a receipt-bound transparent terminal surface without Lean names as authority."""

        folder = directory / "papers" / "Fixture"
        audit = folder / "audit"
        audit.mkdir(parents=True)
        source = (
            "namespace Fixture\n"
            "abbrev Terminal : Prop := ∃ x : ℝ, x = x\n"
            "abbrev OtherTerminal : Prop := ∃ x : ℝ, x = x\n"
            "theorem Root : Terminal := by\n"
            "  exact ⟨0, rfl⟩\n"
            "end Fixture\n"
        )
        interface = folder / "PaperInterface.lean"
        interface.write_text(source, encoding="utf-8")
        (folder / "status.json").write_text(
            json.dumps(
                {
                    "status": "partially formalized",
                    "review_surface": {"auxiliary_names": ["Terminal", "OtherTerminal"]},
                }
            ),
            encoding="utf-8",
        )
        from scripts.internal_derivational_auxiliary import _source_parser

        parser, error = _source_parser()
        assert parser is not None, error
        declarations = parser.parse_local_declarations(directory, [interface])
        by_name = {declaration.name: declaration for declaration in declarations}
        root = by_name["Fixture.Root"]
        terminal = by_name["Fixture.Terminal"]
        other_terminal = by_name["Fixture.OtherTerminal"]
        root_identity = {
            "qualified_declaration": root.name,
            "declaration_sha256": sha256(root.source),
        }
        map_payload: dict[str, Any] = {
            "items": {
                "source_claim": {
                    "source_kind": "theorem",
                    "source_location": "source.txt:10",
                    "lean_declarations": [root.name],
                    "semantic_contract": {
                        "evidence_declaration": root.name,
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                        "spec_declaration": root.name,
                    },
                }
            }
        }
        map_path = audit / "paper_statement_map.json"
        map_path.write_text(json.dumps(map_payload, indent=2), encoding="utf-8")
        source_identity = parser.semantic_contract_source_identity(
            "source_claim", map_payload["items"]["source_claim"]
        )
        signature = {
            "qualified_declaration": root.name,
            "elaborated_signature_sha256": "c" * 64,
        }
        semantic_digest = semantic_association_record_digest(
            [source_identity["source_semantic_sha256"]], signature
        )
        association = {
            "schema": 2,
            "role": "direct_source_route",
            "semantic_association_sha256": semantic_digest,
            "reviewed_declaration_identity": root_identity,
            "reviewed_elaborated_signature_identity": signature,
            "source_item_identities": [source_identity],
        }
        target_record = {
            "declaration": terminal.name,
            "kind": terminal.kind,
            "source_file": terminal.source_file,
            "line": terminal.line,
            "declaration_sha256": sha256(parser.normalize_ws(terminal.source)),
            "body_sha256": sha256(
                parser.normalize_ws(parser.declaration_body_text(terminal.source))
            ),
            "result_type": {"expanded_type": "Prop"},
            "body_surface_inspectable": True,
            "semantic_relevant": True,
            "semantic_construct_flags": {
                "finite_carrier_construct": True,
                "finite_or_ordered_probability_construct": True,
                "integration_or_expectation_construct": True,
                "model_semantics": True,
                "nontrivial_finite_index_expression_construct": True,
                "probability_law_construct": True,
            },
            "direct_local_dependencies": [],
            "dependency_chain": [root.name, terminal.name],
        }
        route = {
            "selected_declaration": root.name,
            "selected_review_rows": ["root_row"],
            "dependency_chain": [root.name, terminal.name],
        }
        target_item = {
            "configuration": "configured_auxiliary",
            "declaration": terminal.name,
            "disposition": "missing_source_map_route_or_quarantine",
            "kind": terminal.kind,
            "line": terminal.line,
            "quarantined": False,
            "quarantine_source_reason": "",
            "source_file": terminal.source_file,
            "source_map_routes": [],
            "transitively_referenced_from": [route],
        }
        parent = {
            "row": "root_row",
            "qualified_declaration": root.name,
            "reviewed_declaration_identity": root_identity,
            "source_statement_association": association,
            "expanded_lean_surface": {
                "terminal_term_dependency_surface": {
                    "scan_complete": True,
                    "incomplete_reasons": [],
                    "transparent_definitions": [target_record],
                    "unexpanded_local_term_heads": [],
                }
            },
        }
        payload: dict[str, Any] = {
            "paper": "Fixture",
            "prompt_version": "source-record-v10-semantic-conclusion-boundary-contract",
            "source_record_audit_sha256": "d" * 64,
            "paper_statement_map_sha256": sha256(map_path.read_bytes()),
            "review_interface_source": {
                "path": "papers/Fixture/PaperInterface.lean",
                "sha256": sha256(interface.read_bytes()),
            },
            "available_local_lean_declarations": [declaration.name for declaration in declarations],
            "configured_review_rows": [
                {"row": "root_row", "qualified_declaration": root.name}
            ],
            "reachable_paper_interface_auxiliary_dependencies": [target_item],
            "unresolved_reachable_paper_interface_auxiliaries": [target_item],
            "semantic_model_items": [parent],
            "row_visible_inputs": {"root_row": []},
            "boundary_input_items": [],
        }
        judgments = {
            "semantic-model::root_row": {
                "classification": "semantic_model_review",
                "prompt_version": "source-record-v10-semantic-conclusion-boundary-contract",
            }
        }
        raw_path = audit / "source_record_audit.json"
        raw_path.write_text(json.dumps(payload, indent=2, sort_keys=True), encoding="utf-8")
        receipt_path = audit / "source_record_transparent_terminal_surface_receipt.json"
        receipt = {
            "schema": 1,
            "kind": "paper_specific_transparent_terminal_surface",
            "paper": "Fixture",
            "raw_source_record": {
                "source_record_audit_sha256": payload["source_record_audit_sha256"],
                "file_sha256": sha256(raw_path.read_bytes()),
                "prompt_version": payload["prompt_version"],
                "paper_statement_map_sha256": payload["paper_statement_map_sha256"],
                "paper_interface_sha256": payload["review_interface_source"]["sha256"],
            },
            "entries": [
                {
                    "declaration": terminal.name,
                    "target_identity": _normalized_declaration_identity(parser, terminal),
                    "transparent_definition": _transparent_terminal_record_identity(
                        target_record
                    ),
                    "root_paths": [
                        _terminal_route_identity(
                            route,
                            parent,
                            judgment_key="semantic-model::root_row",
                            transparent_definition_chain=[root.name, terminal.name],
                        )
                    ],
                }
            ],
        }
        receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True), encoding="utf-8")
        # Keep an easy coordinate for the unrelated-abbrev negative case.
        payload["_other_terminal"] = {
            "declaration": other_terminal.name,
            "kind": other_terminal.kind,
            "line": other_terminal.line,
            "source_file": other_terminal.source_file,
        }
        return folder, payload, judgments, target_item, receipt_path

    def _refresh_terminal_raw_binding(
        self, folder: Path, payload: dict[str, Any], receipt_path: Path
    ) -> None:
        """Simulate a fresh raw replay while deliberately retaining an old receipt."""

        raw_path = folder / "audit" / "source_record_audit.json"
        stored = {key: value for key, value in payload.items() if key != "_other_terminal"}
        raw_path.write_text(json.dumps(stored, indent=2, sort_keys=True), encoding="utf-8")
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        receipt["raw_source_record"]["file_sha256"] = sha256(raw_path.read_bytes())
        receipt["raw_source_record"]["source_record_audit_sha256"] = stored[
            "source_record_audit_sha256"
        ]
        receipt["raw_source_record"]["paper_statement_map_sha256"] = stored[
            "paper_statement_map_sha256"
        ]
        receipt["raw_source_record"]["paper_interface_sha256"] = stored[
            "review_interface_source"
        ]["sha256"]
        receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True), encoding="utf-8")

    def _write_schema2_terminal_receipt(
        self, folder: Path, payload: dict[str, Any], receipt_path: Path
    ) -> None:
        """Upgrade the fixture's terminal receipt to the semantic raw binding."""

        self._write_authenticated_raw_audit(folder, payload)
        binding, binding_error = auxiliary_receipt_semantic_raw_binding(
            payload, receipt_kind=_TRANSPARENT_TERMINAL_RECEIPT_KIND
        )
        assert binding is not None, binding_error
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        receipt["schema"] = _TRANSPARENT_TERMINAL_RECEIPT_SCHEMA
        receipt["raw_source_record"] = binding
        receipt_path.write_text(
            json.dumps(receipt, indent=2, sort_keys=True), encoding="utf-8"
        )

    def _write_derivational_receipt(
        self,
        folder: Path,
        payload: dict[str, Any],
        judgments: dict[str, dict[str, Any]],
        item: dict[str, Any],
    ) -> Path:
        """Opt a fixture into the exact proof-body/closure receipt lane."""

        judgments["semantic-model::root_row"] = {
            "classification": "semantic_model_review",
            "prompt_version": payload["prompt_version"],
        }
        audit = folder / "audit"
        self._write_authenticated_raw_audit(folder, payload)
        from scripts.internal_derivational_auxiliary import _source_parser

        parser, error = _source_parser()
        assert parser is not None, error
        interface = folder / "PaperInterface.lean"
        declarations = parser.parse_local_declarations(folder.parents[1], [interface])
        by_name = {declaration.name: declaration for declaration in declarations}
        target = by_name[item["declaration"]]
        closure, closure_error = derivational_auxiliary_local_closure(
            parser, declarations, target.name
        )
        assert closure is not None, closure_error
        parent = payload["semantic_model_items"][0]
        assert isinstance(parent, dict)
        association = _receipt_source_association(parent, None)
        assert association is not None
        route = item["transitively_referenced_from"][0]
        assert isinstance(route, dict)
        binding, binding_error = auxiliary_receipt_semantic_raw_binding(
            payload, receipt_kind=_DERIVATIONAL_AUXILIARY_RECEIPT_KIND
        )
        assert binding is not None, binding_error
        receipt = {
            "schema": _DERIVATIONAL_AUXILIARY_RECEIPT_SCHEMA,
            "kind": _DERIVATIONAL_AUXILIARY_RECEIPT_KIND,
            "paper": "Fixture",
            "complete_for_current_raw": True,
            "raw_source_record": binding,
            "entries": [
                {
                    "declaration": target.name,
                    "target_identity": _normalized_declaration_identity(parser, target),
                    "local_lexical_closure": closure,
                    "local_lexical_closure_sha256": (
                        derivational_auxiliary_local_closure_sha256(closure)
                    ),
                    "root_paths": [
                        _derivational_root_path_identity(
                            route,
                            parent,
                            judgment_key="semantic-model::root_row",
                            association=association,
                        )
                    ],
                }
            ],
        }
        receipt_path = audit / _DERIVATIONAL_AUXILIARY_RECEIPT_FILE
        receipt_path.write_text(
            json.dumps(receipt, indent=2, sort_keys=True), encoding="utf-8"
        )
        return receipt_path

    def _refresh_derivational_raw_binding(
        self, folder: Path, payload: dict[str, Any], receipt_path: Path
    ) -> None:
        self._write_authenticated_raw_audit(folder, payload)
        binding, binding_error = auxiliary_receipt_semantic_raw_binding(
            payload, receipt_kind=_DERIVATIONAL_AUXILIARY_RECEIPT_KIND
        )
        assert binding is not None, binding_error
        receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
        receipt["raw_source_record"] = binding
        receipt_path.write_text(
            json.dumps(receipt, indent=2, sort_keys=True), encoding="utf-8"
        )

    def test_accepts_exact_paper_specific_transparent_terminal_surface(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item, _ = self._terminal_fixture(Path(tmp))
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertTrue(resolution.accepted, resolution.reason)

    def test_accepts_schema2_terminal_receipt_after_unrelated_raw_reissue(self) -> None:
        """Schema 2 does not bind a terminal route to unrelated raw bytes."""

        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item, receipt_path = self._terminal_fixture(
                Path(tmp)
            )
            self._write_schema2_terminal_receipt(folder, payload, receipt_path)
            raw_path = folder / "audit" / "source_record_audit.json"
            before = raw_path.read_bytes()
            payload["current_source_record_judgment_count"] = 7
            self._write_authenticated_raw_audit(folder, payload)
            self.assertNotEqual(raw_path.read_bytes(), before)
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertTrue(resolution.accepted, resolution.reason)

    def test_schema2_terminal_rejects_relevant_raw_route_drift(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item, receipt_path = self._terminal_fixture(
                Path(tmp)
            )
            self._write_schema2_terminal_receipt(folder, payload, receipt_path)
            route = item["transitively_referenced_from"][0]
            assert isinstance(route, dict)
            route["dependency_chain"] = ["Fixture.Root", "Fixture.Changed"]
            self._write_authenticated_raw_audit(folder, payload)
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("semantic raw dependency manifest is not current", resolution.reason)

    def test_schema2_terminal_rejects_unauthenticated_raw_mutation(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item, receipt_path = self._terminal_fixture(
                Path(tmp)
            )
            self._write_schema2_terminal_receipt(folder, payload, receipt_path)
            raw_path = folder / "audit" / "source_record_audit.json"
            raw = json.loads(raw_path.read_text(encoding="utf-8"))
            raw["unreviewed_mutation"] = True
            raw_path.write_text(json.dumps(raw, indent=2, sort_keys=True), encoding="utf-8")
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("raw source-record audit integrity is invalid", resolution.reason)

    def test_schema1_terminal_remains_byte_exact(self) -> None:
        """Legacy receipts retain their historical whole-raw-file behavior."""

        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item, receipt_path = self._terminal_fixture(
                Path(tmp)
            )
            receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
            self.assertEqual(receipt["schema"], _LEGACY_AUXILIARY_RECEIPT_SCHEMA)
            payload["current_source_record_judgment_count"] = 7
            stored = {
                key: value for key, value in payload.items() if key != "_other_terminal"
            }
            (folder / "audit" / "source_record_audit.json").write_text(
                json.dumps(stored, indent=2, sort_keys=True), encoding="utf-8"
            )
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("raw source-record binding differs from current bytes", resolution.reason)

    def test_lexical_derivational_receipt_lane_is_retired(self) -> None:
        """Only Lean-owned dependency receipts may grant closeout credit."""

        from scripts.internal_derivational_auxiliary import _source_parser

        parser, error = _source_parser()
        self.assertIsNotNone(parser, error)
        self.assertFalse(
            callable(getattr(parser, "_local_declaration_reference_edges", None))
        )
        scripts_dir = Path(__file__).resolve().parents[1]
        for consumer in (
            "audit_conclusion_provenance.py",
            "audit_evidence_integrity.py",
            "audit_repository.py",
        ):
            source = (scripts_dir / consumer).read_text(encoding="utf-8")
            self.assertNotIn("internal_derivational_auxiliary", source)

    def test_rejects_transparent_terminal_body_drift(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item, receipt_path = self._terminal_fixture(Path(tmp))
            interface = folder / "PaperInterface.lean"
            interface.write_text(
                interface.read_text(encoding="utf-8").replace("x = x", "x = 0"),
                encoding="utf-8",
            )
            payload["review_interface_source"]["sha256"] = sha256(interface.read_bytes())
            self._refresh_terminal_raw_binding(folder, payload, receipt_path)
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("target declaration/body identity", resolution.reason)

    def test_rejects_incomplete_transparent_terminal_scan(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item, receipt_path = self._terminal_fixture(Path(tmp))
            terminal_surface = payload["semantic_model_items"][0]["expanded_lean_surface"][
                "terminal_term_dependency_surface"
            ]
            terminal_surface["scan_complete"] = False
            terminal_surface["incomplete_reasons"] = ["depth_limit"]
            self._refresh_terminal_raw_binding(folder, payload, receipt_path)
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("complete terminal dependency scan", resolution.reason)

    def test_rejects_unexpanded_head_in_terminal_target_closure(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item, receipt_path = self._terminal_fixture(Path(tmp))
            terminal_surface = payload["semantic_model_items"][0]["expanded_lean_surface"][
                "terminal_term_dependency_surface"
            ]
            target_record = terminal_surface["transparent_definitions"][0]
            target_record["direct_local_dependencies"] = ["Fixture.HiddenModel"]
            terminal_surface["unexpanded_local_term_heads"] = [
                {
                    "declaration": "Fixture.HiddenModel",
                    "kind": "opaque",
                    "reason": "unexpanded_local_opaque_term_head",
                    "dependency_chain": [
                        item["declaration"],
                        "Fixture.HiddenModel",
                    ],
                    "referenced_from": item["declaration"],
                }
            ]
            self._refresh_terminal_raw_binding(folder, payload, receipt_path)
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("target closure reaches an unexpanded local head", resolution.reason)

    def test_allows_unexpanded_head_outside_terminal_target_closure(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item, receipt_path = self._terminal_fixture(Path(tmp))
            terminal_surface = payload["semantic_model_items"][0]["expanded_lean_surface"][
                "terminal_term_dependency_surface"
            ]
            terminal_surface["unexpanded_local_term_heads"] = [
                {
                    "declaration": "Fixture.UnrelatedOpaque",
                    "kind": "opaque",
                    "reason": "unexpanded_local_opaque_term_head",
                    "dependency_chain": ["Fixture.Unrelated", "Fixture.UnrelatedOpaque"],
                    "referenced_from": "Fixture.Unrelated",
                }
            ]
            self._refresh_terminal_raw_binding(folder, payload, receipt_path)
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertTrue(resolution.accepted, resolution.reason)

    def test_rejects_terminal_without_full_model_payoff_surface(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item, receipt_path = self._terminal_fixture(Path(tmp))
            record = payload["semantic_model_items"][0]["expanded_lean_surface"][
                "terminal_term_dependency_surface"
            ]["transparent_definitions"][0]
            record["semantic_construct_flags"]["model_semantics"] = False
            self._refresh_terminal_raw_binding(folder, payload, receipt_path)
            receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
            receipt["entries"][0]["transparent_definition"][
                "semantic_construct_flags"
            ]["model_semantics"] = False
            receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("fully expanded model/payoff surface", resolution.reason)

    def test_rejects_terminal_source_association_drift(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item, receipt_path = self._terminal_fixture(Path(tmp))
            association = payload["semantic_model_items"][0][
                "source_statement_association"
            ]
            assert isinstance(association, dict)
            source_identities = association["source_item_identities"]
            assert isinstance(source_identities, list)
            assert isinstance(source_identities[0], dict)
            source_identities[0]["source_location"] = "different-source.txt:99"
            self._refresh_terminal_raw_binding(folder, payload, receipt_path)
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("source-map identity", resolution.reason)

    def test_rejects_terminal_receipt_with_missing_root_path(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item, receipt_path = self._terminal_fixture(Path(tmp))
            receipt = json.loads(receipt_path.read_text(encoding="utf-8"))
            receipt["entries"][0]["root_paths"] = []
            receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("complete selected-root path list", resolution.reason)

    def test_does_not_authorize_unrelated_abbrev(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item, _ = self._terminal_fixture(Path(tmp))
            other = payload["_other_terminal"]
            unrelated_item = dict(item)
            unrelated_item.update(other)
            resolution = self._resolution(folder, payload, judgments, unrelated_item)
        self.assertFalse(resolution.accepted)

    def test_accepts_one_byte_pinned_internal_derived_fact(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(Path(tmp))
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertTrue(resolution.accepted, resolution.reason)

    def test_accepts_current_root_semantic_review_for_exact_visible_premise(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(Path(tmp))
            self._install_current_root_semantic_review(payload, judgments)
            self._remove_boundary_judgment(payload, judgments)
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertTrue(resolution.accepted, resolution.reason)

    def test_accepts_item_pinned_root_review_after_unrelated_aggregate_reissue(self) -> None:
        """Root-review freshness follows the shared complete-item-pin policy."""

        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(Path(tmp))
            review_key = self._install_current_root_semantic_review(payload, judgments)
            self._remove_boundary_judgment(payload, judgments)
            judgments[review_key]["source_record_audit_sha256"] = "0" * 64
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertTrue(resolution.accepted, resolution.reason)

    def test_rejects_missing_root_semantic_review_for_missing_boundary_judgment(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(Path(tmp))
            self._remove_boundary_judgment(payload, judgments)
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("no current semantic-model review", resolution.reason)

    def test_rejects_root_semantic_review_without_complete_content_pins(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(Path(tmp))
            review_key = self._install_current_root_semantic_review(payload, judgments)
            self._remove_boundary_judgment(payload, judgments)
            judgments[review_key].pop("source_record_item_sha256s")
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("complete raw content pin", resolution.reason)

    def test_rejects_root_semantic_review_with_changed_content_pin(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(Path(tmp))
            review_key = self._install_current_root_semantic_review(payload, judgments)
            self._remove_boundary_judgment(payload, judgments)
            judgments[review_key]["source_record_item_sha256"] = "0" * 64
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("not pinned to the current raw semantic item", resolution.reason)

    def test_rejects_root_review_when_helper_input_is_not_exact_visible_premise(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(
                Path(tmp), helper_condition_type="∀ x, 0 < density x"
            )
            self._install_current_root_semantic_review(payload, judgments)
            self._remove_boundary_judgment(payload, judgments)
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("exact current selected-root visible premise", resolution.reason)

    def test_rejects_root_review_with_stale_source_semantic_pin(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(Path(tmp))
            review_key = self._install_current_root_semantic_review(payload, judgments)
            self._remove_boundary_judgment(payload, judgments)
            response = judgments[review_key]["semantic_model_dimensions"]
            assert isinstance(response, dict)
            expanded = response["expanded_binders_and_domain"]
            assert isinstance(expanded, dict)
            expanded["semantic_association_sha256"] = "0" * 64
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("source-semantic association", resolution.reason)

    def test_does_not_replace_an_invalid_boundary_route_with_root_review(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(Path(tmp))
            self._install_current_root_semantic_review(payload, judgments)
            boundary = payload["boundary_input_items"][0]
            assert isinstance(boundary, dict)
            association = boundary["source_contract_association"]
            assert isinstance(association, dict)
            association["semantic_association_sha256"] = "0" * 64
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("not tied to the selected root", resolution.reason)

    def test_accepts_schema1_direct_semantic_contract_association(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(
                Path(tmp), source_association_schema=1
            )
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertTrue(resolution.accepted, resolution.reason)

    def test_accepts_schema1_evidence_row_without_expanded_binder_receipt(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(
                Path(tmp),
                source_association_schema=1,
                schema1_outer_is_evidence=True,
            )
            payload["semantic_model_items"][0].pop("expanded_lean_surface")
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertTrue(resolution.accepted, resolution.reason)

    def test_accepts_schema2_evidence_boundary_with_transparent_spec_review(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(
                Path(tmp), schema2_outer_is_spec=True
            )
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertTrue(resolution.accepted, resolution.reason)

    def test_rejects_schema2_boundary_with_changed_direct_endpoint_identity(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(
                Path(tmp), schema2_outer_is_spec=True
            )
            boundary = payload["boundary_input_items"][0]["source_contract_association"]
            assert isinstance(boundary, dict)
            identity = boundary["reviewed_declaration_identity"]
            assert isinstance(identity, dict)
            boundary["reviewed_declaration_identity"] = {
                **identity,
                "declaration_sha256": "0" * 64,
            }
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("authenticated direct source endpoint", resolution.reason)

    def test_rejects_schema2_unpaired_transparent_review_identity(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(
                Path(tmp), schema2_outer_is_spec=True
            )
            parent = payload["semantic_model_items"][0]
            parent["reviewed_declaration_identity"] = {
                "qualified_declaration": "Fixture.Unpaired",
                "declaration_sha256": "1" * 64,
            }
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("source endpoint pair", resolution.reason)

    def test_rejects_changed_schema2_transparent_spec_endpoint(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(
                Path(tmp), schema2_outer_is_spec=True
            )
            interface = folder / "PaperInterface.lean"
            interface.write_text(
                interface.read_text(encoding="utf-8").replace(
                    "(density_nonneg : ∀ x, 0 ≤ density x) : Prop := True",
                    "(density_nonneg : ∀ x, 0 ≤ density x) : Prop := False",
                    1,
                ),
                encoding="utf-8",
            )
            payload["review_interface_source"]["sha256"] = sha256(interface.read_bytes())
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("endpoint declaration bytes changed", resolution.reason)

    def test_accepts_current_transparent_type_alias_expansion(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(
                Path(tmp), transparent_type_alias=True
            )
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertTrue(resolution.accepted, resolution.reason)

    def test_rejects_changed_transparent_type_alias_expansion(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(
                Path(tmp), transparent_type_alias=True
            )
            (folder / "Carrier.lean").write_text(
                "namespace Fixture\n"
                "abbrev Carrier (n : ℕ) := Fin (n + 3)\n"
                "end Fixture\n",
                encoding="utf-8",
            )
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("transparent expanded binder signature", resolution.reason)

    def test_rejects_schema1_source_identity_drift(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(
                Path(tmp), source_association_schema=1
            )
            association = payload["semantic_model_items"][0][
                "semantic_contract_source_association"
            ]
            assert isinstance(association, dict)
            source_identities = association["source_item_identities"]
            assert isinstance(source_identities, list)
            assert isinstance(source_identities[0], dict)
            source_identities[0]["source_location"] = "other-source.txt:1"
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("source-map identity", resolution.reason)

    def test_ignores_unrelated_same_terminal_name(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(
                Path(tmp), ambiguous_locator=True
            )
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertTrue(resolution.accepted, resolution.reason)

    def test_rejects_independently_selected_helper(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(
                Path(tmp), independently_selected=True
            )
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("independently selected", resolution.reason)

    def test_rejects_package_shaped_result(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(
                Path(tmp), helper_result="Nonempty (Subtype fun x : ℝ => 0 ≤ x)"
            )
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("non-package proposition", resolution.reason)

    def test_rejects_new_source_sensitive_input(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(
                Path(tmp), helper_extra_input=" (extra_nonneg : 0 ≤ rate)"
            )
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("selected-root visible premise", resolution.reason)

    def test_rejects_frozen_map_or_interface_drift(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(Path(tmp))
            (folder / "audit" / "paper_statement_map.json").write_text("{}\n", encoding="utf-8")
            resolution = self._resolution(folder, payload, judgments, item)
            self.assertFalse(resolution.accepted)
            self.assertIn("map hash", resolution.reason)

            folder, payload, judgments, item = self._fixture(Path(tmp) / "second")
            with (folder / "PaperInterface.lean").open("a", encoding="utf-8") as handle:
                handle.write("\n")
            resolution = self._resolution(folder, payload, judgments, item)
        self.assertFalse(resolution.accepted)
        self.assertIn("source hash", resolution.reason)

    def test_ignores_duck_typed_association_transport(self) -> None:
        """Only the receipt validator's in-memory authority may rebind data."""

        with tempfile.TemporaryDirectory() as tmp:
            folder, payload, judgments, item = self._fixture(Path(tmp))
            parent_association = payload["semantic_model_items"][0][
                "source_statement_association"
            ]
            assert isinstance(parent_association, dict)
            corrupted = dict(parent_association)
            corrupted["source_item_identities"] = []
            duck_typed_transport = SimpleNamespace(
                association_rebinds={
                    source_map_item_record_digest(parent_association): corrupted
                }
            )
            resolution = internal_derivational_auxiliary_resolution(
                "Fixture",
                folder,
                payload,
                item,
                judgments,
                current_judgment_keys=set(judgments),
                administrative_projection_rebind=duck_typed_transport,  # type: ignore[arg-type]
            )

        self.assertTrue(resolution.accepted, resolution.reason)


if __name__ == "__main__":
    unittest.main()
