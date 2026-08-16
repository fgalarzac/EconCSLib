#!/usr/bin/env python3
"""Focused tests for current-v10 semantic differential source-record reuse."""

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

from scripts import audit_conclusion_provenance as CONCLUSION  # noqa: E402
from scripts import audit_evidence_integrity as EVIDENCE  # noqa: E402
from scripts import audit_repository as REPOSITORY  # noqa: E402
from scripts import source_record_differential_revalidation as DIFFERENTIAL  # noqa: E402
from scripts import source_record_target_disposition as DISPOSITION  # noqa: E402
from scripts.source_record_integrity import stamp_source_record_audit_receipts  # noqa: E402
from scripts.source_record_target_disposition import (  # noqa: E402
    recursive_field_parent_route_record_digest,
    semantic_association_record_digest,
)


PAPER = "FixturePaper"
SOURCE_RECORD_AUDIT_HELPER = (
    ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
)


def digest(char: str) -> str:
    return char * 64


def load_source_record_audit_helper() -> object:
    spec = importlib.util.spec_from_file_location(
        "differential_revalidation_source_record_audit_helper",
        SOURCE_RECORD_AUDIT_HELPER,
    )
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def source_association(*, signature: str = digest("d")) -> dict[str, object]:
    signature_identity = {
        "qualified_declaration": "Fixture.PaperInterface.source_result",
        "elaborated_signature_sha256": signature,
    }
    return {
        "schema": 2,
        "association_mode": "explicit_source_map_direct_route",
        "semantic_contract_member_role": "direct_source_route",
        "semantic_association_sha256": semantic_association_record_digest(
            [digest("a")], signature_identity
        ),
        "semantic_model_judgment_key": "semantic-model::source_result",
        "source_item_identities": [{"source_semantic_sha256": digest("a")}],
        "reviewed_declaration_identity": {
            "qualified_declaration": "Fixture.PaperInterface.source_result",
            "declaration_sha256": digest("c"),
        },
        "reviewed_elaborated_signature_identity": signature_identity,
    }


def statement_component_association(
    parent_source_item: dict[str, object],
    *,
    component_marker: str,
    qualified_declaration: str = "Fixture.PaperInterface.source_result",
    convention_scoped: bool = False,
) -> dict[str, object]:
    signature = {
        "qualified_declaration": qualified_declaration,
        "elaborated_signature_sha256": digest("d"),
    }
    parent_identity = {
        "source_key": "parent_definition",
        "source_location": str(parent_source_item["source_location"]),
        "source_kind": str(parent_source_item["source_kind"]),
        "source_map_item_sha256": DISPOSITION.source_map_item_record_digest(
            parent_source_item
        ),
        "source_semantic_sha256": DISPOSITION.source_item_coverage_sha256(
            parent_source_item, ""
        ),
        "semantic_contract": {
            "evidence_declaration": "",
            "spec_declaration": "",
            "evidence_mode": "",
            "semantic_shape": "",
        },
    }
    component = {
        "schema": 1,
        "source_component_semantic_sha256": digest(component_marker),
        "source_statement_sha256": digest(component_marker),
        "source_anchor_quote_identity_sha256": digest("3"),
        "source_target_sha256": digest(component_marker),
        "source_target_disposition": {
            "kind": "ordinary_or_convention",
            "source_kind": "definition",
            "source_status": "exact",
            "coverage_status": "",
            "protocol_role": "",
        },
        "source_definition_partition_sha256": digest("4"),
        "source_definition_component_sha256": digest(component_marker),
        "source_component_anchor_sha256": digest("5"),
        "statement_manifest_structure_sha256": digest("6"),
        "statement_semantic_dependency_sha256": digest("7"),
        "statement_review_validator_identity_sha256": digest("8"),
        "statement_review_protocol_sha256": digest("9"),
        "statement_source_route_semantic_sha256": digest(component_marker),
        "statement_obligation_ledger_validated": True,
        "statement_source_definition_semantics_validated": True,
    }
    if convention_scoped:
        component["source_model_convention_pins"] = {
            "schema": 2,
            "model_convention_ids": ["FIXTURE-CONVENTION"],
            "record_sha256_by_id": {"FIXTURE-CONVENTION": digest("a")},
        }
    component_pin = DISPOSITION.source_map_item_record_digest(
        {
            "schema": 1,
            "source_definition_component_semantic_identity": component,
            "elaborated_signature_sha256": digest("d"),
        }
    )
    association: dict[str, object] = {
        "schema": 2,
        "association_origin": "authenticated_v10_statement_source_component",
        "role": "source_definition_component_semantic_route",
        "reviewed_declaration_identity": {
            "qualified_declaration": qualified_declaration,
            "declaration_sha256": digest("c"),
        },
        "reviewed_elaborated_signature_identity": signature,
        "source_item_identities": [parent_identity],
        "source_definition_component_semantic_identity": component,
        "component_semantic_association_sha256": component_pin,
        "semantic_association_sha256": component_pin,
        "parent_semantic_association_sha256": semantic_association_record_digest(
            [str(parent_identity["source_semantic_sha256"])], signature
        ),
        "review_scope": "individual_source_definition_component_only",
        "structural_pairing": "authenticated_statement_component_equivalence",
    }
    association["association_sha256"] = (
        DISPOSITION.source_contract_association_record_digest(association)
    )
    return association


def reusable_input(
    key: str,
    *,
    kind: str = "boundary_input",
    signature: str = digest("d"),
    input_type: str = "P x",
    result_type: str = "OldResult",
    result_relation: str = "",
) -> dict[str, object]:
    return {
        "judgment_key": key,
        "kind": kind,
        "row": "source_result",
        "binder": "h",
        "expanded_input_type": input_type,
        "row_result_type": result_type,
        "result_relation": result_relation,
        "expanded_lean_surface": {
            "input_type": input_type,
            "result_type": result_type,
        },
        "source_contract_association": source_association(signature=signature),
        "reviewed_elaborated_signature_identities": [
            {
                "qualified_declaration": "Fixture.PaperInterface.source_result",
                "elaborated_signature_sha256": signature,
            }
        ],
        "source_record_item_reuse_eligibility": {"eligible": True, "blockers": []},
        "source_record_item_digest_schema": 5,
        "source_record_item_semantic_id": digest("1"),
        "source_record_item_context_sha256": digest("2"),
        "source_record_item_sha256": digest("3"),
    }


def aggregate_only_recursive(
    key: str,
    *,
    structure: str,
    field: str,
    direct_parent_route: bool = False,
) -> dict[str, object]:
    item: dict[str, object] = {
        "judgment_key": key,
        "kind": "recursive_field",
        "structure": structure,
        "field": field,
        "type": "User m -> Item n -> Real",
        "nested_structures": [],
        "source_record_item_reuse_eligibility": {
            "eligible": False,
            "blockers": [
                "no source-content semantic identity",
                "no exact current elaborated review-route signature",
            ],
        },
    }
    if direct_parent_route:
        signature = {
            "qualified_declaration": "Fixture.PaperInterface.source_result",
            "elaborated_signature_sha256": digest("d"),
        }
        route: dict[str, object] = {
            "schema": 1,
            "inheritance_mode": "explicit_parent_route_and_field_scope",
            "source_item": "fixture_source_item",
            "source_item_identities": [
                {
                    "source_key": "fixture_source_item",
                    "source_semantic_sha256": digest("a"),
                    "source_map_item_sha256": digest("b"),
                }
            ],
            "root_record": "Fixture.Model",
            "root_input_type_canonical": "Fixture.Model x",
            "field_chain": [{"structure": structure, "field": field}],
            "source_locator": "source.txt:1-2",
            "permitted_classifications": ["nonpropositional_witness_data"],
            "convention_id": "fixture-direct-convention",
            "convention_sha256": digest("c"),
            "field_scope_sha256": digest("e"),
            "parent_association_field": "source_statement_association",
            "parent_source_association_role": "direct_source_route",
            "parent_source_association_origin": "explicit_source_map_direct_route",
            "parent_reviewed_declaration_identity": {
                "qualified_declaration": "Fixture.PaperInterface.source_result",
                "declaration_sha256": digest("f"),
            },
            "parent_elaborated_signature_identity": signature,
            "parent_source_association_sha256": semantic_association_record_digest(
                [digest("a")], signature
            ),
        }
        route["association_sha256"] = recursive_field_parent_route_record_digest(route)
        item["recursive_field_explicit_parent_route"] = route
    return item


def semantic_model_item(
    key: str, *, signature: str = digest("d"), result_type: str = "OldResult"
) -> dict[str, object]:
    return {
        "judgment_key": key,
        "kind": "semantic_model_comparison",
        "row": "source_result",
        "expanded_lean_surface": {
            "binder_type": "P x",
            "result_type": result_type,
        },
        "source_contract_association": source_association(signature=signature),
        "reviewed_elaborated_signature_identities": [
            {
                "qualified_declaration": "Fixture.PaperInterface.source_result",
                "elaborated_signature_sha256": signature,
            }
        ],
        "dimensions": [
            {
                "id": "expanded_binders_and_domain",
                "detected_from_expanded_surface": True,
            }
        ],
        "source_record_item_reuse_eligibility": {"eligible": True, "blockers": []},
        "source_record_item_digest_schema": 5,
        "source_record_item_semantic_id": digest("4"),
        "source_record_item_context_sha256": digest("5"),
        "source_record_item_sha256": digest("6"),
    }


def advance_recursive_parent_signature(
    item: dict[str, object], *, signature: str
) -> None:
    """Update one generated recursive route as a current parent result changes."""

    route = item["recursive_field_explicit_parent_route"]
    assert isinstance(route, dict)
    signature_identity = route["parent_elaborated_signature_identity"]
    assert isinstance(signature_identity, dict)
    signature_identity["elaborated_signature_sha256"] = signature
    identities = route["source_item_identities"]
    assert isinstance(identities, list) and len(identities) == 1
    identity = identities[0]
    assert isinstance(identity, dict)
    source_semantic = identity["source_semantic_sha256"]
    assert isinstance(source_semantic, str)
    route["parent_source_association_sha256"] = semantic_association_record_digest(
        [source_semantic], signature_identity
    )
    route["association_sha256"] = recursive_field_parent_route_record_digest(route)


def direct_source_domain_parent(
    route: dict[str, object],
    *,
    result_type: str = "OldResult",
    binder_domains: list[dict[str, str]] | None = None,
    record_roots: list[str] | None = None,
) -> dict[str, object]:
    """Build a source-pinned semantic parent for a routed recursive field."""

    identities = route["source_item_identities"]
    assert isinstance(identities, list)
    signature = route["parent_elaborated_signature_identity"]
    assert isinstance(signature, dict)
    reviewed_identity = route["parent_reviewed_declaration_identity"]
    assert isinstance(reviewed_identity, dict)
    source_semantic = identities[0]["source_semantic_sha256"]
    assert isinstance(source_semantic, str)
    association = {
        "schema": 2,
        "role": route["parent_source_association_role"],
        "association_origin": route["parent_source_association_origin"],
        "reviewed_declaration_identity": copy.deepcopy(reviewed_identity),
        "reviewed_elaborated_signature_identity": copy.deepcopy(signature),
        "source_item_identities": copy.deepcopy(identities),
        "semantic_association_sha256": semantic_association_record_digest(
            [source_semantic], signature
        ),
    }
    return {
        "judgment_key": "semantic-model::direct_source_domain_parent",
        "kind": "semantic_model_comparison",
        "expanded_lean_surface": {
            "binder_domains": binder_domains
            or [
                {"expanded_type": "Fixture.Model x", "alpha_normalized_type": "Fixture.Model _f0"},
                {"expanded_type": "SourcePremise x", "alpha_normalized_type": "SourcePremise _f0"},
            ],
            "result_type": result_type,
        },
        "record_input_bindings": [
            {
                "record_roots": record_roots or [route["root_record"]],
                "fully_qualified_expanded_type_canonical": route[
                    "root_input_type_canonical"
                ],
                "source_type_canonical": "Model x",
                "binder_names": ["model"],
                "elaborated_outer_binder_atoms": [
                    {
                        "ref": "b/1",
                        "role": "parameter",
                        "signature_atom_sha256": digest("e"),
                    }
                ],
            }
        ],
        str(route["parent_association_field"]): association,
        "reviewed_elaborated_signature_identities": [copy.deepcopy(signature)],
        "source_record_item_reuse_eligibility": {"eligible": True, "blockers": []},
        "source_record_item_digest_schema": 5,
        "source_record_item_semantic_id": digest("4"),
        "source_record_item_context_sha256": digest("5"),
        "source_record_item_sha256": digest("6"),
        "source_record_item_semantic_context_requirements_sha256": digest("7"),
        "source_record_item_source_proof_fidelity_records_sha256": digest("8"),
    }


def complete_presentation_surfaces(
    *,
    reviewed_declaration: str = "Fixture.PaperInterface.source_result",
    effective_declaration: str = "Fixture.Model.source_result",
    proposition_alias: str = "Fixture.Presentation.source_assumption",
    dependency_declaration: str = "Fixture.Model.score",
    dependency_parent: str = "Fixture.Model.source_result",
    source_file: str = "papers/Fixture/MainTheorems.lean",
    line: int = 10,
) -> dict[str, object]:
    """Return complete routes whose declaration strings are presentation only."""

    return {
        "review_alias_expansion": {
            "schema": 1,
            "reviewed_declaration": reviewed_declaration,
            "effective_declaration": effective_declaration,
            "alias_present": True,
            "complete": True,
            "effective_kind": "theorem",
            "steps": [
                {
                    "from": reviewed_declaration,
                    "reference": effective_declaration.rsplit(".", 1)[-1],
                    "to": effective_declaration,
                    "target_kind": "theorem",
                    "source_file": source_file,
                    "line": line,
                }
            ],
            "blocked_routes": [],
        },
        "proposition_alias_expansion": {
            "expanded_type": "P x",
            "transparent_steps": [
                {
                    "declaration": proposition_alias,
                    "kind": "def",
                    "source_file": source_file,
                    "line": line + 1,
                }
            ],
            "blocked_routes": [],
        },
        "terminal_term_dependency_surface": {
            "schema": 1,
            "scan_complete": True,
            "scan_limits": {"max_depth": 8, "max_nodes": 64},
            "incomplete_reasons": [],
            "terminal_result_semantic_construct_flags": {
                "probability_law_construct": True,
                "model_semantics": True,
            },
            "terminal_result_semantic_fragments": [
                {"construct": "probability_law_construct", "fragment": "PMF x"}
            ],
            "transparent_definitions": [
                {
                    "declaration": dependency_declaration,
                    "kind": "def",
                    "source_file": source_file,
                    "line": line + 2,
                    "declaration_sha256": digest("7"),
                    "body_sha256": digest("8"),
                    "parameter_types": [
                        {
                            "names": "x",
                            "expanded_type": "P x",
                            "alpha_normalized_type": "P _termBound0",
                        }
                    ],
                    "result_type": {
                        "expanded_type": "Real",
                        "alpha_normalized_type": "Real",
                    },
                    "semantic_construct_flags": {
                        "probability_law_construct": True,
                        "model_semantics": True,
                    },
                    "semantic_fragments": [
                        {
                            "construct": "probability_law_construct",
                            "fragment": "PMF _termBound0",
                        }
                    ],
                    "body_surface_inspectable": True,
                    "direct_local_dependencies": ["Fixture.Model.distribution"],
                    "dependency_chain": [dependency_parent, dependency_declaration],
                    "semantic_relevant": True,
                }
            ],
            "unexpanded_local_term_heads": [],
            "semantic_construct_flags": {
                "probability_law_construct": True,
                "model_semantics": True,
            },
        },
    }


def raw_audit(
    *,
    boundary: list[dict[str, object]] | None = None,
    conclusion: list[dict[str, object]] | None = None,
    recursive: list[dict[str, object]] | None = None,
    semantic: list[dict[str, object]] | None = None,
) -> dict[str, object]:
    payload: dict[str, object] = {
        "paper": PAPER,
        "prompt_version": DIFFERENTIAL.SOURCE_RECORD_V10_PROMPT_VERSION,
        "source_record_policy_version": DIFFERENTIAL.SOURCE_RECORD_V10_PROMPT_VERSION,
        "boundary_input_items": boundary or [],
        "conclusion_dependency_items": conclusion or [],
        "recursive_field_items": recursive or [],
        "semantic_model_items": semantic or [],
        "lean_check": {"returncode": 0},
        "recursion_failure_count": 0,
    }
    stamp_source_record_audit_receipts(payload)
    return payload


def raw_audit_with_reprojected_selected_semantic_projection(
    *,
    selected_projection_sha256: str,
    boundary: list[dict[str, object]] | None = None,
) -> dict[str, object]:
    """Fixture for the replicated receipt-reprojector delta accepted by reissue."""

    payload = raw_audit(boundary=boundary)
    reprojection = {
        "paper_statement_map_exact_default_mode_delta": {
            "selected_semantic_projection_sha256": selected_projection_sha256,
        }
    }
    payload["source_record_receipt_reprojection"] = copy.deepcopy(reprojection)
    stamp_source_record_audit_receipts(
        payload,
        surface={"source_record_receipt_reprojection": copy.deepcopy(reprojection)},
    )
    return payload


def sidecar(
    raw: dict[str, object], entries: dict[str, dict[str, object]]
) -> dict[str, object]:
    items: dict[str, object] = {}
    for key, value in entries.items():
        item = {
            "classification": "validated_source_assumption",
            "reason": "saved current v10 semantic review",
            "prompt_version": DIFFERENTIAL.SOURCE_RECORD_V10_PROMPT_VERSION,
            "source_record_policy_version": DIFFERENTIAL.SOURCE_RECORD_V10_PROMPT_VERSION,
            "source_record_audit_sha256": raw["source_record_audit_sha256"],
            "validator": "fixture auditor",
            "validated_at": "2026-07-27T00:00:00Z",
        }
        item.update(value)
        items[key] = item
    return {
        "schema": 1,
        "paper": PAPER,
        "prompt_version": DIFFERENTIAL.SOURCE_RECORD_V10_PROMPT_VERSION,
        "source_record_policy_version": DIFFERENTIAL.SOURCE_RECORD_V10_PROMPT_VERSION,
        "source_record_audit_sha256": raw["source_record_audit_sha256"],
        "validator": "fixture auditor",
        "validated_at": "2026-07-27T00:00:00Z",
        "items": items,
    }


def reuse_exclusions(
    raw: dict[str, object], descriptor_reasons: dict[str, str]
) -> dict[str, object]:
    """Build the deliberately descriptor-only reviewer exclusion artifact."""

    return {
        "schema": DIFFERENTIAL.SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_SCHEMA,
        "artifact_kind": (
            DIFFERENTIAL.SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_ARTIFACT_KIND
        ),
        "policy_version": (
            DIFFERENTIAL.SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_POLICY_VERSION
        ),
        "paper": PAPER,
        "current_source_record_audit_sha256": raw["source_record_audit_sha256"],
        "current_source_record_audit_integrity_sha256": raw[
            "source_record_audit_integrity_sha256"
        ],
        DIFFERENTIAL.SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_REASONS_FIELD: (
            descriptor_reasons
        ),
    }


class SourceRecordDifferentialRevalidationTests(unittest.TestCase):
    def test_statement_component_rebind_cannot_downgrade_to_generic_pin(
        self,
    ) -> None:
        parent = {
            "statement": "The source definition has two distinct clauses.",
            "source_kind": "definition",
            "source_location": "source.txt:1-2",
            "source_status": "exact",
        }
        association = statement_component_association(
            parent, component_marker="1"
        )
        self.assertIsNotNone(
            DIFFERENTIAL._semantic_association_rebind_record(
                section="semantic_model_items",
                field="statement_source_component_association",
                association=association,
            )
        )
        for field, replacement in (
            ("association_origin", "ordinary_generated_association"),
            ("role", "direct_evidence"),
        ):
            with self.subTest(field=field):
                malformed = copy.deepcopy(association)
                malformed[field] = replacement
                identities = malformed["source_item_identities"]
                signature = malformed[
                    "reviewed_elaborated_signature_identity"
                ]
                assert isinstance(identities, list) and isinstance(signature, dict)
                malformed["semantic_association_sha256"] = (
                    semantic_association_record_digest(
                        [
                            str(identity["source_semantic_sha256"])
                            for identity in identities
                            if isinstance(identity, dict)
                        ],
                        signature,
                    )
                )
                self.assertIsNone(
                    DIFFERENTIAL._semantic_association_rebind_record(
                        section="semantic_model_items",
                        field="statement_source_component_association",
                        association=malformed,
                    )
                )

    def test_statement_component_descriptor_is_name_free_and_component_exact(self) -> None:
        parent = {
            "statement": "The source definition has two distinct clauses.",
            "source_kind": "definition",
            "source_location": "source.txt:1-2",
            "source_status": "exact",
        }

        def item(marker: str, qualified: str) -> dict[str, object]:
            return {
                "row": qualified.rsplit(".", 1)[-1],
                "judgment_key": "semantic-model::" + qualified,
                "qualified_declaration": qualified,
                "kind": "semantic_model_comparison",
                "expanded_lean_surface": {
                    "binder_domains": [{"expanded_type": "Type"}],
                    "terminal_result": {"expanded_type": "Agent -> Real"},
                },
                "dimensions": [
                    {
                        "id": "expanded_binders_and_domain",
                        "detected_from_expanded_surface": True,
                    }
                ],
                "statement_source_component_association": (
                    statement_component_association(
                        parent,
                        component_marker=marker,
                        qualified_declaration=qualified,
                    )
                ),
            }

        first = item("1", "Fixture.PaperInterface.firstName")
        renamed = item("1", "Fixture.RenamedInterface.unrelatedName")
        distinct_component = item("2", "Fixture.PaperInterface.secondName")
        first_descriptor = DIFFERENTIAL.source_record_differential_item_descriptor(
            first, section="semantic_model_items"
        )
        renamed_descriptor = DIFFERENTIAL.source_record_differential_item_descriptor(
            renamed, section="semantic_model_items"
        )
        distinct_descriptor = DIFFERENTIAL.source_record_differential_item_descriptor(
            distinct_component, section="semantic_model_items"
        )

        self.assertEqual(first_descriptor, renamed_descriptor)
        self.assertNotEqual(first_descriptor, distinct_descriptor)
        serialized = json.dumps(first_descriptor, sort_keys=True)
        self.assertNotIn("firstName", serialized)
        self.assertNotIn("semantic-model::", serialized)
        self.assertIn(digest("1"), serialized)

    def test_statement_component_association_projects_and_validates_target(self) -> None:
        parent = {
            "statement": "The source definition has two distinct clauses.",
            "source_kind": "definition",
            "source_location": "source.txt:1-2",
            "source_status": "exact",
        }
        association = statement_component_association(
            parent, component_marker="1"
        )
        item = {
            "judgment_key": "semantic-model::source_result",
            "qualified_declaration": "Fixture.PaperInterface.source_result",
            "kind": "semantic_model_comparison",
            "dimensions": [{"id": "expanded_binders_and_domain"}],
            "statement_source_component_association": association,
        }
        projection, projection_error = (
            DISPOSITION.source_record_response_association_projection(
                [("semantic_model_items", item)],
                judgment_key="semantic-model::source_result",
                statement_map={"items": {"parent_definition": parent}},
            )
        )
        self.assertEqual(projection_error, "")
        assert projection is not None
        self.assertEqual(
            projection.semantic_dimension_association_sha256,
            {
                "expanded_binders_and_domain": association[
                    "semantic_association_sha256"
                ]
            },
        )
        response = {
            "verdict": "matches_literal_source",
            "source_target_disposition": "literal_source_match",
            "semantic_association_sha256": association[
                "semantic_association_sha256"
            ],
        }
        self.assertEqual(
            DISPOSITION.semantic_target_disposition_errors(
                item,
                response,
                statement_map={"items": {"parent_definition": parent}},
                source_proof_fidelity=None,
            ),
            [],
        )

        sibling_association = statement_component_association(
            parent, component_marker="2"
        )
        sibling_item = copy.deepcopy(item)
        sibling_item["statement_source_component_association"] = sibling_association
        swapped_errors = DISPOSITION.semantic_target_disposition_errors(
            sibling_item,
            response,
            statement_map={"items": {"parent_definition": parent}},
            source_proof_fidelity=None,
        )
        self.assertTrue(
            any("semantic_association_sha256" in error for error in swapped_errors)
        )

        convention_item = copy.deepcopy(item)
        convention_item["statement_source_component_association"] = (
            statement_component_association(
                parent, component_marker="3", convention_scoped=True
            )
        )
        convention_literal_errors = DISPOSITION.semantic_target_disposition_errors(
            convention_item,
            {
                **response,
                "semantic_association_sha256": convention_item[
                    "statement_source_component_association"
                ]["semantic_association_sha256"],
            },
            statement_map={"items": {"parent_definition": parent}},
            source_proof_fidelity=None,
        )
        self.assertTrue(
            any(
                "does not match the authenticated statement source-component"
                in error
                for error in convention_literal_errors
            )
        )

        stale_item = copy.deepcopy(item)
        stale_association = stale_item["statement_source_component_association"]
        assert isinstance(stale_association, dict)
        stale_component = stale_association[
            "source_definition_component_semantic_identity"
        ]
        assert isinstance(stale_component, dict)
        stale_component["source_statement_sha256"] = digest("2")
        errors = DISPOSITION.semantic_target_disposition_errors(
            stale_item,
            response,
            statement_map={"items": {"parent_definition": parent}},
            source_proof_fidelity=None,
        )
        self.assertTrue(any("component semantic pin" in error for error in errors))

    def build_overlay(
        self,
        prior: dict[str, object],
        judgments: dict[str, object],
        current: dict[str, object],
        *,
        reuse_exclusions_payload: dict[str, object] | None = None,
        require_complete_reusable_section_identity: bool = False,
    ) -> tuple[dict[str, object], Path, Path]:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        root_override = patch.object(DIFFERENTIAL, "ROOT", root)
        root_override.start()
        self.addCleanup(root_override.stop)
        prior_path = root / "prior_raw.json"
        judgments_path = root / "prior_judgments.json"
        paper_dir = root / "papers" / PAPER
        current_path = paper_dir / "audit" / "source_record_audit.json"
        overlay_path = DIFFERENTIAL.source_record_differential_revalidation_overlay_path(
            paper_dir
        )
        current_path.parent.mkdir(parents=True)
        prior_path.write_text(json.dumps(prior, sort_keys=True), encoding="utf-8")
        judgments_path.write_text(json.dumps(judgments, sort_keys=True), encoding="utf-8")
        current_path.write_text(json.dumps(current, sort_keys=True), encoding="utf-8")
        reuse_exclusions_path: Path | None = None
        if reuse_exclusions_payload is not None:
            reuse_exclusions_path = root / "reuse_exclusions.json"
            reuse_exclusions_path.write_text(
                json.dumps(reuse_exclusions_payload, sort_keys=True), encoding="utf-8"
            )
        overlay = DIFFERENTIAL.build_source_record_differential_revalidation(
            paper=PAPER,
            prior_raw_audit=prior,
            prior_judgments=judgments,
            current_raw_audit=current,
            prior_raw_audit_path=prior_path,
            prior_judgments_path=judgments_path,
            current_raw_audit_path=current_path,
            reuse_exclusions_path=reuse_exclusions_path,
            require_complete_reusable_section_identity=(
                require_complete_reusable_section_identity
            ),
        )
        overlay_path.write_text(json.dumps(overlay, sort_keys=True), encoding="utf-8")
        ordinary_path = paper_dir / "audit" / "source_record_match_llm.json"
        ordinary_path.write_text(
            json.dumps({"schema": 1, "paper": PAPER, "items": {}}),
            encoding="utf-8",
        )
        return overlay, paper_dir, ordinary_path

    def test_input_local_group_survives_result_change_but_semantic_model_requires_review(self) -> None:
        input_key = "input.old : P x"
        semantic_key = "semantic-model::source_result"
        prior_boundary = reusable_input(input_key)
        prior_conclusion = reusable_input(
            input_key, kind="direct_conclusion_input", result_relation="component_of_target"
        )
        prior_semantic = semantic_model_item(semantic_key)
        prior = raw_audit(
            boundary=[prior_boundary],
            conclusion=[prior_conclusion],
            semantic=[prior_semantic],
        )
        judgments = sidecar(
            prior,
            {
                input_key: {
                    "semantic_association_sha256": prior_boundary[
                        "source_contract_association"
                    ]["semantic_association_sha256"],
                },
                semantic_key: {
                    "classification": "semantic_model_review",
                    "semantic_model_dimensions": {
                        "expanded_binders_and_domain": {
                            "verdict": "matches_literal_source",
                            "source_locator": "source.txt:1-2",
                            "semantic_comparison": "prior result review",
                            "lean_evidence": "prior elaboration",
                        }
                    },
                },
            },
        )
        current_boundary = copy.deepcopy(prior_boundary)
        current_conclusion = copy.deepcopy(prior_conclusion)
        current_semantic = copy.deepcopy(prior_semantic)
        for item in (current_boundary, current_conclusion):
            item["row_result_type"] = "NewDirectResult"
            item["expanded_lean_surface"]["result_type"] = "NewDirectResult"
            item["source_contract_association"]["reviewed_elaborated_signature_identity"][
                "elaborated_signature_sha256"
            ] = digest("8")
            item["source_contract_association"][
                "semantic_association_sha256"
            ] = semantic_association_record_digest(
                [digest("a")],
                item["source_contract_association"][
                    "reviewed_elaborated_signature_identity"
                ],
            )
            item["reviewed_elaborated_signature_identities"][0][
                "elaborated_signature_sha256"
            ] = digest("8")
        current_semantic["expanded_lean_surface"]["result_type"] = "NewDirectResult"
        current_semantic["source_contract_association"]["reviewed_elaborated_signature_identity"][
            "elaborated_signature_sha256"
        ] = digest("8")
        current_semantic["source_contract_association"][
            "semantic_association_sha256"
        ] = semantic_association_record_digest(
            [digest("a")],
            current_semantic["source_contract_association"][
                "reviewed_elaborated_signature_identity"
            ],
        )
        current_semantic["reviewed_elaborated_signature_identities"][0][
            "elaborated_signature_sha256"
        ] = digest("8")
        current = raw_audit(
            boundary=[current_boundary],
            conclusion=[current_conclusion],
            semantic=[current_semantic],
        )

        overlay, paper_dir, ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertEqual(set(overlay["items"]), {input_key})
        self.assertEqual(
            [entry["current_judgment_key"] for entry in overlay["manual_review_required"]],
            [semantic_key],
        )
        loaded = DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
            paper_dir, PAPER, current
        )
        self.assertEqual(set(loaded), {input_key})
        self.assertTrue(
            DIFFERENTIAL.is_loaded_source_record_differential_revalidation_item(
                loaded[input_key]
            )
        )
        self.assertEqual(
            loaded[input_key]["semantic_association_sha256"],
            current_boundary["source_contract_association"]["semantic_association_sha256"],
        )

        with patch.object(EVIDENCE, "source_record_audit_identity_error", return_value=""):
            current_items = EVIDENCE.current_source_record_judgment_items(
                current, {}, folder=paper_dir
            )
        self.assertEqual(set(current_items), {input_key})
        repository_items = REPOSITORY.source_record_judgment_items(
            ordinary_path, PAPER, current_raw_audit=current, paper_dir=paper_dir
        )
        self.assertEqual(set(repository_items), {input_key})
        self.assertTrue(
            REPOSITORY.source_record_judgment_current(
                input_key,
                repository_items[input_key],
                digest="",
                expected_item_digests={},
            )
        )
        with patch.object(CONCLUSION, "PAPERS", paper_dir.parent):
            self.assertEqual(set(CONCLUSION.current_judgments(PAPER, current)), {input_key})
        helper = load_source_record_audit_helper()
        self.assertEqual(
            set(helper.current_source_record_judgments(paper_dir, PAPER, current)),
            {input_key},
        )

    def test_descriptor_only_reuse_exclusion_requires_manual_current_review(self) -> None:
        retained_key = "retained.h : P"
        excluded_key = "excluded.h : Q"
        prior = raw_audit(
            boundary=[
                reusable_input(retained_key, input_type="P x"),
                reusable_input(excluded_key, input_type="Q x"),
            ]
        )
        judgments = sidecar(prior, {retained_key: {}, excluded_key: {}})
        current = raw_audit(
            boundary=[
                reusable_input(retained_key, input_type="P x"),
                reusable_input(excluded_key, input_type="Q x"),
            ]
        )
        excluded_descriptor = DIFFERENTIAL._raw_item_groups(current)[0][excluded_key][
            "descriptor_sha256"
        ]
        assert isinstance(excluded_descriptor, str)
        exclusions = reuse_exclusions(
            current,
            {excluded_descriptor: "the revised source-facing wrapper needs direct review"},
        )

        overlay, paper_dir, _ordinary_path = self.build_overlay(
            prior,
            judgments,
            current,
            reuse_exclusions_payload=exclusions,
        )

        self.assertEqual(set(overlay["items"]), {retained_key})
        self.assertEqual(
            overlay["manual_review_required"],
            [
                {
                    "current_judgment_key": excluded_key,
                    "current_group_semantic_descriptor_sha256": excluded_descriptor,
                    "reason": "the revised source-facing wrapper needs direct review",
                }
            ],
        )
        excluded_decisions = [
            decision
            for decision in overlay["decisions"]
            if decision.get("current_judgment_key") == excluded_key
        ]
        self.assertEqual(len(excluded_decisions), 1)
        self.assertEqual(excluded_decisions[0]["status"], "not_reused")
        self.assertEqual(
            excluded_decisions[0]["current_group_semantic_descriptor_sha256"],
            excluded_descriptor,
        )
        record = overlay[
            DIFFERENTIAL.SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_FIELD
        ]
        assert isinstance(record, dict)
        self.assertEqual(
            record[
                DIFFERENTIAL.SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_REASONS_FIELD
            ],
            {excluded_descriptor: "the revised source-facing wrapper needs direct review"},
        )
        self.assertEqual(
            set(
                DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                    paper_dir, PAPER, current
                )
            ),
            {retained_key},
        )

        # The exclusion artifact is part of the authenticated overlay
        # provenance. Changing it later cannot silently preserve the reuse.
        exclusion_path = DIFFERENTIAL._repository_provenance_path(record["path"])
        changed = json.loads(exclusion_path.read_text(encoding="utf-8"))
        changed[
            DIFFERENTIAL.SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_REASONS_FIELD
        ][excluded_descriptor] = "tampered reason"
        exclusion_path.write_text(json.dumps(changed, sort_keys=True), encoding="utf-8")
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir, PAPER, current
            ),
            {},
        )

    def test_reuse_exclusion_rejects_name_selector_unknown_descriptor_and_empty_reason(
        self,
    ) -> None:
        key = "input.h : P"
        prior = raw_audit(boundary=[reusable_input(key)])
        judgments = sidecar(prior, {key: {}})
        current = raw_audit(boundary=[reusable_input(key)])
        descriptor = DIFFERENTIAL._raw_item_groups(current)[0][key]["descriptor_sha256"]
        assert isinstance(descriptor, str)

        name_selector = reuse_exclusions(current, {descriptor: "needs review"})
        name_selector["current_judgment_key"] = key
        with self.assertRaisesRegex(
            DIFFERENTIAL.SourceRecordDifferentialRevalidationError,
            "unsupported fields",
        ):
            self.build_overlay(
                prior,
                judgments,
                current,
                reuse_exclusions_payload=name_selector,
            )

        unknown_descriptor = reuse_exclusions(current, {digest("f"): "needs review"})
        with self.assertRaisesRegex(
            DIFFERENTIAL.SourceRecordDifferentialRevalidationError,
            "does not identify exactly one current semantic group",
        ):
            self.build_overlay(
                prior,
                judgments,
                current,
                reuse_exclusions_payload=unknown_descriptor,
            )

        ambiguous_first = "first.h : P"
        ambiguous_second = "second.h : P"
        ambiguous_prior = raw_audit(
            boundary=[
                reusable_input(ambiguous_first),
                reusable_input(ambiguous_second),
            ]
        )
        ambiguous_judgments = sidecar(
            ambiguous_prior, {ambiguous_first: {}, ambiguous_second: {}}
        )
        ambiguous_current = raw_audit(
            boundary=[
                reusable_input(ambiguous_first),
                reusable_input(ambiguous_second),
            ]
        )
        ambiguous_descriptor = DIFFERENTIAL._raw_item_groups(ambiguous_current)[0][
            ambiguous_first
        ]["descriptor_sha256"]
        assert isinstance(ambiguous_descriptor, str)
        with self.assertRaisesRegex(
            DIFFERENTIAL.SourceRecordDifferentialRevalidationError,
            "does not identify exactly one current semantic group",
        ):
            self.build_overlay(
                ambiguous_prior,
                ambiguous_judgments,
                ambiguous_current,
                reuse_exclusions_payload=reuse_exclusions(
                    ambiguous_current, {ambiguous_descriptor: "needs review"}
                ),
            )

        empty_reason = reuse_exclusions(current, {descriptor: "  "})
        with self.assertRaisesRegex(
            DIFFERENTIAL.SourceRecordDifferentialRevalidationError,
            "undocumented descriptor exclusion",
        ):
            self.build_overlay(
                prior,
                judgments,
                current,
                reuse_exclusions_payload=empty_reason,
            )

    def test_no_reuse_exclusion_preserves_ordinary_differential_reuse(self) -> None:
        key = "input.h : P"
        prior = raw_audit(boundary=[reusable_input(key)])
        judgments = sidecar(prior, {key: {}})
        current = raw_audit(boundary=[reusable_input(key)])
        overlay, paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertNotIn(
            DIFFERENTIAL.SOURCE_RECORD_DIFFERENTIAL_REUSE_EXCLUSIONS_FIELD,
            overlay,
        )
        self.assertEqual(set(overlay["items"]), {key})
        self.assertEqual(
            set(
                DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                    paper_dir, PAPER, current
                )
            ),
            {key},
        )

    def test_complete_presentation_only_renames_reuse_without_raw_scan(self) -> None:
        prior_key = "old_route.h : P x"
        current_key = "new_route.renamed_h : P x"
        prior_item = reusable_input(prior_key)
        prior_item["expanded_lean_surface"].update(complete_presentation_surfaces())
        prior = raw_audit(boundary=[prior_item])
        judgments = sidecar(prior, {prior_key: {}})

        current_item = copy.deepcopy(prior_item)
        current_item["judgment_key"] = current_key
        current_item["row"] = "renamed_route"
        current_item["binder"] = "renamed_h"
        surface = current_item["expanded_lean_surface"]
        assert isinstance(surface, dict)
        surface.update(
            complete_presentation_surfaces(
                reviewed_declaration="Fixture.RenamedInterface.renamed_route",
                effective_declaration="Fixture.RenamedModel.renamed_route",
                proposition_alias="Fixture.RenamedPresentation.source_assumption",
                dependency_declaration="Fixture.RenamedModel.score",
                dependency_parent="Fixture.RenamedModel.renamed_route",
                source_file="papers/Fixture/Renamed.lean",
                line=70,
            )
        )
        terminal = surface["terminal_term_dependency_surface"]
        assert isinstance(terminal, dict)
        definitions = terminal["transparent_definitions"]
        assert isinstance(definitions, list) and len(definitions) == 1
        definition = definitions[0]
        assert isinstance(definition, dict)
        # A declaration-text receipt changes when its name changes. Its body,
        # typed surfaces, and semantic flags remain the actual local evidence.
        definition["declaration_sha256"] = digest("9")
        definition["direct_local_dependencies"] = ["Fixture.RenamedModel.distribution"]
        current = raw_audit(boundary=[current_item])

        prior_descriptor = DIFFERENTIAL.source_record_differential_item_descriptor(
            prior_item, section="boundary_input_items"
        )
        current_descriptor = DIFFERENTIAL.source_record_differential_item_descriptor(
            current_item, section="boundary_input_items"
        )
        self.assertEqual(prior_descriptor, current_descriptor)
        normalized = json.dumps(prior_descriptor, sort_keys=True)
        self.assertNotIn("Fixture.PaperInterface.source_result", normalized)
        self.assertNotIn("Fixture.Model.score", normalized)

        overlay, paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertEqual(set(overlay["items"]), {current_key})
        self.assertEqual(
            set(
                DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                    paper_dir, PAPER, current
                )
            ),
            {current_key},
        )

        semantic_change = copy.deepcopy(current_item)
        changed_surface = semantic_change["expanded_lean_surface"]
        assert isinstance(changed_surface, dict)
        changed_terminal = changed_surface["terminal_term_dependency_surface"]
        assert isinstance(changed_terminal, dict)
        changed_definitions = changed_terminal["transparent_definitions"]
        assert isinstance(changed_definitions, list) and len(changed_definitions) == 1
        changed_definition = changed_definitions[0]
        assert isinstance(changed_definition, dict)
        changed_definition["body_sha256"] = digest("a")
        self.assertNotEqual(
            prior_descriptor,
            DIFFERENTIAL.source_record_differential_item_descriptor(
                semantic_change, section="boundary_input_items"
            ),
        )

    def test_binder_surface_rename_remains_manual_without_canonical_atom(self) -> None:
        prior_key = "old_route.h : P x"
        current_key = "new_route.renamed_h : P y"
        prior_item = reusable_input(prior_key, input_type="P x")
        prior_item["expanded_lean_surface"].update(complete_presentation_surfaces())
        prior = raw_audit(boundary=[prior_item])
        judgments = sidecar(prior, {prior_key: {}})

        current_item = reusable_input(current_key, input_type="P y")
        current_item["binder"] = "renamed_h"
        current_item["expanded_lean_surface"].update(
            complete_presentation_surfaces(
                reviewed_declaration="Fixture.RenamedInterface.renamed_route",
                effective_declaration="Fixture.RenamedModel.renamed_route",
            )
        )
        proposition_alias = current_item["expanded_lean_surface"][
            "proposition_alias_expansion"
        ]
        assert isinstance(proposition_alias, dict)
        proposition_alias["expanded_type"] = "P y"
        current = raw_audit(boundary=[current_item])

        self.assertNotEqual(
            DIFFERENTIAL.source_record_differential_item_descriptor(
                prior_item, section="boundary_input_items"
            ),
            DIFFERENTIAL.source_record_differential_item_descriptor(
                current_item, section="boundary_input_items"
            ),
        )
        overlay, _paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertEqual(overlay["items"], {})
        self.assertEqual(
            [entry["current_judgment_key"] for entry in overlay["manual_review_required"]],
            [current_key],
        )

    def test_presentation_rename_without_source_identity_stays_manual(self) -> None:
        prior_key = "old_route.h : P x"
        current_key = "new_route.h : P x"
        prior_item = reusable_input(prior_key)
        prior_item.pop("source_contract_association")
        prior_item["expanded_lean_surface"].update(complete_presentation_surfaces())
        prior = raw_audit(boundary=[prior_item])
        judgments = sidecar(prior, {prior_key: {}})

        current_item = copy.deepcopy(prior_item)
        current_item["judgment_key"] = current_key
        current_item["expanded_lean_surface"].update(
            complete_presentation_surfaces(
                reviewed_declaration="Fixture.RenamedInterface.renamed_route",
                effective_declaration="Fixture.RenamedModel.renamed_route",
            )
        )
        current = raw_audit(boundary=[current_item])

        prior_descriptor = DIFFERENTIAL.source_record_differential_item_descriptor(
            prior_item, section="boundary_input_items"
        )
        current_descriptor = DIFFERENTIAL.source_record_differential_item_descriptor(
            current_item, section="boundary_input_items"
        )
        self.assertNotEqual(prior_descriptor, current_descriptor)
        self.assertIn("Fixture.PaperInterface.source_result", json.dumps(prior_descriptor))
        overlay, _paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertEqual(overlay["items"], {})

    def test_direct_parent_routed_recursive_field_is_reused(self) -> None:
        key = "Fixture.Model.utility"
        prior_recursive = aggregate_only_recursive(
            key,
            structure="Fixture.Model",
            field="utility",
            direct_parent_route=True,
        )
        prior = raw_audit(recursive=[prior_recursive])
        judgments = sidecar(prior, {key: {"classification": "model_data"}})
        current_recursive = copy.deepcopy(prior_recursive)
        current = raw_audit(recursive=[current_recursive])
        overlay, paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertEqual(set(overlay["items"]), {key})
        self.assertEqual(
            set(
                DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                    paper_dir, PAPER, current
                )
            ),
            {key},
        )

    def test_unrouted_recursive_field_requires_manual_review(self) -> None:
        key = "Fixture.Model.utility"
        prior_recursive = aggregate_only_recursive(
            key, structure="Fixture.Model", field="utility"
        )
        prior = raw_audit(recursive=[prior_recursive])
        judgments = sidecar(prior, {key: {"classification": "model_data"}})
        current = raw_audit(recursive=[copy.deepcopy(prior_recursive)])
        overlay, paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertEqual(overlay["items"], {})
        self.assertEqual(
            overlay["manual_review_required"],
            [
                {
                    "current_judgment_key": key,
                    "current_group_semantic_descriptor_sha256": (
                        DIFFERENTIAL._raw_item_groups(current)[0][key]["descriptor_sha256"]
                    ),
                    "reason": "no unique archived descriptor-identical prior response",
                }
            ],
        )
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir, PAPER, current
            ),
            {},
        )

    def test_unrouted_explicit_non_source_recursive_field_is_reused(self) -> None:
        key = "Fixture.Model.dataWitness"
        prior_recursive = aggregate_only_recursive(
            key, structure="Fixture.Model", field="dataWitness"
        )
        prior = raw_audit(recursive=[prior_recursive])
        judgments = sidecar(
            prior,
            {
                key: {
                    "classification": "nonpropositional_witness_data",
                    # A bare source location on a non-credit classification is
                    # an audit annotation, not a source-association credential.
                    "source_location": "source.txt:10-12",
                }
            },
        )
        current = raw_audit(recursive=[copy.deepcopy(prior_recursive)])
        overlay, paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertEqual(set(overlay["items"]), {key})
        metadata = overlay["items"][key][
            DIFFERENTIAL.SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD
        ]
        assert isinstance(metadata, dict)
        self.assertIn(
            DIFFERENTIAL.SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_FIELD,
            metadata,
        )
        self.assertEqual(
            set(
                DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                    paper_dir, PAPER, current
                )
            ),
            {key},
        )
        identity = metadata[
            DIFFERENTIAL.SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_FIELD
        ]
        assert isinstance(identity, dict)
        identity["raw_group_identity"]["canonical_sha256"] = digest("f")
        DIFFERENTIAL.stamp_source_record_differential_revalidation(overlay)
        DIFFERENTIAL.source_record_differential_revalidation_overlay_path(
            paper_dir
        ).write_text(json.dumps(overlay, sort_keys=True), encoding="utf-8")
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir, PAPER, current
            ),
            {},
        )

    def test_mapless_non_source_recursive_reuse_requires_exact_full_raw_member_identity(
        self,
    ) -> None:
        key = "Fixture.Model.container"
        prior_recursive = aggregate_only_recursive(
            key, structure="Fixture.Model", field="container"
        )
        prior_recursive["nested_structures"] = ["Fixture.ChildA"]
        prior = raw_audit(recursive=[prior_recursive])
        judgments = sidecar(
            prior, {key: {"classification": "container_recursively_audited"}}
        )
        current_recursive = copy.deepcopy(prior_recursive)
        # Recursive containment is deliberately normalized out of the
        # descriptor. The mapless lane must nevertheless retain a full raw
        # structural witness rather than treating this as a presentation edit.
        current_recursive["nested_structures"] = ["Fixture.ChildB"]
        current = raw_audit(recursive=[current_recursive])
        self.assertEqual(
            DIFFERENTIAL.source_record_differential_item_descriptor(
                prior_recursive, section="recursive_field_items"
            ),
            DIFFERENTIAL.source_record_differential_item_descriptor(
                current_recursive, section="recursive_field_items"
            ),
        )
        overlay, paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertEqual(overlay["items"], {})
        self.assertTrue(
            any(
                entry.get("reason")
                == "source-free recursive full raw-member identity differs"
                for entry in overlay["decisions"]
            )
        )
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir, PAPER, current
            ),
            {},
        )

    def test_mapless_content_identity_resolves_only_unique_current_descriptor_collision(
        self,
    ) -> None:
        first_key = "Fixture.Model.firstContainer"
        second_key = "Fixture.Model.secondContainer"
        first = aggregate_only_recursive(
            first_key, structure="Fixture.Model", field="firstContainer"
        )
        first["nested_structures"] = ["Fixture.FirstChild"]
        second = aggregate_only_recursive(
            second_key, structure="Fixture.Model", field="secondContainer"
        )
        second["nested_structures"] = ["Fixture.SecondChild"]
        self.assertEqual(
            DIFFERENTIAL.source_record_differential_item_descriptor(
                first, section="recursive_field_items"
            ),
            DIFFERENTIAL.source_record_differential_item_descriptor(
                second, section="recursive_field_items"
            ),
        )
        prior = raw_audit(recursive=[first, second])
        judgments = sidecar(
            prior,
            {
                first_key: {"classification": "container_recursively_audited"},
                second_key: {"classification": "container_recursively_audited"},
            },
        )
        current = raw_audit(recursive=[copy.deepcopy(first), copy.deepcopy(second)])
        overlay, paper_dir, _ordinary_path = self.build_overlay(
            prior, judgments, current
        )
        self.assertEqual(set(overlay["items"]), {first_key, second_key})
        self.assertEqual(
            set(
                DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                    paper_dir, PAPER, current
                )
            ),
            {first_key, second_key},
        )
        first_metadata = overlay["items"][first_key][
            DIFFERENTIAL.SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD
        ]
        assert isinstance(first_metadata, dict)
        first_identity = first_metadata[
            DIFFERENTIAL.SOURCE_FREE_RECURSIVE_STRUCTURAL_IDENTITY_FIELD
        ]
        assert isinstance(first_identity, dict)
        self.assertIn("semantic_content_identity", first_identity)
        content_identity = first_identity["semantic_content_identity"]
        assert isinstance(content_identity, dict)
        content_identity["canonical_sha256"] = digest("e")
        DIFFERENTIAL.stamp_source_record_differential_revalidation(overlay)
        DIFFERENTIAL.source_record_differential_revalidation_overlay_path(
            paper_dir
        ).write_text(json.dumps(overlay, sort_keys=True), encoding="utf-8")
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir, PAPER, current
            ),
            {},
        )

        # A non-presentation containment mutation leaves the descriptor
        # collision intact, but no longer identifies this current group by
        # complete name-free content. The other exact group remains reusable.
        changed_first = copy.deepcopy(first)
        changed_first["nested_structures"] = ["Fixture.ChangedChild"]
        changed_current = raw_audit(
            recursive=[changed_first, copy.deepcopy(second)]
        )
        changed_overlay, _changed_paper_dir, _ordinary_path = self.build_overlay(
            prior, judgments, changed_current
        )
        self.assertEqual(set(changed_overlay["items"]), {second_key})

    def test_mapless_content_identity_rejects_ambiguous_current_collision(self) -> None:
        first_key = "Fixture.Model.firstContainer"
        second_key = "Fixture.Model.secondContainer"
        first = aggregate_only_recursive(
            first_key, structure="Fixture.Model", field="firstContainer"
        )
        second = aggregate_only_recursive(
            second_key, structure="Fixture.Model", field="secondContainer"
        )
        prior = raw_audit(recursive=[first, second])
        judgments = sidecar(
            prior,
            {
                first_key: {"classification": "container_recursively_audited"},
                second_key: {"classification": "container_recursively_audited"},
            },
        )
        current = raw_audit(recursive=[copy.deepcopy(first), copy.deepcopy(second)])
        overlay, paper_dir, _ordinary_path = self.build_overlay(
            prior, judgments, current
        )
        self.assertEqual(overlay["items"], {})
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir, PAPER, current
            ),
            {},
        )

    def test_mapless_non_source_recursive_reuse_rejects_semantic_model_group(self) -> None:
        first_key = "Fixture.Model.firstWitness"
        second_key = "Fixture.Model.secondWitness"
        first = aggregate_only_recursive(
            first_key, structure="Fixture.Model", field="firstWitness"
        )
        first["nested_structures"] = ["Fixture.FirstChild"]
        second = aggregate_only_recursive(
            second_key, structure="Fixture.Model", field="secondWitness"
        )
        second["nested_structures"] = ["Fixture.SecondChild"]
        prior = raw_audit(
            recursive=[first, second],
            semantic=[semantic_model_item(first_key), semantic_model_item(second_key)],
        )
        judgments = sidecar(
            prior,
            {
                first_key: {"classification": "nonpropositional_witness_data"},
                second_key: {"classification": "nonpropositional_witness_data"},
            },
        )
        current = raw_audit(
            recursive=[copy.deepcopy(first), copy.deepcopy(second)],
            semantic=[
                semantic_model_item(first_key),
                semantic_model_item(second_key),
            ],
        )
        overlay, paper_dir, _ordinary_path = self.build_overlay(
            prior, judgments, current
        )
        self.assertEqual(overlay["items"], {})
        self.assertTrue(
            any(
                entry.get("reason")
                == "source-free recursive content fallback cannot select a semantic-model group"
                for entry in overlay["decisions"]
            )
        )
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir, PAPER, current
            ),
            {},
        )

    def test_mapless_non_source_recursive_reuse_rejects_source_credit_pin(self) -> None:
        key = "Fixture.Model.dataWitness"
        prior_recursive = aggregate_only_recursive(
            key, structure="Fixture.Model", field="dataWitness"
        )
        prior = raw_audit(recursive=[prior_recursive])
        judgments = sidecar(
            prior,
            {
                key: {
                    "classification": "nonpropositional_witness_data",
                    "semantic_association_sha256": digest("f"),
                }
            },
        )
        current = raw_audit(recursive=[copy.deepcopy(prior_recursive)])
        overlay, paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertEqual(overlay["items"], {})
        self.assertTrue(
            any(
                "source-credit field `semantic_association_sha256`" in entry.get(
                    "reason", ""
                )
                for entry in overlay["decisions"]
            )
        )
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir, PAPER, current
            ),
            {},
        )

    def test_mapless_non_source_recursive_reuse_rejects_raw_source_association(
        self,
    ) -> None:
        key = "Fixture.Model.dataWitness"
        prior_recursive = aggregate_only_recursive(
            key, structure="Fixture.Model", field="dataWitness"
        )
        prior_recursive["source_statement_association"] = source_association()
        prior = raw_audit(recursive=[prior_recursive])
        judgments = sidecar(
            prior, {key: {"classification": "nonpropositional_witness_data"}}
        )
        current = raw_audit(recursive=[copy.deepcopy(prior_recursive)])
        overlay, paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertEqual(overlay["items"], {})
        self.assertTrue(
            any(
                "carries a source association" in entry.get("reason", "")
                for entry in overlay["decisions"]
            )
        )
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir, PAPER, current
            ),
            {},
        )

    def test_unrouted_source_credit_recursive_field_stays_manual(self) -> None:
        key = "Fixture.Model.sourceCondition"
        prior_recursive = aggregate_only_recursive(
            key, structure="Fixture.Model", field="sourceCondition"
        )
        prior = raw_audit(recursive=[prior_recursive])
        judgments = sidecar(
            prior, {key: {"classification": "validated_source_assumption"}}
        )
        current = raw_audit(recursive=[copy.deepcopy(prior_recursive)])
        overlay, paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertEqual(overlay["items"], {})
        self.assertTrue(
            any(
                entry.get("reason")
                == "recursive field lacks a locally authenticated direct semantic parent route"
                for entry in overlay["decisions"]
            )
        )
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir, PAPER, current
            ),
            {},
        )

    def test_recursive_route_descriptor_uses_opaque_scope_not_field_strings(self) -> None:
        key = "Fixture.Model.utility"
        original = aggregate_only_recursive(
            key,
            structure="Fixture.Model",
            field="utility",
            direct_parent_route=True,
        )
        descriptor = DIFFERENTIAL.source_record_differential_item_descriptor(
            original, section="recursive_field_items"
        )
        self.assertNotIn("recursive_structural_coordinate_sha256", descriptor)
        self.assertEqual(
            descriptor["recursive_field_direct_semantic_parent"][
                "field_scope_sha256"
            ],
            digest("e"),
        )
        serialized = json.dumps(descriptor, sort_keys=True)
        self.assertNotIn("Fixture.Model", serialized)
        self.assertNotIn("utility", serialized)

        changed_scope = copy.deepcopy(original)
        route = changed_scope["recursive_field_explicit_parent_route"]
        assert isinstance(route, dict)
        route["field_scope_sha256"] = digest("9")
        route["association_sha256"] = recursive_field_parent_route_record_digest(route)
        self.assertNotEqual(
            descriptor,
            DIFFERENTIAL.source_record_differential_item_descriptor(
                changed_scope, section="recursive_field_items"
            ),
        )

    def test_summary_only_current_rewrite_preserves_overlay_but_new_receipt_does_not(
        self,
    ) -> None:
        key = "input.h : P"
        prior = raw_audit(boundary=[reusable_input(key)])
        judgments = sidecar(prior, {key: {}})
        current = raw_audit(boundary=[reusable_input(key)])
        overlay, paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        current_path = paper_dir / "audit" / "source_record_audit.json"

        refreshed_summary = copy.deepcopy(current)
        refreshed_summary["current_source_record_judgment_count"] = 1
        refreshed_summary["resolved_conclusion_dependency_count"] = 1
        current_path.write_text(
            json.dumps(refreshed_summary, indent=2, sort_keys=True), encoding="utf-8"
        )
        self.assertNotEqual(
            hashlib.sha256(current_path.read_bytes()).hexdigest(),
            overlay["current_raw_audit"]["file_sha256"],
        )
        self.assertEqual(
            refreshed_summary["source_record_audit_sha256"],
            current["source_record_audit_sha256"],
        )
        self.assertEqual(
            refreshed_summary["source_record_audit_integrity_sha256"],
            current["source_record_audit_integrity_sha256"],
        )
        self.assertEqual(
            set(
                DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                    paper_dir, PAPER, refreshed_summary
                )
            ),
            {key},
        )

        changed_semantics = copy.deepcopy(refreshed_summary)
        changed_semantics["boundary_input_items"][0]["expanded_input_type"] = "Q x"
        changed_semantics["boundary_input_items"][0]["expanded_lean_surface"][
            "input_type"
        ] = "Q x"
        stamp_source_record_audit_receipts(changed_semantics)
        current_path.write_text(
            json.dumps(changed_semantics, sort_keys=True), encoding="utf-8"
        )
        self.assertNotEqual(
            changed_semantics["source_record_audit_sha256"],
            current["source_record_audit_sha256"],
        )
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir, PAPER, changed_semantics
            ),
            {},
        )

    def test_formalization_scope_change_requires_manual_review(self) -> None:
        key = "input.h : P"
        prior = raw_audit(boundary=[reusable_input(key)])
        prior["formalization_scope"] = None
        stamp_source_record_audit_receipts(prior)
        judgments = sidecar(prior, {key: {}})
        current = copy.deepcopy(prior)
        current["formalization_scope"] = {
            "target_result_declarations": ["Fixture.PaperInterface.source_result"],
            "semantic_contract": "governing target changed",
        }
        stamp_source_record_audit_receipts(current)

        overlay, paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertEqual(overlay["items"], {})
        self.assertEqual(
            [entry["current_judgment_key"] for entry in overlay["manual_review_required"]],
            [key],
        )
        prior_group = DIFFERENTIAL._raw_item_groups(prior)[0][key]
        current_group = DIFFERENTIAL._raw_item_groups(current)[0][key]
        self.assertNotEqual(
            prior_group["descriptor_sha256"], current_group["descriptor_sha256"]
        )
        self.assertEqual(
            prior_group["descriptor"]["raw_formalization_scope"],
            {"state": "explicit_null"},
        )
        self.assertEqual(
            current_group["descriptor"]["raw_formalization_scope"]["state"],
            "present",
        )
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir, PAPER, current
            ),
            {},
        )

    def test_absent_and_explicit_null_formalization_scope_differ(self) -> None:
        key = "input.h : P"
        absent = raw_audit(boundary=[reusable_input(key)])
        explicit_null = copy.deepcopy(absent)
        explicit_null["formalization_scope"] = None
        stamp_source_record_audit_receipts(explicit_null)
        absent_scope = DIFFERENTIAL._raw_item_groups(absent)[0][key]["descriptor"]
        null_scope = DIFFERENTIAL._raw_item_groups(explicit_null)[0][key]["descriptor"]
        self.assertEqual(absent_scope["raw_formalization_scope"], {"state": "absent"})
        self.assertEqual(
            null_scope["raw_formalization_scope"], {"state": "explicit_null"}
        )

    def test_semantic_association_rebind_requires_valid_archived_and_current_content(
        self,
    ) -> None:
        key = "input.h : P"
        prior_input = reusable_input(key)
        prior = raw_audit(boundary=[prior_input])
        valid_pin = prior_input["source_contract_association"][
            "semantic_association_sha256"
        ]

        stale_response = sidecar(
            prior, {key: {"semantic_association_sha256": digest("f")}}
        )
        current = raw_audit(boundary=[reusable_input(key)])
        overlay, _paper_dir, _ordinary_path = self.build_overlay(
            prior, stale_response, current
        )
        self.assertEqual(overlay["items"], {})
        self.assertIn(
            "not present on the archived generated group",
            overlay["decisions"][0]["reason"],
        )

        current_bad_association = reusable_input(key)
        current_bad_association["source_contract_association"][
            "semantic_association_sha256"
        ] = digest("f")
        current = raw_audit(boundary=[current_bad_association])
        overlay, _paper_dir, _ordinary_path = self.build_overlay(
            prior,
            sidecar(prior, {key: {"semantic_association_sha256": valid_pin}}),
            current,
        )
        self.assertEqual(overlay["items"], {})
        self.assertIn(
            "current generated association content is absent or ambiguous",
            overlay["decisions"][0]["reason"],
        )

    def test_recursive_parent_route_rebind_requires_identical_route_and_raw_group(
        self,
    ) -> None:
        key = "Fixture.Model.endpointDensityMeasurable"
        prior_recursive = aggregate_only_recursive(
            key,
            structure="Fixture.Model",
            field="endpointDensityMeasurable",
            direct_parent_route=True,
        )
        prior = raw_audit(recursive=[prior_recursive])
        route = prior_recursive["recursive_field_explicit_parent_route"]
        assert isinstance(route, dict)
        parent_pin = route["parent_source_association_sha256"]
        assert isinstance(parent_pin, str)
        judgments = sidecar(
            prior,
            {
                key: {
                    "classification": "approved_source_convention",
                    "semantic_association_sha256": parent_pin,
                }
            },
        )
        current = raw_audit(recursive=[copy.deepcopy(prior_recursive)])
        overlay, paper_dir, _ordinary_path = self.build_overlay(
            prior, judgments, current
        )
        self.assertEqual(set(overlay["items"]), {key})
        metadata = overlay["items"][key][
            DIFFERENTIAL.SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD
        ]
        assert isinstance(metadata, dict)
        receipt = metadata[DIFFERENTIAL.SEMANTIC_ASSOCIATION_REBIND_FIELD]
        assert isinstance(receipt, dict)
        self.assertEqual(
            receipt["prior_response_semantic_association_sha256"], parent_pin
        )
        self.assertEqual(
            receipt["current_semantic_association_sha256"], parent_pin
        )
        self.assertIn("recursive_parent_route_raw_group_identity", receipt)
        self.assertEqual(
            set(
                DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                    paper_dir, PAPER, current
                )
            ),
            {key},
        )

        # The semantic descriptor intentionally ignores presentation line
        # numbers. A recursive parent-route response nevertheless requires an
        # exact raw group, so a presentation-only raw mutation cannot reuse it.
        changed_raw = copy.deepcopy(prior_recursive)
        changed_raw["line"] = 99
        changed = raw_audit(recursive=[changed_raw])
        overlay, _paper_dir, _ordinary_path = self.build_overlay(
            prior, judgments, changed
        )
        self.assertEqual(overlay["items"], {})
        self.assertTrue(
            any(
                "recursive parent-route complete receipt reissue prior/current raw groups differ"
                in entry.get("reason", "")
                for entry in overlay["decisions"]
            ),
            overlay["decisions"],
        )

        missing_route = copy.deepcopy(prior_recursive)
        missing_route.pop("recursive_field_explicit_parent_route")
        missing = raw_audit(recursive=[missing_route])
        overlay, _paper_dir, _ordinary_path = self.build_overlay(
            prior, judgments, missing
        )
        self.assertEqual(overlay["items"], {})

        changed_route = copy.deepcopy(prior_recursive)
        current_route = changed_route["recursive_field_explicit_parent_route"]
        assert isinstance(current_route, dict)
        current_route["field_scope_sha256"] = digest("9")
        current_route["association_sha256"] = recursive_field_parent_route_record_digest(
            current_route
        )
        changed = raw_audit(recursive=[changed_route])
        overlay, _paper_dir, _ordinary_path = self.build_overlay(
            prior, judgments, changed
        )
        self.assertEqual(overlay["items"], {})

    def test_routed_recursive_field_reuses_across_parent_result_change_only(self) -> None:
        """A child route tracks its source model domain, not parent result text."""

        key = "Fixture.Model.endpointDensityMeasurable"
        prior_field = aggregate_only_recursive(
            key,
            structure="Fixture.Model",
            field="endpointDensityMeasurable",
            direct_parent_route=True,
        )
        prior_route = prior_field["recursive_field_explicit_parent_route"]
        assert isinstance(prior_route, dict)
        prior_parent = direct_source_domain_parent(prior_route)
        prior = raw_audit(recursive=[prior_field], semantic=[prior_parent])
        prior_pin = prior_route["parent_source_association_sha256"]
        assert isinstance(prior_pin, str)
        judgments = sidecar(
            prior,
            {
                key: {
                    "classification": "approved_source_convention",
                    "semantic_association_sha256": prior_pin,
                }
            },
        )

        current_field = copy.deepcopy(prior_field)
        advance_recursive_parent_signature(current_field, signature=digest("9"))
        current_route = current_field["recursive_field_explicit_parent_route"]
        assert isinstance(current_route, dict)
        current_parent = direct_source_domain_parent(
            current_route, result_type="CorrectedResult"
        )
        current = raw_audit(recursive=[current_field], semantic=[current_parent])

        prior_group = DIFFERENTIAL._raw_item_groups(prior)[0][key]
        current_group = DIFFERENTIAL._raw_item_groups(current)[0][key]
        self.assertEqual(
            prior_group["descriptor"], current_group["descriptor"],
            "the parent input-domain contract should ignore a result-only change",
        )
        overlay, paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertEqual(set(overlay["items"]), {key})
        self.assertIn(
            "semantic-model::direct_source_domain_parent",
            {
                item["current_judgment_key"]
                for item in overlay["manual_review_required"]
            },
        )
        metadata = overlay["items"][key][
            DIFFERENTIAL.SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD
        ]
        assert isinstance(metadata, dict)
        rebind = metadata[DIFFERENTIAL.SEMANTIC_ASSOCIATION_REBIND_FIELD]
        assert isinstance(rebind, dict)
        self.assertNotIn("recursive_parent_route_raw_group_identity", rebind)
        self.assertEqual(
            rebind["current_semantic_association_sha256"],
            current_route["parent_source_association_sha256"],
        )
        loaded = DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
            paper_dir, PAPER, current
        )
        self.assertEqual(set(loaded), {key})
        self.assertEqual(
            loaded[key]["semantic_association_sha256"],
            current_route["parent_source_association_sha256"],
        )

    def test_routed_recursive_field_parent_input_domain_change_stays_manual(self) -> None:
        """A changed direct source-model premise cannot inherit child approval."""

        key = "Fixture.Model.endpointDensityMeasurable"
        prior_field = aggregate_only_recursive(
            key,
            structure="Fixture.Model",
            field="endpointDensityMeasurable",
            direct_parent_route=True,
        )
        prior_route = prior_field["recursive_field_explicit_parent_route"]
        assert isinstance(prior_route, dict)
        prior = raw_audit(
            recursive=[prior_field], semantic=[direct_source_domain_parent(prior_route)]
        )
        prior_pin = prior_route["parent_source_association_sha256"]
        assert isinstance(prior_pin, str)
        judgments = sidecar(
            prior,
            {
                key: {
                    "classification": "approved_source_convention",
                    "semantic_association_sha256": prior_pin,
                }
            },
        )

        current_field = copy.deepcopy(prior_field)
        advance_recursive_parent_signature(current_field, signature=digest("9"))
        current_route = current_field["recursive_field_explicit_parent_route"]
        assert isinstance(current_route, dict)
        current = raw_audit(
            recursive=[current_field],
            semantic=[
                direct_source_domain_parent(
                    current_route,
                    result_type="CorrectedResult",
                    binder_domains=[
                        {
                            "expanded_type": "Fixture.Model x",
                            "alpha_normalized_type": "Fixture.Model _f0",
                        },
                        {
                            "expanded_type": "NewRequiredPremise x",
                            "alpha_normalized_type": "NewRequiredPremise _f0",
                        },
                    ],
                )
            ],
        )

        overlay, _paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertEqual(overlay["items"], {})
        self.assertIn(
            key,
            {
                item["current_judgment_key"]
                for item in overlay["manual_review_required"]
            },
        )

    def test_routed_recursive_field_reuse_does_not_select_by_root_name(self) -> None:
        """An authenticated type/pin route survives a display-root rename."""

        key = "Fixture.Model.endpointDensityMeasurable"
        prior_field = aggregate_only_recursive(
            key,
            structure="Fixture.Model",
            field="endpointDensityMeasurable",
            direct_parent_route=True,
        )
        prior_route = prior_field["recursive_field_explicit_parent_route"]
        assert isinstance(prior_route, dict)
        prior = raw_audit(
            recursive=[prior_field], semantic=[direct_source_domain_parent(prior_route)]
        )
        prior_pin = prior_route["parent_source_association_sha256"]
        assert isinstance(prior_pin, str)
        judgments = sidecar(
            prior,
            {
                key: {
                    "classification": "approved_source_convention",
                    "semantic_association_sha256": prior_pin,
                }
            },
        )

        current_field = copy.deepcopy(prior_field)
        current_route = current_field["recursive_field_explicit_parent_route"]
        assert isinstance(current_route, dict)
        current_route["root_record"] = "Fixture.RenamedModel"
        current_route["association_sha256"] = recursive_field_parent_route_record_digest(
            current_route
        )
        current = raw_audit(
            recursive=[current_field],
            semantic=[
                direct_source_domain_parent(
                    current_route, record_roots=["Fixture.RenamedModel"]
                )
            ],
        )

        prior_group = DIFFERENTIAL._raw_item_groups(prior)[0][key]
        current_group = DIFFERENTIAL._raw_item_groups(current)[0][key]
        self.assertEqual(prior_group["descriptor"], current_group["descriptor"])
        overlay, paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertEqual(set(overlay["items"]), {key})
        loaded = DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
            paper_dir, PAPER, current
        )
        self.assertEqual(set(loaded), {key})

    def test_routed_recursive_field_source_anchor_change_stays_manual(self) -> None:
        """A source-map anchor change invalidates an otherwise equal child."""

        key = "Fixture.Model.endpointDensityMeasurable"
        prior_field = aggregate_only_recursive(
            key,
            structure="Fixture.Model",
            field="endpointDensityMeasurable",
            direct_parent_route=True,
        )
        prior_route = prior_field["recursive_field_explicit_parent_route"]
        assert isinstance(prior_route, dict)
        prior = raw_audit(
            recursive=[prior_field], semantic=[direct_source_domain_parent(prior_route)]
        )
        prior_pin = prior_route["parent_source_association_sha256"]
        assert isinstance(prior_pin, str)
        judgments = sidecar(
            prior,
            {
                key: {
                    "classification": "approved_source_convention",
                    "semantic_association_sha256": prior_pin,
                }
            },
        )

        current_field = copy.deepcopy(prior_field)
        current_route = current_field["recursive_field_explicit_parent_route"]
        assert isinstance(current_route, dict)
        identities = current_route["source_item_identities"]
        assert isinstance(identities, list) and len(identities) == 1
        identity = identities[0]
        assert isinstance(identity, dict)
        identity["source_map_item_sha256"] = digest("changed source anchor")
        current_route["association_sha256"] = recursive_field_parent_route_record_digest(
            current_route
        )
        current = raw_audit(
            recursive=[current_field],
            semantic=[direct_source_domain_parent(current_route)],
        )

        overlay, _paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertEqual(overlay["items"], {})
        self.assertIn(
            key,
            {
                item["current_judgment_key"]
                for item in overlay["manual_review_required"]
            },
        )

    def test_legacy_semantic_association_overlay_rebinds_only_after_recomputation(
        self,
    ) -> None:
        key = "input.h : P"
        prior_input = reusable_input(key)
        prior = raw_audit(boundary=[prior_input])
        judgments = sidecar(
            prior,
            {
                key: {
                    "semantic_association_sha256": prior_input[
                        "source_contract_association"
                    ]["semantic_association_sha256"],
                }
            },
        )
        current_input = reusable_input(key, signature=digest("8"))
        current = raw_audit(boundary=[current_input])
        overlay, paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        item = overlay["items"][key]
        assert isinstance(item, dict)
        metadata = item[DIFFERENTIAL.SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD]
        assert isinstance(metadata, dict)
        metadata.pop(DIFFERENTIAL.SEMANTIC_ASSOCIATION_REBIND_FIELD)
        DIFFERENTIAL.stamp_source_record_differential_revalidation(overlay)
        DIFFERENTIAL.source_record_differential_revalidation_overlay_path(paper_dir).write_text(
            json.dumps(overlay, sort_keys=True), encoding="utf-8"
        )
        loaded = DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
            paper_dir, PAPER, current
        )
        self.assertEqual(set(loaded), {key})
        self.assertEqual(
            loaded[key]["semantic_association_sha256"],
            current_input["source_contract_association"]["semantic_association_sha256"],
        )

    def test_loader_transports_only_a_canonical_receipt_bound_status_projection(
        self,
    ) -> None:
        """A differential response advances only through the exact current receipt."""

        key = "input.h : P"
        source_key = "opaque_source_item"
        source_item = {
            "source_location": "source.txt:4-8",
            "source_status": "administrative_review_complete",
            "source_note": "The source statement was independently checked.",
            "lean_declarations": ["Fixture.PaperInterface.source_result"],
            "source_model": {"carrier": "finite"},
        }
        source_map = {"items": {source_key: source_item}}

        def legacy_status_projection_input() -> dict[str, object]:
            item = reusable_input(key)
            association = item["source_contract_association"]
            assert isinstance(association, dict)
            signature = association["reviewed_elaborated_signature_identity"]
            assert isinstance(signature, dict)
            legacy_semantic = (
                DISPOSITION.legacy_source_item_coverage_sha256_schema4_direct_source_status_excluded(
                    source_item, ""
                )
            )
            association["source_item_identities"] = [
                {
                    "source_key": source_key,
                    "source_location": source_item["source_location"],
                    "source_map_item_sha256": DISPOSITION.source_map_item_record_digest(
                        source_item
                    ),
                    "source_semantic_sha256": legacy_semantic,
                }
            ]
            association["semantic_association_sha256"] = (
                semantic_association_record_digest([legacy_semantic], signature)
            )
            return item

        prior_input = legacy_status_projection_input()
        prior = raw_audit(boundary=[prior_input])
        judgments = sidecar(
            prior,
            {
                key: {
                    "semantic_association_sha256": prior_input[
                        "source_contract_association"
                    ]["semantic_association_sha256"],
                }
            },
        )
        current_input = legacy_status_projection_input()
        current = raw_audit(boundary=[current_input])
        _overlay, paper_dir, _ordinary_path = self.build_overlay(
            prior, judgments, current
        )
        current_path = paper_dir / "audit" / "source_record_audit.json"
        map_path = paper_dir / "audit" / "paper_statement_map.json"
        map_bytes = json.dumps(source_map, sort_keys=True).encode("utf-8")
        map_path.write_bytes(map_bytes)
        receipt, error = DISPOSITION.build_administrative_projection_rebind(
            paper=PAPER,
            raw_audit=current,
            raw_audit_bytes=current_path.read_bytes(),
            raw_audit_relative_path="audit/source_record_audit.json",
            statement_map=source_map,
            statement_map_bytes=map_bytes,
            statement_map_relative_path="audit/paper_statement_map.json",
        )
        self.assertEqual(error, "")
        assert isinstance(receipt, dict)
        receipt_path = (
            paper_dir
            / "audit"
            / DISPOSITION.SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME
        )
        receipt_path.write_text(json.dumps(receipt, sort_keys=True), encoding="utf-8")

        loaded = DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
            paper_dir, PAPER, current
        )
        self.assertEqual(set(loaded), {key})
        expected_semantic = DISPOSITION.source_item_coverage_sha256(source_item, "")
        signature = current_input["source_contract_association"][
            "reviewed_elaborated_signature_identity"
        ]
        assert isinstance(signature, dict)
        self.assertEqual(
            loaded[key]["semantic_association_sha256"],
            semantic_association_record_digest([expected_semantic], signature),
        )

        # Recomputing a self-pin cannot conceal a changed source note. The
        # canonical receipt is bound to the complete raw map item, not merely
        # the direct status field or the semantic hash being transported.
        changed_map = copy.deepcopy(source_map)
        changed_item = changed_map["items"][source_key]
        assert isinstance(changed_item, dict)
        changed_item["source_note"] = "A materially changed source note."
        map_path.write_text(json.dumps(changed_map, sort_keys=True), encoding="utf-8")
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir, PAPER, current
            ),
            {},
        )

    def test_archived_administrative_projection_rebind_is_inert_but_invalid_canonical_rejects(
        self,
    ) -> None:
        """Historical rebind bytes cannot become an active loader input by resemblance.

        A receipt that was exact for an older raw/map pair must be retained under
        a noncanonical archival name once its inputs are no longer available.
        The active canonical basename remains fail-closed: putting those same
        invalid bytes back there blocks all differential reuse.
        """

        key = "input.h : P"
        prior = raw_audit(boundary=[reusable_input(key)])
        current = raw_audit(boundary=[reusable_input(key)])
        judgments = sidecar(prior, {key: {}})
        _overlay, paper_dir, _ordinary_path = self.build_overlay(
            prior, judgments, current
        )

        audit_dir = paper_dir / "audit"
        archived_receipt_path = (
            audit_dir
            / "source_record_administrative_projection_rebind.superseded_2026-07-28.json"
        )
        historical_bytes = b'{"historical_receipt":"no-longer-bound-to-current-inputs"}\n'
        archived_receipt_path.write_bytes(historical_bytes)

        # The canonical loader intentionally does not glob or infer archival
        # names.  The overlay remains usable without a current rebind receipt.
        self.assertEqual(
            set(
                DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                    paper_dir, PAPER, current
                )
            ),
            {key},
        )
        self.assertEqual(archived_receipt_path.read_bytes(), historical_bytes)

        # An equally malformed artifact at the active canonical path is not a
        # no-op: it must stop loading rather than silently fall back.
        (audit_dir / "paper_statement_map.json").write_text(
            json.dumps({"items": {}}, sort_keys=True), encoding="utf-8"
        )
        canonical_receipt_path = (
            audit_dir
            / DISPOSITION.SOURCE_RECORD_ADMINISTRATIVE_PROJECTION_REBIND_BASENAME
        )
        canonical_receipt_path.write_bytes(historical_bytes)
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir, PAPER, current
            ),
            {},
        )

    def test_unique_semantic_descriptor_can_follow_a_renamed_storage_key(self) -> None:
        prior_key = "old_name.h : P"
        current_key = "new_name.h : P"
        prior = raw_audit(boundary=[reusable_input(prior_key)])
        judgments = sidecar(prior, {prior_key: {}})
        current = raw_audit(boundary=[reusable_input(current_key)])
        overlay, paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertEqual(set(overlay["items"]), {current_key})
        item = overlay["items"][current_key]
        assert isinstance(item, dict)
        metadata = item[DIFFERENTIAL.SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD]
        assert isinstance(metadata, dict)
        self.assertEqual(metadata["prior_judgment_key"], prior_key)
        self.assertEqual(metadata["current_judgment_key"], current_key)
        self.assertEqual(
            set(
                DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                    paper_dir, PAPER, current
                )
            ),
            {current_key},
        )

    def test_authenticated_overlay_wins_over_stale_ordinary_collision(self) -> None:
        """An archived local receipt cannot overwrite a current association rebind."""

        key = "input.h : P"
        prior_input = reusable_input(key)
        prior = raw_audit(boundary=[prior_input])
        judgments = sidecar(
            prior,
            {
                key: {
                    "semantic_association_sha256": prior_input[
                        "source_contract_association"
                    ]["semantic_association_sha256"],
                }
            },
        )
        current_input = reusable_input(key, signature=digest("8"))
        current = raw_audit(boundary=[current_input])
        _overlay, paper_dir, ordinary_path = self.build_overlay(prior, judgments, current)

        # This recreates the normal closeout layout: the live sidecar retains
        # historical per-item evidence while the separate authenticated overlay
        # binds its semantically unchanged local obligation to the new endpoint.
        ordinary_path.write_text(json.dumps(judgments, sort_keys=True), encoding="utf-8")
        expected_association = current_input["source_contract_association"][
            "semantic_association_sha256"
        ]

        repository_items = REPOSITORY.source_record_judgment_items(
            ordinary_path, PAPER, current_raw_audit=current, paper_dir=paper_dir
        )
        self.assertTrue(
            DIFFERENTIAL.is_loaded_source_record_differential_revalidation_item(
                repository_items[key]
            )
        )
        self.assertEqual(
            repository_items[key]["semantic_association_sha256"], expected_association
        )

        with patch.object(EVIDENCE, "source_record_audit_identity_error", return_value=""):
            evidence_items = EVIDENCE.current_source_record_judgment_items(
                current, judgments, folder=paper_dir
            )
        self.assertTrue(
            DIFFERENTIAL.is_loaded_source_record_differential_revalidation_item(
                evidence_items[key]
            )
        )
        self.assertEqual(
            evidence_items[key]["semantic_association_sha256"], expected_association
        )

        with patch.object(CONCLUSION, "PAPERS", paper_dir.parent):
            conclusion_items = CONCLUSION.current_judgments(PAPER, current)
        self.assertTrue(
            DIFFERENTIAL.is_loaded_source_record_differential_revalidation_item(
                conclusion_items[key]
            )
        )
        self.assertEqual(
            conclusion_items[key]["semantic_association_sha256"], expected_association
        )

        helper = load_source_record_audit_helper()
        helper_items = helper.current_source_record_judgments(paper_dir, PAPER, current)
        self.assertTrue(
            DIFFERENTIAL.is_loaded_source_record_differential_revalidation_item(
                helper_items[key]
            )
        )
        self.assertEqual(
            helper_items[key]["semantic_association_sha256"], expected_association
        )

    def test_current_ordinary_response_wins_over_every_overlay_collision(self) -> None:
        """A fresh ordinary review is newer evidence than a rebind overlay."""

        key = "input.h : P"
        prior_input = reusable_input(key)
        prior = raw_audit(boundary=[prior_input])
        prior_judgments = sidecar(prior, {key: {}})
        current_input = reusable_input(key, signature=digest("8"))
        current = raw_audit(boundary=[current_input])
        _overlay, paper_dir, ordinary_path = self.build_overlay(
            prior, prior_judgments, current
        )

        ordinary_current = sidecar(
            current,
            {
                key: {
                    "classification": "ordinary_current_preferred",
                    "semantic_association_sha256": current_input[
                        "source_contract_association"
                    ]["semantic_association_sha256"],
                }
            },
        )
        ordinary_path.write_text(
            json.dumps(ordinary_current, sort_keys=True), encoding="utf-8"
        )

        repository_items = REPOSITORY.source_record_judgment_items(
            ordinary_path, PAPER, current_raw_audit=current, paper_dir=paper_dir
        )
        self.assertEqual(
            repository_items[key]["classification"], "ordinary_current_preferred"
        )
        self.assertFalse(
            DIFFERENTIAL.is_loaded_source_record_differential_revalidation_item(
                repository_items[key]
            )
        )

        with patch.object(EVIDENCE, "source_record_audit_identity_error", return_value=""):
            evidence_items = EVIDENCE.current_source_record_judgment_items(
                current, ordinary_current, folder=paper_dir
            )
        self.assertEqual(
            evidence_items[key]["classification"], "ordinary_current_preferred"
        )
        self.assertFalse(
            DIFFERENTIAL.is_loaded_source_record_differential_revalidation_item(
                evidence_items[key]
            )
        )

        helper = load_source_record_audit_helper()
        helper_items = helper.current_source_record_judgments(paper_dir, PAPER, current)
        self.assertEqual(
            helper_items[key]["classification"], "ordinary_current_preferred"
        )
        self.assertFalse(
            DIFFERENTIAL.is_loaded_source_record_differential_revalidation_item(
                helper_items[key]
            )
        )

    def test_loader_builds_descriptor_groups_once_per_authenticated_raw_receipt(self) -> None:
        first = "first.h : P"
        second = "second.h : Q"
        prior = raw_audit(
            boundary=[
                reusable_input(first, input_type="P x"),
                reusable_input(second, input_type="Q x"),
            ]
        )
        judgments = sidecar(prior, {first: {}, second: {}})
        current = raw_audit(
            boundary=[
                reusable_input(first, input_type="P x"),
                reusable_input(second, input_type="Q x"),
            ]
        )
        _overlay, paper_dir, _ordinary_path = self.build_overlay(
            prior, judgments, current
        )
        with patch.object(
            DIFFERENTIAL,
            "_raw_item_groups",
            wraps=DIFFERENTIAL._raw_item_groups,
        ) as groups:
            loaded = DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir, PAPER, current
        )
        self.assertEqual(set(loaded), {first, second})
        # The loader now needs one prior grouping to reauthenticate archived
        # item provenance and one current grouping to authenticate the
        # receiving descriptor index.  Neither is repeated per item.
        self.assertEqual(groups.call_count, 2)

    def test_repository_relative_provenance_normalizes_absolute_paths(self) -> None:
        relative = Path("papers") / PAPER / "audit" / "source_record_audit.json"
        absolute = ROOT / relative
        self.assertEqual(
            DIFFERENTIAL._stable_provenance_path(relative),
            DIFFERENTIAL._stable_provenance_path(absolute),
        )
        self.assertEqual(
            DIFFERENTIAL._repository_provenance_path(relative.as_posix()),
            absolute.resolve(),
        )
        for invalid in ("../outside.json", "./papers/audit.json", "/tmp/outside.json"):
            with self.assertRaises(DIFFERENTIAL.SourceRecordDifferentialRevalidationError):
                DIFFERENTIAL._repository_provenance_path(invalid)

    def test_loader_accepts_relative_receipt_from_absolute_paper_path(self) -> None:
        key = "input.h : P"
        prior = raw_audit(boundary=[reusable_input(key)])
        judgments = sidecar(prior, {key: {}})
        current = raw_audit(boundary=[reusable_input(key)])
        overlay, paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertEqual(
            overlay["current_raw_audit"]["path"],
            (Path("papers") / PAPER / "audit" / "source_record_audit.json").as_posix(),
        )
        self.assertEqual(
            set(
                DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                    paper_dir.resolve(), PAPER, current
                )
            ),
            {key},
        )

    def test_loader_replays_archived_current_receipt_only_with_its_issued_path(self) -> None:
        """Historical bytes need an explicit logical issuance path, not a swap."""

        key = "input.h : P"
        prior = raw_audit(boundary=[reusable_input(key)])
        judgments = sidecar(prior, {key: {}})
        current = raw_audit(boundary=[reusable_input(key)])
        _overlay, paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        canonical_path = paper_dir / "audit" / "source_record_audit.json"
        archive_path = paper_dir / "audit" / "source_record_audit.archived.json"
        archive_path.write_text(json.dumps(current, sort_keys=True), encoding="utf-8")

        # The archive itself has a different storage path, so it cannot be
        # silently substituted for an overlay issued at the canonical path.
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir,
                PAPER,
                current,
                current_raw_audit_path=archive_path,
            ),
            {},
        )
        loaded = DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
            paper_dir,
            PAPER,
            current,
            current_raw_audit_path=archive_path,
            current_raw_audit_provenance_path=canonical_path,
        )
        self.assertEqual(set(loaded), {key})

        # A path override is still exact archive evidence: altered bytes may
        # not be paired with an unchanged in-memory semantic receipt.
        archive_path.write_text("{}", encoding="utf-8")
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir,
                PAPER,
                current,
                current_raw_audit_path=archive_path,
                current_raw_audit_provenance_path=canonical_path,
            ),
            {},
        )

    def test_differential_chain_preserves_an_authenticated_prior_overlay(self) -> None:
        """A B-to-C overlay can replay a materialized A-to-B receipt chain."""

        key = "input.h : P"
        prior = raw_audit(boundary=[reusable_input(key)])
        judgments = sidecar(prior, {key: {}})
        middle = raw_audit(boundary=[reusable_input(key)])
        _first_overlay, paper_dir, _ordinary_path = self.build_overlay(
            prior, judgments, middle
        )
        canonical_path = paper_dir / "audit" / "source_record_audit.json"
        middle_items = DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
            paper_dir, PAPER, middle
        )
        self.assertEqual(set(middle_items), {key})

        # This mirrors a selected-review composition: the middle sidecar is
        # bound to B while preserving the A-to-B differential item receipt.
        composed_middle = sidecar(middle, {key: {}})
        inherited = copy.deepcopy(dict(middle_items[key]))
        inherited["source_record_audit_sha256"] = middle[
            "source_record_audit_sha256"
        ]
        composed_middle["items"] = {key: inherited}
        middle_raw_path = paper_dir / "audit" / "source_record_audit.middle.json"
        middle_sidecar_path = paper_dir / "audit" / "source_record_match_llm.middle.json"
        middle_raw_path.write_text(json.dumps(middle, sort_keys=True), encoding="utf-8")
        middle_sidecar_path.write_text(
            json.dumps(composed_middle, sort_keys=True), encoding="utf-8"
        )

        current = raw_audit(boundary=[reusable_input(key)])
        canonical_path.write_text(json.dumps(current, sort_keys=True), encoding="utf-8")
        chained = DIFFERENTIAL.build_source_record_differential_revalidation(
            paper=PAPER,
            prior_raw_audit=middle,
            prior_judgments=composed_middle,
            current_raw_audit=current,
            prior_raw_audit_path=middle_raw_path,
            prior_judgments_path=middle_sidecar_path,
            current_raw_audit_path=canonical_path,
        )
        self.assertEqual(set(chained["items"]), {key})
        item = chained["items"][key]
        assert isinstance(item, dict)
        self.assertEqual(
            len(item[DIFFERENTIAL.SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_HISTORY_FIELD]),
            1,
        )
        DIFFERENTIAL.source_record_differential_revalidation_overlay_path(
            paper_dir
        ).write_text(json.dumps(chained, sort_keys=True), encoding="utf-8")
        self.assertEqual(
            set(
                DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                    paper_dir, PAPER, current
                )
            ),
            {key},
        )

    def test_loader_rejects_changed_archived_evidence(self) -> None:
        key = "input.h : P"
        prior = raw_audit(boundary=[reusable_input(key)])
        judgments = sidecar(prior, {key: {}})
        current = raw_audit(boundary=[reusable_input(key)])
        overlay, paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        archived_prior = DIFFERENTIAL._repository_provenance_path(
            overlay["prior_raw_audit"]["path"]
        )
        archived_prior.write_text("{}", encoding="utf-8")
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir, PAPER, current
            ),
            {},
        )

    def test_loader_accepts_stale_root_only_for_exact_individual_prior_receipts(
        self,
    ) -> None:
        current_key = "individually_current.h : P"
        stale_key = "root_only.h : Q"
        prior = raw_audit(
            boundary=[
                reusable_input(current_key, input_type="P x"),
                reusable_input(stale_key, input_type="Q x"),
            ]
        )
        judgments = sidecar(prior, {current_key: {}, stale_key: {}})
        # This models a historical sidecar whose aggregate root was not
        # advanced, while one item was explicitly rebound to the B receipt.
        judgments["source_record_audit_sha256"] = digest("f")
        judgments["items"][stale_key].pop("source_record_audit_sha256")
        current = raw_audit(
            boundary=[
                reusable_input(current_key, input_type="P x"),
                reusable_input(stale_key, input_type="Q x"),
            ]
        )

        overlay, paper_dir, _ordinary_path = self.build_overlay(
            prior, judgments, current
        )
        self.assertEqual(set(overlay["items"]), {current_key})
        self.assertEqual(
            set(
                DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                    paper_dir, PAPER, current
                )
            ),
            {current_key},
        )

    def test_loader_rejects_stale_root_item_without_individual_receipt_or_exact_response(
        self,
    ) -> None:
        key = "individually_current.h : P"
        prior = raw_audit(boundary=[reusable_input(key)])
        judgments = sidecar(prior, {key: {}})
        judgments["source_record_audit_sha256"] = digest("f")
        current = raw_audit(boundary=[reusable_input(key)])
        overlay, paper_dir, _ordinary_path = self.build_overlay(
            prior, judgments, current
        )
        self.assertEqual(
            set(
                DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                    paper_dir, PAPER, current
                )
            ),
            {key},
        )

        archived = DIFFERENTIAL._repository_provenance_path(
            overlay["prior_judgments"]["path"]
        )
        archived_payload = json.loads(archived.read_text(encoding="utf-8"))
        archived_payload["items"][key].pop("source_record_audit_sha256")
        archived.write_text(json.dumps(archived_payload, sort_keys=True), encoding="utf-8")
        overlay["prior_judgments"]["file_sha256"] = DIFFERENTIAL._file_sha256(archived)
        DIFFERENTIAL.stamp_source_record_differential_revalidation(overlay)
        DIFFERENTIAL.source_record_differential_revalidation_overlay_path(paper_dir).write_text(
            json.dumps(overlay, sort_keys=True), encoding="utf-8"
        )
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir, PAPER, current
            ),
            {},
        )

        # Restoring the per-item receipt but changing the inherited semantic
        # response still cannot pass: the serialized overlay must match the
        # exact archived response after root metadata materialization.
        archived_payload["items"][key]["source_record_audit_sha256"] = prior[
            "source_record_audit_sha256"
        ]
        archived_payload["items"][key]["reason"] = "tampered archived response"
        archived.write_text(json.dumps(archived_payload, sort_keys=True), encoding="utf-8")
        overlay["prior_judgments"]["file_sha256"] = DIFFERENTIAL._file_sha256(archived)
        DIFFERENTIAL.stamp_source_record_differential_revalidation(overlay)
        DIFFERENTIAL.source_record_differential_revalidation_overlay_path(paper_dir).write_text(
            json.dumps(overlay, sort_keys=True), encoding="utf-8"
        )
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir, PAPER, current
            ),
            {},
        )

    def test_ambiguous_descriptor_and_changed_local_relation_require_review(self) -> None:
        first = "first.h : P"
        second = "second.h : P"
        prior = raw_audit(boundary=[reusable_input(first), reusable_input(second)])
        judgments = sidecar(prior, {first: {}, second: {}})
        current = raw_audit(boundary=[reusable_input(first), reusable_input(second)])
        overlay, _paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertEqual(overlay["items"], {})
        self.assertEqual(len(overlay["manual_review_required"]), 2)

        input_key = "input.h : P"
        prior_boundary = reusable_input(input_key)
        prior_conclusion = reusable_input(
            input_key, kind="direct_conclusion_input", result_relation="component_of_target"
        )
        prior = raw_audit(boundary=[prior_boundary], conclusion=[prior_conclusion])
        judgments = sidecar(prior, {input_key: {}})
        current_boundary = copy.deepcopy(prior_boundary)
        current_conclusion = copy.deepcopy(prior_conclusion)
        current_conclusion["result_relation"] = "equals_target"
        current = raw_audit(
            boundary=[current_boundary], conclusion=[current_conclusion]
        )
        overlay, _paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertEqual(overlay["items"], {})
        self.assertEqual(
            [entry["current_judgment_key"] for entry in overlay["manual_review_required"]],
            [input_key],
        )

    def test_serialized_marker_cannot_bypass_loader(self) -> None:
        key = "input.h : P"
        prior = raw_audit(boundary=[reusable_input(key)])
        judgments = sidecar(prior, {key: {}})
        current = raw_audit(boundary=[reusable_input(key)])
        overlay, paper_dir, ordinary_path = self.build_overlay(prior, judgments, current)
        item = overlay["items"][key]
        assert isinstance(item, dict)
        forged = json.loads(json.dumps(item))
        forged["_source_record_differential_revalidation_loaded"] = True
        self.assertFalse(
            DIFFERENTIAL.is_loaded_source_record_differential_revalidation_item(forged)
        )
        ordinary_path.write_text(
            json.dumps({"schema": 1, "paper": PAPER, "items": {key: forged}}),
            encoding="utf-8",
        )
        # Remove the authenticated overlay so this tests the forged ordinary
        # JSON object rather than the real loader path.
        DIFFERENTIAL.source_record_differential_revalidation_overlay_path(paper_dir).unlink()
        self.assertEqual(
            REPOSITORY.source_record_judgment_items(
                ordinary_path, PAPER, current_raw_audit=current, paper_dir=paper_dir
            ),
            {},
        )

    def test_complete_receipt_reissue_reuses_only_a_complete_identity(self) -> None:
        key = "input.h : P"
        prior = raw_audit(boundary=[reusable_input(key)])
        judgments = sidecar(prior, {key: {}})
        current = raw_audit(boundary=[reusable_input(key)])
        overlay, paper_dir, _ordinary_path = self.build_overlay(
            prior,
            judgments,
            current,
            require_complete_reusable_section_identity=True,
        )
        identity = overlay[DIFFERENTIAL.SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_FIELD]
        self.assertEqual(
            identity["mode"], DIFFERENTIAL.SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_MODE
        )
        self.assertEqual(overlay["manual_review_required"], [])
        self.assertEqual(
            set(
                DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                    paper_dir, PAPER, current
                )
            ),
            {key},
        )

    def test_complete_receipt_reissue_rejects_navigation_only_raw_mutation(self) -> None:
        key = "input.h : P"
        prior = raw_audit(boundary=[reusable_input(key)])
        judgments = sidecar(prior, {key: {}})
        changed = reusable_input(key)
        changed["row"] = "renamed_navigation_row"
        current = raw_audit(boundary=[changed])

        # Ordinary group reuse intentionally ignores this presentation route.
        ordinary, _paper_dir, _ordinary_path = self.build_overlay(prior, judgments, current)
        self.assertEqual(set(ordinary["items"]), {key})
        with self.assertRaisesRegex(
            DIFFERENTIAL.SourceRecordDifferentialRevalidationError,
            "raw reusable sections or descriptor multiset changed",
        ):
            self.build_overlay(
                prior,
                judgments,
                current,
                require_complete_reusable_section_identity=True,
            )

    def test_complete_receipt_reissue_allows_only_reprojected_selected_receipt_delta(
        self,
    ) -> None:
        key = "input.h : P"
        prior = raw_audit_with_reprojected_selected_semantic_projection(
            selected_projection_sha256=digest("a"), boundary=[reusable_input(key)]
        )
        judgments = sidecar(prior, {key: {}})
        current = raw_audit_with_reprojected_selected_semantic_projection(
            selected_projection_sha256=digest("b"), boundary=[reusable_input(key)]
        )
        overlay, paper_dir, _ordinary_path = self.build_overlay(
            prior,
            judgments,
            current,
            require_complete_reusable_section_identity=True,
        )
        aggregate = overlay[
            DIFFERENTIAL.SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_FIELD
        ]["allowed_aggregate_metadata_delta"]
        self.assertEqual(
            aggregate["prior"]["selected_semantic_projection_sha256"], digest("a")
        )
        self.assertEqual(
            aggregate["current"]["selected_semantic_projection_sha256"], digest("b")
        )
        self.assertEqual(
            set(
                DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                    paper_dir, PAPER, current
                )
            ),
            {key},
        )

    def test_complete_receipt_reissue_rejects_unlisted_aggregate_provenance_delta(
        self,
    ) -> None:
        key = "input.h : P"
        prior = raw_audit(boundary=[reusable_input(key)])
        judgments = sidecar(prior, {key: {}})
        current = raw_audit(boundary=[reusable_input(key)])
        current["unexpected_provenance_delta"] = {"changed": True}
        stamp_source_record_audit_receipts(current)
        with self.assertRaisesRegex(
            DIFFERENTIAL.SourceRecordDifferentialRevalidationError,
            "aggregate metadata outside allowed receipt paths",
        ):
            self.build_overlay(
                prior,
                judgments,
                current,
                require_complete_reusable_section_identity=True,
            )

    def test_complete_receipt_reissue_loader_rechecks_identity_receipt(self) -> None:
        key = "input.h : P"
        prior = raw_audit(boundary=[reusable_input(key)])
        judgments = sidecar(prior, {key: {}})
        current = raw_audit(boundary=[reusable_input(key)])
        overlay, paper_dir, _ordinary_path = self.build_overlay(
            prior,
            judgments,
            current,
            require_complete_reusable_section_identity=True,
        )
        identity = overlay[DIFFERENTIAL.SOURCE_RECORD_COMPLETE_REISSUE_IDENTITY_FIELD]
        identity["current"]["reusable_sections"]["boundary_input_items"][
            "canonical_sha256"
        ] = digest("f")
        DIFFERENTIAL.stamp_source_record_differential_revalidation(overlay)
        DIFFERENTIAL.source_record_differential_revalidation_overlay_path(
            paper_dir
        ).write_text(json.dumps(overlay, sort_keys=True), encoding="utf-8")
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir, PAPER, current
            ),
            {},
        )

    def test_complete_receipt_reissue_keeps_duplicate_descriptor_responses_at_exact_addresses(
        self,
    ) -> None:
        first = "first.h : P"
        second = "second.h : P"
        prior = raw_audit(
            boundary=[reusable_input(first), reusable_input(second)]
        )
        judgments = sidecar(
            prior,
            {
                first: {"reason": "first independently reviewed response"},
                second: {"reason": "second independently reviewed response"},
            },
        )
        current = raw_audit(
            boundary=[reusable_input(first), reusable_input(second)]
        )
        overlay, paper_dir, _ordinary_path = self.build_overlay(
            prior,
            judgments,
            current,
            require_complete_reusable_section_identity=True,
        )
        self.assertEqual(set(overlay["items"]), {first, second})
        self.assertTrue(
            all(
                entry["reason"] == "exact complete raw-group identity"
                for entry in overlay["decisions"]
                if entry["status"] == "reused"
            )
        )

        # A duplicate descriptor does not authorize an address swap. Even an
        # attacker who restamps the overlay must fail its archived raw-group
        # address check before a response is made current.
        first_metadata = overlay["items"][first][
            DIFFERENTIAL.SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD
        ]
        second_metadata = overlay["items"][second][
            DIFFERENTIAL.SOURCE_RECORD_DIFFERENTIAL_REVALIDATION_ITEM_FIELD
        ]
        first_metadata["current_judgment_key"] = second
        second_metadata["current_judgment_key"] = first
        DIFFERENTIAL.stamp_source_record_differential_revalidation(overlay)
        DIFFERENTIAL.source_record_differential_revalidation_overlay_path(
            paper_dir
        ).write_text(json.dumps(overlay, sort_keys=True), encoding="utf-8")
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir, PAPER, current
            ),
            {},
        )

    def test_complete_receipt_reissue_rechecks_each_archived_response_provenance(
        self,
    ) -> None:
        key = "input.h : P"
        prior = raw_audit(boundary=[reusable_input(key)])
        judgments = sidecar(prior, {key: {}})
        current = raw_audit(boundary=[reusable_input(key)])
        overlay, paper_dir, _ordinary_path = self.build_overlay(
            prior,
            judgments,
            current,
            require_complete_reusable_section_identity=True,
        )
        archived = DIFFERENTIAL._repository_provenance_path(
            overlay["prior_judgments"]["path"]
        )
        archived_payload = json.loads(archived.read_text(encoding="utf-8"))
        archived_payload["items"][key]["source_record_audit_sha256"] = digest("f")
        archived.write_text(json.dumps(archived_payload, sort_keys=True), encoding="utf-8")
        overlay["prior_judgments"]["file_sha256"] = DIFFERENTIAL._file_sha256(
            archived
        )
        DIFFERENTIAL.stamp_source_record_differential_revalidation(overlay)
        DIFFERENTIAL.source_record_differential_revalidation_overlay_path(
            paper_dir
        ).write_text(json.dumps(overlay, sort_keys=True), encoding="utf-8")
        self.assertEqual(
            DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                paper_dir, PAPER, current
            ),
            {},
        )

    def test_complete_receipt_reissue_rejects_inconsistent_replicated_delta(self) -> None:
        key = "input.h : P"
        prior = raw_audit_with_reprojected_selected_semantic_projection(
            selected_projection_sha256=digest("a"), boundary=[reusable_input(key)]
        )
        judgments = sidecar(prior, {key: {}})
        current = raw_audit_with_reprojected_selected_semantic_projection(
            selected_projection_sha256=digest("b"), boundary=[reusable_input(key)]
        )
        current["source_record_receipt_reprojection"][
            "paper_statement_map_exact_default_mode_delta"
        ]["selected_semantic_projection_sha256"] = digest("c")
        # The semantic surface is internally valid but its direct receipt
        # mirror intentionally disagrees with the raw-evidence projection.
        mismatched_surface = {
            "source_record_receipt_reprojection": {
                "paper_statement_map_exact_default_mode_delta": {
                    "selected_semantic_projection_sha256": digest("b"),
                }
            }
        }
        stamp_source_record_audit_receipts(current, surface=mismatched_surface)
        with self.assertRaisesRegex(
            DIFFERENTIAL.SourceRecordDifferentialRevalidationError,
            "replicated selected semantic-projection receipts disagree",
        ):
            self.build_overlay(
                prior,
                judgments,
                current,
                require_complete_reusable_section_identity=True,
            )

    def test_complete_receipt_reissue_rechecks_attestation_after_issuance(self) -> None:
        class FakeCurrentRevalidation:
            CURRENT_REVALIDATION_FIELD = "current_semantic_revalidation"
            calls: list[bool] = []

            class SourceRecordCurrentRevalidationError(ValueError):
                pass

            @staticmethod
            def validate_rebound_sidecar(
                _raw: object,
                candidate: dict[str, object],
                *,
                paper: str,
                paper_dir: Path,
                output_sidecar_path: Path,
                include_runtime_semantic_checks: bool = True,
            ) -> list[str]:
                FakeCurrentRevalidation.calls.append(include_runtime_semantic_checks)
                if paper != PAPER or not output_sidecar_path.is_file():
                    return ["candidate path is not authenticated"]
                metadata = candidate["current_semantic_revalidation"]
                assert isinstance(metadata, dict)
                attestation = json.loads(
                    (paper_dir / str(metadata["attestation_path"])).read_text(
                        encoding="utf-8"
                    )
                )
                return [] if attestation.get("approved") is True else ["attestation revoked"]

        key = "input.h : P"
        prior = raw_audit(boundary=[reusable_input(key)])
        current = raw_audit(boundary=[reusable_input(key)])
        candidate = sidecar(prior, {key: {"reason": "attested candidate response"}})
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        root = Path(temporary.name)
        root_override = patch.object(DIFFERENTIAL, "ROOT", root)
        root_override.start()
        self.addCleanup(root_override.stop)
        paper_dir = root / "papers" / PAPER
        audit_dir = paper_dir / "audit"
        audit_dir.mkdir(parents=True)
        prior_path = audit_dir / "source_record_audit.candidate.json"
        sidecar_path = audit_dir / "source_record_match_llm.candidate.json"
        current_path = audit_dir / "source_record_audit.json"
        attestation_path = audit_dir / "candidate_attestation.json"
        attestation_path.write_text(
            json.dumps({"approved": True}, sort_keys=True), encoding="utf-8"
        )
        candidate["current_semantic_revalidation"] = {
            "attestation_path": "audit/candidate_attestation.json",
            "attestation_sha256": DIFFERENTIAL._file_sha256(attestation_path),
            "current_judgment_sidecar_path": "audit/source_record_match_llm.candidate.json",
        }
        prior_path.write_text(json.dumps(prior, sort_keys=True), encoding="utf-8")
        sidecar_path.write_text(json.dumps(candidate, sort_keys=True), encoding="utf-8")
        current_path.write_text(json.dumps(current, sort_keys=True), encoding="utf-8")
        with patch.object(
            DIFFERENTIAL,
            "_current_revalidation_module",
            return_value=FakeCurrentRevalidation,
        ):
            overlay = DIFFERENTIAL.build_source_record_differential_revalidation(
                paper=PAPER,
                prior_raw_audit=prior,
                prior_judgments=candidate,
                current_raw_audit=current,
                prior_raw_audit_path=prior_path,
                prior_judgments_path=sidecar_path,
                current_raw_audit_path=current_path,
                require_complete_reusable_section_identity=True,
                prior_current_revalidation_attestation_path=attestation_path,
            )
            overlay_path = DIFFERENTIAL.source_record_differential_revalidation_overlay_path(
                paper_dir
            )
            overlay_path.write_text(json.dumps(overlay, sort_keys=True), encoding="utf-8")
            self.assertEqual(
                set(
                    DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                        paper_dir, PAPER, current
                    )
                ),
                {key},
            )
            self.assertEqual(FakeCurrentRevalidation.calls, [True, False])

            # Update every simple file-hash pin an attacker could rewrite, then
            # revoke the attestation. The loader must still rerun the semantic
            # attestation validator rather than trust those rewritten digests.
            attestation_path.write_text(
                json.dumps({"approved": False}, sort_keys=True), encoding="utf-8"
            )
            candidate["current_semantic_revalidation"][
                "attestation_sha256"
            ] = DIFFERENTIAL._file_sha256(attestation_path)
            sidecar_path.write_text(
                json.dumps(candidate, sort_keys=True), encoding="utf-8"
            )
            provenance = overlay[
                DIFFERENTIAL.SOURCE_RECORD_COMPLETE_REISSUE_CURRENT_REVALIDATION_FIELD
            ]
            provenance["candidate_sidecar"]["file_sha256"] = DIFFERENTIAL._file_sha256(
                sidecar_path
            )
            provenance["attestation"]["file_sha256"] = DIFFERENTIAL._file_sha256(
                attestation_path
            )
            overlay["prior_judgments"]["file_sha256"] = DIFFERENTIAL._file_sha256(
                sidecar_path
            )
            DIFFERENTIAL.stamp_source_record_differential_revalidation(overlay)
            overlay_path.write_text(json.dumps(overlay, sort_keys=True), encoding="utf-8")
            self.assertEqual(
                DIFFERENTIAL.load_current_source_record_differential_revalidation_items(
                    paper_dir, PAPER, current
                ),
                {},
            )


if __name__ == "__main__":
    unittest.main()
