#!/usr/bin/env python3
"""Fail-closed tests for explicit recursive-field source ancestry routes."""

from __future__ import annotations

import copy
import importlib.util
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    import_root_text = str(import_root)
    if import_root_text not in sys.path:
        sys.path.insert(0, import_root_text)

from source_coverage_scope import source_item_coverage_sha256  # noqa: E402

SOURCE_AUDIT_PATH = (
    ROOT / "skills" / "econcs-formalizer" / "scripts" / "source_record_audit.py"
)
DISPOSITION_PATH = ROOT / "scripts" / "source_record_target_disposition.py"

SOURCE_AUDIT_SPEC = importlib.util.spec_from_file_location(
    "source_record_audit_recursive_field_ancestry_fixture", SOURCE_AUDIT_PATH
)
assert SOURCE_AUDIT_SPEC is not None and SOURCE_AUDIT_SPEC.loader is not None
AUDIT = importlib.util.module_from_spec(SOURCE_AUDIT_SPEC)
sys.modules[SOURCE_AUDIT_SPEC.name] = AUDIT
SOURCE_AUDIT_SPEC.loader.exec_module(AUDIT)

DISPOSITION_SPEC = importlib.util.spec_from_file_location(
    "source_record_target_disposition_recursive_field_ancestry_fixture",
    DISPOSITION_PATH,
)
assert DISPOSITION_SPEC is not None and DISPOSITION_SPEC.loader is not None
DISPOSITION = importlib.util.module_from_spec(DISPOSITION_SPEC)
sys.modules[DISPOSITION_SPEC.name] = DISPOSITION
DISPOSITION_SPEC.loader.exec_module(DISPOSITION)


ROOT_RECORD = "Fixture.Model.RootRecord"
NESTED_RECORD = "Fixture.Model.EndpointRecord"
OTHER_ROOT_RECORD = "Fixture.Other.RootRecord"
OTHER_NESTED_RECORD = "Fixture.Other.EndpointRecord"
PARENT_DECLARATION = "Fixture.PaperInterface.reviewedTheorem"
SOURCE_ITEM_KEY = "source_reviewed_theorem"
CONVENTION_ID = "fixture_endpoint_convention"
OTHER_CONVENTION_ID = "fixture_other_convention"
PARENT_DECLARATION_DIGEST = "a" * 64
PARENT_SIGNATURE_DIGEST = "b" * 64


def source_item(*, convention_ids: list[str] | None = None) -> dict[str, object]:
    return {
        "source_location": "source.tex:10",
        "claim_bearing": True,
        "model_convention_ids": convention_ids or [CONVENTION_ID],
    }


def statement_map(*, convention_ids: list[str] | None = None) -> dict[str, object]:
    return {"items": {SOURCE_ITEM_KEY: source_item(convention_ids=convention_ids)}}


def source_identity(statement: dict[str, object]) -> dict[str, str]:
    item = statement["items"][SOURCE_ITEM_KEY]
    assert isinstance(item, dict)
    return {
        "source_key": SOURCE_ITEM_KEY,
        "source_location": str(item["source_location"]),
        "source_map_item_sha256": AUDIT.stable_digest(item),
        "source_semantic_sha256": source_item_coverage_sha256(item, ""),
    }


def parent_signature(*, digest: str = PARENT_SIGNATURE_DIGEST) -> dict[str, str]:
    return {
        "qualified_declaration": PARENT_DECLARATION,
        "elaborated_signature_sha256": digest,
    }


def parent_item(
    statement: dict[str, object],
    *,
    signature_digest: str = PARENT_SIGNATURE_DIGEST,
    declaration_digest: str = PARENT_DECLARATION_DIGEST,
) -> dict[str, object]:
    identity = source_identity(statement)
    reviewed_identity = {
        "qualified_declaration": PARENT_DECLARATION,
        "declaration_sha256": declaration_digest,
    }
    signature = parent_signature(digest=signature_digest)
    association = {
        "schema": 2,
        "association_origin": AUDIT.EXPLICIT_DIRECT_SOURCE_ROUTE_ORIGIN,
        "role": AUDIT.EXPLICIT_DIRECT_SOURCE_ROUTE_ROLE,
        "reviewed_declaration_identity": reviewed_identity,
        "reviewed_elaborated_signature_identity": signature,
        "source_item_identities": [identity],
        "semantic_association_sha256": AUDIT.semantic_source_association_digest(
            [identity], signature
        ),
    }
    return {
        "judgment_key": "semantic-model::reviewedTheorem",
        "qualified_declaration": PARENT_DECLARATION,
        "reviewed_declaration_identity": reviewed_identity,
        "record_input_bindings": [
            {
                "record_roots": [ROOT_RECORD],
                "fully_qualified_expanded_type_canonical": ROOT_RECORD,
            }
        ],
        "source_statement_association": association,
    }


def semantic_contract_parent_item(
    statement: dict[str, object],
    *,
    role: str = "direct_evidence",
    origin: str = "",
) -> dict[str, object]:
    """Build one generator-shaped direct/Spec parent association fixture."""

    parent = parent_item(statement)
    association = parent.pop("source_statement_association")
    assert isinstance(association, dict)
    association.pop("association_origin", None)
    association["role"] = role
    if origin:
        association["association_origin"] = origin
    parent["semantic_contract_source_association"] = association
    return parent


def source_claim_atom_parent_item(statement: dict[str, object]) -> dict[str, object]:
    """Build one generator-shaped direct atom-route parent association."""

    parent = parent_item(statement)
    direct_association = parent.pop("source_statement_association")
    assert isinstance(direct_association, dict)
    identity = source_identity(statement)
    signature = parent_signature()
    atom_context = {
        "schema": 1,
        "id": "fixture-result-clause",
        "source_locator": "source.tex:10",
        "semantic_claim": "The source result has the fixture conclusion.",
        "source_quote": "Fixture result.",
        "source_quote_sha256": AUDIT.hashlib.sha256(
            b"Fixture result."
        ).hexdigest(),
    }
    atom_context["source_claim_atom_semantic_sha256"] = (
        AUDIT.source_claim_atom_semantic_digest(atom_context)
    )
    association = {
        "schema": 1,
        "association_origin": AUDIT.SOURCE_CLAIM_ATOM_ROUTE_ORIGIN,
        "role": AUDIT.SOURCE_CLAIM_ATOM_ROUTE_ROLE,
        "reviewed_declaration_identity": direct_association[
            "reviewed_declaration_identity"
        ],
        "reviewed_elaborated_signature_identity": signature,
        "source_item_identities": [identity],
        "source_claim_atom_routes": [
            {
                "source_key": SOURCE_ITEM_KEY,
                "atom_id": atom_context["id"],
                "reviewed_lean_route": PARENT_DECLARATION,
                "source_claim_atom_semantic_sha256": atom_context[
                    "source_claim_atom_semantic_sha256"
                ],
            }
        ],
        "source_claim_atom_semantic_association_sha256": (
            AUDIT.source_claim_atom_semantic_association_digest(
                [atom_context], signature
            )
        ),
        "review_scope": "individual_row_only",
        "structural_pairing": "not_asserted_by_source_claim_atom_route",
    }
    association["association_sha256"] = AUDIT.stable_digest(association)
    parent["source_claim_atom_association"] = association
    parent["source_claim_atom_contexts"] = [atom_context]
    return parent


def outer_field() -> dict[str, object]:
    return {
        "structure": ROOT_RECORD,
        "field": "endpoint",
        "path": f"{ROOT_RECORD} -> {ROOT_RECORD}.endpoint",
        "nested_structures": [NESTED_RECORD],
        "judgment_key": f"{ROOT_RECORD}.endpoint",
    }


def leaf_field() -> dict[str, object]:
    return {
        "structure": NESTED_RECORD,
        "field": "upper_derivative",
        "path": (
            f"{ROOT_RECORD} -> {ROOT_RECORD}.endpoint -> "
            f"{NESTED_RECORD}.upper_derivative"
        ),
        "nested_structures": [],
        "judgment_key": f"{NESTED_RECORD}.upper_derivative",
    }


def other_path_fields() -> list[dict[str, object]]:
    return [
        {
            "structure": OTHER_ROOT_RECORD,
            "field": "endpoint",
            "path": f"{OTHER_ROOT_RECORD} -> {OTHER_ROOT_RECORD}.endpoint",
            "nested_structures": [OTHER_NESTED_RECORD],
            "judgment_key": f"{OTHER_ROOT_RECORD}.endpoint",
        },
        {
            "structure": OTHER_NESTED_RECORD,
            "field": "upper_derivative",
            "path": (
                f"{OTHER_ROOT_RECORD} -> {OTHER_ROOT_RECORD}.endpoint -> "
                f"{OTHER_NESTED_RECORD}.upper_derivative"
            ),
            "nested_structures": [],
            "judgment_key": f"{OTHER_NESTED_RECORD}.upper_derivative",
        },
    ]


def scope_entry(
    *,
    root_record: str = ROOT_RECORD,
    field_chain: list[dict[str, str]] | None = None,
    permitted_classifications: list[str] | None = None,
    source_locator: str = "source.tex:20",
) -> dict[str, object]:
    return {
        "source_item": SOURCE_ITEM_KEY,
        "root_record": root_record,
        "field_chain": field_chain
        or [
            {"structure": ROOT_RECORD, "field": "endpoint"},
            {"structure": NESTED_RECORD, "field": "upper_derivative"},
        ],
        "source_locator": source_locator,
        "permitted_classifications": permitted_classifications
        or ["approved_source_convention"],
    }


def convention(
    entries: list[dict[str, object]],
    *,
    convention_id: str = CONVENTION_ID,
) -> dict[str, object]:
    return {
        "id": convention_id,
        "source_locator": "source.tex:20",
        "classification": "source_model_convention",
        "formal_meaning": "Fixture endpoint condition is supplied by the source model.",
        "why_needed": "The reviewed theorem consumes the endpoint condition.",
        "checked_scope": "The exact generated recursive field path only.",
        "recursive_field_source_scope": {"schema": 1, "entries": entries},
    }


def ledger(entries: list[dict[str, object]], *, include_other: bool = False) -> dict[str, object]:
    conventions: list[dict[str, object]] = [convention(entries)]
    if include_other:
        conventions.append(
            {
                "id": OTHER_CONVENTION_ID,
                "source_locator": "source.tex:40",
                "classification": "source_model_convention",
                "formal_meaning": "A distinct source-model convention.",
                "why_needed": "Fixture negative test only.",
                "checked_scope": "A distinct scope.",
            }
        )
    return {"model_conventions": conventions}


def attach(
    *,
    fields: list[dict[str, object]],
    statement: dict[str, object],
    source_ledger: dict[str, object],
    parents: list[dict[str, object]] | None = None,
) -> tuple[list[str], dict[str, int]]:
    return AUDIT.attach_recursive_field_explicit_parent_route_associations(
        field_items=fields,
        semantic_model_items=parents or [parent_item(statement)],
        paper_statement_map=statement,
        source_proof_fidelity=source_ledger,
        elaborated_signature_sha256_by_qualified={
            PARENT_DECLARATION: PARENT_SIGNATURE_DIGEST
        },
    )


def attach_item_digests(
    fields: list[dict[str, object]],
    *,
    statement: dict[str, object],
    source_ledger: dict[str, object],
) -> None:
    AUDIT.attach_source_record_item_digests(
        fields,
        source_map_semantic_index=AUDIT.source_record_source_map_semantic_index(
            statement
        ),
        source_proof_fidelity=source_ledger,
        row_qualified_names={"fixture": PARENT_DECLARATION},
        elaborated_signature_sha256_by_qualified={
            PARENT_DECLARATION: PARENT_SIGNATURE_DIGEST
        },
    )


class RecursiveFieldAncestryAssociationTests(unittest.TestCase):
    def test_exact_root_path_and_convention_attach_reusable_route(self) -> None:
        statement = statement_map()
        source_ledger = ledger([scope_entry()])
        fields = [outer_field(), leaf_field()]

        errors, counts = attach(
            fields=fields, statement=statement, source_ledger=source_ledger
        )

        self.assertEqual(errors, [])
        self.assertEqual(counts["recursive_field_scope_association_count"], 1)
        receipt = fields[1]["recursive_field_explicit_parent_route"]
        self.assertEqual(receipt["root_record"], ROOT_RECORD)
        self.assertEqual(receipt["convention_id"], CONVENTION_ID)
        self.assertEqual(receipt["field_chain"], scope_entry()["field_chain"])
        attach_item_digests(fields, statement=statement, source_ledger=source_ledger)
        self.assertTrue(fields[1]["source_record_item_reuse_eligibility"]["eligible"])
        self.assertTrue(fields[1].get("source_record_item_sha256"))
        response = {
            "classification": "approved_source_convention",
            "source_target_disposition": "approved_source_convention",
            "source_location": "source.tex:20",
            "model_convention_ids": [CONVENTION_ID],
            "model_convention_sha256_by_id": {
                CONVENTION_ID: DISPOSITION.model_convention_semantic_digest(
                    source_ledger["model_conventions"][0]
                )
            },
        }
        self.assertEqual(
            DISPOSITION.recursive_field_target_disposition_errors(
                fields[1],
                response,
                statement_map=statement,
                source_proof_fidelity=source_ledger,
            ),
            [],
        )
        semantic_contract_fields = [outer_field(), leaf_field()]
        semantic_contract_errors, _counts = attach(
            fields=semantic_contract_fields,
            statement=statement,
            source_ledger=source_ledger,
            parents=[semantic_contract_parent_item(statement)],
        )
        self.assertEqual(semantic_contract_errors, [])
        self.assertEqual(
            semantic_contract_fields[1]["recursive_field_explicit_parent_route"][
                "parent_association_field"
            ],
            "semantic_contract_source_association",
        )
        atom_route_fields = [outer_field(), leaf_field()]
        atom_route_errors, _counts = attach(
            fields=atom_route_fields,
            statement=statement,
            source_ledger=source_ledger,
            parents=[source_claim_atom_parent_item(statement)],
        )
        self.assertEqual(atom_route_errors, [])
        self.assertEqual(
            atom_route_fields[1]["recursive_field_explicit_parent_route"][
                "parent_association_field"
            ],
            "source_claim_atom_association",
        )
        self.assertEqual(
            DISPOSITION.recursive_field_target_disposition_errors(
                atom_route_fields[1],
                response,
                statement_map=statement,
                source_proof_fidelity=source_ledger,
            ),
            [],
        )

    def test_parent_route_accepts_canonical_applied_record_head(self) -> None:
        """Canonical type rendering may omit spaces before record arguments."""

        statement = statement_map()
        source_ledger = ledger([scope_entry()])
        fields = [outer_field(), leaf_field()]
        errors, _counts = attach(
            fields=fields, statement=statement, source_ledger=source_ledger
        )
        self.assertEqual(errors, [])
        route = fields[1]["recursive_field_explicit_parent_route"]
        assert isinstance(route, dict)
        route["root_input_type_canonical"] = ROOT_RECORD + "(Fin 4)"
        route["association_sha256"] = DISPOSITION.recursive_field_parent_route_record_digest(
            route
        )
        response = {
            "classification": "approved_source_convention",
            "source_target_disposition": "approved_source_convention",
            "source_location": "source.tex:20",
            "model_convention_ids": [CONVENTION_ID],
            "model_convention_sha256_by_id": {
                CONVENTION_ID: DISPOSITION.model_convention_semantic_digest(
                    source_ledger["model_conventions"][0]
                )
            },
        }
        self.assertEqual(
            DISPOSITION.recursive_field_target_disposition_errors(
                fields[1],
                response,
                statement_map=statement,
                source_proof_fidelity=source_ledger,
            ),
            [],
        )

    def test_no_scope_leaves_recursive_fields_aggregate_only(self) -> None:
        statement = statement_map()
        source_ledger = ledger([])
        source_ledger["model_conventions"][0].pop(
            "recursive_field_source_scope"
        )
        fields = [outer_field(), leaf_field()]

        errors, counts = attach(
            fields=fields, statement=statement, source_ledger=source_ledger
        )

        self.assertEqual(errors, [])
        self.assertEqual(counts["recursive_field_scope_association_count"], 0)
        self.assertNotIn("recursive_field_explicit_parent_route", fields[1])
        attach_item_digests(fields, statement=statement, source_ledger=source_ledger)
        self.assertFalse(fields[1]["source_record_item_reuse_eligibility"]["eligible"])
        self.assertNotIn("source_record_item_sha256", fields[1])

    def test_unscoped_legacy_field_without_coordinate_stays_aggregate_only(self) -> None:
        """An explicit scope must not reject unrelated legacy field metadata.

        The source-record producer is allowed to retain aggregate-only
        recursive fields when it cannot recover a fully qualified coordinate.
        Such a field is not a candidate for the exact scoped path below, so it
        must neither receive a route nor make that unrelated scope fail.
        """

        statement = statement_map()
        legacy_field = {
            "path": "LegacyAggregate -> opaque projection",
            "judgment_key": "LegacyAggregate.opaque",
        }
        fields = [legacy_field, outer_field(), leaf_field()]

        errors, counts = attach(
            fields=fields,
            statement=statement,
            source_ledger=ledger([scope_entry()]),
        )

        self.assertEqual(errors, [])
        self.assertEqual(counts["recursive_field_scope_association_count"], 1)
        self.assertNotIn("recursive_field_explicit_parent_route", legacy_field)
        self.assertIn("recursive_field_explicit_parent_route", fields[2])

    def test_wrong_root_or_field_chain_fails_closed(self) -> None:
        statement = statement_map()
        for label, entry in (
            (
                "root",
                scope_entry(root_record="Fixture.Model.OtherRoot"),
            ),
            (
                "chain",
                scope_entry(
                    field_chain=[
                        {"structure": ROOT_RECORD, "field": "endpoint"},
                        {"structure": NESTED_RECORD, "field": "lower_derivative"},
                    ]
                ),
            ),
        ):
            with self.subTest(label=label):
                fields = [outer_field(), leaf_field()]
                errors, _counts = attach(
                    fields=fields,
                    statement=statement,
                    source_ledger=ledger([entry]),
                )
                self.assertTrue(errors)
                self.assertNotIn("recursive_field_explicit_parent_route", fields[1])

    def test_source_item_must_list_the_exact_convention(self) -> None:
        statement = statement_map(convention_ids=[OTHER_CONVENTION_ID])
        fields = [outer_field(), leaf_field()]

        errors, _counts = attach(
            fields=fields,
            statement=statement,
            source_ledger=ledger([scope_entry()]),
        )

        self.assertTrue(
            any("does not explicitly list convention" in error for error in errors)
        )
        self.assertNotIn("recursive_field_explicit_parent_route", fields[1])

    def test_scope_locator_must_stay_within_source_item_or_convention(self) -> None:
        """A syntactically valid nearby locator cannot receive route credit."""

        statement = statement_map()
        fields = [outer_field(), leaf_field()]
        errors, _counts = attach(
            fields=fields,
            statement=statement,
            source_ledger=ledger([scope_entry(source_locator="source.tex:99")]),
        )

        self.assertTrue(
            any("outside the selected source item and model-convention anchors" in error for error in errors)
        )
        self.assertNotIn("recursive_field_explicit_parent_route", fields[1])

    def test_same_short_leaf_in_another_fully_qualified_structure_cannot_match(self) -> None:
        statement = statement_map()
        fields = other_path_fields()

        errors, _counts = attach(
            fields=fields,
            statement=statement,
            source_ledger=ledger([scope_entry()]),
        )

        self.assertTrue(
            any("0 generated fields with its exact root/field chain" in error for error in errors)
        )
        self.assertTrue(
            all("recursive_field_explicit_parent_route" not in field for field in fields)
        )

    def test_ambiguous_direct_parent_route_fails_closed(self) -> None:
        statement = statement_map()
        fields = [outer_field(), leaf_field()]
        parent = parent_item(statement)

        errors, _counts = attach(
            fields=fields,
            statement=statement,
            source_ledger=ledger([scope_entry()]),
            parents=[parent, copy.deepcopy(parent)],
        )

        self.assertTrue(
            any("2 exact current direct parent routes" in error for error in errors)
        )
        self.assertNotIn("recursive_field_explicit_parent_route", fields[1])

    def test_complementary_routes_on_one_parent_choose_canonical_route(self) -> None:
        """An atom receipt must not duplicate its full source-contract parent."""

        statement = statement_map()
        fields = [outer_field(), leaf_field()]
        parent = semantic_contract_parent_item(statement)
        atom_parent = source_claim_atom_parent_item(statement)
        parent["source_claim_atom_association"] = atom_parent[
            "source_claim_atom_association"
        ]
        parent["source_claim_atom_contexts"] = atom_parent[
            "source_claim_atom_contexts"
        ]

        errors, _counts = attach(
            fields=fields,
            statement=statement,
            source_ledger=ledger([scope_entry()]),
            parents=[parent],
        )

        self.assertEqual(errors, [])
        self.assertEqual(
            fields[1]["recursive_field_explicit_parent_route"][
                "parent_association_field"
            ],
            "semantic_contract_source_association",
        )

    def test_tampered_parent_route_identity_or_signature_cannot_attach(self) -> None:
        statement = statement_map()
        for label, mutate in (
            (
                "identity",
                lambda parent: parent["source_statement_association"].update(
                    {
                        "reviewed_declaration_identity": {
                            "qualified_declaration": PARENT_DECLARATION,
                            "declaration_sha256": "c" * 64,
                        }
                    }
                ),
            ),
            (
                "signature",
                lambda parent: parent["source_statement_association"].update(
                    {
                        "reviewed_elaborated_signature_identity": parent_signature(
                            digest="d" * 64
                        )
                    }
                ),
            ),
        ):
            with self.subTest(label=label):
                fields = [outer_field(), leaf_field()]
                parent = parent_item(statement)
                mutate(parent)
                errors, _counts = attach(
                    fields=fields,
                    statement=statement,
                    source_ledger=ledger([scope_entry()]),
                    parents=[parent],
                )
                self.assertTrue(
                    any("0 exact current direct parent routes" in error for error in errors)
                )
                self.assertNotIn("recursive_field_explicit_parent_route", fields[1])

        support_fields = [outer_field(), leaf_field()]
        support_errors, _counts = attach(
            fields=support_fields,
            statement=statement,
            source_ledger=ledger([scope_entry()]),
            parents=[
                semantic_contract_parent_item(
                    statement,
                    role="supporting_helper",
                    origin="helper_support_route",
                )
            ],
        )
        self.assertTrue(
            any("0 exact current direct parent routes" in error for error in support_errors)
        )
        self.assertNotIn("recursive_field_explicit_parent_route", support_fields[1])

        saved_route_fields = [outer_field(), leaf_field()]
        saved_route_ledger = ledger([scope_entry()])
        saved_route_errors, _counts = attach(
            fields=saved_route_fields,
            statement=statement,
            source_ledger=saved_route_ledger,
        )
        self.assertEqual(saved_route_errors, [])
        saved_route = saved_route_fields[1]["recursive_field_explicit_parent_route"]
        assert isinstance(saved_route, dict)
        saved_route["parent_association_field"] = (
            "semantic_contract_source_association"
        )
        saved_route["parent_source_association_role"] = "supporting_helper"
        saved_route["parent_source_association_origin"] = "helper_support_route"
        saved_route["association_sha256"] = (
            DISPOSITION.recursive_field_parent_route_record_digest(saved_route)
        )
        saved_route_errors = DISPOSITION.recursive_field_target_disposition_errors(
            saved_route_fields[1],
            {
                "classification": "approved_source_convention",
                "source_target_disposition": "approved_source_convention",
                "source_location": "source.tex:20",
                "model_convention_ids": [CONVENTION_ID],
                "model_convention_sha256_by_id": {
                    CONVENTION_ID: DISPOSITION.model_convention_semantic_digest(
                        saved_route_ledger["model_conventions"][0]
                    )
                },
            },
            statement_map=statement,
            source_proof_fidelity=saved_route_ledger,
        )
        self.assertTrue(
            any("direct evidence/spec role with no support origin" in error for error in saved_route_errors)
        )

    def test_saved_route_cannot_move_to_a_different_generated_field_path(self) -> None:
        statement = statement_map()
        source_ledger = ledger([scope_entry()])
        fields = [outer_field(), leaf_field()]
        errors, _counts = attach(
            fields=fields,
            statement=statement,
            source_ledger=source_ledger,
        )
        self.assertEqual(errors, [])
        route = fields[1]["recursive_field_explicit_parent_route"]
        assert isinstance(route, dict)
        route["field_chain"] = [
            {"structure": ROOT_RECORD, "field": "endpoint"},
            {"structure": NESTED_RECORD, "field": "other_derivative"},
        ]
        route["association_sha256"] = (
            DISPOSITION.recursive_field_parent_route_record_digest(route)
        )
        response = {
            "classification": "approved_source_convention",
            "source_target_disposition": "approved_source_convention",
            "source_location": "source.tex:20",
            "model_convention_ids": [CONVENTION_ID],
            "model_convention_sha256_by_id": {
                CONVENTION_ID: DISPOSITION.model_convention_semantic_digest(
                    source_ledger["model_conventions"][0]
                )
            },
        }
        disposition_errors = DISPOSITION.recursive_field_target_disposition_errors(
            fields[1],
            response,
            statement_map=statement,
            source_proof_fidelity=source_ledger,
        )
        self.assertTrue(
            any(
                "does not resolve to exactly one current convention field scope"
                in error
                for error in disposition_errors
            )
        )

    def test_literal_scoped_field_must_repeat_its_exact_source_locator(self) -> None:
        statement = statement_map()
        source_ledger = ledger(
            [scope_entry(permitted_classifications=["validated_source_assumption"])]
        )
        fields = [outer_field(), leaf_field()]
        errors, _counts = attach(
            fields=fields,
            statement=statement,
            source_ledger=source_ledger,
        )
        self.assertEqual(errors, [])
        disposition_errors = DISPOSITION.recursive_field_target_disposition_errors(
            fields[1],
            {
                "classification": "validated_source_assumption",
                "source_location": "source.tex:10",
            },
            statement_map=statement,
            source_proof_fidelity=source_ledger,
        )
        self.assertTrue(
            any("source location must equal" in error for error in disposition_errors)
        )

        self.assertTrue(
            any(
                "must use source_target_disposition literal_source_match" in error
                for error in DISPOSITION.recursive_field_target_disposition_errors(
                    fields[1],
                    {
                        "classification": "validated_source_assumption",
                        "source_location": "source.tex:20",
                    },
                    statement_map=statement,
                    source_proof_fidelity=source_ledger,
                )
            )
        )
        self.assertEqual(
            DISPOSITION.recursive_field_target_disposition_errors(
                fields[1],
                {
                    "classification": "validated_source_assumption",
                    "source_target_disposition": "literal_source_match",
                    "source_location": "source.tex:20",
                },
                statement_map=statement,
                source_proof_fidelity=source_ledger,
            ),
            [],
        )

    def test_leaf_scope_rejects_non_source_credit_classifications(self) -> None:
        """A self-consistent route may not invent a new credit channel."""

        statement = statement_map()
        source_ledger = ledger([scope_entry()])
        fields = [outer_field(), leaf_field()]
        errors, _counts = attach(
            fields=fields,
            statement=statement,
            source_ledger=source_ledger,
        )
        self.assertEqual(errors, [])
        route = fields[1]["recursive_field_explicit_parent_route"]
        assert isinstance(route, dict)
        route["permitted_classifications"] = ["proved_from_primitives"]
        route["field_scope_sha256"] = (
            DISPOSITION.recursive_field_source_scope_record_digest(
                {
                    "source_item": SOURCE_ITEM_KEY,
                    "root_record": ROOT_RECORD,
                    "field_chain": scope_entry()["field_chain"],
                    "source_locator": "source.tex:20",
                    "permitted_classifications": ["proved_from_primitives"],
                }
            )
        )
        route["association_sha256"] = (
            DISPOSITION.recursive_field_parent_route_record_digest(route)
        )
        convention = source_ledger["model_conventions"][0]
        assert isinstance(convention, dict)
        scope = convention["recursive_field_source_scope"]
        assert isinstance(scope, dict)
        entry = scope["entries"][0]
        assert isinstance(entry, dict)
        entry["permitted_classifications"] = ["proved_from_primitives"]
        route["convention_sha256"] = DISPOSITION.model_convention_record_digest(
            convention
        )
        route["association_sha256"] = (
            DISPOSITION.recursive_field_parent_route_record_digest(route)
        )

        disposition_errors = DISPOSITION.recursive_field_target_disposition_errors(
            fields[1],
            {
                "classification": "proved_from_primitives",
                "source_location": "source.tex:20",
            },
            statement_map=statement,
            source_proof_fidelity=source_ledger,
        )
        self.assertTrue(
            any("outside the source-credit protocol" in error for error in disposition_errors)
        )

    def test_saved_route_must_rejoin_current_ledger_scope(self) -> None:
        statement = statement_map()
        source_ledger = ledger([scope_entry()])
        fields = [outer_field(), leaf_field()]
        errors, _counts = attach(
            fields=fields,
            statement=statement,
            source_ledger=source_ledger,
        )
        self.assertEqual(errors, [])
        convention = source_ledger["model_conventions"][0]
        assert isinstance(convention, dict)
        scope = convention["recursive_field_source_scope"]
        assert isinstance(scope, dict)
        entry = scope["entries"][0]
        assert isinstance(entry, dict)
        entry["source_locator"] = "source.tex:21"
        route = fields[1]["recursive_field_explicit_parent_route"]
        assert isinstance(route, dict)
        route["source_locator"] = "source.tex:21"
        route["field_scope_sha256"] = (
            DISPOSITION.recursive_field_source_scope_record_digest(entry)
        )
        route["convention_sha256"] = DISPOSITION.model_convention_record_digest(
            convention
        )
        route["association_sha256"] = (
            DISPOSITION.recursive_field_parent_route_record_digest(route)
        )
        # This deliberately recomputes every route and convention pin after
        # changing the current scope. The only remaining defect is semantic:
        # line 21 lies in neither the selected source item nor the convention
        # anchor union, so no self-consistent ledger route earns credit.
        disposition_errors = DISPOSITION.recursive_field_target_disposition_errors(
            fields[1],
            {
                "classification": "approved_source_convention",
                "source_target_disposition": "approved_source_convention",
                "source_location": "source.tex:21",
                "model_convention_ids": [CONVENTION_ID],
                "model_convention_sha256_by_id": {
                    CONVENTION_ID: DISPOSITION.model_convention_semantic_digest(
                        convention
                    )
                },
            },
            statement_map=statement,
            source_proof_fidelity=source_ledger,
        )
        self.assertTrue(
            any(
                "outside the selected source item and model-convention anchors"
                in error
                for error in disposition_errors
            )
        )

    def test_scope_or_permitted_classification_change_invalidates_item_reuse(self) -> None:
        statement = statement_map()
        original_ledger = ledger([scope_entry()])
        original_fields = [outer_field(), leaf_field()]
        original_errors, _counts = attach(
            fields=original_fields,
            statement=statement,
            source_ledger=original_ledger,
        )
        self.assertEqual(original_errors, [])
        attach_item_digests(
            original_fields, statement=statement, source_ledger=original_ledger
        )

        changed_ledger = ledger(
            [
                scope_entry(
                    permitted_classifications=[
                        "validated_source_assumption",
                        "approved_source_convention",
                    ]
                )
            ]
        )
        changed_fields = [outer_field(), leaf_field()]
        changed_errors, _counts = attach(
            fields=changed_fields,
            statement=statement,
            source_ledger=changed_ledger,
        )
        self.assertEqual(changed_errors, [])
        attach_item_digests(
            changed_fields, statement=statement, source_ledger=changed_ledger
        )

        self.assertNotEqual(
            original_fields[1]["recursive_field_explicit_parent_route"][
                "field_scope_sha256"
            ],
            changed_fields[1]["recursive_field_explicit_parent_route"][
                "field_scope_sha256"
            ],
        )
        self.assertNotEqual(
            original_fields[1]["source_record_item_sha256"],
            changed_fields[1]["source_record_item_sha256"],
        )

    def test_container_and_exact_convention_receipt_guards_fail_closed(self) -> None:
        statement = statement_map()
        container_entry = scope_entry(
            field_chain=[{"structure": ROOT_RECORD, "field": "endpoint"}],
            permitted_classifications=["container_recursively_audited"],
        )
        fields = [outer_field(), leaf_field()]
        source_ledger = ledger([container_entry], include_other=True)
        errors, _counts = attach(
            fields=fields, statement=statement, source_ledger=source_ledger
        )
        self.assertEqual(errors, [])
        self.assertIn("recursive_field_explicit_parent_route", fields[0])
        self.assertNotIn("recursive_field_explicit_parent_route", fields[1])
        self.assertEqual(
            DISPOSITION.recursive_field_target_disposition_errors(
                fields[0],
                {"classification": "container_recursively_audited"},
                statement_map=statement,
                source_proof_fidelity=source_ledger,
            ),
            [],
        )

        malformed_fields = [outer_field(), leaf_field()]
        malformed_errors, _counts = attach(
            fields=malformed_fields,
            statement=statement,
            source_ledger=ledger(
                [
                    scope_entry(
                        field_chain=[{"structure": ROOT_RECORD, "field": "endpoint"}],
                        permitted_classifications=[
                            "container_recursively_audited",
                            "approved_source_convention",
                        ],
                    ),
                    scope_entry(
                        permitted_classifications=[
                            "container_recursively_audited"
                        ]
                    ),
                ]
            ),
        )
        self.assertTrue(
            any("nested-record field" in error for error in malformed_errors)
        )
        self.assertTrue(
            any("non-container leaf" in error for error in malformed_errors)
        )

        leaf_fields = [outer_field(), leaf_field()]
        leaf_ledger = ledger([scope_entry()], include_other=True)
        leaf_errors, _counts = attach(
            fields=leaf_fields, statement=statement, source_ledger=leaf_ledger
        )
        self.assertEqual(leaf_errors, [])
        wrong_convention_response = {
            "classification": "approved_source_convention",
            "source_target_disposition": "approved_source_convention",
            "source_location": "source.tex:20",
            "model_convention_ids": [OTHER_CONVENTION_ID],
            "model_convention_sha256_by_id": {
                OTHER_CONVENTION_ID: DISPOSITION.model_convention_semantic_digest(
                    leaf_ledger["model_conventions"][1]
                )
            },
        }
        convention_errors = DISPOSITION.recursive_field_target_disposition_errors(
            leaf_fields[1],
            wrong_convention_response,
            statement_map=statement,
            source_proof_fidelity=leaf_ledger,
        )
        self.assertTrue(
            any("exactly the generated parent-route convention_id" in error for error in convention_errors)
        )


if __name__ == "__main__":
    unittest.main()
