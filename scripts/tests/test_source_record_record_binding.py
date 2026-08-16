#!/usr/bin/env python3
"""Regression coverage for v10 source-record model-binder projection."""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    import_root_text = str(import_root)
    if import_root_text not in sys.path:
        sys.path.insert(0, import_root_text)

import audit_repository as REPOSITORY  # noqa: E402
from lean_signature_manifest import (  # noqa: E402
    FOUNDATION_STRUCTURAL_DATA_ALLOWLIST_SHA256,
    FOUNDATION_STRUCTURAL_DATA_ALLOWLIST_VERSION,
    RECURSIVE_FIELD_SAFETY_LOCATOR_SCHEMA,
    RECURSIVE_FIELD_SAFETY_RECEIPT_SCHEMA,
    recursive_field_safety_locator_identity,
)
from source_record_integrity import stamp_source_record_audit_receipts  # noqa: E402


PAPER = "Fixture"
AUDIT_DIGEST = "a" * 64
DECLARATION = "Fixture.Paper.endpoint"
MODEL_ROOT = "Fixture.Model"
SEMANTIC_KEY = "semantic-model::endpoint"
TRUTH_FIELD = "Fixture.Model.truth"
NESTED_FIELD = "Fixture.Model.nested"
NESTED_DETAIL = "Fixture.Nested.detail"
FIELDLESS_DATA = "Fixture.Model.comparison"


def recursive_field_item(
    *,
    judgment_key: str,
    structure: str,
    nested_structures: list[str],
    declaration: str,
    value_sort: str,
    payload_safety: str,
) -> dict[str, object]:
    """Build a transport-valid synthetic Lean field-slot receipt.

    These tests exercise the Python closure gate; the elaborated-slot safety
    classifier itself has separate Lean integration coverage.  Keep the
    fixture's locator/receipt shape identical to generated raw audits so a
    missing or altered receipt cannot accidentally regain data credit.
    """

    locator: dict[str, object] = {
        "schema": RECURSIVE_FIELD_SAFETY_LOCATOR_SCHEMA,
        "kind": "projection",
        "declaration": declaration,
        "field_index": 0,
    }
    locator["field_identity_sha256"] = recursive_field_safety_locator_identity(locator)
    structural = payload_safety == "structural_data"
    if value_sort == "true":
        route = "proof_payload"
        reasons = ["direct_proposition"]
    elif structural:
        route = "foundation_structural_data"
        reasons = ["foundation_structural_data"]
    else:
        route = "requires_explicit_closure"
        reasons = ["nonstructural_fixture_wrapper"]
    receipt = {
        "schema": RECURSIVE_FIELD_SAFETY_RECEIPT_SCHEMA,
        "field_identity_sha256": locator["field_identity_sha256"],
        "value_sort": value_sort,
        "payload_safety": payload_safety,
        "status": "ok",
        "route": route,
        "normalized_type_sha256": hashlib.sha256(
            f"fixture::{declaration}::{value_sort}::{payload_safety}".encode("utf-8")
        ).hexdigest(),
        "reason_codes": reasons,
        "foundation_module": "Init.Prelude" if structural else "",
        "foundation_head": "Nat" if structural else "",
        "foundation_allowlist_version": FOUNDATION_STRUCTURAL_DATA_ALLOWLIST_VERSION,
        "foundation_allowlist_sha256": FOUNDATION_STRUCTURAL_DATA_ALLOWLIST_SHA256,
    }
    return {
        "judgment_key": judgment_key,
        "structure": structure,
        "nested_structures": nested_structures,
        "proposition_sort": value_sort,
        "payload_safety": payload_safety,
        "elaborated_field_safety_locator": locator,
        "elaborated_field_safety_receipt": receipt,
    }


def source_record_payload(
    *,
    binding_names: list[str] | None = None,
    dependency_binder: str | None = None,
    include_fieldless_data: bool = False,
    truth_semantic_kind: str = "proposition",
    truth_value_sort: str = "true",
    truth_payload_safety: str = "proof_payload",
    fieldless_payload_safety: str = "structural_data",
) -> dict[str, object]:
    """Build a small recursive record surface with one source proposition."""

    identity = {"qualified_declaration": DECLARATION}
    payload: dict[str, object] = {
        "prompt_version": REPOSITORY.REQUIRED_SOURCE_RECORD_PROMPT_VERSION,
        "source_record_audit_sha256": AUDIT_DIGEST,
        "expected_field_judgment_keys": [
            TRUTH_FIELD,
            NESTED_FIELD,
            NESTED_DETAIL,
        ],
        "recursive_field_items": [
            recursive_field_item(
                judgment_key=TRUTH_FIELD,
                structure=MODEL_ROOT,
                nested_structures=[],
                declaration=TRUTH_FIELD,
                value_sort=truth_value_sort,
                payload_safety=truth_payload_safety,
            ),
            recursive_field_item(
                judgment_key=NESTED_FIELD,
                structure=MODEL_ROOT,
                nested_structures=["Fixture.Nested"],
                declaration=NESTED_FIELD,
                value_sort="false",
                payload_safety="structural_data",
            ),
            recursive_field_item(
                judgment_key=NESTED_DETAIL,
                structure="Fixture.Nested",
                nested_structures=[],
                declaration=NESTED_DETAIL,
                value_sort="false",
                payload_safety="structural_data",
            ),
        ],
        "semantic_model_items": [
            {
                "judgment_key": SEMANTIC_KEY,
                "row": "endpoint",
                "qualified_declaration": DECLARATION,
                "reviewed_declaration_identity": identity,
                "record_input_bindings": [
                    {
                        "binder_names": binding_names or ["carrier"],
                        "record_roots": [MODEL_ROOT],
                    }
                ],
                "dimensions": [
                    {
                        "id": "carrier_and_domain",
                        "detected_from_expanded_surface": False,
                        "requires_checked_bridge_when_detected": False,
                        "requires_parameter_translation_when_detected": False,
                    }
                ],
            }
        ],
        "conclusion_dependency_items": [
            {
                "judgment_key": "endpoint.carrier",
                "qualified_declaration": DECLARATION,
                "reviewed_declaration_identity": identity,
                "kind": "record_conclusion_input",
                "record": MODEL_ROOT,
                "binder": dependency_binder or "carrier",
                "record_aliases": ["ModelAlias"],
                "rejected_constructors": [],
                "conclusion_fields": [
                    {
                        "judgment_key": TRUTH_FIELD,
                        "source_antecedent_eligible": True,
                        "relation_to_row_result": "",
                        "semantic_kind": truth_semantic_kind,
                    }
                ],
            }
        ],
    }
    if include_fieldless_data:
        expected = payload["expected_field_judgment_keys"]
        fields = payload["recursive_field_items"]
        assert isinstance(expected, list) and isinstance(fields, list)
        expected.append(FIELDLESS_DATA)
        fields.append(
            recursive_field_item(
                judgment_key=FIELDLESS_DATA,
                structure=MODEL_ROOT,
                nested_structures=["Fixture.ComparisonEnum"],
                declaration=FIELDLESS_DATA,
                value_sort="false",
                payload_safety=fieldless_payload_safety,
            )
        )
    return payload


def source_record_judgments(*, include_fieldless_data: bool = False) -> dict[str, object]:
    payload: dict[str, object] = {
        "schema": 1,
        "paper": PAPER,
        "prompt_version": REPOSITORY.REQUIRED_SOURCE_RECORD_PROMPT_VERSION,
        "source_record_audit_sha256": AUDIT_DIGEST,
        "validator": "fixture-reviewer",
        "validated_at": "2026-07-26T00:00:00Z",
        "items": {
            TRUTH_FIELD: {
                "classification": "validated_source_assumption",
                "source_location": "source.tex:10",
            },
            NESTED_FIELD: {
                "classification": "container_recursively_audited",
            },
            NESTED_DETAIL: {
                "classification": "nonpropositional_witness_data",
            },
            # The canonical sidecar is complete over every generated response
            # group.  This dependency remains unresolved on its own; the tests
            # below exercise whether the exact recursive semantic-model binding
            # can discharge it without granting name-based source credit.
            "endpoint.carrier": {
                "classification": "unresolved_assumed_math",
            },
            SEMANTIC_KEY: {
                "classification": "semantic_model_review",
                "semantic_model_dimensions": {
                    "carrier_and_domain": {
                        "verdict": "not_applicable",
                        "source_locator": "source.tex:10",
                        "semantic_comparison": (
                            "The fixture has no generated carrier restriction to compare."
                        ),
                        "lean_evidence": (
                            "The generated expanded surface contains no carrier restriction."
                        ),
                    }
                },
            },
        },
    }
    if include_fieldless_data:
        items = payload["items"]
        assert isinstance(items, dict)
        items[FIELDLESS_DATA] = {
            "classification": "nonpropositional_witness_data",
        }
    return payload


class SourceRecordModelBinderProjectionTests(unittest.TestCase):
    def bindings(
        self,
        *,
        omit_judgment: str | None = None,
        classification: tuple[str, str] | None = None,
        binding_names: list[str] | None = None,
        dependency_binder: str | None = None,
        include_fieldless_data: bool = False,
        truth_semantic_kind: str = "proposition",
        truth_value_sort: str = "true",
        truth_payload_safety: str = "proof_payload",
        fieldless_payload_safety: str = "structural_data",
    ) -> dict[str, tuple[tuple[frozenset[str], str, frozenset[str]], ...]]:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / PAPER
            audit = folder / "audit"
            audit.mkdir(parents=True)
            judgments = source_record_judgments(
                include_fieldless_data=include_fieldless_data
            )
            items = judgments["items"]
            assert isinstance(items, dict)
            if omit_judgment:
                items.pop(omit_judgment)
            if classification:
                key, value = classification
                item = items[key]
                assert isinstance(item, dict)
                item["classification"] = value
            payload = source_record_payload(
                binding_names=binding_names,
                dependency_binder=dependency_binder,
                include_fieldless_data=include_fieldless_data,
                truth_semantic_kind=truth_semantic_kind,
                truth_value_sort=truth_value_sort,
                truth_payload_safety=truth_payload_safety,
                fieldless_payload_safety=fieldless_payload_safety,
            )
            stamp_source_record_audit_receipts(payload)
            judgments["source_record_audit_sha256"] = payload[
                "source_record_audit_sha256"
            ]
            (audit / "source_record_audit.json").write_text(
                json.dumps(payload), encoding="utf-8"
            )
            (audit / "source_record_match_llm.json").write_text(
                json.dumps(judgments), encoding="utf-8"
            )
            return REPOSITORY.source_record_complete_model_record_bindings(
                PAPER,
                folder,
                {},
                "formalized",
            )

    def test_complete_current_recursive_record_binding_is_admitted(self) -> None:
        self.assertEqual(
            self.bindings(),
            {
                DECLARATION: (
                    (frozenset({"carrier"}), MODEL_ROOT, frozenset({"ModelAlias"})),
                )
            },
        )

    def test_named_binding_requires_generated_record_root_or_alias(self) -> None:
        bindings = self.bindings()
        with tempfile.TemporaryDirectory() as temporary:
            interface = Path(temporary) / "PaperInterface.lean"
            interface.write_text(
                "namespace Fixture.Paper\n"
                "theorem endpoint (carrier : ModelAlias Nat) : True := by trivial\n"
                "end Fixture.Paper\n",
                encoding="utf-8",
            )
            declaration = REPOSITORY.LeanDeclaration(
                interface,
                2,
                "theorem",
                "endpoint",
                "theorem endpoint (carrier : ModelAlias Nat) : True := by trivial",
            )

            self.assertTrue(
                REPOSITORY.premise_matches_current_model_record_binding(
                    "carrier : ModelAlias Nat", declaration, bindings
                )
            )
            self.assertTrue(
                REPOSITORY.premise_matches_current_model_record_binding(
                    "carrier : Fixture.Model Nat", declaration, bindings
                )
            )
            self.assertFalse(
                REPOSITORY.premise_matches_current_model_record_binding(
                    "carrier : Fixture.OtherModel Nat", declaration, bindings
                )
            )
            self.assertFalse(
                REPOSITORY.premise_matches_current_model_record_binding(
                    "other : ModelAlias Nat", declaration, bindings
                )
            )

    def test_missing_recursive_field_judgment_rejects_the_binding(self) -> None:
        self.assertEqual(self.bindings(omit_judgment=NESTED_DETAIL), {})

    def test_unresolved_recursive_field_judgment_rejects_the_binding(self) -> None:
        self.assertEqual(
            self.bindings(
                classification=(TRUTH_FIELD, "unresolved_assumed_math")
            ),
            {},
        )

    def test_grouped_generated_binder_matches_the_exact_semantic_binding(self) -> None:
        self.assertEqual(
            self.bindings(
                binding_names=["first", "second"],
                dependency_binder="first second",
            ),
            {
                DECLARATION: (
                    (
                        frozenset({"first", "second"}),
                        MODEL_ROOT,
                        frozenset({"ModelAlias"}),
                    ),
                )
            },
        )

    def test_partial_generated_binder_does_not_match_a_grouped_binding(self) -> None:
        self.assertEqual(
            self.bindings(
                binding_names=["first", "second"],
                dependency_binder="first",
            ),
            {},
        )

    def test_explicit_fieldless_nonpropositional_data_closes_the_record(self) -> None:
        self.assertEqual(
            self.bindings(include_fieldless_data=True),
            {
                DECLARATION: (
                    (frozenset({"carrier"}), MODEL_ROOT, frozenset({"ModelAlias"})),
                )
            },
        )

    def test_nonproposition_field_does_not_require_proposition_evidence(self) -> None:
        self.assertEqual(
            self.bindings(
                classification=(TRUTH_FIELD, "nonpropositional_witness_data"),
                truth_semantic_kind="unknown_nondata",
                truth_value_sort="false",
                truth_payload_safety="structural_data",
            ),
            {
                DECLARATION: (
                    (frozenset({"carrier"}), MODEL_ROOT, frozenset({"ModelAlias"})),
                )
            },
        )

    def test_proposition_field_cannot_use_raw_witness_data(self) -> None:
        self.assertEqual(
            self.bindings(
                classification=(TRUTH_FIELD, "nonpropositional_witness_data"),
                truth_semantic_kind="proposition",
            ),
            {},
        )

    def test_nonstructural_field_cannot_use_raw_witness_data(self) -> None:
        self.assertEqual(
            self.bindings(
                classification=(TRUTH_FIELD, "nonpropositional_witness_data"),
                truth_semantic_kind="unknown_nondata",
                truth_value_sort="false",
                truth_payload_safety="requires_source_or_lean_closure",
            ),
            {},
        )

    def test_nonstructural_fieldless_data_does_not_close_a_record(self) -> None:
        self.assertEqual(
            self.bindings(
                include_fieldless_data=True,
                fieldless_payload_safety="requires_source_or_lean_closure",
            ),
            {},
        )

    def test_missing_field_semantic_kind_rejects_the_binding(self) -> None:
        self.assertEqual(self.bindings(truth_semantic_kind=""), {})


class SourceRecordAdministrativeProjectionRebindContextTests(unittest.TestCase):
    def test_missing_or_invalid_status_keeps_optional_rebind_inactive(self) -> None:
        for status_contents in (None, "not valid JSON"):
            with self.subTest(status_contents=status_contents), tempfile.TemporaryDirectory() as temporary:
                folder = Path(temporary) / PAPER
                (folder / "audit").mkdir(parents=True)
                if status_contents is not None:
                    (folder / "status.json").write_text(
                        status_contents, encoding="utf-8"
                    )
                context, error = REPOSITORY.source_record_target_disposition_rebind_context(
                    folder,
                    {},
                    {"paper": PAPER},
                )
                self.assertIsNone(context)
                self.assertEqual(error, "")

    def test_present_rebind_still_fails_closed_without_valid_status(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / PAPER
            audit = folder / "audit"
            audit.mkdir(parents=True)
            (folder / "status.json").write_text("not valid JSON", encoding="utf-8")
            (audit / "source_record_administrative_projection_rebind.json").write_text(
                "{}", encoding="utf-8"
            )
            context, error = REPOSITORY.source_record_target_disposition_rebind_context(
                folder,
                {},
                {"paper": PAPER},
            )
            self.assertIsNone(context)
            self.assertTrue(error)


class SourceRecordConclusionDependencyIntegrationTests(unittest.TestCase):
    def findings(
        self,
        *,
        truth_classification: str = "approved_source_convention",
        dependency_root: str = MODEL_ROOT,
        include_semantic_review: bool = True,
        binding_names: list[str] | None = None,
        dependency_binder: str | None = None,
    ) -> list[object]:
        payload = json.loads(
            json.dumps(
                source_record_payload(
                    binding_names=binding_names,
                    dependency_binder=dependency_binder,
                )
            )
        )
        payload.update(
            {
                "import_module": "Fixture.PaperInterface",
                "recursive_field_count": 3,
                "boundary_input_count": 0,
                "rows_with_record_premises": ["endpoint"],
                "expected_semantic_model_judgment_keys": [SEMANTIC_KEY],
            }
        )
        dependencies = payload["conclusion_dependency_items"]
        assert isinstance(dependencies, list) and len(dependencies) == 1
        dependency = dependencies[0]
        assert isinstance(dependency, dict)
        dependency["record"] = dependency_root
        if not include_semantic_review:
            payload["semantic_model_items"] = []
            payload["expected_semantic_model_judgment_keys"] = []

        judgments = source_record_judgments()
        items = judgments["items"]
        assert isinstance(items, dict)
        truth = items[TRUTH_FIELD]
        assert isinstance(truth, dict)
        truth["classification"] = truth_classification
        if not include_semantic_review:
            items.pop(SEMANTIC_KEY)

        with tempfile.TemporaryDirectory() as temporary:
            folder = Path(temporary) / PAPER
            audit = folder / "audit"
            audit.mkdir(parents=True)
            stamp_source_record_audit_receipts(payload)
            judgments["source_record_audit_sha256"] = payload[
                "source_record_audit_sha256"
            ]
            (audit / "source_record_audit.json").write_text(
                json.dumps(payload), encoding="utf-8"
            )
            (audit / "source_record_match_llm.json").write_text(
                json.dumps(judgments), encoding="utf-8"
            )
            with patch.object(
                REPOSITORY,
                "run_source_record_audit_helper",
                return_value=(payload, ""),
            ):
                return REPOSITORY.check_source_record_audit(
                    PAPER,
                    folder,
                    {},
                    "formalized",
                    strict_assumption_policy=True,
                )

    @staticmethod
    def unresolved_messages(findings: list[object]) -> list[str]:
        return [
            finding.message
            for finding in findings
            if isinstance(finding, REPOSITORY.Finding)
            and "unresolved conclusion-bearing theorem input" in finding.message
        ]

    def test_complete_semantic_record_resolves_its_exact_dependency(self) -> None:
        findings = self.findings()

        self.assertEqual(self.unresolved_messages(findings), [])

    def test_unresolved_recursive_field_does_not_resolve_record_dependency(self) -> None:
        findings = self.findings(truth_classification="unresolved_assumed_math")

        self.assertTrue(self.unresolved_messages(findings))

    def test_missing_semantic_review_does_not_resolve_record_dependency(self) -> None:
        findings = self.findings(include_semantic_review=False)

        self.assertTrue(self.unresolved_messages(findings))

    def test_different_record_root_does_not_resolve_record_dependency(self) -> None:
        findings = self.findings(dependency_root="Fixture.OtherModel")

        self.assertTrue(self.unresolved_messages(findings))

    def test_grouped_binder_resolves_only_as_its_exact_generated_group(self) -> None:
        findings = self.findings(
            binding_names=["first", "second"],
            dependency_binder="first second",
        )

        self.assertEqual(self.unresolved_messages(findings), [])

    def test_partial_binder_does_not_resolve_a_grouped_generated_dependency(self) -> None:
        findings = self.findings(
            binding_names=["first", "second"],
            dependency_binder="first",
        )

        self.assertTrue(self.unresolved_messages(findings))


if __name__ == "__main__":
    unittest.main()
