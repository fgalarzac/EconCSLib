#!/usr/bin/env python3
"""Focused tests for fail-closed current component-projection receipts."""

from __future__ import annotations

import copy
import contextlib
import io
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
from scripts import source_record_component_projection as PROJECTION  # noqa: E402
from scripts import source_record_target_disposition as TARGET  # noqa: E402
from scripts.source_record_integrity import stamp_source_record_audit_receipts  # noqa: E402


PAPER = "FixturePaper"
PROMPT = "source-record-v10-semantic-conclusion-boundary-contract"


def digest(char: str) -> str:
    return char * 64


def _identity() -> tuple[dict[str, object], list[dict[str, str]]]:
    return (
        {
            "qualified_declaration": f"{PAPER}.PaperInterface.reviewed_row",
            "declaration_sha256": digest("a"),
        },
        [
            {
                "qualified_declaration": f"{PAPER}.PaperInterface.reviewed_row",
                "elaborated_signature_sha256": digest("b"),
                "semantic_dependency_sha256": digest("c"),
            }
        ],
    )


def _ineligible_item(item: dict[str, object]) -> dict[str, object]:
    item["source_record_item_reuse_eligibility"] = {
        "eligible": False,
        "blockers": ["aggregate-only fixture"],
    }
    return item


def _association(*, direct_field: str) -> dict[str, object]:
    declaration, signatures = _identity()
    association: dict[str, object] = {
        "schema": 2,
        "reviewed_declaration_identity": declaration,
        "reviewed_elaborated_signature_identity": {
            "qualified_declaration": signatures[0]["qualified_declaration"],
            "elaborated_signature_sha256": signatures[0][
                "elaborated_signature_sha256"
            ],
        },
        "source_item_identities": [
            {
                "source_semantic_sha256": digest("e"),
                "source_map_item_sha256": digest("f"),
            }
        ],
    }
    association[direct_field] = (
        "explicit_source_map_direct_route"
        if direct_field == "association_mode"
        else "direct_source_route"
    )
    association["semantic_association_sha256"] = (
        TARGET.semantic_association_record_digest(
            [digest("e")],
            association["reviewed_elaborated_signature_identity"],
        )
    )
    return association


def _data_child() -> dict[str, object]:
    declaration, signatures = _identity()
    return _ineligible_item(
        {
            "judgment_key": "unrelated-storage-address-data",
            "kind": "theorem_facing_input",
            "reviewed_declaration_identity": declaration,
            "reviewed_elaborated_signature_identities": signatures,
            "proposition_sort": "false",
            "theorem_facing_semantic_role": "data_or_container",
            "semantic_restriction_role": "carrier_coherence_only",
            "semantic_restriction_candidates": [],
            "specialized_proof_dependency_kinds": [],
            "source_claim_component_role": "material",
            "source_claim_component_kind": "theorem_input",
            "result_relation": "",
            "input_section": "header",
            "input_origin": "header_binder",
            "lean_outer_binder_route": "outer_telescope",
            "lean_outer_binder_indices": [0],
            "structural_type_sha256": digest("1"),
        }
    )


def _result_child() -> dict[str, object]:
    declaration, signatures = _identity()
    return _ineligible_item(
        {
            "judgment_key": "unrelated-storage-address-result",
            "kind": "type_valued_certificate_result",
            "reviewed_declaration_identity": declaration,
            "reviewed_elaborated_signature_identities": signatures,
            "proposition_sort": "true",
            "theorem_facing_semantic_role": "proof_bearing",
            "semantic_restriction_role": "requires_source_or_lean_closure",
            "source_claim_component_role": "material",
            "source_claim_component_kind": "elaborated_result_type_witness",
            "result_occurrence_role": "provided_result",
            "elaborated_witness_path": "result/exists",
            "structural_type_sha256": digest("2"),
            "source_contract_association": _association(direct_field="association_mode"),
        }
    )


def _parent_semantic_item() -> dict[str, object]:
    declaration, signatures = _identity()
    return _ineligible_item(
        {
            "judgment_key": "semantic-model::opaque-generated-address",
            "kind": "semantic_model_comparison",
            "reviewed_declaration_identity": declaration,
            "reviewed_elaborated_signature_identities": signatures,
            "dimensions": [
                {
                    "id": "expanded_binders_and_domain",
                    "detected_from_expanded_surface": True,
                    "requires_checked_bridge_when_detected": False,
                    "requires_parameter_translation_when_detected": False,
                }
            ],
            "source_statement_association": _association(direct_field="role"),
        }
    )


def _component(
    child: dict[str, object], *, result: bool, traversal_slot: int
) -> dict[str, object]:
    declaration, signatures = _identity()
    occurrence: dict[str, object] = {
        "schema": 1,
        "surface": (
            "type_valued_certificate_result_items"
            if result
            else "theorem_facing_input_items"
        ),
        "kind": "result_type_certificate" if result else "theorem_input",
        "outer_telescope_indices": [] if result else [0],
        "outer_telescope_route": "" if result else "outer_telescope",
        "input_section": "" if result else "header",
        "input_origin": "" if result else "header_binder",
        "recursive_projection_sort": "",
        "traversal_slot": traversal_slot,
    }
    component: dict[str, object] = {
        "kind": child["kind"],
        "reviewed_declaration_identity": declaration,
        "reviewed_elaborated_signature_identities": signatures,
        "proposition_sort": child["proposition_sort"],
        "structural_type_sha256": child["structural_type_sha256"],
        "source_component_section": occurrence["surface"],
        "source_claim_component_kind": occurrence["kind"],
        "source_claim_component_sha256": digest("3" if result else "4"),
        "source_claim_component_occurrence": occurrence,
    }
    if result:
        component["result_occurrence_role"] = "provided_result"
        component["elaborated_witness_path"] = child["elaborated_witness_path"]
    return component


def raw_audit(*, include_result: bool = True) -> dict[str, object]:
    data = _data_child()
    parent = _parent_semantic_item()
    payload: dict[str, object] = {
        "paper": PAPER,
        "prompt_version": PROMPT,
        "source_record_policy_version": PROMPT,
        "theorem_facing_input_items": [data],
        "semantic_model_items": [parent],
        "theorem_realization_component_items": [_component(data, result=False, traversal_slot=0)],
        "lean_check": {"returncode": 0},
        "recursion_failure_count": 0,
    }
    if include_result:
        result = _result_child()
        payload["type_valued_certificate_result_items"] = [result]
        components = payload["theorem_realization_component_items"]
        assert isinstance(components, list)
        components.append(_component(result, result=True, traversal_slot=1))
    stamp_source_record_audit_receipts(payload)
    return payload


def parent_response(*, validator: str = "reviewer", timestamp: str = "2026-08-14T00:00:00Z") -> dict[str, object]:
    return {
        "classification": "semantic_model_review",
        "prompt_version": PROMPT,
        "source_record_audit_sha256": digest("9"),
        "validator": validator,
        "validated_at": timestamp,
        "semantic_model_dimensions": {
            "expanded_binders_and_domain": {
                "verdict": "matches_literal_source",
                "source_locator": "source.txt:1-2",
                "semantic_comparison": "The complete expanded binder domain is reviewed.",
                "lean_evidence": "The elaborated type was checked directly.",
            }
        },
    }


def reviewer_parent_response() -> dict[str, object]:
    """Return only reviewer-authored semantic content for a core template."""

    response = parent_response()
    for field in (
        "prompt_version",
        "source_record_audit_sha256",
        "validator",
        "validated_at",
    ):
        response.pop(field)
    return response


class SourceRecordComponentProjectionTests(unittest.TestCase):
    def _paper_dir(self, temporary: Path) -> Path:
        paper_dir = temporary / "papers" / PAPER
        (paper_dir / "audit").mkdir(parents=True)
        return paper_dir

    def _artifact(
        self, raw: dict[str, object], paper_dir: Path, response: dict[str, object]
    ) -> dict[str, object]:
        parent_key = _parent_semantic_item()["judgment_key"]
        assert isinstance(parent_key, str)
        with patch.object(
            PROJECTION,
            "_current_base_parent_items",
            return_value={parent_key: response},
        ):
            artifact, error = PROJECTION.build_component_projection_artifact(
                paper=PAPER,
                raw_audit=raw,
                base_sidecar={"ignored": True},
                base_sidecar_relative_path="audit/base.json",
                paper_dir=paper_dir,
            )
        self.assertEqual(error, "")
        self.assertIsNotNone(artifact)
        assert artifact is not None
        return artifact

    def _completed_parent_core_template(
        self, raw: dict[str, object]
    ) -> dict[str, object]:
        completed = copy.deepcopy(
            PROJECTION.component_parent_core_template(raw, paper=PAPER)
        )
        completed.pop("non_evidence_scaffold")
        completed.pop("must_not_be_written_to_repository_sidecar")
        completed["reviewed_current_semantics"] = True
        completed["reviewer"] = "Fixture parent-core reviewer"
        completed["validated_at"] = "2026-08-15T00:00:00Z"
        completed["review_notes"] = "Reviewed every exact current parent descriptor."
        groups = completed["parent_core_groups"]
        assert isinstance(groups, list)
        for group in groups:
            assert isinstance(group, dict)
            group["reviewed_current_semantics"] = True
            group["reviewer"] = "Fixture parent-core reviewer"
            group["validated_at"] = "2026-08-15T00:00:00Z"
            group["review_notes"] = "Complete source and Lean semantic review."
            group["response"] = reviewer_parent_response()
        return completed

    def _materialized_parent_core(
        self, raw: dict[str, object], paper_dir: Path
    ) -> dict[str, object]:
        core_path = PROJECTION.component_parent_core_artifact_path(paper_dir)
        return PROJECTION.materialize_component_parent_core(
            raw,
            self._completed_parent_core_template(raw),
            paper=PAPER,
            paper_dir=paper_dir,
            output_sidecar_path=core_path,
        )

    def test_parent_core_is_exact_partial_base_for_component_projection(self) -> None:
        raw = raw_audit()
        template = PROJECTION.component_parent_core_template(raw, paper=PAPER)
        groups = template["parent_core_groups"]
        self.assertIsInstance(groups, list)
        assert isinstance(groups, list)
        self.assertEqual(len(groups), 1)
        # Records intentionally have no serialized current judgment key: the
        # match relation is the descriptor and ordered raw item receipts.
        self.assertNotIn("judgment_key", groups[0])
        with tempfile.TemporaryDirectory() as directory:
            paper_dir = self._paper_dir(Path(directory))
            core = self._materialized_parent_core(raw, paper_dir)
            core_path = PROJECTION.component_parent_core_artifact_path(paper_dir)
            items = core["items"]
            assert isinstance(items, dict)
            self.assertEqual(
                set(items), {"semantic-model::opaque-generated-address"}
            )
            self.assertEqual(
                PROJECTION.component_parent_core_validation_error(
                    core,
                    raw,
                    paper=PAPER,
                    paper_dir=paper_dir,
                    sidecar_path=core_path,
                ),
                "",
            )
            raw_parents = raw["semantic_model_items"]
            assert isinstance(raw_parents, list) and isinstance(raw_parents[0], dict)
            raw_association = raw_parents[0]["source_statement_association"]
            assert isinstance(raw_association, dict)
            response = items["semantic-model::opaque-generated-address"]
            assert isinstance(response, dict)
            dimensions = response["semantic_model_dimensions"]
            assert isinstance(dimensions, dict)
            expanded = dimensions["expanded_binders_and_domain"]
            assert isinstance(expanded, dict)
            self.assertEqual(
                expanded["semantic_association_sha256"],
                raw_association["semantic_association_sha256"],
            )
            with patch.object(
                PROJECTION,
                "_current_base_parent_items",
                return_value=items,
            ):
                artifact, error = PROJECTION.build_component_projection_artifact(
                    paper=PAPER,
                    raw_audit=raw,
                    base_sidecar=core,
                    base_sidecar_relative_path="audit/source_record_component_parent_core.json",
                    paper_dir=paper_dir,
                )
        self.assertEqual(error, "")
        self.assertIsNotNone(artifact)
        assert artifact is not None
        self.assertEqual(len(artifact["component_projections"]), 2)

    def test_parent_core_rejects_extra_or_changed_parent_content(self) -> None:
        raw = raw_audit()
        with tempfile.TemporaryDirectory() as directory:
            paper_dir = self._paper_dir(Path(directory))
            core = self._materialized_parent_core(raw, paper_dir)
            core_path = PROJECTION.component_parent_core_artifact_path(paper_dir)
            tampered = copy.deepcopy(core)
            items = tampered["items"]
            assert isinstance(items, dict)
            items["not-a-current-parent"] = reviewer_parent_response()
            self.assertIn(
                "exactly the current raw parents",
                PROJECTION.component_parent_core_validation_error(
                    tampered,
                    raw,
                    paper=PAPER,
                    paper_dir=paper_dir,
                    sidecar_path=core_path,
                ),
            )

            changed = copy.deepcopy(core)
            changed_items = changed["items"]
            assert isinstance(changed_items, dict)
            response = changed_items["semantic-model::opaque-generated-address"]
            assert isinstance(response, dict)
            dimensions = response["semantic_model_dimensions"]
            assert isinstance(dimensions, dict)
            expanded = dimensions["expanded_binders_and_domain"]
            assert isinstance(expanded, dict)
            expanded["semantic_comparison"] = "Changed after the core receipt."
            self.assertIn(
                "response ledger is stale",
                PROJECTION.component_parent_core_validation_error(
                    changed,
                    raw,
                    paper=PAPER,
                    paper_dir=paper_dir,
                    sidecar_path=core_path,
                ),
            )

    def test_parent_core_projects_raw_source_scoped_analysis_pins(self) -> None:
        """Nested source-analysis credentials are raw-derived, never reviewed text."""

        raw_member = {
            "kind": "semantic_model_comparison",
            "dimensions": [
                {
                    "id": "source_equality_partition",
                    "source_equality_partition_association": {
                        "semantic_association_sha256": digest("e")
                    },
                },
                # The production raw surface currently exercises equality
                # partition. This deliberately unfamiliar schema-shaped pair
                # proves the projector does not enumerate known analysis
                # names such as equality/composition/conditioning.
                {
                    "id": "future_source_scoped_dimension",
                    "future_source_scope_association": {
                        "semantic_association_sha256": digest("f")
                    },
                },
            ],
        }
        reviewer_response = {
            "semantic_model_dimensions": {
                "source_equality_partition": {
                    "source_equality_partition_analysis": {
                        "relation": "feature_equality_iff_class_equality"
                    }
                },
                "future_source_scoped_dimension": {
                    "future_source_scope_analysis": {"review": "present"}
                },
            }
        }
        projected, error = PROJECTION._project_source_scoped_analysis_pins(
            [("semantic_model_items", raw_member)],
            reviewer_response,
            reject_existing=True,
        )
        self.assertEqual(error, "")
        assert isinstance(projected, dict)
        dimensions = projected["semantic_model_dimensions"]
        assert isinstance(dimensions, dict)
        partition = dimensions["source_equality_partition"]
        assert isinstance(partition, dict)
        analysis = partition["source_equality_partition_analysis"]
        assert isinstance(analysis, dict)
        self.assertEqual(analysis["semantic_association_sha256"], digest("e"))
        future = dimensions["future_source_scoped_dimension"]
        assert isinstance(future, dict)
        future_analysis = future["future_source_scope_analysis"]
        assert isinstance(future_analysis, dict)
        self.assertEqual(future_analysis["semantic_association_sha256"], digest("f"))

        forged = copy.deepcopy(reviewer_response)
        forged_dimensions = forged["semantic_model_dimensions"]
        assert isinstance(forged_dimensions, dict)
        forged_partition = forged_dimensions["source_equality_partition"]
        assert isinstance(forged_partition, dict)
        forged_analysis = forged_partition["source_equality_partition_analysis"]
        assert isinstance(forged_analysis, dict)
        forged_analysis["semantic_association_sha256"] = digest("e")
        _forged_projected, forged_error = (
            PROJECTION._project_source_scoped_analysis_pins(
                [("semantic_model_items", raw_member)],
                forged,
                reject_existing=True,
            )
        )
        self.assertIn("reviewer response supplies", forged_error)

    def test_cli_writes_non_evidence_parent_core_template(self) -> None:
        raw = raw_audit()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            paper_dir = self._paper_dir(root)
            raw_path = paper_dir / "audit" / "source_record_audit.json"
            raw_path.write_text(
                json.dumps(raw, indent=2, sort_keys=True) + "\n", encoding="utf-8"
            )
            template_path = paper_dir / "audit" / "parent-core-template.json"
            with (
                patch.object(
                    sys,
                    "argv",
                    [
                        "source_record_component_projection.py",
                        "--root",
                        str(root),
                        "--paper",
                        PAPER,
                        "--write-parent-core-template",
                        str(template_path),
                    ],
                ),
                contextlib.redirect_stdout(io.StringIO()),
                contextlib.redirect_stderr(io.StringIO()),
            ):
                self.assertEqual(PROJECTION.main(), 0)
            written = json.loads(template_path.read_text(encoding="utf-8"))
            self.assertTrue(written["non_evidence_scaffold"])
            self.assertTrue(written["must_not_be_written_to_repository_sidecar"])
            self.assertEqual(len(written["parent_core_groups"]), 1)

    def test_cli_materializes_parent_core_only_with_explicit_output_write(self) -> None:
        raw = raw_audit()
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            paper_dir = self._paper_dir(root)
            raw_path = paper_dir / "audit" / "source_record_audit.json"
            raw_path.write_text(
                json.dumps(raw, indent=2, sort_keys=True) + "\n", encoding="utf-8"
            )
            template_path = paper_dir / "audit" / "completed-parent-core.json"
            template_path.write_text(
                json.dumps(
                    self._completed_parent_core_template(raw),
                    indent=2,
                    sort_keys=True,
                )
                + "\n",
                encoding="utf-8",
            )
            output_path = PROJECTION.component_parent_core_artifact_path(paper_dir)
            common_args = [
                "source_record_component_projection.py",
                "--root",
                str(root),
                "--paper",
                PAPER,
                "--completed-parent-core-template",
                str(template_path),
                "--out",
                str(output_path),
            ]
            with (
                patch.object(sys, "argv", common_args),
                contextlib.redirect_stdout(io.StringIO()),
                contextlib.redirect_stderr(io.StringIO()),
            ):
                self.assertEqual(PROJECTION.main(), 1)
            self.assertFalse(output_path.exists())
            with (
                patch.object(sys, "argv", [*common_args, "--write"]),
                contextlib.redirect_stdout(io.StringIO()),
                contextlib.redirect_stderr(io.StringIO()),
            ):
                self.assertEqual(PROJECTION.main(), 0)
            core = json.loads(output_path.read_text(encoding="utf-8"))
            self.assertEqual(
                PROJECTION.component_parent_core_validation_error(
                    core,
                    raw,
                    paper=PAPER,
                    paper_dir=paper_dir,
                    sidecar_path=output_path,
                ),
                "",
            )

    def test_projects_only_exact_semantic_parent_components_without_names(self) -> None:
        raw = raw_audit()
        candidates, error = PROJECTION.raw_component_projection_candidates(raw, paper=PAPER)
        self.assertEqual(error, "")
        self.assertEqual(len(candidates), 2)
        self.assertEqual(
            {candidate.structural_record["projection_kind"] for candidate in candidates},
            {
                PROJECTION.SOURCE_RECORD_COMPONENT_PROJECTION_DATA_KIND,
                PROJECTION.SOURCE_RECORD_COMPONENT_PROJECTION_RESULT_KIND,
            },
        )
        with tempfile.TemporaryDirectory() as directory:
            paper_dir = self._paper_dir(Path(directory))
            artifact = self._artifact(raw, paper_dir, parent_response())
        serialized = json.dumps(artifact, sort_keys=True)
        self.assertNotIn("unrelated-storage-address-data", serialized)
        self.assertNotIn("unrelated-storage-address-result", serialized)
        self.assertNotIn("semantic-model::opaque-generated-address", serialized)
        records = artifact["component_projections"]
        assert isinstance(records, list)
        self.assertTrue(
            all(
                "parent_response_semantic_sha256" in record
                and "child_component_occurrence_sha256" in record
                for record in records
                if isinstance(record, dict)
            )
        )

    def test_reissued_parent_metadata_keeps_semantic_digest_but_semantic_change_fails(self) -> None:
        raw = raw_audit()
        with tempfile.TemporaryDirectory() as directory:
            paper_dir = self._paper_dir(Path(directory))
            base_path = paper_dir / "audit" / "base.json"
            base_path.write_text("{}\n", encoding="utf-8")
            original = parent_response()
            artifact = self._artifact(raw, paper_dir, original)
            receipt_path = PROJECTION.component_projection_artifact_path(paper_dir)
            receipt_path.write_text(json.dumps(artifact), encoding="utf-8")
            parent_key = _parent_semantic_item()["judgment_key"]
            assert isinstance(parent_key, str)
            reissued = parent_response(
                validator="different reviewer", timestamp="2026-08-15T00:00:00Z"
            )
            self.assertEqual(
                PROJECTION.parent_response_semantic_sha256(original),
                PROJECTION.parent_response_semantic_sha256(reissued),
            )
            with patch.object(
                PROJECTION,
                "_current_base_parent_items",
                return_value={parent_key: reissued},
            ):
                loaded = PROJECTION.load_current_source_record_component_projection_items(
                    paper_dir, PAPER, raw
                )
            self.assertEqual(len(loaded), 2)
            self.assertTrue(
                all(
                    PROJECTION.is_loaded_source_record_component_projection_item(item)
                    for item in loaded.values()
                )
            )
            changed = copy.deepcopy(reissued)
            dimensions = changed["semantic_model_dimensions"]
            assert isinstance(dimensions, dict)
            expanded = dimensions["expanded_binders_and_domain"]
            assert isinstance(expanded, dict)
            expanded["semantic_comparison"] = "A materially different comparison."
            with patch.object(
                PROJECTION,
                "_current_base_parent_items",
                return_value={parent_key: changed},
            ):
                self.assertEqual(
                    PROJECTION.load_current_source_record_component_projection_items(
                        paper_dir, PAPER, raw
                    ),
                    {},
                )

    def test_tampered_structural_record_and_incomplete_parent_fail_closed(self) -> None:
        raw = raw_audit()
        with tempfile.TemporaryDirectory() as directory:
            paper_dir = self._paper_dir(Path(directory))
            (paper_dir / "audit" / "base.json").write_text("{}\n", encoding="utf-8")
            artifact = self._artifact(raw, paper_dir, parent_response())
            records = artifact["component_projections"]
            assert isinstance(records, list) and records and isinstance(records[0], dict)
            records[0]["child_component_occurrence"]["traversal_slot"] = 99  # type: ignore[index]
            body = {
                key: value
                for key, value in artifact.items()
                if key != PROJECTION.SOURCE_RECORD_COMPONENT_PROJECTION_RECEIPT_FIELD
            }
            artifact[PROJECTION.SOURCE_RECORD_COMPONENT_PROJECTION_RECEIPT_FIELD] = (
                PROJECTION._canonical_digest(body)
            )
            PROJECTION.component_projection_artifact_path(paper_dir).write_text(
                json.dumps(artifact), encoding="utf-8"
            )
            parent_key = _parent_semantic_item()["judgment_key"]
            assert isinstance(parent_key, str)
            with patch.object(
                PROJECTION,
                "_current_base_parent_items",
                return_value={parent_key: parent_response()},
            ):
                self.assertEqual(
                    PROJECTION.load_current_source_record_component_projection_items(
                        paper_dir, PAPER, raw
                    ),
                    {},
                )

            valid = self._artifact(raw, paper_dir, parent_response())
            PROJECTION.component_projection_artifact_path(paper_dir).write_text(
                json.dumps(valid), encoding="utf-8"
            )
            incomplete = parent_response()
            incomplete["semantic_model_dimensions"] = {}
            with patch.object(
                PROJECTION,
                "_current_base_parent_items",
                return_value={parent_key: incomplete},
            ):
                self.assertEqual(
                    PROJECTION.load_current_source_record_component_projection_items(
                        paper_dir, PAPER, raw
                    ),
                    {},
                )

    def test_frozen_inputs_use_the_current_base_once_and_never_reread_live_files(
        self,
    ) -> None:
        raw = raw_audit()
        with tempfile.TemporaryDirectory() as directory:
            paper_dir = self._paper_dir(Path(directory))
            base_path = paper_dir / "audit" / "base.json"
            base_path.write_text('{"live": "before"}\n', encoding="utf-8")
            response = parent_response()
            artifact = self._artifact(raw, paper_dir, response)
            receipt_path = PROJECTION.component_projection_artifact_path(paper_dir)
            receipt_path.write_text(json.dumps(artifact), encoding="utf-8")
            frozen = PROJECTION.ComponentProjectionFrozenInputs(
                artifact_path=receipt_path,
                artifact_present=True,
                artifact_payload=copy.deepcopy(artifact),
                base_sidecar_path=base_path,
                base_sidecar_payload={"frozen": "base"},
            )
            # Neither replacement is permitted to influence a frozen run.
            receipt_path.write_text('{"malformed": true}\n', encoding="utf-8")
            base_path.write_text('{"live": "after"}\n', encoding="utf-8")
            parent_key = _parent_semantic_item()["judgment_key"]
            assert isinstance(parent_key, str)
            with patch.object(PROJECTION, "_current_base_parent_items") as replay:
                loaded = PROJECTION.load_current_source_record_component_projection_items(
                    paper_dir,
                    PAPER,
                    raw,
                    frozen_inputs=frozen,
                    base_parent_items={parent_key: response},
                    base_parent_sidecar_path=base_path,
                    expected_paper_statement_map_sha256=digest("8"),
                )
            replay.assert_not_called()
            self.assertEqual(len(loaded), 2)

            mismatched = PROJECTION.ComponentProjectionFrozenInputs(
                artifact_path=receipt_path,
                artifact_present=True,
                artifact_payload=copy.deepcopy(artifact),
                base_sidecar_path=paper_dir / "audit" / "other.json",
                base_sidecar_payload={"frozen": "wrong-path"},
            )
            self.assertEqual(
                PROJECTION.load_current_source_record_component_projection_items(
                    paper_dir,
                    PAPER,
                    raw,
                    frozen_inputs=mismatched,
                    base_parent_items={parent_key: response},
                    base_parent_sidecar_path=base_path,
                ),
                {},
            )

    def test_only_loader_issued_projection_items_reach_the_evidence_materializer(
        self,
    ) -> None:
        raw = raw_audit()
        candidates, error = PROJECTION.raw_component_projection_candidates(raw, paper=PAPER)
        self.assertEqual(error, "")
        candidate = next(
            item
            for item in candidates
            if item.structural_record["projection_kind"]
            == PROJECTION.SOURCE_RECORD_COMPONENT_PROJECTION_DATA_KIND
        )
        record = copy.deepcopy(candidate.structural_record)
        response = parent_response()
        record["parent_response_semantic_sha256"] = (
            PROJECTION.parent_response_semantic_sha256(response)
        )
        projected = PROJECTION._projected_child_response(
            parent_response=response,
            candidate=candidate,
            record=record,
            raw_audit=raw,
        )
        payload = {"schema": 1, "paper": PAPER, "items": {candidate.child_key: projected}}
        admitted = EVIDENCE._current_source_record_judgment_items_from_payload(
            raw,
            payload,
            allow_component_projection=True,
            prevalidated_source_record_identity_error="",
        )
        self.assertEqual(set(admitted), {candidate.child_key})
        self.assertEqual(
            EVIDENCE._current_source_record_judgment_items_from_payload(
                raw,
                payload,
                allow_component_projection=False,
                prevalidated_source_record_identity_error="",
            ),
            {},
        )
        forged_payload = {
            "schema": 1,
            "paper": PAPER,
            "items": {candidate.child_key: dict(projected)},
        }
        self.assertEqual(
            EVIDENCE._current_source_record_judgment_items_from_payload(
                raw,
                forged_payload,
                allow_component_projection=True,
                prevalidated_source_record_identity_error="",
            ),
            {},
        )

    def test_proof_bearing_or_non_direct_children_never_become_candidates(self) -> None:
        raw = raw_audit(include_result=False)
        child = raw["theorem_facing_input_items"][0]  # type: ignore[index]
        assert isinstance(child, dict)
        child["proposition_sort"] = "true"
        stamp_source_record_audit_receipts(raw)
        candidates, error = PROJECTION.raw_component_projection_candidates(raw, paper=PAPER)
        self.assertEqual(error, "")
        self.assertEqual(candidates, [])

        raw = raw_audit(include_result=True)
        result = raw["type_valued_certificate_result_items"][0]  # type: ignore[index]
        assert isinstance(result, dict)
        result.pop("source_contract_association")
        stamp_source_record_audit_receipts(raw)
        candidates, error = PROJECTION.raw_component_projection_candidates(raw, paper=PAPER)
        self.assertEqual(error, "")
        self.assertEqual(len(candidates), 1)
        self.assertEqual(
            candidates[0].structural_record["projection_kind"],
            PROJECTION.SOURCE_RECORD_COMPONENT_PROJECTION_DATA_KIND,
        )

    def test_nested_base_replay_forwards_the_neutral_identity_context(self) -> None:
        """A component receipt must not launch a second current-identity scan."""

        context = object()
        calls: list[dict[str, object]] = []

        def current_items(*_args: object, **kwargs: object) -> dict[str, object]:
            calls.append(dict(kwargs))
            return {}

        fake_evidence = SimpleNamespace(
            current_paper_statement_map_sha256=lambda _paper_dir: "a" * 64,
            current_source_record_judgment_items=current_items,
        )
        with patch.object(PROJECTION, "_evidence_module", return_value=fake_evidence):
            self.assertEqual(
                PROJECTION._current_base_parent_items(
                    raw_audit={"paper": PAPER},
                    base_sidecar={"items": {}},
                    paper_dir=Path("/paper"),
                    expected_paper_statement_map_sha256="a" * 64,
                    source_record_identity_context=context,
                ),
                {},
            )
        self.assertEqual(len(calls), 1)
        self.assertIs(calls[0]["source_record_identity_context"], context)
        self.assertFalse(calls[0]["allow_component_projection"])


if __name__ == "__main__":
    unittest.main()
