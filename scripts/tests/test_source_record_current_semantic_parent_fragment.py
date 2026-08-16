#!/usr/bin/env python3
"""Focused tests for aggregate-only semantic-parent review fragments."""

from __future__ import annotations

import copy
import json
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import source_record_current_semantic_parent_fragment as FRAGMENT  # noqa: E402
from scripts.source_record_integrity import stamp_source_record_audit_receipts  # noqa: E402


PAPER = "FixturePaper"
PROMPT = "source-record-v10-semantic-conclusion-boundary-contract"


def digest(char: str) -> str:
    return char * 64


def _identity(suffix: str = "one") -> tuple[dict[str, str], list[dict[str, str]]]:
    declaration = f"{PAPER}.PaperInterface.opaque_{suffix}"
    return (
        {
            "qualified_declaration": declaration,
            "declaration_sha256": digest("a" if suffix == "one" else "b"),
        },
        [
            {
                "qualified_declaration": declaration,
                "elaborated_signature_sha256": digest(
                    "c" if suffix == "one" else "d"
                ),
                "semantic_dependency_sha256": digest(
                    "e" if suffix == "one" else "f"
                ),
            }
        ],
    )


def _semantic_item(
    *,
    address: str,
    dimension: str = "expanded_binders_and_domain",
    suffix: str = "one",
) -> dict[str, object]:
    declaration, signatures = _identity(suffix)
    return {
        "judgment_key": address,
        "kind": "semantic_model_comparison",
        "reviewed_declaration_identity": declaration,
        "reviewed_elaborated_signature_identities": signatures,
        "dimensions": [
            {
                "id": dimension,
                "detected_from_expanded_surface": True,
                "requires_checked_bridge_when_detected": False,
                "requires_parameter_translation_when_detected": False,
            }
        ],
        "source_record_item_reuse_eligibility": {
            "eligible": False,
            "blockers": ["aggregate-only fixture"],
        },
    }


def raw_audit(*, second_parent: bool = False) -> dict[str, object]:
    items: list[dict[str, object]] = [
        _semantic_item(address="semantic-model::unrelated-storage-address")
    ]
    if second_parent:
        items.append(
            _semantic_item(
                address="semantic-model::second-unrelated-storage-address",
                dimension="carrier_and_domain",
                suffix="two",
            )
        )
    payload: dict[str, object] = {
        "paper": PAPER,
        "prompt_version": PROMPT,
        "source_record_policy_version": PROMPT,
        "semantic_model_items": items,
        "lean_check": {"returncode": 0},
        "recursion_failure_count": 0,
    }
    stamp_source_record_audit_receipts(payload)
    return payload


def response_for(
    candidate: object,
    *,
    verdict: str = "matches_literal_source",
) -> dict[str, object]:
    assert isinstance(candidate, FRAGMENT._Candidate)
    dimension = candidate.semantic_item["dimensions"][0]["id"]
    assert isinstance(dimension, str)
    return {
        "classification": "semantic_model_review",
        "reason": "The source definition and elaborated model were compared directly.",
        "source_location": "source.txt:10-12",
        "semantic_model_dimensions": {
            dimension: {
                "verdict": verdict,
                "source_locator": "source.txt:10-12",
                "semantic_comparison": (
                    "The reviewed source semantics agree with the generated "
                    "expanded domain contract."
                ),
                "lean_evidence": (
                    "The elaborated current Lean type was compared to the source "
                    "contract."
                ),
            }
        },
    }


def review_record(candidate: object, *, response: dict[str, object] | None = None) -> dict[str, object]:
    assert isinstance(candidate, FRAGMENT._Candidate)
    reviewed_response = response or response_for(candidate)
    return {
        "current_group_semantic_descriptor": copy.deepcopy(
            dict(candidate.group_descriptor)
        ),
        "current_group_semantic_descriptor_sha256": candidate.group_descriptor_sha256,
        "current_item_pins": [],
        "reviewer": "semantic reviewer",
        "validated_at": "2026-08-14T00:00:00Z",
        "review_notes": "Reviewed against current source and elaborated Lean surface.",
        "response": reviewed_response,
        "response_semantic_sha256": FRAGMENT.semantic_parent_response_semantic_sha256(
            reviewed_response
        ),
    }


class SourceRecordCurrentSemanticParentFragmentTests(unittest.TestCase):
    def _paper_dir(self, temporary: Path) -> Path:
        paper_dir = temporary / "papers" / PAPER
        (paper_dir / "audit").mkdir(parents=True)
        return paper_dir

    def _candidates(self, raw: dict[str, object]) -> list[FRAGMENT._Candidate]:
        candidates, error = FRAGMENT.aggregate_only_semantic_parent_candidates(
            raw, paper=PAPER
        )
        self.assertEqual(error, "")
        return candidates

    def _artifact(
        self, raw: dict[str, object], records: list[dict[str, object]]
    ) -> dict[str, object]:
        artifact, error = FRAGMENT.build_current_semantic_parent_fragment_artifact(
            paper=PAPER, raw_audit=raw, review_records=records
        )
        self.assertEqual(error, "")
        self.assertIsNotNone(artifact)
        assert artifact is not None
        return artifact

    def test_partial_fragment_matches_exact_descriptor_not_storage_address(self) -> None:
        raw = raw_audit(second_parent=True)
        first, second = self._candidates(raw)
        artifact = self._artifact(raw, [review_record(first)])
        serialized = json.dumps(artifact, sort_keys=True)
        self.assertNotIn(first.current_key, serialized)
        self.assertNotIn(second.current_key, serialized)
        with tempfile.TemporaryDirectory() as directory:
            paper_dir = self._paper_dir(Path(directory))
            receipt_path = FRAGMENT.current_semantic_parent_fragment_artifact_path(
                paper_dir
            )
            receipt_path.write_text(json.dumps(artifact), encoding="utf-8")
            loaded = FRAGMENT.load_current_source_record_current_semantic_parent_fragment_items(
                paper_dir, PAPER, raw
            )
        self.assertEqual(set(loaded), {first.current_key})
        self.assertTrue(
            FRAGMENT.is_loaded_source_record_current_semantic_parent_fragment_item(
                loaded[first.current_key]
            )
        )
        self.assertEqual(
            loaded[first.current_key]["prompt_version"], raw["prompt_version"]
        )
        self.assertNotIn(second.current_key, loaded)

    def test_complete_open_review_is_current_but_cannot_be_forged_from_transport(self) -> None:
        raw = raw_audit()
        candidate = self._candidates(raw)[0]
        open_response = response_for(candidate, verdict="mismatch_or_open")
        artifact = self._artifact(raw, [review_record(candidate, response=open_response)])
        self.assertEqual(
            FRAGMENT.semantic_parent_fragment_validation_error(
                Path("/definitely/absent"), PAPER, raw
            ),
            "",
        )
        changed = copy.deepcopy(artifact)
        record = changed["semantic_parent_reviews"][0]
        assert isinstance(record, dict)
        response = record["response"]
        assert isinstance(response, dict)
        response["source_record_audit_sha256"] = digest("f")
        record["response_semantic_sha256"] = (
            FRAGMENT.semantic_parent_response_semantic_sha256(response)
        )
        changed[FRAGMENT.SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_RECEIPT_FIELD] = (
            FRAGMENT._canonical_digest(
                {
                    key: value
                    for key, value in changed.items()
                    if key
                    != FRAGMENT.SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_RECEIPT_FIELD
                }
            )
        )
        validated, error = FRAGMENT._artifact_error(changed, paper=PAPER, raw_audit=raw)
        self.assertIsNone(validated)
        self.assertIn("generated/transport", error)

    def test_rejects_incomplete_or_non_evidence_reviewer_content(self) -> None:
        raw = raw_audit()
        candidate = self._candidates(raw)[0]
        incomplete = response_for(candidate)
        incomplete.pop("reason")
        artifact, error = FRAGMENT.build_current_semantic_parent_fragment_artifact(
            paper=PAPER,
            raw_audit=raw,
            review_records=[review_record(candidate, response=incomplete)],
        )
        self.assertIsNone(artifact)
        self.assertIn("lacks a reason", error)
        non_evidence = response_for(candidate)
        non_evidence["candidate_only"] = True
        artifact, error = FRAGMENT.build_current_semantic_parent_fragment_artifact(
            paper=PAPER,
            raw_audit=raw,
            review_records=[review_record(candidate, response=non_evidence)],
        )
        self.assertIsNone(artifact)
        self.assertIn("candidate/draft/non-evidence", error)

    def test_rejects_wrong_pins_reusable_shape_and_duplicate_descriptor(self) -> None:
        raw = raw_audit()
        candidate = self._candidates(raw)[0]
        record = review_record(candidate)
        record["current_item_pins"] = [{"not": "an aggregate-only pin"}]
        artifact, error = FRAGMENT.build_current_semantic_parent_fragment_artifact(
            paper=PAPER, raw_audit=raw, review_records=[record]
        )
        self.assertIsNone(artifact)
        self.assertIn("empty aggregate-only pin list", error)
        reusable = copy.deepcopy(dict(candidate.semantic_item))
        reusable["source_record_item_reuse_eligibility"] = {
            "eligible": True,
            "blockers": [],
        }
        self.assertIn(
            "not explicitly aggregate-only",
            FRAGMENT._aggregate_only_semantic_parent_item_error(reusable),
        )

        duplicate_raw = raw_audit()
        duplicate = copy.deepcopy(duplicate_raw["semantic_model_items"][0])
        assert isinstance(duplicate, dict)
        duplicate["judgment_key"] = "semantic-model::different-address-same-content"
        duplicate_raw["semantic_model_items"].append(duplicate)
        stamp_source_record_audit_receipts(duplicate_raw)
        candidates, duplicate_error = FRAGMENT.aggregate_only_semantic_parent_candidates(
            duplicate_raw, paper=PAPER
        )
        self.assertEqual(candidates, [])
        self.assertIn("descriptor-ambiguous", duplicate_error)

    def test_receipt_and_current_raw_mutation_fail_closed(self) -> None:
        raw = raw_audit()
        candidate = self._candidates(raw)[0]
        artifact = self._artifact(raw, [review_record(candidate)])
        with tempfile.TemporaryDirectory() as directory:
            paper_dir = self._paper_dir(Path(directory))
            receipt_path = FRAGMENT.current_semantic_parent_fragment_artifact_path(
                paper_dir
            )
            tampered = copy.deepcopy(artifact)
            record = tampered["semantic_parent_reviews"][0]
            assert isinstance(record, dict)
            response = record["response"]
            assert isinstance(response, dict)
            response["reason"] = "Different review prose."
            receipt_path.write_text(json.dumps(tampered), encoding="utf-8")
            self.assertEqual(
                FRAGMENT.load_current_source_record_current_semantic_parent_fragment_items(
                    paper_dir, PAPER, raw
                ),
                {},
            )
            receipt_path.write_text(json.dumps(artifact), encoding="utf-8")
            changed_raw = copy.deepcopy(raw)
            item = changed_raw["semantic_model_items"][0]
            assert isinstance(item, dict)
            dimensions = item["dimensions"]
            assert isinstance(dimensions, list)
            dimensions[0]["id"] = "changed_generated_dimension"
            stamp_source_record_audit_receipts(changed_raw)
            self.assertEqual(
                FRAGMENT.load_current_source_record_current_semantic_parent_fragment_items(
                    paper_dir, PAPER, changed_raw
                ),
                {},
            )

    def test_completed_fragment_and_template_are_distinct(self) -> None:
        raw = raw_audit()
        candidate = self._candidates(raw)[0]
        template, error = FRAGMENT.semantic_parent_review_fragment_template(raw, paper=PAPER)
        self.assertEqual(error, "")
        self.assertIsNotNone(template)
        assert template is not None
        artifact, error = FRAGMENT.build_current_semantic_parent_fragment_from_review_fragment(
            paper=PAPER, raw_audit=raw, review_fragment=template
        )
        self.assertIsNone(artifact)
        self.assertIn("unsupported top-level", error)
        completed = {
            "schema": FRAGMENT.SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_SCHEMA,
            "artifact_kind": (
                FRAGMENT.SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_REVIEW_FRAGMENT_KIND
            ),
            "policy_version": (
                FRAGMENT.SOURCE_RECORD_CURRENT_SEMANTIC_PARENT_FRAGMENT_POLICY_VERSION
            ),
            "paper": PAPER,
            "current_source_record_audit_sha256": raw["source_record_audit_sha256"],
            "current_source_record_audit_integrity_sha256": raw[
                "source_record_audit_integrity_sha256"
            ],
            "semantic_parent_reviews": [review_record(candidate)],
        }
        artifact, error = FRAGMENT.build_current_semantic_parent_fragment_from_review_fragment(
            paper=PAPER, raw_audit=raw, review_fragment=completed
        )
        self.assertEqual(error, "")
        self.assertIsNotNone(artifact)

    def test_frozen_inputs_never_probe_live_receipt(self) -> None:
        raw = raw_audit()
        candidate = self._candidates(raw)[0]
        artifact = self._artifact(raw, [review_record(candidate)])
        with tempfile.TemporaryDirectory() as directory:
            paper_dir = self._paper_dir(Path(directory))
            receipt_path = FRAGMENT.current_semantic_parent_fragment_artifact_path(
                paper_dir
            )
            receipt_path.write_text(json.dumps(artifact), encoding="utf-8")
            frozen_absent = FRAGMENT.CurrentSemanticParentFragmentFrozenInputs(
                artifact_path=receipt_path,
                artifact_present=False,
                artifact_payload=None,
            )
            self.assertEqual(
                FRAGMENT.load_current_source_record_current_semantic_parent_fragment_items(
                    paper_dir, PAPER, raw, frozen_inputs=frozen_absent
                ),
                {},
            )
            receipt_path.unlink()
            frozen_present = FRAGMENT.CurrentSemanticParentFragmentFrozenInputs(
                artifact_path=receipt_path,
                artifact_present=True,
                artifact_payload=artifact,
            )
            loaded = FRAGMENT.load_current_source_record_current_semantic_parent_fragment_items(
                paper_dir, PAPER, raw, frozen_inputs=frozen_present
            )
        self.assertEqual(set(loaded), {candidate.current_key})


if __name__ == "__main__":
    unittest.main()
