#!/usr/bin/env python3
"""Focused fail-closed tests for v11 correspondence receipt refreshes."""

from __future__ import annotations

import copy
import hashlib
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    value = str(import_root)
    if value not in sys.path:
        sys.path.insert(0, value)

import audit_evidence_integrity as integrity  # noqa: E402
import audit_repository as repository  # noqa: E402
import refresh_source_spec_correspondence as refresh  # noqa: E402


def digest(label: str) -> str:
    return hashlib.sha256(label.encode("utf-8")).hexdigest()


def atom() -> dict[str, str]:
    return {
        "id": "source_clause",
        "source_locator": "source.txt:1",
        "source_quote_sha256": digest("Theorem. Fixture result."),
        "semantic_claim": "Every admissible input has the displayed fixture outcome.",
        "reviewed_lean_route": "Fixture.Proof",
    }


def item() -> dict[str, object]:
    return {
        "claim_bearing": True,
        "source_kind": "theorem",
        "semantic_contract": {
            "spec_declaration": "Fixture.SourceSpec",
            "evidence_declaration": "Fixture.Proof",
            "evidence_mode": "proves",
            "semantic_shape": "plain",
        },
        "source_claim_atoms": [atom()],
    }


def closure(
    *,
    closure_label: str,
    surface_label: str,
    nodes: list[dict[str, object]] | None = None,
    failures: list[dict[str, str]] | None = None,
) -> dict[str, object]:
    return {
        "sha256": digest(closure_label),
        "surface_sha256": digest(surface_label),
        "closure_module_context_sha256": digest("context-" + closure_label),
        "surface_mode": "terminal_fallback" if failures else "closure_expanded",
        "surface": {
            "binder_domains": [],
            "body": {
                "tag": "app",
                "fn": {"tag": "const", "origin": "foundation"},
                "arg": {"tag": "lit", "value": "0"},
            },
        },
        "nodes": nodes or [],
        "failures": failures or [],
    }


def correspondence(
    source_item: dict[str, object], current: dict[str, object], *, dispositions: list[dict[str, object]] | None = None) -> dict[str, object]:
    atoms = source_item["source_claim_atoms"]
    assert isinstance(atoms, list)
    atom_sha = integrity.source_claim_atom_semantic_sha256(atoms[0])
    record: dict[str, object] = {
        "schema": 1,
        "source_atoms_sha256": integrity.source_claim_atoms_semantic_sha256(atoms),
        "spec_closure_sha256": current["sha256"],
        "spec_surface_sha256": current["surface_sha256"],
        "closure_environment_sha256": current["closure_module_context_sha256"],
        "source_atom_bindings": [
            {
                "source_atom_sha256": atom_sha,
                "spec_component_sha256s": [current["surface_sha256"]],
                "semantic_bridge": "The complete canonical Spec surface represents the fixture source clause.",
            }
        ],
        "closure_node_dispositions": dispositions or [],
    }
    record["item_identity_sha256"] = integrity.source_spec_correspondence_item_identity_sha256(
        source_item["semantic_contract"], record
    )
    return record


def workspace_node(label: str) -> dict[str, object]:
    return {
        "structural_path": "body/fn",
        "node_role": "terminal",
        "origin_class": "workspace",
        "canonical_identity": {
            "tag": "declaration",
            "declaration_type_hash": digest("type-" + label),
        },
        "pinned_declaration_identity_sha256": digest("pin-" + label),
    }


def disposition_for(node: dict[str, object], source_item: dict[str, object]) -> dict[str, object]:
    atoms = source_item["source_claim_atoms"]
    assert isinstance(atoms, list)
    return {
        "closure_component_sha256": repository.semantic_contract_closure_node_component_sha256(node),
        "source_atom_sha256": integrity.source_claim_atom_semantic_sha256(atoms[0]),
        "semantic_basis": {
            "artifact_path": "source.txt",
            "artifact_sha256": digest("source artifact"),
            "source_locator": "source.txt:1",
            "semantic_statement": "The source clause explicitly supplies the fixture terminal meaning.",
        },
        "pinned_declaration_identity_sha256": node[
            "pinned_declaration_identity_sha256"
        ],
    }


class SourceSpecCorrespondenceRefreshTests(unittest.TestCase):
    def test_refresh_updates_only_derived_receipt_fields_when_mapping_survives(self) -> None:
        source_item = item()
        old = closure(closure_label="old", surface_label="same")
        current = closure(closure_label="current", surface_label="same")
        record = correspondence(source_item, old)
        # A malformed derived aggregate must be recomputed, not treated as a
        # source-mapping change when all individual atom bindings still match.
        record["source_atoms_sha256"] = digest("stale aggregate")
        record["item_identity_sha256"] = integrity.source_spec_correspondence_item_identity_sha256(
            source_item["semantic_contract"], record
        )
        source_item["source_spec_correspondence"] = record
        original = copy.deepcopy(record)

        candidate, errors = refresh.refresh_existing_correspondence(source_item, current)

        self.assertEqual(errors, [])
        assert candidate is not None
        updated = candidate.correspondence
        changed_fields = {
            key for key in set(updated) | set(original) if updated.get(key) != original.get(key)
        }
        self.assertTrue(changed_fields)
        self.assertTrue(changed_fields <= refresh.DERIVED_RECEIPT_FIELDS)
        self.assertEqual(updated["source_atom_bindings"], original["source_atom_bindings"])
        self.assertEqual(
            updated["closure_node_dispositions"], original["closure_node_dispositions"]
        )
        self.assertEqual(updated["spec_closure_sha256"], current["sha256"])
        self.assertEqual(
            updated["closure_environment_sha256"], current["closure_module_context_sha256"]
        )
        self.assertEqual(
            updated["item_identity_sha256"],
            integrity.source_spec_correspondence_item_identity_sha256(
                source_item["semantic_contract"], updated
            ),
        )
        proposed = copy.deepcopy(source_item)
        proposed["source_spec_correspondence"] = updated
        self.assertEqual(
            repository.source_spec_correspondence_runtime_errors(proposed, current), []
        )

    def test_refresh_refuses_a_changed_bound_spec_component(self) -> None:
        source_item = item()
        old = closure(closure_label="old", surface_label="old-surface")
        current = closure(closure_label="current", surface_label="new-surface")
        source_item["source_spec_correspondence"] = correspondence(source_item, old)

        candidate, errors = refresh.refresh_existing_correspondence(source_item, current)

        self.assertIsNone(candidate)
        self.assertTrue(
            any("absent from the current canonical surface" in error for error in errors),
            errors,
        )

    def test_refresh_refuses_a_changed_material_terminal_disposition(self) -> None:
        source_item = item()
        old_node = workspace_node("old")
        old = closure(
            closure_label="old",
            surface_label="same",
            nodes=[old_node],
            failures=[
                {
                    "tag": "unregistered_workspace_dependency",
                    "declaration": "Fixture.OldTerminal",
                }
            ],
        )
        current_node = workspace_node("new")
        current = closure(
            closure_label="current",
            surface_label="same",
            nodes=[current_node],
            failures=[
                {
                    "tag": "unregistered_workspace_dependency",
                    "declaration": "Fixture.NewTerminal",
                }
            ],
        )
        source_item["source_spec_correspondence"] = correspondence(
            source_item, old, dispositions=[disposition_for(old_node, source_item)]
        )

        candidate, errors = refresh.refresh_existing_correspondence(source_item, current)

        self.assertIsNone(candidate)
        self.assertTrue(
            any("material closure node" in error for error in errors), errors
        )

    def test_refresh_never_synthesizes_a_missing_correspondence_record(self) -> None:
        source_item = item()
        current = closure(closure_label="current", surface_label="same")

        candidate, errors = refresh.refresh_existing_correspondence(source_item, current)

        self.assertIsNone(candidate)
        self.assertEqual(errors, ["no established source_spec_correspondence record to refresh"])

    def test_refresh_refuses_a_changed_theorem_to_spec_relationship(self) -> None:
        source_item = item()
        old = closure(closure_label="old", surface_label="same")
        current = closure(closure_label="current", surface_label="same")
        source_item["source_spec_correspondence"] = correspondence(source_item, old)
        source_item["semantic_contract"] = dict(source_item["semantic_contract"])
        source_item["semantic_contract"]["evidence_mode"] = "refutes"

        candidate, errors = refresh.refresh_existing_correspondence(source_item, current)

        self.assertIsNone(candidate)
        self.assertTrue(
            any("changed evidence relationship" in error for error in errors), errors
        )

    def test_map_refresh_is_all_or_nothing_after_one_semantic_mapping_refusal(self) -> None:
        accepted = item()
        accepted_old = closure(closure_label="accepted-old", surface_label="shared")
        accepted_current = closure(closure_label="accepted-current", surface_label="shared")
        accepted["source_spec_correspondence"] = correspondence(accepted, accepted_old)
        rejected = item()
        rejected["semantic_contract"] = dict(rejected["semantic_contract"])
        rejected["semantic_contract"]["spec_declaration"] = "Fixture.OtherSpec"
        rejected_old = closure(closure_label="rejected-old", surface_label="old")
        rejected_current = closure(closure_label="rejected-current", surface_label="new")
        rejected["source_spec_correspondence"] = correspondence(rejected, rejected_old)
        payload: dict[str, object] = {
            "source_spec_correspondence_schema": 1,
            "items": {"accepted_navigation_key": accepted, "rejected_navigation_key": rejected},
        }

        updated, refreshed, skipped, errors = refresh.refreshed_payload(
            payload,
            {
                "Fixture.SourceSpec": accepted_current,
                "Fixture.OtherSpec": rejected_current,
            },
        )

        self.assertIsNone(updated)
        self.assertEqual(refreshed, [])
        self.assertEqual(skipped, [])
        self.assertTrue(any("rejected_navigation_key" in error for error in errors), errors)


if __name__ == "__main__":
    unittest.main()
