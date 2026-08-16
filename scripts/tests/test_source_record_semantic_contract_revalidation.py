#!/usr/bin/env python3
"""Focused fail-closed tests for semantic-contract receipt revalidation."""

from __future__ import annotations

import copy
import json
import sys
import unittest
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts import source_record_semantic_contract_revalidation as REVALIDATION  # noqa: E402
from scripts import audit_evidence_integrity as EVIDENCE  # noqa: E402
from scripts.source_coverage_scope import (  # noqa: E402
    source_record_source_item_record_sha256,
    source_record_source_item_semantic_sha256,
)


PAPER = "FixturePaper"


def digest(character: str) -> str:
    return character * 64


def encoded(payload: object) -> bytes:
    return json.dumps(
        payload, ensure_ascii=True, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")


def identity(qualified: str, declaration_digest: str) -> dict[str, str]:
    return {
        "qualified_declaration": qualified,
        "declaration_sha256": declaration_digest,
    }


def signature(
    qualified: str, signature_digest: str, dependency_digest: str
) -> dict[str, str]:
    return {
        "qualified_declaration": qualified,
        "elaborated_signature_sha256": signature_digest,
        "semantic_dependency_sha256": dependency_digest,
    }


def association_signature(qualified: str, signature_digest: str) -> dict[str, str]:
    return {
        "qualified_declaration": qualified,
        "elaborated_signature_sha256": signature_digest,
    }


def sealed_artifact(
    raw: dict[str, object],
    raw_bytes: bytes,
    statement_map_bytes: bytes,
    *,
    witnesses: list[dict[str, object]],
) -> tuple[dict[str, object], bytes]:
    artifact: dict[str, object] = {
        "schema": REVALIDATION.SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_SCHEMA,
        "artifact_kind": (
            REVALIDATION.SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_ARTIFACT_KIND
        ),
        "policy_version": (
            REVALIDATION.SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_POLICY_VERSION
        ),
        "paper": PAPER,
        "source_record_audit_file_sha256": REVALIDATION._bytes_sha256(raw_bytes),
        "source_record_audit_sha256": raw["source_record_audit_sha256"],
        "source_record_audit_integrity_sha256": raw[
            "source_record_audit_integrity_sha256"
        ],
        "paper_statement_map_file_sha256": REVALIDATION._bytes_sha256(
            statement_map_bytes
        ),
        "paper_statement_map_sha256": raw["paper_statement_map_sha256"],
        "transparent_spec_pair_witnesses": witnesses,
    }
    artifact[REVALIDATION.SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_RECEIPT_FIELD] = (
        REVALIDATION._canonical_json_sha256(artifact)
    )
    return artifact, encoded(artifact)


def group_fixture(*, malformed_member: bool = False) -> tuple[
    dict[str, object], bytes, dict[str, object], bytes, dict[str, object], bytes
]:
    """Return a minimal raw grouped-association false rejection and receipt."""

    evidence = "Fixture.Direct"
    spec = "Fixture.Transparent"
    key = "fixture-transparent-input"
    map_item = pair_map_item(evidence, spec)
    statement_map = {"items": {"fixture_source": map_item}}
    source_identity: dict[str, object] = {
        "source_key": "fixture_source",
        "source_map_item_sha256": source_record_source_item_record_sha256(map_item),
        "source_semantic_sha256": source_record_source_item_semantic_sha256(
            map_item, "named_theory"
        ),
        "semantic_contract": copy.deepcopy(map_item["semantic_contract"]),
    }
    source_semantic_sha256 = str(source_identity["source_semantic_sha256"])
    direct_identity = identity(evidence, digest("1"))
    spec_identity = identity(spec, digest("2"))
    direct_signature = signature(evidence, digest("3"), digest("4"))
    spec_signature = signature(spec, digest("5"), digest("6"))
    direct_association: dict[str, object] = {
        "schema": 2,
        "role": "direct_evidence",
        "paired_qualified_declaration": spec,
        "reviewed_declaration_identity": direct_identity,
        "reviewed_elaborated_signature_identity": association_signature(
            evidence, digest("3")
        ),
        "source_item_identities": [source_identity],
    }
    direct_association["semantic_association_sha256"] = (
        REVALIDATION.semantic_association_record_digest(
            [source_semantic_sha256],
            direct_association["reviewed_elaborated_signature_identity"],
        )
    )
    member_association: dict[str, object] = {
        "schema": 2,
        "association_mode": "semantic_contract_group_member",
        "semantic_contract_member_role": (
            "direct_evidence" if malformed_member else "transparent_spec"
        ),
        "semantic_model_judgment_key": "semantic-parent",
        "reviewed_declaration_identity": spec_identity,
        "reviewed_elaborated_signature_identity": association_signature(
            spec, digest("5")
        ),
        "source_item_identities": [source_identity],
    }
    member_association["semantic_association_sha256"] = (
        REVALIDATION.semantic_association_record_digest(
            [source_semantic_sha256],
            member_association["reviewed_elaborated_signature_identity"],
        )
    )
    member_association["association_sha256"] = (
        REVALIDATION.source_contract_association_record_digest(member_association)
    )
    alpha_surface = {"alpha_normalized_result": "P", "binder_domains": []}
    parent = {
        "judgment_key": "semantic-parent",
        "qualified_declaration": evidence,
        "reviewed_declaration_identity": direct_identity,
        "reviewed_elaborated_signature_identities": [direct_signature],
        "semantic_contract_group": {
            "schema": 1,
            "structural_alpha_normalized_equal": True,
            "member_rows": [
                {
                    "qualified_declaration": evidence,
                    "reviewed_declaration_identity": direct_identity,
                    "role": "direct_evidence",
                },
                {
                    "qualified_declaration": spec,
                    "reviewed_declaration_identity": spec_identity,
                    "role": "transparent_spec",
                },
            ],
            "direct_evidence_type": {
                "qualified_declaration": evidence,
                "structural_alpha_normalized_surface": alpha_surface,
            },
            "surface_root": {
                "kind": "transparent_spec_body",
                "qualified_declaration": spec,
                "structural_alpha_normalized_surface": alpha_surface,
            },
            "source_item_identities": [source_identity],
        },
        "semantic_contract_source_association": direct_association,
    }
    member = {
        "source_judgment_key": key,
        "reviewed_declaration_identity": spec_identity,
        "reviewed_elaborated_signature_identities": [spec_signature],
        "source_contract_association": member_association,
    }
    statement_map_bytes = encoded(statement_map)
    raw: dict[str, object] = {
        "paper": PAPER,
        "source_record_audit_sha256": digest("7"),
        "source_record_audit_integrity_sha256": digest("8"),
        "paper_statement_map_sha256": REVALIDATION._bytes_sha256(statement_map_bytes),
        "source_contract_association_errors": [
            REVALIDATION._GROUP_MEMBER_ERROR_TEMPLATE.format(key=key)
        ],
        "source_coverage_route_errors": [],
        "semantic_model_items": [parent],
        "theorem_facing_input_items": [member],
        "type_valued_certificate_result_items": [],
        "boundary_input_items": [],
        "conclusion_dependency_items": [],
    }
    raw_bytes = encoded(raw)
    artifact, artifact_bytes = sealed_artifact(
        raw, raw_bytes, statement_map_bytes, witnesses=[]
    )
    return raw, raw_bytes, statement_map, statement_map_bytes, artifact, artifact_bytes


def pair_map_item(evidence: str, spec: str) -> dict[str, object]:
    return {
        "statement": "Fixture theorem",
        "source_location": "source.txt:1-2",
        "source_kind": "theorem",
        "coverage_status": "covered",
        "claim_bearing": True,
        "semantic_contract": {
            "evidence_declaration": evidence,
            "spec_declaration": spec,
            "evidence_mode": "proves",
            "semantic_shape": "plain",
        },
    }


def semantic_association(
    *,
    role: str,
    qualified: str,
    paired: str,
    declaration_identity: dict[str, str],
    signature_identity: dict[str, str],
    source_identity: dict[str, object],
) -> dict[str, object]:
    result: dict[str, object] = {
        "schema": 2,
        "role": role,
        "paired_qualified_declaration": paired,
        "reviewed_declaration_identity": declaration_identity,
        "reviewed_elaborated_signature_identity": signature_identity,
        "source_item_identities": [source_identity],
    }
    result["semantic_association_sha256"] = (
        REVALIDATION.semantic_association_record_digest(
            [str(source_identity["source_semantic_sha256"])], signature_identity
        )
    )
    return result


def graph(*, result_kind: str, result_sha: str, expanded_sha: str | None = None) -> dict[str, object]:
    nodes: list[dict[str, object]] = [
        {"path": "result", "kind": result_kind, "semantic_sha256": result_sha}
    ]
    edges: list[dict[str, str]] = []
    if expanded_sha is not None:
        nodes.append(
            {
                "path": "result/expanded_body",
                "kind": "exists",
                "semantic_sha256": expanded_sha,
            }
        )
        edges.append(
            {
                "source": "result",
                "target": "result/expanded_body",
                "role": "expanded_body",
            }
        )
    return {"complete": True, "nodes": nodes, "edges": edges, "failures": []}


def manifest(
    *,
    declaration_kind: str,
    conclusion_mode: str,
    signature_digest: str,
    dependency_digest: str,
    proposition_graph: dict[str, object],
    transparent_graph: dict[str, object] | None,
) -> dict[str, object]:
    return {
        "schema": 2,
        "declaration_kind": declaration_kind,
        "conclusion_mode": conclusion_mode,
        "sha256": signature_digest,
        "atoms": [
            {
                "ref": "b/0",
                "role": "parameter",
                "binder_info": "explicit",
                "canonical": "Nat",
            },
            {"ref": "result", "role": "conclusion", "canonical": "Prop"},
        ],
        "semantic_dependency_graph": {
            "semantic_dependency_sha256": dependency_digest
        },
        "semantic_dependency_manifest": {
            "semantic_dependency_sha256": dependency_digest
        },
        "elaborated_proposition_graph": proposition_graph,
        "elaborated_transparent_result_value_graph": transparent_graph,
    }


def authority_for(
    manifests: dict[str, dict[str, object]],
    signatures: dict[str, str],
    dependencies: dict[str, str],
) -> dict[str, object]:
    context_projection = {
        "import_module": "Fixture.Interface",
        "semantic_dependency_modules": ["Fixture.Interface"],
        "manifest_cache_context_sha256": digest("e"),
    }
    context = {
        **context_projection,
        "context_id": REVALIDATION._canonical_json_sha256(context_projection),
    }
    entries: list[dict[str, object]] = []
    for index, qualified in enumerate(sorted(manifests)):
        manifest_payload = manifests[qualified]
        entries.append(
            {
                "qualified_declaration": qualified,
                "context_id": context["context_id"],
                "elaborated_signature_sha256": signatures[qualified],
                "semantic_dependency_sha256": dependencies[qualified],
                "elaborated_proposition_graph_sha256": (
                    REVALIDATION.elaborated_proposition_graph_sha256(
                        manifest_payload["elaborated_proposition_graph"]
                    )
                ),
                "manifest_payload_sha256": REVALIDATION._canonical_json_sha256(
                    manifest_payload
                ),
                "authority_binding_sha256": digest("f" if index == 0 else "9"),
            }
        )
    authority: dict[str, object] = {
        "schema": REVALIDATION.AUTHENTICATED_MANIFEST_AUTHORITY_SCHEMA,
        "paper": PAPER,
        "contexts": [context],
        "entries": entries,
    }
    authority["contexts_sha256"] = REVALIDATION._canonical_json_sha256(
        authority["contexts"]
    )
    authority["entries_sha256"] = REVALIDATION._canonical_json_sha256(
        entries
    )
    return authority


def pair_fixture() -> tuple[
    dict[str, object],
    bytes,
    dict[str, object],
    bytes,
    dict[str, object],
    bytes,
    dict[str, object],
]:
    """Return a fully structural direct/transparent-Spec companion fixture."""

    evidence = "Fixture.DirectTheorem"
    spec = "Fixture.TransparentProposition"
    direct_declaration = identity(evidence, digest("1"))
    spec_declaration = identity(spec, digest("2"))
    direct_signature = signature(evidence, digest("3"), digest("4"))
    spec_signature = signature(spec, digest("5"), digest("6"))
    direct_signature_association = association_signature(evidence, digest("3"))
    spec_signature_association = association_signature(spec, digest("5"))
    map_item = pair_map_item(evidence, spec)
    statement_map = {"items": {"fixture_source": map_item}}
    source_identity: dict[str, object] = {
        "source_key": "fixture_source",
        "source_map_item_sha256": source_record_source_item_record_sha256(map_item),
        "source_semantic_sha256": source_record_source_item_semantic_sha256(
            map_item, "named_theory"
        ),
        "semantic_contract": copy.deepcopy(map_item["semantic_contract"]),
    }
    shared_root = digest("7")
    direct_graph = graph(
        result_kind="transparent_wrapper",
        result_sha=digest("8"),
        expanded_sha=shared_root,
    )
    spec_proposition_graph = graph(result_kind="exists", result_sha=digest("9"))
    spec_transparent_graph = graph(result_kind="exists", result_sha=shared_root)
    direct_manifest = manifest(
        declaration_kind="theorem",
        conclusion_mode="type_only",
        signature_digest=digest("3"),
        dependency_digest=digest("4"),
        proposition_graph=direct_graph,
        transparent_graph=None,
    )
    spec_manifest = manifest(
        declaration_kind="definition",
        conclusion_mode="type_and_value",
        signature_digest=digest("5"),
        dependency_digest=digest("6"),
        proposition_graph=spec_proposition_graph,
        transparent_graph=spec_transparent_graph,
    )
    direct_association = semantic_association(
        role="direct_evidence",
        qualified=evidence,
        paired=spec,
        declaration_identity=direct_declaration,
        signature_identity=direct_signature_association,
        source_identity=source_identity,
    )
    spec_association = semantic_association(
        role="transparent_spec",
        qualified=spec,
        paired=evidence,
        declaration_identity=spec_declaration,
        signature_identity=spec_signature_association,
        source_identity=source_identity,
    )
    statement_map_bytes = encoded(statement_map)
    companion_error = REVALIDATION._companion_error(evidence, spec)
    raw: dict[str, object] = {
        "paper": PAPER,
        "source_record_audit_sha256": digest("a"),
        "source_record_audit_integrity_sha256": digest("b"),
        "paper_statement_map_sha256": REVALIDATION._bytes_sha256(statement_map_bytes),
        "source_contract_association_errors": [companion_error],
        "source_coverage_route_errors": [companion_error],
        "semantic_model_items": [
            {
                "judgment_key": "direct-semantic",
                "qualified_declaration": evidence,
                "reviewed_declaration_identity": direct_declaration,
                "reviewed_elaborated_signature_identities": [direct_signature],
                "semantic_contract_group": None,
                "semantic_contract_source_association": direct_association,
            },
            {
                "judgment_key": "spec-semantic",
                "qualified_declaration": spec,
                "reviewed_declaration_identity": spec_declaration,
                "reviewed_elaborated_signature_identities": [spec_signature],
                "semantic_contract_group": None,
                "semantic_contract_source_association": spec_association,
            },
        ],
        "configured_review_rows": [
            {
                "qualified_declaration": evidence,
                "elaborated_signature_sha256": digest("3"),
                "semantic_dependency_sha256": digest("4"),
                "elaborated_proposition_graph_sha256": (
                    REVALIDATION.elaborated_proposition_graph_sha256(direct_graph)
                ),
            },
            {
                "qualified_declaration": spec,
                "elaborated_signature_sha256": digest("5"),
                "semantic_dependency_sha256": digest("6"),
                "elaborated_proposition_graph_sha256": (
                    REVALIDATION.elaborated_proposition_graph_sha256(
                        spec_proposition_graph
                    )
                ),
            },
        ],
        "theorem_facing_input_items": [],
        "type_valued_certificate_result_items": [],
        "boundary_input_items": [],
        "conclusion_dependency_items": [],
    }
    raw_bytes = encoded(raw)
    witness = {
        "evidence_declaration": evidence,
        "spec_declaration": spec,
        "evidence_manifest": direct_manifest,
        "spec_manifest": spec_manifest,
    }
    artifact, artifact_bytes = sealed_artifact(
        raw, raw_bytes, statement_map_bytes, witnesses=[witness]
    )
    authority = authority_for(
        {evidence: direct_manifest, spec: spec_manifest},
        {evidence: digest("3"), spec: digest("5")},
        {evidence: digest("4"), spec: digest("6")},
    )
    return (
        raw,
        raw_bytes,
        statement_map,
        statement_map_bytes,
        artifact,
        artifact_bytes,
        authority,
    )


class SemanticContractRevalidationTests(unittest.TestCase):
    def projection(
        self,
        raw: dict[str, object],
        raw_bytes: bytes,
        statement_map: dict[str, object],
        statement_map_bytes: bytes,
        artifact: dict[str, object] | None,
        artifact_bytes: bytes | None,
        authority: dict[str, object] | None = None,
    ) -> tuple[REVALIDATION.SemanticContractRevalidationProjection, str]:
        return REVALIDATION.semantic_contract_revalidation_projection(
            paper_dir=ROOT / "papers" / PAPER,
            paper=PAPER,
            raw_audit=raw,
            raw_audit_raw_bytes=raw_bytes,
            statement_map_payload=statement_map,
            statement_map_raw_bytes=statement_map_bytes,
            artifact_payload=artifact,
            artifact_raw_bytes=artifact_bytes,
            authority_payload=authority,
            authority_raw_bytes=encoded(authority) if authority is not None else None,
        )

    def test_missing_artifact_grants_no_group_credit(self) -> None:
        raw, raw_bytes, statement_map, map_bytes, _artifact, _artifact_bytes = (
            group_fixture()
        )

        projection, error = self.projection(
            raw, raw_bytes, statement_map, map_bytes, None, None
        )

        self.assertEqual(error, "")
        self.assertFalse(projection.suppressed_expected_input_keys)
        self.assertEqual(
            REVALIDATION.effective_source_record_semantic_errors(raw, projection)[
                "source_contract_association_errors"
            ],
            raw["source_contract_association_errors"],
        )

    def test_manually_constructed_projection_cannot_suppress_association_error(
        self,
    ) -> None:
        raw, _raw_bytes, _statement_map, _map_bytes, _artifact, _artifact_bytes = (
            group_fixture()
        )
        expected_error = REVALIDATION._GROUP_MEMBER_ERROR_TEMPLATE.format(
            key="fixture-transparent-input"
        )
        forged = REVALIDATION.SemanticContractRevalidationProjection(
            suppressed_source_contract_association_errors=frozenset({expected_error}),
            suppressed_source_coverage_route_errors=frozenset(),
            suppressed_expected_input_keys=frozenset({"fixture-transparent-input"}),
        )

        self.assertFalse(hasattr(REVALIDATION, "_issued_projection"))
        self.assertFalse(hasattr(REVALIDATION, "_empty_projection"))
        self.assertFalse(hasattr(REVALIDATION, "_VALIDATOR_ISSUED_PROJECTIONS"))
        self.assertFalse(
            hasattr(REVALIDATION, "_make_semantic_contract_revalidation_api")
        )
        self.assertFalse(REVALIDATION.projection_is_authenticated(forged))
        self.assertEqual(
            REVALIDATION.effective_source_record_semantic_errors(raw, forged)[
                "source_contract_association_errors"
            ],
            raw["source_contract_association_errors"],
        )

    def test_forged_projection_cannot_change_consumer_required_keys(self) -> None:
        """The evidence consumer accepts only validator-minted projections."""

        raw, _raw_bytes, _statement_map, _map_bytes, _artifact, _artifact_bytes = (
            group_fixture()
        )
        key = "fixture-transparent-input"
        expected_error = REVALIDATION._GROUP_MEMBER_ERROR_TEMPLATE.format(key=key)
        raw["expected_input_judgment_keys"] = [key]
        raw["expected_field_judgment_keys"] = ["fixture-field"]
        raw["expected_semantic_model_judgment_keys"] = ["fixture-semantic"]
        forged = REVALIDATION.SemanticContractRevalidationProjection(
            suppressed_source_contract_association_errors=frozenset({expected_error}),
            suppressed_source_coverage_route_errors=frozenset(),
            suppressed_expected_input_keys=frozenset({key}),
        )

        baseline = EVIDENCE.source_record_required_keys(raw)
        with_forged_projection = EVIDENCE.source_record_required_keys(
            raw,
            semantic_contract_revalidation=forged,
        )

        self.assertFalse(REVALIDATION.projection_is_authenticated(forged))
        self.assertEqual(
            baseline,
            ["fixture-field", "fixture-semantic", "fixture-transparent-input"],
        )
        self.assertEqual(with_forged_projection, baseline)

    def test_group_projection_accepts_only_exact_structural_member(self) -> None:
        raw, raw_bytes, statement_map, map_bytes, artifact, artifact_bytes = (
            group_fixture()
        )

        projection, error = self.projection(
            raw, raw_bytes, statement_map, map_bytes, artifact, artifact_bytes
        )

        key = "fixture-transparent-input"
        expected_error = REVALIDATION._GROUP_MEMBER_ERROR_TEMPLATE.format(key=key)
        self.assertEqual(error, "")
        self.assertEqual(projection.suppressed_expected_input_keys, frozenset({key}))
        self.assertEqual(
            projection.suppressed_source_contract_association_errors,
            frozenset({expected_error}),
        )
        self.assertTrue(REVALIDATION.projection_is_authenticated(projection))
        equivalent_forged = REVALIDATION.SemanticContractRevalidationProjection(
            suppressed_source_contract_association_errors=(
                projection.suppressed_source_contract_association_errors
            ),
            suppressed_source_coverage_route_errors=(
                projection.suppressed_source_coverage_route_errors
            ),
            suppressed_expected_input_keys=projection.suppressed_expected_input_keys,
        )
        self.assertFalse(REVALIDATION.projection_is_authenticated(equivalent_forged))

        (
            malformed_raw,
            malformed_raw_bytes,
            malformed_map,
            malformed_map_bytes,
            malformed_artifact,
            malformed_artifact_bytes,
        ) = group_fixture(malformed_member=True)
        rejected, rejected_error = self.projection(
            malformed_raw,
            malformed_raw_bytes,
            malformed_map,
            malformed_map_bytes,
            malformed_artifact,
            malformed_artifact_bytes,
        )
        self.assertIn("no exact current raw correction", rejected_error)
        self.assertFalse(rejected.suppressed_expected_input_keys)

    def test_group_projection_rejects_current_map_identity_drift(self) -> None:
        """Group repair binds its source identity to the exact current map item."""

        raw, _raw_bytes, statement_map, _map_bytes, _artifact, _artifact_bytes = (
            group_fixture()
        )
        drifted_map = copy.deepcopy(statement_map)
        items = drifted_map["items"]
        self.assertIsInstance(items, dict)
        source_item = items["fixture_source"]
        self.assertIsInstance(source_item, dict)
        source_item["statement"] = "Changed fixture theorem"
        drifted_map_bytes = encoded(drifted_map)
        raw["paper_statement_map_sha256"] = REVALIDATION._bytes_sha256(
            drifted_map_bytes
        )
        raw_bytes = encoded(raw)
        artifact, artifact_bytes = sealed_artifact(
            raw, raw_bytes, drifted_map_bytes, witnesses=[]
        )

        projection, error = self.projection(
            raw,
            raw_bytes,
            drifted_map,
            drifted_map_bytes,
            artifact,
            artifact_bytes,
        )

        self.assertIn("no exact current raw correction", error)
        self.assertFalse(projection.suppressed_source_contract_association_errors)
        self.assertFalse(projection.suppressed_expected_input_keys)

    def test_group_member_shared_with_boundary_or_conclusion_keeps_input_obligation(
        self,
    ) -> None:
        """A valid group clears only its false association diagnostic."""

        key = "fixture-transparent-input"
        expected_error = REVALIDATION._GROUP_MEMBER_ERROR_TEMPLATE.format(key=key)
        for field in ("boundary_input_items", "conclusion_dependency_items"):
            with self.subTest(field=field):
                (
                    raw,
                    _raw_bytes,
                    statement_map,
                    map_bytes,
                    _artifact,
                    _artifact_bytes,
                ) = group_fixture()
                raw[field] = [
                    copy.deepcopy(raw["theorem_facing_input_items"][0])
                ]
                raw_bytes = encoded(raw)
                artifact, artifact_bytes = sealed_artifact(
                    raw, raw_bytes, map_bytes, witnesses=[]
                )

                projection, error = self.projection(
                    raw,
                    raw_bytes,
                    statement_map,
                    map_bytes,
                    artifact,
                    artifact_bytes,
                )

                self.assertEqual(error, "")
                self.assertFalse(projection.suppressed_expected_input_keys)
                self.assertEqual(
                    projection.suppressed_source_contract_association_errors,
                    frozenset({expected_error}),
                )
                self.assertEqual(
                    REVALIDATION.effective_source_record_semantic_errors(raw, projection)[
                        "source_contract_association_errors"
                    ],
                    [],
                )

    def test_malformed_shared_boundary_occurrence_keeps_association_error(self) -> None:
        """A same-key boundary row needs its own valid group association."""

        key = "fixture-transparent-input"
        expected_error = REVALIDATION._GROUP_MEMBER_ERROR_TEMPLATE.format(key=key)
        (
            raw,
            _raw_bytes,
            statement_map,
            map_bytes,
            _artifact,
            _artifact_bytes,
        ) = group_fixture()
        raw["boundary_input_items"] = [{"source_judgment_key": key}]
        raw_bytes = encoded(raw)
        artifact, artifact_bytes = sealed_artifact(
            raw, raw_bytes, map_bytes, witnesses=[]
        )

        projection, error = self.projection(
            raw,
            raw_bytes,
            statement_map,
            map_bytes,
            artifact,
            artifact_bytes,
        )

        self.assertIn("no exact current raw correction", error)
        self.assertFalse(projection.suppressed_expected_input_keys)
        self.assertFalse(projection.suppressed_source_contract_association_errors)
        self.assertEqual(
            REVALIDATION.effective_source_record_semantic_errors(raw, projection)[
                "source_contract_association_errors"
            ],
            [expected_error],
        )

    def test_raw_and_map_snapshot_drift_fail_closed(self) -> None:
        raw, raw_bytes, statement_map, map_bytes, artifact, artifact_bytes = (
            group_fixture()
        )

        _projection, raw_error = self.projection(
            raw,
            raw_bytes + b" ",
            statement_map,
            map_bytes,
            artifact,
            artifact_bytes,
        )
        self.assertIn("stale source-record audit bytes", raw_error)

        _projection, map_error = self.projection(
            raw,
            raw_bytes,
            statement_map,
            map_bytes + b" ",
            artifact,
            artifact_bytes,
        )
        self.assertIn("does not bind the supplied paper-statement-map bytes", map_error)

    def test_transparent_pair_root_mutation_is_rejected(self) -> None:
        (
            raw,
            raw_bytes,
            statement_map,
            map_bytes,
            artifact,
            artifact_bytes,
            authority,
        ) = pair_fixture()

        with patch.object(
            REVALIDATION,
            "signature_manifest_digest",
            side_effect=lambda manifest: str(manifest.get("sha256") or ""),
        ):
            accepted, accepted_error = self.projection(
                raw,
                raw_bytes,
                statement_map,
                map_bytes,
                artifact,
                artifact_bytes,
                authority,
            )
            self.assertEqual(accepted_error, "")
            self.assertTrue(accepted.suppressed_source_contract_association_errors)
            self.assertTrue(accepted.suppressed_source_coverage_route_errors)

            mutated_artifact = copy.deepcopy(artifact)
            witnesses = mutated_artifact["transparent_spec_pair_witnesses"]
            self.assertIsInstance(witnesses, list)
            mutated_spec = witnesses[0]["spec_manifest"]
            self.assertIsInstance(mutated_spec, dict)
            transparent_graph = mutated_spec[
                "elaborated_transparent_result_value_graph"
            ]
            self.assertIsInstance(transparent_graph, dict)
            nodes = transparent_graph["nodes"]
            self.assertIsInstance(nodes, list)
            nodes[0]["semantic_sha256"] = digest("c")
            evidence = str(witnesses[0]["evidence_declaration"])
            spec = str(witnesses[0]["spec_declaration"])
            mutated_authority = authority_for(
                {
                    evidence: witnesses[0]["evidence_manifest"],
                    spec: mutated_spec,
                },
                {evidence: digest("3"), spec: digest("5")},
                {evidence: digest("4"), spec: digest("6")},
            )
            mutated_artifact[
                REVALIDATION.SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_RECEIPT_FIELD
            ] = REVALIDATION._canonical_json_sha256(
                {
                    key: value
                    for key, value in mutated_artifact.items()
                    if key
                    != REVALIDATION.SOURCE_RECORD_SEMANTIC_CONTRACT_REVALIDATION_RECEIPT_FIELD
                }
            )
            rejected, rejected_error = self.projection(
                raw,
                raw_bytes,
                statement_map,
                map_bytes,
                mutated_artifact,
                encoded(mutated_artifact),
                mutated_authority,
            )

        self.assertIn("invalid or duplicate pair witness", rejected_error)
        self.assertFalse(rejected.suppressed_source_contract_association_errors)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
