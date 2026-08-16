#!/usr/bin/env python3
"""Focused tests for historical serializer statement-receipt transport."""

from __future__ import annotations

import copy
import hashlib
import json
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    text = str(import_root)
    if text not in sys.path:
        sys.path.insert(0, text)

from scripts import historical_statement_manifest_replay as REPLAY  # noqa: E402
from scripts import lean_signature_manifest as MANIFEST  # noqa: E402
from scripts import review_dashboard  # noqa: E402
from scripts.tests.test_statement_obligation_ledger import (  # noqa: E402
    refresh_manifest_digest,
    valid_ledger,
    valid_manifest,
)


PAPER = "FixturePaper"


def sha(seed: str) -> str:
    return hashlib.sha256(seed.encode("utf-8")).hexdigest()


def canonical_json_sha256(value: object) -> str:
    return hashlib.sha256(
        json.dumps(value, ensure_ascii=True, sort_keys=True, separators=(",", ":")).encode(
            "utf-8"
        )
    ).hexdigest()


def current_manifest(
    *, result: str = "P", dependency_body: str = "stable imported body"
) -> dict[str, object]:
    """Return a complete modern manifest with current closure evidence."""

    value: dict[str, object] = {
        "schema": 2,
        "declaration_kind": "theorem",
        "conclusion_mode": "type_only",
        "atoms": [
            {
                "ref": "new/0",
                "role": "assumption",
                "binder_info": "explicit",
                "canonical": {
                    "tag": "app",
                    "fn": {"tag": "const", "name": "LT.lt", "levels": []},
                    "arg": {"tag": "lit", "value": "0"},
                },
                "display": "0 < x",
            },
            {
                "ref": "result",
                "role": "conclusion",
                "canonical": {"tag": "proposition", "name": result},
                "display": result,
            },
        ],
        "semantic_dependency_graph": {
            "schema": 1,
            "root_declaration": "Fixture.currentNavigation",
            "complete": True,
            "nodes": [
                {
                    "declaration": "Fixture.currentNavigation",
                    "module_origin": "Fixture.Interface",
                    "origin_class": "review_closure",
                    "declaration_kind": "theorem",
                    "canonical_identity": {
                        "tag": "local_theorem",
                        "type": {"tag": "proposition", "name": result},
                    },
                },
                {
                    "declaration": "Fixture.importedNavigation",
                    "module_origin": "Fixture.ImportedModel",
                    "origin_class": "review_closure",
                    "declaration_kind": "definition",
                    "canonical_identity": {
                        "tag": "inlined_definition",
                        "type": {"tag": "sort", "level": {"tag": "zero"}},
                        "value": {"tag": "literal", "value": dependency_body},
                    },
                },
            ],
            "edges": [
                {
                    "source": "Fixture.currentNavigation",
                    "target": "Fixture.importedNavigation",
                    "role": "type_dependency",
                }
            ],
            "failures": [],
        },
        "elaborated_proposition_graph": {
            "schema": 1,
            "complete": True,
            "nodes": [
                {
                    "path": "result",
                    "kind": "constant",
                    "canonical": {"tag": "proposition", "name": result},
                }
            ],
            "edges": [],
            "failures": [],
        },
    }
    normalized = MANIFEST.normalize_signature_manifest(value)
    assert normalized is not None
    normalized["semantic_dependency_module_identities"] = []
    normalized["semantic_dependency_environment_identities"] = [
        {"path": "lean-toolchain", "sha256": sha("lean toolchain")},
        {"path": "lake-manifest.json", "sha256": sha("lake manifest")},
    ]
    dependency = MANIFEST.semantic_dependency_manifest(normalized)
    assert dependency is not None
    normalized["semantic_dependency_manifest"] = dependency
    return normalized


def historic_manifest(*, extra_assumption: bool = False) -> dict[str, object]:
    """Return the old serializer's common outer interface projection."""

    manifest = copy.deepcopy(valid_manifest())
    atoms = manifest["atoms"]
    assert isinstance(atoms, list)
    conclusion = atoms[-1]
    assert isinstance(conclusion, dict)
    # The normal transport fixture is semantically unchanged across the two
    # serializer versions; only its binder ref changes below.
    conclusion["canonical"] = {"tag": "proposition", "name": "P"}
    if extra_assumption:
        atoms.insert(
            1,
            {
                "ref": "b/extra",
                "role": "assumption",
                "binder_info": "explicit",
                "canonical": {"tag": "proposition", "name": "Extra"},
                "display": "Extra x",
            },
        )
    manifest["sha256"] = MANIFEST.signature_manifest_digest(manifest)
    return manifest


def historical_semantic_store(
    historical_outer: dict[str, object],
    *,
    dependency_body: str = "stable imported body",
) -> tuple[dict[str, object], bytes, dict[str, object], bytes]:
    """Build exact authenticated historic closure inputs without output names."""

    # The carrier is a historical complete manifest, while the old serializer
    # fixture supplies only its shared outer-interface projection.  Its graph
    # is deliberately independent from the current target passed to a test so
    # hidden dependency changes cannot be masked by rebuilding this fixture.
    manifest = current_manifest(dependency_body=dependency_body)
    manifest["declaration_kind"] = historical_outer["declaration_kind"]
    manifest["conclusion_mode"] = historical_outer["conclusion_mode"]
    manifest["atoms"] = copy.deepcopy(historical_outer["atoms"])
    manifest["sha256"] = MANIFEST.signature_manifest_digest(manifest)
    assert manifest["sha256"] == historical_outer["sha256"]
    dependency = MANIFEST.semantic_dependency_manifest(manifest)
    assert isinstance(dependency, dict)
    proposition_graph = manifest["elaborated_proposition_graph"]
    assert isinstance(proposition_graph, dict)
    context = {
        "import_module": "Fixture.HistoricalSnapshot",
        "semantic_dependency_modules": ["Fixture.HistoricalSnapshot"],
        "manifest_cache_context_sha256": sha("historic cache context"),
    }
    context["context_id"] = canonical_json_sha256(context)
    qualified = "Fixture.HistoricalSnapshot.route"
    authority_entry = {
        "qualified_declaration": qualified,
        "context_id": context["context_id"],
        "elaborated_signature_sha256": manifest["sha256"],
        "semantic_dependency_sha256": dependency["semantic_dependency_sha256"],
        "elaborated_proposition_graph_sha256": canonical_json_sha256(
            proposition_graph
        ),
        "manifest_payload_sha256": canonical_json_sha256(manifest),
        "authority_binding_sha256": sha("historic authority binding"),
    }
    authority = {
        "schema": 1,
        "paper": PAPER,
        "contexts": [context],
        "contexts_sha256": canonical_json_sha256([context]),
        "entries": [authority_entry],
        "entries_sha256": canonical_json_sha256([authority_entry]),
    }
    carrier = {
        "schema": 1,
        "paper": PAPER,
        "entries": [
            {
                "qualified_declaration": qualified,
                "context_id": context["context_id"],
                "manifest": manifest,
            }
        ],
    }
    carrier_bytes = (json.dumps(carrier, sort_keys=True) + "\n").encode("utf-8")
    authority_bytes = (json.dumps(authority, sort_keys=True) + "\n").encode("utf-8")
    return carrier, carrier_bytes, authority, authority_bytes


def target(
    manifest: dict[str, object],
    *,
    paper_statement: str = "The endpoint holds.",
    translation: str = "The endpoint holds.",
    navigation: str = "Fixture.currentNavigation",
) -> dict[str, object]:
    return {
        "lean_signature_sha256": str(manifest["sha256"]),
        "paper_statement_sha256": review_dashboard.statement_digest(paper_statement),
        "tex_statement_sha256": review_dashboard.statement_digest(translation),
        "lean_signature_manifest": manifest,
        "source_route_sha256": sha("source route " + paper_statement),
        # The transport module must neither inspect nor serialize this.
        "declaration": navigation,
    }


def recipe() -> dict[str, object]:
    return {
        "schema": REPLAY.HISTORICAL_SERIALIZER_RECIPE_SCHEMA,
        "artifact_kind": REPLAY.HISTORICAL_SERIALIZER_RECIPE_ARTIFACT_KIND,
        "policy_version": REPLAY.HISTORICAL_SERIALIZER_RECIPE_POLICY_VERSION,
        "historical_git_commit": "a" * 40,
        "historical_serializer_blob": {
            "git_object_id": "b" * 40,
            "bytes_sha256": sha("old serializer"),
        },
        "historical_helper_blob": {
            "git_object_id": "c" * 40,
            "bytes_sha256": sha("old helper"),
        },
        "current_execution_inputs": {
            "paper_interface_bytes_sha256": sha("current paper interface"),
            "lean_toolchain_bytes_sha256": sha("lean toolchain"),
            "lake_manifest_bytes_sha256": sha("lake manifest"),
            "lean_import_closure_sha256": sha("current Lean import closure"),
        },
        "runner_identity_sha256": sha("fixture historical runner"),
    }


def prior_sidecar(
    historical: dict[str, object],
    current: dict[str, object],
    *,
    navigation: str = "old_sidecar_navigation",
) -> tuple[dict[str, object], bytes]:
    ledger = valid_ledger()
    refresh_manifest_digest(ledger, historical)
    entry = {
        **ledger,
        "paper_statement_sha256": current["paper_statement_sha256"],
        "tex_statement_sha256": current["tex_statement_sha256"],
        "validator": "fixture reviewer",
        "validator_type": "agent",
        "validated_at": "2026-08-14T00:00:00Z",
    }
    sidecar: dict[str, object] = {
        "schema": 1,
        "paper": PAPER,
        "items": {navigation: entry},
    }
    return sidecar, (json.dumps(sidecar, sort_keys=True) + "\n").encode("utf-8")


def historic_runner(
    historical_by_current_signature: dict[str, dict[str, object]],
):
    """Return a test-injected runner that never emits navigation fields."""

    def run(
        supplied_recipe: dict[str, object], current_targets: list[dict[str, object]]
    ) -> dict[str, object]:
        observations: list[dict[str, object]] = []
        for current in current_targets:
            signature = str(current["lean_signature_sha256"])
            historical = historical_by_current_signature[signature]
            evidence, error = REPLAY._current_manifest_evidence(
                current["lean_signature_manifest"]
            )
            assert not error
            observations.append(
                {
                    "current_target_identity": REPLAY.current_target_identity(current),
                    "historical_manifest_signature_sha256": historical["sha256"],
                    "historical_manifest": historical,
                    **evidence,
                }
            )
        return {
            "historical_serializer_recipe_sha256": REPLAY.historical_serializer_recipe_sha256(
                supplied_recipe
            ),
            "verified_historical_git_blobs": {
                "historical_git_commit": supplied_recipe["historical_git_commit"],
                "historical_serializer_blob": supplied_recipe[
                    "historical_serializer_blob"
                ],
                "historical_helper_blob": supplied_recipe["historical_helper_blob"],
            },
            "current_execution_inputs": supplied_recipe["current_execution_inputs"],
            "observations": observations,
        }

    return run


def target_validator(raw: dict[str, object]) -> str:
    return "" if raw.get("live_target") != "rejected" else "target is not live"


def source_route_validator(raw: dict[str, object]) -> str:
    return "" if raw.get("live_route") != "rejected" else "source route is stale"


def blob_verifier(raw: dict[str, object]) -> str:
    return "" if raw.get("historical_git_commit") != "bad" else "Git blob bytes do not match pin"


class HistoricalStatementManifestReplayTests(unittest.TestCase):
    def build_fixture(self) -> tuple[
        dict[str, object],
        bytes,
        dict[str, object],
        dict[str, object],
        object,
    ]:
        current = target(current_manifest())
        historical = historic_manifest()
        sidecar, sidecar_bytes = prior_sidecar(historical, current)
        runner = historic_runner({str(current["lean_signature_sha256"]): historical})
        return sidecar, sidecar_bytes, current, historical, runner

    def historic_store_inputs(
        self, historical: dict[str, object]
    ) -> dict[str, object]:
        carrier, carrier_bytes, authority, authority_bytes = historical_semantic_store(
            historical
        )
        return {
            "historical_manifest_carrier": carrier,
            "historical_manifest_carrier_bytes": carrier_bytes,
            "historical_manifest_authority": authority,
            "historical_manifest_authority_bytes": authority_bytes,
        }

    def build(
        self,
        *,
        current: dict[str, object],
        sidecar: dict[str, object],
        sidecar_bytes: bytes,
        runner: object,
        historical: dict[str, object] | None = None,
        historic_store: dict[str, object] | None = None,
    ):
        inputs = historic_store or self.historic_store_inputs(
            historical or historic_manifest()
        )
        return REPLAY.build_historical_statement_manifest_replay(
            paper=PAPER,
            historical_serializer_recipe=recipe(),
            prior_sidecar=sidecar,
            prior_sidecar_bytes=sidecar_bytes,
            **inputs,
            current_targets=[current],
            current_evidence_sha256=sha("current cache/source-map receipt"),
            historical_manifest_runner=runner,
            historical_blob_verifier=blob_verifier,
            current_target_validator=target_validator,
            source_route_validator=source_route_validator,
        )

    def static_validate(
        self,
        receipt: dict[str, object],
        *,
        current: dict[str, object],
        sidecar: dict[str, object],
        sidecar_bytes: bytes,
        historical: dict[str, object] | None = None,
        historic_store: dict[str, object] | None = None,
    ):
        inputs = historic_store or self.historic_store_inputs(
            historical or historic_manifest()
        )
        return REPLAY.validate_historical_statement_manifest_replay_static(
            receipt,
            paper=PAPER,
            historical_serializer_recipe=recipe(),
            prior_sidecar=sidecar,
            prior_sidecar_bytes=sidecar_bytes,
            **inputs,
            current_targets=[current],
            current_evidence_sha256=sha("current cache/source-map receipt"),
            current_target_validator=target_validator,
            source_route_validator=source_route_validator,
        )

    def test_exact_replay_validates_ledger_and_has_name_free_identity(self) -> None:
        sidecar, sidecar_bytes, current, historical, runner = self.build_fixture()
        receipt, error = self.build(
            current=current,
            sidecar=sidecar,
            sidecar_bytes=sidecar_bytes,
            runner=runner,
            historical=historical,
        )
        self.assertEqual(error, "")
        assert receipt is not None
        self.assertEqual(len(receipt["bindings"]), 1)
        binding = receipt["bindings"][0]
        self.assertEqual(binding["historical_manifest_signature_sha256"], historical["sha256"])
        self.assertEqual(
            [(row["historical_signature_ref"], row["current_signature_ref"])
             for row in binding["atom_transport"]],
            [("b/0", "new/0"), ("result", "result")],
        )
        rendered = json.dumps(receipt, sort_keys=True)
        self.assertNotIn("old_sidecar_navigation", rendered)
        self.assertNotIn("Fixture.currentNavigation", rendered)
        context, validation_error = self.static_validate(
            receipt,
            current=current,
            sidecar=sidecar,
            sidecar_bytes=sidecar_bytes,
            historical=historical,
        )
        self.assertEqual(validation_error, "")
        assert context is not None
        payload = receipt["bindings"][0]["prior_entry_payload_sha256"]
        self.assertIsNotNone(
            REPLAY.replay_binding_for_current_target(
                context,
                prior_entry_payload_sha256=payload,
                current_identity=current,
            )
        )

    def test_navigation_renames_do_not_change_receipt(self) -> None:
        sidecar, sidecar_bytes, current, historical, runner = self.build_fixture()
        first, first_error = self.build(
            current=current,
            sidecar=sidecar,
            sidecar_bytes=sidecar_bytes,
            runner=runner,
            historical=historical,
        )
        renamed_current = copy.deepcopy(current)
        renamed_current["declaration"] = "Other.renamedNavigation"
        renamed_sidecar, renamed_bytes = prior_sidecar(
            historical, renamed_current, navigation="different_storage_key"
        )
        renamed_runner = historic_runner(
            {str(renamed_current["lean_signature_sha256"]): historical}
        )
        second, second_error = self.build(
            current=renamed_current,
            sidecar=renamed_sidecar,
            sidecar_bytes=renamed_bytes,
            runner=renamed_runner,
            historical=historical,
        )
        self.assertEqual((first_error, second_error), ("", ""))
        assert first is not None and second is not None
        # Exact sidecar bytes are independently pinned, so a storage-key edit
        # changes the outer artifact. Its content-paired transport binding does
        # not change and contains neither navigation spelling.
        self.assertNotEqual(first["prior_sidecar_bytes_sha256"], second["prior_sidecar_bytes_sha256"])
        self.assertEqual(first["bindings"], second["bindings"])

    def test_added_historical_binder_cannot_match_archived_receipt(self) -> None:
        sidecar, sidecar_bytes, current, _historical, _runner = self.build_fixture()
        changed_historical = historic_manifest(extra_assumption=True)
        runner = historic_runner(
            {str(current["lean_signature_sha256"]): changed_historical}
        )
        receipt, error = self.build(
            current=current,
            sidecar=sidecar,
            sidecar_bytes=sidecar_bytes,
            runner=runner,
            historical=changed_historical,
        )
        self.assertEqual(error, "")
        assert receipt is not None
        self.assertEqual(receipt["bindings"], [])
        self.assertEqual(len(receipt["unbridged_prior_entry_payload_sha256"]), 1)

    def test_same_role_p_to_q_change_cannot_transport(self) -> None:
        """Role/arity equality is not semantic equality of an atom slot."""

        sidecar, sidecar_bytes, _current, historical, _runner = self.build_fixture()
        changed_current = target(current_manifest(result="Q"))
        runner = historic_runner(
            {str(changed_current["lean_signature_sha256"]): historical}
        )
        receipt, error = self.build(
            current=changed_current,
            sidecar=sidecar,
            sidecar_bytes=sidecar_bytes,
            runner=runner,
            historical=historical,
        )
        self.assertIsNone(receipt)
        self.assertIn("canonical forms differ", error)

    def test_full_archived_ledger_is_required(self) -> None:
        sidecar, sidecar_bytes, current, historical, runner = self.build_fixture()
        item = sidecar["items"]["old_sidecar_navigation"]
        assert isinstance(item, dict)
        obligations = item["lean_obligations"]
        assert isinstance(obligations, list)
        obligations[0]["signature_ref"] = "unknown"
        sidecar_bytes = (json.dumps(sidecar, sort_keys=True) + "\n").encode("utf-8")
        receipt, error = self.build(
            current=current,
            sidecar=sidecar,
            sidecar_bytes=sidecar_bytes,
            runner=runner,
            historical=historical,
        )
        self.assertIsNone(receipt)
        self.assertIn("semantic obligation ledger", error)

    def test_ambiguous_content_pairing_is_rejected(self) -> None:
        sidecar, sidecar_bytes, current, historical, _runner = self.build_fixture()
        second = target(
            current_manifest(result="Q"),
            navigation="Fixture.otherNavigation",
        )
        # Keep the source/translation target identical and make both current
        # declarations replay the same old serializer signature.
        second["paper_statement_sha256"] = current["paper_statement_sha256"]
        second["tex_statement_sha256"] = current["tex_statement_sha256"]
        runner = historic_runner(
            {
                str(current["lean_signature_sha256"]): historical,
                str(second["lean_signature_sha256"]): historical,
            }
        )
        receipt, error = REPLAY.build_historical_statement_manifest_replay(
            paper=PAPER,
            historical_serializer_recipe=recipe(),
            prior_sidecar=sidecar,
            prior_sidecar_bytes=sidecar_bytes,
            **self.historic_store_inputs(historical),
            current_targets=[current, second],
            current_evidence_sha256=sha("current cache/source-map receipt"),
            historical_manifest_runner=runner,
            historical_blob_verifier=blob_verifier,
            current_target_validator=target_validator,
            source_route_validator=source_route_validator,
        )
        self.assertIsNone(receipt)
        self.assertIn("ambiguous", error)

    def test_static_validation_does_not_invoke_runner_and_strong_validation_does(self) -> None:
        sidecar, sidecar_bytes, current, historical, runner = self.build_fixture()
        historic_store = self.historic_store_inputs(historical)
        receipt, error = self.build(
            current=current,
            sidecar=sidecar,
            sidecar_bytes=sidecar_bytes,
            runner=runner,
        )
        self.assertEqual(error, "")
        assert receipt is not None

        # The static validator has no runner argument, so a materializer cannot
        # accidentally trigger a second historical Lean process.
        context, static_error = self.static_validate(
            receipt,
            current=current,
            sidecar=sidecar,
            sidecar_bytes=sidecar_bytes,
        )
        self.assertEqual(static_error, "")
        self.assertIsNotNone(context)
        # The strong path is explicit and therefore may invoke the runner.
        strong_context, strong_error = REPLAY.validate_historical_statement_manifest_replay_replay(
            receipt,
            paper=PAPER,
            historical_serializer_recipe=recipe(),
            prior_sidecar=sidecar,
            prior_sidecar_bytes=sidecar_bytes,
            **historic_store,
            current_targets=[current],
            current_evidence_sha256=sha("current cache/source-map receipt"),
            historical_manifest_runner=runner,
            historical_blob_verifier=blob_verifier,
            current_target_validator=target_validator,
            source_route_validator=source_route_validator,
        )
        self.assertEqual(strong_error, "")
        self.assertIsNotNone(strong_context)

    def test_static_validation_rejects_changed_route_or_atom_transport(self) -> None:
        sidecar, sidecar_bytes, current, historical, runner = self.build_fixture()
        receipt, error = self.build(
            current=current,
            sidecar=sidecar,
            sidecar_bytes=sidecar_bytes,
            runner=runner,
            historical=historical,
        )
        self.assertEqual(error, "")
        assert receipt is not None
        changed = copy.deepcopy(current)
        changed["source_route_sha256"] = sha("changed route")
        _context, route_error = self.static_validate(
            receipt,
            current=changed,
            sidecar=sidecar,
            sidecar_bytes=sidecar_bytes,
            historical=historical,
        )
        self.assertIn("current target surface", route_error)

        callback_rejected = copy.deepcopy(current)
        callback_rejected["live_route"] = "rejected"
        _context, callback_error = self.static_validate(
            receipt,
            current=callback_rejected,
            sidecar=sidecar,
            sidecar_bytes=sidecar_bytes,
            historical=historical,
        )
        self.assertIn("source route is stale", callback_error)

        changed_identity = copy.deepcopy(current)
        changed_identity["paper_statement_sha256"] = sha("changed source target")
        _context, identity_error = self.static_validate(
            receipt,
            current=changed_identity,
            sidecar=sidecar,
            sidecar_bytes=sidecar_bytes,
            historical=historical,
        )
        self.assertIn("current target surface", identity_error)

        tampered = copy.deepcopy(receipt)
        transport = tampered["bindings"][0]["atom_transport"]
        assert isinstance(transport, list)
        transport[0]["current_signature_ref"] = "forged"
        tampered[REPLAY.HISTORICAL_STATEMENT_MANIFEST_REPLAY_INTEGRITY_FIELD] = (
            REPLAY.historical_statement_manifest_replay_digest(tampered)
        )
        _context, atom_error = self.static_validate(
            tampered,
            current=current,
            sidecar=sidecar,
            sidecar_bytes=sidecar_bytes,
            historical=historical,
        )
        self.assertIn("signature-ref transport", atom_error)

        historical_mapping_tamper = copy.deepcopy(receipt)
        historic_bindings = historical_mapping_tamper["bindings"][0][
            "historical_signature_atom_bindings"
        ]
        assert isinstance(historic_bindings, list)
        historic_bindings[0]["signature_ref"] = "forged-historic-ref"
        historical_mapping_tamper[
            REPLAY.HISTORICAL_STATEMENT_MANIFEST_REPLAY_INTEGRITY_FIELD
        ] = REPLAY.historical_statement_manifest_replay_digest(
            historical_mapping_tamper
        )
        _context, historical_atom_error = self.static_validate(
            historical_mapping_tamper,
            current=current,
            sidecar=sidecar,
            sidecar_bytes=sidecar_bytes,
        )
        self.assertIn("historical signature-ref mapping", historical_atom_error)

    def test_creation_requires_verified_recipe_blob_contract(self) -> None:
        sidecar, sidecar_bytes, current, historical, runner = self.build_fixture()

        def runner_with_forged_blob_receipt(
            supplied_recipe: dict[str, object], current_targets: list[dict[str, object]]
        ) -> dict[str, object]:
            result = runner(supplied_recipe, current_targets)
            verified = result["verified_historical_git_blobs"]
            assert isinstance(verified, dict)
            helper = verified["historical_helper_blob"]
            assert isinstance(helper, dict)
            helper["bytes_sha256"] = "0" * 64
            return result

        receipt, error = self.build(
            current=current,
            sidecar=sidecar,
            sidecar_bytes=sidecar_bytes,
            runner=runner_with_forged_blob_receipt,
            historical=historical,
        )
        self.assertIsNone(receipt)
        self.assertIn("pinned Git blobs", error)

        receipt, error = REPLAY.build_historical_statement_manifest_replay(
            paper=PAPER,
            historical_serializer_recipe=recipe(),
            prior_sidecar=sidecar,
            prior_sidecar_bytes=sidecar_bytes,
            **self.historic_store_inputs(historical),
            current_targets=[current],
            current_evidence_sha256=sha("current cache/source-map receipt"),
            historical_manifest_runner=runner,
            historical_blob_verifier=lambda _recipe: "Git object bytes differ",
            current_target_validator=target_validator,
            source_route_validator=source_route_validator,
        )
        self.assertIsNone(receipt)
        self.assertIn("Git object bytes differ", error)


if __name__ == "__main__":  # pragma: no cover
    unittest.main()
