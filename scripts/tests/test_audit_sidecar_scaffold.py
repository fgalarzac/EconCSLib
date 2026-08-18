#!/usr/bin/env python3
"""Regression tests for blank existing-paper audit-sidecar scaffolds."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    import_root_text = str(import_root)
    if import_root_text not in sys.path:
        sys.path.insert(0, import_root_text)

import review_dashboard  # noqa: E402
import scaffold_audit_sidecars  # noqa: E402


class AuditSidecarScaffoldTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.papers = self.root / "papers"
        self.papers.mkdir()
        self.paper = self.papers / "FixturePaper"
        (self.paper / "audit").mkdir(parents=True)
        (self.paper / ".review_traces").mkdir()
        (self.paper / "PaperInterface.lean").write_text(
            "namespace FixturePaper\ntheorem unrelated_lean_row : True := by trivial\n"
            "end FixturePaper\n",
            encoding="utf-8",
        )
        (self.paper / "status.json").write_text(
            json.dumps(
                {
                    "status": "formalized",
                    "review_surface": {
                        "paper_coverage_required": True,
                    },
                }
            ),
            encoding="utf-8",
        )
        (self.paper / "audit" / "paper_statement_map.json").write_text(
            json.dumps(
                {
                    "schema": 1,
                    "paper": "FixturePaper",
                    "items": {
                        "unrelated_source_key": {
                            "statement": "A source theorem has a mathematical conclusion.",
                            "source_location": "source.txt:1",
                            "source_kind": "theorem",
                            "source_url": "https://example.test/source",
                        }
                    },
                }
            ),
            encoding="utf-8",
        )

        patches = (
            mock.patch.object(review_dashboard, "ROOT", self.root),
            mock.patch.object(review_dashboard, "PAPERS_DIR", self.papers),
            mock.patch.object(
                scaffold_audit_sidecars.review_dashboard, "ROOT", self.root
            ),
            mock.patch.object(
                scaffold_audit_sidecars.review_dashboard,
                "PAPERS_DIR",
                self.papers,
            ),
            mock.patch.object(scaffold_audit_sidecars, "ROOT", self.root),
            mock.patch.object(scaffold_audit_sidecars, "PAPERS_DIR", self.papers),
        )
        for patch in patches:
            patch.start()
            self.addCleanup(patch.stop)

        cache = {
            "schema": review_dashboard.PAPER_INTERFACE_CACHE_SCHEMA,
            "paper": "FixturePaper",
            "signature_contexts": {"PaperInterface.lean": {"schema": 1}},
            "hashes": review_dashboard._cache_source_hashes(self.paper),
            "rows": [
                {
                    "name": "unrelated_lean_row",
                    "kind": "theorem",
                    "lean_statement": "theorem unrelated_lean_row : True",
                    "paper_statement": "A paper-facing statement.",
                    "agent_statement": "A cached presentation.",
                }
            ],
        }
        (self.paper / ".review_traces" / "paper_interface_cache.json").write_text(
            json.dumps(cache), encoding="utf-8"
        )
        source_file = "papers/FixturePaper/PaperInterface.lean"
        source_sha256 = scaffold_audit_sidecars._sha256_file(
            self.paper / "PaperInterface.lean"
        )
        fresh_elaboration = {
            "mode": "isolated_temp_overlay",
            "source_file": source_file,
            "source_sha256": source_sha256,
            "returncode": 0,
        }
        self.fresh_source_record_payload = {
            "paper": "FixturePaper",
            "prompt_version": scaffold_audit_sidecars.new_paper.SOURCE_RECORD_PROMPT_VERSION,
            "source_record_policy_version": (
                scaffold_audit_sidecars.new_paper.SOURCE_RECORD_PROMPT_VERSION
            ),
            "source_record_audit_sha256": "a" * 64,
            "source_record_judgment_file": "audit/source_record_match_llm.json",
            "lean_check": {
                "returncode": 0,
                "fresh_source_elaboration": fresh_elaboration,
            },
            "fresh_source_elaboration": fresh_elaboration,
            "current_source_record_judgment_count": 0,
        }
        generator = mock.patch.object(
            scaffold_audit_sidecars,
            "_generate_fresh_source_record_audit",
            side_effect=lambda _folder: json.loads(
                json.dumps(self.fresh_source_record_payload)
            ),
        )
        generator.start()
        self.addCleanup(generator.stop)

    def sidecar(self, name: str) -> Path:
        return self.paper / "audit" / name

    def review_item(self) -> review_dashboard.ReviewItem:
        return review_dashboard.ReviewItem(
            name="unrelated_lean_row",
            kind="theorem",
            lean_statement="theorem unrelated_lean_row : True",
            paper_statement="A paper-facing statement.",
            agent_statement="A cached presentation.",
            interface_source="theorem unrelated_lean_row : True",
        )

    def write_route_configuration(
        self,
        *,
        include_names: list[str],
        auxiliary_names: list[str] | None = None,
        quarantined_auxiliary_names: list[str] | None = None,
        items: dict[str, object],
    ) -> None:
        """Replace the static route inputs and keep the fixture cache current."""

        (self.paper / "status.json").write_text(
            json.dumps(
                {
                    "status": "formalized",
                    "review_surface": {
                        "paper_coverage_required": True,
                        "include_names": include_names,
                        "auxiliary_names": auxiliary_names or [],
                        "quarantined_auxiliary_names": (
                            quarantined_auxiliary_names or []
                        ),
                    },
                }
            ),
            encoding="utf-8",
        )
        (self.paper / "audit" / "paper_statement_map.json").write_text(
            json.dumps(
                {
                    "schema": 1,
                    "paper": "FixturePaper",
                    "items": items,
                }
            ),
            encoding="utf-8",
        )
        cache_path = self.paper / ".review_traces" / "paper_interface_cache.json"
        cache = json.loads(cache_path.read_text(encoding="utf-8"))
        cache["hashes"] = review_dashboard._cache_source_hashes(self.paper)
        cache_path.write_text(json.dumps(cache), encoding="utf-8")

    def test_scaffold_is_deterministic_blank_and_fails_every_review_lane(self) -> None:
        targets = scaffold_audit_sidecars.scaffold_current_audit_sidecars("FixturePaper")
        self.assertEqual(len(targets), 6)
        before = {path.name: path.read_bytes() for path in targets}

        for name in scaffold_audit_sidecars.DASHBOARD_SIDECARS:
            payload = json.loads(self.sidecar(name).read_text(encoding="utf-8"))
            self.assertEqual(payload["items"], {})
            marker = payload["non_evidence_scaffold"]
            self.assertEqual(marker["status"], "needs_review")
            self.assertEqual(marker["input_snapshot"]["review_row_count"], 1)
            self.assertEqual(marker["input_snapshot"]["source_item_count"], 1)
            rendered = json.dumps(payload, sort_keys=True)
            self.assertNotIn("unrelated_lean_row", rendered)
            self.assertNotIn("unrelated_source_key", rendered)
            self.assertNotIn("mathematical conclusion", rendered)

        source_record_audit = json.loads(
            self.sidecar("source_record_audit.json").read_text(encoding="utf-8")
        )
        self.assertEqual(
            source_record_audit["source_record_audit_sha256"], "a" * 64
        )
        self.assertEqual(source_record_audit["lean_check"]["returncode"], 0)
        source_record_match = json.loads(
            self.sidecar("source_record_match_llm.json").read_text(encoding="utf-8")
        )
        self.assertEqual(source_record_match["items"], {})
        self.assertEqual(
            source_record_match["source_record_audit_sha256"], "a" * 64
        )
        self.assertEqual(
            source_record_match["non_evidence_scaffold"]["status"], "needs_review"
        )

        coverage = json.loads(
            self.sidecar("paper_coverage_llm.json").read_text(encoding="utf-8")
        )
        self.assertTrue(coverage["seed_scaffold"])
        self.assertFalse(coverage["source_grounded"])
        self.assertEqual(coverage["audit_kind"], "dashboard_seeded_preliminary")

        scaffold_audit_sidecars.scaffold_current_audit_sidecars(
            "FixturePaper", force=True
        )
        self.assertEqual(
            before,
            {
                name: self.sidecar(name).read_bytes()
                for name in scaffold_audit_sidecars.CANONICAL_SIDECARS
            },
        )

        row = self.review_item()
        statement_summary = review_dashboard.statement_translation_audit_summary(
            self.paper, [row]
        )
        self.assertTrue(statement_summary["needs_attention"])
        self.assertEqual(statement_summary["missing_draft"], [])
        self.assertEqual(statement_summary["missing_judgment"], [row.name])

        coverage_summary = review_dashboard.paper_coverage_audit_summary(
            self.paper, [row]
        )
        self.assertTrue(coverage_summary["audit_is_scaffold"])
        self.assertTrue(coverage_summary["missing_required"])

        surface_summary = review_dashboard.review_surface_audit_summary(
            self.paper, [row]
        )
        self.assertTrue(surface_summary["non_evidence_scaffold"])
        self.assertFalse(surface_summary["needs_attention"])

    def test_marker_blocks_later_payload_fields_until_removed(self) -> None:
        scaffold_audit_sidecars.scaffold_current_audit_sidecars("FixturePaper")
        translation_path = self.sidecar("lean_to_tex_llm.json")
        translation = json.loads(translation_path.read_text(encoding="utf-8"))
        translation["items"] = {
            "unrelated_lean_row": {
                "tex_statement": "True",
                "lean_statement_sha256": "not-evidence",
                "translator": "pretend-reviewer",
                "translated_at": "2026-07-25T00:00:00Z",
            }
        }
        translation_path.write_text(json.dumps(translation), encoding="utf-8")

        judgment_path = self.sidecar("statement_match_llm.json")
        judgment = json.loads(judgment_path.read_text(encoding="utf-8"))
        judgment["items"] = {"unrelated_lean_row": {"judgment": "matches"}}
        judgment_path.write_text(json.dumps(judgment), encoding="utf-8")

        surface_path = self.sidecar("review_surface_llm.json")
        surface = json.loads(surface_path.read_text(encoding="utf-8"))
        surface["judgment"] = "passes"
        surface_path.write_text(json.dumps(surface), encoding="utf-8")

        row = self.review_item()
        statement_summary = review_dashboard.statement_translation_audit_summary(
            self.paper, [row]
        )
        self.assertTrue(statement_summary["needs_attention"])
        self.assertEqual(statement_summary["matches"], 0)
        self.assertEqual(statement_summary["missing_draft"], [])
        self.assertEqual(statement_summary["missing_judgment"], [row.name])
        surface_summary = review_dashboard.review_surface_audit_summary(
            self.paper, [row]
        )
        self.assertFalse(surface_summary["needs_attention"])
        self.assertTrue(surface_summary["non_evidence_scaffold"])

    def test_refuses_existing_and_legacy_sidecars_and_stale_cache(self) -> None:
        existing = self.sidecar("lean_to_tex_llm.json")
        existing.write_text("original", encoding="utf-8")
        with self.assertRaisesRegex(
            scaffold_audit_sidecars.AuditScaffoldError, "already exist"
        ):
            scaffold_audit_sidecars.scaffold_current_audit_sidecars("FixturePaper")
        self.assertEqual(existing.read_text(encoding="utf-8"), "original")
        with self.assertRaisesRegex(
            scaffold_audit_sidecars.AuditScaffoldError,
            "destroy-semantic-evidence",
        ):
            scaffold_audit_sidecars.scaffold_current_audit_sidecars(
                "FixturePaper", force=True
            )
        self.assertEqual(existing.read_text(encoding="utf-8"), "original")
        scaffold_audit_sidecars.scaffold_current_audit_sidecars(
            "FixturePaper", force=True, destroy_semantic_evidence=True
        )
        self.assertNotEqual(existing.read_text(encoding="utf-8"), "original")
        existing.unlink()

        legacy = self.paper / "lean_to_tex_llm.json"
        legacy.write_text("legacy", encoding="utf-8")
        with self.assertRaisesRegex(
            scaffold_audit_sidecars.AuditScaffoldError, "legacy root-level"
        ):
            scaffold_audit_sidecars.scaffold_current_audit_sidecars("FixturePaper")
        legacy.unlink()
        for name in scaffold_audit_sidecars.CANONICAL_SIDECARS:
            self.sidecar(name).unlink(missing_ok=True)

        interface = self.paper / "PaperInterface.lean"
        interface.write_text(interface.read_text(encoding="utf-8") + "\n-- changed\n", encoding="utf-8")
        with self.assertRaisesRegex(
            scaffold_audit_sidecars.AuditScaffoldError, "cache is stale"
        ):
            scaffold_audit_sidecars.scaffold_current_audit_sidecars("FixturePaper")

    def test_creates_fresh_source_record_audit_and_blank_pinned_judgment(self) -> None:
        scaffold_audit_sidecars.scaffold_current_audit_sidecars("FixturePaper")
        self.assertTrue((self.paper / "audit" / "paper_statement_map.json").exists())
        source_record_audit = self.paper / "audit" / "source_record_audit.json"
        source_record_match = self.paper / "audit" / "source_record_match_llm.json"
        self.assertTrue(source_record_audit.exists())
        self.assertTrue(source_record_match.exists())
        audit_payload = json.loads(source_record_audit.read_text(encoding="utf-8"))
        match_payload = json.loads(source_record_match.read_text(encoding="utf-8"))
        self.assertEqual(
            match_payload["source_record_audit_sha256"],
            audit_payload["source_record_audit_sha256"],
        )
        self.assertEqual(
            audit_payload["source_record_policy_version"],
            scaffold_audit_sidecars.new_paper.SOURCE_RECORD_PROMPT_VERSION,
        )
        self.assertEqual(
            match_payload["source_record_policy_version"],
            scaffold_audit_sidecars.new_paper.SOURCE_RECORD_PROMPT_VERSION,
        )
        self.assertEqual(match_payload["items"], {})
        self.assertFalse((self.paper / "audit" / "source_proof_fidelity.json").exists())

    def test_direct_route_preflight_accepts_qualified_source_name_with_short_include(self) -> None:
        self.write_route_configuration(
            include_names=["unrelated_lean_row"],
            items={
                "source_claim": {
                    "claim_bearing": True,
                    "lean_declarations": ["FixturePaper.unrelated_lean_row"],
                }
            },
        )

        snapshot = scaffold_audit_sidecars._frozen_input_snapshot(self.paper)

        self.assertEqual(snapshot["source_item_count"], 1)

    def test_direct_route_preflight_rejects_claim_endpoint_outside_include_names(self) -> None:
        self.write_route_configuration(
            include_names=[],
            items={
                "source_claim": {
                    "claim_bearing": True,
                    "lean_declarations": ["FixturePaper.unrelated_lean_row"],
                }
            },
        )

        with self.assertRaisesRegex(
            scaffold_audit_sidecars.AuditScaffoldError,
            "is not configured in review_surface.include_names",
        ):
            scaffold_audit_sidecars._frozen_input_snapshot(self.paper)

    def test_direct_route_preflight_rejects_auxiliary_only_endpoint(self) -> None:
        self.write_route_configuration(
            include_names=[],
            auxiliary_names=["unrelated_lean_row"],
            items={
                "source_claim": {
                    "claim_bearing": True,
                    "lean_declarations": ["FixturePaper.unrelated_lean_row"],
                }
            },
        )

        with self.assertRaisesRegex(
            scaffold_audit_sidecars.AuditScaffoldError,
            "configured only as auxiliary",
        ):
            scaffold_audit_sidecars._frozen_input_snapshot(self.paper)

    def test_direct_route_preflight_rejects_semantic_contract_endpoint_outside_include(self) -> None:
        (self.paper / "PaperInterface.lean").write_text(
            """namespace FixturePaper
def claimSpec : Prop := True
theorem claimProof : claimSpec := by trivial
end FixturePaper
""",
            encoding="utf-8",
        )
        self.write_route_configuration(
            include_names=["claimProof"],
            auxiliary_names=["claimSpec"],
            items={
                "source_claim": {
                    "claim_bearing": True,
                    "lean_declarations": None,
                    "semantic_contract": {
                        "spec_declaration": "FixturePaper.claimSpec",
                        "evidence_declaration": "FixturePaper.claimProof",
                        "evidence_mode": "proves",
                        "semantic_shape": "plain",
                    }
                }
            },
        )

        with self.assertRaisesRegex(
            scaffold_audit_sidecars.AuditScaffoldError,
            "semantic_contract.spec_declaration.*configured only as auxiliary",
        ):
            scaffold_audit_sidecars._frozen_input_snapshot(self.paper)

    def test_direct_route_preflight_requires_qualified_include_for_ambiguous_short_name(self) -> None:
        (self.paper / "PaperInterface.lean").write_text(
            """namespace FixturePaper
namespace First
theorem endpoint : True := by trivial
end First
namespace Second
theorem endpoint : True := by trivial
end Second
end FixturePaper
""",
            encoding="utf-8",
        )
        item = {
            "source_claim": {
                "claim_bearing": True,
                "lean_declarations": ["FixturePaper.First.endpoint"],
            }
        }
        self.write_route_configuration(include_names=["endpoint"], items=item)

        with self.assertRaisesRegex(
            scaffold_audit_sidecars.AuditScaffoldError,
            "ambiguous or unresolved review_surface.include_names route `endpoint`",
        ):
            scaffold_audit_sidecars._frozen_input_snapshot(self.paper)

        self.write_route_configuration(
            include_names=["FixturePaper.First.endpoint"], items=item
        )
        snapshot = scaffold_audit_sidecars._frozen_input_snapshot(self.paper)
        self.assertEqual(snapshot["source_item_count"], 1)

    def test_rejects_fresh_source_record_without_current_policy_version(self) -> None:
        payload = json.loads(json.dumps(self.fresh_source_record_payload))
        payload["source_record_policy_version"] = "source-record-v9-legacy"

        with self.assertRaisesRegex(
            scaffold_audit_sidecars.AuditScaffoldError,
            "does not expose the current source-record policy",
        ):
            scaffold_audit_sidecars._validate_fresh_source_record_payload(
                self.paper, payload
            )

    def test_force_requires_explicit_destruction_for_populated_judgment(self) -> None:
        scaffold_audit_sidecars.scaffold_current_audit_sidecars("FixturePaper")
        match_path = self.sidecar("source_record_match_llm.json")
        populated = json.loads(match_path.read_text(encoding="utf-8"))
        populated["items"] = {
            "semantic-model::unrelated_lean_row": {
                "classification": "semantic_model_review",
                "reason": "Human review evidence that must not be silently erased.",
            }
        }
        match_path.write_text(json.dumps(populated), encoding="utf-8")
        original = match_path.read_bytes()

        with self.assertRaisesRegex(
            scaffold_audit_sidecars.AuditScaffoldError,
            "destroy-semantic-evidence",
        ):
            scaffold_audit_sidecars.scaffold_current_audit_sidecars(
                "FixturePaper", force=True
            )
        self.assertEqual(match_path.read_bytes(), original)

        scaffold_audit_sidecars.scaffold_current_audit_sidecars(
            "FixturePaper", force=True, destroy_semantic_evidence=True
        )
        replacement = json.loads(match_path.read_text(encoding="utf-8"))
        self.assertEqual(replacement["items"], {})
        self.assertEqual(
            replacement["source_record_audit_sha256"], "a" * 64
        )

    def test_source_record_only_preserves_dashboard_evidence(self) -> None:
        scaffold_audit_sidecars.scaffold_current_audit_sidecars("FixturePaper")
        dashboard_before: dict[str, bytes] = {}
        for name in scaffold_audit_sidecars.DASHBOARD_SIDECARS:
            path = self.sidecar(name)
            payload = json.loads(path.read_text(encoding="utf-8"))
            payload["items"] = {
                "unrelated_lean_row": {
                    "evidence": "Current dashboard evidence must survive v10 refresh."
                }
            }
            payload.pop("non_evidence_scaffold", None)
            path.write_text(json.dumps(payload), encoding="utf-8")
            dashboard_before[name] = path.read_bytes()

        targets = scaffold_audit_sidecars.scaffold_source_record_sidecars(
            "FixturePaper", force=True
        )

        self.assertEqual(
            [target.name for target in targets],
            list(scaffold_audit_sidecars.SOURCE_RECORD_SIDECARS),
        )
        self.assertEqual(
            dashboard_before,
            {
                name: self.sidecar(name).read_bytes()
                for name in scaffold_audit_sidecars.DASHBOARD_SIDECARS
            },
        )
        audit_payload = json.loads(
            self.sidecar("source_record_audit.json").read_text(encoding="utf-8")
        )
        match_payload = json.loads(
            self.sidecar("source_record_match_llm.json").read_text(encoding="utf-8")
        )
        self.assertEqual(match_payload["items"], {})
        self.assertEqual(
            match_payload["source_record_audit_sha256"],
            audit_payload["source_record_audit_sha256"],
        )

    def test_force_replaces_stale_zero_judgment_machine_audit(self) -> None:
        scaffold_audit_sidecars.scaffold_current_audit_sidecars("FixturePaper")
        audit_path = self.sidecar("source_record_audit.json")
        stale = json.loads(audit_path.read_text(encoding="utf-8"))
        stale["fresh_source_elaboration"]["source_sha256"] = "b" * 64
        stale["lean_check"]["fresh_source_elaboration"]["source_sha256"] = "b" * 64
        audit_path.write_text(json.dumps(stale), encoding="utf-8")

        targets = scaffold_audit_sidecars.scaffold_source_record_sidecars(
            "FixturePaper", force=True
        )

        self.assertEqual(
            [target.name for target in targets],
            list(scaffold_audit_sidecars.SOURCE_RECORD_SIDECARS),
        )
        replacement = json.loads(audit_path.read_text(encoding="utf-8"))
        self.assertEqual(
            replacement["fresh_source_elaboration"]["source_sha256"],
            scaffold_audit_sidecars._sha256_file(self.paper / "PaperInterface.lean"),
        )

    def test_source_record_only_protects_populated_judgments(self) -> None:
        scaffold_audit_sidecars.scaffold_current_audit_sidecars("FixturePaper")
        dashboard_before = {
            name: self.sidecar(name).read_bytes()
            for name in scaffold_audit_sidecars.DASHBOARD_SIDECARS
        }
        match_path = self.sidecar("source_record_match_llm.json")
        populated = json.loads(match_path.read_text(encoding="utf-8"))
        populated["items"] = {
            "semantic-model::unrelated_lean_row": {
                "classification": "semantic_model_review",
                "reason": "Do not erase current source-record evidence.",
            }
        }
        match_path.write_text(json.dumps(populated), encoding="utf-8")
        original_match = match_path.read_bytes()

        with self.assertRaisesRegex(
            scaffold_audit_sidecars.AuditScaffoldError,
            "destroy-semantic-evidence",
        ):
            scaffold_audit_sidecars.scaffold_source_record_sidecars(
                "FixturePaper", force=True
            )
        self.assertEqual(match_path.read_bytes(), original_match)

        scaffold_audit_sidecars.scaffold_source_record_sidecars(
            "FixturePaper", force=True, destroy_semantic_evidence=True
        )
        replacement = json.loads(match_path.read_text(encoding="utf-8"))
        self.assertEqual(replacement["items"], {})
        self.assertEqual(
            dashboard_before,
            {
                name: self.sidecar(name).read_bytes()
                for name in scaffold_audit_sidecars.DASHBOARD_SIDECARS
            },
        )

    def test_source_record_only_validates_before_replacing_targets(self) -> None:
        scaffold_audit_sidecars.scaffold_current_audit_sidecars("FixturePaper")
        source_before = {
            name: self.sidecar(name).read_bytes()
            for name in scaffold_audit_sidecars.SOURCE_RECORD_SIDECARS
        }
        dashboard_before = {
            name: self.sidecar(name).read_bytes()
            for name in scaffold_audit_sidecars.DASHBOARD_SIDECARS
        }

        with mock.patch.object(
            scaffold_audit_sidecars,
            "_generate_fresh_source_record_audit",
            side_effect=scaffold_audit_sidecars.AuditScaffoldError("Lean source check failed"),
        ):
            with self.assertRaisesRegex(
                scaffold_audit_sidecars.AuditScaffoldError, "Lean source check failed"
            ):
                scaffold_audit_sidecars.scaffold_source_record_sidecars(
                    "FixturePaper", force=True
                )

        self.assertEqual(
            source_before,
            {
                name: self.sidecar(name).read_bytes()
                for name in scaffold_audit_sidecars.SOURCE_RECORD_SIDECARS
            },
        )
        self.assertEqual(
            dashboard_before,
            {
                name: self.sidecar(name).read_bytes()
                for name in scaffold_audit_sidecars.DASHBOARD_SIDECARS
            },
        )

    def test_force_protects_unknown_source_record_audit_content(self) -> None:
        scaffold_audit_sidecars.scaffold_current_audit_sidecars("FixturePaper")
        audit_path = self.sidecar("source_record_audit.json")
        populated = json.loads(audit_path.read_text(encoding="utf-8"))
        populated["manual_semantic_note"] = "Do not silently discard this evidence."
        audit_path.write_text(json.dumps(populated), encoding="utf-8")
        original = audit_path.read_bytes()

        with self.assertRaisesRegex(
            scaffold_audit_sidecars.AuditScaffoldError,
            "destroy-semantic-evidence",
        ):
            scaffold_audit_sidecars.scaffold_current_audit_sidecars(
                "FixturePaper", force=True
            )
        self.assertEqual(audit_path.read_bytes(), original)

    def test_fresh_machine_audit_preserves_human_judgment_until_atomic_replacement(self) -> None:
        scaffold_audit_sidecars.scaffold_current_audit_sidecars("FixturePaper")
        match_path = self.sidecar("source_record_match_llm.json")
        populated = json.loads(match_path.read_text(encoding="utf-8"))
        populated["items"] = {"reviewed": {"classification": "validated_source_assumption"}}
        match_path.write_text(json.dumps(populated), encoding="utf-8")
        observed_present_during_generation: list[bool] = []

        def generate(folder: Path) -> dict[str, object]:
            observed_present_during_generation.append(
                (folder / "audit" / "source_record_match_llm.json").exists()
            )
            return json.loads(json.dumps(self.fresh_source_record_payload))

        with mock.patch.object(
            scaffold_audit_sidecars,
            "_generate_fresh_source_record_audit",
            side_effect=generate,
        ):
            scaffold_audit_sidecars.scaffold_current_audit_sidecars(
                "FixturePaper", force=True, destroy_semantic_evidence=True
            )
        self.assertEqual(observed_present_during_generation, [True])

    def test_fresh_source_record_generation_is_required_before_any_write(self) -> None:
        with mock.patch.object(
            scaffold_audit_sidecars,
            "_generate_fresh_source_record_audit",
            side_effect=scaffold_audit_sidecars.AuditScaffoldError("Lean source check failed"),
        ):
            with self.assertRaisesRegex(
                scaffold_audit_sidecars.AuditScaffoldError, "Lean source check failed"
            ):
                scaffold_audit_sidecars.scaffold_current_audit_sidecars("FixturePaper")
        self.assertFalse(self.sidecar("lean_to_tex_llm.json").exists())
        self.assertFalse(self.sidecar("source_record_audit.json").exists())
        self.assertFalse(self.sidecar("source_record_match_llm.json").exists())

    def test_destroy_semantic_evidence_requires_force(self) -> None:
        with self.assertRaisesRegex(
            scaffold_audit_sidecars.AuditScaffoldError, "requires --force"
        ):
            scaffold_audit_sidecars.scaffold_current_audit_sidecars(
                "FixturePaper", destroy_semantic_evidence=True
            )


if __name__ == "__main__":
    unittest.main()
