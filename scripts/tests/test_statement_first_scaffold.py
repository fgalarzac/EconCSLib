#!/usr/bin/env python3
"""Regression tests for the statement-first new-paper scaffold."""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import audit_evidence_integrity as AUDIT_EVIDENCE


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "new_paper", ROOT / "scripts" / "new_paper.py"
)
assert SPEC is not None and SPEC.loader is not None
NEW_PAPER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = NEW_PAPER
SPEC.loader.exec_module(NEW_PAPER)


class StatementFirstScaffoldTests(unittest.TestCase):
    def install_status_sync_fixture(self, root: Path) -> None:
        config = root / "config"
        config.mkdir()
        (config / "formalization_audit_protocol.json").write_bytes(
            (ROOT / "config" / "formalization_audit_protocol.json").read_bytes()
        )

    def write_spec(
        self,
        directory: Path,
        *,
        source_location: str = "Theorem 2, p. 4",
        source_kind: str = "theorem",
        recorded_sha256: str | None = None,
        artifact_name: str = "source-transcript.txt",
        artifact_bytes: bytes = b"Theorem 2. For every n, n equals itself.\n",
    ) -> tuple[Path, bytes]:
        artifact = directory / artifact_name
        artifact.write_bytes(artifact_bytes)
        digest = hashlib.sha256(artifact_bytes).hexdigest()
        spec_path = directory / "statement-spec.json"
        spec_path.write_text(
            json.dumps(
                {
                    "schema": 1,
                    "source_artifact_path": artifact.name,
                    "source_artifact_sha256": recorded_sha256 or digest,
                    "source_version": "arXiv v2 (2025-01-01)",
                    "targets": [
                        {
                            "source_item": "Theorem 2",
                            "source_kind": source_kind,
                            "source_location": source_location,
                            "source_statement": "For every natural n, n equals itself.",
                            "lean_name": "theorem2_reflexive",
                            "lean_type": "(n : Nat) -> n = n",
                            "kind": "theorem",
                        }
                    ],
                }
            ),
            encoding="utf-8",
        )
        return spec_path, artifact_bytes

    def test_interface_without_spec_has_no_fake_target_or_proof(self) -> None:
        interface = NEW_PAPER.paper_interface_text(
            "Example", "EX00Example", "EX00Example"
        )
        assumptions = NEW_PAPER.assumption_source_text(
            "Example", "EX00Example", "EX00Example"
        )
        implementation = NEW_PAPER.main_theorems_text("Example", "EX00Example")
        self.assertIn("Intentionally no theorem placeholder", interface)
        self.assertNotIn("theorem paper_", interface)
        self.assertNotIn(":= by\n  sorry", interface)
        self.assertNotIn("abbrev paperDefinition", interface)
        self.assertNotIn("assumption_source_model_conditions", assumptions)
        self.assertNotIn("theorem paper_theorem_1", implementation)
        self.assertNotIn("trivial", implementation)
        NEW_PAPER.validate_rendered_statement_interface("EX00Example", [], interface)

    def test_verified_spec_emits_exact_type_but_not_source_certification(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            spec = NEW_PAPER.load_statement_spec(self.write_spec(Path(temp_dir))[0])
        interface = NEW_PAPER.paper_interface_text(
            "Example", "EX00Example", "EX00Example", spec.targets
        )
        self.assertIn(
            "def theorem2_reflexiveSpec : Prop :=\n  (n : Nat) -> n = n",
            interface,
        )
        self.assertIn(
            "theorem theorem2_reflexive :\n  theorem2_reflexiveSpec := by",
            interface,
        )
        self.assertIn("\n  sorry", interface)
        self.assertIn(
            "Source status: pinned statement-spec transcription; independent source audit pending",
            interface,
        )
        self.assertNotIn("Source status: direct source text", interface)

        args = argparse.Namespace(
            official_url="https://example.test/paper",
            url="https://example.test/paper.pdf",
        )
        source_map = json.loads(
            NEW_PAPER.paper_statement_map_text(
                args,
                "EX00Example",
                spec,
                "papers/EX00Example/source-audited.txt",
            )
        )
        self.assertFalse(source_map["source_curated"])
        self.assertTrue(source_map["seed_scaffold"])
        self.assertEqual(
            source_map["source_artifact_path"],
            "papers/EX00Example/source-audited.txt",
        )
        self.assertIn(
            "independent source audit pending",
            source_map["items"]["theorem2_reflexive"]["source_status"],
        )
        self.assertEqual(
            source_map["items"]["theorem2_reflexive"]["proof_lean_declarations"],
            ["theorem2_reflexive"],
        )
        self.assertEqual(
            source_map["items"]["theorem2_reflexive"]["spec_lean_declarations"],
            ["theorem2_reflexiveSpec"],
        )
        self.assertEqual(
            source_map["items"]["theorem2_reflexive"]["semantic_contract_template"],
            {
                "spec_declaration": "theorem2_reflexiveSpec",
                "evidence_declaration": "theorem2_reflexive",
                "evidence_mode": "proves",
                "semantic_shape": "plain",
            },
        )
        self.assertNotIn("semantic_contract", source_map["items"]["theorem2_reflexive"])
        self.assertNotIn("lean_declarations", source_map["items"]["theorem2_reflexive"])
        self.assertNotIn("semantic_contract_schema", source_map)
        self.assertNotIn("source_spec_correspondence_schema", source_map)
        self.assertIn(
            "Do not manufacture a contract",
            source_map["semantic_contract_policy"]["activation"],
        )
        activation = source_map["semantic_contract_policy"]["activation"]
        self.assertIn("source_spec_correspondence_schema: 1", activation)
        self.assertIn("proof and instance arguments", activation)
        self.assertIn("Legacy v10 evidence remains readable", activation)

    def test_v11_requirement_is_pending_for_fresh_scaffold_and_blocks_closeout(
        self,
    ) -> None:
        args = argparse.Namespace(
            title="Example",
            authors="A. Author",
            version="arXiv v2 (2025-01-01)",
        )
        status = json.loads(NEW_PAPER.status_text(args, "EX00Example"))
        self.assertEqual(status["status"], "not started")
        self.assertEqual(status["repository_visibility"], "private_only")
        self.assertIs(status["intake_freeze_required"], True)
        self.assertTrue(status["review_surface"]["require_source_spec_correspondence"])

        with tempfile.TemporaryDirectory() as temp_dir:
            paper = Path(temp_dir) / "EX00Example"
            audit = paper / "audit"
            audit.mkdir(parents=True)
            (paper / "status.json").write_text(json.dumps(status), encoding="utf-8")
            (audit / "paper_statement_map.json").write_text(
                json.dumps({"schema": 1, "items": {}}), encoding="utf-8"
            )

            self.assertEqual(
                AUDIT_EVIDENCE.source_spec_correspondence_inventory_findings(
                    paper, "not started"
                ),
                [],
            )

            status["status"] = "formalized"
            (paper / "status.json").write_text(json.dumps(status), encoding="utf-8")
            findings = AUDIT_EVIDENCE.source_spec_correspondence_inventory_findings(
                paper, "formalized"
            )
            self.assertTrue(
                any(
                    "require_source_spec_correspondence: true requires "
                    "source_spec_correspondence_schema" in finding.message
                    for finding in findings
                ),
                findings,
            )

    def test_main_copies_verified_artifact_to_stable_paper_local_path(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            self.install_status_sync_fixture(root)
            papers = root / "papers"
            papers.mkdir()
            template_dir = papers / "TEMPLATE"
            template_dir.mkdir()
            (template_dir / "FINAL_VALIDATION_REPORT.md").write_text(
                (ROOT / "papers" / "TEMPLATE" / "FINAL_VALIDATION_REPORT.md").read_text(
                    encoding="utf-8"
                ),
                encoding="utf-8",
            )
            spec_path, artifact_bytes = self.write_spec(root)
            args = argparse.Namespace(
                url="https://example.test/paper.pdf",
                folder="EX00Example",
                title="Example",
                authors="A. Author",
                version="arXiv v2 (2025-01-01)",
                official_url="https://example.test/paper",
                pdf_url=None,
                namespace="EX00Example",
                statement_spec=spec_path,
                no_download=True,
                force=True,
                with_notes=False,
            )
            with (
                mock.patch.object(NEW_PAPER, "ROOT", root),
                mock.patch.object(NEW_PAPER, "PAPERS", papers),
                mock.patch.object(NEW_PAPER, "parse_args", return_value=args),
                mock.patch.object(NEW_PAPER, "refresh_review_cache") as refresh_cache,
            ):
                self.assertEqual(NEW_PAPER.main(), 0)
            refresh_cache.assert_not_called()

            paper = papers / "EX00Example"
            audited = paper / "source-audited.txt"
            self.assertEqual(audited.read_bytes(), artifact_bytes)
            self.assertIn(
                "source-audited*", (paper / ".gitignore").read_text(encoding="utf-8")
            )
            source_map = json.loads(
                (paper / "audit" / "paper_statement_map.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertEqual(
                source_map["source_artifact_path"],
                "papers/EX00Example/source-audited.txt",
            )
            intake = json.loads(
                (paper / "audit" / "intake_freeze.json").read_text(encoding="utf-8")
            )
            self.assertEqual(intake["state"], "draft")
            self.assertFalse(intake["inventory_complete"])
            self.assertEqual(
                intake["source_artifact_path"],
                "papers/EX00Example/source-audited.txt",
            )
            self.assertEqual(intake["items"][0]["owner"], "unassigned")
            self.assertEqual(intake["items"][0]["source_atoms"], [])
            self.assertIsNone(intake["source_text_artifact"])
            proof_fidelity = json.loads(
                (paper / "audit" / "source_proof_fidelity.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertEqual(proof_fidelity["review_status"], "not_started")
            self.assertEqual(proof_fidelity["model_conventions"], [])
            self.assertEqual(proof_fidelity["checked_proof_steps"], [])
            self.assertIn(
                "checked_scope",
                proof_fidelity["model_convention_entry_schema"]["required"],
            )
            self.assertEqual(
                proof_fidelity["source_artifact_path"],
                "papers/EX00Example/source-audited.txt",
            )
            self.assertEqual(
                proof_fidelity["source_artifact_sha256"],
                hashlib.sha256(artifact_bytes).hexdigest(),
            )
            self.assertNotIn(
                "validated_source_assumption",
                proof_fidelity["defect_entry_schema"]["resolution_values"],
            )
            self.assertIn("id", proof_fidelity["defect_entry_schema"]["required"])
            defect_support = json.loads(
                (paper / "audit" / "defect_support_match_llm.json").read_text(
                    encoding="utf-8"
                )
            )
            self.assertEqual(
                defect_support["prompt_version"],
                "defect-support-v1-exact-source-defect-to-lean-semantic",
            )
            status = json.loads((paper / "status.json").read_text(encoding="utf-8"))
            self.assertEqual(status["paper_interface"]["declaration_rows"], 2)
            self.assertEqual(status["paper_interface"]["review_rows"], 2)
            self.assertEqual(
                status["review_surface"]["include_names"],
                ["theorem2_reflexiveSpec", "theorem2_reflexive"],
            )
            self.assertEqual(
                status["review_surface"]["proposition_spec_proofs"],
                {"theorem2_reflexiveSpec": "theorem2_reflexive"},
            )
            review = status["review_surface"]["source_proof_fidelity_review"]
            self.assertEqual(
                review["ledger_file"],
                "papers/EX00Example/audit/source_proof_fidelity.json",
            )
            self.assertEqual(
                status["review_surface"]["llm_paper_coverage_review"][
                    "defect_support_judgment_file"
                ],
                "papers/EX00Example/audit/defect_support_match_llm.json",
            )
            self.assertTrue(
                status["review_surface"]["llm_statement_review"][
                    "require_explicit_source_routes"
                ]
            )
            self.assertEqual(
                status["review_surface"]["llm_statement_review"][
                    "require_direct_expression_semantics_review"
                ],
                "v1",
            )
            self.assertTrue(
                status["review_surface"]["require_source_spec_correspondence"]
            )
            route_policy = status["review_surface"]["llm_statement_review"]["policy"]
            self.assertIn("exact equivalent paper-facing endpoint", route_policy)
            self.assertIn("source_model_convention", route_policy)
            self.assertIn("defect_or_remark_support", route_policy)
            self.assertIn("proof_support", route_policy)
            model_review = status["review_surface"]["semantic_model_review"]
            self.assertEqual(
                model_review["schema"], NEW_PAPER.SEMANTIC_MODEL_REVIEW_SCHEMA
            )
            self.assertEqual(
                set(model_review["required_dimensions"]),
                set(NEW_PAPER.SEMANTIC_MODEL_DIMENSION_ORDER),
            )
            self.assertFalse((paper / "source.pdf").exists())
            readme = (paper / "README.md").read_text(encoding="utf-8")
            self.assertTrue(
                readme.startswith("<!-- BEGIN GENERATED PAPER FOLDER README -->\n")
            )
            notes = paper / "docs" / "FORMALIZATION_NOTES.md"
            self.assertTrue(notes.is_file())
            self.assertIn("## Paper-Facing Ledger", notes.read_text(encoding="utf-8"))
            status_check = subprocess.run(
                [
                    sys.executable,
                    str(ROOT / "scripts" / "sync_paper_status.py"),
                    "--repo",
                    str(root),
                    "--paper",
                    "EX00Example",
                    "--check",
                ],
                cwd=root,
                text=True,
                capture_output=True,
                check=False,
            )
            self.assertEqual(
                status_check.returncode,
                0,
                status_check.stderr or status_check.stdout,
            )

    def test_main_records_pdf_text_receipt_before_writing_intake_freeze(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            self.install_status_sync_fixture(root)
            papers = root / "papers"
            papers.mkdir()
            template_dir = papers / "TEMPLATE"
            template_dir.mkdir()
            (template_dir / "FINAL_VALIDATION_REPORT.md").write_text(
                (ROOT / "papers" / "TEMPLATE" / "FINAL_VALIDATION_REPORT.md").read_text(
                    encoding="utf-8"
                ),
                encoding="utf-8",
            )
            pdf_bytes = b"%PDF-1.7 fixture"
            spec_path, _ = self.write_spec(
                root,
                artifact_name="source-transcript.pdf",
                artifact_bytes=pdf_bytes,
            )
            args = argparse.Namespace(
                url="https://example.test/paper.pdf",
                folder="EX00Example",
                title="Example",
                authors="A. Author",
                version="arXiv v2 (2025-01-01)",
                official_url="https://example.test/paper",
                pdf_url=None,
                namespace="EX00Example",
                statement_spec=spec_path,
                no_download=True,
                force=True,
                with_notes=False,
            )

            def extract_fixture(_pdf: Path, txt: Path, _force: bool) -> bool:
                txt.write_bytes(b"Theorem 2.\r\nFor every n, n equals itself.\r")
                return True

            with (
                mock.patch.object(NEW_PAPER, "ROOT", root),
                mock.patch.object(NEW_PAPER, "PAPERS", papers),
                mock.patch.object(NEW_PAPER, "parse_args", return_value=args),
                mock.patch.object(
                    NEW_PAPER, "extract_text", side_effect=extract_fixture
                ),
            ):
                self.assertEqual(NEW_PAPER.main(), 0)

            paper = papers / "EX00Example"
            intake = json.loads(
                (paper / "audit" / "intake_freeze.json").read_text(encoding="utf-8")
            )
            receipt = intake["source_text_artifact"]
            normalized = b"Theorem 2.\nFor every n, n equals itself.\n"
            self.assertEqual((paper / "source.txt").read_bytes(), normalized)
            self.assertEqual(receipt["sha256"], hashlib.sha256(normalized).hexdigest())
            self.assertEqual(
                receipt["extraction"]["source_artifact_path"],
                "papers/EX00Example/source-audited.pdf",
            )
            self.assertEqual(
                receipt["extraction"]["source_artifact_sha256"],
                hashlib.sha256(pdf_bytes).hexdigest(),
            )

    def test_pdf_text_receipt_is_normalized_and_bound_to_exact_source(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper = root / "papers" / "EX00Example"
            paper.mkdir(parents=True)
            source_text = paper / "source.txt"
            source_text.write_bytes(b"first\r\nsecond\rlast\n")
            source_digest = "a" * 64
            with mock.patch.object(NEW_PAPER, "ROOT", root):
                receipt = NEW_PAPER.normalized_source_text_receipt(
                    source_text,
                    source_artifact_path="papers/EX00Example/source-audited.pdf",
                    source_artifact_sha256=source_digest,
                )

            self.assertIsNotNone(receipt)
            assert receipt is not None
            normalized = b"first\nsecond\nlast\n"
            self.assertEqual(source_text.read_bytes(), normalized)
            self.assertEqual(receipt["path"], "papers/EX00Example/source.txt")
            self.assertEqual(receipt["sha256"], hashlib.sha256(normalized).hexdigest())
            self.assertEqual(receipt["normalization"], "utf8-lf-v1")
            self.assertEqual(
                receipt["extraction"],
                {
                    "schema": 1,
                    "source_artifact_path": ("papers/EX00Example/source-audited.pdf"),
                    "source_artifact_sha256": source_digest,
                    "tool": "pdftotext",
                    "options": [],
                },
            )

    def test_spec_rejects_hash_mismatch_vague_locator_and_definition_kind(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            directory = Path(temp_dir)
            mismatch, _ = self.write_spec(directory, recorded_sha256="0" * 64)
            with self.assertRaisesRegex(
                ValueError, "does not match source artifact bytes"
            ):
                NEW_PAPER.load_statement_spec(mismatch)

            vague, _ = self.write_spec(
                directory, source_location="near the main result"
            )
            with self.assertRaisesRegex(ValueError, "no exact source locator"):
                NEW_PAPER.load_statement_spec(vague)

            definition, _ = self.write_spec(directory, source_kind="definition")
            with self.assertRaisesRegex(ValueError, "unsupported source_kind"):
                NEW_PAPER.load_statement_spec(definition)

            runtime_claim, _ = self.write_spec(directory, source_kind="runtime_claim")
            runtime_spec = NEW_PAPER.load_statement_spec(runtime_claim)
            self.assertEqual(runtime_spec.targets[0].source_kind, "runtime_claim")

    def test_spec_rejects_declaration_breakout_but_allows_type_local_assignments(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            directory = Path(temp_dir)
            spec_path, _ = self.write_spec(directory)
            payload = json.loads(spec_path.read_text(encoding="utf-8"))
            payload["targets"][0]["lean_type"] = (
                "True := by trivial\naxiom hidden : False\ntheorem dummy : True"
            )
            spec_path.write_text(json.dumps(payload), encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "top-level"):
                NEW_PAPER.load_statement_spec(spec_path)

        NEW_PAPER._validate_lean_type_fragment(
            "let n : Nat := 1\nList.replicate (n := n) True = [True]", 1
        )

    def test_post_render_validation_rejects_an_extra_declaration(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            spec = NEW_PAPER.load_statement_spec(self.write_spec(Path(temp_dir))[0])
        rendered = NEW_PAPER.paper_interface_text(
            "Example", "EX00Example", "EX00Example", spec.targets
        )
        injected = rendered.replace(
            "\n\nend EX00Example", "\n\naxiom hidden : False\n\nend EX00Example"
        )
        with self.assertRaisesRegex(ValueError, "outside the requested targets"):
            NEW_PAPER.validate_rendered_statement_interface(
                "EX00Example", spec.targets, injected
            )

    def test_post_render_validation_rejects_changed_spec_or_proof_route(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            spec = NEW_PAPER.load_statement_spec(self.write_spec(Path(temp_dir))[0])
        rendered = NEW_PAPER.paper_interface_text(
            "Example", "EX00Example", "EX00Example", spec.targets
        )
        changed_spec = rendered.replace(
            "(n : Nat) -> n = n", "(n : Nat) -> n + 1 = n", 1
        )
        with self.assertRaisesRegex(ValueError, "transparent `...Spec : Prop`"):
            NEW_PAPER.validate_rendered_statement_interface(
                "EX00Example", spec.targets, changed_spec
            )
        changed_proof = rendered.replace(
            "theorem2_reflexiveSpec := by", "True := by", 1
        )
        with self.assertRaisesRegex(ValueError, "`...Spec := by sorry`"):
            NEW_PAPER.validate_rendered_statement_interface(
                "EX00Example", spec.targets, changed_proof
            )

    def test_spec_rejects_generated_spec_name_collision(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            directory = Path(temp_dir)
            spec_path, _ = self.write_spec(directory)
            payload = json.loads(spec_path.read_text(encoding="utf-8"))
            second = dict(payload["targets"][0])
            second["lean_name"] = "theorem2_reflexiveSpec"
            second["source_item"] = "Theorem 3"
            second["source_location"] = "Theorem 3, p. 5"
            second["source_statement"] = "For every natural n, n equals itself again."
            payload["targets"].append(second)
            spec_path.write_text(json.dumps(payload), encoding="utf-8")
            with self.assertRaisesRegex(
                ValueError, "collide after generating `...Spec`"
            ):
                NEW_PAPER.load_statement_spec(spec_path)

    def test_post_render_validation_imports_econcs_library_surface(self) -> None:
        target = NEW_PAPER.StatementTarget(
            source_item="Theorem 3",
            source_kind="theorem",
            source_location="Theorem 3, p. 5",
            source_statement="Every position environment equals itself.",
            lean_name="theorem3_environment_reflexive",
            lean_type=(
                "(environment : EconCSLib.Auction.PositionEnvironment Unit) -> "
                "environment = environment"
            ),
        )
        rendered = NEW_PAPER.paper_interface_text(
            "Example", "EX00Example", "EX00Example", [target]
        )
        NEW_PAPER.validate_rendered_statement_interface(
            "EX00Example", [target], rendered
        )

    def test_statement_first_pair_preserves_lemma_kind(self) -> None:
        target = NEW_PAPER.StatementTarget(
            source_item="Lemma 1",
            source_kind="lemma",
            source_location="Lemma 1, p. 2",
            source_statement="Every natural number equals itself.",
            lean_name="lemma1_reflexive",
            lean_type="(n : Nat) -> n = n",
            kind="lemma",
        )
        rendered = NEW_PAPER.paper_interface_text(
            "Example", "EX00Example", "EX00Example", [target]
        )
        self.assertIn(
            "def lemma1_reflexiveSpec : Prop :=\n  (n : Nat) -> n = n",
            rendered,
        )
        self.assertIn(
            "lemma lemma1_reflexive :\n  lemma1_reflexiveSpec := by",
            rendered,
        )
        NEW_PAPER.validate_rendered_statement_interface(
            "EX00Example", [target], rendered
        )

    def test_plan_records_manifest_freeze_and_v10_fidelity_review(self) -> None:
        plan = NEW_PAPER.formalization_plan_text("Example", "EX00Example")
        self.assertIn("## Audited Statement Skeleton", plan)
        self.assertIn("v10 declaration-manifest SHA-256", plan)
        self.assertIn("numeric and discrete obligation partitions", plan)
        self.assertNotIn("v7 statement", plan)
        self.assertIn("`by sorry`", plan)
        self.assertIn("`<name>Spec : Prop`", plan)
        self.assertIn("`semantic_contract_template`", plan)
        self.assertIn("v11 source-to-Spec correspondence", plan)
        self.assertIn("proof and instance arguments", plan)
        self.assertIn("Legacy v10 evidence remains", plan)
        self.assertIn(
            "Signature changes after a `matches` verdict invalidate the row", plan
        )
        self.assertIn("source_model_convention", plan)
        self.assertIn("defect_or_remark_support", plan)
        self.assertIn("proof_support", plan)
        self.assertIn("## Intake Freeze Boundary", plan)
        self.assertIn("--bootstrap-current", plan)
        self.assertIn("run_paper_closeout.py", plan)
        self.assertIn("Do not invoke", plan)
        self.assertLess(
            plan.index("Freeze closeout presentation inputs"),
            plan.index("Closeout readiness:"),
        )
        self.assertIn("exact current compiled cache skips a redundant", plan)
        self.assertIn("--source-inventory-check", plan)
        self.assertIn("bounded manifest retry", plan)
        self.assertIn("let the planner schedule the required delta", plan)
        self.assertIn(
            "do not pre-run those\n      gates just to recreate an intermediate receipt",
            plan,
        )
        future_intake = json.loads(
            NEW_PAPER.intake_freeze_text("EX00Example", None, "")
        )
        self.assertEqual(future_intake["state"], "draft")
        self.assertEqual(future_intake["items"], [])
        sidecar = json.loads(NEW_PAPER.statement_match_llm_text("EX00Example"))
        self.assertEqual(
            sidecar["prompt_version"],
            "statement-match-v10-semantic-fidelity-seat-stopping",
        )
        summary = "\n".join(sidecar["prompt_summary"])
        self.assertIn("self_characterizing", summary)
        self.assertIn("semantic worlds", summary)
        self.assertIn("polynomial time", summary)
        self.assertIn("Natural floor division", summary)
        self.assertIn("immediate list successor", summary.lower())
        self.assertIn("source output arity/shape", summary)
        self.assertIn("nonvacuity", summary)
        self.assertIn("coherent realization", summary)
        self.assertIn("nonempty realized fibers", summary)
        self.assertIn("input domains, state transitions, termination", summary)
        self.assertIn("numeric representation", summary)
        self.assertIn("advertised global claim", summary)
        self.assertIn("source_definition_semantics_review", summary)
        self.assertIn("outside the source domain", summary)
        self.assertNotIn("turnout-dependent quota", summary)
        schema = sidecar["semantic_scope_review_schema"]
        self.assertIn("fixed_profile", schema["profile_quantification_values"])
        self.assertIn("all_profiles", schema["profile_quantification_values"])
        self.assertIn("noncomputable_existence", schema["lean_claim_level_values"])
        self.assertIn("preserves_result", schema["world_bridge_relation_values"])
        self.assertIn("numeric_semantics_review", schema["required"])
        self.assertIn("discrete_semantics_review", schema["required"])
        self.assertIn("fidelity_risk_review", schema["required"])
        self.assertIn(
            "source_definition_semantics_review_required_when",
            schema,
        )
        self.assertIn(
            "source_outside_domain_behavior",
            schema["source_definition_semantics_review_required"],
        )
        self.assertIn(
            "properties_reviewed",
            schema["source_definition_advertised_property_status_values"],
        )
        self.assertIn(
            "recursive_expansion_complete",
            schema["named_definition_item_required"],
        )
        self.assertIn(
            "lean_obligation_ids",
            schema["named_definition_item_required"],
        )
        self.assertIn(
            "witness_specific_equivalent",
            schema["numeric_semantics_relation_values"],
        )
        self.assertIn(
            "source_zero_denominator",
            schema["numeric_semantics_item_required"],
        )
        self.assertIn(
            "source_order_sensitivity",
            schema["discrete_semantics_item_required"],
        )
        risk_schema = sidecar["fidelity_risk_review_schema"]
        self.assertEqual(
            risk_schema["version"],
            NEW_PAPER.FIDELITY_RISK_REVIEW_VERSION,
        )
        self.assertEqual(
            set(risk_schema["required_dimensions"]),
            NEW_PAPER.FIDELITY_RISK_DIMENSIONS,
        )
        self.assertIn("surjectivity", risk_schema["surjectivity_rule"])
        self.assertIn("local transition", risk_schema["algorithmic_rule"])
        self.assertIn("global bridge", risk_schema["algorithmic_rule"])
        self.assertIn(
            "source_termination_scope",
            risk_schema["execution_claim_scope_fields"],
        )
        self.assertIn(
            "source_state_transition_scope",
            risk_schema["execution_claim_scope_fields"],
        )
        self.assertNotIn(
            "source_seat_termination_scope",
            risk_schema["execution_claim_scope_fields"],
        )
        self.assertIn(
            "v2 records remain valid", risk_schema["legacy_compatibility_rule"]
        )
        self.assertIn("function names", risk_schema["name_independence_rule"])
        self.assertIn("exact equivalent paper-facing endpoint", summary)
        self.assertIn("source_model_convention", summary)
        self.assertIn("defect_or_remark_support", summary)
        self.assertIn("proof_support", summary)
        self.assertIn("corrected_source_statement", summary)
        self.assertIn("approved_corrected_target", summary)
        self.assertIn("archival_equivalence_claimed=false", summary)

    def test_source_record_scaffold_uses_semantic_result_component_prompt(self) -> None:
        sidecar = json.loads(NEW_PAPER.source_record_match_llm_text("EX00Example"))
        self.assertEqual(
            sidecar["prompt_version"],
            "source-record-v10-semantic-conclusion-boundary-contract",
        )
        self.assertEqual(
            sidecar["source_record_policy_version"],
            NEW_PAPER.SOURCE_RECORD_PROMPT_VERSION,
        )
        summary = "\n".join(sidecar["prompt_summary"])
        self.assertIn("literal legal action space", summary)
        self.assertIn("noncomputable finite selector", summary)
        self.assertIn("logically composing the advertised feasibility", summary)
        self.assertIn("conclusion-bearing proof debt", summary)
        self.assertIn("self-characterizing", summary)
        self.assertIn("distinct semantic worlds", summary)
        self.assertIn("fixed-profile", summary)
        self.assertIn("source output arity/shape", summary)
        self.assertIn("duplicate interactions", summary)
        self.assertIn("one coherent witness", summary)
        self.assertIn("nonempty realized fibers", summary)
        self.assertIn("source/Lean input scope", summary)
        self.assertIn("state transitions, termination", summary)
        self.assertIn("local-to-global bridge basis", summary)
        self.assertNotIn("fixed-quota/mismatched-seat-stopping/one-round", summary)
        self.assertIn("semantic_model_comparison", summary)
        self.assertIn("semantic_model_dimensions", summary)
        self.assertIn("endpoint-support", summary)
        self.assertIn("iid/product", summary)
        self.assertIn("WithTop", summary)

    def test_coverage_scaffold_requires_proof_declarations_and_defect_quarantine(
        self,
    ) -> None:
        sidecar = json.loads(
            NEW_PAPER.paper_coverage_llm_text(
                "EX00Example",
                source_artifact_path="papers/EX00Example/source-audited.txt",
                source_artifact_sha256="a" * 64,
            )
        )
        self.assertEqual(
            sidecar["prompt_version"],
            "paper-coverage-v5-semantic-proof-row-signature-pins",
        )
        self.assertEqual(
            sidecar["source_artifact_path"],
            "papers/EX00Example/source-audited.txt",
        )
        self.assertEqual(sidecar["source_artifact_sha256"], "a" * 64)
        summary = "\n".join(sidecar["prompt_summary"])
        self.assertIn("def/abbrev", summary)
        self.assertIn("quarantined_source_defect", summary)
        self.assertIn("counterexample or refutation", summary)
        self.assertIn("defect_support_match_llm.json", summary)
        self.assertIn("review_row_signature_sha256", summary)
        self.assertIn(
            "review_row_signature_sha256",
            sidecar["item_schema"]["direct_coverage_required"],
        )
        self.assertIn("corrected_source_statement", summary)
        self.assertIn("covered_corrected_target", summary)
        self.assertIn("approved_corrected_target", summary)
        self.assertIn("archival_equivalence_claimed=false", summary)

        defect_sidecar = json.loads(
            NEW_PAPER.defect_support_match_llm_text("EX00Example")
        )
        self.assertEqual(
            defect_sidecar["prompt_version"],
            "defect-support-v1-exact-source-defect-to-lean-semantic",
        )
        self.assertIn("source_defect_sha256", defect_sidecar["item_schema"]["required"])
        defect_prompt = "\n".join(defect_sidecar["prompt_summary"])
        self.assertIn("every elaborated signature atom", defect_prompt)
        self.assertIn("Reject True", defect_prompt)

    def test_no_spec_cli_rejects_path_namespace_and_comment_injection(self) -> None:
        base = {
            "url": "https://example.test/paper.pdf",
            "folder": "EX00Example",
            "title": "Example",
            "authors": "A. Author",
            "version": "arXiv v2",
            "official_url": None,
            "pdf_url": None,
            "namespace": "EX00Example",
            "statement_spec": None,
            "no_download": True,
            "force": True,
            "with_notes": False,
        }
        cases = [
            {"folder": "../Escape"},
            {"namespace": "EX00Example\nend EX00Example\naxiom hidden : False"},
            {"title": "Example -/\naxiom hidden : False\n/-"},
        ]
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            papers = root / "papers"
            papers.mkdir()
            for overrides in cases:
                with self.subTest(overrides=overrides):
                    args = argparse.Namespace(**(base | overrides))
                    with (
                        mock.patch.object(NEW_PAPER, "ROOT", root),
                        mock.patch.object(NEW_PAPER, "PAPERS", papers),
                        mock.patch.object(NEW_PAPER, "parse_args", return_value=args),
                        mock.patch.object(NEW_PAPER, "refresh_review_cache"),
                    ):
                        self.assertEqual(NEW_PAPER.main(), 2)
            self.assertEqual(list(papers.iterdir()), [])


if __name__ == "__main__":
    unittest.main()
