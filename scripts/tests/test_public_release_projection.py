from __future__ import annotations

import hashlib
import json
import unittest
from pathlib import Path

from scripts import public_release_projection as projection
from scripts.source_coverage_scope import source_map_structural_errors


class PublicReleaseProjectionTests(unittest.TestCase):
    def test_json_projection_preserves_source_evidence_without_private_workflow(self) -> None:
        source_sha256 = "a" * 64
        quote = "Verbatim source excerpt: each allocation assigns each item."
        quote_sha256 = hashlib.sha256(quote.encode("utf-8")).hexdigest()
        payload = {
            "paper": "Fixture",
            "source_url": "https://arxiv.org/abs/2405.16762",
            "source_version": (
                "arXiv:2405.16762; exact audit extraction recorded separately "
                "from the older tracked text extraction"
            ),
            "source_artifact_path": ".audit_source/Fixture.txt",
            "source_artifact_sha256": source_sha256,
            "source_artifact_provisioning": {
                "audit_path": "papers/Fixture/.audit_source/Fixture.txt",
                "origin_path": "/tmp/econcs_source_text/Fixture.txt",
            },
            "canonical_source_audit": {
                "path": "papers/Fixture/.audit_source/Fixture.txt",
                "sha256": source_sha256,
            },
            "source_inventory_policy": (
                "The exact extraction /tmp/econcs_source_text/Fixture.txt "
                f"(SHA256 {source_sha256}) is the source record."
            ),
            "llm_judge_prompt": (
                "Compare the source anchor at .audit_source/Fixture.txt:12-15 "
                "with the expanded Lean proposition."
            ),
            "source_text_companion": {
                "canonical_text": {"path": "source.txt", "sha256": source_sha256},
                "visual_comparison_attestation": {
                    "method": "The private text extraction was checked against the primary scan."
                },
                "page_map": [{"line_start": 12, "line_end": 15, "pdf_page": 2}],
            },
            "source_archive_surface": {
                "archive": {"path": "source_arxiv.tar", "sha256": source_sha256}
            },
            "signature_cache": "papers/Fixture/.review_traces/rows.json",
            "items": {
                "claim": {
                    "statement": "The mathematical claim is unchanged.",
                    "source_url": "https://arxiv.org/abs/2405.16762",
                    "source_location": ".audit_source/Fixture.txt:12-15",
                    "source_anchor_evidence": [
                        {
                            "path": ".audit_source/Fixture.txt",
                            "line_start": 12,
                            "line_end": 15,
                            "quoted_text": quote,
                            "quoted_text_sha256": quote_sha256,
                        }
                    ],
                    "source_note": "The unresolved mathematical handoff is retained in the deep observation.",
                    "source_locator": "Theorem 1; .audit_source/Fixture.txt:12-15",
                    "source_restatement_evidence": {
                        "path": "source.txt",
                        "line_start": 12,
                        "line_end": 15,
                        "quoted_text": quote,
                        "quoted_text_sha256": quote_sha256,
                    },
                }
            },
            "defects": [
                {
                    "affected_source_locators": [
                        ".audit_source/Fixture.txt:12-15"
                    ],
                    "source_artifact_identities": [
                        {"path": ".audit_source/Fixture.txt", "sha256": source_sha256}
                    ],
                }
            ],
            "review_surface": {
                "source_proof_fidelity_review": {
                    "policy": "Keep the remediation handoff current before closeout."
                }
            },
            "artifacts": {
                "source_fidelity_remediation": "docs/SOURCE_FIDELITY_REMEDIATION.md"
            },
            "remediation_scope": {"kind": "remediation_closed"},
            "deep_audit_observations": [
                {
                    "repair_handoff": (
                        "A future source review should state the computational model."
                    )
                }
            ],
        }

        raw = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        first = projection.project_bytes(
            "papers/Fixture/audit/paper_statement_map.json",
            raw,
            include_source_display_marker=True,
        )
        second = projection.project_bytes(
            "papers/Fixture/audit/paper_statement_map.json",
            raw,
            include_source_display_marker=True,
        )
        self.assertEqual(first, second)

        projected = json.loads(first)
        self.assertNotIn("source_artifact_path", projected)
        self.assertNotIn("source_artifact_provisioning", projected)
        self.assertNotIn("canonical_source_audit", projected)
        self.assertNotIn("source_archive_surface", projected)
        self.assertNotIn("signature_cache", projected)
        self.assertEqual(projected["source_artifact_sha256"], source_sha256)
        self.assertEqual(projected["source_url"], payload["source_url"])
        self.assertNotIn("private source extraction", projected["source_version"].lower())
        self.assertEqual(projected["source_version"], "cited publication source record")
        self.assertIn(source_sha256, projected["source_inventory_policy"])
        self.assertNotIn(".audit_source", projected["llm_judge_prompt"])
        # A companion has no useful public meaning once its byte paths are
        # deliberately withheld.  Its retained hash would otherwise look like
        # a locally re-verifiable source record, so the public projection omits
        # the whole private-only companion rather than leaving a malformed
        # pathless schema fragment.
        self.assertNotIn("source_text_companion", projected)
        marker = projected[projection.PUBLIC_SOURCE_DISPLAY_PROJECTION_FIELD]
        self.assertEqual(marker["schema"], projection.PUBLIC_SOURCE_DISPLAY_PROJECTION_SCHEMA)
        self.assertEqual(
            marker["manifest"], projection.PUBLIC_SOURCE_DISPLAY_PROJECTION_MANIFEST
        )
        self.assertFalse(marker["raw_source_bytes_included"])

        unmarked = json.loads(
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json", raw
            )
        )
        self.assertNotIn(projection.PUBLIC_SOURCE_DISPLAY_PROJECTION_FIELD, unmarked)
        anchor = projected["items"]["claim"]["source_anchor_evidence"][0]
        self.assertNotIn("path", anchor)
        self.assertEqual(anchor["publication_locator"], projection.PUBLICATION_LOCATOR)
        self.assertEqual(anchor["line_start"], 12)
        self.assertEqual(anchor["line_end"], 15)
        self.assertEqual(anchor["quoted_text"], quote)
        self.assertEqual(anchor["quoted_text_sha256"], quote_sha256)
        self.assertEqual(
            projected["items"]["claim"]["source_location"], "publication text:12-15"
        )
        self.assertIn(
            "remaining mathematical issue", projected["items"]["claim"]["source_note"]
        )
        self.assertNotIn(
            ".audit_source", projected["items"]["claim"]["source_locator"]
        )
        restatement = projected["items"]["claim"]["source_restatement_evidence"]
        self.assertNotIn("path", restatement)
        self.assertEqual(restatement["publication_locator"], projection.PUBLICATION_LOCATOR)
        self.assertNotIn(
            ".audit_source",
            projected["defects"][0]["affected_source_locators"][0],
        )
        self.assertEqual(
            projected["defects"][0]["source_artifact_identities"][0]["path"],
            projection.PUBLICATION_LOCATOR,
        )
        self.assertIn(
            "source-review record",
            projected["review_surface"]["source_proof_fidelity_review"]["policy"],
        )
        self.assertIn("source_fidelity_review", projected["artifacts"])
        self.assertNotIn("source_fidelity_remediation", projected["artifacts"])
        self.assertEqual(projected["review_scope"]["kind"], "review_complete")
        self.assertNotIn("repair_handoff", projected["deep_audit_observations"][0])
        self.assertIn("scope_note", projected["deep_audit_observations"][0])

    def test_unknown_unsafe_json_content_fails_closed(self) -> None:
        payload = {
            "paper": "Fixture",
            "ordinary_note": "The worktree receipt is stored at /tmp/private-note.txt.",
        }
        with self.assertRaisesRegex(projection.ProjectionError, "ordinary_note"):
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json",
                json.dumps(payload).encode("utf-8"),
            )

    def test_nested_object_below_quote_field_is_not_a_source_excerpt_bypass(self) -> None:
        payload = {"quoted_text": {"hidden": "/tmp/private-record.txt"}}
        with self.assertRaisesRegex(projection.ProjectionError, "hidden"):
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json",
                json.dumps(payload).encode("utf-8"),
            )

    def test_scalar_quote_requires_a_bound_source_record(self) -> None:
        payload = {"quoted_text": "/tmp/private-record.txt"}
        with self.assertRaisesRegex(projection.ProjectionError, "quoted_text"):
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json",
                json.dumps(payload).encode("utf-8"),
            )

    def test_bound_quote_in_an_arbitrary_audit_file_cannot_bypass_hygiene(self) -> None:
        quote = "/home/nkgarg/secret-private-workflow"
        payload = {
            "quoted_text": quote,
            "quoted_text_sha256": hashlib.sha256(quote.encode("utf-8")).hexdigest(),
            "publication_locator": "https://arxiv.org/abs/1234.5678",
            "line_start": 1,
            "line_end": 1,
        }
        with self.assertRaisesRegex(projection.ProjectionError, "local /tmp or /home path"):
            projection.project_bytes(
                "papers/Fixture/audit/record.json",
                json.dumps(payload).encode("utf-8"),
            )

    def test_bound_source_anchor_cannot_publish_a_local_workstation_path(self) -> None:
        quote = "/home/nkgarg/secret-private-workflow"
        payload = {
            "items": {
                "claim": {
                    "source_anchor": {
                        "path": "source.txt",
                        "line_start": 1,
                        "line_end": 1,
                        "quoted_text": quote,
                        "quoted_text_sha256": hashlib.sha256(
                            quote.encode("utf-8")
                        ).hexdigest(),
                    }
                }
            }
        }
        with self.assertRaisesRegex(projection.ProjectionError, "local /tmp or /home path"):
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json",
                json.dumps(payload).encode("utf-8"),
            )

    def test_private_url_is_rejected_before_public_url_masking(self) -> None:
        payload = {
            "reference_url": "https://github.com/nikhgarg/EconCSLib-private/tree/main/tmp/secret"
        }
        with self.assertRaisesRegex(projection.ProjectionError, "private repository"):
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json",
                json.dumps(payload).encode("utf-8"),
            )

    def test_percent_encoded_private_url_is_rejected_before_public_url_masking(self) -> None:
        payload = {
            "reference_url": "https://github.com/nikhgarg/EconCSLib%2Dprivate/tree/main"
        }
        with self.assertRaisesRegex(projection.ProjectionError, "private repository"):
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json",
                json.dumps(payload).encode("utf-8"),
            )

    def test_html_entity_encoded_private_url_is_rejected_before_public_url_masking(self) -> None:
        payload = {
            "reference_url": "https://github.com/nikhgarg/EconCSLib&#45;private/tree/main"
        }
        with self.assertRaisesRegex(projection.ProjectionError, "private repository"):
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json",
                json.dumps(payload).encode("utf-8"),
            )

    def test_already_public_safe_json_keeps_its_exact_bytes(self) -> None:
        raw = b'{"paper":"Fixture", "source_url":"https://arxiv.org/abs/1"}\n'
        self.assertEqual(
            projection.project_bytes("papers/Fixture/status.json", raw), raw
        )

    def test_text_projection_rewrites_known_workflow_labels(self) -> None:
        raw = (
            "\\textbf{Source version:} arXiv source; byte-pinned private text extraction\\\\\n"
            "The remediation handoff references /tmp/econcslib/source.txt.\n"
        ).encode("utf-8")
        projected = projection.project_bytes("papers/Fixture/docs/HUMAN_REVIEW_PACKET.tex", raw)
        text = projected.decode("utf-8")
        self.assertNotIn("private text extraction", text.lower())
        self.assertNotIn("remediation handoff", text.lower())
        self.assertNotIn("/tmp/", text)
        self.assertIn("publication source record", text)

        notes = projection.project_bytes(
            "papers/Fixture/docs/HUMAN_REVIEW_PACKET.tex",
            b"Local workflow: PAPER_NOTES.md\n",
        ).decode("utf-8")
        self.assertNotIn("PAPER_NOTES", notes)
        self.assertIn("source-review record", notes)

        workflow = projection.project_bytes(
            "site/index.html",
            (
                b"New paper formalizations should start in a private workflow and be\n"
                b"            proposed to enter the library through a pull request when ready.\n"
            ),
        ).decode("utf-8")
        self.assertIn("private workflow", workflow)

        repository = projection.project_bytes(
            "docs/ordinary-guide.md",
            b"Work in a private repository until the branch is ready.\n",
        ).decode("utf-8")
        self.assertNotIn("private repository", repository)
        self.assertIn("development repository", repository)

        tutorial = b'SOURCE_ARTIFACT=".scratch/$PAPER/source.pdf"\n'
        public_tutorial = projection.project_bytes(
            "docs/ordinary-guide.md", tutorial
        ).decode("utf-8")
        self.assertNotIn(".scratch", public_tutorial)
        self.assertNotIn("source.pdf", public_tutorial)
        self.assertIn("cited publication", public_tutorial)

        navigation = projection.project_bytes(
            "docs/PUBLIC_RELEASE_CHECKLIST.md",
            b"Open site/index.html and compile docs/DependencyDAG.tex.\n",
        ).decode("utf-8")
        self.assertIn("site/index.html", navigation)
        self.assertIn("docs/DependencyDAG.tex", navigation)
        self.assertNotIn("cited publication", navigation)

    def test_public_http_source_url_is_not_rewritten_as_a_local_locator(self) -> None:
        url = "https://arxiv.org/e-print/2601.00001/source/main.tex"
        projected = json.loads(
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json",
                json.dumps({"source_url": url}).encode("utf-8"),
            )
        )
        self.assertEqual(projected["source_url"], url)

    def test_ordinary_html_namespace_and_packet_pdf_path_are_not_source_locators(self) -> None:
        payload = {
            "lean_import_closure": {"external_import_modules": ["ProofWidgets.Data.Html"]},
            "artifacts": {
                "human_review_packet_pdf": (
                    "papers/Fixture/docs/HUMAN_REVIEW_PACKET.pdf"
                )
            },
        }
        projected = json.loads(
            projection.project_bytes(
                "papers/Fixture/audit/source_record_audit.json",
                json.dumps(payload).encode("utf-8"),
            )
        )
        self.assertEqual(projected, payload)

    def test_lean_comment_projection_neutralizes_private_transcript_locator(self) -> None:
        raw = (
            b"/-- Source anchor: source_tex/sections/theorem.tex, lines 2--18. -/\n"
            b"def semantic_target : Prop := True\n"
        )
        projected = projection.project_bytes(
            "papers/Fixture/Assumptions.lean", raw
        ).decode("utf-8")
        self.assertNotIn("source_tex/sections/theorem.tex", projected)
        self.assertIn(projection.PUBLICATION_LOCATOR, projected)
        self.assertIn("def semantic_target : Prop := True", projected)

    def test_source_evidence_keeps_its_mathematical_summary_without_private_notes(self) -> None:
        payload = {
            "source_evidence": (
                "Source basis: /tmp/econcs_source_text/Fixture.txt, PAPER_NOTES.md, "
                "and local PDF cache. Lemma 1 assumes a finite item universe."
            )
        }

        projected = json.loads(
            projection.project_bytes(
                "papers/Fixture/audit/paper_coverage_llm.json",
                json.dumps(payload).encode("utf-8"),
            )
        )

        evidence = projected["source_evidence"]
        self.assertIn("Lemma 1 assumes a finite item universe.", evidence)
        self.assertNotIn("/tmp", evidence)
        self.assertNotIn("PAPER_NOTES", evidence)
        self.assertNotIn("local PDF cache", evidence)

    def test_status_source_transcript_names_become_citation_records(self) -> None:
        payload = {
            "artifacts": {
                "source_tex": "papers/Fixture/source_tex/arxiv.tex",
                "journal_source_transcript": "sources/article.txt",
            }
        }
        projected = json.loads(
            projection.project_bytes(
                "papers/Fixture/status.json", json.dumps(payload).encode("utf-8")
            )
        )
        self.assertEqual(projected["artifacts"]["source_tex"], "cited publication record")
        self.assertEqual(
            projected["artifacts"]["journal_source_transcript"],
            "cited publication record",
        )

    def test_transcript_locators_are_neutralized_outside_verbatim_source(self) -> None:
        payload = {
            "reason": (
                "Compare source.txt., sources/2101.05853.txt:12, and "
                "source_tex/main.tex:3."
            ),
            "source_evidence": "The proof uses audit/source_archive_surface.tex:20.",
            "source_anchor": {
                "path": "source.txt",
                "line_start": 1,
                "line_end": 1,
                "quoted_text": "The cited source itself says sources/2101.05853.txt.",
                "quoted_text_sha256": hashlib.sha256(
                    b"The cited source itself says sources/2101.05853.txt."
                ).hexdigest(),
            },
        }

        projected = json.loads(
            projection.project_bytes(
                "papers/Fixture/audit/source_record_match_llm.json",
                json.dumps(payload).encode("utf-8"),
            )
        )

        self.assertNotIn("sources/2101.05853.txt", projected["reason"])
        self.assertNotIn("source.txt", projected["reason"])
        self.assertNotIn("source_tex/main.tex", projected["reason"])
        semantic_match = json.loads(
            projection.project_bytes(
                "papers/Fixture/audit/source_record_match_llm.json",
                json.dumps(
                    {"source_anchor": {"semantic_match": "See Fixture.txt:12."}}
                ).encode("utf-8"),
            )
        )
        self.assertNotIn("Fixture.txt", semantic_match["source_anchor"]["semantic_match"])
        self.assertEqual(
            projected["source_anchor"]["quoted_text"],
            payload["source_anchor"]["quoted_text"],
        )
        archive = projection.project_bytes(
            "papers/Fixture/audit/statement_match_llm.json",
            b'{"reason":"Checked source.tar member source.txt."}',
        ).decode("utf-8")
        self.assertNotIn("source.tar", archive)
        self.assertNotIn("source.txt", archive)
        archive_field = json.loads(
            projection.project_bytes(
                "papers/Fixture/status.json",
                b'{"artifacts":{"source_archive":"papers/Fixture/source.tar.gz"}}',
            )
        )
        self.assertEqual(
            archive_field["artifacts"]["source_archive"],
            "cited publication",
        )
        archive_object = json.loads(
            projection.project_bytes(
                "papers/Fixture/status.json",
                b'{"formalization_scope":{"base_archive":{"path":"source.tar.gz","sha256":"abc"}}}',
            )
        )
        self.assertEqual(
            archive_object["formalization_scope"]["base_archive"]["path"],
            "cited publication",
        )
        provenance = json.loads(
            projection.project_bytes(
                "papers/Fixture/audit/source_proof_fidelity.json",
                b'{"provenance":"A clarification of source.tar.gz."}',
            )
        )
        self.assertNotIn("source.tar", provenance["provenance"])
        self.assertIn("cited publication", provenance["provenance"])
        self.assertNotIn("audit/source_archive_surface.tex", projected["source_evidence"])
        self.assertIn(projection.PUBLICATION_LOCATOR, projected["reason"])

    def test_strict_private_anchor_schemas_become_public_display_records(self) -> None:
        quote = "The source uses the standard term at this exact location."
        anchor = {
            "path": "source.txt",
            "line_start": 7,
            "line_end": 7,
            "quoted_text": quote,
            "quoted_text_sha256": hashlib.sha256(quote.encode("utf-8")).hexdigest(),
        }
        payload = {
            "items": {
                "standard_term": {
                    "source_standard_term_interpretation": {
                        "source_term_use_anchor": anchor,
                        "standard_interpretation": "A public mathematical explanation.",
                    }
                },
                "partitioned_definition": {
                    "source_definition_partition": {
                        "components": [
                            {
                                "source_location": "source.txt:7",
                                "source_anchor_evidence": [anchor],
                            }
                        ]
                    }
                },
            }
        }
        projected = json.loads(
            projection.project_bytes(
                "papers/Fixture/audit/paper_statement_map.json",
                json.dumps(payload).encode("utf-8"),
            )
        )
        standard = projected["items"]["standard_term"]
        self.assertNotIn("source_standard_term_interpretation", standard)
        public_standard = standard["publication_standard_term_interpretation"]
        self.assertNotIn("path", public_standard["source_term_use_anchor"])
        self.assertEqual(
            public_standard["source_term_use_anchor"]["publication_locator"],
            projection.PUBLICATION_LOCATOR,
        )
        definition = projected["items"]["partitioned_definition"]
        self.assertNotIn("source_definition_partition", definition)
        public_partition = definition["publication_source_definition_partition"]
        public_anchor = public_partition["components"][0]["source_anchor_evidence"][0]
        self.assertNotIn("path", public_anchor)
        self.assertEqual(public_anchor["publication_locator"], projection.PUBLICATION_LOCATOR)
        self.assertEqual(
            public_partition["components"][0]["source_location"],
            f"{projection.PUBLICATION_LOCATOR}:7",
        )

    def test_real_public_maps_preserve_strict_map_shape_by_renaming_private_audit_records(
        self,
    ) -> None:
        root = Path(__file__).resolve().parents[2]
        for paper in (
            "GCG24UserItemFairness",
            "LG21TestOptionalPolicies",
            "GHW01DigitalGoods",
        ):
            relative = f"papers/{paper}/audit/paper_statement_map.json"
            projected = json.loads(
                projection.project_bytes(relative, (root / relative).read_bytes())
            )
            self.assertFalse(
                any(
                    "source_standard_term_interpretation" in item
                    or "source_definition_partition" in item
                    for item in projected["items"].values()
                ),
                paper,
            )
            self.assertFalse(
                source_map_structural_errors(projected["items"]), paper
            )

    def test_approved_source_tex_and_contributor_workflow_are_byte_preserved(self) -> None:
        raw = b"% source excerpt: /tmp and .audit_source and private text extraction\n"
        self.assertEqual(
            projection.project_bytes("papers/Fixture/source/main.tex", raw), raw
        )
        for relative in projection.PUBLIC_CONTRIBUTOR_WORKFLOW_PATHS:
            with self.subTest(relative=relative):
                self.assertEqual(projection.project_bytes(relative, raw), raw)

    def test_formalizer_skill_keeps_its_complete_public_workflow_entrypoint(self) -> None:
        root = Path(__file__).resolve().parents[2]
        relative = "skills/econcs-formalizer/SKILL.md"
        projected = projection.project_bytes(relative, (root / relative).read_bytes()).decode(
            "utf-8"
        )

        self.assertIn("EconCSLib-private", projected)
        self.assertIn("references/formalization-handbook.md", projected)
        self.assertIn("references/public-private-sync.md", projected)
        self.assertIn("private source review", projected.lower())
        self.assertIn(".review_traces", projected)
        self.assertIn("raw-source-to-expanded-Spec", projected)
        self.assertEqual(
            projection.project_bytes(relative, projected.encode("utf-8")).decode("utf-8"),
            projected,
        )


if __name__ == "__main__":
    unittest.main()
