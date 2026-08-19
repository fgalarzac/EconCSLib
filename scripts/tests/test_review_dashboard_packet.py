from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from scripts import review_dashboard_packet as packet


class ReviewDashboardPacketTests(unittest.TestCase):
    def test_packet_template_includes_fresh_clone_dashboard_instructions(self) -> None:
        """A recipient of a packet can open its interactive counterpart."""

        template = packet.TEMPLATE_PATH.read_text(encoding="utf-8")
        self.assertIn(r"\section*{Open the interactive dashboard}", template)
        self.assertIn(
            "optional alternative to using this PDF",
            template,
        )
        self.assertIn("lake exe cache get", template)
        self.assertIn("review_dashboard.py --paper @@PAPER_ID@@ --serve", template)
        self.assertIn("reviewer-owned review record", template)
        self.assertNotIn("local\nreview trace", template)

    def test_packet_public_projection_sanitizes_preescaped_locator_but_not_verbatim_source(self) -> None:
        rendered = packet._public_packet_presentation_tex(
            "\\textbf{Source locator:} {\\footnotesize\\raggedright "
            "audit/\\allowbreak{}source\\_archive\\_surface.\\allowbreak{}tex:"
            "\\allowbreak{}12-\\allowbreak{}15\\par}\n"
            "\\begin{ReviewVerbatim}\n"
            "The raw excerpt may itself mention source_archive_surface.tex.\n"
            "\\end{ReviewVerbatim}\n",
            paper="Fixture",
        )
        self.assertNotIn("audit/\\allowbreak{}source", rendered)
        self.assertIn("cited publication, lines 12-\\allowbreak{}15", rendered)
        self.assertIn(
            "The raw excerpt may itself mention source_archive_surface.tex.",
            rendered,
        )

    def test_existing_packet_refreshes_reviewer_record_wording(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            tex_path = Path(temp_dir) / "HUMAN_REVIEW_PACKET.tex"
            tex_path.write_text(
                "The dashboard records saved annotations in this paper's local\n"
                "review trace.\n",
                encoding="utf-8",
            )
            rendered = packet.sanitize_existing_packet("Fixture", tex_path)
        self.assertIn("reviewer-owned review record", rendered)
        self.assertNotIn("local\nreview trace", rendered)

    def test_verbatim_marks_nonprintable_source_bytes_without_dropping_them(self) -> None:
        rendered = packet._verbatim("before\fafter\x0fend")
        self.assertIn("[form-feed in source extraction]", rendered)
        self.assertIn("[U+000F control character]", rendered)

    def test_verbatim_preserves_plain_text_norm_delimiters_when_font_lacks_unicode(self) -> None:
        rendered = packet._verbatim("∥u - v∥")
        self.assertIn("||u - v||", rendered)
        self.assertNotIn("\x0f", rendered)

    def test_unmarked_packet_requires_an_active_v11_surface(self) -> None:
        self.assertIn(
            "has not explicitly activated",
            packet._v11_packet_surface_error({}, {"semantic_contract_schema": 1}),
        )
        self.assertIn(
            "has not prepared",
            packet._v11_packet_surface_error(
                {"review_surface": {"require_v11_raw_source_spec_screening": True}},
                {},
            ),
        )
        self.assertEqual(
            packet._v11_packet_surface_error(
                {"review_surface": {"require_v11_raw_source_spec_screening": True}},
                {"semantic_contract_schema": 1},
            ),
            "",
        )

    def test_pending_review_notice_is_front_matter_only(self) -> None:
        self.assertIn(
            "0/2 source-claim screens; 1/3 library prerequisite screens",
            packet._review_readiness_notice(
                [{"llm_match_current": False}, {"llm_match_current": False}],
                [
                    {"semantic_current": True},
                    {"semantic_current": False},
                    {"semantic_current": False},
                ],
            ),
        )
        self.assertEqual(
            packet._review_readiness_notice(
                [{"llm_match_current": True}],
                [{"semantic_current": True}],
            ),
            "",
        )

    def test_public_arxiv_tex_source_is_accepted(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper_dir = root / "papers" / "PacketPaper"
            (paper_dir / "audit").mkdir(parents=True)
            source_bytes = b"\\begin{document}official source\\end{document}\n"
            (paper_dir / "source").mkdir()
            (paper_dir / "source" / "main.tex").write_bytes(source_bytes)
            (paper_dir / "audit" / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_url": "https://arxiv.org/abs/2601.00001v1",
                        "source_artifact_path": "source/main.tex",
                        "source_artifact_sha256": hashlib.sha256(source_bytes).hexdigest(),
                    }
                ),
                encoding="utf-8",
            )
            with mock.patch.object(packet, "ROOT", root):
                self.assertEqual(packet.public_arxiv_tex_source_error("PacketPaper"), "")

    def test_non_arxiv_source_is_not_a_public_excerpt_exception(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper_dir = root / "papers" / "PacketPaper"
            (paper_dir / "audit").mkdir(parents=True)
            (paper_dir / "audit" / "paper_statement_map.json").write_text(
                json.dumps(
                    {
                        "source_url": "https://doi.org/10.1000/example",
                        "source_artifact_path": "source/main.tex",
                        "source_artifact_sha256": "a" * 64,
                    }
                ),
                encoding="utf-8",
            )
            with mock.patch.object(packet, "ROOT", root):
                self.assertIn(
                    "official arXiv", packet.public_arxiv_tex_source_error("PacketPaper")
                )

    def test_source_anchor_accepts_safe_repository_relative_paper_path(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            root = Path(temp_dir)
            paper_dir = root / "papers" / "PacketPaper"
            source = paper_dir / "source" / "main.tex"
            source.parent.mkdir(parents=True)
            source.write_text("exact source line\n", encoding="utf-8")
            record = {
                "source_anchor_evidence": [
                    {
                        "path": "papers/PacketPaper/source/main.tex",
                        "line_start": 1,
                        "line_end": 1,
                        "quoted_text": "exact source line",
                    }
                ]
            }
            with mock.patch.object(packet.review_dashboard, "ROOT", root):
                self.assertEqual(
                    packet.review_dashboard.source_anchor_file_error(paper_dir, record),
                    "",
                )

    def test_packet_uses_one_source_and_one_interface_block(self) -> None:
        record = {
            "source_item": "Theorem 1",
            "source_location": "source/main.tex:1-2",
            "statement": "The source statement.",
            "source_anchor_evidence": [{"quoted_text": "Exact source text."}],
        }
        row = packet._row_tex(
            {
                "name": "endpoint",
                "kind": "theorem",
                "full_name": "Paper.endpoint",
                "interface_source": "theorem endpoint : P := by exact h",
                "lean_statement": "def endpointSpec : Prop := P",
                "verbatim_source_input": "Exact source text.",
                "agent_statement": "P.",
                "llm_match_judgment": "match",
                "llm_match_reason": "Same conclusion.",
            },
            [record],
            "Paper.endpoint",
            1,
        )
        self.assertIn("Verbatim source input", row)
        self.assertIn("Expanded PaperInterface specification", row)
        self.assertIn("Exact source text.", row)
        self.assertNotIn("The source statement.", row)
        self.assertNotIn("\\textbf{Kind:}", row)

    def test_presentation_sections_reorder_cards_without_dropping_any(self) -> None:
        main = ({"full_name": "Paper.mainSpec"}, [], "Paper.main_realizes_spec")
        appendix = ({"full_name": "Paper.appendixSpec"}, [], "Paper.appendix_realizes_spec")
        grouped = packet._claim_presentation_sections(
            {
                "review_surface": {
                    "presentation_sections": [
                        {"title": "Main-text source claims", "names": ["main"]},
                        {"title": "Appendix source claims", "names": ["appendix"]},
                    ]
                }
            },
            [main, appendix],
        )
        self.assertEqual(
            [(title, [row[0]["full_name"] for row in rows]) for title, rows in grouped],
            [
                ("Main-text source claims", ["Paper.mainSpec"]),
                ("Appendix source claims", ["Paper.appendixSpec"]),
            ],
        )

    def test_packet_contents_links_prerequisites_and_source_claims(self) -> None:
        claim = ({"full_name": "Paper.mainSpec", "name": "mainSpec"}, [{"source_item": "Theorem 1"}], "Paper.main")
        contents = packet._contents_tex(
            Path("/tmp/PacketPaper"),
            [("Main-text source claims", [claim])],
            [{"lean_name": "EconCSLib.Model", "label": "Model", "direct_library_declarations": []}],
        )
        self.assertIn("Semantic library prerequisites (1; not paper claims)", contents)
        self.assertIn("Main-text source claims (1)", contents)
        self.assertIn("Theorem 1", contents)
        self.assertIn("\\hyperlink{", contents)

    def test_presentation_sections_preserve_dag_order_with_continued_heading(self) -> None:
        main = ({"full_name": "Paper.mainSpec"}, [], "Paper.main_realizes_spec")
        appendix = ({"full_name": "Paper.appendixSpec"}, [], "Paper.appendix_realizes_spec")
        grouped = packet._claim_presentation_sections(
            {
                "review_surface": {
                    "presentation_sections": [
                        {"title": "Main-text source claims", "names": ["main"]},
                        {"title": "Appendix source claims", "names": ["appendix"]},
                    ]
                }
            },
            [appendix, main],
        )
        self.assertEqual(
            [(title, [row[0]["full_name"] for row in rows]) for title, rows in grouped],
            [
                ("Appendix source claims", ["Paper.appendixSpec"]),
                ("Main-text source claims", ["Paper.mainSpec"]),
            ],
        )

    def test_claim_rows_coalesce_spec_and_proof_in_intake_order(self) -> None:
        with tempfile.TemporaryDirectory() as temp_dir:
            paper_dir = Path(temp_dir)
            (paper_dir / "audit").mkdir()
            (paper_dir / "audit" / "intake_freeze.json").write_text(
                json.dumps(
                    {
                        "items": [
                            {
                                "spec_declaration": "secondSpec",
                                "proof_declaration": "second",
                                "dependency_order": 2,
                            },
                            {
                                "spec_declaration": "firstSpec",
                                "proof_declaration": "first",
                                "dependency_order": 1,
                            },
                        ]
                    }
                ),
                encoding="utf-8",
            )
            source_map = {
                "items": {
                    "second": {
                        "semantic_contract": {
                            "spec_declaration": "Packet.secondSpec",
                            "evidence_declaration": "Packet.second",
                        }
                    },
                    "first": {
                        "semantic_contract": {
                            "spec_declaration": "Packet.firstSpec",
                            "evidence_declaration": "Packet.first",
                        }
                    },
                }
            }
            dashboard_items = [
                {"full_name": "Packet.firstSpec", "name": "firstSpec"},
                {"full_name": "Packet.first", "name": "first"},
                {"full_name": "Packet.secondSpec", "name": "secondSpec"},
                {"full_name": "Packet.second", "name": "second"},
            ]
            selected = packet._claim_review_rows(paper_dir, source_map, dashboard_items)

        self.assertEqual(
            [(item["full_name"], proof) for item, _records, proof in selected],
            [("Packet.firstSpec", "Packet.first"), ("Packet.secondSpec", "Packet.second")],
        )

    def test_v11_claim_rows_exclude_unrouted_helpers_and_assumptions(self) -> None:
        """The packet remains source-contract claim-only despite dashboard assumption cards."""

        with tempfile.TemporaryDirectory() as temp_dir:
            paper_dir = Path(temp_dir)
            source_map = {
                "semantic_contract_schema": 1,
                "items": {
                    "claim": {
                        "semantic_contract": {
                            "spec_declaration": "Packet.claimSpec",
                            "evidence_declaration": "Packet.claim",
                        }
                    }
                },
            }
            dashboard_items = [
                {"full_name": "Packet.claimSpec", "name": "claimSpec"},
                {"full_name": "Packet.helperSpec", "name": "helperSpec"},
                {
                    "full_name": "Packet.modelAssumption",
                    "name": "modelAssumption",
                    "is_assumption": True,
                },
            ]
            selected = packet._claim_review_rows(paper_dir, source_map, dashboard_items)

        self.assertEqual(
            [(item["full_name"], proof) for item, _records, proof in selected],
            [("Packet.claimSpec", "Packet.claim")],
        )

    def test_prerequisites_show_exact_library_definition_and_source_connection(self) -> None:
        rendered = packet._prerequisites_tex(
            packet.ROOT / "papers" / "HT26EFXChores",
            [
                {
                    "interface_source": (
                        "EconCSLib.FairDivision.Bundle Item → "
                        "EconCSLib.FairDivision.Allocation Agent Item"
                    )
                }
            ],
            semantic_targets_override={
                "EconCSLib.FairDivision.Bundle": {
                    "display": "abbrev EconCSLib.FairDivision.Bundle (Item : Type*) := Finset Item",
                    "declaration_kind": "abbrev",
                    "direct_library_declarations": (),
                },
                "EconCSLib.FairDivision.Allocation": {
                    "display": "abbrev EconCSLib.FairDivision.Allocation (Agent Item : Type*) := Agent → EconCSLib.FairDivision.Bundle Item",
                    "declaration_kind": "abbrev",
                    "direct_library_declarations": (),
                },
            },
            semantic_target_errors_override={},
        )

        self.assertIn("Material library prerequisites", rendered)
        self.assertIn("Lean-expanded library semantic target", rendered)
        self.assertIn("Exact Lean library declaration", rendered)
        self.assertGreaterEqual(rendered.count(r"\clearpage"), 1)
        self.assertIn(r"\hypertarget{library-prerequisite-", rendered)
        self.assertIn("abbrev Bundle (Item : Type*) := Finset Item", rendered)
        self.assertIn("abbrev Allocation (Agent Item : Type*) := Agent → Bundle Item", rendered)
        self.assertNotIn("the same byte-pinned source bundle shown for", rendered)
        self.assertIn(r"\textbf{Verdict:} \texttt{", rendered)
        self.assertNotIn(r"\textbf{Status:}", rendered)
        self.assertIn(r"\reviewmatch", rendered)
        self.assertIn(r"\textbf{Reviewer annotation}", rendered)

    def test_paper_prerequisite_shows_one_expanded_semantic_target(self) -> None:
        rendered = packet._paper_prerequisites_tex(
            [
                {
                    "lean_name": "Packet.Model",
                    "verbatim_source_input": "The model is finite.",
                    "source_locator": "source/main.tex:1",
                    "paper_semantic_target": "def Packet.Model := Fin 2",
                    "paper_semantic_target_kind": "definition",
                    "paper_declaration_source": "def Model := Fin 2",
                    "semantic_judgment": "matches",
                    "semantic_reason": "The source names the finite model.",
                }
            ]
        )

        self.assertIn("Verbatim paper-source connection", rendered)
        self.assertIn("Lean-expanded paper semantic target", rendered)
        self.assertIn("def Packet.Model := Fin 2", rendered)
        self.assertNotIn("Exact Lean paper declaration", rendered)
        self.assertNotIn("def Model := Fin 2", rendered)

    def test_prerequisite_cards_are_dependency_first(self) -> None:
        entries = [
            {"lean_name": "Packet.ClaimModel", "direct_paper_declarations": ["Packet.BaseModel"]},
            {"lean_name": "Packet.BaseModel", "direct_paper_declarations": []},
        ]
        ordered = packet._dependency_first_entries(
            entries,
            name_field="lean_name",
            dependency_field="direct_paper_declarations",
        )
        self.assertEqual(
            [entry["lean_name"] for entry in ordered],
            ["Packet.BaseModel", "Packet.ClaimModel"],
        )

    def test_corrected_source_target_is_visible_and_not_a_raw_match(self) -> None:
        record = {
            "source_location": "source/main.tex:1-2",
            "source_anchor_evidence": [{"quoted_text": "False archival text."}],
            "coverage_status": "corrected_source_statement",
            "corrected_target": {
                "statement": "The approved corrected proposition.",
                "archival_source_locator": "source/main.tex:1-2",
                "approval": {"reference": "Recorded source clarification."},
            },
        }
        row = packet._row_tex(
            {
                "verbatim_source_input": "False archival text.",
                "semantic_expanded_statement": "def claimSpec : Prop := True",
                "llm_match_judgment": "matches_approved_corrected_target",
                "llm_match_reason": "The corrected target matches the Spec.",
            },
            [record],
            "Paper.claim",
            1,
        )
        self.assertIn("Approved corrected review target", row)
        self.assertIn("The approved corrected proposition.", row)
        self.assertIn("Recorded source clarification.", row)
        self.assertIn("Matches approved corrected target", row)
        self.assertNotIn("\\reviewmatch{Matches source input}", row)
