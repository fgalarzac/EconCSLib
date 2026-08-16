#!/usr/bin/env python3
"""Regression tests for source-only named-result discovery and reconciliation."""

from __future__ import annotations

import hashlib
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
for import_root in (ROOT, ROOT / "scripts"):
    import_root_text = str(import_root)
    if import_root_text not in sys.path:
        sys.path.insert(0, import_root_text)

import source_named_result_index as index  # noqa: E402


def exact_anchor(
    source_text: str, path: str, line_start: int, line_end: int
) -> dict[str, object]:
    normalized = source_text.replace("\r\n", "\n").replace("\r", "\n")
    lines = normalized.split("\n")
    if normalized.endswith("\n"):
        lines.pop()
    quote = "\n".join(lines[line_start - 1 : line_end])
    return {
        "path": path,
        "line_start": line_start,
        "line_end": line_end,
        "quoted_text": quote,
        "quoted_text_sha256": hashlib.sha256(quote.encode("utf-8")).hexdigest(),
    }


class SourceNamedResultIndexTests(unittest.TestCase):
    def test_text_extractor_recognizes_each_supported_presentation_kind(self) -> None:
        source_text = (
            "Theorem 1. Result.\n"
            "Proposition 2. Result.\n"
            "Lemma 3. Result.\n"
            "Corollary 4. Result.\n"
            "Claim 5. Result.\n"
            "Definition 6. Vocabulary.\n"
            "Equation (7). Constraint.\n"
            "Formula 8. Expression.\n"
            "Algorithm 9. Procedure.\n"
            "Assumption A. Condition.\n"
        )

        presentations = index.extract_text_named_result_presentations(source_text)

        self.assertEqual(
            [presentation.kind for presentation in presentations],
            [
                "theorem",
                "proposition",
                "lemma",
                "corollary",
                "claim",
                "definition",
                "equation",
                "formula",
                "algorithm",
                "assumption",
            ],
        )

    def test_line_wrapped_prose_reference_is_not_a_named_result_heading(self) -> None:
        source_text = (
            "Figure 5: Simulation results illustrate\n"
            "Theorem 2: the argmax rule maximizes accuracy.\n"
            "The discussion invokes\n"
            "Lemma 4: the auxiliary bound.\n"
            "Figure 6: A completed caption.\n"
            "Theorem 3: A genuine adjacent theorem.\n"
            "Figure 7: An unfinished caption\n"
            "\n"
            "Theorem 4: A genuine separated theorem.\n"
        )

        presentations = index.extract_text_named_result_presentations(source_text)

        self.assertEqual(
            [(item.kind, item.label, item.line_start) for item in presentations],
            [
                ("theorem", "Theorem 3", 6),
                ("theorem", "Theorem 4", 9),
            ],
        )

    def test_text_headings_extract_supported_named_kinds_and_source_spans(self) -> None:
        source_text = (
            "Introduction.\n"
            "\n"
            "Theorem 1. Every admissible input has a witness.\n"
            "The conclusion continues on this source line.\n"
            "\n"
            "Algorithm 2: Construct the witness.\n"
            "The procedure has one finite step.\n"
            "\n"
            "Assumption A. The parameter is positive.\n"
            "The condition applies throughout this section.\n"
            "\n"
            "Theorem 3 proves the preceding result.\n"
            "Definition B. The designated object is the witness.\n"
        )

        presentations = index.extract_text_named_result_presentations(source_text)

        self.assertEqual(
            [
                (item.kind, item.label, item.line_start, item.line_end)
                for item in presentations
            ],
            [
                ("theorem", "Theorem 1", 3, 4),
                ("algorithm", "Algorithm 2", 6, 7),
                # The transcript's blank line does not prove the Assumption
                # ended; its trailing source prose remains in the conservative
                # source span until Definition B's next named boundary.
                ("assumption", "Assumption A", 9, 12),
                ("definition", "Definition B", 13, 13),
            ],
        )

    def test_text_heading_keeps_blank_line_continuations_until_real_boundary(self) -> None:
        source_text = (
            "Definition 1. A profile is admissible.\n"
            "\n"
            "The displayed equality is part of the definition.\n"
            "\n"
            "Proposition 5. The stated identity holds.\n"
            "Proof. The proof starts here.\n"
            "Lemma D.2. For every admissible parameter, the bound holds.\n"
            "\n"
            "Its displayed limiting conclusion also holds.\n"
            "\n"
            "Proof of Lemma D.2.\n"
        )

        presentations = index.extract_text_named_result_presentations(source_text)

        self.assertEqual(
            [
                (item.kind, item.label, item.line_start, item.line_end)
                for item in presentations
            ],
            [
                ("definition", "Definition 1", 1, 3),
                ("proposition", "Proposition 5", 5, 5),
                ("lemma", "Lemma D.2", 7, 9),
            ],
        )
        lemma = presentations[-1]
        self.assertFalse(
            index.byte_pinned_anchor_covers_presentation(
                exact_anchor(source_text, "source.txt", 7, 7),
                lemma,
                source_text=source_text,
                source_path="source.txt",
            )
        )
        self.assertTrue(
            index.byte_pinned_anchor_covers_presentation(
                exact_anchor(source_text, "source.txt", 7, 9),
                lemma,
                source_text=source_text,
                source_path="source.txt",
            )
        )

    def test_text_heading_stops_at_conservative_section_boundaries(self) -> None:
        source_text = (
            "Lemma 1. The premise holds.\n"
            "\n"
            "Its displayed conclusion holds.\n"
            "\n"
            "Conclusion\n"
            "This is later paper prose.\n"
            "\n"
            "Proposition 2. A separate result holds.\n"
            "\n"
            "Its conclusion is source-visible.\n"
            "\n"
            "2. Further Results\n"
            "Later section prose.\n"
        )

        presentations = index.extract_text_named_result_presentations(source_text)

        self.assertEqual(
            [
                (item.kind, item.label, item.line_start, item.line_end)
                for item in presentations
            ],
            [
                ("lemma", "Lemma 1", 1, 3),
                ("proposition", "Proposition 2", 8, 10),
            ],
        )

    def test_subpart_discovery_survives_table_boundary_between_siblings(self) -> None:
        source_text = (
            "Theorem 1. The following independent conclusions hold.\n"
            "(i) The first conclusion holds.\n"
            "(ii) The second conclusion holds.\n"
            "\n"
            "Table 1. Values used in the illustration.\n"
            "\n"
            "(iii) The third conclusion holds.\n"
            "Proof.\n"
        )

        presentations = index.extract_text_named_result_presentations(source_text)

        self.assertEqual(
            [
                (item.kind, item.label, item.line_start, item.line_end)
                for item in presentations
            ],
            [
                ("theorem", "Theorem 1(i)", 2, 2),
                ("theorem", "Theorem 1(ii)", 3, 3),
                ("theorem", "Theorem 1(iii)", 7, 7),
            ],
        )

    def test_conditional_subparts_remain_one_named_result(self) -> None:
        source_text = (
            "Proposition 1. Suppose a policy set S satisfies:\n"
            "(i) S has a finite linear description.\n"
            "(ii) An optimal policy belongs to S.\n"
            "(iii) That policy is unique in S.\n"
            "Then the stated linear program has the unique optimizer.\n"
            "Proof.\n"
        )

        presentations = index.extract_text_named_result_presentations(source_text)

        self.assertEqual(
            [
                (item.kind, item.label, item.line_start, item.line_end, item.presentation)
                for item in presentations
            ],
            [("proposition", "Proposition 1", 1, 5, "text_heading")],
        )
        self.assertTrue(
            index.source_text_uses_conditional_antecedent_subpart_selection(
                source_text
            )
        )

    def test_conditional_parser_does_not_hide_subpart_with_inline_then(self) -> None:
        """Only a statement-level consequent can collapse enumerated leaves."""

        source_text = (
            "Theorem 1. Suppose the model has finite support.\n"
            "(i) If the first condition holds, then the first conclusion holds.\n"
            "(ii) If the second condition holds, then the second conclusion holds.\n"
            "Proof.\n"
        )

        presentations = index.extract_text_named_result_presentations(source_text)

        self.assertEqual(
            [
                (item.kind, item.label, item.line_start, item.line_end, item.presentation)
                for item in presentations
            ],
            [
                ("theorem", "Theorem 1(i)", 2, 2, "text_heading_subpart"),
                ("theorem", "Theorem 1(ii)", 3, 3, "text_heading_subpart"),
            ],
        )
        self.assertFalse(
            index.source_text_uses_conditional_antecedent_subpart_selection(
                source_text
            )
        )

    def test_text_extractor_does_not_truncate_inline_decimal_cross_references(self) -> None:
        source_text = (
            "Lemma 9.2 we need for the construction is used below.\n"
            "Theorem 4.1 proves the main bound.\n"
            "Lemma 9.2. The actual displayed result.\n"
            "Corollary 4.2 The displayed conclusion begins immediately.\n"
        )

        presentations = index.extract_text_named_result_presentations(source_text)

        self.assertEqual(
            [(item.kind, item.label, item.line_start) for item in presentations],
            [
                ("lemma", "Lemma 9.2", 3),
                ("corollary", "Corollary 4.2", 4),
            ],
        )

    def test_text_extractor_recognizes_parenthesized_titles_and_result_subparts(
        self,
    ) -> None:
        source_text = (
            "Definition 1 (gamma-homogeneity). A profile is admissible.\n"
            "Theorem 2 (Asymptotic allocation). Assume the model hypotheses.\n"
            "(t) iid variables are sampled.\n"
            "(i) [Finite support] The first conclusion holds.\n"
            "(ii) [Continuous support] The second conclusion holds.\n"
            "Proof.\n"
            "Theorem 3 proves the preceding result.\n"
            "Lemma D.1(i): The inline part is source-visible.\n"
        )

        presentations = index.extract_text_named_result_presentations(source_text)

        self.assertEqual(
            [
                (item.kind, item.label, item.line_start, item.line_end, item.presentation)
                for item in presentations
            ],
            [
                ("definition", "Definition 1", 1, 1, "text_heading"),
                ("theorem", "Theorem 2(i)", 4, 4, "text_heading_subpart"),
                ("theorem", "Theorem 2(ii)", 5, 5, "text_heading_subpart"),
                ("lemma", "Lemma D.1(i)", 8, 8, "text_heading"),
            ],
        )

    def test_text_extractor_recovers_decimal_heading_from_interleaved_columns(self) -> None:
        source_text = (
            "The left column continues here Theorem 9.3 For every input, the bound holds.\n"
            "The discussion cites Theorem 9.3 but does not restate it.\n"
        )

        presentations = index.extract_text_named_result_presentations(source_text)

        self.assertEqual(
            [(item.kind, item.label, item.line_start) for item in presentations],
            [("theorem", "Theorem 9.3", 1)],
        )

    def test_tex_environments_extract_line_spans_and_ignore_unlabelled_algorithmic_blocks(
        self,
    ) -> None:
        source_text = (
            "\\begin{theorem}\\label{thm:main}\n"
            "Every admissible input has a witness.\n"
            "\\end{theorem}\n"
            "\\begin{algorithm}\n"
            "\\caption{Construct a witness}\\label{alg:construct}\n"
            "\\end{algorithm}\n"
            "\\begin{algorithmic}\n"
            "\\State auxiliary implementation detail\n"
            "\\end{algorithmic}\n"
            "\\begin{assumption}\n"
            "The parameter is positive.\n"
            "\\end{assumption}\n"
        )

        presentations = index.extract_tex_named_result_presentations(source_text)

        self.assertEqual(
            [
                (item.kind, item.label, item.line_start, item.line_end)
                for item in presentations
            ],
            [
                ("theorem", "thm:main", 1, 3),
                ("algorithm", "alg:construct", 4, 6),
                ("assumption", "assumption@10", 10, 12),
            ],
        )

    def test_tex_extractor_discovers_restatable_inner_results_without_macro_names(
        self,
    ) -> None:
        source_text = (
            "\\begin{restatable}{theorem}{opaqueMacroName}\\label{thm:main}\n"
            "Every admissible input has a witness.\n"
            "\\end{restatable}\n"
            "\\begin{restatable}[Optional visible title]{lemma}{anotherOpaqueMacro}\n"
            "The witness has the stated property.\n"
            "\\end{restatable}\n"
        )

        presentations = index.extract_tex_named_result_presentations(
            source_text,
            # The wrapper itself cannot reclassify its visible inner result.
            environment_kinds={"restatable": "definition"},
        )

        self.assertEqual(
            [
                (item.kind, item.label, item.line_start, item.line_end)
                for item in presentations
            ],
            [
                ("theorem", "thm:main", 1, 3),
                ("lemma", "lemma@4", 4, 6),
            ],
        )

    def test_tex_extractor_resolves_multiline_restatable_alias_from_source_title(
        self,
    ) -> None:
        source_text = (
            "\\newtheorem{sourcebox}{Proposition}\n"
            "\\begin{restatable}\n"
            "  {sourcebox}\n"
            "  {opaqueMacroName}\n"
            "  \\label{prop:box}\n"
            "Every admissible input has a witness.\n"
            "\\end{restatable}\n"
        )

        presentations = index.extract_tex_named_result_presentations(source_text)

        self.assertEqual(
            [
                (item.kind, item.label, item.line_start, item.line_end)
                for item in presentations
            ],
            [("proposition", "prop:box", 2, 7)],
        )

    def test_tex_extractor_keeps_unknown_restatable_inner_environment_unclassified(
        self,
    ) -> None:
        source_text = (
            "\\begin{restatable}{localresultshape}{opaqueMacroName}\n"
            "Every admissible input has a witness.\n"
            "\\end{restatable}\n"
        )

        presentations = index.extract_tex_named_result_presentations(source_text)

        self.assertEqual(
            [(item.kind, item.label) for item in presentations],
            [("unclassified", "localresultshape@1")],
        )

    def test_tex_extractor_requires_visible_formula_or_equation_presentation(
        self,
    ) -> None:
        source_text = (
            "\\begin{equation}\n"
            "x = y\n"
            "\\end{equation}\n"
            "\\begin{equation*}\\label{eq:labelled-star}\n"
            "u = v\n"
            "\\end{equation*}\n"
            "\\begin{equation*}\\tag{Equation 2}\n"
            "r = s\n"
            "\\end{equation*}\n"
            "\\begin{align}\n"
            "a &= b\\\\\n"
            "c &= d \\tag{Formula A}\n"
            "\\end{align}\n"
            "\\newtheorem{formula}{Formula}\n"
            "\\begin{formula}\\label{formula:main}\n"
            "p = q\n"
            "\\end{formula}\n"
            "\\begin{equation*}\\tag{(3)}\n"
            "r = s\n"
            "\\end{equation*}\n"
        )

        presentations = index.extract_tex_named_result_presentations(source_text)

        self.assertEqual(
            [
                (item.kind, item.label, item.line_start, item.line_end)
                for item in presentations
            ],
            [
                ("equation", "Equation 2", 7, 9),
                ("formula", "Formula A", 12, 12),
                ("formula", "formula:main", 15, 17),
            ],
        )

    def test_multiline_equation_displays_ignore_ordinary_numbers_and_labels(
        self,
    ) -> None:
        source_text = (
            "\\begin{align}\n"
            "a &= b \\label{eq:first}\\\\\n"
            "c &= d \\notag\\\\\n"
            "e &= f \\tag{T}\\\\\n"
            "g &= h\n"
            "\\end{align}\n"
            "\\begin{gather}\n"
            "p = q\\\\\n"
            "r = s \\label{eq:last}\n"
            "\\end{gather}\n"
        )

        presentations = index.extract_tex_named_result_presentations(source_text)

        self.assertEqual(
            [
                (
                    item.kind,
                    item.label,
                    item.line_start,
                    item.line_end,
                    item.presentation,
                )
                for item in presentations
            ],
            [],
        )

    def test_unparseable_multiline_display_requires_visible_formula_or_equation_tag(
        self,
    ) -> None:
        source_text = "\\begin{align}\na &= b \\\\ c &= d\n\\end{align}\n"

        self.assertEqual(
            [
                (item.kind, item.label, item.presentation)
                for item in index.extract_tex_named_result_presentations(source_text)
            ],
            [],
        )
        titled_source = (
            "\\begin{align}\n"
            "a &= b \\\\ c &= d \\tag{Equation 4}\n"
            "\\end{align}\n"
        )
        self.assertEqual(
            [
                (
                    item.kind,
                    item.label,
                    item.line_start,
                    item.line_end,
                    item.presentation,
                )
                for item in index.extract_tex_named_result_presentations(titled_source)
            ],
            [("equation", "Equation 4", 1, 3, "tex_multiline_named_display")],
        )

    def test_unambiguous_visible_titles_cannot_be_reclassified_by_mapping(self) -> None:
        tex_source = (
            "\\newtheorem{thm}{Theorem}\n"
            "\\begin{thm}\n"
            "Every input has a witness.\n"
            "\\end{thm}\n"
        )

        with self.assertRaisesRegex(ValueError, "cannot override unambiguous"):
            index.extract_tex_named_result_presentations(
                tex_source,
                environment_kinds={"thm": "definition"},
            )
        with self.assertRaisesRegex(ValueError, "cannot override unambiguous"):
            index.extract_text_named_result_presentations(
                "Theorem 1. Every input has a witness.\n",
                heading_kinds={"Theorem": "definition"},
            )

    def test_tex_extractor_uses_source_declared_theorem_aliases_not_alias_names(
        self,
    ) -> None:
        source_text = (
            "\\newtheorem{thm}{Theorem}\n"
            "\\newtheorem{prop}[thm]{Proposition}\n"
            "\\newtheorem{defn}{Definition}\n"
            "\\newtheorem{note}{Remark}\n"
            "\\begin{thm}\\label{thm:main}\n"
            "Every input has a witness.\n"
            "\\end{thm}\n"
            "\\begin{prop}\n"
            "The witness is unique.\n"
            "\\end{prop}\n"
            "\\begin{defn}\n"
            "A witness is designated.\n"
            "\\end{defn}\n"
            "\\begin{note}\n"
            "This remains a remark.\n"
            "\\end{note}\n"
            "\\begin{customresult}\n"
            "An explicitly declared result.\n"
            "\\end{customresult}\n"
        )

        presentations = index.extract_tex_named_result_presentations(
            source_text,
            environment_kinds={"customresult": "claim"},
        )

        self.assertEqual(
            [
                (item.kind, item.label, item.line_start, item.line_end)
                for item in presentations
            ],
            [
                ("theorem", "thm:main", 5, 7),
                ("proposition", "proposition@8", 8, 10),
                ("definition", "definition@11", 11, 13),
                ("claim", "claim@17", 17, 19),
            ],
        )

    def test_unclassified_named_source_presentations_require_declarative_source_mapping(
        self,
    ) -> None:
        source_text = (
            "\\newtheorem{fact}{Fact}\n"
            "\\begin{fact}\\label{fact:main}\n"
            "Every admissible input has a witness.\n"
            "\\end{fact}\n"
            "Fact 2. The visible transcript repeats the result.\n"
        )

        without_mapping = index.extract_named_result_presentations(
            source_text, source_format="tex"
        )
        self.assertEqual(
            [item.kind for item in without_mapping],
            ["unclassified", "unclassified"],
        )
        self.assertEqual(
            [item.label for item in without_mapping],
            ["fact:main", "Fact 2"],
        )

        with_mapping = index.extract_named_result_presentations(
            source_text,
            source_format="tex",
            environment_kinds={"fact": "claim"},
            heading_kinds={"Fact": "claim"},
        )
        self.assertEqual([item.kind for item in with_mapping], ["claim", "claim"])
        self.assertEqual([item.label for item in with_mapping], ["fact:main", "Fact 2"])

    def test_named_model_condition_and_setup_presentations_are_not_silently_ignored(
        self,
    ) -> None:
        source_text = (
            "Condition 1. Every input belongs to the domain.\n"
            "Model 2. Agents have a common prior.\n"
            "Setup A. The mechanism is fixed.\n"
        )

        presentations = index.extract_text_named_result_presentations(source_text)

        self.assertEqual(
            [(item.kind, item.label) for item in presentations],
            [
                ("unclassified", "Condition 1"),
                ("unclassified", "Model 2"),
                ("unclassified", "Setup A"),
            ],
        )

    def test_text_extractor_excludes_prose_model_headings_and_proof_cases(self) -> None:
        source_text = (
            "Model generalizations. This section is narrative context.\n"
            "Case 1: This is a proof subcase.\n"
            "Case 2. This is another proof subcase.\n"
            "Model A. This is an explicitly labelled source setup.\n"
            "Condition 1. This is an explicitly numbered source condition.\n"
        )

        presentations = index.extract_text_named_result_presentations(source_text)

        self.assertEqual(
            [(item.kind, item.label) for item in presentations],
            [
                ("unclassified", "Model A"),
                ("unclassified", "Condition 1"),
            ],
        )

    def test_named_conjecture_has_an_explicit_nonproof_presentation_kind(self) -> None:
        source_text = (
            "Conjecture 1. Every admissible input has a witness.\n"
            "Open Question 2. Is the witness unique?\n"
        )

        presentations = index.extract_text_named_result_presentations(source_text)

        self.assertEqual(
            [item.kind for item in presentations],
            ["open_problem", "open_problem"],
        )

    def test_reconciliation_uses_only_source_locations_or_exact_anchors(self) -> None:
        source_text = (
            "Introduction.\n"
            "Theorem 1. Every admissible input has a witness.\n"
            "The conclusion is source-visible.\n"
            "\n"
            "Definition 2. A witness is a designated input.\n"
        )
        presentations = index.extract_named_result_presentations(
            source_text, source_format="text"
        )
        source_items = {
            # Deliberately misleading source-map/Lean names must have no effect.
            "figure_caption_navigation_key": {
                "source_kind": "example",
                "lean_declarations": ["Fixture.UnrelatedHelper"],
                "source_location": "source.txt:2-3",
            },
            "theorem_named_but_not_used_for_matching": {
                "source_kind": "remark",
                "proof_lean_declarations": ["Fixture.OtherRoute"],
                "source_anchor_evidence": [
                    exact_anchor(source_text, "source.txt", 5, 5)
                ],
            },
        }

        reconciliations = index.reconcile_named_result_presentations(
            presentations,
            source_items,
            source_text=source_text,
            source_path="source.txt",
        )

        self.assertTrue(all(item.covered for item in reconciliations))
        self.assertEqual(
            [
                (
                    item.presentation.kind,
                    item.matches[0].item_id,
                    item.matches[0].evidence,
                )
                for item in reconciliations
            ],
            [
                ("theorem", "figure_caption_navigation_key", ("source_location",)),
                (
                    "definition",
                    "theorem_named_but_not_used_for_matching",
                    ("source_anchor_evidence[0]",),
                ),
            ],
        )

    def test_reconciliation_requires_a_complete_presentation_span(self) -> None:
        source_text = (
            "Theorem 1. Assume every input is admissible.\n"
            "Then every input has a witness.\n"
        )
        presentation = index.extract_named_result_presentations(
            source_text, source_format="text"
        )[0]
        heading_only_anchor = exact_anchor(source_text, "source.txt", 1, 1)
        full_anchor = exact_anchor(source_text, "source.txt", 1, 2)

        self.assertFalse(
            index.source_location_covers_presentation(
                "source.txt:1", presentation, source_path="source.txt"
            )
        )
        self.assertTrue(
            index.source_location_covers_presentation(
                "source.txt:1-2", presentation, source_path="source.txt"
            )
        )
        self.assertFalse(
            index.byte_pinned_anchor_covers_presentation(
                heading_only_anchor,
                presentation,
                source_text=source_text,
                source_path="source.txt",
            )
        )
        self.assertTrue(
            index.byte_pinned_anchor_covers_presentation(
                full_anchor,
                presentation,
                source_text=source_text,
                source_path="source.txt",
            )
        )

        reconciliation = index.reconcile_named_result_presentations(
            [presentation],
            {
                "opaque_item": {
                    "source_location": "source.txt:1",
                    "source_anchor_evidence": [heading_only_anchor],
                }
            },
            source_text=source_text,
            source_path="source.txt",
        )
        self.assertEqual(
            index.uncovered_named_result_presentations(reconciliation), [presentation]
        )

    def test_source_presentation_core_reconciles_conservative_transcript_span(self) -> None:
        """A reviewed core can end before parser-conservative narrative prose."""

        source_text = (
            "Theorem 1. Assume every input is admissible.\n"
            "Then every input has a witness.\n"
            "This paragraph gives intuition for the theorem.\n"
            "Lemma 2. Every witness is unique.\n"
            "The lemma has its own conclusion.\n"
        )
        presentations = index.extract_named_result_presentations(
            source_text, source_format="text"
        )
        self.assertEqual(
            [(item.label, item.line_start, item.line_end) for item in presentations],
            [("Theorem 1", 1, 3), ("Lemma 2", 4, 5)],
        )

        def core(kind: str, label: str, start: int, end: int) -> dict[str, object]:
            return {
                "schema": 1,
                "relation": "conservative_text_span_core",
                "presentation_kind": kind,
                "presentation_label": label,
                "core_anchor": exact_anchor(source_text, "source.txt", start, end),
                "boundary_reason": "completed_statement_then_explanation",
                "semantic_basis": (
                    "The exact multiline core contains the displayed hypotheses and "
                    "conclusion; the following source prose is explanatory narrative."
                ),
                "validator": "fixture source-only reviewer",
                "validated_at": "2026-07-28T12:00:00Z",
            }

        source_items = {
            # Deliberately unrelated opaque storage ids and Lean-looking text
            # cannot choose the presentation: exact source cores do.
            "navigation_bucket_alpha": {
                "source_anchor_evidence": [
                    exact_anchor(source_text, "source.txt", 1, 3)
                ],
                "source_presentation_reconciliation": core(
                    "theorem", "Theorem 1", 1, 2
                ),
                "lean_declarations": ["Fixture.unrelatedAlpha"],
            },
            "navigation_bucket_beta": {
                "source_anchor_evidence": [
                    exact_anchor(source_text, "source.txt", 1, 5)
                ],
                "source_presentation_reconciliation": core(
                    "lemma", "Lemma 2", 4, 5
                ),
                "lean_declarations": ["Fixture.unrelatedBeta"],
            },
        }
        reconciliations = index.reconcile_named_result_presentations(
            presentations,
            source_items,
            source_text=source_text,
            source_path="source.txt",
        )

        self.assertEqual(
            [
                (reconciliation.presentation.label, reconciliation.matches[0].item_id)
                for reconciliation in reconciliations
            ],
            [
                ("Theorem 1", "navigation_bucket_alpha"),
                ("Lemma 2", "navigation_bucket_beta"),
            ],
        )
        self.assertTrue(
            all(
                reconciliation.matches[0].evidence
                == ("source_presentation_reconciliation",)
                for reconciliation in reconciliations
            )
        )

    def test_source_presentation_core_rejects_heading_only_or_truncated_content(self) -> None:
        source_text = (
            "Theorem 1. Assume every input is admissible.\n"
            "Then every input has a witness.\n"
            "And every witness is unique.\n"
        )
        presentations = index.extract_named_result_presentations(
            source_text, source_format="text"
        )
        base = {
            "source_anchor_evidence": [exact_anchor(source_text, "source.txt", 1, 3)],
            "source_presentation_reconciliation": {
                "schema": 1,
                "relation": "conservative_text_span_core",
                "presentation_kind": "theorem",
                "presentation_label": "Theorem 1",
                "core_anchor": exact_anchor(source_text, "source.txt", 1, 1),
                "boundary_reason": "completed_statement_then_explanation",
                "semantic_basis": "Fixture source-only basis.",
                "validator": "fixture source-only reviewer",
                "validated_at": "2026-07-28T12:00:00Z",
            },
        }
        heading_only_errors = index.source_presentation_reconciliation_errors(
            base,
            presentations,
            source_text=source_text,
            source_path="source.txt",
        )
        self.assertTrue(
            any("nonblank continuation" in error for error in heading_only_errors),
            heading_only_errors,
        )

        truncated = dict(base)
        relation = dict(base["source_presentation_reconciliation"])
        relation["core_anchor"] = exact_anchor(source_text, "source.txt", 1, 2)
        truncated["source_presentation_reconciliation"] = relation
        truncated_errors = index.source_presentation_reconciliation_errors(
            truncated,
            presentations,
            source_text=source_text,
            source_path="source.txt",
        )
        self.assertTrue(
            any("visible statement continuation" in error for error in truncated_errors),
            truncated_errors,
        )

    def test_text_extractor_rejects_sentence_continuation_cross_reference(self) -> None:
        source_text = (
            "Definition 1. Thus, the preceding argument is complete.\n"
            "Theorem 2. Every admissible input has a witness.\n"
        )

        presentations = index.extract_text_named_result_presentations(source_text)

        self.assertEqual(
            [(item.kind, item.label) for item in presentations],
            [("theorem", "Theorem 2")],
        )

    def test_text_extractor_stops_at_two_line_decimal_section_heading(self) -> None:
        source_text = (
            "Theorem 1. Every admissible input has a witness.\n"
            "\n"
            "2.4\n"
            "\n"
            "A Preference for Independence\n"
            "Theorem 2. Every witness is unique.\n"
        )

        presentations = index.extract_text_named_result_presentations(source_text)

        self.assertEqual(
            [(item.label, item.line_start, item.line_end) for item in presentations],
            [("Theorem 1", 1, 1), ("Theorem 2", 6, 6)],
        )

    def test_invalid_anchor_or_wrong_source_path_does_not_cover_a_presentation(
        self,
    ) -> None:
        source_text = "Theorem 1. Every input has a witness.\n"
        presentation = index.extract_text_named_result_presentations(source_text)[0]
        bad_anchor = exact_anchor(source_text, "source.txt", 1, 1)
        bad_anchor["quoted_text"] = "Theorem 1. A different statement."
        bad_anchor["quoted_text_sha256"] = hashlib.sha256(
            str(bad_anchor["quoted_text"]).encode("utf-8")
        ).hexdigest()

        self.assertFalse(
            index.byte_pinned_anchor_covers_presentation(
                bad_anchor,
                presentation,
                source_text=source_text,
                source_path="source.txt",
            )
        )
        missing_path_anchor = exact_anchor(source_text, "source.txt", 1, 1)
        missing_path_anchor["path"] = ""
        self.assertFalse(
            index.byte_pinned_anchor_covers_presentation(
                missing_path_anchor,
                presentation,
                source_text=source_text,
            )
        )
        self.assertFalse(
            index.source_location_covers_presentation(
                "other/source.txt:1-1",
                presentation,
                source_path="source.txt",
            )
        )
        reconciliation = index.reconcile_named_result_presentations(
            [presentation],
            {"opaque_item_identifier": {"source_anchor_evidence": [bad_anchor]}},
            source_text=source_text,
            source_path="papers/Fixture/source.txt",
        )
        self.assertEqual(
            index.uncovered_named_result_presentations(reconciliation), [presentation]
        )

    def test_same_basename_in_another_directory_cannot_cover_a_presentation(
        self,
    ) -> None:
        source_text = "Theorem 1. Every input has a witness.\n"
        presentation = index.extract_text_named_result_presentations(source_text)[0]

        self.assertFalse(
            index.source_location_covers_presentation(
                "other/source.txt:1",
                presentation,
                source_path="source.txt",
            )
        )
        self.assertFalse(
            index.byte_pinned_anchor_covers_presentation(
                exact_anchor(source_text, "other/source.txt", 1, 1),
                presentation,
                source_text=source_text,
                source_path="source.txt",
            )
        )

    def test_source_line_span_parser_handles_multiple_concrete_ranges(self) -> None:
        self.assertEqual(
            index.source_line_spans("source.tex:3-7; appendix.txt:11"),
            (
                index.SourceLineSpan("source.tex", 3, 7),
                index.SourceLineSpan("appendix.txt", 11, 11),
            ),
        )


if __name__ == "__main__":
    unittest.main()
