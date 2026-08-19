# Final Validation Report: Gale--Shapley 1962

Updated: 2026-08-18

## 1. Human Verdict

The paper's selected named theoretical surface is formalized: the two printed
college-admissions definitions, the Section 3 marriage-instability definition,
and Theorems 1--2. Independent reviewer annotations may be added through the
packet or dashboard, but are not a prerequisite for this formalization status.

## 2. Closeout Status

- Completion status: formalized.
- The reviewed surface consists of three definitions and two named theorems.
- Every selected claim has a direct paper-facing semantic statement and a
  checked proof route. No theorem-level boundary remains within this scope.

## 3. Source and Scope

- Paper: D. Gale and L. S. Shapley, *College Admissions and the Stability of
  Marriage*.
- Source version: *American Mathematical Monthly* 69(1), 1962, printed pages
  9--15 ([public record](https://www.jstor.org/stable/2312726)).
- Formalized paper surface: the two displayed college-admissions definitions
  on printed page 10, the Section 3 prose definition of unstable marriages,
  Theorem 1, and Theorem 2.
- Scope boundary: numerical examples, ranking tables, and unnumbered
  extensions are not named theoretical claims in this review surface.

## 4. Researcher Summary of Checked Results

- **Theorem 1 (stable marriage existence).** The paper's finite marriage model
  has a stable set of marriages for every pattern of strict complete
  preferences. The checked proof follows the iterative deferred-acceptance
  procedure given immediately after the theorem.
- **Theorem 2 (applicant optimality).** Every applicant is at least as well off
  under the college deferred-acceptance outcome as under any other stable
  assignment. The checked route formalizes the Section 4 waiting-list procedure
  and the Section 5 comparison against every stable assignment in the same
  operational reading.
- **College-admissions definitions.** The page-10 definition of instability
  records the printed replacement-pair condition, and the following definition
  calls a stable assignment optimal when every applicant is at least as well
  off as under any other stable assignment. The Section 3 definition separately
  gives the corresponding marriage-instability condition.

## 5. Remaining Boundaries and Gaps

None within the selected named theoretical surface.

## 6. Additional Assumptions Beyond Paper

None. The representation of strict preference lists by order-preserving
numerical scores is a formal-model convention, not a cardinal-utility
assumption; its exact role is recorded in the source clarification below.

## 7. Proof-Strategy Deviations

None. Theorem 1 follows the source's iterative proposal-and-rejection route.
Theorem 2 follows the source's induction that no applicant is rejected by a
college that is possible for that applicant.

## 8. Proof Structure Worth Reusing

The source supplies two complementary reusable finite procedures. For Theorem
1, deferred acceptance maintains tentative partners while rejected applicants
continue proposing, and termination yields stability. For Theorem 2, define a
college to be possible for an applicant when some stable assignment sends the
applicant there, then use induction over the rejection steps to show that the
procedure never rejects an applicant from a possible college. This turns the
algorithmic trace into the applicant-optimality comparison.

## 9. Generalizations, Conjectures, and Extensions

This closeout makes no claim beyond the paper's stated marriage and
college-admissions results. In particular, it does not treat the paper's
unnumbered extensions or numerical examples as separately formalized theorems.

## 10. Source Clarifications and Exact Readings

For Sections 4--5 and Theorem 2, “stable assignment” is read operationally:
the assignment respects quotas, assigns only acceptable pairs, and has no
applicant-college block through either a vacant seat or replacement of a
lower-ranked current assignee. The earlier printed page-10 replacement-pair
definition remains a separate literal source claim; it is not asserted to be
equivalent to the Section 4--5 reading in isolation. The formal representation
of preference lists preserves their ordinal order and uses the unmatched option
only as the source's outside alternative. Full details appear in the
[source clarification note](docs/SOURCE_CLARIFICATIONS.md).

## 11. Paper Issues or Caveats

None within the reviewed named theoretical surface. The distinct scope of the
page-10 definition and the completed Sections 4--5 reading is a clarification,
not a caveat on either theorem.

## 12. Checked Claim Inventory

The five checked source claims are:

1. the printed page-10 definition of an unstable college assignment;
2. the printed page-10 definition of an optimal stable college assignment;
3. the Section 3 prose definition of an unstable marriage;
4. **Theorem 1**, existence of a stable set of marriages; and
5. **Theorem 2**, applicant optimality of the college waiting-list procedure.

The [human review packet](docs/HUMAN_REVIEW_PACKET.pdf) presents the five
claims in dependency order, followed by the material procedure and matching
definitions used to read them. The interactive dashboard, launched with
`papers/GS62CollegeAdmissions/review-dashboard.sh`, is an optional alternative
to using the PDF.

## 13. Source and Assumption Provenance

The two college definitions are anchored to `cited publication:93--98` and
`cited publication:115--117` (printed page 10). The marriage definition and Theorem 1
are anchored to `cited publication:133--139` and `cited publication:185` (printed pages
11--12). Theorem 2 is anchored to the Sections 4--5 procedure and comparison
at `cited publication:232--249` and `cited publication:253--255` (printed pages 13--14).
The [statement map](audit/paper_statement_map.json) records these locations
and the selected source bundle.

## 14. Semantic Review and Proof Evidence

For each selected source claim, the [raw source-to-specification ledger](audit/v11_raw_source_spec_screening.json)
records the direct comparison between the byte-pinned source input and its one
semantic review target. The paired Lean theorem is separately checked as the
proof endpoint for that target. The [current focused-build receipt](audit/FOCUSED_BUILD_RECEIPT.json)
and [final closure receipt](FINAL_CLOSURE_RECEIPT.md) identify the current
validation run.

## 15. Reused Definitions and Dependency DAG

The [library review ledger](audit/library_semantic_review.json) records the
source connection for matching definitions reused by the five paper claims.
The [paper-prerequisite ledger](audit/paper_semantic_prerequisites.json)
records the college-procedure declarations needed for the Theorem 2 reading.
The [dependency DAG](docs/DependencyDAG.pdf) places those definitions before
the two theorem routes and is a companion to, rather than a substitute for,
the source comparisons.

## 16. Validation Materials

- [Human review packet (PDF)](docs/HUMAN_REVIEW_PACKET.pdf)
- [Dependency DAG (PDF)](docs/DependencyDAG.pdf)
- [Source clarification note](docs/SOURCE_CLARIFICATIONS.md)
- [Statement map](audit/paper_statement_map.json)
- [Source-to-specification ledger](audit/v11_raw_source_spec_screening.json)
- [Library review ledger](audit/library_semantic_review.json)
- [Final closure receipt](FINAL_CLOSURE_RECEIPT.md)
