# Final Validation Report: GGSG19 Top Three

Updated: 2026-07-03

## 1. Human Verdict
Formalized. The finite-candidate Top Three theorem surface is checked with the
finite-support conditions made explicit. No source-paper error is reported for
the formalized results. No human dashboard sign-off has been recorded.

## 2. Closeout Status
- Completion status: formalized.
- One-sentence recap: The Top Three election-learning results are formalized through finite-support and Mallows/randomization source rows.
- Lean footprint: 35,055 paper-local Lean LOC; `PaperInterface.lean` is 340 lines; 17 human-review declarations are exposed.
- Audit summary: source coverage has 17 covered; statement LLM-as-judge has 17 matches; Lean-to-TeX has 12 row translations; assumption provenance has 5 paper_condition; source-record classification sidecar is not tracked; source-record audit reports 15 review rows, 0 boundary inputs, 0 recursion failures; review-surface audit passes over 17 review rows; holistic source-first audit PASS; DAG/source-json audit PASS in `docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`.

## 3. Source and Scope
- Paper: *Who is in Your Top Three? Optimizing Learning in Elections with Many Candidates*.
- Publication venue: HCOMP 2019.
- Source version: arXiv 1906.08160 TeX/PDF, 2019.
- Lean folder: `papers/GGSG19TopThree`.
- Human-facing theorem file: `papers/GGSG19TopThree/PaperInterface.lean`.
- Detailed post-formalization audit: `papers/GGSG19TopThree/docs/POST_FORMALIZATION_AUDIT.md`.
- DAG artifacts: `papers/GGSG19TopThree/docs/DependencyDAG.tex`, `papers/GGSG19TopThree/docs/DependencyDAG.pdf`.

## 4. Researcher Summary of Checked Results
- The formalization checks the finite-candidate Top Three theorem surface.
- The large-deviation-rate definition, Propositions 1-4, randomized scoring/K-approval results, and Mallows special cases are represented in the paper-facing interface.
- The finite-support conditions needed by the source arguments are explicit.

## 5. Remaining Boundaries and Gaps
None.

## 6. Additional Assumptions Beyond Paper
None.

## 7. Proof-Strategy Deviations
None. Finite-support boundary branches are stated explicitly where the source leaves them in prose, and empirical/numerical sections are outside the Lean theorem surface.

## 8. Proof Tricks Worth Reusing
- Use `WithTop` rates for finite-support large-deviation boundary cases.
- Split ranking-learning proofs into pairwise finite-support rates, K-approval
  ternary specialization, and finite relevant-pair aggregation.
- Keep one-loser/all-but-one K-approval facts in the shared social-choice
  library and paper-specific terminology as thin wrappers.

## 9. Mathematical Typos or Other Fixes Suggested in the Source Paper
None found.

## 10. Paper Issues or Caveats
None found.

## 11. Detailed Formalization Evidence
The formalization covers the finite-candidate source theorem surface: the
large-deviation-rate definition, Propositions 1-4, randomized scoring,
randomized K-approval, the constructed W-selection randomization-improvement
example, Mallows no-randomization, and the high-noise Mallows W-approval
non-optimality example.

Propositions 2-4 expose the finite-support one-sided and eventually-zero
boundary cases explicitly. These are source-model boundary cases, not remaining
proof obligations.

Proposition 4's paper interface now uses the paper's source-shaped unweighted
expected-error sum `Q^N`. The older generalized positive-weight aggregate is
kept only as proof/library infrastructure, not as the paper-facing row.

The paper's empirical and numerical sections are treated as reproducibility
artifacts rather than Lean theorem targets.

## 12. Paper Assumption Provenance
Every non-derived paper-facing premise is routed through
`GGSG19TopThree/Assumptions.lean` and checked by
`assumption_match_llm.json`. These rows are source theorem/domain conditions:
strict cross-tier prefix separation, ternary K-approval score gaps,
randomized-mechanism probability weights, and nontrivial
Mallows/K-approval domains. None are proof-only certificates.

| Lean assumption/condition | Judgment | Source role |
| --- | --- | --- |
| `assumption_strict_cross_tier_no_ties` | source text | Proposition 1 strict cross-tier top-prefix inequalities. |
| `assumption_pairwise_approval_ternary_gap_domain` | derived from source primitives | Proposition 3 K-approval ternary score-gap domain and `s_i > s_j`. |
| `assumption_randomized_mechanism_probability_weights` | source model primitive | Randomized scoring/K-approval rule probabilities. |
| `assumption_mallows_nontrivial_winner_and_noise` | paper condition | Mallows top-W pivotal-pair regime, including the non-uniform Mallows domain. |
| `assumption_nontrivial_k_approval_cutoffs` | source text | Positive proper K-approval cutoffs in the randomized family. |

## 13. Displayed Formula Provenance
Displayed and source-defining formulas are tracked through the paper-facing rows in `PaperInterface.lean` and the current statement-match sidecars. This report pass found no standalone formula-provenance issue beyond any source notes already listed above.

## 14. Library Lift Pass
- `EconCSLib.Foundations.Probability.FiniteSupportMGF`: finite-support
  log-MGF, rate, extended-rate, and pairwise threshold-rate APIs.
- `EconCSLib.Foundations.Probability.LargeDeviations`: finite weighted-sum and
  pairwise aggregation certificates.
- `EconCSLib.SocialChoice.Ranking.Approval`: all-but-one K-approval last-rank
  probability facts.
- `EconCSLib.SocialChoice.Ranking.MallowsRankFactorization`: reusable Mallows
  rank-factorization algebra.

Further candidates are recorded in `POST_FORMALIZATION_AUDIT.md`.

## 15. DAG Audit
- Rendered artifact: yes, `DependencyDAG.pdf`.
- Topology: source-facing named-result topology; empirical sections omitted.
- Layout: visually inspected after rerendering; no known overlap or unintended
  dashed-edge semantics.

## 16. Validation Checks

<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 17 covered.
- Statement match (`audit/statement_match_llm.json`): 17 matches.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 12 row translations generated from Lean statements.
- Assumption provenance (`audit/assumption_match_llm.json`): 5 paper_condition.
- Source-record classification: no source-record classification sidecar tracked for this paper.
- Source-record structural audit (`audit/source_record_audit.json`): 15 review rows, 0 boundary inputs, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): passes over 17 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): PASS.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): PASS.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

The targeted paper build passed for `lake build GGSG19TopThree`. The DAG was
rendered from the paper folder with `latexmk`, converted to PNG, and visually
inspected. Targeted `git diff --check` passed for the changed GGSG documents.

## 17. Paper Definitions Checked
- Large-deviation rate: `r = -lim_N (1 / N) log A_N`.
  Lean: `paper_definition_large_deviation_rate`.

<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| abbrev paper_definition_large_deviation_rate | `paper_definition_large_deviation_rate` | - Paper definition of an exponential large-deviation rate. |
<!-- lean-derived-definitions:end -->

## 18. Named Theorem Statements Checked
### Proposition 1

**Paper statement.** Strict top-prefix cross-tier dominance characterizes the
source tiered consistency/design-invariance condition.

**Lean interface statement.**
- `source_proposition1_thm_consistency_tiered`: tiered finite-ranking form.

**Status.** formalized.

### Propositions 2-4

**Paper statement.** Pairwise score-gap rates, K-approval ternary rates, and
finite relevant-pair aggregation give the outcome-learning rate.

**Lean interface statements.**
- `source_proposition2_thm_pairwiselearning_finite_support`.
- `source_proposition3_lem_pairwiselearning_approval_finite_ternary`.
- `source_proposition4_thm_goal_learning_finite_support`.

**Status.** formalized.

### Randomization and Mallows Results

**Paper statement.** Static scoring/K-approval comparisons and the Mallows
examples establish the paper's no-randomization and randomization-improvement
claims.

**Lean interface statements.**
- `source_theorem1_lem_randomizebetterscoring`.
- `source_theorem2_lem_randomizenotbetterapproval_pairwise`.
- `source_theorem_lem_randomizebetterapproval_w_selection_constructed`.
- `source_corollary_lem_mallowsnorando`.
- `source_theorem_lem_mallowsnotWK_counterexample`.

**Status.** formalized.

<!-- lean-derived-statements:start -->
### Lean-Derived Dashboard Named Statements

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| theorem source_proposition1_thm_consistency_tiered | `source_proposition1_thm_consistency_tiered` | tiered finite-ranking form. |
| theorem source_proposition2_thm_pairwiselearning_finite_support | `source_proposition2_thm_pairwiselearning_finite_support` | - Source Proposition `thm:pairwiselearning`, finite-support form. The ordinary two-sided case has the paper's displayed Chernoff exponent; the explicit one-sided branches record finite-candidate boundary cases where the finite real rate... |
| theorem source_proposition3_lem_pairwiselearning_approval_finite_ternary | `source_proposition3_lem_pairwiselearning_approval_finite_ternary` | - Source Proposition `lem:pairwiselearning_approval`, finite ternary form for K-approval score gaps. The finite-rate branch is exactly the paper's closed form `approvalPairwiseRate`; the other branch is the strict boundary where the mist... |
| theorem source_proposition4_thm_goal_learning_finite_support | `source_proposition4_thm_goal_learning_finite_support` | - Source Proposition `thm:goal_learning`, finite relevant-pair aggregation form. The finite aggregate has an exact finite exponent unless all relevant pairwise errors are eventually empty, represented as extended rate `⊤`. |
| theorem source_theorem1_lem_randomizebetterscoring | `source_theorem1_lem_randomizebetterscoring` | - Source Theorem `lem:randomizebetterscoring`, finite W-selection form. The convex-combination static rule is reasonable, selects the target W-set, and weakly dominates the randomized scoring rule in extended finite outcome rate. |
| theorem source_theorem2_lem_randomizenotbetterapproval_pairwise | `source_theorem2_lem_randomizenotbetterapproval_pairwise` | - Source Theorem `lem:randomizenotbetterapproval`, fixed-pair form. For any finite randomized K-approval rule, some static component weakly dominates the randomized pairwise rate; zero-base static boundaries are treated as top extended r... |
| theorem source_theorem_lem_randomizebetterapproval_w_selection_constructed | `source_theorem_lem_randomizebetterapproval_w_selection_constructed` | - Source Theorem `lem:randomizebetterapproval_Wselection`, concrete finite constructed-law endpoint: the six-ranking law is design-invariant for W-selection and 50/50 randomized approval strictly beats every static K-approval cutoff in t... |
| theorem source_corollary_lem_mallowsnorando | `source_corollary_lem_mallowsnorando` | - Source Corollary `lem:mallowsnorando`: under a finite Mallows model with `q < 1`, an approval-rate-optimal static K-approval cutoff weakly dominates any finite randomized family of nontrivial K-approval rules. |
| theorem source_theorem_lem_mallowsnotWK_counterexample | `source_theorem_lem_mallowsnotWK_counterexample` | - Source Theorem `lem:mallowsnotWK`: a four-candidate high-noise Mallows counterexample where W-approval is not approval-rate optimal. |
<!-- lean-derived-statements:end -->

## 19. Paper-Facing Statement Validator Ledger
Current source: `audit/statement_match_llm.json`, refreshed 2026-06-29, plus assumption provenance in `audit/assumption_match_llm.json`.

| Validator surface | Result |
| --- | --- |
| Statement match | 17 matches. |
| Lean-to-TeX drafts | 12 row translations generated from Lean statements. |
| Assumption provenance | 5 paper_condition. |
| Source coverage | 17 covered. |

The full row-level validator ledger is tracked in the JSON sidecars. Human
dashboard reviews and model/agent statement checks are separate provenance lanes;
this report does not change the human-only `human_review.reviewed_rows` counter.
