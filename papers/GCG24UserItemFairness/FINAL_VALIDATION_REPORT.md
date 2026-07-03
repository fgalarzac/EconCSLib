# Final Validation Report: User-Item Fairness Tradeoffs in Recommendations

Updated: 2026-07-03

## 1. Human Verdict
Formalized. The paper-facing results for user-item fairness tradeoffs are
checked, including the LP/duality and feasible-support ingredients needed by
the source arguments. No paper-correctness caveat is reported. No human
dashboard sign-off has been recorded.

## 2. Closeout Status
- Completion status: formalized.
- One-sentence recap: The user-item fairness tradeoff results are checked through the paper-facing LP, support, and duality ingredients.
- Lean footprint: 46,174 paper-local Lean LOC; `PaperInterface.lean` is 387 lines; 48 human-review declarations are exposed.
- Audit summary: source coverage has 48 covered; statement LLM-as-judge has 48 matches; Lean-to-TeX has 38 row translations; assumption provenance has 10 paper_condition; source-record classification has 26 validated_source_assumption, 4 container_recursively_audited, 4 derived_consequence_record; source-record audit reports 48 review rows, 22 boundary inputs, 0 recursion failures; review-surface audit passes over 48 review rows; holistic source-first audit PASS; DAG/source-json audit PASS in `docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`.

## 3. Source and Scope
The validation source of truth is the paper folder, not older campaign-level notes:

- `papers/GCG24UserItemFairness/docs/DependencyDAG.tex`
- `papers/GCG24UserItemFairness/PaperInterface.lean`
- `papers/GCG24UserItemFairness/MainTheorems.lean`
- the successful targeted Lean build

`PaperInterface.lean` exposes the human-facing definitions and main theorem statements. `MainTheorems.lean` exposes the full paper-facing wrappers. Detailed proof work is split across the paper-local LP reduction, optimization, symmetry, opposing-types, and misestimation files.

## 4. Researcher Summary of Checked Results
- The formalization checks the user-item fairness tradeoff results through the paper-facing LP, feasible-support, and duality ingredients.
- The main theorem wrappers expose the source definitions and theorem statements rather than proof-internal certificates.
- No unresolved mathematical boundary is recorded for the checked theorem surface.

## 5. Remaining Boundaries and Gaps
None.

## 6. Additional Assumptions Beyond Paper
None.

## 7. Proof-Strategy Deviations
None. The Lean development follows the paper's named proof architecture: symmetry reduction, sparse support and opposing-types reductions, canonical pivot and closed-form constructions for Problem 6, mirror symmetry for the second half of Theorem 3, and the Appendix E Problem 11/cold-start construction for Theorem 4. The remaining differences are proof organization, mainly factoring LP arguments through auditable certificate structures and making parity, center, and mirror cases explicit before recombining them in the final source wrappers.

## 8. Proof Tricks Worth Reusing
- Factor LP arguments through auditable certificates, but keep the closed paper-facing wrappers in `PaperInterface.lean`.
- Split parity, center, and mirror cases into small lemmas before recombining them into source-shaped theorem wrappers.

## 9. Mathematical Typos or Other Fixes Suggested in the Source Paper
None found.

## 10. Paper Issues or Caveats
None found.

## 11. Detailed Formalization Evidence
### Results Covered

The formalization covers the paper's tracked named model definitions, supporting
propositions, supporting appendix lemmas, and main paper-facing results,
including:

- recommendation-model user/item fairness definitions and optimization
  predicates;
- Example 1's two-item diverse-preferences toy instance and homogeneous
  tradeoff algebra;
- Proposition 1's symmetric LP-reduction instantiation used downstream;
- Proposition 2's symmetric optimum and sparse-support bridge;
- Appendix C Lemmas 1--2 and Appendix D Lemmas 3--11;
- Theorem 3 price-of-fairness monotonicity through canonical reduction-witness
  wrappers on both halves of the alpha interval;
- Appendix E Lemmas 12--17 and the Problem 11 construction;
- Theorem 4 misestimation/no-fairness and with-fairness source wrappers for both
  possible true cold-start rows.

## 12. Paper Assumption Provenance
Every paper-facing theorem premise that is not derived in Lean is routed through
`Assumptions.lean` and checked separately as either a paper/source model
assumption or a paper-statement condition.

| Assumption or condition | Lean declaration | Source location / statement | Provenance judgment | Comments |
|---|---|---|---|---|
| Positive utilities | `assumption_positive_recommendation_utilities` | Source model / Theorem 3 setup / Appendix C Lemma 1 | paper condition | Covers Proposition 2 and Theorem 3 positive-utility premises. |
| Theorem 3 opposing-type model | `assumption_theorem3_opposing_type_model` | Theorem 3 setup, lines 367-397 and 2078-2086 | paper condition | Records the two-type reduced model, positive value vector, and strict value ordering. |
| Theorem 3 first-half alpha domain | `assumption_theorem3_first_half_alpha_domain` | Theorem 3 statement | paper condition | `0 < alpha <= alpha' <= 1/2`. |
| Theorem 3 second-half alpha domain | `assumption_theorem3_second_half_alpha_domain` | Theorem 3 statement | paper condition | `1/2 <= alpha <= alpha' < 1`. |
| Theorem 4 item domain | `assumption_theorem4_at_least_three_items` | Theorem 4 / Appendix E construction | paper condition | Nontrivial item geometry for the construction. |
| Theorem 4 true model | `assumption_theorem4_true_model_reduction` | Theorem 4 construction | paper condition | Identifies the true model with the two-type source construction. |
| Theorem 4 estimated model | `assumption_theorem4_estimated_model_reduction` | Theorem 4 construction | paper condition | Identifies the estimated model with the three-type estimated construction. |
| Theorem 4 displayed reductions | `assumption_theorem4_displayed_reduced_models` | Theorem 4 / Appendix E displayed model definitions | paper condition | Pins Lean reductions to the displayed true and estimated matrices. |
| Theorem 4 cold-start wiring | `assumption_theorem4_cold_start_type_wiring` | Appendix E three-type construction | paper condition | The cold-start user is estimated as type 2 and has one of the two true opposing rows. |
| Theorem 4 parameter domain | `assumption_theorem4_parameter_domain` | Theorem 4 statement and Appendix E proof | paper condition | Positive epsilon and beta-domain premises. |

### Source-Condition Notes

No additional unverified assumptions remain for the final source Theorem 3 and
Theorem 4 wrappers tracked by the paper README/DAG.

Some declarations expose ordinary mathematical hypotheses that are part of the
formal statement or its intended model, for example finite type representatives
and compatibility assumptions identifying estimated known rows with the true
rows. These are not proof gaps; they are explicit hypotheses in the formalized
model and now have a source-condition ledger.

The main modeling caveat is that the paper's general "finding reduces to an LP"
claim is encoded through paper-local equality-form LP and certificate interfaces
rather than a generic solver-level LP syntax. The final paper-facing wrappers
construct or discharge the needed certificates internally. Auxiliary
selected-BFS/certificate variants that still take explicit inputs are retained
as helper interfaces and are not the closed source theorem wrappers.

## 13. Displayed Formula Provenance
Displayed and source-defining formulas are tracked through the paper-facing rows in `PaperInterface.lean` and the current statement-match sidecars. This report pass found no standalone formula-provenance issue beyond any source notes already listed above.

## 14. Library Lift Pass
The proof uses paper-local LP, optimization, symmetry, opposing-types, and misestimation modules. No additional shared-library extraction was needed in this report pass; future papers that reuse the same equality-form LP certificates would be the right trigger for lifting that layer.

## 15. DAG Audit
`DependencyDAG.tex` and `DependencyDAG.pdf` are present as the paper-facing
dependency artifacts. The rendered `DependencyDAG.pdf` was visually inspected
for node/label overlap and arrow-through-text issues. The DAG covers the
source-result clusters recorded in the source inventory: Problem 1, Example 1,
Lemmas 1--17, Problems 6/11/12, Propositions 1/2, and Theorems 3/4. The
selected-BFS and certificate variants are retained as helper interfaces rather
than separate DAG paper-result nodes.

## 16. Validation Checks

<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 48 covered.
- Statement match (`audit/statement_match_llm.json`): 48 matches.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 38 row translations generated from Lean statements.
- Assumption provenance (`audit/assumption_match_llm.json`): 10 paper_condition.
- Source-record classification (`audit/source_record_match_llm.json`): 26 validated_source_assumption, 4 container_recursively_audited, 4 derived_consequence_record.
- Source-record structural audit (`audit/source_record_audit.json`): 48 review rows, 22 boundary inputs, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): passes over 48 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): PASS.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): PASS.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->

### Statement Translation Audit

Audit date: 2026-06-29.
Scope: current dashboard surface from `PaperInterface.lean`; the generated
LLM-as-judge block above is sourced from the tracked sidecars.

Summary: statement match has 48 matches; Lean-to-TeX has 38 row translations; assumption provenance has 10 paper_condition.
No separate stale manual validator table is maintained in this report.

## 17. Paper Definitions Checked
<!-- lean-derived-definitions:start -->
### Lean-Derived Dashboard Definitions

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| def recommendationUtility | `recommendationUtility` | - Recommendation utility matrix `w_{ij}` for users and items. |
| def rawUserUtility | `rawUserUtility` | - Raw user utility `sum_j w_ij rho_ij`. |
| def normalizedUserUtility | `normalizedUserUtility` | - Normalized user utility `U_i(rho)`. |
| def userFairness | `userFairness` | - User fairness `U_min(rho) = min_i U_i(rho)`. |
| def rawItemUtility | `rawItemUtility` | - Raw item utility `sum_i w_ij rho_ij`. |
| def itemNormalizer | `itemNormalizer` | - Item normalizer `sum_i w_ij`. |
| def normalizedItemUtility | `normalizedItemUtility` | - Normalized item utility `I_j(rho)`. |
| def itemFairness | `itemFairness` | - Item fairness `I_min(rho) = min_j I_j(rho)`. |
| def solvesProblemOne | `solvesProblemOne` | - Problem 1: a policy maximizes user fairness subject to item-fairness level `gamma`. |
| def priceOfFairnessAt | `priceOfFairnessAt` | - Price of fairness at item-fairness level `gamma`. |
| def priceOfFairness | `priceOfFairness` | - Price of maximal item fairness. |
| def priceOfMisestimation | `priceOfMisestimation` | - Price of misestimation for a policy selected on an estimated utility matrix. |
<!-- lean-derived-definitions:end -->

## 18. Named Theorem Statements Checked
<!-- lean-derived-statements:start -->
### Lean-Derived Dashboard Named Statements

| Paper-facing item | Lean declaration | Source-facing statement |
| --- | --- | --- |
| theorem proposition1_symmetric_lp_reduction | `proposition1_symmetric_lp_reduction` | - Proposition 1: symmetric LP reduction. Type-symmetric original optima are represented by reduced type-level policies. |
| theorem proposition2_symmetric_optimum_exists | `proposition2_symmetric_optimum_exists` | - Proposition 2: under positive utilities, a type-symmetric optimal policy exists for the maximal item-fairness problem. |
| theorem theorem3_price_decreases_first_half | `theorem3_price_decreases_first_half` | Theorem 3 first half: in the opposing two-type model, increasing `alpha` toward `1 / 2` weakly decreases the price of fairness. |
| theorem theorem3_price_increases_second_half | `theorem3_price_increases_second_half` | Theorem 3 second half: in the opposing two-type model, increasing `alpha` away from `1 / 2` weakly increases the price of fairness. |
| theorem theorem4_misestimation_tradeoff_typeZero | `theorem4_misestimation_tradeoff_typeZero` | - Theorem 4 final tradeoff, cold-start user whose true row is the first opposing type: without fairness the misestimation price is at most `1/2`, while with maximal item fairness some estimated optimum has misestimation price above `1 -... |
| theorem theorem4_misestimation_tradeoff_typeOne | `theorem4_misestimation_tradeoff_typeOne` | - Theorem 4 final tradeoff for the second opposing true type. |
<!-- lean-derived-statements:end -->

## 19. Paper-Facing Statement Validator Ledger
Current source: `audit/statement_match_llm.json`, refreshed 2026-06-29, plus assumption provenance in `audit/assumption_match_llm.json`.

| Validator surface | Result |
| --- | --- |
| Statement match | 48 matches. |
| Lean-to-TeX drafts | 38 row translations generated from Lean statements. |
| Assumption provenance | 10 paper_condition. |
| Source coverage | 48 covered. |

The full row-level validator ledger is tracked in the JSON sidecars. Human
dashboard reviews and model/agent statement checks are separate provenance lanes;
this report does not change the human-only `human_review.reviewed_rows` counter.
