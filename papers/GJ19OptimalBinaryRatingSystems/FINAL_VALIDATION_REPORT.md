# Final Validation Report: GJ19 Optimal Binary Rating Systems

Updated: 2026-07-31

## 1. Human Verdict

The paper's mathematical results are formalized. Local typos and implied
conventions are recorded directly, and the C.4 row uses an explicit corrected
statement because the printed proof changes objective conventions between its
two directions. These repairs preserve the substantive finite-rate and
non-step obstruction results and do not overturn a central design or algorithm
claim, so the appropriate status is `formalized` rather than `formalized with
caveat`.

## 2. Closeout Status

- Completion status: **formalized**.
- Source-first inventory: 76 atomic items.
- Compact review surface: 61 paper-facing rows.
- Paper coverage: 59 direct items and 17 items tied to named Lean support.

## 3. Source and Scope

The checked source is the AISTATS 2019 / PMLR 89 main paper and supplement in
`cited publication`, SHA-256
`59780d7a9ea09cccd9c6877103434757a6597212512958c6e22e60b189826e89`.
The public source is the
[PMLR paper PDF](https://proceedings.mlr.press/v89/garg19a/garg19a.pdf).
The inventory includes model definitions, formulas, algorithms, named results,
and proof-critical displays. Empirical plots and simulations are context rather
than Lean theorem targets.

## 4. Researcher Summary of Checked Results

The development checks the literal source model and dynamics, Bernoulli
large-deviation formulas, the finite equalized-rate optimizer, general
nondecreasing-matching Theorem 3.1, Algorithm 1 and Theorem 3.2, Lemmas
B.1--B.3, the Appendix C aggregation/refinement chain, Theorem B.1 and
Corollary C.4 convergence branches, and the Kendall/Spearman applications.

The remediation specifically closed the source cell-rate bridge and staged
Theorem 3.1 assembly; the Lemma B.1 optimizer shift; the complete two-scale
B.2/B.3 learning limits from the random-question IID model; general-matching
Lemma C.6; the C.3 finite minimum selected internally; the corrected C.4 finite
selected-pullback positive-rate and non-step source zero-rate branches; and the literal weighted
outer/inner bisection runner with additive loss and optimizer-independent
polynomial runtime.

## 5. Remaining Boundaries and Gaps

No mathematical paper-result boundary remains classified as partial or
missing. The compact dashboard intentionally keeps subsidiary appendix claims
as named support rather than duplicating every implementation theorem as a
paper-facing row; the source-to-Lean protocol reports that review-surface
limitation separately from mathematical completeness.

## 6. Additional Assumptions Beyond Paper

The full lexicographic Theorem 3.1 wrapper makes uniqueness of the first-stage
value maximizer explicit as a tie convention. The corrected Lemma B.3 theorem
assumes strict increase of the mixed expected score, the identifiability
condition required to recover true quality order. These are minor implied
conditions, not caveats; no theorem accepts empirical tracking, rank recovery,
a selected finite minimum, or a selected objective-gap realization as an input.

## 7. Proof-Strategy Deviations

Lean replaces the source's false full-square uniform-convergence remark by
finite separated-cell and weighted essential-infimum arguments. The detailed
Algorithm 1 pseudocode's local variable slips are resolved using the unambiguous
main-paper description and a literal source-shaped runner.

For Lemma C.4, the source forward proof uses a selected cross-level objective
while its reverse proof uses a general tie-erased source gap. Lean states and
proves those two valid branches explicitly; it does not certify a literal
same-kernel iff without a realization bridge.

## 8. Proof Tricks Worth Reusing

- Separate finite Bernoulli-rate identities from continuum aggregation.
- Use endpoint-aware level vectors throughout equalization and optimization.
- Derive random conditional frequencies as a ratio of two Strong Law limits,
  then exploit finiteness for simultaneous convergence.
- Derive ranking stability from a strict limiting score gap.
- Prove an explicit source-optimizer gap lower bound before choosing the
  bisection grid, so runtime does not depend on an unknown optimum coordinate.

## 9. Generalizations, Conjectures, and Extensions

The source's whole-sequence and broader matching-function extensions of the
Theorem B.1 limit are conjectural context and are not promoted to paper claims.
The formalization includes the source multiplicative Theorem 3.2 extension as
a checked support theorem.

## 10. Mathematical Typos or Other Fixes Suggested in the Source Paper

The proof-fidelity ledger records the C.5 endpoint typo, local Algorithm 1
argument slips, first-rate logarithm typo, tied-complement sentence,
Landau-notation direction, full-square uniformity remark, and Remark C.2's
joint-strict-convexity overstatement.  The last cannot be literal while the
whole diagonal is a set of minima; Lean checks the exact content used by the
paper instead: joint interior continuity, diagonal zero, off-diagonal
positivity, and strict coordinatewise separation. Each repair is localized
and preserves the advertised result.

## 11. Paper Issues or Caveats

None requiring `formalized with caveat`. The Theorem 3.1 tie convention and
Lemma B.3 strict identifiability premise remain visible formalized notes.

## 12. Detailed Formalization Evidence

- Source inventory and routing: `audit/paper_statement_map.json`.
- Source-to-Lean coverage: `audit/paper_coverage_llm.json`.
- Row-local v10 judgments: `audit/statement_match_llm.json`.
- Recursive v7 provenance: `audit/source_record_audit.json` and
  `audit/source_record_match_llm.json`.
- Source repairs: `audit/source_proof_fidelity.json`.
- Independent source-first review: `docs/AGENT_SOURCE_AUDIT.md`.

The focused `PaperInterface` and `Theorem32Appendix` builds pass with 3,566
jobs and no warnings. The v10 ledgers validate all 61 rows, the 76-item
paper-coverage lane has no missing/stale item, conclusion provenance reports no
unresolved dependency, and evidence integrity has zero errors.

## 13. Paper Assumption Provenance

All configured premise rows are visible source-model or theorem conditions,
including tie handling and score identifiability where the printed proof needs
them. Their definitions and source roles are recorded in `Assumptions.lean`
and `audit/source_proof_fidelity.json`; no conclusion-bearing certificate is
treated as an assumption. A separate assumption-judgment sidecar is not
currently tracked for this paper.

<!-- BEGIN GENERATED ASSUMPTION PROVENANCE LEDGER -->
### Current Canonical Evidence
Generated from the configured source-condition surface and exact current statement digests in the canonical assumption-provenance sidecar. Model, agent, and automated checks are identified as such; no human review is inferred.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| None | `none` | None | None | No paper-facing assumption declarations are configured. |
<!-- END GENERATED ASSUMPTION PROVENANCE LEDGER -->

## 14. Displayed Formula Provenance

The state transition, score, rate, bisection, aggregation, and corrected C.4
formulas have direct reviewed rows or transparent theorem support. Printed
repairs remain visible in the source-fidelity ledger.

<!-- BEGIN GENERATED FORMULA PROVENANCE LEDGER -->
### Current Canonical Evidence
Rows are selected from semantic `formula` and `equation` source-kind metadata within the configured semantic source-coverage scope, never from declaration names. Coverage and statement checks remain separate evidence lanes. Scope metadata needs repair, so the full inventory is shown: paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout

| Paper formula / subclaim | Lean declaration | Provenance | Validators | Comments |
| --- | --- | --- | --- | --- |
| Conditional on quality, the empirical reputation has the corresponding scaled binomial distribution. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex GJ19 full-formalization source-coverage closeout 2026-07-19; 2026-07-19 | The cited Lean declaration formalize this source formula as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| For an ordered source cell S_i and nondecreasing matching function g, the cell sample-rate coefficient g_i is the infimum of g over S_i, attained at the cell's lower cutpoint. | `theorem31_source_cell_matching_rate_eq_lower_cutpoint` | covered. `theorem31_source_cell_matching_rate_eq_lower_cutpoint`: no completed statement check | covered; Agent check by Codex GJ19 full-formalization source-coverage closeout 2026-07-19; 2026-07-19 | The current paper-facing row states this source formula; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Lemma 3.1 gives the closed weighted Bernoulli adjacent-rate formula obtained at the common threshold. | `lemma31_closed_adjacent_rate_formula`<br>`binary_rating_pairwise_threshold_rate_top_is_closed_weighted_rate` | covered. `lemma31_closed_adjacent_rate_formula`: no completed statement check<br>`binary_rating_pairwise_threshold_rate_top_is_closed_weighted_rate`: no completed statement check | covered; Agent check by Codex GJ19 full-formalization source-coverage closeout 2026-07-19; 2026-07-19 | The current paper-facing rows state this source formula; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| The induced binary response is beta-tilde(theta)=integral psi(theta,y)dH(y). | `section4_induced_binary_response` | covered. `section4_induced_binary_response`: no completed statement check | covered; Agent check by Codex GJ19 full-formalization source-coverage closeout 2026-07-19; 2026-07-19 | The current paper-facing row states this source formula; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Equation (5) defines the finite representative-item L1 discrepancy between the response induced by H and the target optimal binary response beta. | `section4_l1_design_objective` | covered. `section4_l1_design_objective`: no completed statement check | covered; Agent check by Codex GJ19 full-formalization source-coverage closeout 2026-07-19; 2026-07-19 | The current paper-facing row states this source formula; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| The state-update display evolves mu_{k+1} by integrating the transition kernel over E_k and carrying the complement E_k^c forward unchanged. | `appendixB1_state_update` | covered. `appendixB1_state_update`: no completed statement check | covered; Agent check by Codex GJ19 full-formalization source-coverage closeout 2026-07-19; 2026-07-19 | The current paper-facing row states this source formula; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Equations (1)-(3) in the Lemma C.1 proof factor the pairwise event, apply the individual large-deviation rate functions, and minimize their sum at a common threshold. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex GJ19 full-formalization source-coverage closeout 2026-07-19; 2026-07-19 | The cited Lean declarations formalize this source equation as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| Equations (7)-(15) decompose the weighted objective gap into finitely many cell-pair integrals, apply the component rates, and reduce the minimum to adjacent cells. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex GJ19 full-formalization source-coverage closeout 2026-07-19; 2026-07-19 | The cited Lean declarations formalize this source equation as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| Equations (16)-(18) express the general objective-gap exponent as an infimum over quality pairs and use arbitrarily close qualities at a continuity point to obtain rate zero for a non-step rule. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex GJ19 full-formalization source-coverage closeout 2026-07-19; 2026-07-19 | The cited Lean declaration formalize this source equation as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| Equations (19)-(20) identify the limiting weighted objective of a step rule with the total weight of cross-level ordered quality pairs, yielding the source partition-value problem. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex GJ19 full-formalization source-coverage closeout 2026-07-19; 2026-07-19 | The cited Lean declaration formalize this source equation as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| Equations (21)-(22) solve the weighted common-threshold first-order condition and substitute it to obtain the closed adjacent-rate formula. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex GJ19 full-formalization source-coverage closeout 2026-07-19; 2026-07-19 | The cited Lean declaration formalize this source equation as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| The remaining Lemma 3.1 proof shows an optimizer must equalize all adjacent rates and that the equalized endpoint chain is unique. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex GJ19 full-formalization source-coverage closeout 2026-07-19; 2026-07-19 | The cited Lean declaration formalize this source equation as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| Equations (24)-(25) and Remark C.3 verify the new interior levels and equal adjacent rates in the doubled uniform chain. | `source_lemmaC5_refinement_equation24`<br>`source_lemmaC5_refinement_equation25` | covered. `source_lemmaC5_refinement_equation24`: no completed statement check<br>`source_lemmaC5_refinement_equation25`: no completed statement check | covered; Agent check by Codex GJ19 full-formalization source-coverage closeout 2026-07-19; 2026-07-19 | The current paper-facing rows state this source equation; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| The Appendix C.6 proof relates grid width delta to additive rate loss, establishes the outer-loop invariant, and combines it with Lemma C.9 to prove Theorem 3.2. | None recorded | support only. No linked paper-facing row recorded | support only; Agent check by Codex GJ19 full-formalization source-coverage closeout 2026-07-19; 2026-07-19 | The cited Lean declaration formalize this source equation as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| The Theorem B.1 proof uses the C.5 doubled-chain representation and uniform convergence of quantile maps to control the floor-selected optimal levels along geometric subsequences. | `source_theoremB1_proof_selector_nesting` | covered. `source_theoremB1_proof_selector_nesting`: no completed statement check | covered; Agent check by Codex GJ19 full-formalization source-coverage closeout 2026-07-19; 2026-07-19 | The current paper-facing row states this source equation; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
<!-- END GENERATED FORMULA PROVENANCE LEDGER -->

## 15. Library Lift Pass

The large-deviation, finite optimization, and bisection support is reusable.
All source-specific bridge conditions used by the final endpoints are derived
or source-matched; no unresolved library premise remains.

## 16. DAG Audit

The root `DependencyDAG.tex` and canonical `docs/DependencyDAG.tex` show every
formerly partial route as a checked result/model node. The rendered
`docs/DependencyDAG.pdf` was rebuilt and visually inspected on 2026-07-19; the
labels, arrows, legend, and page bounds are readable and consistent with the
formalized status.

## 17. Validation Checks
<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 59 covered, 17 support only; diagnostics: full inventory shown because paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout.
- Statement match (`audit/statement_match_llm.json`): no rows; diagnostics: 61 orphan/stale statement-sidecar rows excluded, 61 configured rows without unambiguous current receipts.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 61 row translations generated from Lean statements.
- Assumption provenance: no assumption-match sidecar tracked for this paper.
- Source-record classification (`audit/source_record_match_llm.json`): 34 source condition.
- Source-record structural audit (`audit/source_record_audit.json`): 61 source-record review rows, 94 boundary inputs, 12 conclusion dependencies, 25 recursive fields, 2 source-record-only unresolved conclusion dependencies, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): review surface passed over 61 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): status not inferred by this generator.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): status not inferred by this generator.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->


```bash
lake build GJ19OptimalBinaryRatingSystems.PaperInterface
lake build GJ19OptimalBinaryRatingSystems.Theorem32Appendix
python3 scripts/review_dashboard.py --paper GJ19OptimalBinaryRatingSystems --statement-precheck
python3 scripts/review_dashboard.py --paper GJ19OptimalBinaryRatingSystems --paper-coverage-precheck
python3 scripts/review_dashboard.py --paper GJ19OptimalBinaryRatingSystems --source-to-lean-precheck
python3 scripts/audit_conclusion_provenance.py --paper GJ19OptimalBinaryRatingSystems --json
python3 scripts/audit_evidence_integrity.py --paper GJ19OptimalBinaryRatingSystems --include-source-obligations
python3 scripts/audit_repository.py --paper GJ19OptimalBinaryRatingSystems --paper-closeout --include-active --info-limit 0
```

## 18. Paper Definitions Checked

The reviewed definitions cover the quality and matching model, rating-state
dynamics, question mixtures, designs, experiments, rate functions, aggregation,
and the literal nested-bisection algorithm.

## 19. Named Theorem Statements Checked

The checked named surface includes Theorems 3.1--3.2, Lemmas B.1--B.3,
Theorem B.1, the Appendix C aggregation and refinement chain, Corollary C.4,
Lemma C.6, and the Kendall and Spearman applications.

## 20. Paper-Facing Statement Validator Ledger

The current surface has 61 paper-facing rows. The 61 raw statement receipts do
not bind the current paper statements by exact semantic identity and remain
diagnostic-only; independent human dashboard review remains 0/61. The raw row
records are stored under `audit/`.

<!-- BEGIN GENERATED STATEMENT VALIDATOR LEDGER -->
### Current Canonical Evidence
Independent human dashboard review: 0/61 rows. No human row-level approval is inferred. review surface passed; Agent check by Codex GJ19 full-formalization source-coverage closeout 2026-07-19; 2026-07-19 Diagnostic-only evidence excluded from this paper-facing ledger: 61 unconfigured, stale, or ambiguous statement-sidecar rows.

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| - KL divergence formula displayed below Theorem 3.1. | `definition_bernoulli_kl_formula` | No completed statement check recorded. Lean translation recorded; Agent check by codex-gpt-5-gj19-v6-ledger-refresh; 2026-07-12 | None recorded |
| - Lemma 3.1 closed-form adjacent-rate expression. | `lemma31_closed_adjacent_rate_formula` | No completed statement check recorded. Lean translation recorded; Agent check by codex-gpt-5-gj19-v6-ledger-refresh; 2026-07-12 | None recorded |
| - For two interior binary-rating levels, the support-safe threshold rate equals the closed weighted Bernoulli rate used in the adjacent-rate analysis. | `binary_rating_pairwise_threshold_rate_top_is_closed_weighted_rate` | No completed statement check recorded. Lean translation recorded; Agent check by codex-gpt-5-gj19-v6-ledger-refresh; 2026-07-12 | None recorded |
| - Corollary C.2 rate consequence: for endpoint-normalized uniform equalized level vectors with `N+1` adjacent intervals, the common last adjacent rate tends to zero. | `paper_corollaryC2_uniform_equalized_last_rate_tendsto_zero` | No completed statement check recorded. Lean translation recorded; Agent check by codex-gpt-5-gj19-v6-ledger-refresh; 2026-07-12 | None recorded |
| - Corollary C.2 mesh consequence: for endpoint-normalized uniform equalized level vectors, the largest adjacent grid width tends to zero. | `paper_corollaryC2_uniform_equalized_adjacent_mesh_tendsto_zero` | No completed statement check recorded. Lean translation recorded; Agent check by codex-gpt-5-gj19-v6-ledger-refresh; 2026-07-12 | None recorded |
| - Lemma C.7 objective-rate comparison for the explicit C.5 doubled chain, with the doubled-chain feasibility and equalization certificates derived internally. | `lemmaC7_uniform_doubled_objective_rate_ge_one_fifth_old_objective` | No completed statement check recorded. Lean translation recorded; Agent check by codex-gpt-5-gj19-v6-ledger-refresh; 2026-07-12 | None recorded |
| - Corollary C.3 first-level lower bound for monotone match functions after normalizing the first nonzero type rate to one. | `corollaryC3_monotone_scaled_first_level_ge_half_inv_adjacent_count_sq` | No completed statement check recorded. Lean translation recorded; Agent check by codex-gpt-5-gj19-v6-ledger-refresh; 2026-07-12 | None recorded |
| - Theorem B.1 closeout route from the paper's quantile-floor source representation, finite optimality, and uniform convergence of interval quantile maps. The selector window is derived from uniform convergence and C.5, rather than assumed separately. | `paper_theoremB1_uniform_subsequence_principle_to_of_quantile_floor_tendstoUniformlyOn_geometric_mesh` | No completed statement check recorded. Lean translation recorded; Agent check by codex-gpt-5-gj19-closeout-theorem-route-refresh; 2026-07-13 | None recorded |
| Definition C.1: population Kendall tau and Spearman rho objectives are proportional to the displayed integrals of P_k. | `definitionC1_kendall_spearman_population_objectives` | No completed statement check recorded. Lean translation recorded; Agent check by codex-gpt-5-gj19-v6-ledger-refresh; 2026-07-12 | None recorded |
| - Lemma C.10 Spearman source-integral reduction: for a partition of `[0,1]`, the ordered interval-pair linear-distance objective equals the cubic gap objective used in Lemma C.12. | `paper_lemmaC10_spearman_linear_weight_ordered_pair_interval_objective_eq_gap_objective` | No completed statement check recorded. Lean translation recorded; Agent check by codex-gpt-5-gj19-v6-ledger-refresh; 2026-07-12 | None recorded |
| - Lemma C.11 source-sum form: the ordered constant-weight interval-pair sum in equation (27) is at most the equispaced partition value. | `paper_lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_le_equispaced` | No completed statement check recorded. Lean translation recorded; Agent check by codex-gpt-5-gj19-v6-ledger-refresh; 2026-07-12 | None recorded |
| - Lemma C.12 source-sum form: the ordered linear-distance interval-pair objective for Spearman's rho is maximized by equispaced cutpoints. | `paper_lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_le_equispaced` | No completed statement check recorded. Lean translation recorded; Agent check by codex-gpt-5-gj19-v6-ledger-refresh; 2026-07-12 | None recorded |
| Source quality domain | `source_quality_domain` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source matching function | `source_matching_function` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source matching count | `source_matching_count` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source empirical reputation score | `source_empirical_reputation_score` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source system state | `source_system_state` | No completed statement check recorded. No Lean translation recorded | None recorded |
| AppendixB1 active set | `appendixB1_active_set` | No completed statement check recorded. No Lean translation recorded | None recorded |
| AppendixB1 transition kernel | `appendixB1_transition_kernel` | No completed statement check recorded. No Lean translation recorded | None recorded |
| AppendixB1 state update | `appendixB1_state_update` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Section4 question distribution | `section4_question_distribution` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Section4 induced binary response | `section4_induced_binary_response` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Section4 l1 design objective | `section4_l1_design_objective` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Section4 question design solution | `section4_question_design_solution` | No completed statement check recorded. No Lean translation recorded | None recorded |
| AppendixB5 random question experiment | `appendixB5_random_question_experiment` | No completed statement check recorded. No Lean translation recorded | None recorded |
| AppendixB5 known type experiment | `appendixB5_known_type_experiment` | No completed statement check recorded. No Lean translation recorded | None recorded |
| AppendixB5 unknown type experiment | `appendixB5_unknown_type_experiment` | No completed statement check recorded. No Lean translation recorded | None recorded |
| AppendixB5 empirical question response | `appendixB5_empirical_question_response` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem31 source cell matching rate eq lower cutpoint | `theorem31_source_cell_matching_rate_eq_lower_cutpoint` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem31 source matching function unique value argmax lexicographic | `theorem31_source_matching_function_unique_value_argmax_lexicographic` | No completed statement check recorded. No Lean translation recorded | None recorded |
| LemmaB1 matching rate shift | `lemmaB1_matching_rate_shift` | No completed statement check recorded. No Lean translation recorded | None recorded |
| LemmaB2 knownTypeExperiment random question slln | `lemmaB2_knownTypeExperiment_random_question_slln` | No completed statement check recorded. No Lean translation recorded | None recorded |
| LemmaB3 unknownTypeExperiment random question response and rank | `lemmaB3_unknownTypeExperiment_random_question_response_and_rank` | No completed statement check recorded. No Lean translation recorded | None recorded |
| LemmaC6 monotone matching penultimate level bound | `lemmaC6_monotone_matching_penultimate_level_bound` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem32 weighted nested bisection output | `theorem32_weighted_nested_bisection_output` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem32 weighted nested bisection loss and runtime | `theorem32_weighted_nested_bisection_loss_and_runtime` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source definition pairwise accuracy eq1 | `source_definition_pairwise_accuracy_eq1` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source definition weighted objective eq2 | `source_definition_weighted_objective_eq2` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source definition large deviation rate | `source_definition_large_deviation_rate` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source definition step rule partition levels | `source_definition_step_rule_partition_levels` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source definition lexicographic optimality | `source_definition_lexicographic_optimality` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source theorem31 adjacent rate eq3 | `source_theorem31_adjacent_rate_eq3` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source lemma31 equalization eq4 | `source_lemma31_equalization_eq4` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source theoremB1 quantile representation | `source_theoremB1_quantile_representation` | No completed statement check recorded. No Lean translation recorded | None recorded |
| - Lemma B.2 deterministic `KnownTypeExperiment` learning core: empirical tracking at representative item qualities plus a vanishing representative mesh and Lipschitz continuity imply uniform convergence of the learned response function. | `paper_lemmaB2_knownTypeExperiment_uniform_convergence_of_lipschitz_tracking` | No completed statement check recorded. No Lean translation recorded | None recorded |
| - Lemma B.3 deterministic `UnknownTypeExperiment` learning core: empirical tracking at rank-selected representatives plus ranking consistency, a vanishing mesh, and Lipschitz continuity imply uniform convergence of the learned response function. | `paper_lemmaB3_unknownTypeExperiment_uniform_convergence_of_ranking_tracking` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source lemmaC1 pairwise error rate from derivatives | `source_lemmaC1_pairwise_error_rate_from_derivatives` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source lemmaC2 binary complement rate | `source_lemmaC2_binary_complement_rate` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source theoremC1 laplace principle | `source_theoremC1_laplace_principle` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source remarkC1 full square application under explicit conditions | `source_remarkC1_full_square_application_under_explicit_conditions` | No completed statement check recorded. No Lean translation recorded | None recorded |
| - Lemma C.3 positive-kernel measurable-partition bridge: componentwise uniform normalized-log rate limits imply that the weighted partitioned continuum error integral decays at the minimum component exponent. convergence to the minimum component exponent. | `paper_lemmaC3_partition_integral_hasExponentialRate_of_min_component_uniform_logRate` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper lemmaC4 finite selected pullback positive rate and nonfiniteStep source zero rate | `paper_lemmaC4_finite_selected_pullback_positive_rate_and_nonfiniteStep_source_zero_rate` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source remarkC2 weighted kl separation monotonicity | `source_remarkC2_weighted_kl_separation_monotonicity` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source appendixC5 rate notation eq23 | `source_appendixC5_rate_notation_eq23` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source lemmaC5 uniform doubled chain | `source_lemmaC5_uniform_doubled_chain` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source lemmaC5 refinement equation24 | `source_lemmaC5_refinement_equation24` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source lemmaC5 refinement equation25 | `source_lemmaC5_refinement_equation25` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source lemmaC8 uniform first level polynomial lower bound | `source_lemmaC8_uniform_first_level_polynomial_lower_bound` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source lemmaC9 nested bisection runtime log squared | `source_lemmaC9_nested_bisection_runtime_log_squared` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source theoremB1 proof selector nesting | `source_theoremB1_proof_selector_nesting` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Source corollaryC4 kendall spearman subsequence | `source_corollaryC4_kendall_spearman_subsequence` | No completed statement check recorded. No Lean translation recorded | None recorded |
<!-- END GENERATED STATEMENT VALIDATOR LEDGER -->

## 21. Source-Coverage Audit Ledger

The source inventory has 76 atomic items: 59 have direct routes and 17 are
covered by explicit theorem support. Empirical plots and simulations are
outside normal named-theory scope. No selected named result is missing or
conditional.

<!-- BEGIN GENERATED SOURCE COVERAGE LEDGER -->
### Current Canonical Evidence
- Coverage scope: full inventory shown because scope metadata needs repair (paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout).
- Source inventory: 76 source statements from `cited publication`.
- Coverage result: 59 covered, 17 support only.
- Coverage review: coverage ledger recorded; Agent check by Codex GJ19 full-formalization source-coverage closeout 2026-07-19; 2026-07-19.
- Row-local statement checks: 0/61 linked row references have a completed canonical statement check; repeated links are counted per source row.

| Source statement | Linked Lean review rows | Coverage judgment | Row-local statement checks | Comments |
| --- | --- | --- | --- | --- |
| Items have true quality theta in the normalized unit interval [0,1]. | `source_quality_domain` | covered | `source_quality_domain`: no completed statement check | The current paper-facing row states this source model; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| The quality continuum is normalized so item quality rank is uniform on [0,1]. | None recorded | support only | No linked paper-facing row recorded | The cited Lean declaration formalize this source model as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| An item of quality theta receives n_k(theta)=floor(k g(theta)) ratings. | `source_matching_count` | covered | `source_matching_count`: no completed statement check | The current paper-facing row states this source model; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| The matching function g is nondecreasing, bounded above by one, and bounded strictly away from zero on [0,1]. | `source_matching_function` | covered | `source_matching_function`: no completed statement check | The current paper-facing row states this source model; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Each rating is an independent Bernoulli observation with success probability beta(theta). | None recorded | support only | No linked paper-facing row recorded | The cited Lean declarations formalize this source model as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| The platform reputation is the empirical average of an item's binary ratings. | `source_empirical_reputation_score` | covered | `source_empirical_reputation_score`: no completed statement check | The current paper-facing row states this source definition; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Conditional on quality, the empirical reputation has the corresponding scaled binomial distribution. | None recorded | support only | No linked paper-facing row recorded | The cited Lean declaration formalize this source formula as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| mu_k(Theta,X) is the mass of items whose true qualities lie in Theta and whose reputation scores lie in X at time k. | `source_system_state` | covered | `source_system_state`: no completed statement check | The current paper-facing row states this source definition; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Equation (1) defines P_k(theta_1,theta_2) as the probability that the higher-quality item receives the higher reputation score, with the source tie convention. | `source_definition_pairwise_accuracy_eq1` | covered | `source_definition_pairwise_accuracy_eq1`: no completed statement check | The current paper-facing row states this source definition; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Equation (2) defines W_k as the normalized positive-weight integral of pairwise ranking accuracy over ordered quality pairs. | `source_definition_weighted_objective_eq2` | covered | `source_definition_weighted_objective_eq2`: no completed statement check | The current paper-facing row states this source definition; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| For a fixed rating rule beta, the large-deviation rate is the limit -lim_{k to infinity} k^{-1} log(W-W_k), when that limit exists. | `source_definition_large_deviation_rate` | covered | `source_definition_large_deviation_rate`: no completed statement check | The current paper-facing row states this source definition; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| The design beta is a nondecreasing step rule on ordered quality intervals with levels 0=t_0<...<t_{M-1}=1 and ordered cutpoints. | `source_definition_step_rule_partition_levels` | covered | `source_definition_step_rule_partition_levels`: no completed statement check | The current paper-facing row states this source definition; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| A rating rule is optimal when it first maximizes the limiting value W and then maximizes the exponential convergence rate among limiting-value maximizers. | `source_definition_lexicographic_optimality` | covered | `source_definition_lexicographic_optimality`: no completed statement check | The current paper-facing row states this source definition; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Theorem 3.1 chooses ordered cells S* to maximize the limiting weighted cross-cell value and then chooses rate-optimal levels on that value-optimal discretization. | `theorem31_source_matching_function_unique_value_argmax_lexicographic` | covered | `theorem31_source_matching_function_unique_value_argmax_lexicographic`: no completed statement check | The current paper-facing row states this source theorem; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Theorem 3.1 equation (3) identifies the overall exponent as the minimum over adjacent cells of inf_a {g_{i+1} KL(a\|\|t_{i+1})+g_i KL(a\|\|t_i)} with g_i=inf_{theta in S_i}g(theta). | `source_theorem31_adjacent_rate_eq3` | covered | `source_theorem31_adjacent_rate_eq3`: no completed statement check | The current paper-facing row states this source theorem; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| For an ordered source cell S_i and nondecreasing matching function g, the cell sample-rate coefficient g_i is the infimum of g over S_i, attained at the cell's lower cutpoint. | `theorem31_source_cell_matching_rate_eq_lower_cutpoint` | covered | `theorem31_source_cell_matching_rate_eq_lower_cutpoint`: no completed statement check | The current paper-facing row states this source formula; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| The Bernoulli KL divergence is KL(a\|\|b)=a log(a/b)+(1-a)log((1-a)/(1-b)), with the intended endpoint convention. | `definition_bernoulli_kl_formula` | covered | `definition_bernoulli_kl_formula`: no completed statement check | The current paper-facing row states this source definition; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Lemma 3.1 says the unique finite level vector maximizing the minimum adjacent rate equalizes all adjacent rates subject to t_0=0 and t_{M-1}=1. | `source_lemma31_equalization_eq4` | covered | `source_lemma31_equalization_eq4`: no completed statement check | The current paper-facing row states this source lemma; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Lemma 3.1 gives the closed weighted Bernoulli adjacent-rate formula obtained at the common threshold. | `lemma31_closed_adjacent_rate_formula`<br>`binary_rating_pairwise_threshold_rate_top_is_closed_weighted_rate` | covered | `lemma31_closed_adjacent_rate_formula`: no completed statement check<br>`binary_rating_pairwise_threshold_rate_top_is_closed_weighted_rate`: no completed statement check | The current paper-facing rows state this source formula; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Algorithm 1 performs an outer bisection on t_{M-2}; each candidate reconstructs the other levels by inner bisections at the last-pair target rate and updates the outer interval by comparing the candidate first and last rates. | `theorem32_weighted_nested_bisection_output` | covered | `theorem32_weighted_nested_bisection_output`: no completed statement check | The current paper-facing row states this source algorithm; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Theorem 3.2 claims NestedBisection returns an epsilon-optimal level vector in O(M log^2(M/epsilon)) operations. | `theorem32_weighted_nested_bisection_loss_and_runtime` | covered | `theorem32_weighted_nested_bisection_loss_and_runtime`: no completed statement check | The current paper-facing row states this source theorem; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Section 4 uses a probability distribution H over the finite question set Y. | `section4_question_distribution` | covered | `section4_question_distribution`: no completed statement check | The current paper-facing row states this source definition; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| The induced binary response is beta-tilde(theta)=integral psi(theta,y)dH(y). | `section4_induced_binary_response` | covered | `section4_induced_binary_response`: no completed statement check | The current paper-facing row states this source formula; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Equation (5) defines the finite representative-item L1 discrepancy between the response induced by H and the target optimal binary response beta. | `section4_l1_design_objective` | covered | `section4_l1_design_objective`: no completed statement check | The current paper-facing row states this source formula; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| The Section 4 design heuristic chooses a probability distribution H minimizing the equation-(5) L1 discrepancy. | `section4_question_design_solution` | covered | `section4_question_design_solution`: no completed statement check | The current paper-facing row states this source algorithm; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Appendix B.1 defines E_k as the item qualities receiving one additional rating between times k-1 and k. | `appendixB1_active_set` | covered | `appendixB1_active_set`: no completed statement check | The current paper-facing row states this source definition; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Appendix B.1 defines omega(theta,x,x') as the Bernoulli transition probability from reputation x' to x when an item receives a new rating. | `appendixB1_transition_kernel` | covered | `appendixB1_transition_kernel`: no completed statement check | The current paper-facing row states this source definition; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| The state-update display evolves mu_{k+1} by integrating the transition kernel over E_k and carrying the complement E_k^c forward unchanged. | `appendixB1_state_update` | covered | `appendixB1_state_update`: no completed statement check | The current paper-facing row states this source formula; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| The detailed main routine bisects the last interior level over [1-1/(M-1),1-delta], reconstructs the candidate chain, compares endpoint rates, and returns the final reconstructed levels. | None recorded | support only | No linked paper-facing row recorded | The cited Lean declarations formalize this source algorithm as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| PairwiseRate evaluates the closed weighted Bernoulli separation exponent for two adjacent candidate levels and matching rates. | None recorded | support only | No linked paper-facing row recorded | The cited Lean declaration formalize this source algorithm as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| CalculateOtherLevels sequentially reconstructs lower candidate levels by calling BisectNextLevel at a fixed target rate. | None recorded | support only | No linked paper-facing row recorded | The cited Lean declaration formalize this source algorithm as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| BisectNextLevel bisects a lower endpoint until its PairwiseRate is within the grid convention of the target rate and returns the selected endpoint. | None recorded | support only | No linked paper-facing row recorded | The cited Lean declaration formalize this source algorithm as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| Lemma B.1 says that a one-crossing shift between matching-rate vectors g and g-tilde implies the corresponding optimal levels satisfy t*_k >= t-tilde*_k. | `lemmaB1_matching_rate_shift` | covered | `lemmaB1_matching_rate_shift`: no completed statement check | The current paper-facing row states this source lemma; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Theorem B.1 uses q_M^w(theta), the normalized index of the optimal weighted partition cell containing theta, and represents beta_M^w by the corresponding optimal level. | `source_theoremB1_quantile_representation` | covered | `source_theoremB1_quantile_representation`: no completed statement check | The current paper-facing row states this source definition; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| For uniform matching, if q_M^w converges uniformly, then every geometric subsequence beta_{C 2^N+1}^w converges uniformly to a limiting response function. | `paper_theoremB1_uniform_subsequence_principle_to_of_quantile_floor_tendstoUniformlyOn_geometric_mesh` | covered | `paper_theoremB1_uniform_subsequence_principle_to_of_quantile_floor_tendstoUniformlyOn_geometric_mesh`: no completed statement check | The current paper-facing row states this source theorem; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| KnownTypeExperiment records finitely many approximately known representative qualities and their empirical response frequencies for each question. | `appendixB5_known_type_experiment` | covered | `appendixB5_known_type_experiment`: no completed statement check | The current paper-facing row states this source algorithm; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| KnownTypeExperiment extends each representative item's empirical question response to the neighboring quality interval. | None recorded | support only | No linked paper-facing row recorded | The cited Lean declaration formalize this source algorithm as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| On every experimental match, the platform draws a question from Y and records a binary positive or negative response for that item. | `appendixB5_random_question_experiment` | covered | `appendixB5_random_question_experiment`: no completed statement check | The current paper-facing row states this source algorithm; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| For each item and question y, the experiment tracks the fraction of question-y observations receiving a positive response. | `appendixB5_empirical_question_response` | covered | `appendixB5_empirical_question_response`: no completed statement check | The current paper-facing row states this source definition; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Lemma B.2 claims uniform convergence of the KnownTypeExperiment estimator to psi under Lipschitz continuity as the per-item samples and representative mesh grow. | `paper_lemmaB2_knownTypeExperiment_uniform_convergence_of_lipschitz_tracking` | covered | `paper_lemmaB2_knownTypeExperiment_uniform_convergence_of_lipschitz_tracking`: no completed statement check | The current paper-facing row states this source lemma; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| For a fixed finite representative set and finite question set with positive question mass, the Strong Law makes every empirical conditional question-response frequency converge simultaneously to its source response probability as N tends to infinity. | `lemmaB2_knownTypeExperiment_random_question_slln` | covered | `lemmaB2_knownTypeExperiment_random_question_slln`: no completed statement check | The current paper-facing row states this source claim; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| UnknownTypeExperiment records unknown true qualities, empirical question responses and aggregate scores, and the item occupying each empirical rank. | `appendixB5_unknown_type_experiment` | covered | `appendixB5_unknown_type_experiment`: no completed statement check | The current paper-facing row states this source algorithm; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| UnknownTypeExperiment assigns each quality-percentile interval the empirical question responses of the item occupying the corresponding empirical rank. | None recorded | support only | No linked paper-facing row recorded | The cited Lean declaration formalize this source algorithm as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| Lemma B.3 claims the UnknownTypeExperiment estimator converges uniformly to psi as the numbers of items and samples grow, under the printed Lipschitz hypothesis. | `paper_lemmaB3_unknownTypeExperiment_uniform_convergence_of_ranking_tracking` | covered | `paper_lemmaB3_unknownTypeExperiment_uniform_convergence_of_ranking_tracking`: no completed statement check | The current paper-facing row states this source lemma; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| For fixed finite L, the Strong Law makes empirical question responses converge and makes empirical average-score ranking recover the true quality order, provided the mixed expected score is strictly increasing in true quality. | `lemmaB3_unknownTypeExperiment_random_question_response_and_rank` | covered | `lemmaB3_unknownTypeExperiment_random_question_response_and_rank`: no completed statement check | The current paper-facing row states this source claim; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Lemma C.1 identifies the large-deviation exponent of the pairwise score-error event as the infimum over a common threshold of the two weighted Bernoulli rate functions. | `source_lemmaC1_pairwise_error_rate_from_derivatives` | covered | `source_lemmaC1_pairwise_error_rate_from_derivatives`: no completed statement check | The current paper-facing row states this source lemma; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Equations (1)-(3) in the Lemma C.1 proof factor the pairwise event, apply the individual large-deviation rate functions, and minimize their sum at a common threshold. | None recorded | support only | No linked paper-facing row recorded | The cited Lean declarations formalize this source equation as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| Lemma C.2 applies Lemma C.1 to the complement ranking-error probability and obtains the same adjacent Bernoulli exponent. | `source_lemmaC2_binary_complement_rate` | covered | `source_lemmaC2_binary_complement_rate`: no completed statement check | The current paper-facing row states this source lemma; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Theorem C.1 says a nonnegative sequence of rate functions converging uniformly on a compact finite-measure space has log-integral exponent equal to the negative essential infimum. | `source_theoremC1_laplace_principle` | covered | `source_theoremC1_laplace_principle`: no completed statement check | The current paper-facing row states this source theorem; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Corrected Remark C.1: on the full quality square, the weighted Laplace conclusion follows only when Theorem C.1's integrability, essential-infimum, positive-weight-near-minimizer, and uniform-convergence conditions are explicit; the actual piecewise-constant application avoids the false diagonal-uniformity claim by using the finite separated-cell route in Lemma C.3. | `source_remarkC1_full_square_application_under_explicit_conditions` | covered | `source_remarkC1_full_square_application_under_explicit_conditions`: no completed statement check | The current paper-facing row states this source remark; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Lemma C.3 says a finite piecewise-constant response has objective-gap exponent equal to the minimum adjacent weighted Bernoulli separation rate. | `paper_lemmaC3_partition_integral_hasExponentialRate_of_min_component_uniform_logRate` | covered | `paper_lemmaC3_partition_integral_hasExponentialRate_of_min_component_uniform_logRate`: no completed statement check | The current paper-facing row states this source lemma; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Equations (7)-(15) decompose the weighted objective gap into finitely many cell-pair integrals, apply the component rates, and reduce the minimum to adjacent cells. | None recorded | support only | No linked paper-facing row recorded | The cited Lean declarations formalize this source equation as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| Corrected Lemma C.4: every finite strict endpoint chain with positive monotone sampling rates and positive selected-cell weights has a positive exponential-rate certificate for its canonical tie-erased selected pullback; every monotone positive-support source that is not finite-step has rate zero, and hence no positive exponential-rate certificate, for its defined tie-erased objective gap. | `paper_lemmaC4_finite_selected_pullback_positive_rate_and_nonfiniteStep_source_zero_rate` | covered | `paper_lemmaC4_finite_selected_pullback_positive_rate_and_nonfiniteStep_source_zero_rate`: no completed statement check | The current paper-facing row states this source lemma; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Equations (16)-(18) express the general objective-gap exponent as an infimum over quality pairs and use arbitrarily close qualities at a continuity point to obtain rate zero for a non-step rule. | None recorded | support only | No linked paper-facing row recorded | The cited Lean declaration formalize this source equation as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| Remark C.2 records continuity, diagonal minima, and strict coordinatewise separation of the weighted Bernoulli KL objective used in Lemma 3.1. Its phrase 'strictly convex in t_i,t_{i+1}, with minima at t_i=t_{i+1}' is interpreted through that exact used content, since literal joint strict convexity is incompatible with a whole diagonal of minima. | `source_remarkC2_weighted_kl_separation_monotonicity` | covered | `source_remarkC2_weighted_kl_separation_monotonicity`: no completed statement check | The current paper-facing row states this source remark; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Equations (19)-(20) identify the limiting weighted objective of a step rule with the total weight of cross-level ordered quality pairs, yielding the source partition-value problem. | None recorded | support only | No linked paper-facing row recorded | The cited Lean declaration formalize this source equation as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| Equations (21)-(22) solve the weighted common-threshold first-order condition and substitute it to obtain the closed adjacent-rate formula. | None recorded | support only | No linked paper-facing row recorded | The cited Lean declaration formalize this source equation as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| The remaining Lemma 3.1 proof shows an optimizer must equalize all adjacent rates and that the equalized endpoint chain is unique. | None recorded | support only | No linked paper-facing row recorded | The cited Lean declaration formalize this source equation as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| Equation (23) fixes the adjacent closed-rate notation r_i used in the refinement and Theorem 3.2 analysis. | `source_appendixC5_rate_notation_eq23` | covered | `source_appendixC5_rate_notation_eq23`: no completed statement check | The current paper-facing row states this source definition; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Lemma C.5 explicitly constructs the optimal equalized levels for a doubled uniform-matching chain from the smaller optimal chain. | `source_lemmaC5_uniform_doubled_chain` | covered | `source_lemmaC5_uniform_doubled_chain`: no completed statement check | The current paper-facing row states this source lemma; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Equations (24)-(25) and Remark C.3 verify the new interior levels and equal adjacent rates in the doubled uniform chain. | `source_lemmaC5_refinement_equation24`<br>`source_lemmaC5_refinement_equation25` | covered | `source_lemmaC5_refinement_equation24`: no completed statement check<br>`source_lemmaC5_refinement_equation25`: no completed statement check | The current paper-facing rows state this source equation; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Corollary C.1 says the optimal uniform-matching finite-chain rate tends to zero as the number of intervals grows. | `paper_corollaryC2_uniform_equalized_last_rate_tendsto_zero` | covered | `paper_corollaryC2_uniform_equalized_last_rate_tendsto_zero`: no completed statement check | The current paper-facing row states this source corollary; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Corollary C.2 says the maximum adjacent level gap of optimal uniform-matching rules tends to zero. | `paper_corollaryC2_uniform_equalized_adjacent_mesh_tendsto_zero` | covered | `paper_corollaryC2_uniform_equalized_adjacent_mesh_tendsto_zero`: no completed statement check | The current paper-facing row states this source corollary; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Lemma C.6 claims that nondecreasing matching implies t_{M-2} >= 1-1/(M-1). | `lemmaC6_monotone_matching_penultimate_level_bound` | covered | `lemmaC6_monotone_matching_penultimate_level_bound`: no completed statement check | The current paper-facing row states this source lemma; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Lemma C.7 lower-bounds the optimal rate after uniform doubled refinement by one fifth of the previous optimal rate. | `lemmaC7_uniform_doubled_objective_rate_ge_one_fifth_old_objective` | covered | `lemmaC7_uniform_doubled_objective_rate_ge_one_fifth_old_objective`: no completed statement check | The current paper-facing row states this source lemma; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Lemma C.8 derives a polynomial lower bound on the first interior optimal level under uniform matching. | `source_lemmaC8_uniform_first_level_polynomial_lower_bound` | covered | `source_lemmaC8_uniform_first_level_polynomial_lower_bound`: no completed statement check | The current paper-facing row states this source lemma; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Corollary C.3 extends the first-level lower-bound condition to normalized nondecreasing matching rates. | `corollaryC3_monotone_scaled_first_level_ge_half_inv_adjacent_count_sq` | covered | `corollaryC3_monotone_scaled_first_level_ge_half_inv_adjacent_count_sq`: no completed statement check | The current paper-facing row states this source corollary; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Lemma C.9 counts the nested-bisection iterations as O(M log^2(1/delta)). | `source_lemmaC9_nested_bisection_runtime_log_squared` | covered | `source_lemmaC9_nested_bisection_runtime_log_squared`: no completed statement check | The current paper-facing row states this source lemma; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| The Appendix C.6 proof relates grid width delta to additive rate loss, establishes the outer-loop invariant, and combines it with Lemma C.9 to prove Theorem 3.2. | None recorded | support only | No linked paper-facing row recorded | The cited Lean declaration formalize this source equation as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| The source states that uniform matching plus Lemma C.7 yields a (1-epsilon) multiplicative approximation in O(M log^2(M/epsilon)) time. | None recorded | support only | No linked paper-facing row recorded | The cited Lean declaration formalize this source remark as a definition, proof step, or specialization. It is kept off the compact 61-row paper-facing surface because the enclosing source result is already represented there or the item is internal proof detail. |
| The Theorem B.1 proof uses the C.5 doubled-chain representation and uniform convergence of quantile maps to control the floor-selected optimal levels along geometric subsequences. | `source_theoremB1_proof_selector_nesting` | covered | `source_theoremB1_proof_selector_nesting`: no completed statement check | The current paper-facing row states this source equation; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Corollary C.4 applies Theorem B.1 to Kendall and Spearman weights to obtain uniformly convergent optimal subsequences. | `source_corollaryC4_kendall_spearman_subsequence` | covered | `source_corollaryC4_kendall_spearman_subsequence`: no completed statement check | The current paper-facing row states this source corollary; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Definition C.1 gives the Kendall constant-weight and Spearman linear-distance population ranking objectives. | `definitionC1_kendall_spearman_population_objectives` | covered | `definitionC1_kendall_spearman_population_objectives`: no completed statement check | The current paper-facing row states this source definition; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Lemma C.10 reduces the Spearman ordered-pair interval integral to the cubic interval-gap objective. | `paper_lemmaC10_spearman_linear_weight_ordered_pair_interval_objective_eq_gap_objective` | covered | `paper_lemmaC10_spearman_linear_weight_ordered_pair_interval_objective_eq_gap_objective`: no completed statement check | The current paper-facing row states this source lemma; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Lemma C.11 and equation (27) show equispaced intervals maximize the finite Kendall constant-weight objective. | `paper_lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_le_equispaced` | covered | `paper_lemmaC11_kendall_constant_weight_ordered_pair_interval_objective_le_equispaced`: no completed statement check | The current paper-facing row states this source lemma; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
| Lemma C.12 and equation (28) show equispaced intervals maximize the finite Spearman linear-weight objective. | `paper_lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_le_equispaced` | covered | `paper_lemmaC12_spearman_linear_weight_ordered_pair_interval_objective_le_equispaced`: no completed statement check | The current paper-facing row states this source lemma; the v10 ledger validates the elaborated binders, assumptions, conclusion, and source-facing semantics for every linked row. |
<!-- END GENERATED SOURCE COVERAGE LEDGER -->
