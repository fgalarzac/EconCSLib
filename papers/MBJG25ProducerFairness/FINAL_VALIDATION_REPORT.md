# Final Validation Report: MBJG25 Producer Fairness

Updated: 2026-07-31

## 1. Human Verdict

Formalized. The checked development covers the paper's fixed and responsive
rating models, both named theorems, the fairness and regret metrics, and the
mathematical content of Appendices C--F. Formalization found three local source
errors: an endpoint overstatement and two appendix formula typos. In each case,
the surrounding mathematics uniquely determines the correction and the
corrected result plus comparison evidence is checked. These are disclosed
source notes, not caveats to the paper's substantive conclusions.

## 2. Closeout Status

- Completion status: formalized.
- Mathematical surface: 39 source-curated review rows, comprising 11 explicit
  source conditions and 28 definitions or proved claims.
- Lean footprint: 981 paper-local Lean lines; `PaperInterface.lean` is 584
  lines and exposes 28 definition/theorem rows, joined to 11 assumption rows.
- Main caveat: none.
- Release certification: separate from mathematical status. Saved human
  source-to-Lean review is currently 0 of 39 rows, so the paper is not being
  represented as independently human-certified.
- Paper-local receipt: the focused build and current semantic evidence gates
  are recorded in Section 17.

## 3. Source and Scope

- Paper: *Balancing Producer Fairness and Efficiency via Prior-Weighted Rating
  System Design*.
- Authors: Thomas Ma, Michael S. Bernstein, Ramesh Johari, and Nikhil Garg.
- Source version: ICWSM 2025, DOI `10.1609/icwsm.v19i1.35854`, corresponding to
  arXiv:2207.04369.
- Public source: https://arxiv.org/abs/2207.04369
- Audited source PDF SHA-256:
  `fe566f61676aa347d331aa666a6533adc1325784cd5195f5068fab704fa6b981`.
- Page, section, theorem, and equation locators in
  `audit/paper_statement_map.json` identify the reviewed source passages.

The source-first inventory includes every mathematical definition, displayed
formula, named theorem, theorem-like appendix result, and stated sampling rule:
Equations 1--5; Theorems 3.1--3.2; the responsive-market Thompson rule;
Appendix C's conditional MSE derivation; Appendix D's weighted Bayesian rating;
Appendix E's ordinal posterior rating; and Appendix F's `k`-sampling mechanism
and endpoint comparisons. Raw datasets, calibrated estimates, simulator
implementation details, plots, and numerical findings are empirical
non-theorem scope. Named mathematical instantiations are not excluded on that
basis.

## 4. Researcher Summary of Checked Results

- The binary posterior rating, fixed-market mean squared error, bias, variance,
  and finite bias--variance decomposition are exposed directly.
- Theorem 3.1's squared-bias monotonicity and variance monotonicity are checked:
  variance decreases weakly on the full Bernoulli interval and strictly in its
  interior, with both endpoint failures proved explicitly.
- Theorem 3.2's squared-bias convexity and prior-mean minimizer, and variance
  concavity and one-half maximizer, are checked.
- Selection rate, quality-conditional individual producer unfairness,
  marketplace producer unfairness, finite-horizon expected regret, and the
  one-profile Thompson-sampling choice law are represented at their source
  semantic level.
- Appendix C's responsive MSE identity is proved from finite conditional
  probability laws and conditional mean and variance identities.
- Appendix D's displayed weighted rating is proved equal to both its simplified
  form and the binary posterior with the corrected pseudo-count shape.
- Appendix E's corrected finite Dirichlet posterior formula is exposed, and its
  exact reduction to the expression printed in Equation 21 at zero prior mass
  is proved.
- Appendix F's top-`k` uniform rule is exposed, together with the proved
  `k = 1` argmax endpoint and full-market uniform endpoint.

## 5. Remaining Boundaries and Gaps

No mathematical proof boundary remains on the 39-item source inventory. There
is no caller-supplied paper conclusion, unresolved certificate, weaker model,
or unproved concrete instantiation on the declared surface.

The absence of saved human row judgments is a release-certification boundary,
not a mathematical-formalization gap. Empirical source artifacts listed in
Section 3 are also outside theorem scope; all associated mathematical formulas
and algorithms that make source claims are included.

## 6. Additional Assumptions Beyond Paper

None.

The interface makes ordinary source domains explicit: positive prior-shape
mass, positive or nonnegative review time, Bernoulli quality bounds,
nonnegative and ordered prior strengths, nonempty finite markets, and a
positive observed count in Appendix D's displayed expression containing
`k/n`. The strict-variance interior conditions are not new assumptions used to
rescue a restricted proof; they are the exact domain correction forced by the
source variance formula, and Lean also proves the full-interval weak result and
both excluded endpoint counterexamples.

## 7. Proof-Strategy Deviations

- Appendix C's informal tower-law derivation is implemented using a finite PMF
  over review-count states and finite conditional PMFs over ratings. A generic
  finite bias--variance identity is proved first, so the paper-facing result
  does not assume its own pointwise decomposition.
- The responsive Thompson row specifies the source's mathematical one-period
  law as a joint posterior-profile draw followed by an argmax map. Calibrated
  independent Beta draws are an empirical model instance, not a hidden theorem
  premise.
- Appendix D and E use the uniquely source-implied corrected formulas described
  in Section 10 rather than encoding the printed typos.
- Appendix F constructs a size-`k` top set from the sampled profile by
  maximizing total score over all size-`k` subsets, then proves cross-cutoff
  dominance by exchange. Thus cutoff tie resolution is explicit without
  accepting either the top set or its dominance property from the caller.

## 8. Proof Tricks Worth Reusing

- Prove finite bias--variance algebra from expectation linearity before
  instantiating a conditional stochastic model.
- When strict monotonicity fails only at a compact-domain endpoint, expose the
  weak closed-domain theorem, the strict interior theorem, and concrete
  endpoint counterexamples as separate review rows.
- For a formula typo whose correction is uniquely pinned by adjacent notation,
  prove both the corrected formula and a direct comparison to the printed
  expression.
- For a finite top-`k` rule, maximize total score over size-`k` subsets and use
  a one-element exchange contradiction to derive cross-cutoff dominance; then
  prove advertised parameter endpoints from that constructed mechanism.

## 9. Generalizations, Conjectures, and Extensions

- The finite PMF bias--variance theorem is model-neutral and is a candidate for
  a shared probability/statistics module.
- The corrected ordinal posterior definition already works for any finite
  category type and arbitrary real rating values, rather than only a fixed
  five-star scale.
- The `k`-sampling statement makes cutoff ties explicit. Further results about
  monotonic tradeoffs as `k` varies would require new claims; the source states
  only the mechanism and its two endpoints.
- No unproved generalization or conjecture is used to support completion.

## 10. Mathematical Typos or Other Fixes Suggested in the Source Paper

1. **Theorem 3.1 endpoint domain.** The printed strict variance decrease cannot
   hold at `q_v = 0` or `q_v = 1`, because the numerator
   `t q_v (1-q_v)` is zero for every prior strength. The corrected statement is
   weak decrease on `0 <= q_v <= 1` and strict decrease on `0 < q_v < 1` under
   the source's remaining conditions. Lean checks both statements and both
   endpoint counterexamples.
2. **Appendix D, Equation 20 prior label.** The displayed estimator and baseline
   mean `C` use pseudo-counts `mC` and `m(1-C)`. The corresponding strength-one
   shape is `Beta(C, 1-C)`, not the printed `Beta(C, 1)`. Lean proves the
   weighted-average simplification and its equality to the corrected binary
   posterior formula.
3. **Appendix E, Equation 21 prior terms.** The surrounding text introduces a
   Dirichlet prior `alphaHat`, names the estimate by that prior, and then scales
   it by `eta`, but the printed display omits `alphaHat_j` from numerator and
   denominator. The corrected posterior uses `alphaHat_j + N_j` in both sums.
   Lean exposes that formula and proves that the printed display is exactly its
   zero-prior special case.

## 11. Paper Issues or Caveats

None at caveat level. The three issues in Section 10 are minor source
corrections with no status impact: they are local domain or formula repairs
whose corrected targets are uniquely determined and fully checked, while the
paper's substantive fairness--efficiency conclusions remain unchanged.

## 12. Detailed Formalization Evidence

`PaperInterface.lean` is the canonical 39-row review surface. The source-first
statement map pins 39 source items one-to-one to those rows. Current evidence
uses statement match v10, paper coverage v4, Lean-to-TeX v3, assumption
provenance v3, review-surface v2, source-record v7, and source-proof fidelity
schema 2.

All 39 statement rows are judged `matches`; all 39 source items are `covered`;
28 non-assumption rows have context-free Lean-to-TeX translations; all 11
assumption rows have exact source provenance; and the 39-row review surface
passes. The schema-2 fidelity ledger records three minor source corrections
with no status impact and includes explicit corrected-statement evidence for
each one.

The current v7 source-record audit has 46 boundary inputs. Thirty-six are
covered atom-by-atom by their current v10 semantic ledgers. Ten representation
or market-nonemptiness inputs have current independent judgments: five
finite-equality instances are proved from finite representation primitives;
four carrier-nonemptiness instances and one per-period available-set
nonemptiness condition are validated source assumptions. There are no
recursive-field failures, conclusion dependencies, or unresolved source
records.

## 13. Paper Assumption Provenance

<!-- BEGIN GENERATED ASSUMPTION PROVENANCE LEDGER -->
### Current Canonical Evidence
Generated from the configured source-condition surface and exact current statement digests in the canonical assumption-provenance sidecar. Model, agent, and automated checks are identified as such; no human review is inferred. Diagnostic-only evidence excluded from this ledger: 11 unconfigured, stale, or ambiguous source-condition sidecar rows.

| Assumption declaration | Lean declaration | Source location / statement | Assumption validators | Comments |
| --- | --- | --- | --- | --- |
| Assumption positive prior shape | `assumption_positive_prior_shape` | - The prior shape has positive total mass. | No completed assumption check recorded | None recorded |
| Assumption positive time | `assumption_positive_time` | - The fixed-setting theorem is evaluated after a positive number of timesteps. | No completed assumption check recorded | None recorded |
| Assumption positive rating count | `assumption_positive_rating_count` | None recorded | No completed assumption check recorded | None recorded |
| Assumption nonnegative time | `assumption_nonnegative_time` | - Nonnegative time/sample mass for Jensen concavity and global maximum statements. | No completed assumption check recorded | None recorded |
| Assumption quality nonnegative | `assumption_quality_nonnegative` | - True quality lies in the closed Bernoulli quality interval. | No completed assumption check recorded | None recorded |
| Assumption quality at most one | `assumption_quality_at_most_one` | - True quality lies in the closed Bernoulli quality interval. | No completed assumption check recorded | None recorded |
| Assumption quality positive | `assumption_quality_positive` | - Interior true quality for the corrected strict variance statement. | No completed assumption check recorded | None recorded |
| Assumption quality lt one | `assumption_quality_lt_one` | - Interior true quality for the corrected strict variance statement. | No completed assumption check recorded | None recorded |
| Assumption prior strength nonnegative | `assumption_prior_strength_nonnegative` | - Prior strength is nonnegative. | No completed assumption check recorded | None recorded |
| Assumption prior strength weak order | `assumption_prior_strength_weak_order` | - Prior strength weakly increases. | No completed assumption check recorded | None recorded |
| Assumption prior strength strict order | `assumption_prior_strength_strict_order` | - Prior strength strictly increases. | No completed assumption check recorded | None recorded |
<!-- END GENERATED ASSUMPTION PROVENANCE LEDGER -->

## 14. Displayed Formula Provenance

<!-- BEGIN GENERATED FORMULA PROVENANCE LEDGER -->
### Current Canonical Evidence
Rows are selected from semantic `formula` and `equation` source-kind metadata within the configured semantic source-coverage scope, never from declaration names. Coverage and statement checks remain separate evidence lanes. Scope metadata needs repair, so the full inventory is shown: paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout

| Paper formula / subclaim | Lean declaration | Provenance | Validators | Comments |
| --- | --- | --- | --- | --- |
| After fixing prior shape (alpha_tilde,beta_tilde) and strength eta, the conditional expected posterior rating in the fixed model is (eta*alpha_tilde + t*q_v) / (eta*alpha_tilde + eta*beta_tilde + t). | `paper_posterior_mean` | covered. `paper_posterior_mean`: no completed statement check | covered; Agent check by Codex MBJG25 source inventory coverage auditor 2026-07-18; 2026-07-18 | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| The fixed-model conditional variance of the posterior rating is t*q_v*(1-q_v)/(eta*alpha_tilde + eta*beta_tilde + t)^2. | `paper_variance` | covered. `paper_variance`: no completed statement check | covered; Agent check by Codex MBJG25 source inventory coverage auditor 2026-07-18; 2026-07-18 | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
<!-- END GENERATED FORMULA PROVENANCE LEDGER -->

## 15. Library Lift Pass

The audit found one plausible reusable lift:
`Responsive.finite_bias_variance_decomposition`, a finite-PMF version of the
standard identity. It remains paper-local in this remediation because the
shared-library API is outside this paper-scoped commit; a later lift should
target a generic probability/statistics module and retain this paper wrapper.
No paper-source formula has been moved into reusable library code.

## 16. DAG Audit

`docs/DependencyDAG.tex` represents the fixed model, both named theorems,
responsive metrics and choice rules, Appendices C--F, and all three source
notes without caveat or partial styling. `docs/DependencyDAG.pdf` is rendered
from that source with `latexmk`. The rendered one-page PDF was visually
inspected after the final topology edit: the legend, node labels, source-note
boxes, and dependency arrows are readable, with no node or label overlap and
no arrow running through text.

## 17. Validation Checks
<!-- BEGIN GENERATED LLM-AS-JUDGE RESULTS -->
### LLM-as-Judge Results
- Source coverage (`audit/paper_coverage_llm.json`): 39 covered; diagnostics: full inventory shown because paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout.
- Statement match (`audit/statement_match_llm.json`): no rows; diagnostics: 39 orphan/stale statement-sidecar rows excluded, 11 orphan/stale source-condition sidecar rows excluded, 39 configured rows without unambiguous current receipts.
- Lean-to-TeX translations (`audit/lean_to_tex_llm.json`): 28 row translations generated from Lean statements.
- Assumption provenance (`audit/assumption_match_llm.json`): no current configured source-condition receipts; diagnostics: 11 unconfigured, stale, or ambiguous source-condition sidecar rows excluded, 11 configured source conditions without unambiguous current receipts.
- Source-record classification (`audit/source_record_match_llm.json`): 3 derived, 3 source condition.
- Source-record structural audit (`audit/source_record_audit.json`): 39 source-record review rows, 46 boundary inputs, 0 conclusion dependencies, 0 recursive fields, 0 source-record-only unresolved conclusion dependencies, 0 recursion failures.
- Review-surface audit (`audit/review_surface_llm.json`): review surface passed over 39 review rows.
- Holistic source-first audit (`docs/AGENT_SOURCE_AUDIT.md`): status not inferred by this generator.
- DAG/source/source-json audit (`docs/PUBLIC_DAG_HOLISTIC_AUDIT_2026-07-02.md`): status not inferred by this generator.
<!-- END GENERATED LLM-AS-JUDGE RESULTS -->


- `lake build MBJG25ProducerFairness`: passed; 3,345 jobs completed.
- `python3 scripts/audit_conclusion_provenance.py --paper MBJG25ProducerFairness`:
  0 errors across 1 paper.
- `python3 scripts/audit_evidence_integrity.py --paper MBJG25ProducerFairness`:
  0 errors and 1 release-certification warning for incomplete human review
  (0/39).
- Source-record v7 refresh: 39 review rows, 46 boundary inputs, 10 current
  judgments, 0 recursion failures, and 0 unresolved conclusion dependencies.
- Targeted closeout command:
  `python3 scripts/audit_repository.py --paper MBJG25ProducerFairness --paper-closeout --include-active --info-limit 0`.

## 18. Paper Definitions Checked

The reviewed definitions cover the posterior rating, bias, variance, fixed and
responsive mean squared error, selection rate, producer-unfairness measures,
finite-horizon regret, Thompson sampling, the corrected appendix ratings, and
the top-`k` sampling rule. Their exact paper-facing declarations and formulas
are listed in Sections 13--14.

## 19. Named Theorem Statements Checked

| Source result | Status | Note |
| --- | --- | --- |
| Theorem 3.1 squared-bias monotonicity | formalized | Source direction and domain preserved. |
| Theorem 3.1 variance monotonicity | formalized | Weak closed interval, strict interior, both endpoint counterexamples. |
| Theorem 3.2 squared-bias convexity and minimizer | formalized | Prior-mean minimizer exposed. |
| Theorem 3.2 variance concavity and maximizer | formalized | One-half maximizer exposed. |
| Appendix C responsive MSE decomposition | formalized | Finite conditional laws and both conditional moments explicit. |
| Appendix D Equation 20 equivalence | formalized | Corrected Beta shape note. |
| Appendix E ordinal posterior | formalized | Corrected Equation 21 and zero-prior comparison. |
| Appendix F `k`-sampling endpoints | formalized | `k=1` argmax and full-market uniformity proved. |

## 20. Paper-Facing Statement Validator Ledger

The configured surface contains 39 rows: 28 definition/result statements and
11 source conditions. None of the raw statement or condition receipts binds the
current cached semantic identities, so those rows remain diagnostic-only.
Independent human dashboard review remains 0/39; no such sign-off is claimed
here.

<!-- BEGIN GENERATED STATEMENT VALIDATOR LEDGER -->
### Current Canonical Evidence
Independent human dashboard review: 0/39 rows. No human row-level approval is inferred. review surface passed; Agent check by Codex MBJG25 paper-surface curator 2026-07-18; 2026-07-18 Diagnostic-only evidence excluded from this paper-facing ledger: 39 unconfigured, stale, or ambiguous statement-sidecar rows, 11 unconfigured, stale, or ambiguous source-condition sidecar rows.

| Paper-facing statement | Lean declaration | Validators | Validator comments |
| --- | --- | --- | --- |
| Paper posterior rating | `paper_posterior_rating` | No completed statement check recorded. No Lean translation recorded | None recorded |
| - The posterior mean estimated quality in the fixed binary rating model. Paper Definition: $\frac{\eta \widetilde{\alpha} + t q_v} {\eta(\widetilde{\alpha}+\widetilde{\beta}) + t}$ | `paper_posterior_mean` | No completed statement check recorded. Lean translation recorded; Agent check by Codex MBJG25 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| - The bias of the estimated quality. Paper Definition: $E[\hat{q}_v] - q_v$ | `paper_bias` | No completed statement check recorded. Lean translation recorded; Agent check by Codex MBJG25 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| - The variance of the estimated quality. Paper Definition: $\frac{t q_v (1 - q_v)} {(\eta(\widetilde{\alpha}+\widetilde{\beta}) + t)^2}$ | `paper_variance` | No completed statement check recorded. Lean translation recorded; Agent check by Codex MBJG25 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| - The squared bias of the estimated quality. Paper Definition: $(E[\hat{q}_v] - q_v)^2$ | `paper_squared_bias` | No completed statement check recorded. Lean translation recorded; Agent check by Codex MBJG25 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| Paper fixed market mse | `paper_fixed_market_mse` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper facing fixed mse decomposition | `paper_facing_fixed_mse_decomposition` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Theorem 3.1. Suppose we have a prior-weighted rating system in the fixed setting with prior parameters (η α̃, η β̃). Fix product v with true quality qv and consider quality estimation after t timesteps. ≥ 0 increases, (1) squared bias 2 E[q̂ηα̃,ηβ̃ (v, t)\|qv ] − qv is nondecreasing; (2) variThen, as η  This demonstrates that variance is always strictly decreasing for η ≥ 0. ance Var[q̂ηα̃,ηβ̃ (v, t)\|qv ] is stri... | `paper_facing_theorem3_1_variance_weak_decrease` | No completed statement check recorded. Lean translation recorded; Agent check by Codex MBJG25 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| Theorem 3.1. Suppose we have a prior-weighted rating system in the fixed setting with prior parameters (η α̃, η β̃). Fix product v with true quality qv and consider quality estimation after t timesteps. ≥ 0 increases, (1) squared bias 2 E[q̂ηα̃,ηβ̃ (v, t)\|qv ] − qv is nondecreasing; (2) variThen, as η  This demonstrates that variance is always strictly decreasing for η ≥ 0. ance Var[q̂ηα̃,ηβ̃ (v, t)\|qv ] is stri... | `paper_facing_theorem3_1_variance_strict_decrease_interior` | No completed statement check recorded. Lean translation recorded; Agent check by Codex MBJG25 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| Theorem 3.1. Suppose we have a prior-weighted rating system in the fixed setting with prior parameters (η α̃, η β̃). Fix product v with true quality qv and consider quality estimation after t timesteps. ≥ 0 increases, (1) squared bias 2 E[q̂ηα̃,ηβ̃ (v, t)\|qv ] − qv is nondecreasing; (2) variThen, as η  This demonstrates that variance is always strictly decreasing for η ≥ 0. ance Var[q̂ηα̃,ηβ̃ (v, t)\|qv ] is stri... | `paper_facing_theorem3_1_squared_bias_nondecreasing` | No completed statement check recorded. Lean translation recorded; Agent check by Codex MBJG25 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| Theorem 3.2. Suppose we have a prior-weighted rating system in the fixed setting with prior parameters (η α̃, η β̃). Consider quality estimation after t timesteps.  Then, as a function of true product quality, squared bias 2 E[q̂ηα̃,ηβ̃ (v, t)\|qv ] − qv is convex with a global mini- α̃ mum at α̃+ , while variance Var[q̂ηα̃,ηβ̃ (v, t)\|qv ] is concave β̃ with a global maximum at 1/2. Variance can also be broken do... | `paper_facing_theorem3_2_squared_bias_convex_in_quality` | No completed statement check recorded. Lean translation recorded; Agent check by Codex MBJG25 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| Theorem 3.2. Suppose we have a prior-weighted rating system in the fixed setting with prior parameters (η α̃, η β̃). Consider quality estimation after t timesteps.  Then, as a function of true product quality, squared bias 2 E[q̂ηα̃,ηβ̃ (v, t)\|qv ] − qv is convex with a global mini- α̃ mum at α̃+ , while variance Var[q̂ηα̃,ηβ̃ (v, t)\|qv ] is concave β̃ with a global maximum at 1/2. Variance can also be broken do... | `paper_facing_theorem3_2_squared_bias_global_min_at_prior_mean` | No completed statement check recorded. Lean translation recorded; Agent check by Codex MBJG25 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| Theorem 3.2. Suppose we have a prior-weighted rating system in the fixed setting with prior parameters (η α̃, η β̃). Consider quality estimation after t timesteps.  Then, as a function of true product quality, squared bias 2 E[q̂ηα̃,ηβ̃ (v, t)\|qv ] − qv is convex with a global mini- α̃ mum at α̃+ , while variance Var[q̂ηα̃,ηβ̃ (v, t)\|qv ] is concave β̃ with a global maximum at 1/2. Variance can also be broken do... | `paper_facing_theorem3_2_variance_concave_in_quality` | No completed statement check recorded. Lean translation recorded; Agent check by Codex MBJG25 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| Theorem 3.2. Suppose we have a prior-weighted rating system in the fixed setting with prior parameters (η α̃, η β̃). Consider quality estimation after t timesteps.  Then, as a function of true product quality, squared bias 2 E[q̂ηα̃,ηβ̃ (v, t)\|qv ] − qv is convex with a global mini- α̃ mum at α̃+ , while variance Var[q̂ηα̃,ηβ̃ (v, t)\|qv ] is concave β̃ with a global maximum at 1/2. Variance can also be broken do... | `paper_facing_theorem3_2_variance_global_max_at_half` | No completed statement check recorded. Lean translation recorded; Agent check by Codex MBJG25 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| Theorem 3.1. Suppose we have a prior-weighted rating system in the fixed setting with prior parameters (η α̃, η β̃). Fix product v with true quality qv and consider quality estimation after t timesteps. ≥ 0 increases, (1) squared bias 2 E[q̂ηα̃,ηβ̃ (v, t)\|qv ] − qv is nondecreasing; (2) variThen, as η  This demonstrates that variance is always strictly decreasing for η ≥ 0. ance Var[q̂ηα̃,ηβ̃ (v, t)\|qv ] is stri... | `paper_facing_theorem3_1_variance_strict_decrease_counterexample_quality_zero` | No completed statement check recorded. Lean translation recorded; Agent check by Codex MBJG25 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| Theorem 3.1. Suppose we have a prior-weighted rating system in the fixed setting with prior parameters (η α̃, η β̃). Fix product v with true quality qv and consider quality estimation after t timesteps. ≥ 0 increases, (1) squared bias 2 E[q̂ηα̃,ηβ̃ (v, t)\|qv ] − qv is nondecreasing; (2) variThen, as η  This demonstrates that variance is always strictly decreasing for η ≥ 0. ance Var[q̂ηα̃,ηβ̃ (v, t)\|qv ] is stri... | `paper_facing_theorem3_1_variance_strict_decrease_counterexample_quality_one` | No completed statement check recorded. Lean translation recorded; Agent check by Codex MBJG25 context-free Lean translator 2026-07-18; 2026-07-18 | None recorded |
| Paper facing selection rate | `paper_facing_selection_rate` | No completed statement check recorded. No Lean translation recorded | None recorded |
| - Section 4: Individual Producer Unfairness. Defined as the standard deviation in Selection Rate (SR) among producers with the same true quality `q`. | `paper_facing_individual_producer_unfairness` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper facing marketplace producer unfairness | `paper_facing_marketplace_producer_unfairness` | No completed statement check recorded. No Lean translation recorded | None recorded |
| - Section 4: Thompson Sampling. A dynamic policy that selects an arm by drawing from a belief distribution and picking the argmax. | `paper_facing_thompson_sampling_mechanism` | No completed statement check recorded. No Lean translation recorded | None recorded |
| - Section 4: Expected Regret (Efficiency). The total expected regret across a finite time horizon. | `paper_facing_expected_regret` | No completed statement check recorded. No Lean translation recorded | None recorded |
| - Appendix C: MSE Decomposition in the responsive setting. When the number of reviews $N$ is a random variable, the expected mean squared error conditional on true quality decomposes into the expected squared bias and the expected variance. | `paper_facing_responsive_mse_decomposition` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper facing eq20 bayesian rating equivalence | `paper_facing_eq20_bayesian_rating_equivalence` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper ordinal posterior rating | `paper_ordinal_posterior_rating` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper facing eq21 zero prior comparison | `paper_facing_eq21_zero_prior_comparison` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper facing k sampling mechanism | `paper_facing_k_sampling_mechanism` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper facing k sampling one is argmax | `paper_facing_k_sampling_one_is_argmax` | No completed statement check recorded. No Lean translation recorded | None recorded |
| Paper facing k sampling market size is uniform | `paper_facing_k_sampling_market_size_is_uniform` | No completed statement check recorded. No Lean translation recorded | None recorded |
| - The prior shape has positive total mass. | `assumption_positive_prior_shape` | No completed source-condition check recorded | None recorded |
| - The fixed-setting theorem is evaluated after a positive number of timesteps. | `assumption_positive_time` | No completed source-condition check recorded | None recorded |
| Assumption positive rating count | `assumption_positive_rating_count` | No completed source-condition check recorded | None recorded |
| - Nonnegative time/sample mass for Jensen concavity and global maximum statements. | `assumption_nonnegative_time` | No completed source-condition check recorded | None recorded |
| - True quality lies in the closed Bernoulli quality interval. | `assumption_quality_nonnegative` | No completed source-condition check recorded | None recorded |
| - True quality lies in the closed Bernoulli quality interval. | `assumption_quality_at_most_one` | No completed source-condition check recorded | None recorded |
| - Interior true quality for the corrected strict variance statement. | `assumption_quality_positive` | No completed source-condition check recorded | None recorded |
| - Interior true quality for the corrected strict variance statement. | `assumption_quality_lt_one` | No completed source-condition check recorded | None recorded |
| - Prior strength is nonnegative. | `assumption_prior_strength_nonnegative` | No completed source-condition check recorded | None recorded |
| - Prior strength weakly increases. | `assumption_prior_strength_weak_order` | No completed source-condition check recorded | None recorded |
| - Prior strength strictly increases. | `assumption_prior_strength_strict_order` | No completed source-condition check recorded | None recorded |
<!-- END GENERATED STATEMENT VALIDATOR LEDGER -->

## 21. Source-Coverage Audit Ledger

The source-first inventory contains 39 mathematical items, all with recorded
coverage. Their 39 declaration links do not currently bind exact semantic
statement receipts and remain diagnostic at the row-local validation lane. The
inventory includes Equations 1--5, Theorems 3.1--3.2,
the responsive-market formulas, and the mathematical content of Appendices
C--F. Empirical data, fitted estimates, plots, simulator implementation, and
numerical findings are outside normal named-theory scope.

<!-- BEGIN GENERATED SOURCE COVERAGE LEDGER -->
### Current Canonical Evidence
- Coverage scope: full inventory shown because scope metadata needs repair (paper_statement_map.json must explicitly set source_coverage_mode before a source-coverage closeout).
- Source inventory: 39 source statements from `source.pdf`.
- Coverage result: 39 covered.
- Coverage review: coverage ledger recorded; Agent check by Codex MBJG25 source inventory coverage auditor 2026-07-18; 2026-07-18.
- Row-local statement checks: 0/39 linked row references have a completed canonical statement check; repeated links are counted per source row.

| Source statement | Linked Lean review rows | Coverage judgment | Row-local statement checks | Comments |
| --- | --- | --- | --- | --- |
| Equation 1 defines the posterior mean rating after binary feedback as (alpha_hat + R(v,t)) / (alpha_hat + beta_hat + \|S(v,t)\|). | `paper_posterior_rating` | covered | `paper_posterior_rating`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| After fixing prior shape (alpha_tilde,beta_tilde) and strength eta, the conditional expected posterior rating in the fixed model is (eta*alpha_tilde + t*q_v) / (eta*alpha_tilde + eta*beta_tilde + t). | `paper_posterior_mean` | covered | `paper_posterior_mean`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| The fixed-model bias is the conditional expected posterior rating minus true product quality q_v. | `paper_bias` | covered | `paper_bias`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| The fixed-model conditional variance of the posterior rating is t*q_v*(1-q_v)/(eta*alpha_tilde + eta*beta_tilde + t)^2. | `paper_variance` | covered | `paper_variance`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| The squared-bias component is the square of conditional expected posterior rating minus true quality. | `paper_squared_bias` | covered | `paper_squared_bias`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Equation 2 defines fixed-market MSE as the average over products of squared posterior-rating error relative to true quality. | `paper_fixed_market_mse` | covered | `paper_fixed_market_mse`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Equation 3 states that conditional mean squared error for one product equals squared conditional bias plus conditional variance. | `paper_facing_fixed_mse_decomposition` | covered | `paper_facing_fixed_mse_decomposition`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Corrected Theorem 3.1 variance conclusion: on 0 <= q_v <= 1, increasing nonnegative prior strength weakly decreases posterior-rating variance. | `paper_facing_theorem3_1_variance_weak_decrease` | covered | `paper_facing_theorem3_1_variance_weak_decrease`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Corrected Theorem 3.1 strict conclusion: for 0 < q_v < 1, positive elapsed reviews, positive prior-shape mass, and a strict increase in nonnegative prior strength, posterior-rating variance strictly decreases. | `paper_facing_theorem3_1_variance_strict_decrease_interior` | covered | `paper_facing_theorem3_1_variance_strict_decrease_interior`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Theorem 3.1 states that squared conditional bias is nondecreasing as prior strength eta increases in the fixed model. | `paper_facing_theorem3_1_squared_bias_nondecreasing` | covered | `paper_facing_theorem3_1_squared_bias_nondecreasing`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Theorem 3.2 states that squared bias is convex as a function of true product quality. | `paper_facing_theorem3_2_squared_bias_convex_in_quality` | covered | `paper_facing_theorem3_2_squared_bias_convex_in_quality`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Theorem 3.2 states that squared bias has a global minimum at the prior mean alpha_tilde/(alpha_tilde+beta_tilde). | `paper_facing_theorem3_2_squared_bias_global_min_at_prior_mean` | covered | `paper_facing_theorem3_2_squared_bias_global_min_at_prior_mean`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Theorem 3.2 states that posterior-rating variance is concave as a function of true product quality. | `paper_facing_theorem3_2_variance_concave_in_quality` | covered | `paper_facing_theorem3_2_variance_concave_in_quality`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Theorem 3.2 states that posterior-rating variance has a global maximum at true quality one half. | `paper_facing_theorem3_2_variance_global_max_at_half` | covered | `paper_facing_theorem3_2_variance_global_max_at_half`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| At q_v=0, the variance numerator t*q_v*(1-q_v) is zero for every prior strength, refuting the printed closed-interval strict wording at the lower endpoint. | `paper_facing_theorem3_1_variance_strict_decrease_counterexample_quality_zero` | covered | `paper_facing_theorem3_1_variance_strict_decrease_counterexample_quality_zero`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| At q_v=1, the variance numerator t*q_v*(1-q_v) is zero for every prior strength, refuting the printed closed-interval strict wording at the upper endpoint. | `paper_facing_theorem3_1_variance_strict_decrease_counterexample_quality_one` | covered | `paper_facing_theorem3_1_variance_strict_decrease_counterexample_quality_one`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Section 2.3 defines a product's selection rate as its number of selections (equivalently ratings) divided by its lifespan. | `paper_facing_selection_rate` | covered | `paper_facing_selection_rate`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Equation 5 defines quality-conditional individual producer unfairness as the standard deviation of selection rates among products with the same true quality. | `paper_facing_individual_producer_unfairness` | covered | `paper_facing_individual_producer_unfairness`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Marketplace-level producer unfairness is the expectation of quality-conditional individual unfairness over true product qualities. | `paper_facing_marketplace_producer_unfairness` | covered | `paper_facing_marketplace_producer_unfairness`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| In each responsive-market period, Thompson sampling draws one posterior-quality value for every currently available product and chooses a product attaining the maximum draw. | `paper_facing_thompson_sampling_mechanism` | covered | `paper_facing_thompson_sampling_mechanism`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Equation 4 defines finite-horizon expected regret as the expected sum of the quality gap between the best currently available product and the selected product. | `paper_facing_expected_regret` | covered | `paper_facing_expected_regret`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Appendix C Equations 19-20 apply the tower law over random review count and decompose responsive-market conditional MSE into expected squared fixed-model bias plus expected fixed-model variance. | `paper_facing_responsive_mse_decomposition` | covered | `paper_facing_responsive_mse_decomposition`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| The fixed prior shape has positive total mass so its Beta mean and scaled prior parameters are defined. | `assumption_positive_prior_shape` | covered | `assumption_positive_prior_shape`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| The fixed-setting results evaluate quality after a positive number of elapsed review timesteps. | `assumption_positive_time` | covered | `assumption_positive_time`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Elapsed time and review-count mass are nonnegative in the fixed and responsive models. | `assumption_nonnegative_time` | covered | `assumption_nonnegative_time`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Every product's Bernoulli true quality satisfies 0 <= q_v. | `assumption_quality_nonnegative` | covered | `assumption_quality_nonnegative`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Every product's Bernoulli true quality satisfies q_v <= 1. | `assumption_quality_at_most_one` | covered | `assumption_quality_at_most_one`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| The corrected strict-variance conclusion restricts true quality to 0 < q_v so that the Bernoulli variance numerator is positive. | `assumption_quality_positive` | covered | `assumption_quality_positive`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| The corrected strict-variance conclusion restricts true quality to q_v < 1 so that the Bernoulli variance numerator is positive. | `assumption_quality_lt_one` | covered | `assumption_quality_lt_one`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Prior strength eta is nonnegative in the source parameterization (alpha_hat,beta_hat)=(eta*alpha_tilde,eta*beta_tilde). | `assumption_prior_strength_nonnegative` | covered | `assumption_prior_strength_nonnegative`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| The nondecreasing/nonincreasing clauses compare a lower prior strength eta_low with eta_high satisfying eta_low <= eta_high. | `assumption_prior_strength_weak_order` | covered | `assumption_prior_strength_weak_order`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Strict variance decrease compares prior strengths satisfying eta_low < eta_high. | `assumption_prior_strength_strict_order` | covered | `assumption_prior_strength_strict_order`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Equation 20's observed-rating weighted-average expression is evaluated for a positive observed rating count n. | `assumption_positive_rating_count` | covered | `assumption_positive_rating_count`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Equation 20 simplifies the convex combination of the observed positive-rating share and population baseline C to (k+m*C)/(n+m), which is the binary posterior formula with pseudo-counts m*C and m*(1-C). | `paper_facing_eq20_bayesian_rating_equivalence` | covered | `paper_facing_eq20_bayesian_rating_equivalence`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Corrected Equation 21: under a Dirichlet prior, ordinal posterior expected rating is the rating-value-weighted sum of prior pseudo-count plus observed count, divided by total prior plus observed mass. | `paper_ordinal_posterior_rating` | covered | `paper_ordinal_posterior_rating`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| The expression printed in Equation 21 is exactly the zero-prior special case of the corrected Dirichlet posterior expected-rating formula. | `paper_facing_eq21_zero_prior_comparison` | covered | `paper_facing_eq21_zero_prior_comparison`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| Appendix F defines k-sampling by taking the k products with the highest values in the sampled reward profile and selecting uniformly from that top-k set. | `paper_facing_k_sampling_mechanism` | covered | `paper_facing_k_sampling_mechanism`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| At k=1, k-sampling selects the profile argmax and is the one-profile choice step of traditional Thompson sampling. | `paper_facing_k_sampling_one_is_argmax` | covered | `paper_facing_k_sampling_one_is_argmax`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
| When k equals the number of products in the market, k-sampling is uniform random selection over the whole market. | `paper_facing_k_sampling_market_size_is_uniform` | covered | `paper_facing_k_sampling_market_size_is_uniform`: no completed statement check | The complete source definition, formula, condition, corrected theorem target, or defect-evidence item is exposed by the routed reviewed row; claim-bearing items are theorem-proved and all rows have complete v10 ledgers. |
<!-- END GENERATED SOURCE COVERAGE LEDGER -->
