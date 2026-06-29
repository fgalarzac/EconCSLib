# Formalization Plan: Designing Optimal Binary Rating Systems

- Namespace: `GJ19OptimalBinaryRatingSystems`
- Source target: AISTATS 2019 / PMLR 89 version plus supplementary PDF.
- Local source cache: `source/garg19a.pdf`, `source/garg19a.txt`,
  `source/garg19a-supp.pdf`, and `source/garg19a-supp.txt`. Use these local
  files; do not repeatedly web-search for the source.
- Current Lean endpoint: `lake build GJ19OptimalBinaryRatingSystems`.

## Current Plan Status (2026-06-28)

This file began as the initial outside-Lean formalization plan. Some phase
descriptions below are now historical. The current proof state is:

- the finite/discrete rating-design layer, Lemma 3.1 optimizer layer,
  Theorem 3.2 calculated-grid certificate layer, Appendix B.2/B.3 learning
  wrappers, and Lemma C.10-C.12 Kendall/Spearman finite objective reductions
  are Lean-checked;
- the fixed-discretization Theorem 3.1 source-`Wbar_k` bridges and the
  constant-weight, exact Spearman, and general integrable-weight Lebesgue
  `S*` cell-integral argmax/two-stage branches are Lean-checked;
- the raw C.4 reverse obstruction is Lean-checked under explicit
  positive-support/local-regularity fields, including wrappers where the
  one-dimensional `theta` distribution charges every nonempty open interval;
- the C.4 source-realization seam is now the selected-integral realization of
  the paper's tie-erased `Wbar_k` convention, not a generic Laplace-principle
  gap;
- the B.1 source seam is deriving one arbitrary-selector coherence route for
  optimal `beta_M` sequences. The preferred named route is `O(1/m)`
  quantile-floor limit tracking, with value-anchor, finite coarse-cell,
  metric-window, variable-width, and exact representative-transfer routes also
  checked.

The active tactical document is `FAST_FINISH_PLAN_2026-06-28.md`; use it for
the next proof steps.

## Initial Outside-Lean Paper Audit

### Source Scope And Model Assumptions

The paper studies a continuum of item qualities, normalized to the quantile
space `[0,1]`. A rating design is a nondecreasing map
`β : [0,1] -> [0,1]`; conditional on quality `θ`, ratings are Bernoulli with
success probability `β(θ)`. The score `x_k(θ)` is the fraction of positive
ratings among `n_k(θ) = floor(k g(θ))` samples.

The source assumes a nondecreasing matching-rate function `g`, with
`g(θ) <= 1` and bounded away from zero. The objective weight
`w(θ_1, θ_2)` is positive on ordered quality pairs and normalized so its
integral over `θ_1 > θ_2` is one. The main optimization is restricted to
stepwise increasing `β` with intervals `S_i` and levels `t_i`.

Formal statements must make the following premises visible when they are used:

- positivity and boundedness of `g`, especially when sample counts are
  `floor(k g(θ))`;
- monotonicity of `g` for Lemma B.1, Corollary C.3, and Theorem 3.2;
- strict ordering and endpoint conventions for levels, eventually
  `0 = t_0 < ... < t_{M-1} = 1`;
- finite-support Bernoulli domain restrictions for thresholds `a in [0,1]`;
- regularity/measurability/uniform-convergence assumptions for the continuum
  Laplace and bounded-convergence steps.

### Named Result Inventory

Main paper:

- Theorem 3.1: decomposition of optimal stepwise `β` into an optimal
  discretization `S*` and optimal levels `t*`; for fixed intervals the
  large-deviation rate is the minimum adjacent Bernoulli-KL threshold rate.
- Lemma 3.1: the unique optimal level vector equalizes adjacent rates and has
  endpoints `t_0 = 0`, `t_{M-1} = 1`; includes the closed adjacent-rate formula.
- Algorithm 1: `NestedBisection`.
- Theorem 3.2: `NestedBisection` returns an additive-`ε` optimal level vector
  in `O(M log^2(M/ε))` operations.

Supplement Appendix B:

- Lemma B.1: monotone shift of matching rates moves optimal levels.
- Theorem B.1: subsequential convergence of optimal `β_M` under uniform
  matching and uniform convergence of the interval quantile maps.  The Lean
  API now has both the equispaced identity-limit specialization and the
  source-facing arbitrary-quantile-limit statement; the open work is deriving
  the selector-tracking hypothesis for arbitrary optimal `β_M`.
- Lemma B.2: `KnownTypeExperiment` uniformly learns `ψ(θ,y)` under Lipschitz
  assumptions and SLLN.
- Lemma B.3: `UnknownTypeExperiment` uniformly learns `ψ(θ,y)` under ranking
  consistency, Lipschitz assumptions, and SLLN.

Supplement Appendix C:

- Lemma C.1: pairwise large-deviation rate for score comparisons.
- Lemma C.2: Bernoulli/KL specialization of the pairwise error rate.
- Theorem C.1: compact-space Laplace principle for a sequence of rate
  functions.
- Remark C.1: applies Theorem C.1 to `[0,1] x [0,1]` pairwise errors.
- Lemma C.3: rate of `W_k` for piecewise constant `β`.
- Lemma C.4: positive exponential rate iff `β` is piecewise constant.
- Remark C.2: KL convexity/monotonicity used in Lemma 3.1.
- Lemma C.5 and Remark C.3: doubling construction for uniform matching.
- Corollaries C.1-C.2: rate tends to zero and level mesh shrinks under uniform
  matching.
- Lemma C.6: upper endpoint lower bound under nondecreasing `g`.
- Lemma C.7: rate lower bound along doubling subsequence under uniform
  matching.
- Lemma C.8 and Corollary C.3: first-level lower bound `t_1 >= C M^-3`.
- Lemma C.9: `NestedBisection` runtime in terms of grid width `δ`.
- Theorem 3.2 proof: converts grid width `δ` to rate error `ε`.
- Theorem B.1 proof and Corollary C.4: subsequential convergence and the
  Kendall/Spearman consequence.
- Definition C.1 and Lemmas C.10-C.12: Kendall tau and Spearman rho fit the
  objective-weight framework and have equispaced optimal intervals.

The empirical, visualization, and implementation-heuristic sections are source
scope but not primary theorem-DAG targets. Lemmas B.2 and B.3 are named source
results, but they are a separate SLLN/experiment branch and do not feed
Theorem 3.1, Lemma 3.1, or Theorem 3.2.

### Formula And Source Sanity Notes

- The Bernoulli KL formula is consistent with the source:
  `KL(a || b) = a log(a/b) + (1-a) log((1-a)/(1-b))`.
- The support-safe convention is necessary. The source writes `inf_a` over
  `R`, but the Bernoulli finite-support rate is only finite for
  `a in [0,1]`. Existing GJ18 infrastructure uses `WithTop` for this exact
  reason, and GJ19 should follow that convention.
- Lemma C.2 replaces `1 - P_k` by a nonpositive score-gap probability. The
  displayed algebra has the usual strict-left/tie decomposition:
  `1 - P_k = 2 Pr(gap < 0) + Pr(gap = 0)`. Exact constants do not affect the
  exponential rate; the library already has constant-sandwich transfer for this
  `P_k` complement pattern.
- Lemma C.1 is written as a continuum integral over score means. For the binary
  finite-rating model, the safer Lean route is the existing finite iid/floor
  count LDP certificates in `FiniteRatingComparison`, then a paper-facing
  bridge to the Bernoulli formula.
- Lemma C.3's last step reduces the minimum over all interval pairs to adjacent
  pairs by monotonicity as levels move farther apart. This is a real proof
  obligation, not just algebra.
- Lemma C.4's reverse direction is informal: it uses the existence of a
  continuity point for non-piecewise monotone `β` and a nonuniform-convergence
  argument. Do not treat it as a small corollary of the finite rate formula.
- The supplement's extracted text around C.5 contains OCR/formatting artifacts;
  one line reads like `t_0 = 1`, but Lemma 3.1 and all rate formulas require
  `t_0 = 0`, `t_{M-1} = 1`. Use the PDF visually for C.5/Theorem 3.2 formulas.
- Theorem 3.2's statement hides several domain details needed in Lean: `M`
  large enough for indices such as `M-2`, positive/nondecreasing `g`, a grid
  width `δ` small enough relative to adjacent gaps, and the translation from
  `δ` to additive `ε`.

No definite mathematical source error is recorded at this stage, but Lemma 3.1,
Lemma C.3, Lemma C.4, and Theorem 3.2 each contain proof steps that must be
made much more explicit before being claimed as fully formalized.

## Shared-Library Reuse Checkpoint

Inspected reusable large-deviation infrastructure:

- `EconCSLib.Foundations.Probability.LargeDeviations`
  - `HasExponentialRate`, `HasExtendedExponentialRate`,
    `ExponentialRateCertificate`;
  - finite weighted-sum aggregation;
  - `FiniteErrorRateCertificate` and pairwise error certificates.
- `EconCSLib.Foundations.Probability.FiniteSupportMGF`
  - finite MGF/log-MGF/rate-function APIs;
  - convex derivative tools for rate-function minimizers;
  - `bernoulliKL`, `twoBernoulliThresholdRate`,
    `withTopRealScale`;
  - ternary Chernoff tools used by GGSG19.
- `EconCSLib.Foundations.Probability.IIDLargeDeviations` and
  `FiniteEmpiricalMultinomialCounts`
  - finite iid Cramer/method-of-types certificates;
  - score-gap left-tail exact-rate constructors.
- `EconCSLib.Foundations.Probability.FiniteRatingComparison`
  - `FiniteRatingLDPModel`;
  - `ratingRateFunctionTop`, `pairwiseSellerThresholdRateTop`;
  - two-sample floor-count comparison probabilities;
  - `twoSampleFloorPkComplementErrorProb` and constant-factor transfer;
  - `PairwiseThresholdRateTopLdpCertificate`;
  - finite-chain joint floor-rating samples and uniform-pair objectives.
- `EconCSLib.Foundations.Probability.FiniteRankingEvents`
  - interval-adjacent inversion event bounds.

Nearby paper lessons:

- GJ18 is the closest precedent. It already routes finite rating-scale
  pairwise LDP, floor-count `P_k`, adjacent-pair aggregation, and support-safe
  threshold rates through `FiniteRatingComparison`.
- GGSG19 is useful for generic finite iid Chernoff/Cramer and finite
  aggregation, but its ternary election-rate specialization is less directly
  useful than GJ18 for GJ19.
- PRPKG-style Laplace/continuous-order-statistic work is conceptually relevant
  to Theorem C.1, but the concrete existing useful layer for GJ19 is still the
  finite rating comparison stack.

Conclusion: GJ19 should not build local pairwise-LDP or finite aggregation
machinery. Refactor toward `FiniteRatingComparison` first. The genuinely
missing reusable library layer is binary-rating/Bernoulli optimization:
closed-form weighted Bernoulli KL minimizers, endpoint-safe closed rates,
monotonicity as endpoints separate, and finite adjacent-chain maximin
equalization.

## Proof Plan

### Phase 1: Route GJ19 Through Existing Finite-Rating LDP

Goal: make the current scaffold use the strongest existing library API before
adding new paper-local code.

Lean tasks:

1. Change the paper import from direct `FiniteSupportMGF`/`LargeDeviations`
   to `FiniteRatingComparison` where appropriate.
2. Add a reusable binary-rating specialization in the library if it can be
   kept paper-neutral:
   - a Bernoulli PMF on `Bool` or `Fin 2`;
   - score `false = 0`, `true = 1`;
   - mass formulas for the two atoms;
   - log-MGF/rate-function wrappers.
3. Prove source-shape identifications:
   - binary finite-rating `ratingRateFunctionTop` equals
     support-safe Bernoulli KL;
   - binary pairwise threshold objective equals
     `adjacentBinaryThresholdObjectiveTop`;
   - binary pairwise threshold rate equals
     `adjacentBinaryRatingRateTop`.
4. If GJ19 needs the same finite-chain ordered-pair infrastructure currently
   in GJ18, move paper-neutral pieces into `FiniteRatingComparison` instead of
   copying them into GJ19.

Expected result: a closed finite binary-rating LDP surface for adjacent pairs
and finite weighted objectives, still short of the continuum Theorem 3.1.

### Phase 2: Bernoulli Closed Adjacent Rate

Goal: turn Lemma 3.1's displayed adjacent closed-rate expression from a wrapper
into a derived minimization theorem.

Reusable library targets:

- derivative of `a ↦ g_lo KL(a || t_lo) + g_hi KL(a || t_hi)`;
- interior minimizer
  `a/(1-a) = ((t_lo/(1-t_lo))^g_lo *
              (t_hi/(1-t_hi))^g_hi)^(1/(g_lo+g_hi))`;
- closed base expression after substituting the minimizer;
- theorem that the closed expression realizes the support-safe infimum under
  clean hypotheses such as `0 < g_lo`, `0 < g_hi`,
  `0 <= t_lo`, `t_lo < t_hi`, `t_hi <= 1`.

Endpoint plan:

- First prove the interior theorem for `0 < t_lo < t_hi < 1`.
- Then add endpoint-specialized theorems for `(t_lo,t_hi) = (0,t)` and
  `(t,1)`, matching the source's first and last rates.
- Only combine endpoints into the paper-facing Lemma 3.1 once the endpoint
  conventions are explicit and no real-power/log undefinedness is hidden.

### Phase 3: Finite Adjacent-Chain Equalization

Goal: prove the optimization/equalization part of Lemma 3.1 in a reusable
form.

Likely abstraction:

- an adjacent-chain rate family `R_i(t_i,t_{i+1})`;
- each `R_i` increases when endpoints separate and decreases when they move
  closer;
- endpoint rates have the one-sided forms from Phase 2;
- a level vector with all adjacent rates equal is maximin optimal.

Proof route:

1. Prove an abstract finite-chain maximin theorem: if all adjacent rates are
   equal and each level move that increases one side decreases the next side,
   no perturbation can increase the minimum rate.
2. Prove a converse/equalization theorem: if a finite vector is maximin
   optimal and some minimum adjacent rate is not tied to neighbors, a local
   perturbation improves the minimum.
3. Prove uniqueness from inverse-chain monotonicity: an overall common rate
   determines `t_1` and `t_{M-2}`, then determines every interior level
   iteratively.

Potential difficulty: existence of a solution to the equalized system may
require intermediate value/bisection machinery. If this becomes long, expose a
source-shaped existence/uniqueness certificate first, prove optimality from the
certificate, and then discharge existence via bisection/continuity later.

### Phase 4: Finite Theorem 3.1 For Fixed Discretization

Goal: close the finite/discrete part of Theorem 3.1 before tackling the full
continuum statement.

Lean route:

1. Instantiate `FiniteRatingLDPModel` with the finite set of stepwise intervals
   and binary ratings.
2. Use `PairwiseThresholdRateTopLdpCertificate` or a derived binary
   specialization to get exact pairwise floor-count exponents.
3. Use the finite-chain adjacent-pair objective/aggregation theorem to show
   the finite ranking objective has rate equal to the minimum adjacent binary
   threshold rate.
4. Connect the support-safe extended rate to the paper's real formula under
   interior/endpoint hypotheses.

This phase should produce a valuable partial theorem: the paper's rate formula
for a fixed finite discretization, with the continuum choice of `S*` left for
later.

### Phase 5: Continuum Theorem 3.1

Goal: prove the full source decomposition of the optimal stepwise `β`.

Needed ingredients:

- bounded-convergence bridge for the limiting value of `W_k`;
- optimization of the interval partition `S*` from the limiting objective;
- Theorem C.1 or a finite/compact Laplace principle strong enough for the
  continuum integral in Lemma C.3;
- uniform convergence or explicit certificate that the pairwise rate functions
  satisfy Theorem C.1's hypotheses;
- adjacent-pair dominance from monotonicity.

Recommendation: do not start here until Phases 1-4 are stable. Theorem C.1 is
likely the hardest non-discrete analysis dependency and should be built as a
general library theorem only if it is needed by more than this paper or by a
clear public partial boundary.

### Phase 6: Algorithm 1 And Theorem 3.2

Goal: formalize `NestedBisection` and its approximation/runtime guarantee.

Required support:

- an abstract bisection correctness theorem for monotone scalar equations;
- an implementation of nested bisection over level vectors;
- Lemma C.6 endpoint lower bound and Corollary C.3 first-level lower bound;
- a Lipschitz/rate-loss bound converting grid width `δ` to additive `ε`;
- operation count `O(M log^2(M/ε))`.

Recommendation: only start after Lemma 3.1 is fully closed. The algorithm proof
depends heavily on equalization monotonicity and endpoint lower bounds.

### Phase 7: Appendix Examples And Learning Branch

Lower-risk later targets:

- Definition C.1 and Lemmas C.10-C.12 for Kendall/Spearman objective weights;
- Corollary C.4 once Theorem B.1 is available;
- Lemmas B.2/B.3 if the project wants the learning-experiment branch, using
  existing SLLN/probability infrastructure or adding a reusable finite-uniform
  LLN interface.

These do not block Theorem 3.1/Lemma 3.1 and should not distract from the
binary-rate proof path.

## Partial Formalization Boundaries

### Historical Boundary Decision

This section is retained as historical planning material. The original
near-term boundary was the finite/discrete GJ19 layer, with the continuum
Laplace-principle passage treated as a later reusable analysis library
project. That boundary has been substantially surpassed: the current remaining
continuum work is source-model assembly, selected-integral realization for
the tie-erased `Wbar_k` convention, and Appendix B selector/coherence.

Do not use the older wording below to describe current status without checking
`FINAL_VALIDATION_REPORT.md`, `POST_FORMALIZATION_AUDIT.md`, and
`ADDITIONAL_ASSUMPTIONS_NEEDED.md`.

Boundary A: binary-rate formula layer.

- Closes: Bernoulli KL formula, support-safe Bernoulli KL, adjacent rate
  formula, closed adjacent-rate formula as a derived minimization theorem.
- Leaves open: equalized maximin, finite/continuum `W_k` rate, algorithm.
- Usefulness: establishes the core analytic expression shared by later proofs.

Boundary B: finite fixed-discretization rate theorem.

- Closes: pairwise binary LDP, finite floor-count `P_k` transfer, finite
  adjacent-pair aggregation, and the fixed-`S` Theorem 3.1 rate formula.
- Leaves open: optimizing `S*` over the continuum, Lemma C.4, Theorem C.1 if
  not needed for the finite route, and `NestedBisection`.
- Usefulness: strongest likely near-term partial boundary; it reuses GJ18 and
  gives a genuine paper-facing theorem seam rather than only formula wrappers.

Boundary C: Lemma 3.1 fully closed.

- Closes: closed adjacent-rate minimization, equalization iff optimality, and
  uniqueness of the level vector.
- Leaves open: continuum Theorem 3.1 and Theorem 3.2 runtime.
- Usefulness: this is the main optimization heart of the paper and unlocks the
  algorithm proof.

Boundary D: Theorem 3.1 without Algorithm 1.

- Closes: optimal discretization/maximin decomposition and fixed-level rate
  proof, including the needed continuum Laplace/bounded-convergence bridge.
- Leaves open: `NestedBisection` approximation/runtime and possibly Appendix B
  convergence/learning lemmas.
- Usefulness: a strong partial formalization of the main theorem of the paper.

Boundary E: Theorem 3.2.

- Closes: `NestedBisection` approximation and runtime.
- Leaves open: possibly only secondary Appendix B/C example or learning
  branches.
- Usefulness: completes the algorithmic contribution, but likely requires the
  most new algorithm/real-analysis infrastructure after Lemma 3.1.

Recommended first commitment: Boundary B plus as much of Boundary C as is
tractable. If Boundary C's existence/uniqueness proof stalls, keep the
equalization certificate explicit and do not claim full Lemma 3.1.

## First Lean Targets

1. Refactor `MainTheorems.lean` to import `FiniteRatingComparison`.
2. Add paper-neutral binary-rating specializations in `EconCSLib` if no
   existing PMF/Bool API already gives the exact formulas cleanly.
3. Prove the binary finite-rating rate-function identification with
   support-safe Bernoulli KL.
4. Prove the adjacent binary pairwise-rate identification with
   `pairwiseSellerThresholdRateTop`.
5. Add a finite fixed-discretization theorem using
   `PairwiseThresholdRateTopLdpCertificate` and finite adjacent aggregation.
6. Start the Bernoulli minimizer/closed-rate derivation in the library.

Validation after each coherent batch:

```bash
lake build EconCSLib.Foundations.Probability.FiniteRatingComparison
lake build GJ19OptimalBinaryRatingSystems
```

Run the full review dashboard, post-formalization audit, DAG refresh, and final
validation report only at a real proof boundary, not after each planning edit.

## Transition Note: 2026-06-19

Current stopping point:

- The finite/discrete binary-rating layer, Corollary C.2 rate/mesh
  consequences, Lemmas C.5-C.9 support, selected endpoint-pair Lemma C.3
  aggregation, the fixed-discretization forward continuum bridge for Theorem
  3.1, the reverse C.4 zero-rate bridge layer, the C.10-C.12 finite
  Kendall/Spearman reductions, the finite ordered-pair `S*` optimizer layer
  with the midpoint-weighted finite-objective and source-range-lift
  identifications, the exact fixed-cutpoint equation-(20) cell-integral
  objective identity, and the continuity-supplied exact cell-integral
  argmax/two-stage bridges, plus the closed constant-weight Lebesgue
  and general integrable-weight Lebesgue cell-integral S* branches and the
  exact Spearman linear-weight rectangle/monotone finite-sum identities,
  the finite-step C.4 source-model iff under explicit structured
  source-realization fields, and the B.1/C.4 convergence bridges under
  explicit source-model witnesses compile.
- Recent cleanup packaged C.3/C.4 analytic ordered-rectangle bridges through
  the source endpoint-level-vector convention, so callers can use
  `BinaryEndpointLevelVector` instead of restating endpoint support,
  monotonicity, and interior positivity facts.
- The paper remains partial. The hard remaining work is still source-model
  derivation: deriving the non-piecewise C.4 witness package and the
  selected-integral realization from the paper model,
  deriving B.1-style source representation and optimal-sequence hypotheses,
  and closing the remaining source convergence branch.

Recommended next proof target:

1. Prove the uniform source Lemma C.8/Corollary C.3 polynomial first-level
   lower-bound layer. The useful missing input is an objective-rate lower
   bound for a concrete feasible endpoint vector, then transfer it to the
   equalized/maximin vector.
2. Start with an equispaced feasible endpoint vector:
   `equispacedEndpointLevels : Fin (m + 2) -> ℝ`, its
   `BinaryEndpointLevelVector` certificate, and a uniform lower bound on each
   adjacent rate.
3. Derive a polynomial lower bound of the form
   `c / ((m + 1 : ℝ) ^ 3) ≤
    binaryEndpointAwareAdjacentRateObjective optimal (fun _ => (1 : ℝ))`
   by combining the equispaced lower bound with
   `theorem31_rate_optimal_of_pairwise_equalized` or
   `binaryEndpointAwareAdjacentRateObjective_isMaximizerOn_of_pairwise_equalized`.
4. Feed that lower bound into
   `lemmaC8_uniform_first_level_ge_half_of_equalized_objective_rate_lower`.

Good first Lean proof shape:

```lean
have hfirst_level :
    rateLower / 2 ≤
      optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) :=
  lemmaC8_uniform_first_level_ge_half_of_equalized_objective_rate_lower
    hm hoptimal_levels heq hrateLower_nonneg hrateLower_le_one
    hrateLower_le_objective
```

Verification checkpoint before the next commit:

```bash
lake build GJ19OptimalBinaryRatingSystems
python3 scripts/review_dashboard.py --paper GJ19OptimalBinaryRatingSystems --precheck
```

## Fast Finish Update: 2026-06-28

The current detailed plan is `FAST_FINISH_PLAN_2026-06-28.md`. It supersedes
the older single-target transition notes for active proof work. The fastest
route to full closure is to discharge three source-model seams:

1. `S*` optimization: the moving-cell integral continuity theorem is now
   closed for any Lebesgue weight integrable on `[0,1]^2`. The fixed-cutpoint
   cell-integral objective is named and identified with the selected-support
   integral, continuity-supplied argmax/two-stage bridges are closed, the
   constant-weight and general integrable-weight no-premise S* branches are
   closed, the Spearman linear-weight rectangle integral is identified exactly
   with the midpoint-area formula on monotone cells, and the generic finite
   ordered-pair midpoint summand is already identified after lifting through
   `cutpointRangeFunctional`.
2. Lemma C.4 reverse direction: derive the
   `LemmaC4RawSourcePositiveSupportIntervalModel` and non-finite-range witness
   from the arbitrary monotone non-piecewise `beta` source model, rather than
   exposing those fields as paper-facing certificates. The exact-zero
   reverse theorem and finite-step iff are now closed once the
   positive-support fields, finite-step/non-piecewise source witness, and
   finite-level selected-integral realization is supplied. The
   selected-source coordinate-map, support measurability, support pullback
   containment, canonical selected pullback source convention, and integral
   congruence are Lean-checked; the
   fields are not derivable from the current `R` and `S` records alone.
3. Appendix B arbitrary selector: first try to prove exact pointwise
   normalization of arbitrary optimal representatives to the canonical
   representative on `[0,1]`, or finite coarse-cell uniqueness of refined and
   anchor quantile-floor selectors, consumed by
   `theoremB1UniformOptimalSubsequencePrincipleTo_of_uniform_optimal_quantile_floor_finite_coarse_cell`.
   If the source argument gives value-level control instead, use
   `theoremB1UniformOptimalSubsequencePrincipleTo_of_eventually_anchor_bound_by_subsequence`.
   If neither follows from the source hypotheses, document the corrected
   theorem with explicit selector regularity.

This is a proof-strategy update only. Do not update line-count fields,
aggregate generated status files, or website/paper tables until the proof
surface actually changes.

## Deviations And Assumptions

- The current interface is a scaffold, not a paper formalization.
- The full continuous discretization result still needs Appendix C's
  continuum-to-finite large-deviation/Laplace argument plus optimization
  structure.
- The support-safe finite-support convention is intentionally stricter than the
  paper's informal all-real `inf_a`; this is the correct Lean convention for
  Bernoulli finite-support rates and matches the prior GJ18 formalization.
- Theorem 3.2 will need explicit finite-size and grid-width hypotheses that
  are implicit in the prose.
