import MBJG25ProducerFairness.MainTheorems
import MBJG25ProducerFairness.Assumptions
import MBJG25ProducerFairness.ResponsiveMarket
import EconCSLib.Learning.Bandits.ThompsonSampling
import EconCSLib.Algorithms.Online.Regret
import Mathlib.Probability.Distributions.Uniform

/-!
# Paper Interface: Prior-Weighted Rating Fairness

This file is the single-file human-facing Lean interface for the ICWSM 2025
*Balancing Producer Fairness and Efficiency via Prior-Weighted Rating System Design*
formalization. The declarations are ordered to match paper presentation:

1. fixed binary-rating model definitions,
2. Theorem 3.1 claims,
3. Theorem 3.2 claims,
4. boundary audit notes,
5. responsive-market metrics and the Appendix C decomposition,
6. Appendix D--F rating formulas and sampling variants.

If this file typechecks and the commented statements match your paper notes, the
folder has a consistent paper-facing proof surface.
-/

namespace MBJG25ProducerFairness

open scoped BigOperators

/-! ## 1) Binary-rating model primitives - -/

/-- The posterior rating after a product has received binary feedback.
    Source status: direct paper formula (Equation 1)
    Paper Definition:
    $\frac{\widehat\alpha + R(v,t)}
            {\widehat\alpha+\widehat\beta+|S(v,t)|}$
-/
noncomputable def paper_posterior_rating
    (alphaHat betaHat : ℝ) (positiveRatings totalRatings : ℕ) : ℝ :=
  (alphaHat + positiveRatings) / (alphaHat + betaHat + totalRatings)

/-- The posterior mean estimated quality in the fixed binary rating model.
    Source status: direct paper formula
    Paper Definition:
    $\frac{\eta \widetilde{\alpha} + t q_v}
            {\eta(\widetilde{\alpha}+\widetilde{\beta}) + t}$
-/
noncomputable def paper_posterior_mean (alpha beta eta t q_v : ℝ) : ℝ :=
  (eta * alpha + t * q_v) / (eta * alpha + eta * beta + t)

/-- The bias of the estimated quality.
    Source status: direct paper formula
    Paper Definition: $E[\hat{q}_v] - q_v$
-/
noncomputable def paper_bias (alpha beta eta t q_v : ℝ) : ℝ :=
  (eta * alpha + t * q_v) / (eta * alpha + eta * beta + t) - q_v

/-- The variance of the estimated quality.
    Source status: direct paper formula
    Paper Definition:
    $\frac{t q_v (1 - q_v)}
            {(\eta(\widetilde{\alpha}+\widetilde{\beta}) + t)^2}$
-/
noncomputable def paper_variance (alpha beta eta t q_v : ℝ) : ℝ :=
  t * q_v * (1 - q_v) / (eta * alpha + eta * beta + t) ^ 2

/-- The squared bias of the estimated quality.
    Source status: direct paper formula
    Paper Definition: $(E[\hat{q}_v] - q_v)^2$
-/
noncomputable def paper_squared_bias (alpha beta eta t q_v : ℝ) : ℝ :=
  (paper_bias alpha beta eta t q_v) ^ 2

/-- Fixed-market mean squared error across a nonempty finite product set.
    Source status: direct paper formula (Equation 2)
-/
noncomputable def paper_fixed_market_mse
    {V : Type*} [Fintype V] [Nonempty V]
    (estimatedQuality trueQuality : V → ℝ) : ℝ :=
  (∑ v : V, (estimatedQuality v - trueQuality v) ^ 2) /
    (Fintype.card V : ℝ)

/-- Fixed-setting bias--variance decomposition for one product's rating law.
    Source status: direct paper identity (Equation 3)
-/
theorem paper_facing_fixed_mse_decomposition
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (rating_dist : PMF Ω) (posterior_rating : Ω → ℝ) (q_v : ℝ) :
    EconCSLib.pmfExp rating_dist (fun ω =>
      (posterior_rating ω - q_v) ^ 2) =
      (EconCSLib.pmfExp rating_dist posterior_rating - q_v) ^ 2 +
        EconCSLib.pmfExp rating_dist (fun ω =>
          (posterior_rating ω -
            EconCSLib.pmfExp rating_dist posterior_rating) ^ 2) := by
  exact MBJG25ProducerFairness.Responsive.finite_bias_variance_decomposition
    rating_dist posterior_rating q_v

/-! ## 2) Theorem 3.1 statements -/

/--
Theorem 3.1, variance weakly decreases in prior strength:
for full quality interval `0 ≤ q_v ≤ 1`, if prior strength increases the
posterior-mean variance is nonincreasing.
Source status: corrected source statement
Source note: The paper's Theorem 3.1 variance monotonicity claim is split here into a weak full-interval statement and a strict interior statement because the unqualified strict statement fails at `q_v = 0` and `q_v = 1`.
-/
theorem paper_facing_theorem3_1_variance_weak_decrease
    {alpha beta t q etaLow etaHigh : ℝ}
    (hshape : assumption_positive_prior_shape alpha beta)
    (ht : assumption_positive_time t)
    (hq0 : assumption_quality_nonnegative q)
    (hq1 : assumption_quality_at_most_one q)
    (hetaLow_nonneg : assumption_prior_strength_nonnegative etaLow)
    (heta_le : assumption_prior_strength_weak_order etaLow etaHigh) :
    paper_variance alpha beta etaHigh t q ≤
      paper_variance alpha beta etaLow t q := by
  simpa [paper_variance, EconCSLib.Statistics.priorWeightedVariance] using
    paper_theorem3_1_variance_weak_decrease
      hshape ht hq0 hq1 hetaLow_nonneg heta_le

/--
Theorem 3.1, strict decrease on interior quality values.
For `0 < q_v < 1`, positive prior-shape mass, positive number of prior samples,
and stronger prior strength `η_high > η_low`, variance is strictly decreasing.
Source status: corrected source statement
Source note: The paper states strict variance decrease without excluding boundary qualities; this formal statement adds `0 < q_v < 1` because variance is identically zero at `q_v = 0` and `q_v = 1`.
-/
theorem paper_facing_theorem3_1_variance_strict_decrease_interior
    {alpha beta t q etaLow etaHigh : ℝ}
    (hshape : assumption_positive_prior_shape alpha beta)
    (ht : assumption_positive_time t)
    (hq0 : assumption_quality_positive q)
    (hq1 : assumption_quality_lt_one q)
    (hetaLow_nonneg : assumption_prior_strength_nonnegative etaLow)
    (heta_lt : assumption_prior_strength_strict_order etaLow etaHigh) :
    paper_variance alpha beta etaHigh t q <
      paper_variance alpha beta etaLow t q := by
  simpa [paper_variance, EconCSLib.Statistics.priorWeightedVariance] using
    paper_theorem3_1_variance_strict_decrease_interior
      hshape ht hq0 hq1 hetaLow_nonneg heta_lt

/--
Theorem 3.1, squared posterior-mean bias is nondecreasing in prior strength.
With stronger prior (`η_high ≥ η_low`) and basic nonnegativity assumptions,
the squared bias term does not decrease.
Source status: direct paper statement
-/
theorem paper_facing_theorem3_1_squared_bias_nondecreasing
    {alpha beta t q etaLow etaHigh : ℝ}
    (hshape : assumption_positive_prior_shape alpha beta)
    (ht : assumption_positive_time t)
    (hetaLow_nonneg : assumption_prior_strength_nonnegative etaLow)
    (heta_le : assumption_prior_strength_weak_order etaLow etaHigh) :
    paper_squared_bias alpha beta etaLow t q ≤
      paper_squared_bias alpha beta etaHigh t q := by
  simpa [paper_squared_bias, paper_bias, paper_posterior_mean,
    EconCSLib.Statistics.priorWeightedSquaredBias,
    EconCSLib.Statistics.priorWeightedBias,
    EconCSLib.Statistics.priorWeightedPosteriorMean] using
    paper_theorem3_1_squared_bias_nondecreasing
      hshape ht hetaLow_nonneg heta_le

/-! ## 3) Theorem 3.2 statements -/

/--
Theorem 3.2, squared-bias Jensen convexity in true quality.
The squared bias is Jensen-convex as a function of quality.
Source status: direct paper statement
-/
theorem paper_facing_theorem3_2_squared_bias_convex_in_quality
    {alpha beta eta t : ℝ}
    (hshape : assumption_positive_prior_shape alpha beta)
    (heta_nonneg : assumption_prior_strength_nonnegative eta)
    (ht : assumption_positive_time t) :
    EconCSLib.Statistics.JensenConvex
      (fun q => paper_squared_bias alpha beta eta t q) := by
  have hden_pos : 0 < eta * alpha + eta * beta + t := by
    calc
      0 < eta * (alpha + beta) + t :=
        add_pos_of_nonneg_of_pos
          (mul_nonneg heta_nonneg hshape.le) ht
      _ = eta * alpha + eta * beta + t := by ring
  simpa [paper_squared_bias, paper_bias, paper_posterior_mean,
    EconCSLib.Statistics.priorWeightedSquaredBias,
    EconCSLib.Statistics.priorWeightedBias,
    EconCSLib.Statistics.priorWeightedPosteriorMean] using
    paper_theorem3_2_squared_bias_convex_in_quality (ne_of_gt hden_pos)

/--
Theorem 3.2, squared-bias global minimizer.
On the full quality interval, squared bias is minimized at the prior mean
`alpha / (alpha + beta)` under positive shape mass and positive sample weight.
Source status: direct paper statement
-/
theorem paper_facing_theorem3_2_squared_bias_global_min_at_prior_mean
    {alpha beta eta t : ℝ}
    (hshape : assumption_positive_prior_shape alpha beta)
    (heta_nonneg : assumption_prior_strength_nonnegative eta)
    (ht : assumption_positive_time t) :
    EconCSLib.Statistics.GlobalMinAt
      (fun q => paper_squared_bias alpha beta eta t q)
      (alpha / (alpha + beta)) := by
  simpa [paper_squared_bias, paper_bias, paper_posterior_mean,
    EconCSLib.Statistics.priorWeightedSquaredBias,
    EconCSLib.Statistics.priorWeightedBias,
    EconCSLib.Statistics.priorWeightedPosteriorMean] using
    paper_theorem3_2_squared_bias_global_min_at_prior_mean
      hshape heta_nonneg ht

/--
Theorem 3.2, posterior-mean variance Jensen concavity in true quality.
This holds when the prior-weighted sample mass is nonnegative (`t ≥ 0`).
Source status: direct paper statement
-/
theorem paper_facing_theorem3_2_variance_concave_in_quality
    {alpha beta eta t : ℝ}
    (ht : assumption_nonnegative_time t) :
    EconCSLib.Statistics.JensenConcave
      (fun q => paper_variance alpha beta eta t q) := by
  simpa [paper_variance, EconCSLib.Statistics.priorWeightedVariance] using
    paper_theorem3_2_variance_concave_in_quality
      (alpha := alpha) (beta := beta) (eta := eta) ht

/--
Theorem 3.2, posterior-mean variance global maximum at `q = 1/2`.
For nonnegative prior-weighted sample mass, variance is globally maximized at
`q_v = 1/2`.
Source status: direct paper statement
-/
theorem paper_facing_theorem3_2_variance_global_max_at_half
    {alpha beta eta t : ℝ}
    (ht : assumption_nonnegative_time t) :
    EconCSLib.Statistics.GlobalMaxAt
      (fun q => paper_variance alpha beta eta t q)
      (1 / 2) := by
  simpa [paper_variance, EconCSLib.Statistics.priorWeightedVariance] using
    paper_theorem3_2_variance_global_max_at_half
      (alpha := alpha) (beta := beta) (eta := eta) ht

/-! ## 4) Formalized source-correction evidence -/

/--
Formalized source correction for Theorem 3.1 strict decrease:
at `q_v = 0`, posterior-mean variance is identically zero for any prior strength,
so strict decrease cannot hold unconditionally.
Source status: proof evidence for a formalized source note
Source note: This is not a separate source theorem. It proves why the printed
closed-interval strict claim needs the corrected interior domain.
-/
theorem paper_facing_theorem3_1_variance_strict_decrease_counterexample_quality_zero
    (alpha beta t etaLow etaHigh : ℝ) :
    ¬ paper_variance alpha beta etaHigh t 0 <
      paper_variance alpha beta etaLow t 0 := by
  simpa [paper_variance, EconCSLib.Statistics.priorWeightedVariance] using
    paper_theorem3_1_variance_strict_decrease_counterexample_quality_zero
      alpha beta t etaLow etaHigh

/--
Formalized source correction for Theorem 3.1 strict decrease:
at `q_v = 1`, posterior-mean variance is identically zero for any prior strength,
so strict decrease cannot hold unconditionally.
Source status: proof evidence for a formalized source note
Source note: This is not a separate source theorem. It proves why the printed
closed-interval strict claim needs the corrected interior domain.
-/
theorem paper_facing_theorem3_1_variance_strict_decrease_counterexample_quality_one
    (alpha beta t etaLow etaHigh : ℝ) :
    ¬ paper_variance alpha beta etaHigh t 1 <
      paper_variance alpha beta etaLow t 1 := by
  simpa [paper_variance, EconCSLib.Statistics.priorWeightedVariance] using
    paper_theorem3_1_variance_strict_decrease_counterexample_quality_one
      alpha beta t etaLow etaHigh

/-! ## 5) Section 4 & Appendix C: Responsive Market and Dynamic Model -/

/-- Section 2.3: a product's selection rate is its number of selections divided
by its lifespan.
Source status: direct paper definition
-/
noncomputable def paper_facing_selection_rate
    (selections lifespan : ℝ) : ℝ :=
  selections / lifespan

/-- Section 2.3: Individual Producer Unfairness.
Defined as the standard deviation in Selection Rate (SR) among producers with
the same true quality `q`. The source denotes this statistic by `σ̂(U)` without
specifying a divisor; this row uses the empirical-distribution convention
`sqrt((1 / |U|) * sum (x - mean U)^2)` and returns zero for an empty class.
Source status: direct paper definition with an explicit denominator convention
-/
noncomputable def paper_facing_individual_producer_unfairness
    {V : Type*} [Fintype V] [DecidableEq V]
    (selections : V → ℝ)
    (lifespan : V → ℝ)
    (q_v : V → ℝ)
    (q : ℝ) : ℝ :=
  let S := Finset.univ.filter (fun v => q_v v = q)
  let selectionRate := fun v =>
    paper_facing_selection_rate (selections v) (lifespan v)
  let meanSelectionRate :=
    if S.card = 0 then 0
    else (∑ v ∈ S, selectionRate v) / (S.card : ℝ)
  if S.card = 0 then 0
  else
    Real.sqrt
      ((∑ v ∈ S, (selectionRate v - meanSelectionRate) ^ 2) /
      (S.card : ℝ))

/-- Section 2.3: marketplace-level producer unfairness averages the
quality-conditional unfairness metric over the quality distribution.
Source status: direct paper definition
-/
noncomputable def paper_facing_marketplace_producer_unfairness
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (quality_dist : PMF Q) (quality_unfairness : Q → ℝ) : ℝ :=
  ∑ q : Q, (quality_dist q).toReal * quality_unfairness q

/-- Section 4: Thompson Sampling on the currently available product set.
The supplied `belief` is the joint posterior law of the one-per-product quality
draws (the source instantiates its marginals as the current Beta posteriors).
The policy samples one profile and selects an argmax, with a fixed tie breaker.
Source status: direct mathematical policy definition; the calibrated simulator
and continuous-Beta implementation are empirical implementation scope
-/
theorem paper_facing_thompson_sampling_mechanism
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (belief : PMF (V → ℝ)) :
  ∃ tie_breaker : (V → ℝ) → V,
    (∀ (profile : V → ℝ) (v : V), profile v ≤ profile (tie_breaker profile)) ∧
    ∃ policy : PMF V,
      policy = belief.bind (fun profile => PMF.pure (tie_breaker profile)) := by
  classical
  let tie_breaker : (V → ℝ) → V := fun profile =>
    Classical.choose
      (Finset.exists_max_image (Finset.univ : Finset V) profile
        Finset.univ_nonempty)
  refine ⟨tie_breaker, ?_,
    belief.bind (fun profile => PMF.pure (tie_breaker profile)), rfl⟩
  intro profile v
  exact
    (Classical.choose_spec
      (Finset.exists_max_image (Finset.univ : Finset V) profile
        Finset.univ_nonempty)).2 v (Finset.mem_univ v)

/-- Section 4: Expected Regret (Efficiency).
The total expected regret across a finite time horizon.
Source status: direct paper definition
-/
noncomputable def paper_facing_expected_regret
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (T : ℕ)
    (M : Fin T → Finset V)
    (h_nonempty : ∀ t, (M t).Nonempty)
    (q : V → ℝ)
    (pi : (t : Fin T) → PMF {v // v ∈ M t}) : ℝ :=
  ∑ t : Fin T,
    ((M t).sup' (h_nonempty t) q -
      EconCSLib.pmfExp (pi t) (fun v => q v.1))

/-- Appendix C: MSE Decomposition in the responsive setting.
When the number of reviews $N$ is a random variable, the expected mean squared
error conditional on true quality decomposes into expected squared bias plus
expected variance. `state_dist` is the review-count-state law and `rating_dist s`
is the finite conditional law of the posterior rating in state `s`. The two
moment premises are the fixed-model conditional mean and variance formulas from
Appendix A; the bias--variance expansion and outer expectation step are proved
in Lean rather than supplied as a pointwise decomposition premise.
Source status: direct paper statement (Equations 19--20)
-/
theorem paper_facing_responsive_mse_decomposition
    {α Ω : Type*} [Fintype α] [DecidableEq α]
    [Fintype Ω] [DecidableEq Ω]
    {alpha beta eta q_v : ℝ}
    (state_dist : PMF α)
    (rating_dist : α → PMF Ω)
    (N : α → ℝ)
    (posterior_rating : α → Ω → ℝ)
    (h_cond_mean : ∀ s,
      EconCSLib.pmfExp (rating_dist s) (posterior_rating s) =
      paper_posterior_mean alpha beta eta (N s) q_v)
    (h_cond_var : ∀ s,
      EconCSLib.pmfExp (rating_dist s) (fun ω =>
        (posterior_rating s ω -
          EconCSLib.pmfExp (rating_dist s) (posterior_rating s)) ^ 2) =
      paper_variance alpha beta eta (N s) q_v) :
    EconCSLib.pmfExp state_dist (fun s =>
      EconCSLib.pmfExp (rating_dist s) (fun ω =>
        (posterior_rating s ω - q_v) ^ 2)) =
      EconCSLib.pmfExp state_dist (fun s =>
        paper_squared_bias alpha beta eta (N s) q_v) +
      EconCSLib.pmfExp state_dist (fun s =>
        paper_variance alpha beta eta (N s) q_v) := by
  have h_mean_lib : ∀ s,
      EconCSLib.pmfExp (rating_dist s) (posterior_rating s) =
      EconCSLib.Statistics.priorWeightedPosteriorMean alpha beta eta (N s) q_v := by
    intro s
    simpa [paper_posterior_mean,
      EconCSLib.Statistics.priorWeightedPosteriorMean] using h_cond_mean s
  have h_var_lib : ∀ s,
      EconCSLib.pmfExp (rating_dist s) (fun ω =>
        (posterior_rating s ω -
          EconCSLib.pmfExp (rating_dist s) (posterior_rating s)) ^ 2) =
      EconCSLib.Statistics.priorWeightedVariance alpha beta eta (N s) q_v := by
    intro s
    simpa [paper_variance,
      EconCSLib.Statistics.priorWeightedVariance] using h_cond_var s
  simpa [paper_squared_bias, paper_bias, paper_posterior_mean, paper_variance,
    EconCSLib.Statistics.priorWeightedSquaredBias,
    EconCSLib.Statistics.priorWeightedBias,
    EconCSLib.Statistics.priorWeightedPosteriorMean,
    EconCSLib.Statistics.priorWeightedVariance] using
    MBJG25ProducerFairness.Responsive.paper_responsive_mse_decomposition
      state_dist rating_dist N posterior_rating h_mean_lib h_var_lib

/-! ## 6) Appendix D--F: additional rating formulas and choice rules -/

/-- Appendix D, Equation 20.  For a product with `n > 0` ratings, `k` positive
ratings, population baseline `C`, and pseudo-count strength `m`, the displayed
weighted average simplifies to `(k + m*C)/(n+m)`.  The latter is exactly the
binary posterior-rating formula with corrected baseline Beta shape
`(C, 1-C)` scaled by `m`.

Source status: direct Equation 20 plus a formalized source correction
Source note: the paper prints `Beta(C,1)`, whose mean is `C/(C+1)`; Equation 20
and the surrounding baseline-mean description uniquely require shape
`Beta(C,1-C)` before scaling by `m`.
-/
theorem paper_facing_eq20_bayesian_rating_equivalence
    (n k : ℕ) (m C : ℝ)
    (hn : assumption_positive_rating_count n) :
    let nR := (n : ℝ)
    let kR := (k : ℝ)
    nR / (nR + m) * (kR / nR) + m / (nR + m) * C =
        (kR + m * C) / (nR + m) ∧
      paper_posterior_rating (m * C) (m * (1 - C)) k n =
        (kR + m * C) / (nR + m) := by
  dsimp
  constructor
  · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    by_cases hden : (n : ℝ) + m = 0
    · simp [hden]
    · field_simp [hnR, hden]
  · simp only [paper_posterior_rating]
    congr 1 <;> ring

/-- Appendix E's corrected Dirichlet--categorical posterior expected rating.
For rating values `ratingValue j`, prior pseudo-counts `priorPseudoCount j`,
and observed counts `observedCount j`, the posterior mean includes both prior
and observed mass in the numerator and denominator.

Source status: corrected source formula for Equation 21
Source note: the printed Equation 21 omits `alphaHat` from both sums even though
its notation, the preceding Dirichlet-prior paragraph, and the following
`alphaHat_j = eta * alphaTilde_j` paragraph all specify a prior-weighted
posterior.  The printed expression is exactly the zero-prior special case proved
in the next row.
-/
noncomputable def paper_ordinal_posterior_rating
    {K : Type*} [Fintype K]
    (ratingValue priorPseudoCount observedCount : K → ℝ) : ℝ :=
  (∑ j : K, (priorPseudoCount j + observedCount j) * ratingValue j) /
    (∑ j : K, (priorPseudoCount j + observedCount j))

/-- Formalized comparison evidence for the Equation 21 correction: when every
prior pseudo-count is zero, the corrected posterior formula reduces exactly to
the sample-average expression printed in Equation 21.
Source status: proof evidence for a formalized source note
-/
theorem paper_facing_eq21_zero_prior_comparison
    {K : Type*} [Fintype K]
    (ratingValue observedCount : K → ℝ) :
    paper_ordinal_posterior_rating ratingValue (fun _ => 0) observedCount =
      (∑ j : K, observedCount j * ratingValue j) /
        (∑ j : K, observedCount j) := by
  simp [paper_ordinal_posterior_rating]

/-- Appendix F's `k`-sampling choice rule for one sampled score profile.
For every feasible positive `k`, the theorem constructs a size-`k` set whose
members all weakly outrank its nonmembers, and then constructs the uniform
policy on that set.  Ties at the cutoff are resolved by the maximizing-set
choice made inside the proof; the top-`k` property is a proved conclusion, not
a caller-supplied premise.
Source status: direct source algorithm definition
-/
theorem paper_facing_k_sampling_mechanism
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (profile : V → ℝ)
    (k : ℕ)
    (hk : 0 < k)
    (hbound : k ≤ Fintype.card V) :
    ∃ top : Finset V,
      top.card = k ∧
      (∀ v ∈ top, ∀ w ∉ top, profile w ≤ profile v) ∧
      ∃ htop : top.Nonempty, ∃ policy : PMF V,
        policy = PMF.uniformOfFinset top htop := by
  classical
  have hcandidates :
      ((Finset.univ : Finset V).powersetCard k).Nonempty := by
    exact Finset.powersetCard_nonempty.mpr (by simpa using hbound)
  obtain ⟨top, htop_mem, hmax⟩ :=
    Finset.exists_max_image
      ((Finset.univ : Finset V).powersetCard k)
      (fun s => ∑ i ∈ s, profile i) hcandidates
  have hcard : top.card = k :=
    (Finset.mem_powersetCard.mp htop_mem).2
  have htop : top.Nonempty :=
    Finset.card_pos.mp (by simpa [hcard] using hk)
  refine ⟨top, hcard, ?_, htop, PMF.uniformOfFinset top htop, rfl⟩
  intro v hv w hw
  by_contra hnot
  have hlt : profile v < profile w := lt_of_not_ge hnot
  let swapped : Finset V := insert w (top.erase v)
  have hw_erase : w ∉ top.erase v := by
    intro hmem
    exact hw (Finset.mem_of_mem_erase hmem)
  have hswap_card : swapped.card = k := by
    dsimp [swapped]
    rw [Finset.card_insert_of_notMem hw_erase,
      Finset.card_erase_of_mem hv, hcard]
    omega
  have hswap_mem :
      swapped ∈ (Finset.univ : Finset V).powersetCard k :=
    Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hswap_card⟩
  have hswap_sum :
      (∑ i ∈ swapped, profile i) =
        (∑ i ∈ top, profile i) - profile v + profile w := by
    calc
      (∑ i ∈ swapped, profile i) =
          profile w + ∑ i ∈ top.erase v, profile i := by
            simp [swapped, hw_erase]
      _ = (∑ i ∈ top, profile i) - profile v + profile w := by
            rw [← Finset.sum_erase_add top profile hv]
            ring
  have hstrict :
      (∑ i ∈ top, profile i) < ∑ i ∈ swapped, profile i := by
    rw [hswap_sum]
    linarith
  exact (not_lt_of_ge (hmax swapped hswap_mem)) hstrict

/-- Appendix F's `k=1` endpoint: the unique sampled product is an argmax and
the resulting policy is the pure policy on that product, matching the
one-profile choice step of ordinary Thompson sampling.
Source status: direct source comparison claim
-/
theorem paper_facing_k_sampling_one_is_argmax
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (profile : V → ℝ) :
    ∃ top : Finset V, top.card = 1 ∧
      ∃ v : V, top = {v} ∧
        (∀ w : V, profile w ≤ profile v) ∧
        ∃ htop : top.Nonempty,
          PMF.uniformOfFinset top htop = PMF.pure v := by
  obtain ⟨top, hcard, hdominates, htop, _policy, _hpolicy⟩ :=
    paper_facing_k_sampling_mechanism profile 1 (by omega)
      (by simpa using (Fintype.card_pos : 0 < Fintype.card V))
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
  refine ⟨{v}, by simp, v, rfl, ?_, ⟨by simp, ?_⟩⟩
  · intro w
    by_cases hw : w = v
    · simpa [hw]
    · exact hdominates v (by simp) w (by simpa [hw])
  · ext w
    simp [PMF.uniformOfFinset_apply]

/-- Appendix F's `k=n` endpoint: selecting uniformly from the top `n` products
when the market has `n` products is the uniform policy on the whole market.
Source status: direct source comparison claim
-/
theorem paper_facing_k_sampling_market_size_is_uniform
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (profile : V → ℝ) :
    ∃ top : Finset V, top.card = Fintype.card V ∧
      ∃ htop : top.Nonempty,
        PMF.uniformOfFinset top htop = PMF.uniformOfFintype V := by
  obtain ⟨top, hcard, _hdominates, htop, _policy, _hpolicy⟩ :=
    paper_facing_k_sampling_mechanism profile (Fintype.card V)
      Fintype.card_pos le_rfl
  have htop_univ : top = Finset.univ :=
    Finset.eq_univ_of_card top hcard
  subst top
  exact ⟨Finset.univ, by simp, Finset.univ_nonempty,
    by simp [PMF.uniformOfFintype]⟩

end MBJG25ProducerFairness
