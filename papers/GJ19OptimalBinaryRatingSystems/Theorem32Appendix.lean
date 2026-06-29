import GJ19OptimalBinaryRatingSystems.ContinuumTheorems

open scoped BigOperators

namespace GJ19OptimalBinaryRatingSystems

noncomputable section

open EconCSLib.Probability
open Filter Topology
open MeasureTheory

/--
For the Boolean bisection convention used in Algorithm 1, the upper endpoint is
always an endpoint at which the `above` predicate is true, provided this holds
for the initial upper endpoint.
-/
theorem theorem32_realBisectionStep_upper_true_of_upper_true
    (above : ℝ → Bool) {lower upper : ℝ}
    (hupper : above upper = true) :
    above (EconCSLib.Optimization.realBisectionStep above lower upper).2 =
      true := by
  by_cases hmid :
      above (EconCSLib.Optimization.realBisectionMidpoint lower upper) = true
  · simpa [EconCSLib.Optimization.realBisectionStep, hmid]
  · have hmid_false :
        above (EconCSLib.Optimization.realBisectionMidpoint lower upper) =
          false := by
      cases h :
          above (EconCSLib.Optimization.realBisectionMidpoint lower upper) <;>
        simp [h] at hmid ⊢
    simpa [EconCSLib.Optimization.realBisectionStep, hmid_false] using hupper

/--
Finite bisection preserves the invariant that the upper endpoint satisfies the
Boolean `above` predicate.
-/
theorem theorem32_realBisectionRun_upper_true_of_upper_true
    (above : ℝ → Bool) {n : ℕ} {lower upper : ℝ}
    (hupper : above upper = true) :
    above (EconCSLib.Optimization.realBisectionRun above n lower upper).2 =
      true := by
  induction n with
  | zero =>
      simpa [EconCSLib.Optimization.realBisectionRun] using hupper
  | succ n ih =>
      simpa [EconCSLib.Optimization.realBisectionRun,
        EconCSLib.Optimization.realBisectionStepFn,
        Function.iterate_succ_apply'] using
        theorem32_realBisectionStep_upper_true_of_upper_true above ih

/--
Source-shaped outer classifier from Algorithm 1: after `CalculateOtherLevels`
at a tested final-low endpoint, the branch that updates the upper endpoint is
the non-strict comparison `ratelast ≤ ratefirst`.
-/
def theorem32OuterSourceRateAbove {n : ℕ}
    (candidate : Fin (n + 2) → ℝ) : Bool :=
  if
      binaryEndpointAwareAdjacentRate candidate
          (fun _ : Fin (n + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (n + 1)) ≤
        binaryEndpointAwareAdjacentRate candidate
          (fun _ : Fin (n + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin (n + 1))
    then true else false

/-- True branch of the source-shaped outer classifier. -/
theorem theorem32OuterSourceRateAbove_eq_true_iff {n : ℕ}
    (candidate : Fin (n + 2) → ℝ) :
    theorem32OuterSourceRateAbove candidate = true ↔
      binaryEndpointAwareAdjacentRate candidate
          (fun _ : Fin (n + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (n + 1)) ≤
        binaryEndpointAwareAdjacentRate candidate
          (fun _ : Fin (n + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin (n + 1)) := by
  unfold theorem32OuterSourceRateAbove
  by_cases h :
      binaryEndpointAwareAdjacentRate candidate
          (fun _ : Fin (n + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (n + 1)) ≤
        binaryEndpointAwareAdjacentRate candidate
          (fun _ : Fin (n + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin (n + 1))
  · simp
  · simp

/-- False branch of the source-shaped outer classifier, matching the paper's `ratefirst < ratelast` case. -/
theorem theorem32OuterSourceRateAbove_eq_false_iff {n : ℕ}
    (candidate : Fin (n + 2) → ℝ) :
    theorem32OuterSourceRateAbove candidate = false ↔
      binaryEndpointAwareAdjacentRate candidate
          (fun _ : Fin (n + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin (n + 1)) <
        binaryEndpointAwareAdjacentRate candidate
          (fun _ : Fin (n + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (n + 1)) := by
  unfold theorem32OuterSourceRateAbove
  by_cases h :
      binaryEndpointAwareAdjacentRate candidate
          (fun _ : Fin (n + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (n + 1)) ≤
        binaryEndpointAwareAdjacentRate candidate
          (fun _ : Fin (n + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin (n + 1))
  · simp
  · have hlt :
        binaryEndpointAwareAdjacentRate candidate
            (fun _ : Fin (n + 2) => (1 : ℝ))
            (firstAdjacentIndex : Fin (n + 1)) <
          binaryEndpointAwareAdjacentRate candidate
            (fun _ : Fin (n + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin (n + 1)) :=
      lt_of_not_ge h
    simp

/--
Soundness of the source-shaped outer classifier's upper-endpoint branch.  This
is the exact hypothesis needed to feed Algorithm 1's `else u = j` branch into
the reusable bisection-bracket API.
-/
theorem theorem32OuterSourceRateAbove_true_sound
    {n : ℕ} {levelTarget : ℝ}
    (candidate : ℝ → Fin (n + 2) → ℝ)
    (hsource :
      ∀ x,
        binaryEndpointAwareAdjacentRate (candidate x)
            (fun _ : Fin (n + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin (n + 1)) ≤
          binaryEndpointAwareAdjacentRate (candidate x)
            (fun _ : Fin (n + 2) => (1 : ℝ))
            (firstAdjacentIndex : Fin (n + 1)) →
        levelTarget ≤ x) :
    ∀ x,
      theorem32OuterSourceRateAbove (candidate x) = true →
        levelTarget ≤ x := by
  intro x hx
  exact hsource x ((theorem32OuterSourceRateAbove_eq_true_iff (candidate x)).mp hx)

/--
Soundness of the source-shaped outer classifier's lower-endpoint branch.  This
packages the paper's `if ratefirst < ratelast then ℓ = j` branch for reuse by
the bisection-bracket API.
-/
theorem theorem32OuterSourceRateAbove_false_sound
    {n : ℕ} {levelTarget : ℝ}
    (candidate : ℝ → Fin (n + 2) → ℝ)
    (hsource :
      ∀ x,
        binaryEndpointAwareAdjacentRate (candidate x)
            (fun _ : Fin (n + 2) => (1 : ℝ))
            (firstAdjacentIndex : Fin (n + 1)) <
          binaryEndpointAwareAdjacentRate (candidate x)
            (fun _ : Fin (n + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin (n + 1)) →
        x ≤ levelTarget) :
    ∀ x,
      theorem32OuterSourceRateAbove (candidate x) = false →
        x ≤ levelTarget := by
  intro x hx
  exact hsource x ((theorem32OuterSourceRateAbove_eq_false_iff (candidate x)).mp hx)

/--
Weighted source-shaped outer classifier from Algorithm 1.  The uniform
classifier above is the specialization used by the existing doubled-grid
endpoint; this version is the source-facing branch predicate for monotone
sample rates.
-/
def theorem32OuterSourceWeightedRateAbove {n : ℕ}
    (candidate sampleRate : Fin (n + 2) → ℝ) : Bool :=
  if
      binaryEndpointAwareAdjacentRate candidate sampleRate
          (lastAdjacentIndex : Fin (n + 1)) ≤
        binaryEndpointAwareAdjacentRate candidate sampleRate
          (firstAdjacentIndex : Fin (n + 1))
    then true else false

/-- True branch of the weighted source-shaped outer classifier. -/
theorem theorem32OuterSourceWeightedRateAbove_eq_true_iff {n : ℕ}
    (candidate sampleRate : Fin (n + 2) → ℝ) :
    theorem32OuterSourceWeightedRateAbove candidate sampleRate = true ↔
      binaryEndpointAwareAdjacentRate candidate sampleRate
          (lastAdjacentIndex : Fin (n + 1)) ≤
        binaryEndpointAwareAdjacentRate candidate sampleRate
          (firstAdjacentIndex : Fin (n + 1)) := by
  unfold theorem32OuterSourceWeightedRateAbove
  by_cases h :
      binaryEndpointAwareAdjacentRate candidate sampleRate
          (lastAdjacentIndex : Fin (n + 1)) ≤
        binaryEndpointAwareAdjacentRate candidate sampleRate
          (firstAdjacentIndex : Fin (n + 1))
  · simp
  · simp

/-- False branch of the weighted source-shaped outer classifier. -/
theorem theorem32OuterSourceWeightedRateAbove_eq_false_iff {n : ℕ}
    (candidate sampleRate : Fin (n + 2) → ℝ) :
    theorem32OuterSourceWeightedRateAbove candidate sampleRate = false ↔
      binaryEndpointAwareAdjacentRate candidate sampleRate
          (firstAdjacentIndex : Fin (n + 1)) <
        binaryEndpointAwareAdjacentRate candidate sampleRate
          (lastAdjacentIndex : Fin (n + 1)) := by
  unfold theorem32OuterSourceWeightedRateAbove
  by_cases h :
      binaryEndpointAwareAdjacentRate candidate sampleRate
          (lastAdjacentIndex : Fin (n + 1)) ≤
        binaryEndpointAwareAdjacentRate candidate sampleRate
          (firstAdjacentIndex : Fin (n + 1))
  · simp
  · have hlt :
        binaryEndpointAwareAdjacentRate candidate sampleRate
            (firstAdjacentIndex : Fin (n + 1)) <
          binaryEndpointAwareAdjacentRate candidate sampleRate
            (lastAdjacentIndex : Fin (n + 1)) :=
      lt_of_not_ge h
    simp

/--
Soundness of the weighted source-shaped outer classifier's upper-endpoint
branch for the reusable bisection API.
-/
theorem theorem32OuterSourceWeightedRateAbove_true_sound
    {n : ℕ} {levelTarget : ℝ}
    (sampleRate : Fin (n + 2) → ℝ)
    (candidate : ℝ → Fin (n + 2) → ℝ)
    (hsource :
      ∀ x,
        binaryEndpointAwareAdjacentRate (candidate x) sampleRate
            (lastAdjacentIndex : Fin (n + 1)) ≤
          binaryEndpointAwareAdjacentRate (candidate x) sampleRate
            (firstAdjacentIndex : Fin (n + 1)) →
        levelTarget ≤ x) :
    ∀ x,
      theorem32OuterSourceWeightedRateAbove (candidate x) sampleRate = true →
        levelTarget ≤ x := by
  intro x hx
  exact
    hsource x
      ((theorem32OuterSourceWeightedRateAbove_eq_true_iff
        (candidate x) sampleRate).mp hx)

/--
Soundness of the weighted source-shaped outer classifier's lower-endpoint
branch for the reusable bisection API.
-/
theorem theorem32OuterSourceWeightedRateAbove_false_sound
    {n : ℕ} {levelTarget : ℝ}
    (sampleRate : Fin (n + 2) → ℝ)
    (candidate : ℝ → Fin (n + 2) → ℝ)
    (hsource :
      ∀ x,
        binaryEndpointAwareAdjacentRate (candidate x) sampleRate
            (firstAdjacentIndex : Fin (n + 1)) <
          binaryEndpointAwareAdjacentRate (candidate x) sampleRate
            (lastAdjacentIndex : Fin (n + 1)) →
        x ≤ levelTarget) :
    ∀ x,
      theorem32OuterSourceWeightedRateAbove (candidate x) sampleRate = false →
        x ≤ levelTarget := by
  intro x hx
  exact
    hsource x
      ((theorem32OuterSourceWeightedRateAbove_eq_false_iff
        (candidate x) sampleRate).mp hx)

/--
Algorithm 1's inner bisection can be viewed either as a direct rate comparison
or as threshold bisection on the Bernoulli low-endpoint inverse.  The two tests
have the same true branch on the feasible bracket.
-/
theorem theorem32_inner_weighted_rate_le_target_iff_threshold_classifier_true
    {gHi gLo floor pHi target x : ℝ}
    (hfeasible :
      WeightedBernoulliLowEndpointTargetFeasible
        gHi gLo floor pHi target)
    (hfloor_le_x : floor ≤ x)
    (hx_le_hi : x ≤ pHi) :
    EconCSLib.Optimization.realBisectionAboveTarget
        (weightedBernoulliLowEndpointOfRateOrFloor
          gHi gLo floor pHi target) x = true ↔
      weightedBernoulliClosedThresholdRate
        gHi gLo pHi x ≤ target := by
  rw [EconCSLib.Optimization.realBisectionAboveTarget_eq_true_iff]
  exact
    weightedBernoulliLowEndpointOfRateOrFloor_le_iff_rate_le_target_of_feasible
      hfeasible hfloor_le_x hx_le_hi

/--
The false branch of the weighted inner source test: a midpoint below the
inverse root is exactly a midpoint whose weighted Bernoulli rate is still
strictly above the target.
-/
theorem theorem32_inner_weighted_target_lt_rate_iff_threshold_classifier_false
    {gHi gLo floor pHi target x : ℝ}
    (hfeasible :
      WeightedBernoulliLowEndpointTargetFeasible
        gHi gLo floor pHi target)
    (hfloor_le_x : floor ≤ x)
    (hx_le_hi : x ≤ pHi) :
    EconCSLib.Optimization.realBisectionAboveTarget
        (weightedBernoulliLowEndpointOfRateOrFloor
          gHi gLo floor pHi target) x = false ↔
      target <
        weightedBernoulliClosedThresholdRate
          gHi gLo pHi x := by
  rw [EconCSLib.Optimization.realBisectionAboveTarget_eq_false_iff]
  have hiff :
      weightedBernoulliLowEndpointOfRateOrFloor
          gHi gLo floor pHi target ≤ x ↔
        weightedBernoulliClosedThresholdRate
          gHi gLo pHi x ≤ target :=
    weightedBernoulliLowEndpointOfRateOrFloor_le_iff_rate_le_target_of_feasible
      hfeasible hfloor_le_x hx_le_hi
  constructor
  · intro hx_lt_root
    exact
      lt_of_not_ge
        (by
          intro hrate_le
          exact not_lt_of_ge (hiff.mpr hrate_le) hx_lt_root)
  · intro htarget_lt_rate
    have hnot_rate_le : ¬
        weightedBernoulliClosedThresholdRate gHi gLo pHi x ≤ target :=
      not_le_of_gt htarget_lt_rate
    exact lt_of_not_ge (fun hroot_le_x => hnot_rate_le (hiff.mp hroot_le_x))

theorem theorem32_inner_rate_le_target_iff_threshold_classifier_true
    {floor pHi target x : ℝ}
    (hfeasible :
      WeightedBernoulliLowEndpointTargetFeasible
        (1 : ℝ) (1 : ℝ) floor pHi target)
    (hfloor_le_x : floor ≤ x)
    (hx_le_hi : x ≤ pHi) :
    EconCSLib.Optimization.realBisectionAboveTarget
        (weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) floor pHi target) x = true ↔
      weightedBernoulliClosedThresholdRate
        (1 : ℝ) (1 : ℝ) pHi x ≤ target := by
  rw [EconCSLib.Optimization.realBisectionAboveTarget_eq_true_iff]
  exact
    weightedBernoulliLowEndpointOfRateOrFloor_le_iff_rate_le_target_of_feasible
      hfeasible hfloor_le_x hx_le_hi

/--
The false branch of the same source test: a midpoint below the inverse root is
exactly a midpoint whose rate is still strictly above the target.
-/
theorem theorem32_inner_target_lt_rate_iff_threshold_classifier_false
    {floor pHi target x : ℝ}
    (hfeasible :
      WeightedBernoulliLowEndpointTargetFeasible
        (1 : ℝ) (1 : ℝ) floor pHi target)
    (hfloor_le_x : floor ≤ x)
    (hx_le_hi : x ≤ pHi) :
    EconCSLib.Optimization.realBisectionAboveTarget
        (weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) floor pHi target) x = false ↔
      target <
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ) pHi x := by
  rw [EconCSLib.Optimization.realBisectionAboveTarget_eq_false_iff]
  have hiff :
      weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) floor pHi target ≤ x ↔
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ) pHi x ≤ target :=
    weightedBernoulliLowEndpointOfRateOrFloor_le_iff_rate_le_target_of_feasible
      hfeasible hfloor_le_x hx_le_hi
  constructor
  · intro hx_lt_root
    exact
      lt_of_not_ge
        (by
          intro hrate_le
          exact not_lt_of_ge (hiff.mpr hrate_le) hx_lt_root)
  · intro htarget_lt_rate
    exact
      lt_of_not_ge
        (by
          intro hroot_le_x
          exact not_lt_of_ge (hiff.mp hroot_le_x) htarget_lt_rate)

/--
Theorem 3.2 floor-rate reduction from a nested-interval domination invariant.
If each returned high endpoint lies above the corresponding exact comparison
high endpoint, and the fixed floor lies below the exact comparison low
endpoint, then the source floor-rate condition follows from the exact
comparison rate by monotonicity of the Bernoulli closed threshold rate.
-/
theorem theorem32_target_lt_floor_rate_of_nested_comparison_intervals
    {n : ℕ}
    (comparison returned : Fin (n + 2) → ℝ)
    {floor target : ℝ}
    (hcomparisonLevels : BinaryEndpointLevelVector comparison)
    (hfloor_pos : 0 < floor)
    (hfloor_le_comparison_low :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        floor ≤ comparison (adjacentLowIndex i))
    (hcomparison_high_le_returned_high :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        comparison (adjacentHighIndex i) ≤ returned (adjacentHighIndex i))
    (hreturned_high_lt_one :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        returned (adjacentHighIndex i) < 1)
    (htarget_lt_comparison_rate :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (comparison (adjacentHighIndex i))
            (comparison (adjacentLowIndex i))) :
    ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
      target <
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (returned (adjacentHighIndex i)) floor := by
  intro i hi_first hi_last
  exact
    lt_weightedBernoulliClosedThresholdRate_of_lt_of_shrink
      (gHi := (1 : ℝ)) (gLo := (1 : ℝ))
      (pHi := returned (adjacentHighIndex i))
      (pLo := floor)
      (pHi' := comparison (adjacentHighIndex i))
      (pLo' := comparison (adjacentLowIndex i))
      (target := target)
      (by norm_num) (by norm_num) (by norm_num)
      hfloor_pos
      (hfloor_le_comparison_low i hi_first hi_last)
      (hcomparisonLevels.2.2 i).le
      (hcomparison_high_le_returned_high i hi_first hi_last)
      (hreturned_high_lt_one i hi_first hi_last)
      (htarget_lt_comparison_rate i hi_first hi_last)

/--
Non-strict version of `theorem32_target_lt_floor_rate_of_nested_comparison_intervals`.
This is the boundary case needed when the outer bisection lands exactly on the
refined penultimate endpoint: shrinking can turn strict source inequalities
into equalities, but the clipped low-endpoint selector only needs `≤`.
-/
theorem theorem32_target_le_floor_rate_of_nested_comparison_intervals
    {n : ℕ}
    (comparison returned : Fin (n + 2) → ℝ)
    {floor target : ℝ}
    (hcomparisonLevels : BinaryEndpointLevelVector comparison)
    (hfloor_pos : 0 < floor)
    (hfloor_le_comparison_low :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        floor ≤ comparison (adjacentLowIndex i))
    (hcomparison_high_le_returned_high :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        comparison (adjacentHighIndex i) ≤ returned (adjacentHighIndex i))
    (hreturned_high_lt_one :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        returned (adjacentHighIndex i) < 1)
    (htarget_le_comparison_rate :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        target ≤
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (comparison (adjacentHighIndex i))
            (comparison (adjacentLowIndex i))) :
    ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
      target ≤
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (returned (adjacentHighIndex i)) floor := by
  intro i hi_first hi_last
  exact
    (htarget_le_comparison_rate i hi_first hi_last).trans
      (weightedBernoulliClosedThresholdRate_le_of_shrink
        (gHi := (1 : ℝ)) (gLo := (1 : ℝ))
        (pHi := returned (adjacentHighIndex i))
        (pLo := floor)
        (pHi' := comparison (adjacentHighIndex i))
        (pLo' := comparison (adjacentLowIndex i))
        (by norm_num) (by norm_num) (by norm_num)
        hfloor_pos
        (hfloor_le_comparison_low i hi_first hi_last)
        (hcomparisonLevels.2.2 i).le
        (hcomparison_high_le_returned_high i hi_first hi_last)
        (hreturned_high_lt_one i hi_first hi_last))

/--
For the exact Lemma C.5 doubled chain, a strict outer return above the exact
last lower endpoint makes the target `-log lastLow` strictly smaller than each
interior exact adjacent comparison rate.  This packages the source
Theorem 3.2 fact that the outer bisection has not collapsed to the exact last
target.
-/
theorem theorem32_target_lt_comparison_rate_of_uniform_doubled_lastLow_strict
    {m : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {lastLow : ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlevelTarget_lt_lastLow :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) < lastLow) :
    let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
      uniformDoubledEndpointLevels oldLevels
    let target : ℝ := -Real.log lastLow
    ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
      target <
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (comparison (adjacentHighIndex i))
          (comparison (adjacentLowIndex i)) := by
  let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let target : ℝ := -Real.log lastLow
  let lastAdj : Fin ((2 * m + 1) + 1) := lastAdjacentIndex
  let lastLowIndex : Fin ((2 * m + 1) + 2) := adjacentLowIndex lastAdj
  have hcomparisonLevels : BinaryEndpointLevelVector comparison := by
    simpa [comparison] using
      uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hcomparisonEq :
      BinaryEndpointAwareAdjacentRatesEqualize comparison
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    simpa [comparison] using
      uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have hlastLow_pos : 0 < comparison lastLowIndex := by
    exact
      BinaryEndpointLevelVector_pos_of_not_first hcomparisonLevels
        lastLowIndex
        (by
          simp [lastLowIndex, lastAdj])
  have hlog_lt :
      Real.log (comparison lastLowIndex) < Real.log lastLow := by
    exact
      Real.log_lt_log hlastLow_pos
        (by
          simpa [comparison, lastLowIndex, lastAdj] using
            hlevelTarget_lt_lastLow)
  have htarget_lt_last_rate :
      target < -Real.log (comparison lastLowIndex) := by
    dsimp [target]
    linarith
  dsimp
  intro i hi_first hi_last
  have hlast_branch :
      binaryEndpointAwareAdjacentRate comparison
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) lastAdj =
        -Real.log (comparison lastLowIndex) := by
    have hbranch :=
      binaryEndpointAwareAdjacentRate_last comparison
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) lastAdj
        (by
          simp [lastAdj])
        (by simp [lastAdj])
    simpa [lastLowIndex, lastAdj] using hbranch
  have hinterior :
      binaryEndpointAwareAdjacentRate comparison
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i =
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (comparison (adjacentHighIndex i))
          (comparison (adjacentLowIndex i)) := by
    simpa using
      binaryEndpointAwareAdjacentRate_interior comparison
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i hi_first hi_last
  calc
    target < -Real.log (comparison lastLowIndex) := htarget_lt_last_rate
    _ = binaryEndpointAwareAdjacentRate comparison
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) lastAdj := hlast_branch.symm
    _ = binaryEndpointAwareAdjacentRate comparison
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i :=
          (hcomparisonEq i lastAdj).symm
    _ = weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (comparison (adjacentHighIndex i))
          (comparison (adjacentLowIndex i)) := hinterior

/--
Non-strict target-rate comparison for the exact Lemma C.5 doubled chain.  If
the outer return is at or above the exact last lower endpoint, the target
`-log lastLow` is at most every interior exact adjacent comparison rate.
-/
theorem theorem32_target_le_comparison_rate_of_uniform_doubled_lastLow_ge
    {m : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {lastLow : ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlevelTarget_le_lastLow :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ lastLow) :
    let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
      uniformDoubledEndpointLevels oldLevels
    let target : ℝ := -Real.log lastLow
    ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
      target ≤
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (comparison (adjacentHighIndex i))
          (comparison (adjacentLowIndex i)) := by
  let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let target : ℝ := -Real.log lastLow
  let lastAdj : Fin ((2 * m + 1) + 1) := lastAdjacentIndex
  let lastLowIndex : Fin ((2 * m + 1) + 2) := adjacentLowIndex lastAdj
  have hcomparisonLevels : BinaryEndpointLevelVector comparison := by
    simpa [comparison] using
      uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hcomparisonEq :
      BinaryEndpointAwareAdjacentRatesEqualize comparison
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    simpa [comparison] using
      uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have hlastLowIndex_pos : 0 < comparison lastLowIndex := by
    exact
      BinaryEndpointLevelVector_pos_of_not_first hcomparisonLevels
        lastLowIndex
        (by
          simp [lastLowIndex, lastAdj])
  have hlastLow_pos : 0 < lastLow :=
    hlastLowIndex_pos.trans_le
      (by
        simpa [comparison, lastLowIndex, lastAdj] using
          hlevelTarget_le_lastLow)
  have hlog_le :
      Real.log (comparison lastLowIndex) ≤ Real.log lastLow := by
    exact
      Real.log_le_log hlastLowIndex_pos
        (by
          simpa [comparison, lastLowIndex, lastAdj] using
            hlevelTarget_le_lastLow)
  have htarget_le_last_rate :
      target ≤ -Real.log (comparison lastLowIndex) := by
    dsimp [target]
    linarith
  dsimp
  intro i hi_first hi_last
  have hlast_branch :
      binaryEndpointAwareAdjacentRate comparison
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) lastAdj =
        -Real.log (comparison lastLowIndex) := by
    have hbranch :=
      binaryEndpointAwareAdjacentRate_last comparison
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) lastAdj
        (by
          simp [lastAdj])
        (by simp [lastAdj])
    simpa [lastLowIndex, lastAdj] using hbranch
  have hinterior :
      binaryEndpointAwareAdjacentRate comparison
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i =
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (comparison (adjacentHighIndex i))
          (comparison (adjacentLowIndex i)) := by
    simpa using
      binaryEndpointAwareAdjacentRate_interior comparison
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i hi_first hi_last
  calc
    target ≤ -Real.log (comparison lastLowIndex) := htarget_le_last_rate
    _ = binaryEndpointAwareAdjacentRate comparison
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) lastAdj := hlast_branch.symm
    _ = binaryEndpointAwareAdjacentRate comparison
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i :=
          (hcomparisonEq i lastAdj).symm
    _ = weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (comparison (adjacentHighIndex i))
          (comparison (adjacentLowIndex i)) := hinterior

/--
Approximation-certificate core for Theorem 3.2.  If an optimal equalized level
vector has common adjacent rate `rStar`, and a returned level vector has every
adjacent rate at least `rStar - eps`, then its finite worst-adjacent objective
is within additive `eps` of the optimal objective.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_le_of_all_rates_ge
    {m : ℕ}
    (optimal returned sampleRate : Fin (m + 2) → ℝ)
    {rStar eps : ℝ}
    (hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal sampleRate i = rStar)
    (hreturned :
      ∀ i : Fin (m + 1),
        rStar - eps ≤
          binaryEndpointAwareAdjacentRate returned sampleRate i) :
    binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
        binaryEndpointAwareAdjacentRateObjective returned sampleRate ≤
      eps := by
  have hopt_obj :
      binaryEndpointAwareAdjacentRateObjective optimal sampleRate = rStar :=
    binaryEndpointAwareAdjacentRateObjective_eq_common_of_all_eq
      optimal sampleRate rStar hoptimal
  have hret_obj :
      rStar - eps ≤
        binaryEndpointAwareAdjacentRateObjective returned sampleRate := by
    unfold binaryEndpointAwareAdjacentRateObjective
    exact EconCSLib.le_finiteMin
      (binaryEndpointAwareAdjacentRate returned sampleRate)
      hreturned
  linarith

/--
Theorem 3.2 rate-loss decomposition.  If the returned last adjacent rate is
within `epsLast` of the optimal equalized rate, and every returned adjacent
rate is within `epsGrid` below that last rate, then the returned finite
worst-adjacent objective is within any `eps ≥ epsLast + epsGrid` of optimum.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_le_of_last_rate_and_grid
    {m : ℕ}
    (optimal returned sampleRate : Fin (m + 2) → ℝ)
    {rStar epsLast epsGrid eps : ℝ}
    (hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal sampleRate i = rStar)
    (hlast :
      rStar - epsLast ≤
        binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1)) - epsGrid ≤
          binaryEndpointAwareAdjacentRate returned sampleRate i)
    (heps : epsLast + epsGrid ≤ eps) :
    binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
        binaryEndpointAwareAdjacentRateObjective returned sampleRate ≤
      eps := by
  have hreturned :
      ∀ i : Fin (m + 1),
        rStar - eps ≤
          binaryEndpointAwareAdjacentRate returned sampleRate i := by
    intro i
    have hi := hgrid i
    have hsum :
        rStar - (epsLast + epsGrid) ≤
          binaryEndpointAwareAdjacentRate returned sampleRate i := by
      linarith
    have hmono : rStar - eps ≤ rStar - (epsLast + epsGrid) := by
      linarith
    exact hmono.trans hsum
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_le_of_all_rates_ge
      optimal returned sampleRate hoptimal hreturned

/--
Theorem 3.2 outer-bracket bridge for the last adjacent rate.  If the returned
last low endpoint is the upper endpoint of a bisection bracket around the
optimal last low endpoint, then the source's logarithmic last-level loss
certificate follows.  This is the checked algebra behind the source invariant
`u <= t*_{M-2} + delta`.
-/
theorem binaryEndpointAwareAdjacentRate_uniform_last_ge_of_bisection_bracket
    {m : ℕ} (hm : 0 < m)
    (optimal returned : Fin (m + 2) → ℝ)
    {lower delta : ℝ}
    (hoptimalLevels : BinaryEndpointLevelVector optimal)
    (B :
      EconCSLib.Optimization.RealBisectionBracket
        (optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
        lower
        (returned (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
        delta) :
    binaryEndpointAwareAdjacentRate optimal
        (fun _ : Fin (m + 2) => (1 : ℝ))
        (lastAdjacentIndex : Fin (m + 1)) -
        Real.log
          ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                delta) /
            optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
      binaryEndpointAwareAdjacentRate returned
        (fun _ : Fin (m + 2) => (1 : ℝ))
        (lastAdjacentIndex : Fin (m + 1)) := by
  let last : Fin (m + 1) := lastAdjacentIndex
  let low : Fin (m + 2) := adjacentLowIndex last
  let target : ℝ := optimal low
  let upper : ℝ := returned low
  let uniform : Fin (m + 2) → ℝ := fun _ => (1 : ℝ)
  have hlast_val : last.val = m := by
    simp [last]
  have hfirst_val : last.val ≠ 0 := by
    omega
  have htarget_pos : 0 < target := by
    simpa [target, low, last] using
      BinaryEndpointLevelVector_last_low_pos
        (m := m) hm hoptimalLevels
  have hupper_pos : 0 < upper := by
    exact lt_of_lt_of_le htarget_pos B.target_le_upper
  have hupper_le : upper ≤ target + delta := by
    simpa [target, upper, low, last] using B.upper_le_target_add_delta
  have htarget_delta_pos : 0 < target + delta :=
    lt_of_lt_of_le hupper_pos hupper_le
  have hlog_le : Real.log upper ≤ Real.log (target + delta) :=
    Real.log_le_log hupper_pos hupper_le
  have hneglog_le : -Real.log (target + delta) ≤ -Real.log upper := by
    linarith
  have hopt_last :
      binaryEndpointAwareAdjacentRate optimal uniform last =
        -Real.log target := by
    have hbranch :=
      binaryEndpointAwareAdjacentRate_last optimal uniform last
        hfirst_val hlast_val
    simpa [target, low, uniform] using hbranch
  have hreturned_last :
      binaryEndpointAwareAdjacentRate returned uniform last =
        -Real.log upper := by
    have hbranch :=
      binaryEndpointAwareAdjacentRate_last returned uniform last
        hfirst_val hlast_val
    simpa [upper, low, uniform] using hbranch
  have hleft :
      binaryEndpointAwareAdjacentRate optimal uniform last -
          Real.log ((target + delta) / target) =
        -Real.log (target + delta) := by
    have hlog_div :
        Real.log ((target + delta) / target) =
          Real.log (target + delta) - Real.log target := by
      rw [Real.log_div (ne_of_gt htarget_delta_pos) (ne_of_gt htarget_pos)]
    rw [hopt_last, hlog_div]
    ring
  calc
    binaryEndpointAwareAdjacentRate optimal
        (fun _ : Fin (m + 2) => (1 : ℝ))
        (lastAdjacentIndex : Fin (m + 1)) -
        Real.log
          ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                delta) /
            optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
        = -Real.log (target + delta) := by
          simpa [last, low, target, uniform] using hleft
    _ ≤ -Real.log upper := hneglog_le
    _ = binaryEndpointAwareAdjacentRate returned
        (fun _ : Fin (m + 2) => (1 : ℝ))
        (lastAdjacentIndex : Fin (m + 1)) := by
          simpa [last, low, upper, uniform] using hreturned_last.symm

/--
Nonuniform last-rate bridge for Theorem 3.2.  If the returned last low
endpoint is the upper endpoint of a bisection bracket around the optimal last
low endpoint, then the source's logarithmic last-level certificate follows
with the last sample rate `gLast`.
-/
theorem binaryEndpointAwareAdjacentRate_last_ge_of_bisection_bracket
    {m : ℕ} (hm : 0 < m)
    (optimal returned sampleRate : Fin (m + 2) → ℝ)
    {gLast lower delta : ℝ}
    (hoptimalLevels : BinaryEndpointLevelVector optimal)
    (hgLast_nonneg : 0 ≤ gLast)
    (hgLast :
      sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) = gLast)
    (B :
      EconCSLib.Optimization.RealBisectionBracket
        (optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
        lower
        (returned (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
        delta) :
    binaryEndpointAwareAdjacentRate optimal sampleRate
        (lastAdjacentIndex : Fin (m + 1)) -
        gLast *
          Real.log
            ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                  delta) /
              optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
      binaryEndpointAwareAdjacentRate returned sampleRate
        (lastAdjacentIndex : Fin (m + 1)) := by
  let last : Fin (m + 1) := lastAdjacentIndex
  let low : Fin (m + 2) := adjacentLowIndex last
  let target : ℝ := optimal low
  let upper : ℝ := returned low
  have hlast_val : last.val = m := by
    simp [last]
  have hfirst_val : last.val ≠ 0 := by
    omega
  have htarget_pos : 0 < target := by
    simpa [target, low, last] using
      BinaryEndpointLevelVector_last_low_pos
        (m := m) hm hoptimalLevels
  have hupper_pos : 0 < upper := by
    exact lt_of_lt_of_le htarget_pos B.target_le_upper
  have hupper_le : upper ≤ target + delta := by
    simpa [target, upper, low, last] using B.upper_le_target_add_delta
  have htarget_delta_pos : 0 < target + delta :=
    lt_of_lt_of_le hupper_pos hupper_le
  have hlog_le : Real.log upper ≤ Real.log (target + delta) :=
    Real.log_le_log hupper_pos hupper_le
  have hneglog_le : -Real.log (target + delta) ≤ -Real.log upper := by
    linarith
  have hscaled_neglog :
      gLast * (-Real.log (target + delta)) ≤
        gLast * (-Real.log upper) :=
    mul_le_mul_of_nonneg_left hneglog_le hgLast_nonneg
  have hopt_last :
      binaryEndpointAwareAdjacentRate optimal sampleRate last =
        gLast * (-Real.log target) := by
    have hbranch :=
      binaryEndpointAwareAdjacentRate_last optimal sampleRate last
        hfirst_val hlast_val
    have hbranch' :
        binaryEndpointAwareAdjacentRate optimal sampleRate last =
          -(sampleRate low * Real.log target) := by
      simpa [target, low, last] using hbranch
    calc
      binaryEndpointAwareAdjacentRate optimal sampleRate last
          = -(sampleRate low * Real.log target) := hbranch'
      _ = gLast * (-Real.log target) := by
        rw [hgLast]
        ring
  have hreturned_last :
      binaryEndpointAwareAdjacentRate returned sampleRate last =
        gLast * (-Real.log upper) := by
    have hbranch :=
      binaryEndpointAwareAdjacentRate_last returned sampleRate last
        hfirst_val hlast_val
    have hbranch' :
        binaryEndpointAwareAdjacentRate returned sampleRate last =
          -(sampleRate low * Real.log upper) := by
      simpa [upper, low, last] using hbranch
    calc
      binaryEndpointAwareAdjacentRate returned sampleRate last
          = -(sampleRate low * Real.log upper) := hbranch'
      _ = gLast * (-Real.log upper) := by
        rw [hgLast]
        ring
  have hleft :
      binaryEndpointAwareAdjacentRate optimal sampleRate last -
          gLast * Real.log ((target + delta) / target) =
        gLast * (-Real.log (target + delta)) := by
    have hlog_div :
        Real.log ((target + delta) / target) =
          Real.log (target + delta) - Real.log target := by
      rw [Real.log_div (ne_of_gt htarget_delta_pos) (ne_of_gt htarget_pos)]
    rw [hopt_last, hlog_div]
    ring
  calc
    binaryEndpointAwareAdjacentRate optimal sampleRate
        (lastAdjacentIndex : Fin (m + 1)) -
        gLast *
          Real.log
            ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                  delta) /
              optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
        = gLast * (-Real.log (target + delta)) := by
          simpa [last, low, target] using hleft
    _ ≤ gLast * (-Real.log upper) := hscaled_neglog
    _ = binaryEndpointAwareAdjacentRate returned sampleRate
        (lastAdjacentIndex : Fin (m + 1)) := by
          simpa [last, low, upper] using hreturned_last.symm

/--
Theorem 3.2 shifted-last-level loss bound.  This is the source step
`g log((tStar + delta) / tStar) <= g delta / tStar`, used when the final
outer bisection endpoint is within `delta` of the optimal final level.
-/
theorem binaryEndpointAwareLastRateShift_log_loss_le_linear
    {g tStar delta : ℝ}
    (hg : 0 ≤ g)
    (htStar : 0 < tStar)
    (hdelta : 0 ≤ delta) :
    g * Real.log ((tStar + delta) / tStar) ≤
      g * (delta / tStar) :=
  EconCSLib.Math.mul_log_add_div_self_le_mul_div hg htStar hdelta

/--
Theorem 3.2 source-shaped logarithmic certificate.  If the final returned
rate loses at most the last-level logarithmic shift, every inner bisection
rate loses at most the first-level logarithmic shift relative to the final
returned rate, and the corresponding linearized losses sum to `eps`, then the
returned finite objective is `eps`-optimal.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_le_of_shift_log_certificates
    {m : ℕ}
    (optimal returned sampleRate : Fin (m + 2) → ℝ)
    {rStar gLast tFirstStar tLastStar delta eps : ℝ}
    (hgLast : 0 ≤ gLast)
    (htFirstStar : 0 < tFirstStar)
    (htLastStar : 0 < tLastStar)
    (hdelta : 0 ≤ delta)
    (hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal sampleRate i = rStar)
    (hlast :
      rStar -
          gLast * Real.log ((tLastStar + delta) / tLastStar) ≤
        binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1)) -
            gLast * Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned sampleRate i)
    (hlinear :
      gLast * (delta / tLastStar) +
          gLast * (delta / tFirstStar) ≤ eps) :
    binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
        binaryEndpointAwareAdjacentRateObjective returned sampleRate ≤
      eps := by
  have hlast_log :
      gLast * Real.log ((tLastStar + delta) / tLastStar) ≤
        gLast * (delta / tLastStar) :=
    binaryEndpointAwareLastRateShift_log_loss_le_linear
      hgLast htLastStar hdelta
  have hfirst_log :
      gLast * Real.log ((tFirstStar + delta) / tFirstStar) ≤
        gLast * (delta / tFirstStar) :=
    binaryEndpointAwareLastRateShift_log_loss_le_linear
      hgLast htFirstStar hdelta
  have hsum :
      gLast * Real.log ((tLastStar + delta) / tLastStar) +
          gLast * Real.log ((tFirstStar + delta) / tFirstStar) ≤ eps := by
    exact (add_le_add hlast_log hfirst_log).trans hlinear
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_le_of_last_rate_and_grid
      optimal returned sampleRate
      (rStar := rStar)
      (epsLast :=
        gLast * Real.log ((tLastStar + delta) / tLastStar))
      (epsGrid :=
        gLast * Real.log ((tFirstStar + delta) / tFirstStar))
      (eps := eps)
      hoptimal hlast hgrid hsum

/--
Linear loss bound from lower bounds on the first and last optimal levels.  This
is the reciprocal-monotonicity step used after Lemma C.6 and Corollary C.3 in
the source proof of Theorem 3.2.
-/
theorem binaryEndpointAwareAdjacentRateObjective_shift_linear_loss_le_of_lower_bounds
    {gLast delta tFirstStar tLastStar firstLower lastLower eps : ℝ}
    (hgLast : 0 ≤ gLast)
    (hdelta : 0 ≤ delta)
    (hfirstLower_pos : 0 < firstLower)
    (hlastLower_pos : 0 < lastLower)
    (hfirstLower : firstLower ≤ tFirstStar)
    (hlastLower : lastLower ≤ tLastStar)
    (hbound :
      gLast * (delta / lastLower) +
          gLast * (delta / firstLower) ≤ eps) :
    gLast * (delta / tLastStar) +
        gLast * (delta / tFirstStar) ≤ eps := by
  have htFirstStar : 0 < tFirstStar := lt_of_lt_of_le hfirstLower_pos hfirstLower
  have htLastStar : 0 < tLastStar := lt_of_lt_of_le hlastLower_pos hlastLower
  have hlast_div :
      delta / tLastStar ≤ delta / lastLower := by
    exact div_le_div_of_nonneg_left hdelta hlastLower_pos hlastLower
  have hfirst_div :
      delta / tFirstStar ≤ delta / firstLower := by
    exact div_le_div_of_nonneg_left hdelta hfirstLower_pos hfirstLower
  have hlast_mul :
      gLast * (delta / tLastStar) ≤ gLast * (delta / lastLower) :=
    mul_le_mul_of_nonneg_left hlast_div hgLast
  have hfirst_mul :
      gLast * (delta / tFirstStar) ≤ gLast * (delta / firstLower) :=
    mul_le_mul_of_nonneg_left hfirst_div hgLast
  exact (add_le_add hlast_mul hfirst_mul).trans hbound

/--
Theorem 3.2 delta-choice bridge.  Choosing
`delta = eps / (gLast * (lastLower⁻¹ + firstLower⁻¹))` makes the linearized
loss budget implied by the first- and last-level lower bounds at most `eps`.
-/
theorem binaryEndpointAwareAdjacentRateObjective_shift_linear_loss_le_of_delta_choice
    {gLast delta tFirstStar tLastStar firstLower lastLower eps : ℝ}
    (hgLast_pos : 0 < gLast)
    (heps : 0 ≤ eps)
    (hfirstLower_pos : 0 < firstLower)
    (hlastLower_pos : 0 < lastLower)
    (hfirstLower : firstLower ≤ tFirstStar)
    (hlastLower : lastLower ≤ tLastStar)
    (hdelta :
      delta =
        eps / (gLast * (lastLower⁻¹ + firstLower⁻¹))) :
    gLast * (delta / tLastStar) +
        gLast * (delta / tFirstStar) ≤ eps := by
  have hlast_inv_pos : 0 < lastLower⁻¹ := inv_pos.mpr hlastLower_pos
  have hfirst_inv_pos : 0 < firstLower⁻¹ := inv_pos.mpr hfirstLower_pos
  have hsum_pos : 0 < lastLower⁻¹ + firstLower⁻¹ :=
    add_pos hlast_inv_pos hfirst_inv_pos
  have hdelta_nonneg : 0 ≤ delta := by
    rw [hdelta]
    exact div_nonneg heps (mul_nonneg hgLast_pos.le hsum_pos.le)
  have hbudget_eq :
      gLast * (delta * lastLower⁻¹) +
          gLast * (delta * firstLower⁻¹) = eps :=
    EconCSLib.Math.mul_delta_split_budget_eq_of_delta_eq_div_mul_add
      hgLast_pos.ne' hsum_pos.ne' hdelta
  have hbudget :
      gLast * (delta / lastLower) +
          gLast * (delta / firstLower) ≤ eps := by
    have hconvert :
        gLast * (delta / lastLower) +
            gLast * (delta / firstLower) =
          gLast * (delta * lastLower⁻¹) +
            gLast * (delta * firstLower⁻¹) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
    exact le_of_eq (hconvert.trans hbudget_eq)
  exact
    binaryEndpointAwareAdjacentRateObjective_shift_linear_loss_le_of_lower_bounds
      hgLast_pos.le hdelta_nonneg hfirstLower_pos hlastLower_pos
      hfirstLower hlastLower hbudget

/--
Theorem 3.2 approximation certificate with the source's delta choice.  This
packages the remaining algorithm-facing obligations into the two rate
certificates (`hlast` and `hgrid`) and the first/last optimal-level lower
bounds supplied by Lemma C.6 and Corollary C.3.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_certificates
    {m : ℕ}
    (optimal returned sampleRate : Fin (m + 2) → ℝ)
    {rStar gLast tFirstStar tLastStar firstLower lastLower delta eps : ℝ}
    (hgLast_pos : 0 < gLast)
    (heps : 0 ≤ eps)
    (hfirstLower_pos : 0 < firstLower)
    (hlastLower_pos : 0 < lastLower)
    (hfirstLower : firstLower ≤ tFirstStar)
    (hlastLower : lastLower ≤ tLastStar)
    (hdelta :
      delta =
        eps / (gLast * (lastLower⁻¹ + firstLower⁻¹)))
    (hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal sampleRate i = rStar)
    (hlast :
      rStar -
          gLast * Real.log ((tLastStar + delta) / tLastStar) ≤
        binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1)) -
            gLast * Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned sampleRate i) :
    binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
        binaryEndpointAwareAdjacentRateObjective returned sampleRate ≤
      eps := by
  have hsum_pos : 0 < lastLower⁻¹ + firstLower⁻¹ :=
    add_pos (inv_pos.mpr hlastLower_pos) (inv_pos.mpr hfirstLower_pos)
  have hdelta_nonneg : 0 ≤ delta := by
    rw [hdelta]
    exact div_nonneg heps (mul_nonneg hgLast_pos.le hsum_pos.le)
  have htFirstStar : 0 < tFirstStar := lt_of_lt_of_le hfirstLower_pos hfirstLower
  have htLastStar : 0 < tLastStar := lt_of_lt_of_le hlastLower_pos hlastLower
  have hlinear :
      gLast * (delta / tLastStar) +
          gLast * (delta / tFirstStar) ≤ eps :=
    binaryEndpointAwareAdjacentRateObjective_shift_linear_loss_le_of_delta_choice
      hgLast_pos heps hfirstLower_pos hlastLower_pos hfirstLower hlastLower
      hdelta
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_le_of_shift_log_certificates
      optimal returned sampleRate hgLast_pos.le htFirstStar htLastStar
      hdelta_nonneg hoptimal hlast hgrid hlinear

/--
Theorem 3.2 approximation certificate with the Lemma C.6 last-level lower
bound derived from the source's width-minimality condition.  This leaves the
first-level lower bound as the remaining Corollary C.3 input, but no longer
requires an explicit certificate for the last optimal level.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_width_minimal
    {m : ℕ} (hm : 0 < m)
    (optimal returned sampleRate : Fin (m + 2) → ℝ)
    {rStar gLast tFirstStar firstLower delta eps : ℝ}
    (hgLast_pos : 0 < gLast)
    (heps : 0 ≤ eps)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (hlast_width :
      ∀ i : Fin (m + 1),
        optimal (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
            optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
          optimal (adjacentHighIndex i) - optimal (adjacentLowIndex i))
    (hfirstLower_pos : 0 < firstLower)
    (hfirstLower : firstLower ≤ tFirstStar)
    (hdelta :
      delta =
        eps /
          (gLast *
            ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ + firstLower⁻¹)))
    (hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal sampleRate i = rStar)
    (hlast :
      rStar -
          gLast *
            Real.log
              ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                    delta) /
                optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1)) -
            gLast * Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned sampleRate i) :
    binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
        binaryEndpointAwareAdjacentRateObjective returned sampleRate ≤
      eps := by
  let lastLower : ℝ := 1 - 1 / ((m + 1 : ℕ) : ℝ)
  have hlastLower_pos : 0 < lastLower := by
    simpa [lastLower] using one_sub_inv_adjacent_count_pos hm
  have hlastLower :
      lastLower ≤
        optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) := by
    simpa [lastLower] using
      BinaryEndpointLevelVector_last_low_ge_one_sub_inv_of_last_width_le_all
        hoptimal_levels hlast_width
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_certificates
      optimal returned sampleRate
      (rStar := rStar) (gLast := gLast) (tFirstStar := tFirstStar)
      (tLastStar :=
        optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
      (firstLower := firstLower) (lastLower := lastLower)
      (delta := delta) (eps := eps)
      hgLast_pos heps hfirstLower_pos hlastLower_pos hfirstLower
      hlastLower (by simpa [lastLower] using hdelta) hoptimal hlast hgrid

/--
Source-shaped operation count for the NestedBisection runtime proof.  It
counts one outer comparison per outer iteration plus `(M - 3)` inner bisection
calls, each with the same worst-case inner iteration count.
-/
def nestedBisectionOperationCount
    (M outerSteps innerSteps : ℕ) : ℕ :=
  outerSteps + outerSteps * ((M - 3) * innerSteps)

/--
Lemma C.9 runtime core: if the outer bisection has at most `L + 1` iterations
and each inner bisection has at most `L` iterations, then the source-shaped
NestedBisection operation count is bounded by the reusable nested-bisection
closed form.
-/
theorem nestedBisectionOperationCount_le_stepBound
    {M L outerSteps innerSteps : ℕ}
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    nestedBisectionOperationCount M outerSteps innerSteps ≤
      EconCSLib.Optimization.nestedBisectionStepBound M L := by
  simpa [nestedBisectionOperationCount] using
    EconCSLib.Optimization.nestedBisection_operation_count_le
      (M := M) (L := L) houter hinner

/--
Lemma C.9 runtime core in finite quadratic form: the source-shaped
NestedBisection operation count is bounded by `M * (L + 1)^2`.  This is the
arithmetic content of the paper's `O(M log^2(1 / δ))` bound once `L` is chosen
as a logarithmic bisection depth.
-/
theorem nestedBisectionOperationCount_le_mul_succ_sq
    {M L outerSteps innerSteps : ℕ} (hM : 0 < M)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    nestedBisectionOperationCount M outerSteps innerSteps ≤
      M * (L + 1) ^ 2 :=
  (nestedBisectionOperationCount_le_stepBound
    (M := M) (L := L) houter hinner).trans
    (EconCSLib.Optimization.nestedBisectionStepBound_le_mul_succ_sq hM)

/--
Theorem 3.2 Algorithm-1 run certificate.  A run that supplies the source's
rate certificates, first/last optimal-level lower bounds, delta choice, and
outer/inner iteration bounds is both `eps`-optimal and within the reusable
nested-bisection operation-count bound.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_run
    {m M L outerSteps innerSteps : ℕ}
    (optimal returned sampleRate : Fin (m + 2) → ℝ)
    {rStar gLast tFirstStar tLastStar firstLower lastLower delta eps : ℝ}
    (hgLast_pos : 0 < gLast)
    (heps : 0 ≤ eps)
    (hfirstLower_pos : 0 < firstLower)
    (hlastLower_pos : 0 < lastLower)
    (hfirstLower : firstLower ≤ tFirstStar)
    (hlastLower : lastLower ≤ tLastStar)
    (hdelta :
      delta =
        eps / (gLast * (lastLower⁻¹ + firstLower⁻¹)))
    (hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal sampleRate i = rStar)
    (hlast :
      rStar -
          gLast * Real.log ((tLastStar + delta) / tLastStar) ≤
        binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1)) -
            gLast * Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned sampleRate i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
        binaryEndpointAwareAdjacentRateObjective returned sampleRate ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  constructor
  · exact
      binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_certificates
        optimal returned sampleRate hgLast_pos heps hfirstLower_pos
        hlastLower_pos hfirstLower hlastLower hdelta hoptimal hlast hgrid
  · exact nestedBisectionOperationCount_le_stepBound houter hinner

/--
Theorem 3.2 Algorithm-1 run certificate with the Lemma C.6 last-level lower
bound derived from the source's width-minimality condition.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_width_minimal_run
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (optimal returned sampleRate : Fin (m + 2) → ℝ)
    {rStar gLast tFirstStar firstLower delta eps : ℝ}
    (hgLast_pos : 0 < gLast)
    (heps : 0 ≤ eps)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (hlast_width :
      ∀ i : Fin (m + 1),
        optimal (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
            optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
          optimal (adjacentHighIndex i) - optimal (adjacentLowIndex i))
    (hfirstLower_pos : 0 < firstLower)
    (hfirstLower : firstLower ≤ tFirstStar)
    (hdelta :
      delta =
        eps /
          (gLast *
            ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ + firstLower⁻¹)))
    (hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal sampleRate i = rStar)
    (hlast :
      rStar -
          gLast *
            Real.log
              ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                    delta) /
                optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1)) -
            gLast * Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned sampleRate i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
        binaryEndpointAwareAdjacentRateObjective returned sampleRate ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  constructor
  · exact
      binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_width_minimal
        hm optimal returned sampleRate hgLast_pos heps hoptimal_levels
        hlast_width hfirstLower_pos hfirstLower hdelta hoptimal hlast hgrid
  · exact nestedBisectionOperationCount_le_stepBound houter hinner

/--
General monotone-match Theorem 3.2 run certificate with the source Corollary
C.3 first-level lower bound discharged.  The remaining hypotheses are the
source-shaped run certificates: the optimal chain equalizes rates, the last
interval is width-minimal, the returned run satisfies the final last-rate and
inner-grid inequalities, and the outer/inner iteration counts are bounded.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_monotone_equalized_width_minimal_run
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (optimal returned sampleRate : Fin (m + 2) → ℝ)
    {rStar gLast delta eps : ℝ}
    (hgLast_pos : 0 < gLast)
    (heps : 0 ≤ eps)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (heq : BinaryEndpointAwareAdjacentRatesEqualize optimal sampleRate)
    (hsample_pos : ∀ idx : Fin (m + 2), 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hfirst_sample :
      sampleRate (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) = 1)
    (hlast_width :
      ∀ i : Fin (m + 1),
        optimal (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
            optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
          optimal (adjacentHighIndex i) - optimal (adjacentLowIndex i))
    (hdelta :
      delta =
        eps /
          (gLast *
            ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ +
              (((1 / ((m + 1 : ℕ) : ℝ)) ^ 2) / 2)⁻¹)))
    (hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal sampleRate i = rStar)
    (hlast :
      rStar -
          gLast *
            Real.log
              ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                    delta) /
                optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1)) -
            gLast *
              Real.log
                ((optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) +
                    delta) /
                  optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))) ≤
          binaryEndpointAwareAdjacentRate returned sampleRate i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
        binaryEndpointAwareAdjacentRateObjective returned sampleRate ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let firstLower : ℝ := ((1 / ((m + 1 : ℕ) : ℝ)) ^ 2) / 2
  have hfirstLower_pos : 0 < firstLower := by
    dsimp [firstLower]
    positivity
  have hfirstLower :
      firstLower ≤
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) := by
    simpa [firstLower] using
      BinaryEndpointAwareAdjacentRatesEqualize_monotone_scaled_first_level_ge_half_inv_adjacent_count_sq
        hm hoptimal_levels heq hsample_pos hsample_mono hfirst_sample
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_width_minimal_run
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm optimal returned sampleRate
      (rStar := rStar) (gLast := gLast)
      (tFirstStar :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
      (firstLower := firstLower) (delta := delta) (eps := eps)
      hgLast_pos heps hoptimal_levels hlast_width hfirstLower_pos
      hfirstLower (by simpa [firstLower] using hdelta) hoptimal hlast
      hgrid houter hinner

/--
General monotone-match Theorem 3.2 run certificate from source-shaped
bisection invariants.  The final last-rate loss is derived from the outer
bisection bracket, and the inner grid loss is derived from the interior
low-endpoint bisection brackets; callers no longer supply those two rate
inequalities directly.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_monotone_equalized_width_minimal_bracket_run
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (optimal returned sampleRate : Fin (m + 2) → ℝ)
    {rStar gLast delta eps lastBracketLower : ℝ}
    (hgLast_pos : 0 < gLast)
    (heps : 0 ≤ eps)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (hreturned_levels : BinaryEndpointLevelVector returned)
    (heq : BinaryEndpointAwareAdjacentRatesEqualize optimal sampleRate)
    (hsample_pos : ∀ idx : Fin (m + 2), 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hfirst_sample :
      sampleRate (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) = 1)
    (hgLast :
      sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) =
        gLast)
    (hlast_width :
      ∀ i : Fin (m + 1),
        optimal (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
            optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
          optimal (adjacentHighIndex i) - optimal (adjacentLowIndex i))
    (hdelta :
      delta =
        eps /
          (gLast *
            ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ +
              (((1 / ((m + 1 : ℕ) : ℝ)) ^ 2) / 2)⁻¹)))
    (hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal sampleRate i = rStar)
    (hfirstRate :
      binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)) ≤
        binaryEndpointAwareAdjacentRate returned sampleRate
          (firstAdjacentIndex : Fin (m + 1)))
    (hlastBracket :
      EconCSLib.Optimization.RealBisectionBracket
        (optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
        lastBracketLower
        (returned (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
        delta)
    (root lower : Fin (m + 1) → ℝ)
    (hroot0 :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m → 0 < root i)
    (htFirst_le_root :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) ≤
          root i)
    (hroot_rate :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (returned (adjacentHighIndex i)) (root i) =
          binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1)))
    (hbracket :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        EconCSLib.Optimization.RealBisectionBracket
          (root i) (lower i) (returned (adjacentLowIndex i)) delta)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
        binaryEndpointAwareAdjacentRateObjective returned sampleRate ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  have hfirstHigh_pos :
      0 <
        optimal
          (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) := by
    have hnot_first :
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))).val ≠ 0 := by
      simp [adjacentHighIndex, firstAdjacentIndex]
    exact
      BinaryEndpointLevelVector_pos_of_not_first hoptimal_levels
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) hnot_first
  have hfirstLower_pos :
      0 < ((1 / ((m + 1 : ℕ) : ℝ)) ^ 2) / 2 := by
    positivity
  have hlastLower_pos : 0 < 1 - 1 / ((m + 1 : ℕ) : ℝ) :=
    one_sub_inv_adjacent_count_pos hm
  have hsum_pos :
      0 <
        (1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ +
          (((1 / ((m + 1 : ℕ) : ℝ)) ^ 2) / 2)⁻¹ :=
    add_pos (inv_pos.mpr hlastLower_pos) (inv_pos.mpr hfirstLower_pos)
  have hdelta_nonneg : 0 ≤ delta := by
    rw [hdelta]
    exact div_nonneg heps (mul_nonneg hgLast_pos.le hsum_pos.le)
  have hlastRate :
      binaryEndpointAwareAdjacentRate optimal sampleRate
          (lastAdjacentIndex : Fin (m + 1)) -
          gLast *
            Real.log
              ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                    delta) /
                optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)) :=
    binaryEndpointAwareAdjacentRate_last_ge_of_bisection_bracket
      hm optimal returned sampleRate hoptimal_levels hgLast_pos.le hgLast
      hlastBracket
  have hlast :
      rStar -
          gLast *
            Real.log
              ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                    delta) /
                optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)) := by
    simpa [hoptimal (lastAdjacentIndex : Fin (m + 1))] using hlastRate
  have hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1)) -
            gLast *
              Real.log
                ((optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) +
                    delta) /
                  optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))) ≤
          binaryEndpointAwareAdjacentRate returned sampleRate i :=
    by
      intro i
      have hratio_ge_one :
          1 ≤
            (optimal
                  (adjacentHighIndex
                    (firstAdjacentIndex : Fin (m + 1))) +
                delta) /
              optimal
                (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) := by
        rw [le_div_iff₀ hfirstHigh_pos]
        linarith
      have hlog_nonneg :
          0 ≤
            Real.log
              ((optimal
                    (adjacentHighIndex
                      (firstAdjacentIndex : Fin (m + 1))) +
                  delta) /
                optimal
                  (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))) :=
        Real.log_nonneg hratio_ge_one
      have hscaled_log_nonneg :
          0 ≤
            gLast *
              Real.log
                ((optimal
                      (adjacentHighIndex
                        (firstAdjacentIndex : Fin (m + 1))) +
                    delta) /
                  optimal
                    (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))) :=
        mul_nonneg hgLast_pos.le hlog_nonneg
      by_cases hi_first : i.val = 0
      · have hi : i = (firstAdjacentIndex : Fin (m + 1)) := by
          ext
          simpa [firstAdjacentIndex] using hi_first
        subst i
        exact
          (sub_le_self
            (binaryEndpointAwareAdjacentRate returned sampleRate
              (lastAdjacentIndex : Fin (m + 1)))
            hscaled_log_nonneg).trans hfirstRate
      · by_cases hi_last : i.val = m
        · have hi : i = (lastAdjacentIndex : Fin (m + 1)) := by
            ext
            simpa [lastAdjacentIndex] using hi_last
          subst i
          exact
            sub_le_self
              (binaryEndpointAwareAdjacentRate returned sampleRate
                (lastAdjacentIndex : Fin (m + 1)))
              hscaled_log_nonneg
        · have hhigh_not_first :
              (adjacentHighIndex i).val ≠ 0 := by
            simp [adjacentHighIndex]
          have hhigh_not_last :
              (adjacentHighIndex i).val ≠ m + 1 := by
            simp [adjacentHighIndex]
            omega
          have hlow_not_last :
              (adjacentLowIndex i).val ≠ m + 1 := by
            simp [adjacentLowIndex]
            omega
          have hhi0 :
              0 < returned (adjacentHighIndex i) :=
            BinaryEndpointLevelVector_pos_of_not_first
              hreturned_levels (adjacentHighIndex i) hhigh_not_first
          have hhi1 :
              returned (adjacentHighIndex i) < 1 :=
            BinaryEndpointLevelVector_lt_one_of_not_last
              hreturned_levels (adjacentHighIndex i) hhigh_not_last
          have hreturned1 :
              returned (adjacentLowIndex i) < 1 :=
            BinaryEndpointLevelVector_lt_one_of_not_last
              hreturned_levels (adjacentLowIndex i) hlow_not_last
          have hlow_rate_le_last :
              sampleRate (adjacentLowIndex i) ≤ gLast := by
            have hidx :
                (adjacentLowIndex i).val ≤
                  (adjacentLowIndex
                    (lastAdjacentIndex : Fin (m + 1))).val := by
              simp [adjacentLowIndex, lastAdjacentIndex]
              omega
            exact
              (hsample_mono
                (a := adjacentLowIndex i)
                (b :=
                  adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
                hidx).trans_eq hgLast
          have hlocal_scale :
              sampleRate (adjacentLowIndex i) *
                  Real.log
                    ((optimal
                        (adjacentHighIndex
                          (firstAdjacentIndex : Fin (m + 1))) +
                      delta) /
                    optimal
                      (adjacentHighIndex
                        (firstAdjacentIndex : Fin (m + 1)))) ≤
                gLast *
                  Real.log
                    ((optimal
                        (adjacentHighIndex
                          (firstAdjacentIndex : Fin (m + 1))) +
                      delta) /
                    optimal
                      (adjacentHighIndex
                        (firstAdjacentIndex : Fin (m + 1)))) :=
            mul_le_mul_of_nonneg_right hlow_rate_le_last hlog_nonneg
          have hstep :=
            binaryEndpointAwareAdjacentRate_interior_ge_target_sub_first_log_of_bisection_bracket
              returned sampleRate i hi_first hi_last
              (root := root i) (lower := lower i) (delta := delta)
              (target :=
                binaryEndpointAwareAdjacentRate returned sampleRate
                  (lastAdjacentIndex : Fin (m + 1)))
              (tFirst :=
                optimal
                  (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
              (hsample_pos (adjacentHighIndex i)).le
              (hsample_pos (adjacentLowIndex i)).le
              (add_pos (hsample_pos (adjacentHighIndex i))
                (hsample_pos (adjacentLowIndex i)))
              hhi0 hhi1 (hroot0 i hi_first hi_last) hreturned1
              hfirstHigh_pos (htFirst_le_root i hi_first hi_last)
              hdelta_nonneg (hroot_rate i hi_first hi_last)
              (hbracket i hi_first hi_last)
          linarith
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_monotone_equalized_width_minimal_run
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm optimal returned sampleRate
      (rStar := rStar) (gLast := gLast) (delta := delta) (eps := eps)
      hgLast_pos heps hoptimal_levels heq hsample_pos hsample_mono
      hfirst_sample hlast_width hdelta hoptimal hlast hgrid houter hinner

/--
Executable weighted outer-bisection bracket for the last low endpoint.  A
sound weighted source classifier, an initial bracket, and the usual bisection
width bound imply that the returned upper endpoint remains within `delta` of
the optimal last low endpoint.
-/
theorem theorem32_monotone_last_low_bracket_of_weighted_outer_run
    {m outerSteps : ℕ}
    (optimal returned sampleRate : Fin (m + 2) → ℝ)
    {delta lower0 upper0 : ℝ}
    (candidate : ℝ → Fin (m + 2) → ℝ)
    (habove :
      ∀ x,
        theorem32OuterSourceWeightedRateAbove (candidate x) sampleRate = true →
          optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤ x)
    (hbelow :
      ∀ x,
        theorem32OuterSourceWeightedRateAbove (candidate x) sampleRate = false →
          x ≤ optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
    (hlower0 :
      lower0 ≤ optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
    (hupper0 :
      optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤ upper0)
    (hwidth : (upper0 - lower0) / (2 : ℝ) ^ outerSteps ≤ delta)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (fun x => theorem32OuterSourceWeightedRateAbove (candidate x) sampleRate)
          outerSteps lower0 upper0).2 =
        returned (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) :
    EconCSLib.Optimization.RealBisectionBracket
      (optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
      (EconCSLib.Optimization.realBisectionRun
          (fun x => theorem32OuterSourceWeightedRateAbove (candidate x) sampleRate)
          outerSteps lower0 upper0).1
      (returned (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
      delta := by
  let target : ℝ :=
    optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
  let above : ℝ → Bool := fun x =>
    theorem32OuterSourceWeightedRateAbove (candidate x) sampleRate
  have B :
      EconCSLib.Optimization.RealBisectionBracket target
        (EconCSLib.Optimization.realBisectionRun above outerSteps lower0 upper0).1
        (EconCSLib.Optimization.realBisectionRun above outerSteps lower0 upper0).2
        delta :=
    EconCSLib.Optimization.realBisectionRun_bracket_of_width_le
      (above := above) (n := outerSteps)
      (target := target) (lower := lower0) (upper := upper0)
      (delta := delta)
      (by simpa [target, above] using habove)
      (by simpa [target, above] using hbelow)
      (by simpa [target] using hlower0)
      (by simpa [target] using hupper0)
      hwidth
  simpa [target, above, hreturnedLast] using B

/--
Executable weighted inner low-endpoint bisection brackets.  Each canonical
threshold bisection run around the exact low-endpoint root produces the
source-level bracket consumed by the monotone Theorem 3.2 grid proof.
-/
theorem theorem32_monotone_inner_low_bisection_brackets_of_runs
    {m innerSteps : ℕ}
    (returned sampleRate : Fin (m + 2) → ℝ)
    {delta : ℝ}
    (root lower0 upper0 : Fin (m + 1) → ℝ)
    (hinnerLower0 :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        lower0 i ≤ root i)
    (hinnerUpper0 :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        root i ≤ upper0 i)
    (hinnerWidth :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        (upper0 i - lower0 i) / (2 : ℝ) ^ innerSteps ≤ delta)
    (hreturnedLow :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps (lower0 i) (upper0 i)).2 =
          returned (adjacentLowIndex i)) :
    ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
      EconCSLib.Optimization.RealBisectionBracket
        (root i)
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps (lower0 i) (upper0 i)).1
        (returned (adjacentLowIndex i))
        delta := by
  intro i hi_first hi_last
  have B :
      EconCSLib.Optimization.RealBisectionBracket
        (root i)
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps (lower0 i) (upper0 i)).1
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps (lower0 i) (upper0 i)).2
        delta :=
    EconCSLib.Optimization.realBisectionRun_bracket_aboveTarget_of_width_le
      (n := innerSteps)
      (lower := lower0 i) (upper := upper0 i) (target := root i)
      (delta := delta)
      (hinnerLower0 i hi_first hi_last)
      (hinnerUpper0 i hi_first hi_last)
      (hinnerWidth i hi_first hi_last)
  simpa [hreturnedLow i hi_first hi_last] using B

/--
Weighted feasible-root constructor for the monotone Theorem 3.2 inner loop.
The exact root is the weighted Bernoulli low-endpoint inverse at the current
high endpoint and the returned last rate.
-/
theorem theorem32_monotone_inner_low_bisection_root_facts_of_feasible
    {m : ℕ}
    (returned sampleRate : Fin (m + 2) → ℝ)
    {tFirst target : ℝ}
    (root : Fin (m + 1) → ℝ)
    (hroot_def :
      root =
        fun i : Fin (m + 1) =>
          weightedBernoulliLowEndpointOfRateOrFloor
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            tFirst
            (returned (adjacentHighIndex i)) target)
    (hfeasible :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        WeightedBernoulliLowEndpointTargetFeasible
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          tFirst
          (returned (adjacentHighIndex i)) target) :
    (∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m → 0 < root i) ∧
      (∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m → tFirst ≤ root i) ∧
        (∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
          weightedBernoulliClosedThresholdRate
              (sampleRate (adjacentHighIndex i))
              (sampleRate (adjacentLowIndex i))
              (returned (adjacentHighIndex i)) (root i) =
            target) := by
  constructor
  · intro i hi_first hi_last
    have hmem :
        root i ∈ Set.Ioo tFirst (returned (adjacentHighIndex i)) := by
      simpa [hroot_def] using
        weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
          (hfeasible i hi_first hi_last)
    exact (hfeasible i hi_first hi_last).hfloor0.trans hmem.1
  constructor
  · intro i hi_first hi_last
    have hmem :
        root i ∈ Set.Ioo tFirst (returned (adjacentHighIndex i)) := by
      simpa [hroot_def] using
        weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
          (hfeasible i hi_first hi_last)
    exact le_of_lt hmem.1
  · intro i hi_first hi_last
    simpa [hroot_def] using
      weightedBernoulliLowEndpointOfRateOrFloor_rate_of_feasible
        (hfeasible i hi_first hi_last)

/--
Weighted inner feasibility from the source's floor/high and floor-rate
inequalities.  This is the monotone analogue of the uniform helper used later
in the appendix: positive weights and endpoint-level vectors discharge the
routine feasibility fields.
-/
theorem theorem32_monotone_inner_lowEndpointTargetFeasible_of_floor_lt_high_and_target_lt_floor_rate
    {m : ℕ} (hm : 0 < m)
    (optimal returned sampleRate : Fin (m + 2) → ℝ)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (hreturned_levels : BinaryEndpointLevelVector returned)
    (hsample_pos : ∀ idx : Fin (m + 2), 0 < sampleRate idx)
    (hfloor_lt_high :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) <
          returned (adjacentHighIndex i))
    (htarget_lt_floor_rate :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1)) <
          weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (returned (adjacentHighIndex i))
            (optimal (adjacentHighIndex
              (firstAdjacentIndex : Fin (m + 1)))) ) :
    ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
      WeightedBernoulliLowEndpointTargetFeasible
        (sampleRate (adjacentHighIndex i))
        (sampleRate (adjacentLowIndex i))
        (optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
        (returned (adjacentHighIndex i))
        (binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1))) := by
  intro i hi_first hi_last
  have htFirst0 :
      0 <
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) := by
    have hnot_first :
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))).val ≠ 0 := by
      simp [adjacentHighIndex, firstAdjacentIndex]
    exact
      BinaryEndpointLevelVector_pos_of_not_first hoptimal_levels
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) hnot_first
  have hhi_lt_one :
      returned (adjacentHighIndex i) < 1 := by
    have hnot_last : (adjacentHighIndex i).val ≠ m + 1 := by
      simp [adjacentHighIndex]
      omega
    exact
      BinaryEndpointLevelVector_lt_one_of_not_last
        hreturned_levels (adjacentHighIndex i) hnot_last
  have htarget_pos :
      0 <
        binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)) :=
    binaryEndpointAwareAdjacentRate_pos
      (m := m) hm returned sampleRate hreturned_levels
      (by intro j; exact hsample_pos (adjacentHighIndex j))
      (by intro j; exact hsample_pos (adjacentLowIndex j))
      (lastAdjacentIndex : Fin (m + 1))
  exact
    { hgHi := hsample_pos (adjacentHighIndex i)
      hgLo := hsample_pos (adjacentLowIndex i)
      hfloor0 := htFirst0
      hfloor_lt_hi := hfloor_lt_high i hi_first hi_last
      hpHi1 := hhi_lt_one
      htarget_pos := htarget_pos
      htarget_lt_floor := htarget_lt_floor_rate i hi_first hi_last }

/--
Raw weighted inner feasibility constructor.  This version avoids requiring a
full endpoint-vector certificate for the returned levels; callers supply the
primitive high-endpoint and target bounds directly.
-/
theorem theorem32_monotone_inner_lowEndpointTargetFeasible_of_raw_bounds
    {m : ℕ}
    (returned sampleRate : Fin (m + 2) → ℝ)
    {tFirst target : ℝ}
    (hsample_pos : ∀ idx : Fin (m + 2), 0 < sampleRate idx)
    (htFirst0 : 0 < tFirst)
    (hfloor_lt_high :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        tFirst < returned (adjacentHighIndex i))
    (hhigh_lt_one :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        returned (adjacentHighIndex i) < 1)
    (htarget_pos : 0 < target)
    (htarget_lt_floor_rate :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        target <
          weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (returned (adjacentHighIndex i)) tFirst) :
    ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
      WeightedBernoulliLowEndpointTargetFeasible
        (sampleRate (adjacentHighIndex i))
        (sampleRate (adjacentLowIndex i))
        tFirst
        (returned (adjacentHighIndex i)) target := by
  intro i hi_first hi_last
  exact
    { hgHi := hsample_pos (adjacentHighIndex i)
      hgLo := hsample_pos (adjacentLowIndex i)
      hfloor0 := htFirst0
      hfloor_lt_hi := hfloor_lt_high i hi_first hi_last
      hpHi1 := hhigh_lt_one i hi_first hi_last
      htarget_pos := htarget_pos
      htarget_lt_floor := htarget_lt_floor_rate i hi_first hi_last }

/--
Weighted backward `CalculateOtherLevels` recursion for the monotone Theorem
3.2 proof.  The recursion is the nonuniform analogue of the source-style
backward low-endpoint bisection: the adjacent sample weights used at each
interior step are read from the corresponding adjacent interval.
-/
noncomputable def theorem32WeightedBackwardLowBisectionFromTop
    (n innerSteps : ℕ) (sampleRate : Fin (n + 2) → ℝ)
    (tFirst target lastLow : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => lastLow
  | d + 2 =>
      let high :=
        theorem32WeightedBackwardLowBisectionFromTop
          n innerSteps sampleRate tFirst target lastLow (d + 1)
      let adj : Fin (n + 1) := ⟨n - d - 1, by omega⟩
      let root :=
        weightedBernoulliLowEndpointOfRateOrFloor
          (sampleRate (adjacentHighIndex adj))
          (sampleRate (adjacentLowIndex adj))
          tFirst high target
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget root)
        innerSteps 0 high).2

/--
Endpoint vector produced by the weighted backward `CalculateOtherLevels`
recursion once the outer bisection has selected the penultimate endpoint.
-/
noncomputable def theorem32WeightedBackwardLowBisectionLevels
    (n innerSteps : ℕ) (sampleRate : Fin (n + 2) → ℝ)
    (tFirst target lastLow : ℝ) : Fin (n + 2) → ℝ := fun k =>
  if k.val = 0 then 0
  else
    theorem32WeightedBackwardLowBisectionFromTop
      n innerSteps sampleRate tFirst target lastLow (n + 1 - k.val)

/-- The weighted backward recursion fixes the final endpoint at `1`. -/
theorem theorem32WeightedBackwardLowBisectionLevels_last
    (n innerSteps : ℕ) (sampleRate : Fin (n + 2) → ℝ)
    (tFirst target lastLow : ℝ) :
    theorem32WeightedBackwardLowBisectionLevels
        n innerSteps sampleRate tFirst target lastLow
        (lastLevelIndex : Fin (n + 2)) = 1 := by
  simp [theorem32WeightedBackwardLowBisectionLevels,
    theorem32WeightedBackwardLowBisectionFromTop]

/--
The weighted backward recursion records the outer bisection's penultimate
endpoint.
-/
theorem theorem32WeightedBackwardLowBisectionLevels_last_low
    {n innerSteps : ℕ} (hn : 0 < n)
    (sampleRate : Fin (n + 2) → ℝ)
    (tFirst target lastLow : ℝ) :
    theorem32WeightedBackwardLowBisectionLevels
        n innerSteps sampleRate tFirst target lastLow
        (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) =
      lastLow := by
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
  simp [theorem32WeightedBackwardLowBisectionLevels,
    theorem32WeightedBackwardLowBisectionFromTop, adjacentLowIndex,
    lastAdjacentIndex, hn_ne]

/--
For the weighted backward recursion, the last adjacent endpoint-aware rate is
the weighted endpoint rate determined by the selected penultimate endpoint.
-/
theorem theorem32WeightedBackwardLowBisectionLevels_last_rate
    {n innerSteps : ℕ} (hn : 0 < n)
    (sampleRate : Fin (n + 2) → ℝ)
    (tFirst target lastLow : ℝ) :
    binaryEndpointAwareAdjacentRate
        (theorem32WeightedBackwardLowBisectionLevels
          n innerSteps sampleRate tFirst target lastLow)
        sampleRate
        (lastAdjacentIndex : Fin (n + 1)) =
      sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) *
        (-Real.log lastLow) := by
  let returned :=
    theorem32WeightedBackwardLowBisectionLevels
      n innerSteps sampleRate tFirst target lastLow
  let last : Fin (n + 1) := lastAdjacentIndex
  have hlast_val : last.val = n := by
    simp [last]
  have hfirst_val : last.val ≠ 0 := by
    omega
  have hbranch :=
    binaryEndpointAwareAdjacentRate_last returned sampleRate last
      hfirst_val hlast_val
  have hlow :
      returned (adjacentLowIndex last) = lastLow := by
    simpa [returned, last] using
      theorem32WeightedBackwardLowBisectionLevels_last_low
        (n := n) (innerSteps := innerSteps) hn sampleRate tFirst target lastLow
  calc
    binaryEndpointAwareAdjacentRate returned sampleRate last
        = -(sampleRate (adjacentLowIndex last) *
              Real.log (returned (adjacentLowIndex last))) := by
          simpa [returned, last] using hbranch
    _ = sampleRate (adjacentLowIndex last) * (-Real.log lastLow) := by
          rw [hlow]
          ring

/--
For every interior adjacent interval, the weighted backward recursion records
the upper endpoint returned by the corresponding low-endpoint bisection run.
-/
theorem theorem32WeightedBackwardLowBisectionLevels_returnedLow
    {n innerSteps : ℕ} (sampleRate : Fin (n + 2) → ℝ)
    (tFirst target lastLow : ℝ)
    (i : Fin (n + 1)) (hfirst : i.val ≠ 0) (hlast : i.val ≠ n) :
    let returned :=
      theorem32WeightedBackwardLowBisectionLevels
        n innerSteps sampleRate tFirst target lastLow
    let root : Fin (n + 1) → ℝ := fun j =>
      weightedBernoulliLowEndpointOfRateOrFloor
        (sampleRate (adjacentHighIndex j))
        (sampleRate (adjacentLowIndex j))
        tFirst
        (returned (adjacentHighIndex j)) target
    (EconCSLib.Optimization.realBisectionRun
      (EconCSLib.Optimization.realBisectionAboveTarget (root i))
      innerSteps 0 (returned (adjacentHighIndex i))).2 =
      returned (adjacentLowIndex i) := by
  dsimp
  have hi_lt : i.val < n := lt_of_le_of_ne (Nat.le_of_lt_succ i.2) hlast
  have hlow_sub :
      n + 1 - i.val = (n - i.val) + 1 := by omega
  have hhigh_sub :
      n + 1 - (i.val + 1) = n - i.val := by omega
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : n - i.val ≠ 0) with
    ⟨d, hd⟩
  have hlow_sub' : n + 1 - i.val = d + 2 := by omega
  have hhigh_sub' : n + 1 - (i.val + 1) = d + 1 := by omega
  have hadj :
      (⟨n - d - 1, by omega⟩ : Fin (n + 1)) = i := by
    ext
    simp
    omega
  simp [theorem32WeightedBackwardLowBisectionLevels, adjacentLowIndex,
    adjacentHighIndex, hfirst, hlow_sub', hhigh_sub',
    theorem32WeightedBackwardLowBisectionFromTop, hadj]

/--
Returned-low fact for the weighted recursion with the source last-rate target.
This is the form needed by the paper-facing weighted run wrapper: the exact
inner root is defined using the returned vector's actual last adjacent rate.
-/
theorem theorem32WeightedBackwardLowBisectionLevels_returnedLow_last_rate
    {n innerSteps : ℕ} (hn : 0 < n)
    (sampleRate : Fin (n + 2) → ℝ) (tFirst lastLow : ℝ)
    (i : Fin (n + 1)) (hfirst : i.val ≠ 0) (hlast : i.val ≠ n) :
    let target : ℝ :=
      sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) *
        (-Real.log lastLow)
    let returned :=
      theorem32WeightedBackwardLowBisectionLevels
        n innerSteps sampleRate tFirst target lastLow
    let root : Fin (n + 1) → ℝ := fun j =>
      weightedBernoulliLowEndpointOfRateOrFloor
        (sampleRate (adjacentHighIndex j))
        (sampleRate (adjacentLowIndex j))
        tFirst
        (returned (adjacentHighIndex j))
        (binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (n + 1)))
    (EconCSLib.Optimization.realBisectionRun
      (EconCSLib.Optimization.realBisectionAboveTarget (root i))
      innerSteps 0 (returned (adjacentHighIndex i))).2 =
      returned (adjacentLowIndex i) := by
  let target : ℝ :=
    sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) *
      (-Real.log lastLow)
  let returned :=
    theorem32WeightedBackwardLowBisectionLevels
      n innerSteps sampleRate tFirst target lastLow
  have htarget_eq :
      binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (n + 1)) =
        target := by
    simpa [returned, target] using
      theorem32WeightedBackwardLowBisectionLevels_last_rate
        (n := n) (innerSteps := innerSteps) hn sampleRate tFirst target lastLow
  change
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget
          (weightedBernoulliLowEndpointOfRateOrFloor
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            tFirst
            (returned (adjacentHighIndex i))
            (binaryEndpointAwareAdjacentRate returned sampleRate
              (lastAdjacentIndex : Fin (n + 1)))))
        innerSteps 0 (returned (adjacentHighIndex i))).2 =
        returned (adjacentLowIndex i)
  rw [htarget_eq]
  simpa [returned] using
    theorem32WeightedBackwardLowBisectionLevels_returnedLow
      (n := n) (innerSteps := innerSteps)
      sampleRate tFirst target lastLow i hfirst hlast

/--
Interior strictness for the weighted backward recursion from the source
bisection gap condition.
-/
theorem theorem32WeightedBackwardLowBisectionLevels_interior_adjacent_strict_of_feasible_gap
    {n innerSteps : ℕ} (sampleRate : Fin (n + 2) → ℝ)
    (tFirst target lastLow : ℝ)
    (hfeasible :
      let returned :=
        theorem32WeightedBackwardLowBisectionLevels
          n innerSteps sampleRate tFirst target lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        WeightedBernoulliLowEndpointTargetFeasible
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          tFirst
          (returned (adjacentHighIndex i)) target)
    (hgap :
      let returned :=
        theorem32WeightedBackwardLowBisectionLevels
          n innerSteps sampleRate tFirst target lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        (returned (adjacentHighIndex i) - 0) /
            (2 : ℝ) ^ innerSteps <
          returned (adjacentHighIndex i) - root i)
    (i : Fin (n + 1)) (hfirst : i.val ≠ 0) (hlast : i.val ≠ n) :
    theorem32WeightedBackwardLowBisectionLevels
        n innerSteps sampleRate tFirst target lastLow
        (adjacentLowIndex i) <
      theorem32WeightedBackwardLowBisectionLevels
        n innerSteps sampleRate tFirst target lastLow
        (adjacentHighIndex i) := by
  let returned :=
    theorem32WeightedBackwardLowBisectionLevels
      n innerSteps sampleRate tFirst target lastLow
  let root : Fin (n + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (sampleRate (adjacentHighIndex i))
      (sampleRate (adjacentLowIndex i))
      tFirst
      (returned (adjacentHighIndex i)) target
  have hmem :
      root i ∈ Set.Ioo tFirst (returned (adjacentHighIndex i)) := by
    simpa [root, returned] using
      weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
        (hfeasible i hfirst hlast)
  have hroot_nonneg : 0 ≤ root i := by
    exact le_of_lt ((hfeasible i hfirst hlast).hfloor0.trans hmem.1)
  have hroot_le_high : root i ≤ returned (adjacentHighIndex i) :=
    le_of_lt hmem.2
  have hreturnedLow :
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget (root i))
        innerSteps 0 (returned (adjacentHighIndex i))).2 =
        returned (adjacentLowIndex i) := by
    simpa [returned, root] using
      theorem32WeightedBackwardLowBisectionLevels_returnedLow
        (n := n) (innerSteps := innerSteps)
        sampleRate tFirst target lastLow i hfirst hlast
  have hstrict :
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget (root i))
        innerSteps 0 (returned (adjacentHighIndex i))).2 <
        returned (adjacentHighIndex i) := by
    exact
      EconCSLib.Optimization.realBisectionRun_aboveTarget_upper_lt_initial_upper_of_width_lt_gap
        (n := innerSteps) (lower := 0)
        (target := root i) (upper := returned (adjacentHighIndex i))
        hroot_nonneg hroot_le_high
        (by simpa [returned, root] using hgap i hfirst hlast)
  simpa [returned, hreturnedLow] using hstrict

/--
The first interior endpoint of the weighted backward recursion is positive once
there is a genuine first inner bisection call.
-/
theorem theorem32WeightedBackwardLowBisectionLevels_first_high_pos_of_feasible
    {n innerSteps : ℕ} (hn : 1 < n) (sampleRate : Fin (n + 2) → ℝ)
    (tFirst target lastLow : ℝ)
    (hfeasible :
      let returned :=
        theorem32WeightedBackwardLowBisectionLevels
          n innerSteps sampleRate tFirst target lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        WeightedBernoulliLowEndpointTargetFeasible
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          tFirst
          (returned (adjacentHighIndex i)) target) :
    0 <
      theorem32WeightedBackwardLowBisectionLevels
        n innerSteps sampleRate tFirst target lastLow
        (adjacentHighIndex (firstAdjacentIndex : Fin (n + 1))) := by
  let returned :=
    theorem32WeightedBackwardLowBisectionLevels
      n innerSteps sampleRate tFirst target lastLow
  let i : Fin (n + 1) := ⟨1, by omega⟩
  let root : Fin (n + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (sampleRate (adjacentHighIndex i))
      (sampleRate (adjacentLowIndex i))
      tFirst
      (returned (adjacentHighIndex i)) target
  have hi_first : i.val ≠ 0 := by
    simp [i]
  have hi_last : i.val ≠ n := by
    simp [i]
    omega
  have hmem :
      root i ∈ Set.Ioo tFirst (returned (adjacentHighIndex i)) := by
    simpa [root, returned] using
      weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
        (hfeasible i hi_first hi_last)
  have hroot_pos : 0 < root i :=
    (hfeasible i hi_first hi_last).hfloor0.trans hmem.1
  have hroot_nonneg : 0 ≤ root i := le_of_lt hroot_pos
  have hroot_le_high : root i ≤ returned (adjacentHighIndex i) :=
    le_of_lt hmem.2
  have hupper_ge_root :
      root i ≤
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 :=
    EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
      (n := innerSteps) (lower := 0)
      (target := root i) (upper := returned (adjacentHighIndex i))
      hroot_nonneg hroot_le_high
  have hreturnedLow :
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget (root i))
        innerSteps 0 (returned (adjacentHighIndex i))).2 =
        returned (adjacentLowIndex i) := by
    simpa [returned, root] using
      theorem32WeightedBackwardLowBisectionLevels_returnedLow
        (n := n) (innerSteps := innerSteps)
        sampleRate tFirst target lastLow i hi_first hi_last
  have hlevel_pos : 0 < returned (adjacentLowIndex i) := by
    exact hroot_pos.trans_le (by simpa [hreturnedLow] using hupper_ge_root)
  simpa [returned, i, adjacentLowIndex, adjacentHighIndex,
    firstAdjacentIndex] using hlevel_pos

/--
Endpoint-vector constructor for the weighted backward recursion from feasible
inner roots and the source bisection gap condition.
-/
theorem theorem32WeightedBackwardLowBisectionLevels_isEndpointLevelVector_of_feasible_gap
    {n innerSteps : ℕ} (hn : 0 < n) (sampleRate : Fin (n + 2) → ℝ)
    (tFirst target lastLow : ℝ)
    (hfirst_pos :
      0 <
        theorem32WeightedBackwardLowBisectionLevels
          n innerSteps sampleRate tFirst target lastLow
          (adjacentHighIndex (firstAdjacentIndex : Fin (n + 1))))
    (hlastLow_lt_one : lastLow < 1)
    (hfeasible :
      let returned :=
        theorem32WeightedBackwardLowBisectionLevels
          n innerSteps sampleRate tFirst target lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        WeightedBernoulliLowEndpointTargetFeasible
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          tFirst
          (returned (adjacentHighIndex i)) target)
    (hgap :
      let returned :=
        theorem32WeightedBackwardLowBisectionLevels
          n innerSteps sampleRate tFirst target lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        (returned (adjacentHighIndex i) - 0) /
            (2 : ℝ) ^ innerSteps <
          returned (adjacentHighIndex i) - root i) :
    BinaryEndpointLevelVector
      (theorem32WeightedBackwardLowBisectionLevels
        n innerSteps sampleRate tFirst target lastLow) := by
  let returned :=
    theorem32WeightedBackwardLowBisectionLevels
      n innerSteps sampleRate tFirst target lastLow
  refine ⟨?_, ?_, ?_⟩
  · simp [theorem32WeightedBackwardLowBisectionLevels]
  · simpa [returned] using
      theorem32WeightedBackwardLowBisectionLevels_last
        n innerSteps sampleRate tFirst target lastLow
  · intro i
    by_cases hfirst : i.val = 0
    · have hi : i = (firstAdjacentIndex : Fin (n + 1)) := by
        ext
        simpa [firstAdjacentIndex] using hfirst
      subst i
      have hlow :
          returned
              (adjacentLowIndex (firstAdjacentIndex : Fin (n + 1))) = 0 := by
        simp [returned, theorem32WeightedBackwardLowBisectionLevels,
          adjacentLowIndex, firstAdjacentIndex]
      simpa [returned, hlow] using hfirst_pos
    · by_cases hlast : i.val = n
      · have hi : i = (lastAdjacentIndex : Fin (n + 1)) := by
          ext
          simpa [lastAdjacentIndex] using hlast
        subst i
        have hlow :
            returned
                (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) =
              lastLow := by
          simpa [returned] using
            theorem32WeightedBackwardLowBisectionLevels_last_low
              (n := n) (innerSteps := innerSteps) hn
              sampleRate tFirst target lastLow
        have hhigh :
            returned
                (adjacentHighIndex (lastAdjacentIndex : Fin (n + 1))) =
              1 := by
          simpa [returned, adjacentHighIndex, lastAdjacentIndex, lastLevelIndex] using
            theorem32WeightedBackwardLowBisectionLevels_last
              n innerSteps sampleRate tFirst target lastLow
        change
          returned (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) <
            returned (adjacentHighIndex (lastAdjacentIndex : Fin (n + 1)))
        rw [hlow, hhigh]
        exact hlastLow_lt_one
      · simpa [returned] using
          theorem32WeightedBackwardLowBisectionLevels_interior_adjacent_strict_of_feasible_gap
            (n := n) (innerSteps := innerSteps)
            sampleRate tFirst target lastLow hfeasible hgap i hfirst hlast

/--
Endpoint-vector constructor for the weighted backward recursion with the first
positive endpoint derived from feasibility.
-/
theorem theorem32WeightedBackwardLowBisectionLevels_isEndpointLevelVector_of_feasible_gap_auto_first
    {n innerSteps : ℕ} (hn : 1 < n) (sampleRate : Fin (n + 2) → ℝ)
    (tFirst target lastLow : ℝ)
    (hlastLow_lt_one : lastLow < 1)
    (hfeasible :
      let returned :=
        theorem32WeightedBackwardLowBisectionLevels
          n innerSteps sampleRate tFirst target lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        WeightedBernoulliLowEndpointTargetFeasible
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          tFirst
          (returned (adjacentHighIndex i)) target)
    (hgap :
      let returned :=
        theorem32WeightedBackwardLowBisectionLevels
          n innerSteps sampleRate tFirst target lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        (returned (adjacentHighIndex i) - 0) /
            (2 : ℝ) ^ innerSteps <
          returned (adjacentHighIndex i) - root i) :
    BinaryEndpointLevelVector
      (theorem32WeightedBackwardLowBisectionLevels
        n innerSteps sampleRate tFirst target lastLow) :=
  theorem32WeightedBackwardLowBisectionLevels_isEndpointLevelVector_of_feasible_gap
    (n := n) (innerSteps := innerSteps) (Nat.lt_of_succ_lt hn)
    sampleRate tFirst target lastLow
    (theorem32WeightedBackwardLowBisectionLevels_first_high_pos_of_feasible
      (n := n) (innerSteps := innerSteps) hn sampleRate tFirst target lastLow
      hfeasible)
    hlastLow_lt_one hfeasible hgap

/--
Weighted monotone Theorem 3.2 executable-run wrapper.  It converts a sound
weighted outer bisection run and interior low-endpoint bisection runs into the
bracket/root facts consumed by
`...monotone_equalized_width_minimal_bracket_run`.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_monotone_equalized_width_minimal_weighted_runs
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (optimal returned sampleRate : Fin (m + 2) → ℝ)
    {rStar gLast delta eps lower0 upper0 : ℝ}
    (candidate : ℝ → Fin (m + 2) → ℝ)
    (hgLast_pos : 0 < gLast)
    (heps : 0 ≤ eps)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (hreturned_levels : BinaryEndpointLevelVector returned)
    (heq : BinaryEndpointAwareAdjacentRatesEqualize optimal sampleRate)
    (hsample_pos : ∀ idx : Fin (m + 2), 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hfirst_sample :
      sampleRate (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) = 1)
    (hgLast :
      sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) =
        gLast)
    (hlast_width :
      ∀ i : Fin (m + 1),
        optimal (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
            optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
          optimal (adjacentHighIndex i) - optimal (adjacentLowIndex i))
    (hdelta :
      delta =
        eps /
          (gLast *
            ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ +
              (((1 / ((m + 1 : ℕ) : ℝ)) ^ 2) / 2)⁻¹)))
    (hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal sampleRate i = rStar)
    (hfirstRate :
      binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)) ≤
        binaryEndpointAwareAdjacentRate returned sampleRate
          (firstAdjacentIndex : Fin (m + 1)))
    (habove :
      ∀ x,
        theorem32OuterSourceWeightedRateAbove (candidate x) sampleRate = true →
          optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤ x)
    (hbelow :
      ∀ x,
        theorem32OuterSourceWeightedRateAbove (candidate x) sampleRate = false →
          x ≤ optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
    (hlower0 :
      lower0 ≤ optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
    (hupper0 :
      optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤ upper0)
    (houterWidth : (upper0 - lower0) / (2 : ℝ) ^ outerSteps ≤ delta)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (fun x => theorem32OuterSourceWeightedRateAbove (candidate x) sampleRate)
          outerSteps lower0 upper0).2 =
        returned (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
    (root lowerInner upperInner : Fin (m + 1) → ℝ)
    (hroot_def :
      root =
        fun i : Fin (m + 1) =>
          weightedBernoulliLowEndpointOfRateOrFloor
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
            (returned (adjacentHighIndex i))
            (binaryEndpointAwareAdjacentRate returned sampleRate
              (lastAdjacentIndex : Fin (m + 1))))
    (hfeasible :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        WeightedBernoulliLowEndpointTargetFeasible
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          (optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
          (returned (adjacentHighIndex i))
          (binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1))))
    (hinnerLower0 :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        lowerInner i ≤ root i)
    (hinnerUpper0 :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        root i ≤ upperInner i)
    (hinnerWidth :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        (upperInner i - lowerInner i) / (2 : ℝ) ^ innerSteps ≤ delta)
    (hreturnedLow :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps (lowerInner i) (upperInner i)).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
        binaryEndpointAwareAdjacentRateObjective returned sampleRate ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  have hlastBracket :
      EconCSLib.Optimization.RealBisectionBracket
        (optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
        (EconCSLib.Optimization.realBisectionRun
          (fun x => theorem32OuterSourceWeightedRateAbove (candidate x) sampleRate)
          outerSteps lower0 upper0).1
        (returned (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
        delta :=
    theorem32_monotone_last_low_bracket_of_weighted_outer_run
      optimal returned sampleRate candidate habove hbelow hlower0 hupper0
      houterWidth hreturnedLast
  have hrootFacts :=
    theorem32_monotone_inner_low_bisection_root_facts_of_feasible
      returned sampleRate
      (tFirst :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
      (target :=
        binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)))
      root hroot_def hfeasible
  have hbracket :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        EconCSLib.Optimization.RealBisectionBracket
          (root i)
          (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget (root i))
            innerSteps (lowerInner i) (upperInner i)).1
          (returned (adjacentLowIndex i))
          delta :=
    theorem32_monotone_inner_low_bisection_brackets_of_runs
      returned sampleRate root lowerInner upperInner hinnerLower0
      hinnerUpper0 hinnerWidth hreturnedLow
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_monotone_equalized_width_minimal_bracket_run
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm optimal returned sampleRate
      (rStar := rStar) (gLast := gLast)
      (delta := delta) (eps := eps)
      (lastBracketLower :=
        (EconCSLib.Optimization.realBisectionRun
          (fun x => theorem32OuterSourceWeightedRateAbove (candidate x) sampleRate)
          outerSteps lower0 upper0).1)
      hgLast_pos heps hoptimal_levels hreturned_levels heq hsample_pos
      hsample_mono hfirst_sample hgLast hlast_width hdelta hoptimal
      hfirstRate hlastBracket root
      (fun i =>
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps (lowerInner i) (upperInner i)).1)
      hrootFacts.1 hrootFacts.2.1 hrootFacts.2.2 hbracket houter hinner

/--
Weighted monotone Theorem 3.2 executable-run wrapper specialized to the
backward `CalculateOtherLevels` recursion.  Compared with
`...weighted_runs`, this theorem no longer asks for a certificate that the
inner bisection outputs agree with the returned levels: that equality is proved
from the recursion.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_monotone_equalized_width_minimal_weighted_backward_runs
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (optimal sampleRate : Fin (m + 2) → ℝ)
    {rStar gLast delta eps lower0 upper0 lastLow : ℝ}
    (candidate : ℝ → Fin (m + 2) → ℝ)
    (hgLast_pos : 0 < gLast)
    (heps : 0 ≤ eps)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (hreturned_levels :
      let tFirst : ℝ :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
      let target : ℝ :=
        sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
          (-Real.log lastLow)
      BinaryEndpointLevelVector
        (theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst target lastLow))
    (heq : BinaryEndpointAwareAdjacentRatesEqualize optimal sampleRate)
    (hsample_pos : ∀ idx : Fin (m + 2), 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hfirst_sample :
      sampleRate (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) = 1)
    (hgLast :
      sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) =
        gLast)
    (hlast_width :
      ∀ i : Fin (m + 1),
        optimal (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
            optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
          optimal (adjacentHighIndex i) - optimal (adjacentLowIndex i))
    (hdelta :
      delta =
        eps /
          (gLast *
            ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ +
              (((1 / ((m + 1 : ℕ) : ℝ)) ^ 2) / 2)⁻¹)))
    (hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal sampleRate i = rStar)
    (hfirstRate :
      let tFirst : ℝ :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
      let target : ℝ :=
        sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
          (-Real.log lastLow)
      let returned :=
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst target lastLow
      binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)) ≤
        binaryEndpointAwareAdjacentRate returned sampleRate
          (firstAdjacentIndex : Fin (m + 1)))
    (habove :
      ∀ x,
        theorem32OuterSourceWeightedRateAbove (candidate x) sampleRate = true →
          optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤ x)
    (hbelow :
      ∀ x,
        theorem32OuterSourceWeightedRateAbove (candidate x) sampleRate = false →
          x ≤ optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
    (hlower0 :
      lower0 ≤ optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
    (hupper0 :
      optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤ upper0)
    (houterWidth : (upper0 - lower0) / (2 : ℝ) ^ outerSteps ≤ delta)
    (houterRunLast :
      (EconCSLib.Optimization.realBisectionRun
          (fun x => theorem32OuterSourceWeightedRateAbove (candidate x) sampleRate)
          outerSteps lower0 upper0).2 = lastLow)
    (hfeasible :
      let tFirst : ℝ :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
      let target : ℝ :=
        sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
          (-Real.log lastLow)
      let returned :=
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst target lastLow
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        WeightedBernoulliLowEndpointTargetFeasible
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          tFirst
          (returned (adjacentHighIndex i))
          (binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1))))
    (hinnerWidth :
      let tFirst : ℝ :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
      let target : ℝ :=
        sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
          (-Real.log lastLow)
      let returned :=
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst target lastLow
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        (returned (adjacentHighIndex i) - 0) / (2 : ℝ) ^ innerSteps ≤
          delta)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
    let target : ℝ :=
      sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
        (-Real.log lastLow)
    let returned :=
      theorem32WeightedBackwardLowBisectionLevels
        m innerSteps sampleRate tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
        binaryEndpointAwareAdjacentRateObjective returned sampleRate ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
  let target : ℝ :=
    sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
      (-Real.log lastLow)
  let returned :=
    theorem32WeightedBackwardLowBisectionLevels
      m innerSteps sampleRate tFirst target lastLow
  let root : Fin (m + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (sampleRate (adjacentHighIndex i))
      (sampleRate (adjacentLowIndex i))
      tFirst
      (returned (adjacentHighIndex i))
      (binaryEndpointAwareAdjacentRate returned sampleRate
        (lastAdjacentIndex : Fin (m + 1)))
  have hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (fun x => theorem32OuterSourceWeightedRateAbove (candidate x) sampleRate)
          outerSteps lower0 upper0).2 =
        returned (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) := by
    have hlast_low :
        returned (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) =
          lastLow := by
      simpa [returned, target, tFirst] using
        theorem32WeightedBackwardLowBisectionLevels_last_low
          (n := m) (innerSteps := innerSteps) hm sampleRate tFirst target lastLow
    have hlast_low' :
        returned ⟨m, by omega⟩ = lastLow := by
      simpa [adjacentLowIndex, lastAdjacentIndex] using hlast_low
    exact houterRunLast.trans hlast_low'.symm
  have hroot_def :
      root =
        fun i : Fin (m + 1) =>
          weightedBernoulliLowEndpointOfRateOrFloor
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
            (returned (adjacentHighIndex i))
            (binaryEndpointAwareAdjacentRate returned sampleRate
              (lastAdjacentIndex : Fin (m + 1))) := by
    ext i
    simp [root, tFirst]
  have hinnerLower0 :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        (fun _ : Fin (m + 1) => (0 : ℝ)) i ≤ root i := by
    intro i hi_first hi_last
    have hmem :
        root i ∈ Set.Ioo tFirst (returned (adjacentHighIndex i)) := by
      simpa [root, returned, target, tFirst] using
        weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
          (hfeasible i hi_first hi_last)
    exact le_of_lt ((hfeasible i hi_first hi_last).hfloor0.trans hmem.1)
  have hinnerUpper0 :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        root i ≤ (fun i : Fin (m + 1) => returned (adjacentHighIndex i)) i := by
    intro i hi_first hi_last
    have hmem :
        root i ∈ Set.Ioo tFirst (returned (adjacentHighIndex i)) := by
      simpa [root, returned, target, tFirst] using
        weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
          (hfeasible i hi_first hi_last)
    exact le_of_lt hmem.2
  have hreturnedLow :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps ((fun _ : Fin (m + 1) => (0 : ℝ)) i)
            ((fun i : Fin (m + 1) => returned (adjacentHighIndex i)) i)).2 =
          returned (adjacentLowIndex i) := by
    intro i hi_first hi_last
    simpa [root, returned, target, tFirst] using
      theorem32WeightedBackwardLowBisectionLevels_returnedLow_last_rate
        (n := m) (innerSteps := innerSteps) hm sampleRate tFirst lastLow
        i hi_first hi_last
  simpa [returned, target, tFirst] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_monotone_equalized_width_minimal_weighted_runs
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm optimal returned sampleRate
      (rStar := rStar) (gLast := gLast)
      (delta := delta) (eps := eps)
      (lower0 := lower0) (upper0 := upper0)
      candidate hgLast_pos heps hoptimal_levels
      (by simpa [returned, target, tFirst] using hreturned_levels)
      heq hsample_pos hsample_mono hfirst_sample hgLast hlast_width hdelta
      hoptimal (by simpa [returned, target, tFirst] using hfirstRate)
      habove hbelow hlower0 hupper0 houterWidth hreturnedLast
      root (fun _ : Fin (m + 1) => (0 : ℝ))
      (fun i : Fin (m + 1) => returned (adjacentHighIndex i))
      hroot_def
      (by
        intro i hi_first hi_last
        simpa [returned, target, tFirst] using hfeasible i hi_first hi_last)
      hinnerLower0 hinnerUpper0
      (by
        intro i hi_first hi_last
        simpa [returned, target, tFirst] using hinnerWidth i hi_first hi_last)
      hreturnedLow houter hinner

/--
Weighted monotone Theorem 3.2 wrapper for the executable outer run and backward
inner recursion.  The final `rate_last <= rate_first` condition and the
returned outer endpoint are derived from the actual bisection run.  The inner
low-endpoint feasibility certificate is reduced to the source's floor/high and
floor-rate inequalities, and a single global inner-width bound supplies all
per-interval bisection width bounds.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_monotone_equalized_width_minimal_weighted_source_outer_run
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (optimal sampleRate : Fin (m + 2) → ℝ)
    {rStar gLast delta eps lower0 upper0 : ℝ}
    (hgLast_pos : 0 < gLast)
    (heps : 0 ≤ eps)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (hreturned_levels :
      let tFirst : ℝ :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
      let candidate : ℝ → Fin (m + 2) → ℝ := fun x =>
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst
          (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
            (-Real.log x))
          x
      let lastLow : ℝ :=
        (EconCSLib.Optimization.realBisectionRun
          (fun x => theorem32OuterSourceWeightedRateAbove
            (candidate x) sampleRate)
          outerSteps lower0 upper0).2
      let target : ℝ :=
        sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
          (-Real.log lastLow)
      let returned :=
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst target lastLow
      BinaryEndpointLevelVector returned)
    (heq : BinaryEndpointAwareAdjacentRatesEqualize optimal sampleRate)
    (hsample_pos : ∀ idx : Fin (m + 2), 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hfirst_sample :
      sampleRate (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) = 1)
    (hgLast :
      sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) =
        gLast)
    (hlast_width :
      ∀ i : Fin (m + 1),
        optimal (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
            optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
          optimal (adjacentHighIndex i) - optimal (adjacentLowIndex i))
    (hdelta :
      delta =
        eps /
          (gLast *
            ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ +
              (((1 / ((m + 1 : ℕ) : ℝ)) ^ 2) / 2)⁻¹)))
    (hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal sampleRate i = rStar)
    (hupperAbove :
      let tFirst : ℝ :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
      let candidate : ℝ → Fin (m + 2) → ℝ := fun x =>
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst
          (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
            (-Real.log x))
          x
      theorem32OuterSourceWeightedRateAbove (candidate upper0) sampleRate =
        true)
    (hsourceAbove :
      let tFirst : ℝ :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
      let candidate : ℝ → Fin (m + 2) → ℝ := fun x =>
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst
          (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
            (-Real.log x))
          x
      ∀ x,
        binaryEndpointAwareAdjacentRate (candidate x) sampleRate
            (lastAdjacentIndex : Fin (m + 1)) ≤
          binaryEndpointAwareAdjacentRate (candidate x) sampleRate
            (firstAdjacentIndex : Fin (m + 1)) →
        optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤ x)
    (hsourceBelow :
      let tFirst : ℝ :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
      let candidate : ℝ → Fin (m + 2) → ℝ := fun x =>
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst
          (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
            (-Real.log x))
          x
      ∀ x,
        binaryEndpointAwareAdjacentRate (candidate x) sampleRate
            (firstAdjacentIndex : Fin (m + 1)) <
          binaryEndpointAwareAdjacentRate (candidate x) sampleRate
            (lastAdjacentIndex : Fin (m + 1)) →
        x ≤ optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
    (hlower0 :
      lower0 ≤ optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
    (hupper0 :
      optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤ upper0)
    (houterWidth : (upper0 - lower0) / (2 : ℝ) ^ outerSteps ≤ delta)
    (hfloor_lt_high :
      let tFirst : ℝ :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
      let candidate : ℝ → Fin (m + 2) → ℝ := fun x =>
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst
          (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
            (-Real.log x))
          x
      let lastLow : ℝ :=
        (EconCSLib.Optimization.realBisectionRun
          (fun x => theorem32OuterSourceWeightedRateAbove
            (candidate x) sampleRate)
          outerSteps lower0 upper0).2
      let target : ℝ :=
        sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
          (-Real.log lastLow)
      let returned :=
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst target lastLow
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        tFirst < returned (adjacentHighIndex i))
    (htarget_lt_floor_rate :
      let tFirst : ℝ :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
      let candidate : ℝ → Fin (m + 2) → ℝ := fun x =>
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst
          (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
            (-Real.log x))
          x
      let lastLow : ℝ :=
        (EconCSLib.Optimization.realBisectionRun
          (fun x => theorem32OuterSourceWeightedRateAbove
            (candidate x) sampleRate)
          outerSteps lower0 upper0).2
      let target : ℝ :=
        sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
          (-Real.log lastLow)
      let returned :=
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst target lastLow
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1)) <
          weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (returned (adjacentHighIndex i)) tFirst)
    (hinnerUnitWidth :
      (1 : ℝ) / (2 : ℝ) ^ innerSteps ≤ delta)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
    let candidate : ℝ → Fin (m + 2) → ℝ := fun x =>
      theorem32WeightedBackwardLowBisectionLevels
        m innerSteps sampleRate tFirst
        (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
          (-Real.log x))
        x
    let lastLow : ℝ :=
      (EconCSLib.Optimization.realBisectionRun
        (fun x => theorem32OuterSourceWeightedRateAbove
          (candidate x) sampleRate)
        outerSteps lower0 upper0).2
    let target : ℝ :=
      sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
        (-Real.log lastLow)
    let returned :=
      theorem32WeightedBackwardLowBisectionLevels
        m innerSteps sampleRate tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
        binaryEndpointAwareAdjacentRateObjective returned sampleRate ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
  let candidate : ℝ → Fin (m + 2) → ℝ := fun x =>
    theorem32WeightedBackwardLowBisectionLevels
      m innerSteps sampleRate tFirst
      (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
        (-Real.log x))
      x
  let above : ℝ → Bool := fun x =>
    theorem32OuterSourceWeightedRateAbove (candidate x) sampleRate
  let lastLow : ℝ :=
    (EconCSLib.Optimization.realBisectionRun
      above outerSteps lower0 upper0).2
  let target : ℝ :=
    sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
      (-Real.log lastLow)
  let returned :=
    theorem32WeightedBackwardLowBisectionLevels
      m innerSteps sampleRate tFirst target lastLow
  have hreturnedLevels : BinaryEndpointLevelVector returned := by
    simpa [returned, target, lastLow, above, candidate, tFirst] using
      hreturned_levels
  have hfirstRate :
      binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)) ≤
        binaryEndpointAwareAdjacentRate returned sampleRate
          (firstAdjacentIndex : Fin (m + 1)) := by
    have hupperAbove' : above upper0 = true := by
      simpa [above, candidate, tFirst] using hupperAbove
    have hrunAbove :
        above
            (EconCSLib.Optimization.realBisectionRun
              above outerSteps lower0 upper0).2 = true :=
      theorem32_realBisectionRun_upper_true_of_upper_true
        above hupperAbove'
    have hreturnedAbove :
        theorem32OuterSourceWeightedRateAbove returned sampleRate = true := by
      simpa [returned, target, lastLow, above, candidate, tFirst] using hrunAbove
    exact
      (theorem32OuterSourceWeightedRateAbove_eq_true_iff
        returned sampleRate).mp hreturnedAbove
  have habove :
      ∀ x,
        theorem32OuterSourceWeightedRateAbove (candidate x) sampleRate = true →
          optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤ x := by
    exact
      theorem32OuterSourceWeightedRateAbove_true_sound
        sampleRate candidate
        (by
          intro x hx
          exact hsourceAbove x hx)
  have hbelow :
      ∀ x,
        theorem32OuterSourceWeightedRateAbove (candidate x) sampleRate = false →
          x ≤ optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) := by
    exact
      theorem32OuterSourceWeightedRateAbove_false_sound
        sampleRate candidate
        (by
          intro x hx
          exact hsourceBelow x hx)
  have hfeasible :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        WeightedBernoulliLowEndpointTargetFeasible
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          tFirst
          (returned (adjacentHighIndex i))
          (binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1))) := by
    exact
      theorem32_monotone_inner_lowEndpointTargetFeasible_of_floor_lt_high_and_target_lt_floor_rate
        (m := m) hm optimal returned sampleRate hoptimal_levels
        hreturnedLevels hsample_pos
        (by
          intro i hi_first hi_last
          simpa [returned, target, lastLow, above, candidate, tFirst] using
            hfloor_lt_high i hi_first hi_last)
        (by
          intro i hi_first hi_last
          simpa [returned, target, lastLow, above, candidate, tFirst] using
            htarget_lt_floor_rate i hi_first hi_last)
  have hinnerWidth :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        (returned (adjacentHighIndex i) - 0) / (2 : ℝ) ^ innerSteps ≤
          delta := by
    intro i _hi_first _hi_last
    have hhigh_le_one :
        returned (adjacentHighIndex i) ≤ 1 :=
      BinaryEndpointLevelVector_le_one hreturnedLevels (adjacentHighIndex i)
    have hnum :
        returned (adjacentHighIndex i) - 0 ≤ 1 := by
      linarith
    have hden_nonneg : 0 ≤ (2 : ℝ) ^ innerSteps :=
      pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) innerSteps
    exact
      (div_le_div_of_nonneg_right hnum hden_nonneg).trans hinnerUnitWidth
  simpa [returned, target, lastLow, above, candidate, tFirst] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_monotone_equalized_width_minimal_weighted_backward_runs
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm optimal sampleRate
      (rStar := rStar) (gLast := gLast)
      (delta := delta) (eps := eps)
      (lower0 := lower0) (upper0 := upper0)
      (lastLow := lastLow)
      candidate hgLast_pos heps hoptimal_levels hreturnedLevels heq
      hsample_pos hsample_mono hfirst_sample hgLast hlast_width hdelta
      hoptimal hfirstRate habove hbelow hlower0 hupper0 houterWidth
      (by rfl) hfeasible hinnerWidth houter hinner

/--
Executable weighted outer-run wrapper with the returned endpoint-vector
certificate derived from primitive inner-loop bounds and the source bisection
gap condition.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_monotone_equalized_width_minimal_weighted_source_outer_run_of_raw_inner_bounds
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (optimal sampleRate : Fin (m + 2) → ℝ)
    {rStar gLast delta eps lower0 upper0 : ℝ}
    (hgLast_pos : 0 < gLast)
    (heps : 0 ≤ eps)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (heq : BinaryEndpointAwareAdjacentRatesEqualize optimal sampleRate)
    (hsample_pos : ∀ idx : Fin (m + 2), 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hfirst_sample :
      sampleRate (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) = 1)
    (hgLast :
      sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) =
        gLast)
    (hlast_width :
      ∀ i : Fin (m + 1),
        optimal (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
            optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
          optimal (adjacentHighIndex i) - optimal (adjacentLowIndex i))
    (hdelta :
      delta =
        eps /
          (gLast *
            ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ +
              (((1 / ((m + 1 : ℕ) : ℝ)) ^ 2) / 2)⁻¹)))
    (hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal sampleRate i = rStar)
    (hupperAbove :
      let tFirst : ℝ :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
      let candidate : ℝ → Fin (m + 2) → ℝ := fun x =>
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst
          (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
            (-Real.log x))
          x
      theorem32OuterSourceWeightedRateAbove (candidate upper0) sampleRate =
        true)
    (hsourceAbove :
      let tFirst : ℝ :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
      let candidate : ℝ → Fin (m + 2) → ℝ := fun x =>
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst
          (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
            (-Real.log x))
          x
      ∀ x,
        binaryEndpointAwareAdjacentRate (candidate x) sampleRate
            (lastAdjacentIndex : Fin (m + 1)) ≤
          binaryEndpointAwareAdjacentRate (candidate x) sampleRate
            (firstAdjacentIndex : Fin (m + 1)) →
        optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤ x)
    (hsourceBelow :
      let tFirst : ℝ :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
      let candidate : ℝ → Fin (m + 2) → ℝ := fun x =>
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst
          (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
            (-Real.log x))
          x
      ∀ x,
        binaryEndpointAwareAdjacentRate (candidate x) sampleRate
            (firstAdjacentIndex : Fin (m + 1)) <
          binaryEndpointAwareAdjacentRate (candidate x) sampleRate
            (lastAdjacentIndex : Fin (m + 1)) →
        x ≤ optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
    (hlower0 :
      lower0 ≤ optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
    (hupper0 :
      optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤ upper0)
    (houterWidth : (upper0 - lower0) / (2 : ℝ) ^ outerSteps ≤ delta)
    (hfirst_pos :
      let tFirst : ℝ :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
      let candidate : ℝ → Fin (m + 2) → ℝ := fun x =>
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst
          (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
            (-Real.log x))
          x
      let lastLow : ℝ :=
        (EconCSLib.Optimization.realBisectionRun
          (fun x => theorem32OuterSourceWeightedRateAbove
            (candidate x) sampleRate)
          outerSteps lower0 upper0).2
      let target : ℝ :=
        sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
          (-Real.log lastLow)
      let returned :=
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst target lastLow
      0 < returned (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (hlastLow_pos :
      let tFirst : ℝ :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
      let candidate : ℝ → Fin (m + 2) → ℝ := fun x =>
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst
          (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
            (-Real.log x))
          x
      let lastLow : ℝ :=
        (EconCSLib.Optimization.realBisectionRun
          (fun x => theorem32OuterSourceWeightedRateAbove
            (candidate x) sampleRate)
          outerSteps lower0 upper0).2
      0 < lastLow)
    (hlastLow_lt_one :
      let tFirst : ℝ :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
      let candidate : ℝ → Fin (m + 2) → ℝ := fun x =>
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst
          (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
            (-Real.log x))
          x
      let lastLow : ℝ :=
        (EconCSLib.Optimization.realBisectionRun
          (fun x => theorem32OuterSourceWeightedRateAbove
            (candidate x) sampleRate)
          outerSteps lower0 upper0).2
      lastLow < 1)
    (hhigh_lt_one :
      let tFirst : ℝ :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
      let candidate : ℝ → Fin (m + 2) → ℝ := fun x =>
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst
          (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
            (-Real.log x))
          x
      let lastLow : ℝ :=
        (EconCSLib.Optimization.realBisectionRun
          (fun x => theorem32OuterSourceWeightedRateAbove
            (candidate x) sampleRate)
          outerSteps lower0 upper0).2
      let target : ℝ :=
        sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
          (-Real.log lastLow)
      let returned :=
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst target lastLow
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        returned (adjacentHighIndex i) < 1)
    (hfloor_lt_high :
      let tFirst : ℝ :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
      let candidate : ℝ → Fin (m + 2) → ℝ := fun x =>
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst
          (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
            (-Real.log x))
          x
      let lastLow : ℝ :=
        (EconCSLib.Optimization.realBisectionRun
          (fun x => theorem32OuterSourceWeightedRateAbove
            (candidate x) sampleRate)
          outerSteps lower0 upper0).2
      let target : ℝ :=
        sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
          (-Real.log lastLow)
      let returned :=
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst target lastLow
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        tFirst < returned (adjacentHighIndex i))
    (htarget_lt_floor_rate :
      let tFirst : ℝ :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
      let candidate : ℝ → Fin (m + 2) → ℝ := fun x =>
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst
          (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
            (-Real.log x))
          x
      let lastLow : ℝ :=
        (EconCSLib.Optimization.realBisectionRun
          (fun x => theorem32OuterSourceWeightedRateAbove
            (candidate x) sampleRate)
          outerSteps lower0 upper0).2
      let target : ℝ :=
        sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
          (-Real.log lastLow)
      let returned :=
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst target lastLow
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        target <
          weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (returned (adjacentHighIndex i)) tFirst)
    (hgap :
      let tFirst : ℝ :=
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
      let candidate : ℝ → Fin (m + 2) → ℝ := fun x =>
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst
          (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
            (-Real.log x))
          x
      let lastLow : ℝ :=
        (EconCSLib.Optimization.realBisectionRun
          (fun x => theorem32OuterSourceWeightedRateAbove
            (candidate x) sampleRate)
          outerSteps lower0 upper0).2
      let target : ℝ :=
        sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
          (-Real.log lastLow)
      let returned :=
        theorem32WeightedBackwardLowBisectionLevels
          m innerSteps sampleRate tFirst target lastLow
      let root : Fin (m + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        (returned (adjacentHighIndex i) - 0) /
            (2 : ℝ) ^ innerSteps <
          returned (adjacentHighIndex i) - root i)
    (hinnerUnitWidth :
      (1 : ℝ) / (2 : ℝ) ^ innerSteps ≤ delta)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
    let candidate : ℝ → Fin (m + 2) → ℝ := fun x =>
      theorem32WeightedBackwardLowBisectionLevels
        m innerSteps sampleRate tFirst
        (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
          (-Real.log x))
        x
    let lastLow : ℝ :=
      (EconCSLib.Optimization.realBisectionRun
        (fun x => theorem32OuterSourceWeightedRateAbove
          (candidate x) sampleRate)
        outerSteps lower0 upper0).2
    let target : ℝ :=
      sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
        (-Real.log lastLow)
    let returned :=
      theorem32WeightedBackwardLowBisectionLevels
        m innerSteps sampleRate tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective optimal sampleRate -
        binaryEndpointAwareAdjacentRateObjective returned sampleRate ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))
  let candidate : ℝ → Fin (m + 2) → ℝ := fun x =>
    theorem32WeightedBackwardLowBisectionLevels
      m innerSteps sampleRate tFirst
      (sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
        (-Real.log x))
      x
  let above : ℝ → Bool := fun x =>
    theorem32OuterSourceWeightedRateAbove (candidate x) sampleRate
  let lastLow : ℝ :=
    (EconCSLib.Optimization.realBisectionRun
      above outerSteps lower0 upper0).2
  let target : ℝ :=
    sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) *
      (-Real.log lastLow)
  let returned :=
    theorem32WeightedBackwardLowBisectionLevels
      m innerSteps sampleRate tFirst target lastLow
  have htFirst0 : 0 < tFirst := by
    have hnot_first :
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))).val ≠ 0 := by
      simp [adjacentHighIndex, firstAdjacentIndex]
    simpa [tFirst] using
      BinaryEndpointLevelVector_pos_of_not_first hoptimal_levels
        (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))) hnot_first
  have htarget_pos : 0 < target := by
    have hlog_neg : Real.log lastLow < 0 := by
      exact Real.log_neg (by simpa [lastLow, above, candidate, tFirst] using hlastLow_pos)
        (by simpa [lastLow, above, candidate, tFirst] using hlastLow_lt_one)
    exact
      mul_pos
        (hsample_pos (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))))
        (neg_pos.mpr hlog_neg)
  have hfloor_lt_high_local :
      ∀ j : Fin (m + 1), j.val ≠ 0 → j.val ≠ m →
        tFirst < returned (adjacentHighIndex j) := by
    simpa [returned, target, lastLow, above, candidate, tFirst] using
      hfloor_lt_high
  have hhigh_lt_one_local :
      ∀ j : Fin (m + 1), j.val ≠ 0 → j.val ≠ m →
        returned (adjacentHighIndex j) < 1 := by
    simpa [returned, target, lastLow, above, candidate, tFirst] using
      hhigh_lt_one
  have htarget_lt_floor_rate_local :
      ∀ j : Fin (m + 1), j.val ≠ 0 → j.val ≠ m →
        target <
          weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex j))
            (sampleRate (adjacentLowIndex j))
            (returned (adjacentHighIndex j)) tFirst := by
    simpa [returned, target, lastLow, above, candidate, tFirst] using
      htarget_lt_floor_rate
  have hgap_local :
      let root : Fin (m + 1) → ℝ := fun j =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (sampleRate (adjacentHighIndex j))
          (sampleRate (adjacentLowIndex j))
          tFirst
          (returned (adjacentHighIndex j)) target
      ∀ j : Fin (m + 1), j.val ≠ 0 → j.val ≠ m →
        (returned (adjacentHighIndex j) - 0) /
            (2 : ℝ) ^ innerSteps <
          returned (adjacentHighIndex j) - root j := by
    simpa [returned, target, lastLow, above, candidate, tFirst] using hgap
  have hfeasible :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        WeightedBernoulliLowEndpointTargetFeasible
          (sampleRate (adjacentHighIndex i))
          (sampleRate (adjacentLowIndex i))
          tFirst
          (returned (adjacentHighIndex i)) target := by
    exact
      theorem32_monotone_inner_lowEndpointTargetFeasible_of_raw_bounds
        returned sampleRate hsample_pos htFirst0
        hfloor_lt_high_local hhigh_lt_one_local htarget_pos
        htarget_lt_floor_rate_local
  have hreturnedLevels : BinaryEndpointLevelVector returned := by
    simpa [returned, target, lastLow, above, candidate, tFirst] using
      theorem32WeightedBackwardLowBisectionLevels_isEndpointLevelVector_of_feasible_gap
        (n := m) (innerSteps := innerSteps) hm sampleRate tFirst target lastLow
        (by
          simpa [returned, target, lastLow, above, candidate, tFirst] using hfirst_pos)
        (by
          simpa [lastLow, above, candidate, tFirst] using hlastLow_lt_one)
        hfeasible
        (by simpa using hgap_local)
  have htarget_eq :
      binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)) =
        target := by
    simpa [returned, target, lastLow, above, candidate, tFirst] using
      theorem32WeightedBackwardLowBisectionLevels_last_rate
        (n := m) (innerSteps := innerSteps) hm sampleRate tFirst target lastLow
  simpa [returned, target, lastLow, above, candidate, tFirst] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_monotone_equalized_width_minimal_weighted_source_outer_run
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm optimal sampleRate
      (rStar := rStar) (gLast := gLast)
      (delta := delta) (eps := eps)
      (lower0 := lower0) (upper0 := upper0)
      hgLast_pos heps hoptimal_levels
      (by simpa [returned, target, lastLow, above, candidate, tFirst] using hreturnedLevels)
      heq hsample_pos hsample_mono hfirst_sample hgLast hlast_width hdelta
      hoptimal hupperAbove hsourceAbove hsourceBelow hlower0 hupper0
      houterWidth
      (by
        simpa [returned, target, lastLow, above, candidate, tFirst] using
          hfloor_lt_high_local)
      (by
        dsimp
        intro j hj_first hj_last
        change
          binaryEndpointAwareAdjacentRate returned sampleRate
              (lastAdjacentIndex : Fin (m + 1)) <
            weightedBernoulliClosedThresholdRate
              (sampleRate (adjacentHighIndex j))
              (sampleRate (adjacentLowIndex j))
              (returned (adjacentHighIndex j)) tFirst
        rw [htarget_eq]
        exact htarget_lt_floor_rate_local j hj_first hj_last)
      hinnerUnitWidth houter hinner

/--
Uniform-matching Theorem 3.2 approximation certificate.  Equalized optimal
uniform adjacent rates supply the Lemma C.6 last-level lower bound, so the
remaining explicit lower-bound input is the first-level lower bound from the
source's Corollary C.3-style argument.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_uniform_equalized
    {m : ℕ} (hm : 0 < m)
    (optimal returned : Fin (m + 2) → ℝ)
    {tFirstStar firstLower delta eps : ℝ}
    (heps : 0 ≤ eps)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hfirstLower_pos : 0 < firstLower)
    (hfirstLower : firstLower ≤ tFirstStar)
    (hdelta :
      delta =
        eps /
          ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ + firstLower⁻¹))
    (hlast :
      binaryEndpointAwareAdjacentRate optimal
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) -
          Real.log
            ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                  delta) /
              optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin (m + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ)) i) :
    binaryEndpointAwareAdjacentRateObjective optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin (m + 2) => (1 : ℝ)) ≤
      eps := by
  let uniform : Fin (m + 2) → ℝ := fun _ => (1 : ℝ)
  let rStar : ℝ :=
    binaryEndpointAwareAdjacentRate optimal uniform
      (lastAdjacentIndex : Fin (m + 1))
  have hlast_width :
      ∀ i : Fin (m + 1),
        optimal (adjacentHighIndex (lastAdjacentIndex : Fin (m + 1))) -
            optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) ≤
          optimal (adjacentHighIndex i) - optimal (adjacentLowIndex i) :=
    BinaryEndpointAwareAdjacentRatesEqualize_uniform_last_width_le_all
      hm hoptimal_levels (by simpa [uniform] using heq)
  have hdelta' :
      delta =
        eps /
          ((1 : ℝ) *
            ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ + firstLower⁻¹)) := by
    simpa [one_mul] using hdelta
  have hoptimal :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate optimal uniform i = rStar := by
    intro i
    dsimp [rStar]
    exact heq i (lastAdjacentIndex : Fin (m + 1))
  have hlast' :
      rStar -
          (1 : ℝ) *
            Real.log
              ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                    delta) /
                optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned uniform
          (lastAdjacentIndex : Fin (m + 1)) := by
    simpa [rStar, uniform] using hlast
  have hgrid' :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned uniform
            (lastAdjacentIndex : Fin (m + 1)) -
            (1 : ℝ) * Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned uniform i := by
    intro i
    simpa [uniform] using hgrid i
  simpa [uniform] using
    binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_width_minimal
      hm optimal returned uniform
      (rStar := rStar) (gLast := (1 : ℝ))
      (tFirstStar := tFirstStar) (firstLower := firstLower)
      (delta := delta) (eps := eps)
      (by norm_num) heps hoptimal_levels hlast_width
      hfirstLower_pos hfirstLower hdelta' hoptimal hlast' hgrid'

/--
Uniform-matching Theorem 3.2 run certificate with the Lemma C.6 last-level
lower bound derived from equalized uniform optimal rates.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_uniform_equalized_run
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (optimal returned : Fin (m + 2) → ℝ)
    {tFirstStar firstLower delta eps : ℝ}
    (heps : 0 ≤ eps)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hfirstLower_pos : 0 < firstLower)
    (hfirstLower : firstLower ≤ tFirstStar)
    (hdelta :
      delta =
        eps /
          ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ + firstLower⁻¹))
    (hlast :
      binaryEndpointAwareAdjacentRate optimal
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) -
          Real.log
            ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                  delta) /
              optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin (m + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ)) i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin (m + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  constructor
  · exact
      binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_uniform_equalized
        hm optimal returned heps hoptimal_levels heq hfirstLower_pos
        hfirstLower hdelta hlast hgrid
  · exact nestedBisectionOperationCount_le_stepBound houter hinner

/--
Uniform-matching Theorem 3.2 approximation certificate with the first-level
lower bound derived from a lower bound on the equalized optimal rate.  This is
the source role of Lemma C.7/C.8/Corollary C.3 abstracted as a rate-lower
certificate.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_uniform_equalized_rate_lower
    {m : ℕ} (hm : 0 < m)
    (optimal returned : Fin (m + 2) → ℝ)
    {rateLower tFirstStar delta eps : ℝ}
    (heps : 0 ≤ eps)
    (hrateLower_pos : 0 < rateLower)
    (hrateLower_le_one : rateLower ≤ 1)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (htFirstStar :
      tFirstStar =
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (hrateLower_le_last :
      rateLower ≤
        binaryEndpointAwareAdjacentRate optimal
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)))
    (hdelta :
      delta =
        eps /
          ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ + (rateLower / 2)⁻¹))
    (hlast :
      binaryEndpointAwareAdjacentRate optimal
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) -
          Real.log
            ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                  delta) /
              optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin (m + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ)) i) :
    binaryEndpointAwareAdjacentRateObjective optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin (m + 2) => (1 : ℝ)) ≤
      eps := by
  have hfirstLower_pos : 0 < rateLower / 2 := by positivity
  have hfirstLower :
      rateLower / 2 ≤ tFirstStar := by
    have hfirst :=
      BinaryEndpointLevelVector_uniform_first_level_ge_half_of_equalized_last_rate_lower
        hm hoptimal_levels heq hrateLower_pos.le hrateLower_le_one
        hrateLower_le_last
    simpa [htFirstStar] using hfirst
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_uniform_equalized
      hm optimal returned heps hoptimal_levels heq hfirstLower_pos
      hfirstLower hdelta hlast hgrid

/--
Uniform-matching Theorem 3.2 run certificate with the first-level lower bound
derived from a lower bound on the equalized optimal rate.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_uniform_equalized_rate_lower_run
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (optimal returned : Fin (m + 2) → ℝ)
    {rateLower tFirstStar delta eps : ℝ}
    (heps : 0 ≤ eps)
    (hrateLower_pos : 0 < rateLower)
    (hrateLower_le_one : rateLower ≤ 1)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (htFirstStar :
      tFirstStar =
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (hrateLower_le_last :
      rateLower ≤
        binaryEndpointAwareAdjacentRate optimal
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)))
    (hdelta :
      delta =
        eps /
          ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ + (rateLower / 2)⁻¹))
    (hlast :
      binaryEndpointAwareAdjacentRate optimal
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) -
          Real.log
            ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                  delta) /
              optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin (m + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ)) i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin (m + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  constructor
  · exact
      binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_uniform_equalized_rate_lower
        hm optimal returned heps hrateLower_pos hrateLower_le_one
        hoptimal_levels heq htFirstStar hrateLower_le_last hdelta hlast
        hgrid
  · exact nestedBisectionOperationCount_le_stepBound houter hinner

/--
Uniform-matching Theorem 3.2 approximation certificate with the first-level
lower bound derived from a lower bound on the optimal equalized objective.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_uniform_equalized_objective_rate_lower
    {m : ℕ} (hm : 0 < m)
    (optimal returned : Fin (m + 2) → ℝ)
    {rateLower tFirstStar delta eps : ℝ}
    (heps : 0 ≤ eps)
    (hrateLower_pos : 0 < rateLower)
    (hrateLower_le_one : rateLower ≤ 1)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (htFirstStar :
      tFirstStar =
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (hrateLower_le_objective :
      rateLower ≤
        binaryEndpointAwareAdjacentRateObjective optimal
          (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hdelta :
      delta =
        eps /
          ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ + (rateLower / 2)⁻¹))
    (hlast :
      binaryEndpointAwareAdjacentRate optimal
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) -
          Real.log
            ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                  delta) /
              optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin (m + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ)) i) :
    binaryEndpointAwareAdjacentRateObjective optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin (m + 2) => (1 : ℝ)) ≤
      eps := by
  have hobj :
      binaryEndpointAwareAdjacentRateObjective optimal
          (fun _ : Fin (m + 2) => (1 : ℝ)) =
        binaryEndpointAwareAdjacentRate optimal
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) :=
    binaryEndpointAwareAdjacentRateObjective_eq_rate_of_equalizes
      optimal (fun _ : Fin (m + 2) => (1 : ℝ)) heq
      (lastAdjacentIndex : Fin (m + 1))
  have hrateLower_le_last :
      rateLower ≤
        binaryEndpointAwareAdjacentRate optimal
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) := by
    simpa [hobj] using hrateLower_le_objective
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_uniform_equalized_rate_lower
      hm optimal returned heps hrateLower_pos hrateLower_le_one
      hoptimal_levels heq htFirstStar hrateLower_le_last hdelta hlast hgrid

/--
Uniform-matching Theorem 3.2 approximation certificate for the explicit C.5
doubled chain.  The lower bound on the doubled optimal objective is derived
from the old equalized chain by Lemma C.5/C.7.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_uniform_doubled_closed
    {m : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {tFirstStar delta eps : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlower_le_one :
      (1 / 5 : ℝ) *
          binaryEndpointAwareAdjacentRateObjective oldLevels
            (fun _ : Fin (m + 2) => (1 : ℝ)) ≤ 1)
    (htFirstStar :
      tFirstStar =
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hdelta :
      delta =
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hlast :
      binaryEndpointAwareAdjacentRate
          (uniformDoubledEndpointLevels oldLevels)
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
          Real.log
            ((uniformDoubledEndpointLevels oldLevels
                  (adjacentLowIndex
                    (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) +
                delta) /
              uniformDoubledEndpointLevels oldLevels
                (adjacentLowIndex
                  (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (hgrid :
      ∀ i : Fin ((2 * m + 1) + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤
      eps := by
  let newLevels : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let rateLower : ℝ :=
    (1 / 5 : ℝ) *
      binaryEndpointAwareAdjacentRateObjective oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))
  have hOldObj_pos :
      0 <
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ)) := by
    have hobj_eq :
        binaryEndpointAwareAdjacentRateObjective oldLevels
            (fun _ : Fin (m + 2) => (1 : ℝ)) =
          binaryEndpointAwareAdjacentRate oldLevels
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (firstAdjacentIndex : Fin (m + 1)) :=
      binaryEndpointAwareAdjacentRateObjective_eq_rate_of_equalizes
        oldLevels (fun _ : Fin (m + 2) => (1 : ℝ)) holdEq
        (firstAdjacentIndex : Fin (m + 1))
    rw [hobj_eq]
    exact
      binaryEndpointAwareAdjacentRate_pos
        hm oldLevels (fun _ : Fin (m + 2) => (1 : ℝ)) holdLevels
        (by intro i; norm_num) (by intro i; norm_num)
        (firstAdjacentIndex : Fin (m + 1))
  have hrateLower_pos : 0 < rateLower := by
    dsimp [rateLower]
    positivity
  have hrateLower_le_objective :
      rateLower ≤
        binaryEndpointAwareAdjacentRateObjective newLevels
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    dsimp [rateLower, newLevels]
    exact
      uniformDoubledEndpointLevels_objective_rate_ge_one_fifth_old_objective_closed
        hm holdLevels holdEq
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_uniform_equalized_objective_rate_lower
      (m := 2 * m + 1) (by omega) newLevels returned heps
      hrateLower_pos (by simpa [rateLower] using hlower_le_one)
      (uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels)
      (uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq)
      (by simpa [newLevels] using htFirstStar)
      hrateLower_le_objective
      (by simpa [rateLower] using hdelta)
      (by simpa [newLevels] using hlast)
      (by simpa [newLevels] using hgrid)

/--
Uniform-matching Theorem 3.2 run certificate for the explicit C.5 doubled
chain, with the C.5/C.7 objective lower bound derived internally.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {tFirstStar delta eps : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlower_le_one :
      (1 / 5 : ℝ) *
          binaryEndpointAwareAdjacentRateObjective oldLevels
            (fun _ : Fin (m + 2) => (1 : ℝ)) ≤ 1)
    (htFirstStar :
      tFirstStar =
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hdelta :
      delta =
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hlast :
      binaryEndpointAwareAdjacentRate
          (uniformDoubledEndpointLevels oldLevels)
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
          Real.log
            ((uniformDoubledEndpointLevels oldLevels
                  (adjacentLowIndex
                    (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) +
                delta) /
              uniformDoubledEndpointLevels oldLevels
                (adjacentLowIndex
                  (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (hgrid :
      ∀ i : Fin ((2 * m + 1) + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  constructor
  · exact
      binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_uniform_doubled_closed
        hm oldLevels returned heps holdLevels holdEq hlower_le_one
        htFirstStar hdelta hlast hgrid
  · exact nestedBisectionOperationCount_le_stepBound houter hinner

/--
Theorem 3.2 explicit-delta run certificate for the doubled uniform chain.
This removes the administrative equalities for the first level and grid width:
the source delta choice is substituted directly into the last-rate and grid
certificates.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_explicit_delta
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlower_le_one :
      (1 / 5 : ℝ) *
          binaryEndpointAwareAdjacentRateObjective oldLevels
            (fun _ : Fin (m + 2) => (1 : ℝ)) ≤ 1)
    (hlast :
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      binaryEndpointAwareAdjacentRate
          (uniformDoubledEndpointLevels oldLevels)
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
          Real.log
            ((uniformDoubledEndpointLevels oldLevels
                  (adjacentLowIndex
                    (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) +
                delta) /
              uniformDoubledEndpointLevels oldLevels
                (adjacentLowIndex
                  (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (hgrid :
      let tFirstStar : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      ∀ i : Fin ((2 * m + 1) + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run
      hm oldLevels returned heps holdLevels holdEq hlower_le_one
      (by rfl) (by rfl) hlast hgrid houter hinner

/--
Theorem 3.2 explicit-delta doubled-chain run certificate with the C.7
`lower ≤ 1` side condition discharged from uniform equalization.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_explicit_delta_auto_lower
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlast :
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      binaryEndpointAwareAdjacentRate
          (uniformDoubledEndpointLevels oldLevels)
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
          Real.log
            ((uniformDoubledEndpointLevels oldLevels
                  (adjacentLowIndex
                    (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) +
                delta) /
              uniformDoubledEndpointLevels oldLevels
                (adjacentLowIndex
                  (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (hgrid :
      let tFirstStar : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      ∀ i : Fin ((2 * m + 1) + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_explicit_delta
      hm oldLevels returned heps holdLevels holdEq
      (BinaryEndpointLevelVector_uniform_equalized_one_fifth_objective_le_one
        hm holdLevels holdEq)
      hlast hgrid houter hinner

/--
Paper-specific run certificate for Theorem 3.2's `NestedBisection` proof.
It records exactly the algorithm-facing facts used by the checked approximation
argument: the final-level rate certificate, all-grid rate certificate, and the
outer/inner bisection depth bounds.  This is a source-level run contract, not
an executable implementation of the algorithm.
-/
structure Theorem32NestedBisectionRunCertificate
    {m M L : ℕ}
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    (eps : ℝ) where
  outerSteps : ℕ
  innerSteps : ℕ
  hlast :
    let delta : ℝ :=
      eps /
        ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
          (((1 / 5 : ℝ) *
              binaryEndpointAwareAdjacentRateObjective oldLevels
                (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
    binaryEndpointAwareAdjacentRate
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
        Real.log
          ((uniformDoubledEndpointLevels oldLevels
                (adjacentLowIndex
                  (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) +
              delta) /
            uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))) ≤
      binaryEndpointAwareAdjacentRate returned
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
  hgrid :
    let tFirstStar : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let delta : ℝ :=
      eps /
        ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
          (((1 / 5 : ℝ) *
              binaryEndpointAwareAdjacentRateObjective oldLevels
                (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
    ∀ i : Fin ((2 * m + 1) + 1),
      binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
          Real.log ((tFirstStar + delta) / tFirstStar) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i
  houter : outerSteps ≤ L + 1
  hinner : innerSteps ≤ L

/--
Source-shaped backward `CalculateOtherLevels` recursion used by Algorithm 1.
`d = 0` is the fixed last endpoint `1`, `d = 1` is the outer bisection's
returned penultimate endpoint, and larger `d` values are produced by the
inner `BisectNextLevel` low-endpoint bisection from the already-computed high
endpoint.
-/
noncomputable def theorem32BackwardLowBisectionFromTop
    (innerSteps : ℕ) (tFirst target lastLow : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => lastLow
  | d + 2 =>
      let high :=
        theorem32BackwardLowBisectionFromTop innerSteps tFirst target lastLow
          (d + 1)
      let root :=
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst high target
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget root)
        innerSteps 0 high).2

/--
Endpoint vector produced by the backward `CalculateOtherLevels` recursion once
the outer bisection has selected the penultimate endpoint.
-/
noncomputable def theorem32BackwardLowBisectionLevels
    (n innerSteps : ℕ) (tFirst target lastLow : ℝ) :
    Fin (n + 2) → ℝ := fun k =>
  if k.val = 0 then 0
  else
    theorem32BackwardLowBisectionFromTop innerSteps tFirst target lastLow
      (n + 1 - k.val)

/-- The backward recursion fixes the final endpoint at `1`. -/
theorem theorem32BackwardLowBisectionLevels_last
    (n innerSteps : ℕ) (tFirst target lastLow : ℝ) :
    theorem32BackwardLowBisectionLevels n innerSteps tFirst target lastLow
        (lastLevelIndex : Fin (n + 2)) = 1 := by
  simp [theorem32BackwardLowBisectionLevels,
    theorem32BackwardLowBisectionFromTop]

/-- The backward recursion records the outer bisection's penultimate endpoint. -/
theorem theorem32BackwardLowBisectionLevels_last_low
    {n innerSteps : ℕ} (hn : 0 < n)
    (tFirst target lastLow : ℝ) :
    theorem32BackwardLowBisectionLevels n innerSteps tFirst target lastLow
        (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) = lastLow := by
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
  simp [theorem32BackwardLowBisectionLevels,
    theorem32BackwardLowBisectionFromTop, adjacentLowIndex,
    lastAdjacentIndex, hn_ne]

/--
For every interior adjacent interval, the backward `CalculateOtherLevels`
vector is exactly the upper endpoint returned by the corresponding
`BisectNextLevel` run.
-/
theorem theorem32BackwardLowBisectionLevels_returnedLow
    {n innerSteps : ℕ} (tFirst target lastLow : ℝ)
    (i : Fin (n + 1)) (hfirst : i.val ≠ 0) (hlast : i.val ≠ n) :
    let returned :=
      theorem32BackwardLowBisectionLevels n innerSteps tFirst target lastLow
    let root : Fin (n + 1) → ℝ := fun j =>
      weightedBernoulliLowEndpointOfRateOrFloor
        (1 : ℝ) (1 : ℝ) tFirst
        (returned (adjacentHighIndex j)) target
    (EconCSLib.Optimization.realBisectionRun
      (EconCSLib.Optimization.realBisectionAboveTarget (root i))
      innerSteps 0 (returned (adjacentHighIndex i))).2 =
      returned (adjacentLowIndex i) := by
  dsimp
  have hi_lt : i.val < n := lt_of_le_of_ne (Nat.le_of_lt_succ i.2) hlast
  have hhigh_ne_zero : (i.val + 1) ≠ 0 := by omega
  have hlow_sub :
      n + 1 - i.val = (n - i.val) + 1 := by omega
  have hhigh_sub :
      n + 1 - (i.val + 1) = n - i.val := by omega
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : n - i.val ≠ 0) with
    ⟨d, hd⟩
  have hlow_sub' : n + 1 - i.val = d + 2 := by omega
  have hhigh_sub' : n + 1 - (i.val + 1) = d + 1 := by omega
  simp [theorem32BackwardLowBisectionLevels, adjacentLowIndex,
    adjacentHighIndex, hfirst, hlow_sub', hhigh_sub',
    theorem32BackwardLowBisectionFromTop]

/--
Interior strictness for the backward `CalculateOtherLevels` recursion from the
source bisection gap condition.  If the final inner-bisection width is smaller
than the gap between the exact low-endpoint root and the previous high
endpoint, then the returned upper endpoint is strictly below that high
endpoint.
-/
theorem theorem32BackwardLowBisectionLevels_interior_adjacent_strict_of_feasible_gap
    {n innerSteps : ℕ} (tFirst target lastLow : ℝ)
    (hfeasible :
      let returned :=
        theorem32BackwardLowBisectionLevels n innerSteps tFirst target lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hgap :
      let returned :=
        theorem32BackwardLowBisectionLevels n innerSteps tFirst target lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        (returned (adjacentHighIndex i) - 0) /
            (2 : ℝ) ^ innerSteps <
          returned (adjacentHighIndex i) - root i)
    (i : Fin (n + 1)) (hfirst : i.val ≠ 0) (hlast : i.val ≠ n) :
    theorem32BackwardLowBisectionLevels n innerSteps tFirst target lastLow
        (adjacentLowIndex i) <
      theorem32BackwardLowBisectionLevels n innerSteps tFirst target lastLow
        (adjacentHighIndex i) := by
  let returned :=
    theorem32BackwardLowBisectionLevels n innerSteps tFirst target lastLow
  let root : Fin (n + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  have hmem :
      root i ∈ Set.Ioo tFirst (returned (adjacentHighIndex i)) := by
    simpa [root, returned] using
      weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
        (hfeasible i hfirst hlast)
  have hroot_nonneg : 0 ≤ root i := by
    exact le_of_lt ((hfeasible i hfirst hlast).hfloor0.trans hmem.1)
  have hroot_le_high : root i ≤ returned (adjacentHighIndex i) :=
    le_of_lt hmem.2
  have hreturnedLow :
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget (root i))
        innerSteps 0 (returned (adjacentHighIndex i))).2 =
        returned (adjacentLowIndex i) := by
    simpa [returned, root] using
      theorem32BackwardLowBisectionLevels_returnedLow
        (n := n) (innerSteps := innerSteps)
        tFirst target lastLow i hfirst hlast
  have hstrict :
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget (root i))
        innerSteps 0 (returned (adjacentHighIndex i))).2 <
        returned (adjacentHighIndex i) := by
    exact
      EconCSLib.Optimization.realBisectionRun_aboveTarget_upper_lt_initial_upper_of_width_lt_gap
        (n := innerSteps) (lower := 0)
        (target := root i) (upper := returned (adjacentHighIndex i))
        hroot_nonneg hroot_le_high
        (by simpa [returned, root] using hgap i hfirst hlast)
  simpa [returned, hreturnedLow] using hstrict

/--
The first interior endpoint of the backward recursion is positive once the
recursion has a genuine interior bisection call.  It is the returned upper
endpoint of the call whose low endpoint is level `1`, and executable bisection
keeps that upper endpoint above the positive exact root.
-/
theorem theorem32BackwardLowBisectionLevels_first_high_pos_of_feasible
    {n innerSteps : ℕ} (hn : 1 < n) (tFirst target lastLow : ℝ)
    (hfeasible :
      let returned :=
        theorem32BackwardLowBisectionLevels n innerSteps tFirst target lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target) :
    0 <
      theorem32BackwardLowBisectionLevels n innerSteps tFirst target lastLow
        (adjacentHighIndex (firstAdjacentIndex : Fin (n + 1))) := by
  let returned :=
    theorem32BackwardLowBisectionLevels n innerSteps tFirst target lastLow
  let i : Fin (n + 1) := ⟨1, by omega⟩
  let root : Fin (n + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  have hi_first : i.val ≠ 0 := by
    simp [i]
  have hi_last : i.val ≠ n := by
    simp [i]
    omega
  have hmem :
      root i ∈ Set.Ioo tFirst (returned (adjacentHighIndex i)) := by
    simpa [root, returned] using
      weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
        (hfeasible i hi_first hi_last)
  have hroot_pos : 0 < root i :=
    (hfeasible i hi_first hi_last).hfloor0.trans hmem.1
  have hroot_nonneg : 0 ≤ root i := le_of_lt hroot_pos
  have hroot_le_high : root i ≤ returned (adjacentHighIndex i) :=
    le_of_lt hmem.2
  have hupper_ge_root :
      root i ≤
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 :=
    EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
      (n := innerSteps) (lower := 0)
      (target := root i) (upper := returned (adjacentHighIndex i))
      hroot_nonneg hroot_le_high
  have hreturnedLow :
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget (root i))
        innerSteps 0 (returned (adjacentHighIndex i))).2 =
        returned (adjacentLowIndex i) := by
    simpa [returned, root] using
      theorem32BackwardLowBisectionLevels_returnedLow
        (n := n) (innerSteps := innerSteps)
        tFirst target lastLow i hi_first hi_last
  have hlevel_pos : 0 < returned (adjacentLowIndex i) := by
    exact hroot_pos.trans_le (by simpa [hreturnedLow] using hupper_ge_root)
  simpa [returned, i, adjacentLowIndex, adjacentHighIndex,
    firstAdjacentIndex] using hlevel_pos

/--
Endpoint-vector constructor for the backward `CalculateOtherLevels` recursion.
The only source-shaped strictness input is the inner bisection gap condition:
the final bisection width must be smaller than the exact root-to-high gap for
each nonterminal interior call.
-/
theorem theorem32BackwardLowBisectionLevels_isEndpointLevelVector_of_feasible_gap
    {n innerSteps : ℕ} (hn : 0 < n) (tFirst target lastLow : ℝ)
    (hfirst_pos :
      0 <
        theorem32BackwardLowBisectionLevels n innerSteps tFirst target lastLow
          (adjacentHighIndex (firstAdjacentIndex : Fin (n + 1))))
    (hlastLow_lt_one : lastLow < 1)
    (hfeasible :
      let returned :=
        theorem32BackwardLowBisectionLevels n innerSteps tFirst target lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hgap :
      let returned :=
        theorem32BackwardLowBisectionLevels n innerSteps tFirst target lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        (returned (adjacentHighIndex i) - 0) /
            (2 : ℝ) ^ innerSteps <
          returned (adjacentHighIndex i) - root i) :
    BinaryEndpointLevelVector
      (theorem32BackwardLowBisectionLevels n innerSteps tFirst target lastLow) := by
  let returned :=
    theorem32BackwardLowBisectionLevels n innerSteps tFirst target lastLow
  refine ⟨?_, ?_, ?_⟩
  · simp [theorem32BackwardLowBisectionLevels]
  · simpa [returned] using
      theorem32BackwardLowBisectionLevels_last n innerSteps tFirst target lastLow
  · intro i
    by_cases hfirst : i.val = 0
    · have hi : i = (firstAdjacentIndex : Fin (n + 1)) := by
        ext
        simpa [firstAdjacentIndex] using hfirst
      subst i
      have hlow :
          returned
              (adjacentLowIndex (firstAdjacentIndex : Fin (n + 1))) = 0 := by
        simp [returned, theorem32BackwardLowBisectionLevels,
          adjacentLowIndex, firstAdjacentIndex]
      simpa [returned, hlow] using hfirst_pos
    · by_cases hlast : i.val = n
      · have hi : i = (lastAdjacentIndex : Fin (n + 1)) := by
          ext
          simpa [lastAdjacentIndex] using hlast
        subst i
        have hlow :
            returned
                (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) =
              lastLow := by
          simpa [returned] using
            theorem32BackwardLowBisectionLevels_last_low
              (n := n) (innerSteps := innerSteps) hn tFirst target lastLow
        have hhigh :
            returned
                (adjacentHighIndex (lastAdjacentIndex : Fin (n + 1))) =
              1 := by
          simpa [returned, adjacentHighIndex, lastAdjacentIndex, lastLevelIndex] using
            theorem32BackwardLowBisectionLevels_last
              n innerSteps tFirst target lastLow
        change
          returned (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) <
            returned (adjacentHighIndex (lastAdjacentIndex : Fin (n + 1)))
        rw [hlow, hhigh]
        exact hlastLow_lt_one
      · simpa [returned] using
          theorem32BackwardLowBisectionLevels_interior_adjacent_strict_of_feasible_gap
            (n := n) (innerSteps := innerSteps)
            tFirst target lastLow hfeasible hgap i hfirst hlast

/--
Endpoint-vector constructor with the first positive endpoint derived from the
first genuine inner bisection call.  This is the form used by the source
Theorem 3.2 bridge for `n = 2m + 1`.
-/
theorem theorem32BackwardLowBisectionLevels_isEndpointLevelVector_of_feasible_gap_auto_first
    {n innerSteps : ℕ} (hn : 1 < n) (tFirst target lastLow : ℝ)
    (hlastLow_lt_one : lastLow < 1)
    (hfeasible :
      let returned :=
        theorem32BackwardLowBisectionLevels n innerSteps tFirst target lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hgap :
      let returned :=
        theorem32BackwardLowBisectionLevels n innerSteps tFirst target lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        (returned (adjacentHighIndex i) - 0) /
            (2 : ℝ) ^ innerSteps <
          returned (adjacentHighIndex i) - root i) :
    BinaryEndpointLevelVector
      (theorem32BackwardLowBisectionLevels n innerSteps tFirst target lastLow) :=
  theorem32BackwardLowBisectionLevels_isEndpointLevelVector_of_feasible_gap
    (n := n) (innerSteps := innerSteps) (Nat.lt_of_succ_lt hn)
    tFirst target lastLow
    (theorem32BackwardLowBisectionLevels_first_high_pos_of_feasible
      (n := n) (innerSteps := innerSteps) hn tFirst target lastLow hfeasible)
    hlastLow_lt_one hfeasible hgap

/--
Source-shaped backward `CalculateOtherLevels` recursion with the inner
`BisectNextLevel` upper endpoint shifted down by the source grid width.  This
matches the supplement's `r = j_m - δ` initialization for each inner
low-endpoint bisection.
-/
noncomputable def theorem32BackwardGridLowBisectionFromTop
    (innerSteps : ℕ) (grid tFirst target lastLow : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => lastLow
  | d + 2 =>
      let high :=
        theorem32BackwardGridLowBisectionFromTop innerSteps grid tFirst target
          lastLow (d + 1)
      let root :=
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst high target
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget root)
        innerSteps 0 (high - grid)).2

/--
Endpoint vector produced by the source-grid backward `CalculateOtherLevels`
recursion once the outer bisection has selected the penultimate endpoint.
-/
noncomputable def theorem32BackwardGridLowBisectionLevels
    (n innerSteps : ℕ) (grid tFirst target lastLow : ℝ) :
    Fin (n + 2) → ℝ := fun k =>
  if k.val = 0 then 0
  else
    theorem32BackwardGridLowBisectionFromTop innerSteps grid tFirst target
      lastLow (n + 1 - k.val)

/-- The source-grid backward recursion fixes the final endpoint at `1`. -/
theorem theorem32BackwardGridLowBisectionLevels_last
    (n innerSteps : ℕ) (grid tFirst target lastLow : ℝ) :
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow (lastLevelIndex : Fin (n + 2)) = 1 := by
  simp [theorem32BackwardGridLowBisectionLevels,
    theorem32BackwardGridLowBisectionFromTop]

/-- The source-grid backward recursion records the outer bisection's penultimate endpoint. -/
theorem theorem32BackwardGridLowBisectionLevels_last_low
    {n innerSteps : ℕ} (hn : 0 < n)
    (grid tFirst target lastLow : ℝ) :
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) =
      lastLow := by
  have hn_ne : n ≠ 0 := Nat.ne_of_gt hn
  simp [theorem32BackwardGridLowBisectionLevels,
    theorem32BackwardGridLowBisectionFromTop, adjacentLowIndex,
    lastAdjacentIndex, hn_ne]

/--
Uniform source-shaped `NestedBisection` output for the doubled endpoint chain.
This is the executable specialization represented by the Theorem 3.2 proof:
the outer bisection searches the penultimate optimal endpoint on
`[1 - 1/(2m+2), 1 - grid]`, the inner recursion uses the supplement's
`r = j_m - grid` right endpoint, and an exact outer hit returns the already
optimal doubled chain.
-/
noncomputable def theorem32UniformDoubledNestedBisectionOutput
    (m L : ℕ) (oldLevels : Fin (m + 2) → ℝ) (grid : ℝ) :
    Fin ((2 * m + 1) + 2) → ℝ :=
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let levelTarget : ℝ :=
    optimal
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let lastLow : ℝ :=
    (EconCSLib.Optimization.realBisectionRun
      (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
      (L + 1)
      (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
      (1 - grid)).2
  let tFirst : ℝ :=
    optimal
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let gridReturned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) L grid tFirst target lastLow
  if levelTarget = lastLow then optimal else gridReturned

/--
For every interior adjacent interval, the source-grid backward
`CalculateOtherLevels` vector is exactly the upper endpoint returned by the
corresponding `BisectNextLevel` run initialized on `[0, high - grid]`.
-/
theorem theorem32BackwardGridLowBisectionLevels_returnedLow
    {n innerSteps : ℕ} (grid tFirst target lastLow : ℝ)
    (i : Fin (n + 1)) (hfirst : i.val ≠ 0) (hlast : i.val ≠ n) :
    let returned :=
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow
    let root : Fin (n + 1) → ℝ := fun j =>
      weightedBernoulliLowEndpointOfRateOrFloor
        (1 : ℝ) (1 : ℝ) tFirst
        (returned (adjacentHighIndex j)) target
    (EconCSLib.Optimization.realBisectionRun
      (EconCSLib.Optimization.realBisectionAboveTarget (root i))
      innerSteps 0 (returned (adjacentHighIndex i) - grid)).2 =
      returned (adjacentLowIndex i) := by
  dsimp
  have hi_lt : i.val < n := lt_of_le_of_ne (Nat.le_of_lt_succ i.2) hlast
  have hlow_sub :
      n + 1 - i.val = (n - i.val) + 1 := by omega
  have hhigh_sub :
      n + 1 - (i.val + 1) = n - i.val := by omega
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : n - i.val ≠ 0) with
    ⟨d, hd⟩
  have hlow_sub' : n + 1 - i.val = d + 2 := by omega
  have hhigh_sub' : n + 1 - (i.val + 1) = d + 1 := by omega
  simp [theorem32BackwardGridLowBisectionLevels, adjacentLowIndex,
    adjacentHighIndex, hfirst, hlow_sub', hhigh_sub',
    theorem32BackwardGridLowBisectionFromTop]

/--
Interior strictness for the source-grid backward `CalculateOtherLevels`
recursion.  If the exact low-endpoint root lies below the source upper
endpoint `high - grid`, then the returned upper endpoint is strictly below
the previous high endpoint as soon as `grid > 0`.
-/
theorem theorem32BackwardGridLowBisectionLevels_interior_adjacent_strict_of_feasible_grid
    {n innerSteps : ℕ} (grid tFirst target lastLow : ℝ)
    (hgrid_pos : 0 < grid)
    (hfeasible :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hroot_le_grid_upper :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        root i ≤ returned (adjacentHighIndex i) - grid)
    (i : Fin (n + 1)) (hfirst : i.val ≠ 0) (hlast : i.val ≠ n) :
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow (adjacentLowIndex i) <
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow (adjacentHighIndex i) := by
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  let root : Fin (n + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  have hmem :
      root i ∈ Set.Ioo tFirst (returned (adjacentHighIndex i)) := by
    simpa [root, returned] using
      weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
        (hfeasible i hfirst hlast)
  have hroot_nonneg : 0 ≤ root i := by
    exact le_of_lt ((hfeasible i hfirst hlast).hfloor0.trans hmem.1)
  have hroot_le_upper :
      root i ≤ returned (adjacentHighIndex i) - grid := by
    simpa [returned, root] using hroot_le_grid_upper i hfirst hlast
  have hupper_nonneg : 0 ≤ returned (adjacentHighIndex i) - grid :=
    hroot_nonneg.trans hroot_le_upper
  have hrun_le :
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget (root i))
        innerSteps 0 (returned (adjacentHighIndex i) - grid)).2 ≤
        returned (adjacentHighIndex i) - grid :=
    EconCSLib.Optimization.realBisectionRun_upper_le_initial
      (EconCSLib.Optimization.realBisectionAboveTarget (root i))
      hupper_nonneg
  have hreturnedLow :
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget (root i))
        innerSteps 0 (returned (adjacentHighIndex i) - grid)).2 =
        returned (adjacentLowIndex i) := by
    simpa [returned, root] using
      theorem32BackwardGridLowBisectionLevels_returnedLow
        (n := n) (innerSteps := innerSteps)
        grid tFirst target lastLow i hfirst hlast
  have hlow_le :
      returned (adjacentLowIndex i) ≤
        returned (adjacentHighIndex i) - grid := by
    simpa [hreturnedLow] using hrun_le
  linarith

/--
The first interior endpoint of the source-grid backward recursion is positive
once the first genuine inner bisection brackets a positive exact root.
-/
theorem theorem32BackwardGridLowBisectionLevels_first_high_pos_of_feasible_grid
    {n innerSteps : ℕ} (hn : 1 < n) (grid tFirst target lastLow : ℝ)
    (hfeasible :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hroot_le_grid_upper :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        root i ≤ returned (adjacentHighIndex i) - grid) :
    0 <
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow (adjacentHighIndex (firstAdjacentIndex : Fin (n + 1))) := by
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  let i : Fin (n + 1) := ⟨1, by omega⟩
  let root : Fin (n + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  have hi_first : i.val ≠ 0 := by
    simp [i]
  have hi_last : i.val ≠ n := by
    simp [i]
    omega
  have hmem :
      root i ∈ Set.Ioo tFirst (returned (adjacentHighIndex i)) := by
    simpa [root, returned] using
      weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
        (hfeasible i hi_first hi_last)
  have hroot_pos : 0 < root i :=
    (hfeasible i hi_first hi_last).hfloor0.trans hmem.1
  have hroot_nonneg : 0 ≤ root i := le_of_lt hroot_pos
  have hroot_le_upper :
      root i ≤ returned (adjacentHighIndex i) - grid := by
    simpa [returned, root] using
      hroot_le_grid_upper i hi_first hi_last
  have hupper_ge_root :
      root i ≤
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i) - grid)).2 :=
    EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
      (n := innerSteps) (lower := 0)
      (target := root i)
      (upper := returned (adjacentHighIndex i) - grid)
      hroot_nonneg hroot_le_upper
  have hreturnedLow :
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget (root i))
        innerSteps 0 (returned (adjacentHighIndex i) - grid)).2 =
        returned (adjacentLowIndex i) := by
    simpa [returned, root] using
      theorem32BackwardGridLowBisectionLevels_returnedLow
        (n := n) (innerSteps := innerSteps)
        grid tFirst target lastLow i hi_first hi_last
  have hlevel_pos : 0 < returned (adjacentLowIndex i) := by
    exact hroot_pos.trans_le (by simpa [hreturnedLow] using hupper_ge_root)
  simpa [returned, i, adjacentLowIndex, adjacentHighIndex,
    firstAdjacentIndex] using hlevel_pos

/--
Endpoint-vector constructor for the source-grid backward
`CalculateOtherLevels` recursion.  The source-grid assumptions are exactly
that the grid is positive and every exact root lies below the initialized
upper endpoint `high - grid`.
-/
theorem theorem32BackwardGridLowBisectionLevels_isEndpointLevelVector_of_feasible_grid
    {n innerSteps : ℕ} (hn : 0 < n) (grid tFirst target lastLow : ℝ)
    (hgrid_pos : 0 < grid)
    (hfirst_pos :
      0 <
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
          (adjacentHighIndex (firstAdjacentIndex : Fin (n + 1))))
    (hlastLow_lt_one : lastLow < 1)
    (hfeasible :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hroot_le_grid_upper :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        root i ≤ returned (adjacentHighIndex i) - grid) :
    BinaryEndpointLevelVector
      (theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow) := by
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  refine ⟨?_, ?_, ?_⟩
  · simp [theorem32BackwardGridLowBisectionLevels]
  · simpa [returned] using
      theorem32BackwardGridLowBisectionLevels_last
        n innerSteps grid tFirst target lastLow
  · intro i
    by_cases hfirst : i.val = 0
    · have hi : i = (firstAdjacentIndex : Fin (n + 1)) := by
        ext
        simpa [firstAdjacentIndex] using hfirst
      subst i
      have hlow :
          returned
              (adjacentLowIndex (firstAdjacentIndex : Fin (n + 1))) = 0 := by
        simp [returned, theorem32BackwardGridLowBisectionLevels,
          adjacentLowIndex, firstAdjacentIndex]
      simpa [returned, hlow] using hfirst_pos
    · by_cases hlast : i.val = n
      · have hi : i = (lastAdjacentIndex : Fin (n + 1)) := by
          ext
          simpa [lastAdjacentIndex] using hlast
        subst i
        have hlow :
            returned
                (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) =
              lastLow := by
          simpa [returned] using
            theorem32BackwardGridLowBisectionLevels_last_low
              (n := n) (innerSteps := innerSteps) hn grid tFirst target lastLow
        have hhigh :
            returned
                (adjacentHighIndex (lastAdjacentIndex : Fin (n + 1))) =
              1 := by
          simpa [returned, adjacentHighIndex, lastAdjacentIndex, lastLevelIndex] using
            theorem32BackwardGridLowBisectionLevels_last
              n innerSteps grid tFirst target lastLow
        change
          returned (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) <
            returned (adjacentHighIndex (lastAdjacentIndex : Fin (n + 1)))
        rw [hlow, hhigh]
        exact hlastLow_lt_one
      · simpa [returned] using
          theorem32BackwardGridLowBisectionLevels_interior_adjacent_strict_of_feasible_grid
            (n := n) (innerSteps := innerSteps)
            grid tFirst target lastLow hgrid_pos hfeasible
            hroot_le_grid_upper i hfirst hlast

/--
Endpoint-vector constructor for the source-grid recursion with the first
positive endpoint derived from the first genuine inner bisection call.
-/
theorem theorem32BackwardGridLowBisectionLevels_isEndpointLevelVector_of_feasible_grid_auto_first
    {n innerSteps : ℕ} (hn : 1 < n) (grid tFirst target lastLow : ℝ)
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (hfeasible :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hroot_le_grid_upper :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        root i ≤ returned (adjacentHighIndex i) - grid) :
    BinaryEndpointLevelVector
      (theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow) :=
  theorem32BackwardGridLowBisectionLevels_isEndpointLevelVector_of_feasible_grid
    (n := n) (innerSteps := innerSteps) (Nat.lt_of_succ_lt hn)
    grid tFirst target lastLow hgrid_pos
    (theorem32BackwardGridLowBisectionLevels_first_high_pos_of_feasible_grid
      (n := n) (innerSteps := innerSteps) hn grid tFirst target lastLow
      hfeasible hroot_le_grid_upper)
    hlastLow_lt_one hfeasible hroot_le_grid_upper

/--
Interior strictness for the source-grid backward recursion from root placement
alone.  The clipped low-endpoint selector is always at least its floor, so a
positive floor and `root ≤ high - grid` make the executable bisection bracket
nonempty and keep its returned upper endpoint strictly below the previous
high endpoint.
-/
theorem theorem32BackwardGridLowBisectionLevels_interior_adjacent_strict_of_root_le_grid_upper
    {n innerSteps : ℕ} (grid tFirst target lastLow : ℝ)
    (htFirst_pos : 0 < tFirst)
    (hgrid_pos : 0 < grid)
    (hroot_le_grid_upper :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        root i ≤ returned (adjacentHighIndex i) - grid)
    (i : Fin (n + 1)) (hfirst : i.val ≠ 0) (hlast : i.val ≠ n) :
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow (adjacentLowIndex i) <
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow (adjacentHighIndex i) := by
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  let root : Fin (n + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  have hfloor_le_root : tFirst ≤ root i := by
    simpa [root] using
      (floor_le_weightedBernoulliLowEndpointOfRateOrFloor_unconditional
        (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
        (pHi := returned (adjacentHighIndex i)) (target := target))
  have hroot_nonneg : 0 ≤ root i := (le_of_lt htFirst_pos).trans hfloor_le_root
  have hroot_le_upper :
      root i ≤ returned (adjacentHighIndex i) - grid := by
    simpa [returned, root] using hroot_le_grid_upper i hfirst hlast
  have hupper_nonneg : 0 ≤ returned (adjacentHighIndex i) - grid :=
    hroot_nonneg.trans hroot_le_upper
  have hrun_le :
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget (root i))
        innerSteps 0 (returned (adjacentHighIndex i) - grid)).2 ≤
        returned (adjacentHighIndex i) - grid :=
    EconCSLib.Optimization.realBisectionRun_upper_le_initial
      (above := EconCSLib.Optimization.realBisectionAboveTarget (root i))
      (n := innerSteps) hupper_nonneg
  have hreturnedLow :
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget (root i))
        innerSteps 0 (returned (adjacentHighIndex i) - grid)).2 =
        returned (adjacentLowIndex i) := by
    simpa [returned, root] using
      theorem32BackwardGridLowBisectionLevels_returnedLow
        (n := n) (innerSteps := innerSteps)
        grid tFirst target lastLow i hfirst hlast
  have hlow_le_grid :
      returned (adjacentLowIndex i) ≤
        returned (adjacentHighIndex i) - grid := by
    simpa [hreturnedLow] using hrun_le
  linarith

/--
The first interior endpoint of the source-grid recursion is positive from
root placement alone.
-/
theorem theorem32BackwardGridLowBisectionLevels_first_high_pos_of_root_le_grid_upper
    {n innerSteps : ℕ} (hn : 1 < n) (grid tFirst target lastLow : ℝ)
    (htFirst_pos : 0 < tFirst)
    (hroot_le_grid_upper :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        root i ≤ returned (adjacentHighIndex i) - grid) :
    0 <
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow
        (adjacentHighIndex (firstAdjacentIndex : Fin (n + 1))) := by
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  let i : Fin (n + 1) := ⟨1, by omega⟩
  let root : Fin (n + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  have hi_first : i.val ≠ 0 := by simp [i]
  have hi_last : i.val ≠ n := by
    simp [i]
    omega
  have hfloor_le_root : tFirst ≤ root i := by
    simpa [root] using
      (floor_le_weightedBernoulliLowEndpointOfRateOrFloor_unconditional
        (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
        (pHi := returned (adjacentHighIndex i)) (target := target))
  have hroot_pos : 0 < root i := htFirst_pos.trans_le hfloor_le_root
  have hroot_le_upper :
      root i ≤ returned (adjacentHighIndex i) - grid := by
    simpa [returned, root] using hroot_le_grid_upper i hi_first hi_last
  have hupper_ge_root :
      root i ≤
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i) - grid)).2 :=
    EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
      (n := innerSteps) (lower := 0)
      (target := root i) (upper := returned (adjacentHighIndex i) - grid)
      hroot_pos.le hroot_le_upper
  have hreturnedLow :
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget (root i))
        innerSteps 0 (returned (adjacentHighIndex i) - grid)).2 =
        returned (adjacentLowIndex i) := by
    simpa [returned, root] using
      theorem32BackwardGridLowBisectionLevels_returnedLow
        (n := n) (innerSteps := innerSteps)
        grid tFirst target lastLow i hi_first hi_last
  have hlow_pos : 0 < returned (adjacentLowIndex i) :=
    hroot_pos.trans_le (by simpa [hreturnedLow] using hupper_ge_root)
  simpa [returned, i, adjacentLowIndex, adjacentHighIndex,
    firstAdjacentIndex] using hlow_pos

/--
The first interior endpoint of the source-grid recursion is at least the fixed
floor from root placement alone.
-/
theorem theorem32BackwardGridLowBisectionLevels_first_high_ge_floor_of_root_le_grid_upper
    {n innerSteps : ℕ} (hn : 1 < n) (grid tFirst target lastLow : ℝ)
    (htFirst_pos : 0 < tFirst)
    (hroot_le_grid_upper :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        root i ≤ returned (adjacentHighIndex i) - grid) :
    tFirst ≤
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow
        (adjacentHighIndex (firstAdjacentIndex : Fin (n + 1))) := by
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  let i : Fin (n + 1) := ⟨1, by omega⟩
  let root : Fin (n + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  have hi_first : i.val ≠ 0 := by simp [i]
  have hi_last : i.val ≠ n := by
    simp [i]
    omega
  have hfloor_le_root : tFirst ≤ root i := by
    simpa [root] using
      (floor_le_weightedBernoulliLowEndpointOfRateOrFloor_unconditional
        (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
        (pHi := returned (adjacentHighIndex i)) (target := target))
  have hroot_pos : 0 < root i := htFirst_pos.trans_le hfloor_le_root
  have hroot_le_upper :
      root i ≤ returned (adjacentHighIndex i) - grid := by
    simpa [returned, root] using hroot_le_grid_upper i hi_first hi_last
  have hupper_ge_root :
      root i ≤
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i) - grid)).2 :=
    EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
      (n := innerSteps) (lower := 0)
      (target := root i) (upper := returned (adjacentHighIndex i) - grid)
      hroot_pos.le hroot_le_upper
  have hreturnedLow :
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget (root i))
        innerSteps 0 (returned (adjacentHighIndex i) - grid)).2 =
        returned (adjacentLowIndex i) := by
    simpa [returned, root] using
      theorem32BackwardGridLowBisectionLevels_returnedLow
        (n := n) (innerSteps := innerSteps)
        grid tFirst target lastLow i hi_first hi_last
  calc
    tFirst ≤ root i := hfloor_le_root
    _ ≤ returned (adjacentLowIndex i) := by
      simpa [hreturnedLow] using hupper_ge_root
    _ =
        returned
          (adjacentHighIndex (firstAdjacentIndex : Fin (n + 1))) := by
      simp [i, adjacentLowIndex, adjacentHighIndex, firstAdjacentIndex]

/--
Endpoint-vector constructor for the source-grid recursion from root placement
alone.  Feasibility of the low-endpoint target can then be proved afterward
from the resulting endpoint vector and source rate inequalities.
-/
theorem theorem32BackwardGridLowBisectionLevels_isEndpointLevelVector_of_root_le_grid_upper
    {n innerSteps : ℕ} (hn : 1 < n) (grid tFirst target lastLow : ℝ)
    (htFirst_pos : 0 < tFirst)
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (hroot_le_grid_upper :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        root i ≤ returned (adjacentHighIndex i) - grid) :
    BinaryEndpointLevelVector
      (theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow) := by
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  refine ⟨?_, ?_, ?_⟩
  · simp [theorem32BackwardGridLowBisectionLevels]
  · simpa [returned] using
      theorem32BackwardGridLowBisectionLevels_last
        n innerSteps grid tFirst target lastLow
  · intro i
    by_cases hfirst : i.val = 0
    · have hi : i = (firstAdjacentIndex : Fin (n + 1)) := by
        ext
        simpa [firstAdjacentIndex] using hfirst
      subst i
      have hlow :
          returned
              (adjacentLowIndex (firstAdjacentIndex : Fin (n + 1))) = 0 := by
        simp [returned, theorem32BackwardGridLowBisectionLevels,
          adjacentLowIndex, firstAdjacentIndex]
      have hfirst_pos :
          0 <
            returned
              (adjacentHighIndex (firstAdjacentIndex : Fin (n + 1))) := by
        simpa [returned] using
          theorem32BackwardGridLowBisectionLevels_first_high_pos_of_root_le_grid_upper
            (n := n) (innerSteps := innerSteps) hn grid tFirst target lastLow
            htFirst_pos hroot_le_grid_upper
      simpa [returned, hlow] using hfirst_pos
    · by_cases hlast : i.val = n
      · have hi : i = (lastAdjacentIndex : Fin (n + 1)) := by
          ext
          simpa [lastAdjacentIndex] using hlast
        subst i
        have hlow :
            returned
                (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) =
              lastLow := by
          simpa [returned] using
            theorem32BackwardGridLowBisectionLevels_last_low
              (n := n) (innerSteps := innerSteps) (Nat.lt_of_succ_lt hn)
              grid tFirst target lastLow
        have hhigh :
            returned
                (adjacentHighIndex (lastAdjacentIndex : Fin (n + 1))) =
              1 := by
          simpa [returned, adjacentHighIndex, lastAdjacentIndex,
            lastLevelIndex] using
            theorem32BackwardGridLowBisectionLevels_last
              n innerSteps grid tFirst target lastLow
        change
          returned (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) <
            returned (adjacentHighIndex (lastAdjacentIndex : Fin (n + 1)))
        rw [hlow, hhigh]
        exact hlastLow_lt_one
      · simpa [returned] using
          theorem32BackwardGridLowBisectionLevels_interior_adjacent_strict_of_root_le_grid_upper
            (n := n) (innerSteps := innerSteps)
            grid tFirst target lastLow htFirst_pos hgrid_pos
            hroot_le_grid_upper i hfirst hlast

/--
Low-endpoint feasibility for every source-grid inner bisection call follows
from the endpoint vector derived from root placement and the source's target
rate inequality at the fixed floor.
-/
theorem theorem32BackwardGridLowBisectionLevels_feasible_of_root_le_grid_upper_and_target_lt_floor_rate
    {n innerSteps : ℕ} (hn : 1 < n) (grid tFirst target lastLow : ℝ)
    (htFirst_pos : 0 < tFirst)
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (htarget_pos : 0 < target)
    (hroot_le_grid_upper :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        root i ≤ returned (adjacentHighIndex i) - grid)
    (htarget_lt_floor_rate :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst) :
    let returned :=
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow
    ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
      WeightedBernoulliLowEndpointTargetFeasible
        (1 : ℝ) (1 : ℝ) tFirst
        (returned (adjacentHighIndex i)) target := by
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  have hreturnedLevels : BinaryEndpointLevelVector returned := by
    simpa [returned] using
      theorem32BackwardGridLowBisectionLevels_isEndpointLevelVector_of_root_le_grid_upper
        (n := n) (innerSteps := innerSteps) hn grid tFirst target lastLow
        htFirst_pos hgrid_pos hlastLow_lt_one hroot_le_grid_upper
  have hfirst_ge :
      tFirst ≤ returned
        (adjacentHighIndex (firstAdjacentIndex : Fin (n + 1))) := by
    simpa [returned] using
      theorem32BackwardGridLowBisectionLevels_first_high_ge_floor_of_root_le_grid_upper
        (n := n) (innerSteps := innerSteps) hn grid tFirst target lastLow
        htFirst_pos hroot_le_grid_upper
  dsimp
  intro i hi_first hi_last
  have hfirst_to_low :
      returned (adjacentHighIndex (firstAdjacentIndex : Fin (n + 1))) ≤
        returned (adjacentLowIndex i) := by
    exact
      BinaryEndpointLevelVector_mono hreturnedLevels
        (by
          simp [firstAdjacentIndex, adjacentHighIndex, adjacentLowIndex]
          omega)
  have hlow_lt_high :
      returned (adjacentLowIndex i) < returned (adjacentHighIndex i) :=
    hreturnedLevels.2.2 i
  have hfloor_lt_high :
      tFirst < returned (adjacentHighIndex i) :=
    lt_of_le_of_lt (hfirst_ge.trans hfirst_to_low) hlow_lt_high
  have hhi_lt_one : returned (adjacentHighIndex i) < 1 := by
    have hnot_last : (adjacentHighIndex i).val ≠ n + 1 := by
      simp [adjacentHighIndex]
      omega
    exact
      BinaryEndpointLevelVector_lt_one_of_not_last
        hreturnedLevels (adjacentHighIndex i) hnot_last
  exact
    { hgHi := by norm_num
      hgLo := by norm_num
      hfloor0 := htFirst_pos
      hfloor_lt_hi := hfloor_lt_high
      hpHi1 := hhi_lt_one
      htarget_pos := htarget_pos
      htarget_lt_floor := by
        simpa [returned] using htarget_lt_floor_rate i hi_first hi_last }

/--
Low-endpoint feasibility for every source-grid inner bisection call follows
from the operational selector fact that the clipped endpoint has moved
strictly above the fixed floor.  The shared binary LDP selector lemma then
recovers all feasibility fields, including the source floor-rate inequality.
-/
theorem theorem32BackwardGridLowBisectionLevels_feasible_of_floor_lt_lowEndpointOfRateOrFloor
    {n innerSteps : ℕ} (grid tFirst target lastLow : ℝ)
    (hfloor_lt_root :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        tFirst < root i) :
    let returned :=
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow
    ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
      WeightedBernoulliLowEndpointTargetFeasible
        (1 : ℝ) (1 : ℝ) tFirst
        (returned (adjacentHighIndex i)) target := by
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  let root : Fin (n + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  dsimp at hfloor_lt_root ⊢
  intro i hi_first hi_last
  exact
    weightedBernoulliLowEndpointTargetFeasible_of_floor_lt_lowEndpointOfRateOrFloor
      (by simpa [returned, root] using hfloor_lt_root i hi_first hi_last)

/--
Source-grid root-placement bridge for `BisectNextLevel`.  If the right endpoint
`high - grid` of the source bisection interval already has closed threshold
rate at most the target, then the clipped low-endpoint root lies below that
right endpoint.  This is the Algorithm 1 endpoint-side condition corresponding
to returning the right side of the final bisection interval.
-/
theorem theorem32BackwardGridLowBisectionLevels_root_le_grid_upper_of_grid_upper_rate_le_target
    {n innerSteps : ℕ} (grid tFirst target lastLow : ℝ)
    (hgrid_pos : 0 < grid)
    (hfloor_le_grid_upper :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        tFirst ≤ returned (adjacentHighIndex i) - grid)
    (hgrid_upper_rate_le_target :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i))
            (returned (adjacentHighIndex i) - grid) ≤
          target) :
    let returned :=
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow
    let root : Fin (n + 1) → ℝ := fun i =>
      weightedBernoulliLowEndpointOfRateOrFloor
        (1 : ℝ) (1 : ℝ) tFirst
        (returned (adjacentHighIndex i)) target
    ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
      root i ≤ returned (adjacentHighIndex i) - grid := by
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  let root : Fin (n + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  dsimp
  intro i hi_first hi_last
  exact
    weightedBernoulliLowEndpointOfRateOrFloor_le_of_rate_le_target
      (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
      (pHi := returned (adjacentHighIndex i)) (target := target)
      (x := returned (adjacentHighIndex i) - grid)
      (by simpa [returned] using hfloor_le_grid_upper i hi_first hi_last)
      (by linarith [hgrid_pos])
      (by
        simpa [returned] using
          hgrid_upper_rate_le_target i hi_first hi_last)

/--
Endpoint-vector constructor for the source-grid recursion from the non-strict
grid-upper rate condition.  This is the weak counterpart to the strict
feasibility constructors: once the source bisection interval contains the
clipped target-rate root, the executable recursion forms a valid endpoint
vector without needing the target to be strictly below the floor rate.
-/
theorem theorem32BackwardGridLowBisectionLevels_isEndpointLevelVector_of_grid_upper_rate_le_target
    {n innerSteps : ℕ} (hn : 1 < n) (grid tFirst target lastLow : ℝ)
    (htFirst_pos : 0 < tFirst)
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (hfloor_le_grid_upper :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        tFirst ≤ returned (adjacentHighIndex i) - grid)
    (hgrid_upper_rate_le_target :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i))
            (returned (adjacentHighIndex i) - grid) ≤
          target) :
    BinaryEndpointLevelVector
      (theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow) := by
  have hroot_le_grid_upper :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        root i ≤ returned (adjacentHighIndex i) - grid := by
    simpa using
      theorem32BackwardGridLowBisectionLevels_root_le_grid_upper_of_grid_upper_rate_le_target
        (n := n) (innerSteps := innerSteps)
        grid tFirst target lastLow hgrid_pos hfloor_le_grid_upper
        hgrid_upper_rate_le_target
  exact
    theorem32BackwardGridLowBisectionLevels_isEndpointLevelVector_of_root_le_grid_upper
      (n := n) (innerSteps := innerSteps) hn grid tFirst target lastLow
      htFirst_pos hgrid_pos hlastLow_lt_one hroot_le_grid_upper

/--
Source-grid returned-high domination reduction.  To show that every high
endpoint returned by the backward inner bisection dominates the corresponding
exact comparison high endpoint, it suffices to show that each exact successor
low endpoint lies below the low-endpoint root used for that successor
bisection call.
-/
theorem theorem32BackwardGridLowBisectionLevels_comparison_high_le_returned_high_of_comparison_low_le_root
    {n innerSteps : ℕ} (hn : 0 < n)
    (comparison : Fin (n + 2) → ℝ)
    (hcomparisonLevels : BinaryEndpointLevelVector comparison)
    (grid tFirst target lastLow : ℝ)
    (hcomparison_last_low_le_lastLow :
      comparison (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) ≤
        lastLow)
    (hroot_le_grid_upper :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        root i ≤ returned (adjacentHighIndex i) - grid)
    (hcomparison_low_le_root :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        comparison (adjacentLowIndex i) ≤ root i) :
    let returned :=
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow
    ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
      comparison (adjacentHighIndex i) ≤ returned (adjacentHighIndex i) := by
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  let root : Fin (n + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  dsimp
  intro i hi_first hi_last
  by_cases hnext_last : i.val + 1 = n
  · have hcomparison_high_eq :
        comparison (adjacentHighIndex i) =
          comparison (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) := by
      congr 1
      ext
      simp [adjacentHighIndex, adjacentLowIndex, lastAdjacentIndex]
      omega
    have hreturned_high_eq :
        returned (adjacentHighIndex i) = lastLow := by
      have hidx :
          adjacentHighIndex i =
            adjacentLowIndex (lastAdjacentIndex : Fin (n + 1)) := by
        ext
        simp [adjacentHighIndex, adjacentLowIndex, lastAdjacentIndex]
        omega
      rw [hidx]
      simpa [returned] using
        theorem32BackwardGridLowBisectionLevels_last_low
          (n := n) (innerSteps := innerSteps) hn grid tFirst target lastLow
    calc
      comparison (adjacentHighIndex i) =
          comparison
            (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) :=
        hcomparison_high_eq
      _ ≤ lastLow := hcomparison_last_low_le_lastLow
      _ = returned (adjacentHighIndex i) := hreturned_high_eq.symm
  · let j : Fin (n + 1) := ⟨i.val + 1, by omega⟩
    have hj_first : j.val ≠ 0 := by
      simp [j]
    have hj_last : j.val ≠ n := by
      simpa [j] using hnext_last
    have hcomparison_high_eq_low :
        comparison (adjacentHighIndex i) =
          comparison (adjacentLowIndex j) := by
      congr 1
    have hreturned_high_eq_low :
        returned (adjacentHighIndex i) = returned (adjacentLowIndex j) := by
      congr 1
    have hroot_nonneg : 0 ≤ root j := by
      exact
        (BinaryEndpointLevelVector_nonneg hcomparisonLevels
          (adjacentLowIndex j)).trans
          (hcomparison_low_le_root j hj_first hj_last)
    have hroot_le_upper :
        root j ≤
          (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget (root j))
            innerSteps 0 (returned (adjacentHighIndex j) - grid)).2 := by
      exact
        EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
          (n := innerSteps) hroot_nonneg
          (hroot_le_grid_upper j hj_first hj_last)
    have hreturnedLow :
        (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget (root j))
            innerSteps 0 (returned (adjacentHighIndex j) - grid)).2 =
          returned (adjacentLowIndex j) := by
      simpa [returned, root] using
        theorem32BackwardGridLowBisectionLevels_returnedLow
          (n := n) (innerSteps := innerSteps)
          grid tFirst target lastLow j hj_first hj_last
    calc
      comparison (adjacentHighIndex i) =
          comparison (adjacentLowIndex j) := hcomparison_high_eq_low
      _ ≤ root j := hcomparison_low_le_root j hj_first hj_last
      _ ≤
          (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget (root j))
            innerSteps 0 (returned (adjacentHighIndex j) - grid)).2 :=
        hroot_le_upper
      _ = returned (adjacentLowIndex j) := hreturnedLow
      _ = returned (adjacentHighIndex i) := hreturned_high_eq_low.symm

/--
One-interval comparison-root bridge.  If a returned high endpoint dominates
the exact comparison high endpoint, then the exact comparison low endpoint
lies below the clipped low-endpoint root selected for that returned high.
-/
theorem theorem32BackwardGridLowBisectionLevels_comparison_low_le_root_of_high_domination
    {n innerSteps : ℕ}
    (comparison : Fin (n + 2) → ℝ)
    (hcomparisonLevels : BinaryEndpointLevelVector comparison)
    (grid tFirst target lastLow : ℝ)
    (htFirst_pos : 0 < tFirst)
    (htarget_pos : 0 < target)
    (hfloor_le_comparison_low :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        tFirst ≤ comparison (adjacentLowIndex i))
    (htarget_lt_comparison_rate :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (comparison (adjacentHighIndex i))
            (comparison (adjacentLowIndex i)))
    (i : Fin (n + 1)) (hi_first : i.val ≠ 0) (hi_last : i.val ≠ n)
    (hcomparison_high_le :
      comparison (adjacentHighIndex i) ≤
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst
          target lastLow (adjacentHighIndex i))
    (hreturned_high_lt_one :
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst
          target lastLow (adjacentHighIndex i) < 1) :
    let returned :=
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst
        target lastLow
    let root : Fin (n + 1) → ℝ := fun j =>
      weightedBernoulliLowEndpointOfRateOrFloor
        (1 : ℝ) (1 : ℝ) tFirst
        (returned (adjacentHighIndex j)) target
    comparison (adjacentLowIndex i) ≤ root i := by
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  let root : Fin (n + 1) → ℝ := fun j =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex j)) target
  dsimp
  have hfloor_le_low :
      tFirst ≤ comparison (adjacentLowIndex i) :=
    hfloor_le_comparison_low i hi_first hi_last
  have hcomparison_low_lt_high :
      comparison (adjacentLowIndex i) <
        comparison (adjacentHighIndex i) :=
    hcomparisonLevels.2.2 i
  have hcomparison_low_le_returned_high :
      comparison (adjacentLowIndex i) ≤ returned (adjacentHighIndex i) :=
    hcomparison_low_lt_high.le.trans hcomparison_high_le
  have hcomparison_low_pos :
      0 < comparison (adjacentLowIndex i) :=
    htFirst_pos.trans_le hfloor_le_low
  have htarget_lt_returned_low :
      target <
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (returned (adjacentHighIndex i))
          (comparison (adjacentLowIndex i)) := by
    have hshrink :
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (comparison (adjacentHighIndex i))
          (comparison (adjacentLowIndex i)) ≤
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (returned (adjacentHighIndex i))
          (comparison (adjacentLowIndex i)) :=
      weightedBernoulliClosedThresholdRate_le_of_shrink
        (gHi := (1 : ℝ)) (gLo := (1 : ℝ))
        (pHi := returned (adjacentHighIndex i))
        (pLo := comparison (adjacentLowIndex i))
        (pHi' := comparison (adjacentHighIndex i))
        (pLo' := comparison (adjacentLowIndex i))
        (by norm_num) (by norm_num) (by norm_num)
        hcomparison_low_pos le_rfl hcomparison_low_lt_high.le
        hcomparison_high_le hreturned_high_lt_one
    exact (htarget_lt_comparison_rate i hi_first hi_last).trans_le hshrink
  have htarget_lt_floor_rate :
      target <
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (returned (adjacentHighIndex i)) tFirst := by
    have hshrink :
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (returned (adjacentHighIndex i))
          (comparison (adjacentLowIndex i)) ≤
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (returned (adjacentHighIndex i)) tFirst :=
      weightedBernoulliClosedThresholdRate_le_of_shrink
        (gHi := (1 : ℝ)) (gLo := (1 : ℝ))
        (pHi := returned (adjacentHighIndex i))
        (pLo := tFirst)
        (pHi' := returned (adjacentHighIndex i))
        (pLo' := comparison (adjacentLowIndex i))
        (by norm_num) (by norm_num) (by norm_num)
        htFirst_pos hfloor_le_low hcomparison_low_le_returned_high
        le_rfl hreturned_high_lt_one
    exact htarget_lt_returned_low.trans_le hshrink
  have hfeasible :
      WeightedBernoulliLowEndpointTargetFeasible
        (1 : ℝ) (1 : ℝ) tFirst
        (returned (adjacentHighIndex i)) target :=
    { hgHi := by norm_num
      hgLo := by norm_num
      hfloor0 := htFirst_pos
      hfloor_lt_hi :=
        hfloor_le_low.trans_lt
          (hcomparison_low_lt_high.trans_le hcomparison_high_le)
      hpHi1 := hreturned_high_lt_one
      htarget_pos := htarget_pos
      htarget_lt_floor := htarget_lt_floor_rate }
  exact
    le_weightedBernoulliLowEndpointOfRateOrFloor_of_feasible_target_le_rate
      (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
      (pHi := returned (adjacentHighIndex i)) (target := target)
      (x := comparison (adjacentLowIndex i))
      hfeasible hfloor_le_low hcomparison_low_le_returned_high
      (le_of_lt htarget_lt_returned_low)

/--
Weak one-interval comparison-root bridge.  This is the exact-hit-compatible
version of
`theorem32BackwardGridLowBisectionLevels_comparison_low_le_root_of_high_domination`:
the exact comparison rate may equal the target, so the clipped selector may
return the floor endpoint.
-/
theorem theorem32BackwardGridLowBisectionLevels_comparison_low_le_root_of_high_domination_weak
    {n innerSteps : ℕ}
    (comparison : Fin (n + 2) → ℝ)
    (hcomparisonLevels : BinaryEndpointLevelVector comparison)
    (grid tFirst target lastLow : ℝ)
    (htFirst_pos : 0 < tFirst)
    (htarget_pos : 0 < target)
    (hfloor_le_comparison_low :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        tFirst ≤ comparison (adjacentLowIndex i))
    (htarget_le_comparison_rate :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        target ≤
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (comparison (adjacentHighIndex i))
            (comparison (adjacentLowIndex i)))
    (i : Fin (n + 1)) (hi_first : i.val ≠ 0) (hi_last : i.val ≠ n)
    (hcomparison_high_le :
      comparison (adjacentHighIndex i) ≤
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst
          target lastLow (adjacentHighIndex i))
    (hreturned_high_lt_one :
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst
          target lastLow (adjacentHighIndex i) < 1) :
    let returned :=
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst
        target lastLow
    let root : Fin (n + 1) → ℝ := fun j =>
      weightedBernoulliLowEndpointOfRateOrFloor
        (1 : ℝ) (1 : ℝ) tFirst
        (returned (adjacentHighIndex j)) target
    comparison (adjacentLowIndex i) ≤ root i := by
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  let root : Fin (n + 1) → ℝ := fun j =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex j)) target
  dsimp
  have hfloor_le_low :
      tFirst ≤ comparison (adjacentLowIndex i) :=
    hfloor_le_comparison_low i hi_first hi_last
  have hcomparison_low_lt_high :
      comparison (adjacentLowIndex i) <
        comparison (adjacentHighIndex i) :=
    hcomparisonLevels.2.2 i
  have hcomparison_low_le_returned_high :
      comparison (adjacentLowIndex i) ≤ returned (adjacentHighIndex i) :=
    hcomparison_low_lt_high.le.trans hcomparison_high_le
  have hcomparison_low_pos :
      0 < comparison (adjacentLowIndex i) :=
    htFirst_pos.trans_le hfloor_le_low
  have htarget_le_returned_low :
      target ≤
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (returned (adjacentHighIndex i))
          (comparison (adjacentLowIndex i)) := by
    have hshrink :
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (comparison (adjacentHighIndex i))
          (comparison (adjacentLowIndex i)) ≤
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (returned (adjacentHighIndex i))
          (comparison (adjacentLowIndex i)) :=
      weightedBernoulliClosedThresholdRate_le_of_shrink
        (gHi := (1 : ℝ)) (gLo := (1 : ℝ))
        (pHi := returned (adjacentHighIndex i))
        (pLo := comparison (adjacentLowIndex i))
        (pHi' := comparison (adjacentHighIndex i))
        (pLo' := comparison (adjacentLowIndex i))
        (by norm_num) (by norm_num) (by norm_num)
        hcomparison_low_pos le_rfl hcomparison_low_lt_high.le
        hcomparison_high_le hreturned_high_lt_one
    exact (htarget_le_comparison_rate i hi_first hi_last).trans hshrink
  have hfloor_lt_high :
      tFirst < returned (adjacentHighIndex i) :=
    hfloor_le_low.trans_lt
      (hcomparison_low_lt_high.trans_le hcomparison_high_le)
  exact
    le_weightedBernoulliLowEndpointOfRateOrFloor_of_target_le_rate
      (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
      (pHi := returned (adjacentHighIndex i)) (target := target)
      (x := comparison (adjacentLowIndex i))
      (by norm_num) (by norm_num) htFirst_pos hfloor_lt_high
      hreturned_high_lt_one htarget_pos hfloor_le_low
      hcomparison_low_le_returned_high htarget_le_returned_low

/--
One-interval source-grid root-placement bridge from exact comparison
domination.  Once the returned high endpoint dominates the exact comparison
high endpoint, the low-endpoint shooting problem is feasible and the source
right endpoint `high - grid` lies to the right of the selected root.
-/
theorem theorem32BackwardGridLowBisectionLevels_root_le_grid_upper_of_high_domination
    {n innerSteps : ℕ}
    (comparison : Fin (n + 2) → ℝ)
    (hcomparisonLevels : BinaryEndpointLevelVector comparison)
    (grid tFirst lastLow : ℝ)
    (htFirst_pos : 0 < tFirst)
    (hgrid_pos : 0 < grid)
    (hgrid_lt_tFirst : grid < tFirst)
    (hlastLow_pos : 0 < lastLow)
    (hlastLow_lt_one : lastLow < 1)
    (hlastLow_le_one_sub_grid : lastLow ≤ 1 - grid)
    (hfloor_le_comparison_low :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        tFirst ≤ comparison (adjacentLowIndex i))
    (htarget_lt_comparison_rate :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        -Real.log lastLow <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (comparison (adjacentHighIndex i))
            (comparison (adjacentLowIndex i)))
    (i : Fin (n + 1)) (hi_first : i.val ≠ 0) (hi_last : i.val ≠ n)
    (hcomparison_high_le :
      comparison (adjacentHighIndex i) ≤
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst
          (-Real.log lastLow) lastLow (adjacentHighIndex i))
    (hreturned_high_lt_one :
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst
          (-Real.log lastLow) lastLow (adjacentHighIndex i) < 1) :
    let target : ℝ := -Real.log lastLow
    let returned :=
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow
    let root : Fin (n + 1) → ℝ := fun j =>
      weightedBernoulliLowEndpointOfRateOrFloor
        (1 : ℝ) (1 : ℝ) tFirst
        (returned (adjacentHighIndex j)) target
    root i ≤ returned (adjacentHighIndex i) - grid := by
  let target : ℝ := -Real.log lastLow
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  let root : Fin (n + 1) → ℝ := fun j =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex j)) target
  dsimp
  have htarget_pos : 0 < target := by
    have hlog_neg : Real.log lastLow < 0 :=
      Real.log_neg hlastLow_pos hlastLow_lt_one
    dsimp [target]
    linarith
  have hfloor_le_low :
      tFirst ≤ comparison (adjacentLowIndex i) :=
    hfloor_le_comparison_low i hi_first hi_last
  have hcomparison_low_lt_high :
      comparison (adjacentLowIndex i) <
        comparison (adjacentHighIndex i) :=
    hcomparisonLevels.2.2 i
  have hcomparison_low_le_returned_high :
      comparison (adjacentLowIndex i) ≤ returned (adjacentHighIndex i) :=
    hcomparison_low_lt_high.le.trans hcomparison_high_le
  have hcomparison_low_pos :
      0 < comparison (adjacentLowIndex i) :=
    htFirst_pos.trans_le hfloor_le_low
  have htarget_lt_returned_low :
      target <
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (returned (adjacentHighIndex i))
          (comparison (adjacentLowIndex i)) := by
    have hshrink :
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (comparison (adjacentHighIndex i))
          (comparison (adjacentLowIndex i)) ≤
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (returned (adjacentHighIndex i))
          (comparison (adjacentLowIndex i)) :=
      weightedBernoulliClosedThresholdRate_le_of_shrink
        (gHi := (1 : ℝ)) (gLo := (1 : ℝ))
        (pHi := returned (adjacentHighIndex i))
        (pLo := comparison (adjacentLowIndex i))
        (pHi' := comparison (adjacentHighIndex i))
        (pLo' := comparison (adjacentLowIndex i))
        (by norm_num) (by norm_num) (by norm_num)
        hcomparison_low_pos le_rfl hcomparison_low_lt_high.le
        hcomparison_high_le hreturned_high_lt_one
    exact (htarget_lt_comparison_rate i hi_first hi_last).trans_le hshrink
  have htarget_lt_floor_rate :
      target <
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (returned (adjacentHighIndex i)) tFirst := by
    have hshrink :
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (returned (adjacentHighIndex i))
          (comparison (adjacentLowIndex i)) ≤
        weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (returned (adjacentHighIndex i)) tFirst :=
      weightedBernoulliClosedThresholdRate_le_of_shrink
        (gHi := (1 : ℝ)) (gLo := (1 : ℝ))
        (pHi := returned (adjacentHighIndex i))
        (pLo := tFirst)
        (pHi' := returned (adjacentHighIndex i))
        (pLo' := comparison (adjacentLowIndex i))
        (by norm_num) (by norm_num) (by norm_num)
        htFirst_pos hfloor_le_low hcomparison_low_le_returned_high
        le_rfl hreturned_high_lt_one
    exact htarget_lt_returned_low.trans_le hshrink
  have hfeasible :
      WeightedBernoulliLowEndpointTargetFeasible
        (1 : ℝ) (1 : ℝ) tFirst
        (returned (adjacentHighIndex i)) target :=
    { hgHi := by norm_num
      hgLo := by norm_num
      hfloor0 := htFirst_pos
      hfloor_lt_hi :=
        hfloor_le_low.trans_lt
          (hcomparison_low_lt_high.trans_le hcomparison_high_le)
      hpHi1 := hreturned_high_lt_one
      htarget_pos := htarget_pos
      htarget_lt_floor := htarget_lt_floor_rate }
  have hupper_pos : 0 < returned (adjacentHighIndex i) - grid := by
    have hfloor_lt_high : tFirst < returned (adjacentHighIndex i) :=
      hfloor_le_low.trans_lt
        (hcomparison_low_lt_high.trans_le hcomparison_high_le)
    linarith
  have hlog_target :
      -Real.log (1 - grid) ≤ target := by
    have hone_sub_pos : 0 < 1 - grid :=
      hlastLow_pos.trans_le hlastLow_le_one_sub_grid
    have hlog_le : Real.log lastLow ≤ Real.log (1 - grid) :=
      Real.log_le_log hlastLow_pos hlastLow_le_one_sub_grid
    dsimp [target]
    linarith
  have hgrid_lt_one : grid < 1 := by
    have hone_sub_pos : 0 < 1 - grid :=
      hlastLow_pos.trans_le hlastLow_le_one_sub_grid
    linarith
  have hgrid_rate :
      weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (returned (adjacentHighIndex i))
          (returned (adjacentHighIndex i) - grid) ≤
        target := by
    have hrate :=
      weightedBernoulliClosedThresholdRate_one_one_le_neg_log_one_sub_width
        (pLo := returned (adjacentHighIndex i) - grid) (x := grid)
        (le_of_lt hupper_pos) (le_of_lt hgrid_pos)
        (by
          simpa [sub_add_cancel] using
            le_of_lt hreturned_high_lt_one)
        hgrid_lt_one
    have hrate' :
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i))
            (returned (adjacentHighIndex i) - grid) ≤
          -Real.log (1 - grid) := by
      simpa [sub_add_cancel] using hrate
    exact hrate'.trans hlog_target
  exact
    weightedBernoulliLowEndpointOfRateOrFloor_le_of_feasible_rate_le_target
      (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
      (pHi := returned (adjacentHighIndex i)) (target := target)
      (x := returned (adjacentHighIndex i) - grid)
      hfeasible hupper_pos (by linarith) hgrid_rate

/--
Backward source-grid comparison-root invariant.  The exact doubled chain lies
below the executable root selected at each interior interval once the outer
endpoint dominates the exact final low endpoint and every exact adjacent rate
is above the target.
-/
theorem theorem32BackwardGridLowBisectionLevels_comparison_low_le_root_of_nested_comparison
    {n innerSteps : ℕ} (hn : 1 < n)
    (comparison : Fin (n + 2) → ℝ)
    (hcomparisonLevels : BinaryEndpointLevelVector comparison)
    (grid tFirst target lastLow : ℝ)
    (htFirst_pos : 0 < tFirst)
    (htarget_pos : 0 < target)
    (hcomparison_last_low_le_lastLow :
      comparison (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) ≤
        lastLow)
    (hroot_le_grid_upper :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        root i ≤ returned (adjacentHighIndex i) - grid)
    (hreturned_high_lt_one :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        returned (adjacentHighIndex i) < 1)
    (hfloor_le_comparison_low :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        tFirst ≤ comparison (adjacentLowIndex i))
    (htarget_lt_comparison_rate :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (comparison (adjacentHighIndex i))
            (comparison (adjacentLowIndex i))) :
    let returned :=
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow
    let root : Fin (n + 1) → ℝ := fun i =>
      weightedBernoulliLowEndpointOfRateOrFloor
        (1 : ℝ) (1 : ℝ) tFirst
        (returned (adjacentHighIndex i)) target
    ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
      comparison (adjacentLowIndex i) ≤ root i := by
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  let root : Fin (n + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  have hstep :
      ∀ d : ℕ, 1 ≤ d → d < n →
        let i : Fin (n + 1) := ⟨n - d, by omega⟩
        comparison (adjacentHighIndex i) ≤ returned (adjacentHighIndex i) ∧
          comparison (adjacentLowIndex i) ≤ root i := by
    intro d
    refine Nat.strong_induction_on d ?_
    intro d ih hd_pos hd_lt
    let i : Fin (n + 1) := ⟨n - d, by omega⟩
    have hi_first : i.val ≠ 0 := by
      dsimp [i]
      omega
    have hi_last : i.val ≠ n := by
      dsimp [i]
      omega
    have hhigh :
        comparison (adjacentHighIndex i) ≤ returned (adjacentHighIndex i) := by
      by_cases hd_one : d = 1
      · subst d
        have hcomparison_high_eq :
            comparison (adjacentHighIndex i) =
              comparison
                (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) := by
          congr 1
          ext
          simp [i, adjacentHighIndex, adjacentLowIndex, lastAdjacentIndex]
          omega
        have hreturned_high_eq :
            returned (adjacentHighIndex i) = lastLow := by
          have hidx :
              adjacentHighIndex i =
                adjacentLowIndex (lastAdjacentIndex : Fin (n + 1)) := by
            ext
            simp [i, adjacentHighIndex, adjacentLowIndex, lastAdjacentIndex]
            omega
          rw [hidx]
          simpa [returned] using
            theorem32BackwardGridLowBisectionLevels_last_low
              (n := n) (innerSteps := innerSteps) (Nat.lt_of_succ_lt hn)
              grid tFirst target lastLow
        calc
          comparison (adjacentHighIndex i) =
              comparison
                (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) :=
            hcomparison_high_eq
          _ ≤ lastLow := hcomparison_last_low_le_lastLow
          _ = returned (adjacentHighIndex i) := hreturned_high_eq.symm
      · let j : Fin (n + 1) := ⟨n - (d - 1), by omega⟩
        have hj_first : j.val ≠ 0 := by
          dsimp [j]
          omega
        have hj_last : j.val ≠ n := by
          dsimp [j]
          omega
        have hd_pred_pos : 1 ≤ d - 1 := by omega
        have hd_pred_lt : d - 1 < n := by omega
        have hprev := ih (d - 1) (by omega) hd_pred_pos hd_pred_lt
        have hcomparison_high_eq_low :
            comparison (adjacentHighIndex i) =
              comparison (adjacentLowIndex j) := by
          congr 1
          ext
          simp [i, j, adjacentHighIndex, adjacentLowIndex]
          omega
        have hreturned_high_eq_low :
            returned (adjacentHighIndex i) = returned (adjacentLowIndex j) := by
          congr 1
          ext
          simp [i, j, adjacentHighIndex, adjacentLowIndex]
          omega
        have hroot_nonneg : 0 ≤ root j := by
          have hfloor_le_root :
              tFirst ≤ root j := by
            simpa [root] using
              (floor_le_weightedBernoulliLowEndpointOfRateOrFloor_unconditional
                (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
                (pHi := returned (adjacentHighIndex j)) (target := target))
          exact (le_of_lt htFirst_pos).trans hfloor_le_root
        have hroot_le_upper :
            root j ≤
              (EconCSLib.Optimization.realBisectionRun
                (EconCSLib.Optimization.realBisectionAboveTarget (root j))
                innerSteps 0 (returned (adjacentHighIndex j) - grid)).2 := by
          exact
            EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
              (n := innerSteps) hroot_nonneg
              (by
                simpa [returned, root] using
                  hroot_le_grid_upper j hj_first hj_last)
        have hreturnedLow :
            (EconCSLib.Optimization.realBisectionRun
                (EconCSLib.Optimization.realBisectionAboveTarget (root j))
                innerSteps 0 (returned (adjacentHighIndex j) - grid)).2 =
              returned (adjacentLowIndex j) := by
          simpa [returned, root] using
            theorem32BackwardGridLowBisectionLevels_returnedLow
              (n := n) (innerSteps := innerSteps)
              grid tFirst target lastLow j hj_first hj_last
        calc
          comparison (adjacentHighIndex i) =
              comparison (adjacentLowIndex j) := hcomparison_high_eq_low
          _ ≤ root j := hprev.2
          _ ≤
              (EconCSLib.Optimization.realBisectionRun
                (EconCSLib.Optimization.realBisectionAboveTarget (root j))
                innerSteps 0 (returned (adjacentHighIndex j) - grid)).2 :=
            hroot_le_upper
          _ = returned (adjacentLowIndex j) := hreturnedLow
          _ = returned (adjacentHighIndex i) := hreturned_high_eq_low.symm
    have hlow :
        comparison (adjacentLowIndex i) ≤ root i :=
      theorem32BackwardGridLowBisectionLevels_comparison_low_le_root_of_high_domination
        (n := n) (innerSteps := innerSteps)
        comparison hcomparisonLevels grid tFirst target lastLow
        htFirst_pos htarget_pos hfloor_le_comparison_low
        htarget_lt_comparison_rate i hi_first hi_last hhigh
        (hreturned_high_lt_one i hi_first hi_last)
    exact ⟨hhigh, hlow⟩
  dsimp
  intro i hi_first hi_last
  have hd_pos : 1 ≤ n - i.val := by
    omega
  have hd_lt : n - i.val < n := by
    have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi_first
    omega
  have hi_eq :
      (⟨n - (n - i.val), by omega⟩ : Fin (n + 1)) = i := by
    have hval : n - (n - i.val) = i.val := by
      omega
    ext
    exact hval
  have h := hstep (n - i.val) hd_pos hd_lt
  simpa [returned, root, hi_eq] using h.2

/--
Weak backward source-grid comparison-root invariant.  This exact-hit-compatible
variant only assumes non-strict target domination by the exact doubled
comparison rates.
-/
theorem theorem32BackwardGridLowBisectionLevels_comparison_low_le_root_of_nested_comparison_weak
    {n innerSteps : ℕ} (hn : 1 < n)
    (comparison : Fin (n + 2) → ℝ)
    (hcomparisonLevels : BinaryEndpointLevelVector comparison)
    (grid tFirst target lastLow : ℝ)
    (htFirst_pos : 0 < tFirst)
    (htarget_pos : 0 < target)
    (hcomparison_last_low_le_lastLow :
      comparison (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) ≤
        lastLow)
    (hroot_le_grid_upper :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        root i ≤ returned (adjacentHighIndex i) - grid)
    (hreturned_high_lt_one :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        returned (adjacentHighIndex i) < 1)
    (hfloor_le_comparison_low :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        tFirst ≤ comparison (adjacentLowIndex i))
    (htarget_le_comparison_rate :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        target ≤
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (comparison (adjacentHighIndex i))
            (comparison (adjacentLowIndex i))) :
    let returned :=
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow
    let root : Fin (n + 1) → ℝ := fun i =>
      weightedBernoulliLowEndpointOfRateOrFloor
        (1 : ℝ) (1 : ℝ) tFirst
        (returned (adjacentHighIndex i)) target
    ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
      comparison (adjacentLowIndex i) ≤ root i := by
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  let root : Fin (n + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  have hstep :
      ∀ d : ℕ, 1 ≤ d → d < n →
        let i : Fin (n + 1) := ⟨n - d, by omega⟩
        comparison (adjacentHighIndex i) ≤ returned (adjacentHighIndex i) ∧
          comparison (adjacentLowIndex i) ≤ root i := by
    intro d
    refine Nat.strong_induction_on d ?_
    intro d ih hd_pos hd_lt
    let i : Fin (n + 1) := ⟨n - d, by omega⟩
    have hi_first : i.val ≠ 0 := by
      dsimp [i]
      omega
    have hi_last : i.val ≠ n := by
      dsimp [i]
      omega
    have hhigh :
        comparison (adjacentHighIndex i) ≤ returned (adjacentHighIndex i) := by
      by_cases hd_one : d = 1
      · subst d
        have hcomparison_high_eq :
            comparison (adjacentHighIndex i) =
              comparison
                (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) := by
          congr 1
          ext
          simp [i, adjacentHighIndex, adjacentLowIndex, lastAdjacentIndex]
          omega
        have hreturned_high_eq :
            returned (adjacentHighIndex i) = lastLow := by
          have hidx :
              adjacentHighIndex i =
                adjacentLowIndex (lastAdjacentIndex : Fin (n + 1)) := by
            ext
            simp [i, adjacentHighIndex, adjacentLowIndex, lastAdjacentIndex]
            omega
          rw [hidx]
          simpa [returned] using
            theorem32BackwardGridLowBisectionLevels_last_low
              (n := n) (innerSteps := innerSteps) (Nat.lt_of_succ_lt hn)
              grid tFirst target lastLow
        calc
          comparison (adjacentHighIndex i) =
              comparison
                (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) :=
            hcomparison_high_eq
          _ ≤ lastLow := hcomparison_last_low_le_lastLow
          _ = returned (adjacentHighIndex i) := hreturned_high_eq.symm
      · let j : Fin (n + 1) := ⟨n - (d - 1), by omega⟩
        have hj_first : j.val ≠ 0 := by
          dsimp [j]
          omega
        have hj_last : j.val ≠ n := by
          dsimp [j]
          omega
        have hd_pred_pos : 1 ≤ d - 1 := by omega
        have hd_pred_lt : d - 1 < n := by omega
        have hprev := ih (d - 1) (by omega) hd_pred_pos hd_pred_lt
        have hcomparison_high_eq_low :
            comparison (adjacentHighIndex i) =
              comparison (adjacentLowIndex j) := by
          congr 1
          ext
          simp [i, j, adjacentHighIndex, adjacentLowIndex]
          omega
        have hreturned_high_eq_low :
            returned (adjacentHighIndex i) = returned (adjacentLowIndex j) := by
          congr 1
          ext
          simp [i, j, adjacentHighIndex, adjacentLowIndex]
          omega
        have hroot_nonneg : 0 ≤ root j := by
          have hfloor_le_root :
              tFirst ≤ root j := by
            simpa [root] using
              (floor_le_weightedBernoulliLowEndpointOfRateOrFloor_unconditional
                (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
                (pHi := returned (adjacentHighIndex j)) (target := target))
          exact (le_of_lt htFirst_pos).trans hfloor_le_root
        have hroot_le_upper :
            root j ≤
              (EconCSLib.Optimization.realBisectionRun
                (EconCSLib.Optimization.realBisectionAboveTarget (root j))
                innerSteps 0 (returned (adjacentHighIndex j) - grid)).2 := by
          exact
            EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
              (n := innerSteps) hroot_nonneg
              (by
                simpa [returned, root] using
                  hroot_le_grid_upper j hj_first hj_last)
        have hreturnedLow :
            (EconCSLib.Optimization.realBisectionRun
                (EconCSLib.Optimization.realBisectionAboveTarget (root j))
                innerSteps 0 (returned (adjacentHighIndex j) - grid)).2 =
              returned (adjacentLowIndex j) := by
          simpa [returned, root] using
            theorem32BackwardGridLowBisectionLevels_returnedLow
              (n := n) (innerSteps := innerSteps)
              grid tFirst target lastLow j hj_first hj_last
        calc
          comparison (adjacentHighIndex i) =
              comparison (adjacentLowIndex j) := hcomparison_high_eq_low
          _ ≤ root j := hprev.2
          _ ≤
              (EconCSLib.Optimization.realBisectionRun
                (EconCSLib.Optimization.realBisectionAboveTarget (root j))
                innerSteps 0 (returned (adjacentHighIndex j) - grid)).2 :=
            hroot_le_upper
          _ = returned (adjacentLowIndex j) := hreturnedLow
          _ = returned (adjacentHighIndex i) := hreturned_high_eq_low.symm
    have hlow :
        comparison (adjacentLowIndex i) ≤ root i :=
      theorem32BackwardGridLowBisectionLevels_comparison_low_le_root_of_high_domination_weak
        (n := n) (innerSteps := innerSteps)
        comparison hcomparisonLevels grid tFirst target lastLow
        htFirst_pos htarget_pos hfloor_le_comparison_low
        htarget_le_comparison_rate i hi_first hi_last hhigh
        (hreturned_high_lt_one i hi_first hi_last)
    exact ⟨hhigh, hlow⟩
  dsimp
  intro i hi_first hi_last
  have hd_pos : 1 ≤ n - i.val := by
    omega
  have hd_lt : n - i.val < n := by
    have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi_first
    omega
  have hi_eq :
      (⟨n - (n - i.val), by omega⟩ : Fin (n + 1)) = i := by
    have hval : n - (n - i.val) = i.val := by
      omega
    ext
    exact hval
  have h := hstep (n - i.val) hd_pos hd_lt
  simpa [returned, root, hi_eq] using h.2

/--
Backward source-grid root-placement invariant from exact comparison rates.
This carries returned-high domination, support, exact-low/root domination, and
root placement in one induction, avoiding a separate root-placement
certificate for the calculated Theorem 3.2 recursion.
-/
theorem theorem32BackwardGridLowBisectionLevels_root_le_grid_upper_of_nested_comparison
    {n innerSteps : ℕ} (hn : 1 < n)
    (comparison : Fin (n + 2) → ℝ)
    (hcomparisonLevels : BinaryEndpointLevelVector comparison)
    (grid tFirst lastLow : ℝ)
    (htFirst_pos : 0 < tFirst)
    (hgrid_pos : 0 < grid)
    (hgrid_lt_tFirst : grid < tFirst)
    (hlastLow_pos : 0 < lastLow)
    (hlastLow_lt_one : lastLow < 1)
    (hlastLow_le_one_sub_grid : lastLow ≤ 1 - grid)
    (hcomparison_last_low_le_lastLow :
      comparison (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) ≤
        lastLow)
    (hfloor_le_comparison_low :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        tFirst ≤ comparison (adjacentLowIndex i))
    (htarget_lt_comparison_rate :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        -Real.log lastLow <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (comparison (adjacentHighIndex i))
            (comparison (adjacentLowIndex i))) :
    let target : ℝ := -Real.log lastLow
    let returned :=
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow
    let root : Fin (n + 1) → ℝ := fun i =>
      weightedBernoulliLowEndpointOfRateOrFloor
        (1 : ℝ) (1 : ℝ) tFirst
        (returned (adjacentHighIndex i)) target
    ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
      root i ≤ returned (adjacentHighIndex i) - grid := by
  let target : ℝ := -Real.log lastLow
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  let root : Fin (n + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  have htarget_pos : 0 < target := by
    have hlog_neg : Real.log lastLow < 0 :=
      Real.log_neg hlastLow_pos hlastLow_lt_one
    dsimp [target]
    linarith
  have hstep :
      ∀ d : ℕ, 1 ≤ d → d < n →
        let i : Fin (n + 1) := ⟨n - d, by omega⟩
        comparison (adjacentHighIndex i) ≤ returned (adjacentHighIndex i) ∧
          returned (adjacentHighIndex i) < 1 ∧
          comparison (adjacentLowIndex i) ≤ root i ∧
          root i ≤ returned (adjacentHighIndex i) - grid := by
    intro d
    refine Nat.strong_induction_on d ?_
    intro d ih hd_pos hd_lt
    let i : Fin (n + 1) := ⟨n - d, by omega⟩
    have hi_first : i.val ≠ 0 := by
      dsimp [i]
      omega
    have hi_last : i.val ≠ n := by
      dsimp [i]
      omega
    have hhigh :
        comparison (adjacentHighIndex i) ≤ returned (adjacentHighIndex i) := by
      by_cases hd_one : d = 1
      · subst d
        have hcomparison_high_eq :
            comparison (adjacentHighIndex i) =
              comparison
                (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) := by
          congr 1
          ext
          simp [i, adjacentHighIndex, adjacentLowIndex, lastAdjacentIndex]
          omega
        have hreturned_high_eq :
            returned (adjacentHighIndex i) = lastLow := by
          have hidx :
              adjacentHighIndex i =
                adjacentLowIndex (lastAdjacentIndex : Fin (n + 1)) := by
            ext
            simp [i, adjacentHighIndex, adjacentLowIndex, lastAdjacentIndex]
            omega
          rw [hidx]
          simpa [returned, target] using
            theorem32BackwardGridLowBisectionLevels_last_low
              (n := n) (innerSteps := innerSteps) (Nat.lt_of_succ_lt hn)
              grid tFirst target lastLow
        calc
          comparison (adjacentHighIndex i) =
              comparison
                (adjacentLowIndex (lastAdjacentIndex : Fin (n + 1))) :=
            hcomparison_high_eq
          _ ≤ lastLow := hcomparison_last_low_le_lastLow
          _ = returned (adjacentHighIndex i) := hreturned_high_eq.symm
      · let j : Fin (n + 1) := ⟨n - (d - 1), by omega⟩
        have hj_first : j.val ≠ 0 := by
          dsimp [j]
          omega
        have hj_last : j.val ≠ n := by
          dsimp [j]
          omega
        have hd_pred_pos : 1 ≤ d - 1 := by omega
        have hd_pred_lt : d - 1 < n := by omega
        have hprev := ih (d - 1) (by omega) hd_pred_pos hd_pred_lt
        have hcomparison_high_eq_low :
            comparison (adjacentHighIndex i) =
              comparison (adjacentLowIndex j) := by
          congr 1
          ext
          simp [i, j, adjacentHighIndex, adjacentLowIndex]
          omega
        have hreturned_high_eq_low :
            returned (adjacentHighIndex i) = returned (adjacentLowIndex j) := by
          congr 1
          ext
          simp [i, j, adjacentHighIndex, adjacentLowIndex]
          omega
        have hroot_nonneg : 0 ≤ root j := by
          have hfloor_le_root :
              tFirst ≤ root j := by
            simpa [root] using
              (floor_le_weightedBernoulliLowEndpointOfRateOrFloor_unconditional
                (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
                (pHi := returned (adjacentHighIndex j)) (target := target))
          exact (le_of_lt htFirst_pos).trans hfloor_le_root
        have hroot_le_upper :
            root j ≤
              (EconCSLib.Optimization.realBisectionRun
                (EconCSLib.Optimization.realBisectionAboveTarget (root j))
                innerSteps 0 (returned (adjacentHighIndex j) - grid)).2 := by
          exact
            EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
              (n := innerSteps) hroot_nonneg hprev.2.2.2
        have hreturnedLow :
            (EconCSLib.Optimization.realBisectionRun
                (EconCSLib.Optimization.realBisectionAboveTarget (root j))
                innerSteps 0 (returned (adjacentHighIndex j) - grid)).2 =
              returned (adjacentLowIndex j) := by
          simpa [returned, root, target] using
            theorem32BackwardGridLowBisectionLevels_returnedLow
              (n := n) (innerSteps := innerSteps)
              grid tFirst target lastLow j hj_first hj_last
        calc
          comparison (adjacentHighIndex i) =
              comparison (adjacentLowIndex j) := hcomparison_high_eq_low
          _ ≤ root j := hprev.2.2.1
          _ ≤
              (EconCSLib.Optimization.realBisectionRun
                (EconCSLib.Optimization.realBisectionAboveTarget (root j))
                innerSteps 0 (returned (adjacentHighIndex j) - grid)).2 :=
            hroot_le_upper
          _ = returned (adjacentLowIndex j) := hreturnedLow
          _ = returned (adjacentHighIndex i) := hreturned_high_eq_low.symm
    have hhigh_lt_one :
        returned (adjacentHighIndex i) < 1 := by
      by_cases hd_one : d = 1
      · subst d
        have hreturned_high_eq :
            returned (adjacentHighIndex i) = lastLow := by
          have hidx :
              adjacentHighIndex i =
                adjacentLowIndex (lastAdjacentIndex : Fin (n + 1)) := by
            ext
            simp [i, adjacentHighIndex, adjacentLowIndex, lastAdjacentIndex]
            omega
          rw [hidx]
          simpa [returned, target] using
            theorem32BackwardGridLowBisectionLevels_last_low
              (n := n) (innerSteps := innerSteps) (Nat.lt_of_succ_lt hn)
              grid tFirst target lastLow
        simpa [hreturned_high_eq] using hlastLow_lt_one
      · let j : Fin (n + 1) := ⟨n - (d - 1), by omega⟩
        have hj_first : j.val ≠ 0 := by
          dsimp [j]
          omega
        have hj_last : j.val ≠ n := by
          dsimp [j]
          omega
        have hd_pred_pos : 1 ≤ d - 1 := by omega
        have hd_pred_lt : d - 1 < n := by omega
        have hprev := ih (d - 1) (by omega) hd_pred_pos hd_pred_lt
        have hreturned_high_eq_low :
            returned (adjacentHighIndex i) = returned (adjacentLowIndex j) := by
          congr 1
          ext
          simp [i, j, adjacentHighIndex, adjacentLowIndex]
          omega
        have hroot_nonneg : 0 ≤ root j := by
          have hfloor_le_root :
              tFirst ≤ root j := by
            simpa [root] using
              (floor_le_weightedBernoulliLowEndpointOfRateOrFloor_unconditional
                (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
                (pHi := returned (adjacentHighIndex j)) (target := target))
          exact (le_of_lt htFirst_pos).trans hfloor_le_root
        have hupper_nonneg : 0 ≤ returned (adjacentHighIndex j) - grid :=
          hroot_nonneg.trans hprev.2.2.2
        have hrun_le :
            (EconCSLib.Optimization.realBisectionRun
                (EconCSLib.Optimization.realBisectionAboveTarget (root j))
                innerSteps 0 (returned (adjacentHighIndex j) - grid)).2 ≤
              returned (adjacentHighIndex j) - grid :=
          EconCSLib.Optimization.realBisectionRun_upper_le_initial
            (EconCSLib.Optimization.realBisectionAboveTarget (root j))
            hupper_nonneg
        have hreturnedLow :
            (EconCSLib.Optimization.realBisectionRun
                (EconCSLib.Optimization.realBisectionAboveTarget (root j))
                innerSteps 0 (returned (adjacentHighIndex j) - grid)).2 =
              returned (adjacentLowIndex j) := by
          simpa [returned, root, target] using
            theorem32BackwardGridLowBisectionLevels_returnedLow
              (n := n) (innerSteps := innerSteps)
              grid tFirst target lastLow j hj_first hj_last
        have hlow_le :
            returned (adjacentLowIndex j) ≤
              returned (adjacentHighIndex j) - grid := by
          simpa [hreturnedLow] using hrun_le
        calc
          returned (adjacentHighIndex i) =
              returned (adjacentLowIndex j) := hreturned_high_eq_low
          _ ≤ returned (adjacentHighIndex j) - grid := hlow_le
          _ < returned (adjacentHighIndex j) := by linarith
          _ < 1 := hprev.2.1
    have hlow :
        comparison (adjacentLowIndex i) ≤ root i :=
      theorem32BackwardGridLowBisectionLevels_comparison_low_le_root_of_high_domination
        (n := n) (innerSteps := innerSteps)
        comparison hcomparisonLevels grid tFirst target lastLow
        htFirst_pos htarget_pos hfloor_le_comparison_low
        (by simpa [target] using htarget_lt_comparison_rate)
        i hi_first hi_last hhigh hhigh_lt_one
    have hroot :
        root i ≤ returned (adjacentHighIndex i) - grid := by
      simpa [target, returned, root] using
        theorem32BackwardGridLowBisectionLevels_root_le_grid_upper_of_high_domination
          (n := n) (innerSteps := innerSteps)
          comparison hcomparisonLevels grid tFirst lastLow
          htFirst_pos hgrid_pos hgrid_lt_tFirst hlastLow_pos
          hlastLow_lt_one hlastLow_le_one_sub_grid
          hfloor_le_comparison_low htarget_lt_comparison_rate
          i hi_first hi_last
          (by simpa [target, returned] using hhigh)
          (by simpa [target, returned] using hhigh_lt_one)
    exact ⟨hhigh, hhigh_lt_one, hlow, hroot⟩
  dsimp
  intro i hi_first hi_last
  have hd_pos : 1 ≤ n - i.val := by
    omega
  have hd_lt : n - i.val < n := by
    have hi_pos : 0 < i.val := Nat.pos_of_ne_zero hi_first
    omega
  have hi_eq :
      (⟨n - (n - i.val), by omega⟩ : Fin (n + 1)) = i := by
    have hval : n - (n - i.val) = i.val := by
      omega
    ext
    exact hval
  have h := hstep (n - i.val) hd_pos hd_lt
  simpa [target, returned, root, hi_eq] using h.2.2.2

/--
Source-grid root-placement bridge for a feasible `BisectNextLevel` call.
Compared with
`theorem32BackwardGridLowBisectionLevels_root_le_grid_upper_of_grid_upper_rate_le_target`,
this version does not require the caller to separately prove that the fixed
floor lies below `high - grid`: feasibility of the low-endpoint shooting
problem plus positivity of the right endpoint and the rate comparison at that
right endpoint force the selected root into the source bisection interval.
-/
theorem theorem32BackwardGridLowBisectionLevels_root_le_grid_upper_of_feasible_grid_upper_rate_le_target
    {n innerSteps : ℕ} (grid tFirst target lastLow : ℝ)
    (hgrid_pos : 0 < grid)
    (hfeasible :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hgrid_upper_pos :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        0 < returned (adjacentHighIndex i) - grid)
    (hgrid_upper_rate_le_target :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i))
            (returned (adjacentHighIndex i) - grid) ≤
          target) :
    let returned :=
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow
    let root : Fin (n + 1) → ℝ := fun i =>
      weightedBernoulliLowEndpointOfRateOrFloor
        (1 : ℝ) (1 : ℝ) tFirst
        (returned (adjacentHighIndex i)) target
    ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
      root i ≤ returned (adjacentHighIndex i) - grid := by
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  let root : Fin (n + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  dsimp
  intro i hi_first hi_last
  exact
    weightedBernoulliLowEndpointOfRateOrFloor_le_of_feasible_rate_le_target
      (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
      (pHi := returned (adjacentHighIndex i)) (target := target)
      (x := returned (adjacentHighIndex i) - grid)
      (by simpa [returned] using hfeasible i hi_first hi_last)
      (by simpa [returned] using hgrid_upper_pos i hi_first hi_last)
      (by linarith [hgrid_pos])
      (by
        simpa [returned] using
          hgrid_upper_rate_le_target i hi_first hi_last)

/--
The source-grid backward recursion stays below the final endpoint once each
inner interval `[0, high - grid]` is nonempty.  This is the scalar recursion
form; the `Fin`-indexed endpoint-vector version below packages the same
invariant for the calculated Theorem 3.2 level vector.
-/
theorem theorem32BackwardGridLowBisectionFromTop_lt_one_of_grid_upper_pos
    {innerSteps maxD : ℕ} (grid tFirst target lastLow : ℝ)
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (hgrid_upper_pos :
      ∀ d : ℕ, 1 ≤ d → d < maxD →
        0 <
          theorem32BackwardGridLowBisectionFromTop innerSteps grid tFirst
            target lastLow d - grid) :
    ∀ d : ℕ, 1 ≤ d → d ≤ maxD →
      theorem32BackwardGridLowBisectionFromTop innerSteps grid tFirst target
        lastLow d < 1 := by
  intro d hd_pos hd_le
  induction d with
  | zero =>
      omega
  | succ d ih =>
      cases d with
      | zero =>
          simpa [theorem32BackwardGridLowBisectionFromTop] using hlastLow_lt_one
      | succ d =>
          have hprev :
              theorem32BackwardGridLowBisectionFromTop innerSteps grid tFirst
                target lastLow (d + 1) < 1 := by
            exact ih (by omega) (by omega)
          have hupper_nonneg :
              0 ≤
                theorem32BackwardGridLowBisectionFromTop innerSteps grid
                  tFirst target lastLow (d + 1) - grid := by
            exact le_of_lt (hgrid_upper_pos (d + 1) (by omega) (by omega))
          have hrun_le :
              (EconCSLib.Optimization.realBisectionRun
                (EconCSLib.Optimization.realBisectionAboveTarget
                  (weightedBernoulliLowEndpointOfRateOrFloor
                    (1 : ℝ) (1 : ℝ) tFirst
                    (theorem32BackwardGridLowBisectionFromTop innerSteps grid
                      tFirst target lastLow (d + 1)) target))
                innerSteps 0
                (theorem32BackwardGridLowBisectionFromTop innerSteps grid
                  tFirst target lastLow (d + 1) - grid)).2 ≤
                theorem32BackwardGridLowBisectionFromTop innerSteps grid
                  tFirst target lastLow (d + 1) - grid :=
            EconCSLib.Optimization.realBisectionRun_upper_le_initial
              (EconCSLib.Optimization.realBisectionAboveTarget
                (weightedBernoulliLowEndpointOfRateOrFloor
                  (1 : ℝ) (1 : ℝ) tFirst
                  (theorem32BackwardGridLowBisectionFromTop innerSteps grid
                    tFirst target lastLow (d + 1)) target))
              hupper_nonneg
          have hcurrent_le :
              theorem32BackwardGridLowBisectionFromTop innerSteps grid tFirst
                  target lastLow (d + 2) ≤
                theorem32BackwardGridLowBisectionFromTop innerSteps grid
                  tFirst target lastLow (d + 1) - grid := by
            simpa [theorem32BackwardGridLowBisectionFromTop] using hrun_le
          linarith

/--
Every interior high endpoint of the calculated source-grid level vector is
strictly below `1`, assuming each source-grid inner bisection interval is
nonempty.  This discharges the support-side `pHi < 1` fact needed by later
Theorem 3.2 feasibility bridges.
-/
theorem theorem32BackwardGridLowBisectionLevels_high_lt_one_of_grid_upper_pos
    {n innerSteps : ℕ} (grid tFirst target lastLow : ℝ)
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (hgrid_upper_pos :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        0 < returned (adjacentHighIndex i) - grid) :
    let returned :=
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow
    ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
      returned (adjacentHighIndex i) < 1 := by
  let seq : ℕ → ℝ :=
    theorem32BackwardGridLowBisectionFromTop innerSteps grid tFirst target
      lastLow
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  have hseq_grid :
      ∀ d : ℕ, 1 ≤ d → d < n →
        0 < seq d - grid := by
    intro d hd_pos hd_lt
    let i : Fin (n + 1) := ⟨n - d, by omega⟩
    have hi_first : i.val ≠ 0 := by
      dsimp [i]
      omega
    have hi_last : i.val ≠ n := by
      dsimp [i]
      omega
    have hhigh :
        returned (adjacentHighIndex i) = seq d := by
      dsimp [returned, seq, theorem32BackwardGridLowBisectionLevels,
        adjacentHighIndex, i]
      simp
      congr 1
      omega
    simpa [returned, hhigh] using hgrid_upper_pos i hi_first hi_last
  have hseq_lt_one :
      ∀ d : ℕ, 1 ≤ d → d ≤ n →
        seq d < 1 := by
    intro d hd_pos hd_le
    simpa [seq] using
      theorem32BackwardGridLowBisectionFromTop_lt_one_of_grid_upper_pos
        (innerSteps := innerSteps) (maxD := n)
        grid tFirst target lastLow hgrid_pos hlastLow_lt_one
        (by simpa [seq] using hseq_grid) d hd_pos hd_le
  dsimp
  intro i hi_first hi_last
  have hd_pos : 1 ≤ n - i.val := by omega
  have hd_le : n - i.val ≤ n := by omega
  have hhigh :
      returned (adjacentHighIndex i) = seq (n - i.val) := by
    dsimp [returned, seq, theorem32BackwardGridLowBisectionLevels,
      adjacentHighIndex]
    simp
  simpa [returned, hhigh] using hseq_lt_one (n - i.val) hd_pos hd_le

/--
Source-grid right-endpoint rate check for Theorem 3.2.  If the final outer
endpoint is at most `1 - grid`, then every inner bisection upper endpoint
`high - grid` has equal-weight closed rate no larger than the final target
`-log(lastLow)`.
-/
theorem theorem32BackwardGridLowBisectionLevels_grid_upper_rate_le_target_of_lastLow_le_one_sub_grid
    {n innerSteps : ℕ} (grid tFirst lastLow : ℝ)
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (hlastLow_pos : 0 < lastLow)
    (hlastLow_le_one_sub_grid : lastLow ≤ 1 - grid)
    (hgrid_upper_pos :
      let target : ℝ := -Real.log lastLow
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        0 < returned (adjacentHighIndex i) - grid) :
    let target : ℝ := -Real.log lastLow
    let returned :=
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow
    ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
      weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ)
          (returned (adjacentHighIndex i))
          (returned (adjacentHighIndex i) - grid) ≤
        target := by
  let target : ℝ := -Real.log lastLow
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  have hhigh_lt_one :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        returned (adjacentHighIndex i) < 1 := by
    simpa [target, returned] using
      theorem32BackwardGridLowBisectionLevels_high_lt_one_of_grid_upper_pos
        (n := n) (innerSteps := innerSteps)
        grid tFirst target lastLow hgrid_pos hlastLow_lt_one
        (by simpa [target, returned] using hgrid_upper_pos)
  have hlog_target :
      -Real.log (1 - grid) ≤ target := by
    have hgrid_lt_one : grid < 1 := by
      have hpos_one_sub_grid : 0 < 1 - grid :=
        hlastLow_pos.trans_le hlastLow_le_one_sub_grid
      linarith
    have hone_sub_pos : 0 < 1 - grid := by linarith
    have hlog_le : Real.log lastLow ≤ Real.log (1 - grid) :=
      Real.log_le_log hlastLow_pos hlastLow_le_one_sub_grid
    dsimp [target]
    linarith
  dsimp
  intro i hi_first hi_last
  let high : ℝ := returned (adjacentHighIndex i)
  have hupper_pos : 0 < high - grid := by
    simpa [target, returned, high] using
      hgrid_upper_pos i hi_first hi_last
  have hhigh_lt : high < 1 := by
    simpa [returned, high] using hhigh_lt_one i hi_first hi_last
  have hgrid_lt_one : grid < 1 := by linarith
  have hwidth_rate :
      weightedBernoulliClosedThresholdRate
          (1 : ℝ) (1 : ℝ) high (high - grid) ≤
        -Real.log (1 - grid) := by
    have hrate :=
      weightedBernoulliClosedThresholdRate_one_one_le_neg_log_one_sub_width
        (pLo := high - grid) (x := grid)
        (le_of_lt hupper_pos) (le_of_lt hgrid_pos)
        (by simpa [high, sub_add_cancel] using le_of_lt hhigh_lt)
        hgrid_lt_one
    simpa [sub_add_cancel] using hrate
  exact hwidth_rate.trans hlog_target

/--
Source-grid floor/high support invariant for the calculated Theorem 3.2
recursion.  If the final outer endpoint is above the fixed first floor, every
source-grid bisection interval is nonempty, and the source floor-rate
strictness holds, then every interior high endpoint remains above the fixed
floor.
-/
theorem theorem32BackwardGridLowBisectionLevels_floor_lt_high_of_lastLow_gt_floor
    {n innerSteps : ℕ} (grid tFirst lastLow : ℝ)
    (htFirst_pos : 0 < tFirst)
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (hlastLow_pos : 0 < lastLow)
    (hlastLow_le_one_sub_grid : lastLow ≤ 1 - grid)
    (htFirst_lt_lastLow : tFirst < lastLow)
    (hgrid_upper_pos :
      let target : ℝ := -Real.log lastLow
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        0 < returned (adjacentHighIndex i) - grid)
    (htarget_lt_floor_rate :
      let target : ℝ := -Real.log lastLow
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst) :
    let target : ℝ := -Real.log lastLow
    let returned :=
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow
    ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
      tFirst < returned (adjacentHighIndex i) := by
  let target : ℝ := -Real.log lastLow
  let seq : ℕ → ℝ :=
    theorem32BackwardGridLowBisectionFromTop innerSteps grid tFirst target
      lastLow
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  have htarget_pos : 0 < target := by
    have hlog_neg : Real.log lastLow < 0 :=
      Real.log_neg hlastLow_pos hlastLow_lt_one
    dsimp [target]
    linarith
  have hhigh_lt_one :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        returned (adjacentHighIndex i) < 1 := by
    simpa [target, returned] using
      theorem32BackwardGridLowBisectionLevels_high_lt_one_of_grid_upper_pos
        (n := n) (innerSteps := innerSteps)
        grid tFirst target lastLow hgrid_pos hlastLow_lt_one
        (by simpa [target, returned] using hgrid_upper_pos)
  have hgrid_upper_rate_le_target :
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i))
            (returned (adjacentHighIndex i) - grid) ≤
          target := by
    simpa [target, returned] using
      theorem32BackwardGridLowBisectionLevels_grid_upper_rate_le_target_of_lastLow_le_one_sub_grid
        (n := n) (innerSteps := innerSteps)
        grid tFirst lastLow hgrid_pos hlastLow_lt_one hlastLow_pos
        hlastLow_le_one_sub_grid
        (by simpa [target, returned] using hgrid_upper_pos)
  have hseq_floor :
      ∀ d : ℕ, 1 ≤ d → d ≤ n → tFirst < seq d := by
    intro d
    refine Nat.strong_induction_on d ?_
    intro d ih hd_pos hd_le
    cases d with
    | zero =>
        omega
    | succ d =>
        cases d with
        | zero =>
            simpa [seq, theorem32BackwardGridLowBisectionFromTop] using
              htFirst_lt_lastLow
        | succ d =>
            have hprev : tFirst < seq (d + 1) := by
              exact ih (d + 1) (by omega) (by omega) (by omega)
            let i : Fin (n + 1) := ⟨n - (d + 1), by omega⟩
            have hi_first : i.val ≠ 0 := by
              dsimp [i]
              omega
            have hi_last : i.val ≠ n := by
              dsimp [i]
              omega
            have hhigh :
                returned (adjacentHighIndex i) = seq (d + 1) := by
              dsimp [returned, seq, theorem32BackwardGridLowBisectionLevels,
                adjacentHighIndex, i]
              simp
              congr 1
              omega
            let root : ℝ :=
              weightedBernoulliLowEndpointOfRateOrFloor
                (1 : ℝ) (1 : ℝ) tFirst (seq (d + 1)) target
            have hhi1 : seq (d + 1) < 1 := by
              simpa [returned, hhigh] using hhigh_lt_one i hi_first hi_last
            have hfeasible :
                WeightedBernoulliLowEndpointTargetFeasible
                  (1 : ℝ) (1 : ℝ) tFirst (seq (d + 1)) target :=
              { hgHi := by norm_num
                hgLo := by norm_num
                hfloor0 := htFirst_pos
                hfloor_lt_hi := hprev
                hpHi1 := hhi1
                htarget_pos := htarget_pos
                htarget_lt_floor := by
                  simpa [target, returned, hhigh] using
                    htarget_lt_floor_rate i hi_first hi_last }
            have hroot_mem :
                root ∈ Set.Ioo tFirst (seq (d + 1)) := by
              simpa [root] using
                weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
                  hfeasible
            have hroot_pos : 0 < root := htFirst_pos.trans hroot_mem.1
            have hroot_le_grid_upper :
                root ≤ seq (d + 1) - grid := by
              have hgrid_rate :
                  weightedBernoulliClosedThresholdRate
                      (1 : ℝ) (1 : ℝ)
                      (seq (d + 1)) (seq (d + 1) - grid) ≤
                    target := by
                have hgrid_rate' :
                    weightedBernoulliClosedThresholdRate
                        (1 : ℝ) (1 : ℝ)
                        (returned (adjacentHighIndex i))
                        (returned (adjacentHighIndex i) - grid) ≤
                      target := by
                  simpa [target, returned] using
                    hgrid_upper_rate_le_target i hi_first hi_last
                simpa [hhigh] using hgrid_rate'
              have hx0 : 0 < seq (d + 1) - grid := by
                have hx0' :
                    0 < returned (adjacentHighIndex i) - grid := by
                  simpa [target, returned] using
                    hgrid_upper_pos i hi_first hi_last
                simpa [hhigh] using hx0'
              exact
                weightedBernoulliLowEndpointOfRateOrFloor_le_of_feasible_rate_le_target
                  hfeasible hx0 (by linarith) hgrid_rate
            have hupper_ge_root :
                root ≤
                  (EconCSLib.Optimization.realBisectionRun
                    (EconCSLib.Optimization.realBisectionAboveTarget root)
                    innerSteps 0 (seq (d + 1) - grid)).2 :=
              EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
                (n := innerSteps) (lower := 0) (target := root)
                (upper := seq (d + 1) - grid)
                hroot_pos.le hroot_le_grid_upper
            have hseq_eq :
                seq (d + 2) =
                  (EconCSLib.Optimization.realBisectionRun
                    (EconCSLib.Optimization.realBisectionAboveTarget root)
                    innerSteps 0 (seq (d + 1) - grid)).2 := by
              simp [seq, theorem32BackwardGridLowBisectionFromTop, root]
            rw [hseq_eq]
            exact hroot_mem.1.trans_le hupper_ge_root
  dsimp
  intro i hi_first hi_last
  have hd_pos : 1 ≤ n - i.val := by omega
  have hd_le : n - i.val ≤ n := by omega
  have hhigh :
      returned (adjacentHighIndex i) = seq (n - i.val) := by
    dsimp [returned, seq, theorem32BackwardGridLowBisectionLevels,
      adjacentHighIndex]
    simp
  change tFirst < returned (adjacentHighIndex i)
  rw [hhigh]
  exact hseq_floor (n - i.val) hd_pos hd_le

/--
Source-grid support invariant with the source grid width stated as a scalar
small-grid condition.  If `grid < tFirst`, the induction that keeps every
inner high endpoint above `tFirst` also proves every source-grid interval
`[0, high - grid]` is nonempty, so callers do not need to supply
`0 < high - grid` separately.
-/
theorem theorem32BackwardGridLowBisectionLevels_floor_lt_high_and_grid_upper_pos_of_grid_lt_floor
    {n innerSteps : ℕ} (grid tFirst lastLow : ℝ)
    (htFirst_pos : 0 < tFirst)
    (hgrid_pos : 0 < grid)
    (hgrid_lt_tFirst : grid < tFirst)
    (hlastLow_lt_one : lastLow < 1)
    (hlastLow_pos : 0 < lastLow)
    (hlastLow_le_one_sub_grid : lastLow ≤ 1 - grid)
    (htFirst_lt_lastLow : tFirst < lastLow)
    (htarget_lt_floor_rate :
      let target : ℝ := -Real.log lastLow
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst) :
    let target : ℝ := -Real.log lastLow
    let returned :=
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow
    (∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        tFirst < returned (adjacentHighIndex i)) ∧
      (∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        0 < returned (adjacentHighIndex i) - grid) := by
  let target : ℝ := -Real.log lastLow
  let seq : ℕ → ℝ :=
    theorem32BackwardGridLowBisectionFromTop innerSteps grid tFirst target
      lastLow
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  have htarget_pos : 0 < target := by
    have hlog_neg : Real.log lastLow < 0 :=
      Real.log_neg hlastLow_pos hlastLow_lt_one
    dsimp [target]
    linarith
  have hlog_target :
      -Real.log (1 - grid) ≤ target := by
    have hpos_one_sub_grid : 0 < 1 - grid :=
      hlastLow_pos.trans_le hlastLow_le_one_sub_grid
    have hgrid_lt_one : grid < 1 := by linarith
    have hlog_le : Real.log lastLow ≤ Real.log (1 - grid) :=
      Real.log_le_log hlastLow_pos hlastLow_le_one_sub_grid
    dsimp [target]
    linarith
  have hseq :
      ∀ d : ℕ, 1 ≤ d → d ≤ n → tFirst < seq d ∧ seq d < 1 := by
    intro d
    refine Nat.strong_induction_on d ?_
    intro d ih hd_pos hd_le
    cases d with
    | zero =>
        omega
    | succ d =>
        cases d with
        | zero =>
            exact
              ⟨by
                simpa [seq, theorem32BackwardGridLowBisectionFromTop] using
                  htFirst_lt_lastLow,
               by
                simpa [seq, theorem32BackwardGridLowBisectionFromTop] using
                  hlastLow_lt_one⟩
        | succ d =>
            have hprev : tFirst < seq (d + 1) ∧ seq (d + 1) < 1 :=
              ih (d + 1) (by omega) (by omega) (by omega)
            let i : Fin (n + 1) := ⟨n - (d + 1), by omega⟩
            have hi_first : i.val ≠ 0 := by
              dsimp [i]
              omega
            have hi_last : i.val ≠ n := by
              dsimp [i]
              omega
            have hhigh :
                returned (adjacentHighIndex i) = seq (d + 1) := by
              dsimp [returned, seq, theorem32BackwardGridLowBisectionLevels,
                adjacentHighIndex, i]
              simp
              congr 1
              omega
            let root : ℝ :=
              weightedBernoulliLowEndpointOfRateOrFloor
                (1 : ℝ) (1 : ℝ) tFirst (seq (d + 1)) target
            have hfeasible :
                WeightedBernoulliLowEndpointTargetFeasible
                  (1 : ℝ) (1 : ℝ) tFirst (seq (d + 1)) target :=
              { hgHi := by norm_num
                hgLo := by norm_num
                hfloor0 := htFirst_pos
                hfloor_lt_hi := hprev.1
                hpHi1 := hprev.2
                htarget_pos := htarget_pos
                htarget_lt_floor := by
                  simpa [target, returned, hhigh] using
                    htarget_lt_floor_rate i hi_first hi_last }
            have hroot_mem :
                root ∈ Set.Ioo tFirst (seq (d + 1)) := by
              simpa [root] using
                weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
                  hfeasible
            have hroot_pos : 0 < root := htFirst_pos.trans hroot_mem.1
            have hupper_pos : 0 < seq (d + 1) - grid := by
              linarith [hgrid_lt_tFirst, hprev.1]
            have hgrid_lt_one : grid < 1 := by
              linarith [hgrid_pos, hprev.2]
            have hgrid_rate :
                weightedBernoulliClosedThresholdRate
                    (1 : ℝ) (1 : ℝ)
                    (seq (d + 1)) (seq (d + 1) - grid) ≤
                  target := by
              have hrate :=
                weightedBernoulliClosedThresholdRate_one_one_le_neg_log_one_sub_width
                  (pLo := seq (d + 1) - grid) (x := grid)
                  (le_of_lt hupper_pos) (le_of_lt hgrid_pos)
                  (by simpa [sub_add_cancel] using le_of_lt hprev.2)
                  hgrid_lt_one
              have hrate' :
                  weightedBernoulliClosedThresholdRate
                      (1 : ℝ) (1 : ℝ)
                      (seq (d + 1)) (seq (d + 1) - grid) ≤
                    -Real.log (1 - grid) := by
                simpa [sub_add_cancel] using hrate
              exact hrate'.trans hlog_target
            have hroot_le_grid_upper : root ≤ seq (d + 1) - grid :=
              weightedBernoulliLowEndpointOfRateOrFloor_le_of_feasible_rate_le_target
                hfeasible hupper_pos (by linarith) hgrid_rate
            have hupper_ge_root :
                root ≤
                  (EconCSLib.Optimization.realBisectionRun
                    (EconCSLib.Optimization.realBisectionAboveTarget root)
                    innerSteps 0 (seq (d + 1) - grid)).2 :=
              EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
                (n := innerSteps) (lower := 0) (target := root)
                (upper := seq (d + 1) - grid)
                hroot_pos.le hroot_le_grid_upper
            have hupper_le_initial :
                (EconCSLib.Optimization.realBisectionRun
                    (EconCSLib.Optimization.realBisectionAboveTarget root)
                    innerSteps 0 (seq (d + 1) - grid)).2 ≤
                  seq (d + 1) - grid :=
              EconCSLib.Optimization.realBisectionRun_upper_le_initial
                (EconCSLib.Optimization.realBisectionAboveTarget root)
                (le_of_lt hupper_pos)
            have hseq_eq :
                seq (d + 2) =
                  (EconCSLib.Optimization.realBisectionRun
                    (EconCSLib.Optimization.realBisectionAboveTarget root)
                    innerSteps 0 (seq (d + 1) - grid)).2 := by
              simp [seq, theorem32BackwardGridLowBisectionFromTop, root]
            rw [hseq_eq]
            constructor
            · exact hroot_mem.1.trans_le hupper_ge_root
            · exact lt_of_le_of_lt hupper_le_initial (by linarith [hprev.2, hgrid_pos])
  dsimp
  constructor
  · intro i hi_first hi_last
    have hd_pos : 1 ≤ n - i.val := by omega
    have hd_le : n - i.val ≤ n := by omega
    have hhigh :
        returned (adjacentHighIndex i) = seq (n - i.val) := by
      dsimp [returned, seq, theorem32BackwardGridLowBisectionLevels,
        adjacentHighIndex]
      simp
    change tFirst < returned (adjacentHighIndex i)
    rw [hhigh]
    exact (hseq (n - i.val) hd_pos hd_le).1
  · intro i hi_first hi_last
    have hd_pos : 1 ≤ n - i.val := by omega
    have hd_le : n - i.val ≤ n := by omega
    have hhigh :
        returned (adjacentHighIndex i) = seq (n - i.val) := by
      dsimp [returned, seq, theorem32BackwardGridLowBisectionLevels,
        adjacentHighIndex]
      simp
    change 0 < returned (adjacentHighIndex i) - grid
    rw [hhigh]
    linarith [(hseq (n - i.val) hd_pos hd_le).1, hgrid_lt_tFirst]

/--
Low-endpoint feasibility for every calculated source-grid inner bisection
call from direct source-shaped support/rate facts.  The previous wrappers
often derived this through an endpoint-vector certificate; this form only
needs positivity of the fixed floor and target, the current high endpoint
support facts, and the floor-rate comparison.
-/
theorem theorem32BackwardGridLowBisectionLevels_feasible_of_floor_lt_high_and_high_lt_one
    {n innerSteps : ℕ} (grid tFirst target lastLow : ℝ)
    (htFirst_pos : 0 < tFirst)
    (htarget_pos : 0 < target)
    (hfloor_lt_high :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        tFirst < returned (adjacentHighIndex i))
    (hhigh_lt_one :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        returned (adjacentHighIndex i) < 1)
    (htarget_lt_floor_rate :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst) :
    let returned :=
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow
    ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
      WeightedBernoulliLowEndpointTargetFeasible
        (1 : ℝ) (1 : ℝ) tFirst
        (returned (adjacentHighIndex i)) target := by
  dsimp
  intro i hi_first hi_last
  exact
    { hgHi := by norm_num
      hgLo := by norm_num
      hfloor0 := htFirst_pos
      hfloor_lt_hi := by
        simpa using hfloor_lt_high i hi_first hi_last
      hpHi1 := by
        simpa using hhigh_lt_one i hi_first hi_last
      htarget_pos := htarget_pos
      htarget_lt_floor := by
        simpa using htarget_lt_floor_rate i hi_first hi_last }

/--
Source-grid root-placement bridge from the older strict floor-rate invariant.
If the fixed floor is a feasible interior point whose closed threshold rate is
strictly above the target, then the selected low-endpoint root is strictly
above that floor.  This identifies the paper's rate-comparison loop invariant
with the root-position invariant used by the newer calculated-grid wrappers.
-/
theorem theorem32BackwardGridLowBisectionLevels_floor_lt_lowEndpointOfRateOrFloor_of_floor_rate
    {n innerSteps : ℕ} (grid tFirst target lastLow : ℝ)
    (htFirst_pos : 0 < tFirst)
    (htarget_pos : 0 < target)
    (hfloor_lt_high :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        tFirst < returned (adjacentHighIndex i))
    (hhigh_lt_one :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        returned (adjacentHighIndex i) < 1)
    (htarget_lt_floor_rate :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst) :
    let returned :=
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
        lastLow
    let root : Fin (n + 1) → ℝ := fun i =>
      weightedBernoulliLowEndpointOfRateOrFloor
        (1 : ℝ) (1 : ℝ) tFirst
        (returned (adjacentHighIndex i)) target
    ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
      tFirst < root i := by
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
      lastLow
  let root : Fin (n + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  have hfeasible :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target
          lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target := by
    simpa [returned] using
      theorem32BackwardGridLowBisectionLevels_feasible_of_floor_lt_high_and_high_lt_one
        (n := n) (innerSteps := innerSteps)
        grid tFirst target lastLow htFirst_pos htarget_pos
        (by simpa [returned] using hfloor_lt_high)
        (by simpa [returned] using hhigh_lt_one)
        (by simpa [returned] using htarget_lt_floor_rate)
  dsimp at hfeasible ⊢
  intro i hi_first hi_last
  have hmem :
      root i ∈ Set.Ioo tFirst (returned (adjacentHighIndex i)) := by
    simpa [returned, root] using
      weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
        (hfeasible i hi_first hi_last)
  exact hmem.1

/--
The source-grid backward recursion turns a single global inner-depth budget
into every per-adjacent inner-width budget.  Endpoint normalization gives
`high ≤ 1`, so the interval `[0, high - grid]` is no wider than the unit
interval used in the source's asymptotic runtime calculation.
-/
theorem theorem32BackwardGridLowBisectionLevels_innerWidth_of_feasible_grid_width
    {n innerSteps : ℕ} (hn : 1 < n)
    (grid tFirst target lastLow delta : ℝ)
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (hfeasible :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target lastLow
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hroot_le_grid_upper :
      let returned :=
        theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target lastLow
      let root : Fin (n + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
        root i ≤ returned (adjacentHighIndex i) - grid)
    (hwidth : 1 ≤ delta * (2 : ℝ) ^ innerSteps) :
    let returned :=
      theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target lastLow
    ∀ i : Fin (n + 1), i.val ≠ 0 → i.val ≠ n →
      (returned (adjacentHighIndex i) - grid - 0) /
          (2 : ℝ) ^ innerSteps ≤ delta := by
  let returned :=
    theorem32BackwardGridLowBisectionLevels n innerSteps grid tFirst target lastLow
  have hreturnedLevels : BinaryEndpointLevelVector returned := by
    simpa [returned] using
      theorem32BackwardGridLowBisectionLevels_isEndpointLevelVector_of_feasible_grid_auto_first
        (n := n) (innerSteps := innerSteps) hn grid tFirst target lastLow
        hgrid_pos hlastLow_lt_one hfeasible hroot_le_grid_upper
  dsimp
  intro i _hi_first _hi_last
  have hpow_pos : 0 < (2 : ℝ) ^ innerSteps :=
    pow_pos (by norm_num) innerSteps
  have hhigh_le_one : returned (adjacentHighIndex i) ≤ 1 :=
    BinaryEndpointLevelVector_le_one hreturnedLevels (adjacentHighIndex i)
  have hnum_le_one : returned (adjacentHighIndex i) - grid - 0 ≤ 1 := by
    linarith [hhigh_le_one, hgrid_pos]
  have hdiv_le_one :
      (returned (adjacentHighIndex i) - grid - 0) /
          (2 : ℝ) ^ innerSteps ≤
        (1 : ℝ) / (2 : ℝ) ^ innerSteps :=
    div_le_div_of_nonneg_right hnum_le_one hpow_pos.le
  have hone_div_le_delta :
      (1 : ℝ) / (2 : ℝ) ^ innerSteps ≤ delta :=
    (div_le_iff₀ hpow_pos).2 hwidth
  exact hdiv_le_one.trans hone_div_le_delta

/--
Source-shaped inner-grid constructor for Theorem 3.2.  The first adjacent
rate is handled by the source invariant `r(1) ≥ r(last)`, the last adjacent
rate is immediate, and each interior adjacent rate follows from a level-space
bisection bracket around the exact low-endpoint root for the last rate.
-/
theorem theorem32_uniform_inner_grid_of_low_bisection_brackets
    {m : ℕ}
    (returned : Fin (m + 2) → ℝ)
    {tFirst delta : ℝ}
    (hlevels : BinaryEndpointLevelVector returned)
    (htFirst0 : 0 < tFirst)
    (hdelta : 0 ≤ delta)
    (hfirstRate :
      binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin (m + 1)))
    (root lower : Fin (m + 1) → ℝ)
    (hroot0 :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m → 0 < root i)
    (htFirst_le_root :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m → tFirst ≤ root i)
    (hroot_rate :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i)) (root i) =
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin (m + 1)))
    (hbracket :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        EconCSLib.Optimization.RealBisectionBracket
          (root i) (lower i) (returned (adjacentLowIndex i)) delta) :
    ∀ i : Fin (m + 1),
      binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) -
          Real.log ((tFirst + delta) / tFirst) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin (m + 2) => (1 : ℝ)) i := by
  intro i
  have hratio_ge_one : 1 ≤ (tFirst + delta) / tFirst := by
    rw [le_div_iff₀ htFirst0]
    linarith
  have hlog_nonneg :
      0 ≤ Real.log ((tFirst + delta) / tFirst) :=
    Real.log_nonneg hratio_ge_one
  by_cases hi_first : i.val = 0
  · have hi : i = (firstAdjacentIndex : Fin (m + 1)) := by
      ext
      simpa [firstAdjacentIndex] using hi_first
    subst i
    exact
      (sub_le_self
        (binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)))
        hlog_nonneg).trans hfirstRate
  · by_cases hi_last : i.val = m
    · have hi : i = (lastAdjacentIndex : Fin (m + 1)) := by
        ext
        simpa [lastAdjacentIndex] using hi_last
      subst i
      exact
        sub_le_self
          (binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin (m + 1)))
          hlog_nonneg
    · have hhigh_not_first : (adjacentHighIndex i).val ≠ 0 := by
        simp [adjacentHighIndex]
      have hhigh_not_last : (adjacentHighIndex i).val ≠ m + 1 := by
        simp [adjacentHighIndex]
        omega
      have hlow_not_last : (adjacentLowIndex i).val ≠ m + 1 := by
        simp [adjacentLowIndex]
        omega
      have hhi0 :
          0 < returned (adjacentHighIndex i) :=
        BinaryEndpointLevelVector_pos_of_not_first
          hlevels (adjacentHighIndex i) hhigh_not_first
      have hhi1 :
          returned (adjacentHighIndex i) < 1 :=
        BinaryEndpointLevelVector_lt_one_of_not_last
          hlevels (adjacentHighIndex i) hhigh_not_last
      have hreturned1 :
          returned (adjacentLowIndex i) < 1 :=
        BinaryEndpointLevelVector_lt_one_of_not_last
          hlevels (adjacentLowIndex i) hlow_not_last
      have hstep :=
        binaryEndpointAwareAdjacentRate_interior_ge_target_sub_first_log_of_bisection_bracket
          returned (fun _ : Fin (m + 2) => (1 : ℝ)) i
          hi_first hi_last
          (root := root i) (lower := lower i) (delta := delta)
          (target :=
            binaryEndpointAwareAdjacentRate returned
              (fun _ : Fin (m + 2) => (1 : ℝ))
              (lastAdjacentIndex : Fin (m + 1)))
          (tFirst := tFirst)
          (by norm_num) (by norm_num) (by norm_num)
          hhi0 hhi1 (hroot0 i hi_first hi_last) hreturned1
          htFirst0 (htFirst_le_root i hi_first hi_last) hdelta
          (hroot_rate i hi_first hi_last)
          (hbracket i hi_first hi_last)
      simpa using hstep

/--
Source-shaped inner-grid constructor for monotone sample rates.  This is the
nonuniform analogue of `theorem32_uniform_inner_grid_of_low_bisection_brackets`:
the source first-rate invariant handles the first interval, the last interval
is immediate, and every interior interval follows from a low-endpoint bisection
bracket.  Monotonicity of the match weights is used only to replace the local
low weight by the last weight in the common logarithmic loss term.
-/
theorem theorem32_monotone_inner_grid_of_low_bisection_brackets
    {m : ℕ}
    (returned sampleRate : Fin (m + 2) → ℝ)
    {tFirst delta gLast : ℝ}
    (hlevels : BinaryEndpointLevelVector returned)
    (htFirst0 : 0 < tFirst)
    (hdelta : 0 ≤ delta)
    (hsample_pos : ∀ idx : Fin (m + 2), 0 < sampleRate idx)
    (hsample_mono :
      ∀ {a b : Fin (m + 2)}, a.val ≤ b.val → sampleRate a ≤ sampleRate b)
    (hgLast :
      sampleRate (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) =
        gLast)
    (hfirstRate :
      binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)) ≤
        binaryEndpointAwareAdjacentRate returned sampleRate
          (firstAdjacentIndex : Fin (m + 1)))
    (root lower : Fin (m + 1) → ℝ)
    (hroot0 :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m → 0 < root i)
    (htFirst_le_root :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m → tFirst ≤ root i)
    (hroot_rate :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        weightedBernoulliClosedThresholdRate
            (sampleRate (adjacentHighIndex i))
            (sampleRate (adjacentLowIndex i))
            (returned (adjacentHighIndex i)) (root i) =
          binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1)))
    (hbracket :
      ∀ i : Fin (m + 1), i.val ≠ 0 → i.val ≠ m →
        EconCSLib.Optimization.RealBisectionBracket
          (root i) (lower i) (returned (adjacentLowIndex i)) delta) :
    ∀ i : Fin (m + 1),
      binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)) -
          gLast * Real.log ((tFirst + delta) / tFirst) ≤
        binaryEndpointAwareAdjacentRate returned sampleRate i := by
  intro i
  have hratio_ge_one : 1 ≤ (tFirst + delta) / tFirst := by
    rw [le_div_iff₀ htFirst0]
    linarith
  have hlog_nonneg :
      0 ≤ Real.log ((tFirst + delta) / tFirst) :=
    Real.log_nonneg hratio_ge_one
  have hgLast_nonneg : 0 ≤ gLast := by
    have hpos :
        0 < sampleRate
          (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) :=
      hsample_pos (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
    rw [hgLast] at hpos
    exact hpos.le
  have hscaled_log_nonneg :
      0 ≤ gLast * Real.log ((tFirst + delta) / tFirst) :=
    mul_nonneg hgLast_nonneg hlog_nonneg
  by_cases hi_first : i.val = 0
  · have hi : i = (firstAdjacentIndex : Fin (m + 1)) := by
      ext
      simpa [firstAdjacentIndex] using hi_first
    subst i
    exact
      (sub_le_self
        (binaryEndpointAwareAdjacentRate returned sampleRate
          (lastAdjacentIndex : Fin (m + 1)))
        hscaled_log_nonneg).trans hfirstRate
  · by_cases hi_last : i.val = m
    · have hi : i = (lastAdjacentIndex : Fin (m + 1)) := by
        ext
        simpa [lastAdjacentIndex] using hi_last
      subst i
      exact
        sub_le_self
          (binaryEndpointAwareAdjacentRate returned sampleRate
            (lastAdjacentIndex : Fin (m + 1)))
          hscaled_log_nonneg
    · have hhigh_not_first : (adjacentHighIndex i).val ≠ 0 := by
        simp [adjacentHighIndex]
      have hhigh_not_last : (adjacentHighIndex i).val ≠ m + 1 := by
        simp [adjacentHighIndex]
        omega
      have hlow_not_last : (adjacentLowIndex i).val ≠ m + 1 := by
        simp [adjacentLowIndex]
        omega
      have hhi0 :
          0 < returned (adjacentHighIndex i) :=
        BinaryEndpointLevelVector_pos_of_not_first
          hlevels (adjacentHighIndex i) hhigh_not_first
      have hhi1 :
          returned (adjacentHighIndex i) < 1 :=
        BinaryEndpointLevelVector_lt_one_of_not_last
          hlevels (adjacentHighIndex i) hhigh_not_last
      have hreturned1 :
          returned (adjacentLowIndex i) < 1 :=
        BinaryEndpointLevelVector_lt_one_of_not_last
          hlevels (adjacentLowIndex i) hlow_not_last
      have hlow_rate_le_last :
          sampleRate (adjacentLowIndex i) ≤ gLast := by
        have hidx :
            (adjacentLowIndex i).val ≤
              (adjacentLowIndex
                (lastAdjacentIndex : Fin (m + 1))).val := by
          simp [adjacentLowIndex, lastAdjacentIndex]
          omega
        exact
          (hsample_mono
            (a := adjacentLowIndex i)
            (b := adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
            hidx).trans_eq hgLast
      have hlocal_scale :
          sampleRate (adjacentLowIndex i) *
              Real.log ((tFirst + delta) / tFirst) ≤
            gLast * Real.log ((tFirst + delta) / tFirst) :=
        mul_le_mul_of_nonneg_right hlow_rate_le_last hlog_nonneg
      have hstep :=
        binaryEndpointAwareAdjacentRate_interior_ge_target_sub_first_log_of_bisection_bracket
          returned sampleRate i hi_first hi_last
          (root := root i) (lower := lower i) (delta := delta)
          (target :=
            binaryEndpointAwareAdjacentRate returned sampleRate
              (lastAdjacentIndex : Fin (m + 1)))
          (tFirst := tFirst)
          (hsample_pos (adjacentHighIndex i)).le
          (hsample_pos (adjacentLowIndex i)).le
          (add_pos (hsample_pos (adjacentHighIndex i))
            (hsample_pos (adjacentLowIndex i)))
          hhi0 hhi1 (hroot0 i hi_first hi_last) hreturned1
          htFirst0 (htFirst_le_root i hi_first hi_last) hdelta
          (hroot_rate i hi_first hi_last)
          (hbracket i hi_first hi_last)
      linarith

/--
Construct the Theorem 3.2 source-level run certificate from a genuine real
bisection bracket for the final low endpoint, plus the remaining inner-grid
rate certificate and loop-count bounds.  This replaces the last-rate
inequality by the bracket invariant maintained by the outer bisection loop.
-/
def theorem32_run_certificate_of_last_bisection_bracket
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps lastBracketLower : ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (hlastBracket :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      EconCSLib.Optimization.RealBisectionBracket
        (optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        lastBracketLower
        (returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        delta)
    (hgrid :
      let tFirstStar : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      ∀ i : Fin ((2 * m + 1) + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    Theorem32NestedBisectionRunCertificate
      (m := m) (M := M) (L := L) oldLevels returned eps := by
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let uniform : Fin ((2 * m + 1) + 2) → ℝ := fun _ => (1 : ℝ)
  let delta : ℝ :=
    eps /
      ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
        (((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
  have hoptimalLevels : BinaryEndpointLevelVector optimal := by
    simpa [optimal] using
      uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  refine
    { outerSteps := outerSteps
      innerSteps := innerSteps
      hlast := ?_
      hgrid := hgrid
      houter := houter
      hinner := hinner }
  dsimp only
  have hlast_raw :
      binaryEndpointAwareAdjacentRate optimal uniform
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
          Real.log
            ((optimal
                  (adjacentLowIndex
                    (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) +
                delta) /
              optimal
                (adjacentLowIndex
                  (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned uniform
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) := by
    exact
      binaryEndpointAwareAdjacentRate_uniform_last_ge_of_bisection_bracket
        (m := 2 * m + 1) (by omega) optimal returned
        (lower := lastBracketLower) (delta := delta)
        hoptimalLevels (by simpa [optimal, delta] using hlastBracket)
  simpa [optimal, uniform, delta] using hlast_raw

/--
Construct the Theorem 3.2 source-level run certificate from bisection brackets
for both levels of the source algorithm: an outer bracket for the final low
endpoint and rate-space brackets for the inner `CalculateOtherLevels` calls.
The generic bracket lemma turns each inner rate bracket into the grid
inequality used by the approximation proof.
-/
def theorem32_run_certificate_of_outer_level_and_inner_rate_brackets
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps lastBracketLower : ℝ}
    (gridUpper : Fin ((2 * m + 1) + 1) → ℝ)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (hlastBracket :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      EconCSLib.Optimization.RealBisectionBracket
        (optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        lastBracketLower
        (returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        delta)
    (hgridBrackets :
      let tFirstStar : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      ∀ i : Fin ((2 * m + 1) + 1),
        EconCSLib.Optimization.RealBisectionBracket
          (binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
          (binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i)
          (gridUpper i)
          (Real.log ((tFirstStar + delta) / tFirstStar)))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    Theorem32NestedBisectionRunCertificate
      (m := m) (M := M) (L := L) oldLevels returned eps := by
  let tFirstStar : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let delta : ℝ :=
    eps /
      ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
        (((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
  have hgrid :
      ∀ i : Fin ((2 * m + 1) + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i := by
    intro i
    have Bi := hgridBrackets i
    simpa [tFirstStar, delta] using
      Bi.target_sub_delta_le_lower
  exact
    theorem32_run_certificate_of_last_bisection_bracket
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned
      (lastBracketLower := lastBracketLower)
      holdLevels hlastBracket hgrid houter hinner

/--
Construct the Theorem 3.2 run certificate from an outer level bracket and
executable inner bisection runs in rate space.  Each inner run brackets the
target last adjacent rate, and the returned adjacent rate is the final lower
endpoint of that rate bracket.
-/
noncomputable def theorem32_run_certificate_of_outer_level_bracket_and_inner_rate_runs
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps lastBracketLower : ℝ}
    (rateAbove : Fin ((2 * m + 1) + 1) → ℝ → Bool)
    (rateLower0 rateUpper0 : Fin ((2 * m + 1) + 1) → ℝ)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (hlastBracket :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      EconCSLib.Optimization.RealBisectionBracket
        (optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        lastBracketLower
        (returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        delta)
    (hinnerAbove :
      ∀ i : Fin ((2 * m + 1) + 1), ∀ x,
        rateAbove i x = true →
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) ≤ x)
    (hinnerBelow :
      ∀ i : Fin ((2 * m + 1) + 1), ∀ x,
        rateAbove i x = false →
          x ≤
            binaryEndpointAwareAdjacentRate returned
              (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (hinnerLower0 :
      ∀ i : Fin ((2 * m + 1) + 1),
        rateLower0 i ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (hinnerUpper0 :
      ∀ i : Fin ((2 * m + 1) + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) ≤
          rateUpper0 i)
    (hinnerWidth :
      let tFirstStar : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      ∀ i : Fin ((2 * m + 1) + 1),
        (rateUpper0 i - rateLower0 i) / (2 : ℝ) ^ innerSteps ≤
          Real.log ((tFirstStar + delta) / tFirstStar))
    (hreturnedRate :
      ∀ i : Fin ((2 * m + 1) + 1),
        (EconCSLib.Optimization.realBisectionRun
          (rateAbove i) innerSteps (rateLower0 i) (rateUpper0 i)).1 =
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    Theorem32NestedBisectionRunCertificate
      (m := m) (M := M) (L := L) oldLevels returned eps := by
  let tFirstStar : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let delta : ℝ :=
    eps /
      ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
        (((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
  let gridUpper : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
    (EconCSLib.Optimization.realBisectionRun
      (rateAbove i) innerSteps (rateLower0 i) (rateUpper0 i)).2
  have hgridBrackets :
      ∀ i : Fin ((2 * m + 1) + 1),
        EconCSLib.Optimization.RealBisectionBracket
          (binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
          (binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i)
          (gridUpper i)
          (Real.log ((tFirstStar + delta) / tFirstStar)) := by
    intro i
    have Bi :
        EconCSLib.Optimization.RealBisectionBracket
          (binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
          (EconCSLib.Optimization.realBisectionRun
            (rateAbove i) innerSteps (rateLower0 i) (rateUpper0 i)).1
          (EconCSLib.Optimization.realBisectionRun
            (rateAbove i) innerSteps (rateLower0 i) (rateUpper0 i)).2
          (Real.log ((tFirstStar + delta) / tFirstStar)) := by
      exact
        EconCSLib.Optimization.realBisectionRun_bracket_of_width_le
          (above := rateAbove i) (n := innerSteps)
          (target :=
            binaryEndpointAwareAdjacentRate returned
              (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
          (lower := rateLower0 i) (upper := rateUpper0 i)
          (delta := Real.log ((tFirstStar + delta) / tFirstStar))
          (hinnerAbove i) (hinnerBelow i) (hinnerLower0 i)
          (hinnerUpper0 i) (by simpa [tFirstStar, delta] using hinnerWidth i)
    simpa [gridUpper, hreturnedRate i] using Bi
  exact
    theorem32_run_certificate_of_outer_level_and_inner_rate_brackets
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned
      (lastBracketLower := lastBracketLower)
      gridUpper holdLevels hlastBracket
      (by simpa [tFirstStar, delta] using hgridBrackets)
      houter hinner

/--
Construct the Theorem 3.2 run certificate from an executable outer bisection
run.  The run supplies the final low endpoint's bracket invariant through a
sound midpoint classifier and the usual `width / 2^n` bisection-width bound.
The inner-grid rate certificate remains the separate `CalculateOtherLevels`
obligation.
-/
noncomputable def theorem32_run_certificate_of_last_bisection_run
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps lower0 upper0 : ℝ}
    (above : ℝ → Bool)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (habove :
      ∀ x,
        above x = true →
          uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ x)
    (hbelow :
      ∀ x,
        above x = false →
          x ≤
            uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlower0 :
      lower0 ≤
        uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hupper0 :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ upper0)
    (hwidth :
      (upper0 - lower0) / (2 : ℝ) ^ outerSteps ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          above outerSteps lower0 upper0).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hgrid :
      let tFirstStar : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      ∀ i : Fin ((2 * m + 1) + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    Theorem32NestedBisectionRunCertificate
      (m := m) (M := M) (L := L) oldLevels returned eps := by
  let target : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let delta : ℝ :=
    eps /
      ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
        (((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
  have B :
      EconCSLib.Optimization.RealBisectionBracket target
        (EconCSLib.Optimization.realBisectionRun
          above outerSteps lower0 upper0).1
        (EconCSLib.Optimization.realBisectionRun
          above outerSteps lower0 upper0).2
        delta := by
    exact
      EconCSLib.Optimization.realBisectionRun_bracket_of_width_le
        (above := above) (n := outerSteps)
        (target := target) (lower := lower0) (upper := upper0)
        (delta := delta)
        (by simpa [target] using habove)
        (by simpa [target] using hbelow)
        (by simpa [target] using hlower0)
        (by simpa [target] using hupper0)
        (by simpa [delta] using hwidth)
  exact
    theorem32_run_certificate_of_last_bisection_bracket
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned
      (lastBracketLower :=
        (EconCSLib.Optimization.realBisectionRun
          above outerSteps lower0 upper0).1)
      holdLevels
      (by
        simpa [target, delta, hreturnedLast] using B)
      hgrid houter hinner

/--
Combined executable-bisection constructor for Theorem 3.2.  The outer
bisection run brackets the final low endpoint, while the inner bisection runs
bracket the target last adjacent rate in rate space.  This is the current
formal run contract closest to Algorithm 1's nested-bisection pseudocode.
-/
noncomputable def theorem32_run_certificate_of_outer_level_run_and_inner_rate_runs
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps lower0 upper0 : ℝ}
    (levelAbove : ℝ → Bool)
    (rateAbove : Fin ((2 * m + 1) + 1) → ℝ → Bool)
    (rateLower0 rateUpper0 : Fin ((2 * m + 1) + 1) → ℝ)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (hlevelAbove :
      ∀ x,
        levelAbove x = true →
          uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ x)
    (hlevelBelow :
      ∀ x,
        levelAbove x = false →
          x ≤
            uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlevelLower0 :
      lower0 ≤
        uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlevelUpper0 :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ upper0)
    (hlevelWidth :
      (upper0 - lower0) / (2 : ℝ) ^ outerSteps ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          levelAbove outerSteps lower0 upper0).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hinnerAbove :
      ∀ i : Fin ((2 * m + 1) + 1), ∀ x,
        rateAbove i x = true →
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) ≤ x)
    (hinnerBelow :
      ∀ i : Fin ((2 * m + 1) + 1), ∀ x,
        rateAbove i x = false →
          x ≤
            binaryEndpointAwareAdjacentRate returned
              (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (hinnerLower0 :
      ∀ i : Fin ((2 * m + 1) + 1),
        rateLower0 i ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (hinnerUpper0 :
      ∀ i : Fin ((2 * m + 1) + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) ≤
          rateUpper0 i)
    (hinnerWidth :
      let tFirstStar : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      ∀ i : Fin ((2 * m + 1) + 1),
        (rateUpper0 i - rateLower0 i) / (2 : ℝ) ^ innerSteps ≤
          Real.log ((tFirstStar + delta) / tFirstStar))
    (hreturnedRate :
      ∀ i : Fin ((2 * m + 1) + 1),
        (EconCSLib.Optimization.realBisectionRun
          (rateAbove i) innerSteps (rateLower0 i) (rateUpper0 i)).1 =
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    Theorem32NestedBisectionRunCertificate
      (m := m) (M := M) (L := L) oldLevels returned eps := by
  let target : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let delta : ℝ :=
    eps /
      ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
        (((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
  let levelRun : ℝ × ℝ :=
    EconCSLib.Optimization.realBisectionRun
      levelAbove outerSteps lower0 upper0
  have hlastBracket :
      EconCSLib.Optimization.RealBisectionBracket target
        levelRun.1
        (returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        delta := by
    have B :
        EconCSLib.Optimization.RealBisectionBracket target
          levelRun.1 levelRun.2 delta := by
      exact
        EconCSLib.Optimization.realBisectionRun_bracket_of_width_le
          (above := levelAbove) (n := outerSteps)
          (target := target) (lower := lower0) (upper := upper0)
          (delta := delta)
          (by simpa [target] using hlevelAbove)
          (by simpa [target] using hlevelBelow)
          (by simpa [target] using hlevelLower0)
          (by simpa [target] using hlevelUpper0)
          (by simpa [delta] using hlevelWidth)
    simpa [levelRun, hreturnedLast] using B
  exact
    theorem32_run_certificate_of_outer_level_bracket_and_inner_rate_runs
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned
      (lastBracketLower := levelRun.1)
      rateAbove rateLower0 rateUpper0 holdLevels
      (by simpa [target, delta] using hlastBracket)
      hinnerAbove hinnerBelow hinnerLower0 hinnerUpper0 hinnerWidth
      hreturnedRate houter hinner

/--
Canonical-threshold specialization of the combined executable-bisection
constructor.  The midpoint classifiers are the library predicates
`x ↦ target ≤ x`, so callers only provide initial brackets, width bounds, and
the fact that the returned coordinates are the final bisection endpoints.
-/
noncomputable def theorem32_run_certificate_of_outer_level_threshold_run_and_inner_rate_threshold_runs
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps lower0 upper0 : ℝ}
    (rateLower0 rateUpper0 : Fin ((2 * m + 1) + 1) → ℝ)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (hlevelLower0 :
      lower0 ≤
        uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlevelUpper0 :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ upper0)
    (hlevelWidth :
      (upper0 - lower0) / (2 : ℝ) ^ outerSteps ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps lower0 upper0).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hinnerLower0 :
      ∀ i : Fin ((2 * m + 1) + 1),
        rateLower0 i ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (hinnerUpper0 :
      ∀ i : Fin ((2 * m + 1) + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) ≤
          rateUpper0 i)
    (hinnerWidth :
      let tFirstStar : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      ∀ i : Fin ((2 * m + 1) + 1),
        (rateUpper0 i - rateLower0 i) / (2 : ℝ) ^ innerSteps ≤
          Real.log ((tFirstStar + delta) / tFirstStar))
    (hreturnedRate :
      ∀ i : Fin ((2 * m + 1) + 1),
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (binaryEndpointAwareAdjacentRate returned
              (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
          innerSteps (rateLower0 i) (rateUpper0 i)).1 =
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    Theorem32NestedBisectionRunCertificate
      (m := m) (M := M) (L := L) oldLevels returned eps := by
  let levelTarget : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let rateTarget : ℝ :=
    binaryEndpointAwareAdjacentRate returned
      (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
      (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
  exact
    theorem32_run_certificate_of_outer_level_run_and_inner_rate_runs
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned
      (levelAbove := EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
      (rateAbove := fun _ =>
        EconCSLib.Optimization.realBisectionAboveTarget rateTarget)
      (rateLower0 := rateLower0) (rateUpper0 := rateUpper0)
      holdLevels
      (fun x hx =>
        EconCSLib.Optimization.realBisectionAboveTarget_true
          (target := levelTarget) (x := x) hx)
      (fun x hx =>
        EconCSLib.Optimization.realBisectionAboveTarget_false
          (target := levelTarget) (x := x) hx)
      (by simpa [levelTarget] using hlevelLower0)
      (by simpa [levelTarget] using hlevelUpper0)
      hlevelWidth
      (by simpa [levelTarget] using hreturnedLast)
      (fun i x hx =>
        EconCSLib.Optimization.realBisectionAboveTarget_true
          (target := rateTarget) (x := x) hx)
      (fun i x hx =>
        EconCSLib.Optimization.realBisectionAboveTarget_false
          (target := rateTarget) (x := x) hx)
      (by simpa [rateTarget] using hinnerLower0)
      (by simpa [rateTarget] using hinnerUpper0)
      hinnerWidth
      (by simpa [rateTarget] using hreturnedRate)
      houter hinner

/-- The explicit Theorem 3.2 grid width is nonnegative for feasible old levels. -/
theorem theorem32_uniform_doubled_explicit_delta_nonneg
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels) :
    0 ≤
      eps /
        ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
          (((1 / 5 : ℝ) *
              binaryEndpointAwareAdjacentRateObjective oldLevels
                (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) := by
  have hgrid_pos :
      0 < 1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)) := by
    simpa using
      one_sub_inv_adjacent_count_pos (m := 2 * m + 1) (by omega)
  have hobj_pos :
      0 <
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ)) := by
    unfold binaryEndpointAwareAdjacentRateObjective
    exact
      EconCSLib.finiteMin_pos
        (binaryEndpointAwareAdjacentRate oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ)))
        (fun i =>
          binaryEndpointAwareAdjacentRate_pos
            hm oldLevels (fun _ : Fin (m + 2) => (1 : ℝ)) holdLevels
            (by intro j; norm_num) (by intro j; norm_num) i)
  have hhalf_pos :
      0 <
        ((1 / 5 : ℝ) *
          binaryEndpointAwareAdjacentRateObjective oldLevels
            (fun _ : Fin (m + 2) => (1 : ℝ))) / 2 := by
    positivity
  have hden_pos :
      0 <
        (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
          (((1 / 5 : ℝ) *
              binaryEndpointAwareAdjacentRateObjective oldLevels
                (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹ :=
    add_pos (inv_pos.mpr hgrid_pos) (inv_pos.mpr hhalf_pos)
  exact div_nonneg heps hden_pos.le

/-- The explicit Theorem 3.2 grid width is positive for positive tolerance. -/
theorem theorem32_uniform_doubled_explicit_delta_pos
    {m : ℕ} (hm : 0 < m)
    {oldLevels : Fin (m + 2) → ℝ}
    {eps : ℝ}
    (heps : 0 < eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels) :
    0 <
      eps /
        ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
          (((1 / 5 : ℝ) *
              binaryEndpointAwareAdjacentRateObjective oldLevels
                (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) := by
  have hgrid_pos :
      0 < 1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)) := by
    simpa using
      one_sub_inv_adjacent_count_pos (m := 2 * m + 1) (by omega)
  have hobj_pos :
      0 <
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ)) := by
    unfold binaryEndpointAwareAdjacentRateObjective
    exact
      EconCSLib.finiteMin_pos
        (binaryEndpointAwareAdjacentRate oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ)))
        (fun i =>
          binaryEndpointAwareAdjacentRate_pos
            hm oldLevels (fun _ : Fin (m + 2) => (1 : ℝ)) holdLevels
            (by intro j; norm_num) (by intro j; norm_num) i)
  have hhalf_pos :
      0 <
        ((1 / 5 : ℝ) *
          binaryEndpointAwareAdjacentRateObjective oldLevels
            (fun _ : Fin (m + 2) => (1 : ℝ))) / 2 := by
    positivity
  have hden_pos :
      0 <
        (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
          (((1 / 5 : ℝ) *
              binaryEndpointAwareAdjacentRateObjective oldLevels
                (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹ :=
    add_pos (inv_pos.mpr hgrid_pos) (inv_pos.mpr hhalf_pos)
  exact div_pos heps hden_pos

/--
Construct the Theorem 3.2 source-level run certificate from the outer final
low-endpoint bracket and source-style inner level-space bisection brackets.
This replaces the previous all-rates `hgrid` certificate by the obligations
visible in `CalculateOtherLevels`: a first-rate invariant, exact interior
low-endpoint roots for the last rate, and bisection brackets around those
roots.
-/
def theorem32_run_certificate_of_outer_level_bracket_and_inner_low_bisection_brackets
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps lastBracketLower : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlastBracket :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      EconCSLib.Optimization.RealBisectionBracket
        (optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        lastBracketLower
        (returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        delta)
    (hfirstRate :
      binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (root lower : Fin ((2 * m + 1) + 1) → ℝ)
    (hroot0 :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        0 < root i)
    (htFirst_le_root :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
          root i)
    (hroot_rate :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i)) (root i) =
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (hbracket :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        EconCSLib.Optimization.RealBisectionBracket
          (root i) (lower i) (returned (adjacentLowIndex i))
          (eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    Theorem32NestedBisectionRunCertificate
      (m := m) (M := M) (L := L) oldLevels returned eps := by
  let tFirstStar : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let delta : ℝ :=
    eps /
      ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
        (((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
  have hoptimalLevels :
      BinaryEndpointLevelVector (uniformDoubledEndpointLevels oldLevels) := by
    simpa using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have htFirstStar0 : 0 < tFirstStar := by
    have hnot_first :
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
          0 := by
      simp [adjacentHighIndex, firstAdjacentIndex]
    simpa [tFirstStar] using
      BinaryEndpointLevelVector_pos_of_not_first
        hoptimalLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
        hnot_first
  have hdelta_nonneg : 0 ≤ delta := by
    simpa [delta] using
      theorem32_uniform_doubled_explicit_delta_nonneg
        (m := m) hm (oldLevels := oldLevels) heps holdLevels
  have hgrid :
      ∀ i : Fin ((2 * m + 1) + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i := by
    exact
      theorem32_uniform_inner_grid_of_low_bisection_brackets
        (m := 2 * m + 1) returned hreturnedLevels
        htFirstStar0 hdelta_nonneg hfirstRate root lower
        hroot0
        (by simpa [tFirstStar] using htFirst_le_root)
        hroot_rate
        (by simpa [delta] using hbracket)
  exact
    theorem32_run_certificate_of_last_bisection_bracket
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned
      (lastBracketLower := lastBracketLower)
      holdLevels hlastBracket
      (by simpa [tFirstStar, delta] using hgrid)
      houter hinner

/--
Executable version of the source-style inner-grid constructor: each interior
`BisectNextLevel` call is represented by a real bisection run on the lower
endpoint with the canonical threshold classifier for its exact root.
-/
noncomputable def theorem32_run_certificate_of_outer_level_bracket_and_inner_low_bisection_runs
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps lastBracketLower : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlastBracket :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      EconCSLib.Optimization.RealBisectionBracket
        (optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        lastBracketLower
        (returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        delta)
    (hfirstRate :
      binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (root lower0 upper0 : Fin ((2 * m + 1) + 1) → ℝ)
    (hroot0 :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        0 < root i)
    (htFirst_le_root :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
          root i)
    (hroot_rate :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i)) (root i) =
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (hinnerLower0 :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        lower0 i ≤ root i)
    (hinnerUpper0 :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ upper0 i)
    (hinnerWidth :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (upper0 i - lower0 i) / (2 : ℝ) ^ innerSteps ≤
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLow :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps (lower0 i) (upper0 i)).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    Theorem32NestedBisectionRunCertificate
      (m := m) (M := M) (L := L) oldLevels returned eps := by
  let delta : ℝ :=
    eps /
      ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
        (((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
  have hbracket :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        EconCSLib.Optimization.RealBisectionBracket
          (root i)
          (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget (root i))
            innerSteps (lower0 i) (upper0 i)).1
          (returned (adjacentLowIndex i))
          delta := by
    intro i hi_first hi_last
    have B :
        EconCSLib.Optimization.RealBisectionBracket
          (root i)
          (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget (root i))
            innerSteps (lower0 i) (upper0 i)).1
          (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget (root i))
            innerSteps (lower0 i) (upper0 i)).2
          delta :=
      EconCSLib.Optimization.realBisectionRun_bracket_aboveTarget_of_width_le
        (n := innerSteps)
        (lower := lower0 i) (upper := upper0 i) (target := root i)
        (delta := delta)
        (hinnerLower0 i hi_first hi_last)
        (hinnerUpper0 i hi_first hi_last)
        (by simpa [delta] using hinnerWidth i hi_first hi_last)
    simpa [hreturnedLow i hi_first hi_last] using B
  exact
    theorem32_run_certificate_of_outer_level_bracket_and_inner_low_bisection_brackets
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned heps holdLevels hreturnedLevels hlastBracket
      hfirstRate root
      (fun i =>
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps (lower0 i) (upper0 i)).1)
      hroot0 htFirst_le_root hroot_rate
      (by simpa [delta] using hbracket)
      houter hinner

/--
Feasible-selector version of the source-style inner bisection constructor.
For each interior adjacent pair, the exact low-endpoint root is chosen by the
shared `weightedBernoulliLowEndpointOfRateOrFloor` inverse at the first
optimal doubled level.  Feasibility of that selector supplies the root
positivity, the lower bound by the first level, and the exact target-rate
identity used in the Theorem 3.2 grid argument.
-/
noncomputable def theorem32_run_certificate_of_outer_level_bracket_and_inner_low_bisection_runs_from_feasible_floor
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps lastBracketLower : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlastBracket :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      EconCSLib.Optimization.RealBisectionBracket
        (optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        lastBracketLower
        (returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        delta)
    (hfirstRate :
      binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (lower0 upper0 : Fin ((2 * m + 1) + 1) → ℝ)
    (hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hinnerLower0 :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        lower0 i ≤ root i)
    (hinnerUpper0 :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ upper0 i)
    (hinnerWidth :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (upper0 i - lower0 i) / (2 : ℝ) ^ innerSteps ≤
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps (lower0 i) (upper0 i)).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    Theorem32NestedBisectionRunCertificate
      (m := m) (M := M) (L := L) oldLevels returned eps := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ :=
    binaryEndpointAwareAdjacentRate returned
      (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
      (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
  let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  have hroot0 :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        0 < root i := by
    intro i hi_first hi_last
    have hmem :
        root i ∈ Set.Ioo tFirst (returned (adjacentHighIndex i)) := by
      simpa [root, tFirst, target] using
        weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
          (hfeasible i hi_first hi_last)
    exact (hfeasible i hi_first hi_last).hfloor0.trans hmem.1
  have htFirst_le_root :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
          root i := by
    intro i hi_first hi_last
    have hmem :
        root i ∈ Set.Ioo tFirst (returned (adjacentHighIndex i)) := by
      simpa [root, tFirst, target] using
        weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
          (hfeasible i hi_first hi_last)
    simpa [tFirst] using hmem.1.le
  have hroot_rate :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i)) (root i) =
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) := by
    intro i hi_first hi_last
    simpa [root, tFirst, target] using
      weightedBernoulliLowEndpointOfRateOrFloor_rate_of_feasible
        (hfeasible i hi_first hi_last)
  exact
    theorem32_run_certificate_of_outer_level_bracket_and_inner_low_bisection_runs
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned heps holdLevels hreturnedLevels hlastBracket
      hfirstRate root lower0 upper0 hroot0 htFirst_le_root hroot_rate
      (by simpa [root, tFirst, target] using hinnerLower0)
      (by simpa [root, tFirst, target] using hinnerUpper0)
      hinnerWidth
      (by simpa [root, tFirst, target] using hreturnedLow)
      houter hinner

/--
Endpoint-invariant version of the feasible-selector constructor.  The
first-rate comparison required by Theorem 3.2 is derived from the concrete
mirror inequality `1 - t₁ ≤ t_{last-low}` for the returned vector.
-/
noncomputable def theorem32_run_certificate_of_outer_level_bracket_and_inner_low_bisection_runs_from_feasible_floor_and_endpoint_mirror
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps lastBracketLower : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlastBracket :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      EconCSLib.Optimization.RealBisectionBracket
        (optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        lastBracketLower
        (returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        delta)
    (hmirror :
      1 -
          returned
            (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (lower0 upper0 : Fin ((2 * m + 1) + 1) → ℝ)
    (hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hinnerLower0 :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        lower0 i ≤ root i)
    (hinnerUpper0 :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ upper0 i)
    (hinnerWidth :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (upper0 i - lower0 i) / (2 : ℝ) ^ innerSteps ≤
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps (lower0 i) (upper0 i)).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    Theorem32NestedBisectionRunCertificate
      (m := m) (M := M) (L := L) oldLevels returned eps := by
  have hfirstRate :
      binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin ((2 * m + 1) + 1)) :=
    binaryEndpointAwareAdjacentRate_uniform_last_le_first_of_one_sub_first_high_le_last_low
      (m := 2 * m + 1) (by omega) returned hreturnedLevels hmirror
  exact
    theorem32_run_certificate_of_outer_level_bracket_and_inner_low_bisection_runs_from_feasible_floor
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned heps holdLevels hreturnedLevels hlastBracket
      hfirstRate lower0 upper0 hfeasible hinnerLower0 hinnerUpper0
      hinnerWidth hreturnedLow houter hinner

/--
Endpoint-lower-bound version of the feasible-selector constructor.  The
source shifting invariant can be supplied as the statement that the returned
first high endpoint and last low endpoint are both at least their equalized
doubled-chain counterparts; equalization turns those two endpoint inequalities
into the mirror condition used for the first-rate comparison.
-/
noncomputable def theorem32_run_certificate_of_outer_level_bracket_and_inner_low_bisection_runs_from_feasible_floor_and_endpoint_ge
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps lastBracketLower : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlastBracket :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      EconCSLib.Optimization.RealBisectionBracket
        (optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        lastBracketLower
        (returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        delta)
    (hfirst_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlast_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (lower0 upper0 : Fin ((2 * m + 1) + 1) → ℝ)
    (hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hinnerLower0 :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        lower0 i ≤ root i)
    (hinnerUpper0 :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ upper0 i)
    (hinnerWidth :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (upper0 i - lower0 i) / (2 : ℝ) ^ innerSteps ≤
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps (lower0 i) (upper0 i)).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    Theorem32NestedBisectionRunCertificate
      (m := m) (M := M) (L := L) oldLevels returned eps := by
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  have hoptimalLevels : BinaryEndpointLevelVector optimal := by
    simpa [optimal] using
      uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    simpa [optimal] using
      uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have hmirror :
      1 -
          returned
            (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
    exact
      BinaryEndpointAwareAdjacentRatesEqualize_uniform_endpoint_mirror_of_endpoint_ge
        (m := 2 * m + 1) (by omega) optimal returned
        hoptimalLevels hoptimalEq
        (by simpa [optimal] using hfirst_ge)
        (by simpa [optimal] using hlast_ge)
  exact
    theorem32_run_certificate_of_outer_level_bracket_and_inner_low_bisection_runs_from_feasible_floor_and_endpoint_mirror
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned heps holdLevels hreturnedLevels hlastBracket
      hmirror lower0 upper0 hfeasible hinnerLower0 hinnerUpper0
      hinnerWidth hreturnedLow houter hinner

/--
Executable outer-run version of the source-style Theorem 3.2 constructor.  The
outer bisection run supplies the final-low bracket; the inner calls are the
source low-endpoint bisections with feasible inverse roots and endpoint
lower-bound invariants.
-/
noncomputable def theorem32_run_certificate_of_outer_level_run_and_inner_low_bisection_runs_from_feasible_floor_and_endpoint_ge
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps levelLower0 levelUpper0 : ℝ}
    (levelAbove : ℝ → Bool)
    (innerLower0 innerUpper0 : Fin ((2 * m + 1) + 1) → ℝ)
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelAbove :
      ∀ x,
        levelAbove x = true →
          uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ x)
    (hlevelBelow :
      ∀ x,
        levelAbove x = false →
          x ≤
            uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlevelLower0 :
      levelLower0 ≤
        uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlevelUpper0 :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ levelUpper0)
    (hlevelWidth :
      (levelUpper0 - levelLower0) / (2 : ℝ) ^ outerSteps ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          levelAbove outerSteps levelLower0 levelUpper0).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfirst_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlast_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hinnerLower0 :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        innerLower0 i ≤ root i)
    (hinnerUpper0 :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ innerUpper0 i)
    (hinnerWidth :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (innerUpper0 i - innerLower0 i) / (2 : ℝ) ^ innerSteps ≤
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps (innerLower0 i) (innerUpper0 i)).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    Theorem32NestedBisectionRunCertificate
      (m := m) (M := M) (L := L) oldLevels returned eps := by
  let levelTarget : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let delta : ℝ :=
    eps /
      ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
        (((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
  have hlastBracket :
      EconCSLib.Optimization.RealBisectionBracket
        levelTarget
        (EconCSLib.Optimization.realBisectionRun
          levelAbove outerSteps levelLower0 levelUpper0).1
        (returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        delta := by
    have B :
        EconCSLib.Optimization.RealBisectionBracket
          levelTarget
          (EconCSLib.Optimization.realBisectionRun
            levelAbove outerSteps levelLower0 levelUpper0).1
          (EconCSLib.Optimization.realBisectionRun
            levelAbove outerSteps levelLower0 levelUpper0).2
          delta :=
      EconCSLib.Optimization.realBisectionRun_bracket_of_width_le
        (above := levelAbove) (n := outerSteps)
        (target := levelTarget) (lower := levelLower0) (upper := levelUpper0)
        (delta := delta)
        (by simpa [levelTarget] using hlevelAbove)
        (by simpa [levelTarget] using hlevelBelow)
        (by simpa [levelTarget] using hlevelLower0)
        (by simpa [levelTarget] using hlevelUpper0)
        (by simpa [delta] using hlevelWidth)
    simpa [hreturnedLast] using B
  exact
    theorem32_run_certificate_of_outer_level_bracket_and_inner_low_bisection_runs_from_feasible_floor_and_endpoint_ge
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned heps holdLevels holdEq hreturnedLevels
      (lastBracketLower :=
        (EconCSLib.Optimization.realBisectionRun
          levelAbove outerSteps levelLower0 levelUpper0).1)
      (by simpa [levelTarget, delta] using hlastBracket)
      hfirst_ge hlast_ge innerLower0 innerUpper0
      hfeasible hinnerLower0 hinnerUpper0 hinnerWidth hreturnedLow
      houter hinner

/--
The exact doubled equalized chain itself satisfies the Theorem 3.2 run
certificate with zero recorded bisection steps.  This is an implementation
sanity check for the certificate shape; it does not derive Algorithm 1's
returned vector from executable bisection semantics.
-/
def theorem32_uniform_doubled_exact_run_certificate
    {m M L : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    Theorem32NestedBisectionRunCertificate
      (m := m) (M := M) (L := L) oldLevels
      (uniformDoubledEndpointLevels oldLevels) eps := by
  let newLevels : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let uniform : Fin ((2 * m + 1) + 2) → ℝ := fun _ => (1 : ℝ)
  let delta : ℝ :=
    eps /
      ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
        (((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
  have hnewLevels : BinaryEndpointLevelVector newLevels := by
    simpa [newLevels] using
      uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hnewEq : BinaryEndpointAwareAdjacentRatesEqualize newLevels uniform := by
    simpa [newLevels, uniform] using
      uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have hdelta_nonneg : 0 ≤ delta := by
    simpa [delta] using
      theorem32_uniform_doubled_explicit_delta_nonneg
        (m := m) hm (oldLevels := oldLevels) heps holdLevels
  refine
    { outerSteps := 0
      innerSteps := 0
      hlast := ?_
      hgrid := ?_
      houter := by omega
      hinner := by omega }
  · dsimp
    have hlastLow_pos :
        0 <
          newLevels
            (adjacentLowIndex
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
      exact
        BinaryEndpointLevelVector_last_low_pos
          (m := 2 * m + 1) (by omega) hnewLevels
    have hratio_ge_one :
        1 ≤
          (newLevels
                (adjacentLowIndex
                  (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) +
              delta) /
            newLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
      rw [le_div_iff₀ hlastLow_pos]
      linarith
    have hlog_nonneg :
        0 ≤
          Real.log
            ((newLevels
                  (adjacentLowIndex
                    (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) +
                delta) /
              newLevels
                (adjacentLowIndex
                  (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))) :=
      Real.log_nonneg hratio_ge_one
    simpa [newLevels, uniform, delta] using
      sub_le_self
        (binaryEndpointAwareAdjacentRate newLevels uniform
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
        hlog_nonneg
  · dsimp
    intro i
    have hfirst_pos :
        0 <
          newLevels
            (adjacentHighIndex
              (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
      exact
        BinaryEndpointLevelVector_pos_of_not_first hnewLevels
          (adjacentHighIndex
            (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
          (by simp [adjacentHighIndex, firstAdjacentIndex])
    have hratio_ge_one :
        1 ≤
          (newLevels
                (adjacentHighIndex
                  (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) +
              delta) /
            newLevels
              (adjacentHighIndex
                (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
      rw [le_div_iff₀ hfirst_pos]
      linarith
    have hlog_nonneg :
        0 ≤
          Real.log
            ((newLevels
                  (adjacentHighIndex
                    (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) +
                delta) /
              newLevels
                (adjacentHighIndex
                  (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))) :=
      Real.log_nonneg hratio_ge_one
    have hrate_eq :
        binaryEndpointAwareAdjacentRate newLevels uniform
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) =
          binaryEndpointAwareAdjacentRate newLevels uniform i :=
      hnewEq (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) i
    have hstep :
        binaryEndpointAwareAdjacentRate newLevels uniform
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) -
            Real.log
              ((newLevels
                    (adjacentHighIndex
                      (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) +
                  delta) /
                newLevels
                  (adjacentHighIndex
                    (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))) ≤
          binaryEndpointAwareAdjacentRate newLevels uniform i :=
      (sub_le_self
        (binaryEndpointAwareAdjacentRate newLevels uniform
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
        hlog_nonneg).trans (le_of_eq hrate_eq)
    simpa [newLevels, uniform, delta] using hstep

/--
Theorem 3.2 explicit-delta statement from a named source-level
`NestedBisection` run certificate.  The proof is the checked approximation and
runtime argument above; constructing the certificate from executable
pseudocode remains the separate algorithm-semantics boundary.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_run_certificate
    {m M L : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (run : Theorem32NestedBisectionRunCertificate
      (m := m) (M := M) (L := L) oldLevels returned eps) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M run.outerSteps run.innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_uniform_doubled_closed_run_explicit_delta_auto_lower
      hm oldLevels returned heps holdLevels holdEq
      run.hlast run.hgrid run.houter run.hinner

/--
Theorem 3.2 finite loss/runtime endpoint from source-style level-space
bisection brackets.  The inner-grid condition is derived from
`CalculateOtherLevels`-style low-endpoint brackets rather than assumed as a
rate-space certificate.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_low_bisection_brackets
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps lastBracketLower : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlastBracket :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      EconCSLib.Optimization.RealBisectionBracket
        (optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        lastBracketLower
        (returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        delta)
    (hfirstRate :
      binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (root lower : Fin ((2 * m + 1) + 1) → ℝ)
    (hroot0 :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        0 < root i)
    (htFirst_le_root :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
          root i)
    (hroot_rate :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i)) (root i) =
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (hbracket :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        EconCSLib.Optimization.RealBisectionBracket
          (root i) (lower i) (returned (adjacentLowIndex i))
          (eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let run :=
    theorem32_run_certificate_of_outer_level_bracket_and_inner_low_bisection_brackets
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned heps holdLevels hreturnedLevels hlastBracket
      hfirstRate root lower hroot0 htFirst_le_root hroot_rate hbracket
      houter hinner
  simpa [run] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_run_certificate
      (m := m) (M := M) (L := L)
      hm oldLevels returned heps holdLevels holdEq run

/--
Theorem 3.2 finite loss/runtime endpoint from canonical executable bisection
runs for the source-style inner low-endpoint searches.  The only remaining
inputs are the source invariants identifying each exact low-endpoint root,
the first-rate comparison maintained by `CalculateOtherLevels`, and the
outer final-low bracket.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_low_bisection_runs
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps lastBracketLower : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlastBracket :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      EconCSLib.Optimization.RealBisectionBracket
        (optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        lastBracketLower
        (returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        delta)
    (hfirstRate :
      binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (root lower0 upper0 : Fin ((2 * m + 1) + 1) → ℝ)
    (hroot0 :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        0 < root i)
    (htFirst_le_root :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
          root i)
    (hroot_rate :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i)) (root i) =
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (hinnerLower0 :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        lower0 i ≤ root i)
    (hinnerUpper0 :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ upper0 i)
    (hinnerWidth :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (upper0 i - lower0 i) / (2 : ℝ) ^ innerSteps ≤
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLow :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps (lower0 i) (upper0 i)).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let run :=
    theorem32_run_certificate_of_outer_level_bracket_and_inner_low_bisection_runs
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned heps holdLevels hreturnedLevels hlastBracket
      hfirstRate root lower0 upper0 hroot0 htFirst_le_root hroot_rate
      hinnerLower0 hinnerUpper0 hinnerWidth hreturnedLow houter hinner
  simpa [run] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_run_certificate
      (m := m) (M := M) (L := L)
      hm oldLevels returned heps holdLevels holdEq run

/--
Theorem 3.2 finite loss/runtime endpoint from executable source-style inner
low-endpoint searches, with the exact low-endpoint roots generated by the
shared feasible inverse selector at the first doubled optimal level.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_feasible_low_bisection_runs
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps lastBracketLower : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlastBracket :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      EconCSLib.Optimization.RealBisectionBracket
        (optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        lastBracketLower
        (returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        delta)
    (hfirstRate :
      binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (lower0 upper0 : Fin ((2 * m + 1) + 1) → ℝ)
    (hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hinnerLower0 :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        lower0 i ≤ root i)
    (hinnerUpper0 :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ upper0 i)
    (hinnerWidth :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (upper0 i - lower0 i) / (2 : ℝ) ^ innerSteps ≤
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps (lower0 i) (upper0 i)).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let run :=
    theorem32_run_certificate_of_outer_level_bracket_and_inner_low_bisection_runs_from_feasible_floor
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned heps holdLevels hreturnedLevels hlastBracket
      hfirstRate lower0 upper0 hfeasible hinnerLower0 hinnerUpper0
      hinnerWidth hreturnedLow houter hinner
  simpa [run] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_run_certificate
      (m := m) (M := M) (L := L)
      hm oldLevels returned heps holdLevels holdEq run

/--
Theorem 3.2 finite loss/runtime endpoint from an executable outer final-level
bisection run and executable source-style inner low-endpoint bisection runs.
Endpoint lower bounds against the equalized doubled chain supply the
first-rate invariant.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_feasible_low_bisection_runs
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps levelLower0 levelUpper0 : ℝ}
    (levelAbove : ℝ → Bool)
    (innerLower0 innerUpper0 : Fin ((2 * m + 1) + 1) → ℝ)
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelAbove :
      ∀ x,
        levelAbove x = true →
          uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ x)
    (hlevelBelow :
      ∀ x,
        levelAbove x = false →
          x ≤
            uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlevelLower0 :
      levelLower0 ≤
        uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlevelUpper0 :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ levelUpper0)
    (hlevelWidth :
      (levelUpper0 - levelLower0) / (2 : ℝ) ^ outerSteps ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          levelAbove outerSteps levelLower0 levelUpper0).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfirst_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlast_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hinnerLower0 :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        innerLower0 i ≤ root i)
    (hinnerUpper0 :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ innerUpper0 i)
    (hinnerWidth :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (innerUpper0 i - innerLower0 i) / (2 : ℝ) ^ innerSteps ≤
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps (innerLower0 i) (innerUpper0 i)).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let run :=
    theorem32_run_certificate_of_outer_level_run_and_inner_low_bisection_runs_from_feasible_floor_and_endpoint_ge
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned levelAbove innerLower0 innerUpper0 heps
      holdLevels holdEq hreturnedLevels
      hlevelAbove hlevelBelow hlevelLower0 hlevelUpper0 hlevelWidth
      hreturnedLast hfirst_ge hlast_ge hfeasible
      hinnerLower0 hinnerUpper0 hinnerWidth hreturnedLow houter hinner
  simpa [run] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_run_certificate
      (m := m) (M := M) (L := L)
      hm oldLevels returned heps holdLevels holdEq run

/--
Theorem 3.2 finite loss/runtime endpoint with source-shaped initial brackets
for each inner low-endpoint bisection: lower endpoint `0`, upper endpoint the
current high endpoint.  Feasibility of the low-endpoint inverse supplies the
root-bracketing facts automatically.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_feasible_low_bisection_runs_from_zero_to_high
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps levelLower0 levelUpper0 : ℝ}
    (levelAbove : ℝ → Bool)
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelAbove :
      ∀ x,
        levelAbove x = true →
          uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ x)
    (hlevelBelow :
      ∀ x,
        levelAbove x = false →
          x ≤
            uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlevelLower0 :
      levelLower0 ≤
        uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlevelUpper0 :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ levelUpper0)
    (hlevelWidth :
      (levelUpper0 - levelLower0) / (2 : ℝ) ^ outerSteps ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          levelAbove outerSteps levelLower0 levelUpper0).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfirst_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlast_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hinnerWidth :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (returned (adjacentHighIndex i) - 0) / (2 : ℝ) ^ innerSteps ≤
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ :=
    binaryEndpointAwareAdjacentRate returned
      (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
      (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
  let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  have hinnerLower0 :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (fun _ : Fin ((2 * m + 1) + 1) => (0 : ℝ)) i ≤ root i := by
    intro i hi_first hi_last
    have hmem :
        root i ∈ Set.Ioo tFirst (returned (adjacentHighIndex i)) := by
      simpa [root, tFirst, target] using
        weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
          (hfeasible i hi_first hi_last)
    exact (le_of_lt ((hfeasible i hi_first hi_last).hfloor0.trans hmem.1))
  have hinnerUpper0 :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ (fun i => returned (adjacentHighIndex i)) i := by
    intro i hi_first hi_last
    have hmem :
        root i ∈ Set.Ioo tFirst (returned (adjacentHighIndex i)) := by
      simpa [root, tFirst, target] using
        weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
          (hfeasible i hi_first hi_last)
    exact hmem.2.le
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_feasible_low_bisection_runs
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned levelAbove
      (fun _ : Fin ((2 * m + 1) + 1) => (0 : ℝ))
      (fun i => returned (adjacentHighIndex i))
      heps holdLevels holdEq hreturnedLevels hlevelAbove hlevelBelow
      hlevelLower0 hlevelUpper0 hlevelWidth hreturnedLast
      hfirst_ge hlast_ge hfeasible
      (by simpa [root, tFirst, target] using hinnerLower0)
      (by simpa [root, tFirst, target] using hinnerUpper0)
      (by simpa using hinnerWidth)
      (by simpa [root, tFirst, target] using hreturnedLow)
      houter hinner

/--
Same source-initial-bracket Theorem 3.2 endpoint, but with the returned
last-low lower bound derived from the outer bisection bracket.  The only
endpoint-side invariant left explicit is the first refined level's lower
bound.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_feasible_low_bisection_runs_from_zero_to_high_first_ge
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps levelLower0 levelUpper0 : ℝ}
    (levelAbove : ℝ → Bool)
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelAbove :
      ∀ x,
        levelAbove x = true →
          uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ x)
    (hlevelBelow :
      ∀ x,
        levelAbove x = false →
          x ≤
            uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlevelLower0 :
      levelLower0 ≤
        uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlevelUpper0 :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ levelUpper0)
    (hlevelWidth :
      (levelUpper0 - levelLower0) / (2 : ℝ) ^ outerSteps ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          levelAbove outerSteps levelLower0 levelUpper0).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfirst_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hinnerWidth :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (returned (adjacentHighIndex i) - 0) / (2 : ℝ) ^ innerSteps ≤
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let levelTarget : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let delta : ℝ :=
    eps /
      ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
        (((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
  have B :
      EconCSLib.Optimization.RealBisectionBracket
        levelTarget
        (EconCSLib.Optimization.realBisectionRun
          levelAbove outerSteps levelLower0 levelUpper0).1
        (EconCSLib.Optimization.realBisectionRun
          levelAbove outerSteps levelLower0 levelUpper0).2
        delta :=
    EconCSLib.Optimization.realBisectionRun_bracket_of_width_le
      (above := levelAbove) (n := outerSteps)
      (target := levelTarget) (lower := levelLower0) (upper := levelUpper0)
      (delta := delta)
      (by simpa [levelTarget] using hlevelAbove)
      (by simpa [levelTarget] using hlevelBelow)
      (by simpa [levelTarget] using hlevelLower0)
      (by simpa [levelTarget] using hlevelUpper0)
      (by simpa [delta] using hlevelWidth)
  have hlast_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
    simpa [levelTarget, hreturnedLast] using B.target_le_upper
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_feasible_low_bisection_runs_from_zero_to_high
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned levelAbove heps holdLevels holdEq
      hreturnedLevels hlevelAbove hlevelBelow hlevelLower0 hlevelUpper0
      hlevelWidth hreturnedLast hfirst_ge hlast_ge hfeasible hinnerWidth
      hreturnedLow houter hinner

/--
Source-initial-bracket Theorem 3.2 endpoint with the first refined endpoint
lower bound derived from the first inner low-endpoint bisection.  The first
interior root is at least the equalized doubled first level by construction,
and the returned first level is the bisection upper endpoint.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_feasible_low_bisection_runs_from_zero_to_high_auto_first
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps levelLower0 levelUpper0 : ℝ}
    (levelAbove : ℝ → Bool)
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelAbove :
      ∀ x,
        levelAbove x = true →
          uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ x)
    (hlevelBelow :
      ∀ x,
        levelAbove x = false →
          x ≤
            uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlevelLower0 :
      levelLower0 ≤
        uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlevelUpper0 :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ levelUpper0)
    (hlevelWidth :
      (levelUpper0 - levelLower0) / (2 : ℝ) ^ outerSteps ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          levelAbove outerSteps levelLower0 levelUpper0).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hinnerWidth :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (returned (adjacentHighIndex i) - 0) / (2 : ℝ) ^ innerSteps ≤
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ :=
    binaryEndpointAwareAdjacentRate returned
      (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
      (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
  let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  let firstInterior : Fin ((2 * m + 1) + 1) := ⟨1, by omega⟩
  have hfirstInterior_not_first : firstInterior.val ≠ 0 := by
    simp [firstInterior]
  have hfirstInterior_not_last : firstInterior.val ≠ 2 * m + 1 := by
    simp [firstInterior]
    omega
  have hroot_mem :
      root firstInterior ∈
        Set.Ioo tFirst (returned (adjacentHighIndex firstInterior)) := by
    simpa [root, tFirst, target] using
      weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
        (hfeasible firstInterior hfirstInterior_not_first hfirstInterior_not_last)
  let delta : ℝ :=
    eps /
      ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
        (((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
  have B :
      EconCSLib.Optimization.RealBisectionBracket
        (root firstInterior)
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (root firstInterior))
          innerSteps 0 (returned (adjacentHighIndex firstInterior))).1
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (root firstInterior))
          innerSteps 0 (returned (adjacentHighIndex firstInterior))).2
        delta :=
    EconCSLib.Optimization.realBisectionRun_bracket_aboveTarget_of_width_le
      (n := innerSteps) (lower := 0)
      (upper := returned (adjacentHighIndex firstInterior))
      (target := root firstInterior) (delta := delta)
      (le_of_lt ((hfeasible firstInterior hfirstInterior_not_first
        hfirstInterior_not_last).hfloor0.trans hroot_mem.1))
      hroot_mem.2.le
      (by
        simpa [delta] using
          hinnerWidth firstInterior hfirstInterior_not_first
            hfirstInterior_not_last)
  have hfirst_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
    have hroot_le_returned :
        root firstInterior ≤ returned (adjacentLowIndex firstInterior) := by
      have hret :
          (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget
              (root firstInterior))
            innerSteps 0 (returned (adjacentHighIndex firstInterior))).2 =
            returned (adjacentLowIndex firstInterior) := by
        simpa [root, tFirst, target] using
          hreturnedLow firstInterior hfirstInterior_not_first
            hfirstInterior_not_last
      simpa [hret] using B.target_le_upper
    calc
      uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
          root firstInterior := by
            simpa [tFirst] using hroot_mem.1.le
      _ ≤ returned (adjacentLowIndex firstInterior) := hroot_le_returned
      _ =
          returned
            (adjacentHighIndex
              (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
            simp [firstInterior, adjacentLowIndex, adjacentHighIndex,
              firstAdjacentIndex]
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_feasible_low_bisection_runs_from_zero_to_high_first_ge
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned levelAbove heps holdLevels holdEq
      hreturnedLevels hlevelAbove hlevelBelow hlevelLower0 hlevelUpper0
      hlevelWidth hreturnedLast hfirst_ge hfeasible hinnerWidth
      hreturnedLow houter hinner

/--
Theorem 3.2 endpoint with the paper's source lower endpoint for the outer
bisection.  Lemma C.6, applied to the C.5 doubled equalized chain, proves that
the optimal final low endpoint lies above `1 - 1 / (number of adjacent
intervals)`.  The width assumptions are stated in the source-shaped form
`initial width ≤ tolerance * 2^steps`.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_feasible_low_bisection_runs_from_source_lower_global_width
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps levelUpper0 : ℝ}
    (levelAbove : ℝ → Bool)
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelAbove :
      ∀ x,
        levelAbove x = true →
          uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ x)
    (hlevelBelow :
      ∀ x,
        levelAbove x = false →
          x ≤
            uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlevelUpper0 :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ levelUpper0)
    (hlevelWidth :
      levelUpper0 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          levelAbove outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          levelUpper0).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (hreturnedLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  have hoptimalLevels :
      BinaryEndpointLevelVector (uniformDoubledEndpointLevels oldLevels) := by
    simpa using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    exact uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have hlevelLower0 :
      1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)) ≤
        uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
    simpa using
      BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
        (m := 2 * m + 1) (by omega) hoptimalLevels hoptimalEq
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_feasible_low_bisection_runs_from_zero_to_high_auto_first
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned levelAbove heps holdLevels holdEq
      hreturnedLevels hlevelAbove hlevelBelow hlevelLower0 hlevelUpper0
      (EconCSLib.Optimization.width_div_pow_two_le_of_le_delta_mul_pow_two
        hlevelWidth)
      hreturnedLast hfeasible
      (fun i hi_first hi_last =>
        EconCSLib.Optimization.width_div_pow_two_le_of_le_delta_mul_pow_two
          (by
            have hhigh_le_one :
                returned (adjacentHighIndex i) ≤ 1 :=
              BinaryEndpointLevelVector_le_one hreturnedLevels
                (adjacentHighIndex i)
            linarith))
      hreturnedLow houter hinner

/--
Source-outer-classifier version of the preceding Theorem 3.2 endpoint.  The
outer loop predicate is now exactly Algorithm 1's `ratefirst < ratelast`
branch, packaged as `theorem32OuterSourceRateAbove`; callers provide the
source shifting invariant that makes the two Boolean branches bracket the
optimal final-low endpoint.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_source_rate_run_feasible_low_bisection_runs_from_source_lower_global_width
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps levelUpper0 : ℝ}
    (candidate : ℝ → Fin ((2 * m + 1) + 2) → ℝ)
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hsourceAbove :
      ∀ x,
        binaryEndpointAwareAdjacentRate (candidate x)
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) ≤
          binaryEndpointAwareAdjacentRate (candidate x)
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (firstAdjacentIndex : Fin ((2 * m + 1) + 1)) →
        uniformDoubledEndpointLevels oldLevels
            (adjacentLowIndex
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ x)
    (hsourceBelow :
      ∀ x,
        binaryEndpointAwareAdjacentRate (candidate x)
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (firstAdjacentIndex : Fin ((2 * m + 1) + 1)) <
          binaryEndpointAwareAdjacentRate (candidate x)
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) →
        x ≤
          uniformDoubledEndpointLevels oldLevels
            (adjacentLowIndex
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlevelUpper0 :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ levelUpper0)
    (hlevelWidth :
      levelUpper0 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (fun x => theorem32OuterSourceRateAbove (candidate x))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          levelUpper0).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (hreturnedLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_feasible_low_bisection_runs_from_source_lower_global_width
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned
      (fun x => theorem32OuterSourceRateAbove (candidate x))
      heps holdLevels holdEq hreturnedLevels
      (theorem32OuterSourceRateAbove_true_sound
        (n := 2 * m + 1)
        (levelTarget :=
          uniformDoubledEndpointLevels oldLevels
            (adjacentLowIndex
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        candidate hsourceAbove)
      (theorem32OuterSourceRateAbove_false_sound
        (n := 2 * m + 1)
        (levelTarget :=
          uniformDoubledEndpointLevels oldLevels
            (adjacentLowIndex
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        candidate hsourceBelow)
      hlevelUpper0 hlevelWidth hreturnedLast hfeasible
      hinnerWidth hreturnedLow houter hinner

/--
Canonical-threshold, upper-one version of the source-lower feasible-root
Theorem 3.2 endpoint.  This is the source-shaped low-endpoint
`BisectNextLevel` interface: the reusable inverse-rate feasibility certificate
is supplied directly, while the outer classifier and upper bracket are
discharged by bisection on
`[1 - 1 / (number of refined adjacent intervals), 1]`.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_threshold_run_feasible_low_bisection_runs_from_source_lower_upper_one
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (hreturnedLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let levelTarget : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hoptimalLevels :
      BinaryEndpointLevelVector (uniformDoubledEndpointLevels oldLevels) := by
    simpa using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hlevelUpper0 : levelTarget ≤ (1 : ℝ) := by
    simpa [levelTarget] using
      BinaryEndpointLevelVector_le_one hoptimalLevels
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_feasible_low_bisection_runs_from_source_lower_global_width
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned
      (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
      heps holdLevels holdEq hreturnedLevels
      (by
        intro x hx
        simpa [levelTarget] using
          EconCSLib.Optimization.realBisectionAboveTarget_true hx)
      (by
        intro x hx
        simpa [levelTarget] using
          EconCSLib.Optimization.realBisectionAboveTarget_false hx)
      (by simpa [levelTarget] using hlevelUpper0)
      hlevelWidth
      (by simpa [levelTarget] using hreturnedLast)
      hfeasible hinnerWidth hreturnedLow houter hinner

/--
Canonical-threshold Theorem 3.2 endpoint with Algorithm 1's outer upper
endpoint `1 - grid`.  This specializes the generic source-lower bisection
wrapper to the interval used in the supplement after the paper assumes the
refined penultimate optimum is below the grid ceiling.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_threshold_run_feasible_low_bisection_runs_from_source_lower_upper_one_sub_grid
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps grid : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelUpper0 :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        1 - grid)
    (hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (hreturnedLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let levelTarget : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_feasible_low_bisection_runs_from_source_lower_global_width
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned
      (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
      heps holdLevels holdEq hreturnedLevels
      (by
        intro x hx
        simpa [levelTarget] using
          EconCSLib.Optimization.realBisectionAboveTarget_true hx)
      (by
        intro x hx
        simpa [levelTarget] using
          EconCSLib.Optimization.realBisectionAboveTarget_false hx)
      (by simpa [levelTarget] using hlevelUpper0)
      (by simpa [levelTarget] using hlevelWidth)
      (by simpa [levelTarget] using hreturnedLast)
      hfeasible hinnerWidth hreturnedLow houter hinner

/--
Algorithm-1 grid-ceiling wrapper whose inner feasibility is recovered from the
source fact that each exact clipped low-endpoint selector moves strictly above
the fixed floor.  This avoids exposing the stronger floor-rate inequality in
the source-facing Theorem 3.2 interface.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_threshold_run_feasible_low_bisection_runs_from_source_lower_upper_one_sub_grid_floor_lt_root
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps grid : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelUpper0 :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        1 - grid)
    (hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfloor_lt_root :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        tFirst < root i)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (hreturnedLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ :=
    binaryEndpointAwareAdjacentRate returned
      (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
      (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
  let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  have hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target := by
    dsimp at hfloor_lt_root ⊢
    intro i hi_first hi_last
    exact
      weightedBernoulliLowEndpointTargetFeasible_of_floor_lt_lowEndpointOfRateOrFloor
        (by
          simpa [tFirst, target, root] using
            hfloor_lt_root i hi_first hi_last)
  simpa [tFirst, target, root] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_threshold_run_feasible_low_bisection_runs_from_source_lower_upper_one_sub_grid
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned heps holdLevels holdEq hreturnedLevels
      hlevelUpper0 hlevelWidth hreturnedLast hfeasible hinnerWidth
      hreturnedLow houter hinner

/--
Theorem 3.2 endpoint with the paper's source lower endpoint for the outer
bisection and explicit exact roots for the inner `BisectNextLevel` calls.
This is the source-loop form of the argument: each interior low endpoint is
returned by bisection around the exact level whose closed adjacent rate equals
the final adjacent rate, avoiding the stronger feasible-floor certificate.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_low_bisection_runs_from_source_lower_exact_roots
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps levelUpper0 : ℝ}
    (levelAbove : ℝ → Bool)
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelAbove :
      ∀ x,
        levelAbove x = true →
          uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ x)
    (hlevelBelow :
      ∀ x,
        levelAbove x = false →
          x ≤
            uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlevelUpper0 :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ levelUpper0)
    (hlevelWidth :
      levelUpper0 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          levelAbove outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          levelUpper0).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfirstRate :
      binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (root : Fin ((2 * m + 1) + 1) → ℝ)
    (hroot0 :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        0 < root i)
    (htFirst_le_root :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
          root i)
    (hroot_le_high :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ returned (adjacentHighIndex i))
    (hroot_rate :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i)) (root i) =
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (hreturnedLow :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let levelLower0 : ℝ :=
    1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
  let delta : ℝ :=
    eps /
      ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
        (((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
  let levelRun : ℝ × ℝ :=
    EconCSLib.Optimization.realBisectionRun
      levelAbove outerSteps levelLower0 levelUpper0
  have hoptimalLevels :
      BinaryEndpointLevelVector (uniformDoubledEndpointLevels oldLevels) := by
    simpa using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    exact uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have hlevelLower0 :
      levelLower0 ≤
        uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
    simpa [levelLower0] using
      BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
        (m := 2 * m + 1) (by omega) hoptimalLevels hoptimalEq
  have hlastBracket :
      EconCSLib.Optimization.RealBisectionBracket
        (uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        levelRun.1
        (returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        delta := by
    have B :
        EconCSLib.Optimization.RealBisectionBracket
          (uniformDoubledEndpointLevels oldLevels
            (adjacentLowIndex
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
          levelRun.1 levelRun.2 delta := by
      exact
        EconCSLib.Optimization.realBisectionRun_bracket_of_width_le
          (above := levelAbove) (n := outerSteps)
          (target :=
            uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
          (lower := levelLower0) (upper := levelUpper0) (delta := delta)
          hlevelAbove hlevelBelow hlevelLower0 hlevelUpper0
          (by
            simpa [levelLower0, delta] using
              EconCSLib.Optimization.width_div_pow_two_le_of_le_delta_mul_pow_two
                hlevelWidth)
    have hupper :
        levelRun.2 =
          returned
            (adjacentLowIndex
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
      simpa [levelRun, levelLower0] using hreturnedLast
    simpa [hupper] using B
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_low_bisection_runs
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned heps holdLevels holdEq hreturnedLevels
      (lastBracketLower := levelRun.1)
      (by simpa [delta] using hlastBracket)
      hfirstRate root
      (fun _ => 0)
      (fun i => returned (adjacentHighIndex i))
      hroot0 htFirst_le_root hroot_rate
      (fun i hi_first hi_last => (hroot0 i hi_first hi_last).le)
      hroot_le_high
      (fun i _hi_first _hi_last =>
        EconCSLib.Optimization.width_div_pow_two_le_of_le_delta_mul_pow_two
          (by
            have hhigh_le_one :
                returned (adjacentHighIndex i) ≤ 1 :=
              BinaryEndpointLevelVector_le_one hreturnedLevels
                (adjacentHighIndex i)
            linarith))
      hreturnedLow houter hinner

/--
Source-lower exact-root Theorem 3.2 endpoint with the first-rate comparison
derived from the final endpoints.  The first returned high endpoint comes from
the upper endpoint of the first inner bisection, while the last returned low
endpoint comes from the upper endpoint of the outer bisection; the equalized
doubled chain then supplies the endpoint mirror inequality.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_low_bisection_runs_from_source_lower_exact_roots_auto_first
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps levelUpper0 : ℝ}
    (levelAbove : ℝ → Bool)
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelAbove :
      ∀ x,
        levelAbove x = true →
          uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ x)
    (hlevelBelow :
      ∀ x,
        levelAbove x = false →
          x ≤
            uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlevelUpper0 :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ levelUpper0)
    (hlevelWidth :
      levelUpper0 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          levelAbove outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          levelUpper0).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (root : Fin ((2 * m + 1) + 1) → ℝ)
    (hroot0 :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        0 < root i)
    (htFirst_le_root :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
          root i)
    (hroot_le_high :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ returned (adjacentHighIndex i))
    (hroot_rate :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i)) (root i) =
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (hreturnedLow :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let levelLower0 : ℝ :=
    1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
  let delta : ℝ :=
    eps /
      ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
        (((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
  let levelRun : ℝ × ℝ :=
    EconCSLib.Optimization.realBisectionRun
      levelAbove outerSteps levelLower0 levelUpper0
  have hoptimalLevels :
      BinaryEndpointLevelVector (uniformDoubledEndpointLevels oldLevels) := by
    simpa using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    exact uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have hlevelLower0 :
      levelLower0 ≤
        uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
    simpa [levelLower0] using
      BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
        (m := 2 * m + 1) (by omega) hoptimalLevels hoptimalEq
  have Blast :
      EconCSLib.Optimization.RealBisectionBracket
        (uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        levelRun.1 levelRun.2 delta := by
    exact
      EconCSLib.Optimization.realBisectionRun_bracket_of_width_le
        (above := levelAbove) (n := outerSteps)
        (target :=
          uniformDoubledEndpointLevels oldLevels
            (adjacentLowIndex
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        (lower := levelLower0) (upper := levelUpper0) (delta := delta)
        hlevelAbove hlevelBelow hlevelLower0 hlevelUpper0
        (by
          simpa [levelLower0, delta] using
            EconCSLib.Optimization.width_div_pow_two_le_of_le_delta_mul_pow_two
              hlevelWidth)
  have hlast_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
    have hupper :
        levelRun.2 =
          returned
            (adjacentLowIndex
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
      simpa [levelRun, levelLower0] using hreturnedLast
    simpa [hupper] using Blast.target_le_upper
  let firstInterior : Fin ((2 * m + 1) + 1) := ⟨1, by omega⟩
  have hfirstInterior_not_first : firstInterior.val ≠ 0 := by
    simp [firstInterior]
  have hfirstInterior_not_last : firstInterior.val ≠ 2 * m + 1 := by
    simp [firstInterior]
    omega
  have Bfirst :
      EconCSLib.Optimization.RealBisectionBracket
        (root firstInterior)
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (root firstInterior))
          innerSteps 0 (returned (adjacentHighIndex firstInterior))).1
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (root firstInterior))
          innerSteps 0 (returned (adjacentHighIndex firstInterior))).2
        delta :=
    EconCSLib.Optimization.realBisectionRun_bracket_aboveTarget_of_width_le
      (n := innerSteps) (lower := 0)
      (upper := returned (adjacentHighIndex firstInterior))
      (target := root firstInterior) (delta := delta)
      (hroot0 firstInterior hfirstInterior_not_first hfirstInterior_not_last).le
      (hroot_le_high firstInterior hfirstInterior_not_first
        hfirstInterior_not_last)
      (by
        simpa [delta] using
          EconCSLib.Optimization.width_div_pow_two_le_of_le_delta_mul_pow_two
            (by
              have hhigh_le_one :
                  returned (adjacentHighIndex firstInterior) ≤ 1 :=
                BinaryEndpointLevelVector_le_one hreturnedLevels
                  (adjacentHighIndex firstInterior)
              have hdelta_width : 1 ≤ delta * (2 : ℝ) ^ innerSteps := by
                simpa [delta] using hinnerWidth
              simpa [delta] using le_trans hhigh_le_one hdelta_width))
  have hfirst_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
    have hroot_le_returned :
        root firstInterior ≤ returned (adjacentLowIndex firstInterior) := by
      have hret :
          (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget
              (root firstInterior))
            innerSteps 0 (returned (adjacentHighIndex firstInterior))).2 =
            returned (adjacentLowIndex firstInterior) := by
        simpa using
          hreturnedLow firstInterior hfirstInterior_not_first
            hfirstInterior_not_last
      simpa [hret] using Bfirst.target_le_upper
    calc
      uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
          root firstInterior := by
            exact htFirst_le_root firstInterior hfirstInterior_not_first
              hfirstInterior_not_last
      _ ≤ returned (adjacentLowIndex firstInterior) := hroot_le_returned
      _ =
          returned
            (adjacentHighIndex
              (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
            simp [firstInterior, adjacentLowIndex, adjacentHighIndex,
              firstAdjacentIndex]
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  have hmirror :
      1 -
          returned
            (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) :=
    BinaryEndpointAwareAdjacentRatesEqualize_uniform_endpoint_mirror_of_endpoint_ge
      (m := 2 * m + 1) (by omega) optimal returned
      (by simpa [optimal] using hoptimalLevels)
      (by simpa [optimal] using hoptimalEq)
      (by simpa [optimal] using hfirst_ge)
      (by simpa [optimal] using hlast_ge)
  have hfirstRate :
      binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin ((2 * m + 1) + 1)) :=
    binaryEndpointAwareAdjacentRate_uniform_last_le_first_of_one_sub_first_high_le_last_low
      (m := 2 * m + 1) (by omega) returned hreturnedLevels hmirror
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_low_bisection_runs_from_source_lower_exact_roots
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned levelAbove heps holdLevels holdEq hreturnedLevels
      hlevelAbove hlevelBelow hlevelUpper0 hlevelWidth hreturnedLast
      hfirstRate root hroot0 htFirst_le_root hroot_le_high hroot_rate
      hinnerWidth hreturnedLow houter hinner

/--
Canonical-threshold source-lower exact-root Theorem 3.2 endpoint.  This
specializes the outer bisection predicate to the reusable threshold classifier,
so the outer midpoint-classifier soundness no longer appears as a paper-facing
premise.  The remaining assumptions are the source Algorithm 1 loop data:
the returned outer endpoint, exact inner roots, inner bisection returns, and
the two width budgets.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_threshold_run_low_bisection_runs_from_source_lower_exact_roots_auto_first
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps levelUpper0 : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelUpper0 :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ levelUpper0)
    (hlevelWidth :
      levelUpper0 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          levelUpper0).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (root : Fin ((2 * m + 1) + 1) → ℝ)
    (hroot0 :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        0 < root i)
    (htFirst_le_root :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
          root i)
    (hroot_le_high :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ returned (adjacentHighIndex i))
    (hroot_rate :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i)) (root i) =
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (hreturnedLow :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let levelTarget : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_low_bisection_runs_from_source_lower_exact_roots_auto_first
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned
      (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
      heps holdLevels holdEq hreturnedLevels
      (by
        intro x hx
        simpa [levelTarget] using
          EconCSLib.Optimization.realBisectionAboveTarget_true hx)
      (by
        intro x hx
        simpa [levelTarget] using
          EconCSLib.Optimization.realBisectionAboveTarget_false hx)
      hlevelUpper0 hlevelWidth
      (by simpa [levelTarget] using hreturnedLast)
      root hroot0 htFirst_le_root hroot_le_high hroot_rate
      hinnerWidth hreturnedLow houter hinner

/--
Canonical-threshold exact-root Theorem 3.2 endpoint with outer upper endpoint
`1`.  The source lower endpoint is
`1 - 1 / (number of refined adjacent intervals)`, and the upper bracket
condition is derived from the endpoint-vector invariant.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_threshold_run_low_bisection_runs_from_source_lower_exact_roots_upper_one_auto_first
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (root : Fin ((2 * m + 1) + 1) → ℝ)
    (hroot0 :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        0 < root i)
    (htFirst_le_root :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
          root i)
    (hroot_le_high :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ returned (adjacentHighIndex i))
    (hroot_rate :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i)) (root i) =
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (hreturnedLow :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  have hoptimalLevels :
      BinaryEndpointLevelVector (uniformDoubledEndpointLevels oldLevels) := by
    simpa using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hlevelUpper0 :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ (1 : ℝ) :=
    BinaryEndpointLevelVector_le_one hoptimalLevels
      (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_threshold_run_low_bisection_runs_from_source_lower_exact_roots_auto_first
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned heps holdLevels holdEq hreturnedLevels
      hlevelUpper0 hlevelWidth hreturnedLast root hroot0
      htFirst_le_root hroot_le_high hroot_rate hinnerWidth hreturnedLow
      houter hinner

/--
Canonical-threshold Theorem 3.2 endpoint for the concrete backward
`CalculateOtherLevels` recursion.  The returned level vector is defined by the
outer bisection's penultimate endpoint and the inner `BisectNextLevel`
bisections, so the inner returned-low equations are no longer separate
premises.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_low_bisection_upper_one
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels :
      BinaryEndpointLevelVector
        (let tFirst : ℝ :=
          uniformDoubledEndpointLevels oldLevels
            (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
        let target : ℝ := -Real.log lastLow
        theorem32BackwardLowBisectionLevels
          (2 * m + 1) innerSteps tFirst target lastLow))
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 = lastLow)
    (hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardLowBisectionLevels
          (2 * m + 1) innerSteps tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardLowBisectionLevels
        (2 * m + 1) innerSteps tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardLowBisectionLevels
      (2 * m + 1) innerSteps tFirst target lastLow
  have hlastLow_eq :
      returned
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) =
        lastLow := by
    simpa [returned, tFirst, target] using
      theorem32BackwardLowBisectionLevels_last_low
        (n := 2 * m + 1) (innerSteps := innerSteps) (by omega)
        tFirst target lastLow
  have htarget_eq :
      binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) = target := by
    have hlast_formula :
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) =
          -Real.log
            (returned
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))) := by
      have hfirst_last :
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)).val ≠ 0 := by
        simp
      have hlast_last :
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)).val =
            2 * m + 1 := by
        simp
      simpa using
        binaryEndpointAwareAdjacentRate_last
          returned (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
          hfirst_last hlast_last
    rw [hlast_formula, hlastLow_eq]
  have hreturnedLast' :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
    rw [hlastLow_eq]
    exact hreturnedLast
  have hfeasible' :
      let tFirst' : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target' : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst'
          (returned (adjacentHighIndex i)) target' := by
    dsimp
    rw [htarget_eq]
    intro i hi_first hi_last
    simpa [returned, tFirst, target] using
      hfeasible i hi_first hi_last
  have hreturnedLow' :
      let tFirst' : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target' : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst'
          (returned (adjacentHighIndex i)) target'
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i) := by
    dsimp
    rw [htarget_eq]
    intro i hi_first hi_last
    simpa [returned, tFirst, target] using
      theorem32BackwardLowBisectionLevels_returnedLow
        (n := 2 * m + 1) (innerSteps := innerSteps)
        tFirst target lastLow i hi_first hi_last
  simpa [tFirst, target, returned] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_threshold_run_feasible_low_bisection_runs_from_source_lower_upper_one
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned heps holdLevels holdEq
      (by simpa [returned, tFirst, target] using hreturnedLevels)
      hlevelWidth hreturnedLast' hfeasible' hinnerWidth hreturnedLow'
      houter hinner

/--
Calculated-recursion Theorem 3.2 endpoint with the returned endpoint-vector
certificate derived from source-shaped bisection gap data.  This is closer to
the supplement's `δ << min_i (t_i - t_{i-1})` convention: the inner bisection
grid is small enough to move each returned upper endpoint strictly below the
previous high endpoint.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_low_bisection_upper_one_of_feasible_gap
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlastLow_lt_one : lastLow < 1)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 = lastLow)
    (hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardLowBisectionLevels
          (2 * m + 1) innerSteps tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hgap :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardLowBisectionLevels
          (2 * m + 1) innerSteps tFirst target lastLow
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (returned (adjacentHighIndex i) - 0) /
            (2 : ℝ) ^ innerSteps <
          returned (adjacentHighIndex i) - root i)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardLowBisectionLevels
        (2 * m + 1) innerSteps tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardLowBisectionLevels
      (2 * m + 1) innerSteps tFirst target lastLow
  have hreturnedLevels : BinaryEndpointLevelVector returned := by
    simpa [returned, tFirst, target] using
      theorem32BackwardLowBisectionLevels_isEndpointLevelVector_of_feasible_gap_auto_first
        (n := 2 * m + 1) (innerSteps := innerSteps)
        (by omega) tFirst target lastLow hlastLow_lt_one hfeasible hgap
  simpa [tFirst, target, returned] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_low_bisection_upper_one
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hreturnedLevels
      hlevelWidth hreturnedLast hfeasible hinnerWidth houter hinner

/--
Calculated-recursion Theorem 3.2 endpoint for the source-grid version of
`CalculateOtherLevels`.  The inner bisection calls start from
`[0, high - grid]`, matching the supplement's `r = j_m - δ` convention.
The remaining source obligations are explicit: each exact low-endpoint root
must be feasible and must lie below `high - grid`, and the resulting inner
width must fit inside the theorem's explicit error budget.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_feasible_grid
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 = lastLow)
    (hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hroot_le_grid_upper :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ returned (adjacentHighIndex i) - grid)
    (hinnerWidth :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (returned (adjacentHighIndex i) - grid - 0) /
            (2 : ℝ) ^ innerSteps ≤
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  let delta : ℝ :=
    eps /
      ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
        (((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
  have hreturnedLevels : BinaryEndpointLevelVector returned := by
    simpa [returned, tFirst, target] using
      theorem32BackwardGridLowBisectionLevels_isEndpointLevelVector_of_feasible_grid_auto_first
        (n := 2 * m + 1) (innerSteps := innerSteps)
        (by omega) grid tFirst target lastLow hgrid_pos hlastLow_lt_one
        hfeasible hroot_le_grid_upper
  have hlastLow_eq :
      returned
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) =
        lastLow := by
    simpa [returned, tFirst, target] using
      theorem32BackwardGridLowBisectionLevels_last_low
        (n := 2 * m + 1) (innerSteps := innerSteps) (by omega)
        grid tFirst target lastLow
  have htarget_eq :
      binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) = target := by
    have hlast_formula :
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) =
          -Real.log
            (returned
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))) := by
      have hfirst_last :
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)).val ≠ 0 := by
        simp
      have hlast_last :
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)).val =
            2 * m + 1 := by
        simp
      simpa using
        binaryEndpointAwareAdjacentRate_last
          returned (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
          hfirst_last hlast_last
    rw [hlast_formula, hlastLow_eq]
  have hoptimalLevels :
      BinaryEndpointLevelVector (uniformDoubledEndpointLevels oldLevels) := by
    simpa using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    exact uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  let levelLower0 : ℝ :=
    1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
  let levelTarget : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hlevelLower0 :
      levelLower0 ≤ levelTarget := by
    simpa [levelLower0, levelTarget] using
      BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
        (m := 2 * m + 1) (by omega) hoptimalLevels hoptimalEq
  have hlevelUpper0 : levelTarget ≤ (1 : ℝ) := by
    simpa [levelTarget] using
      BinaryEndpointLevelVector_le_one hoptimalLevels
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hlevelWidth' :
      (1 - levelLower0) / (2 : ℝ) ^ outerSteps ≤ delta := by
    simpa [levelLower0, delta] using
      EconCSLib.Optimization.width_div_pow_two_le_of_le_delta_mul_pow_two
        hlevelWidth
  have hreturnedLast' :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 1).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
    rw [hlastLow_eq]
    simpa [levelTarget, levelLower0] using hreturnedLast
  have hlastBracket :
      EconCSLib.Optimization.RealBisectionBracket
        levelTarget
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 1).1
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 1).2
        delta :=
    EconCSLib.Optimization.realBisectionRun_bracket_aboveTarget_of_width_le
      (n := outerSteps) (lower := levelLower0) (upper := 1)
      (target := levelTarget) (delta := delta)
      hlevelLower0 hlevelUpper0 hlevelWidth'
  have hlast_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
    have hrun_upper := hlastBracket.target_le_upper
    rw [hreturnedLast'] at hrun_upper
    simpa [levelTarget] using hrun_upper
  let firstInterior : Fin ((2 * m + 1) + 1) := ⟨1, by omega⟩
  have hfirstInterior_not_first : firstInterior.val ≠ 0 := by
    simp [firstInterior]
  have hfirstInterior_not_last : firstInterior.val ≠ 2 * m + 1 := by
    simp [firstInterior]
    omega
  have hfirst_root_mem :
      root firstInterior ∈
        Set.Ioo tFirst (returned (adjacentHighIndex firstInterior)) := by
    simpa [root, returned, tFirst, target] using
      weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
        (hfeasible firstInterior hfirstInterior_not_first
          hfirstInterior_not_last)
  have hfirst_root_pos : 0 < root firstInterior :=
    (hfeasible firstInterior hfirstInterior_not_first
      hfirstInterior_not_last).hfloor0.trans hfirst_root_mem.1
  have hfirst_root_le_grid_upper :
      root firstInterior ≤
        returned (adjacentHighIndex firstInterior) - grid := by
    simpa [root, returned, tFirst, target] using
      hroot_le_grid_upper firstInterior hfirstInterior_not_first
        hfirstInterior_not_last
  have hfirst_run_target_le :
      root firstInterior ≤
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (root firstInterior))
          innerSteps 0
          (returned (adjacentHighIndex firstInterior) - grid)).2 :=
    EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
      (n := innerSteps) (lower := 0)
      (target := root firstInterior)
      (upper := returned (adjacentHighIndex firstInterior) - grid)
      hfirst_root_pos.le hfirst_root_le_grid_upper
  have hfirst_returned_low :
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget
          (root firstInterior))
        innerSteps 0 (returned (adjacentHighIndex firstInterior) - grid)).2 =
        returned (adjacentLowIndex firstInterior) := by
    simpa [returned, root, tFirst, target] using
      theorem32BackwardGridLowBisectionLevels_returnedLow
        (n := 2 * m + 1) (innerSteps := innerSteps)
        grid tFirst target lastLow firstInterior
        hfirstInterior_not_first hfirstInterior_not_last
  have hfirst_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
    calc
      uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
          root firstInterior := by
            simpa [tFirst] using hfirst_root_mem.1.le
      _ ≤ returned (adjacentLowIndex firstInterior) := by
            simpa [hfirst_returned_low] using hfirst_run_target_le
      _ =
          returned
            (adjacentHighIndex
              (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
            simp [firstInterior, adjacentLowIndex, adjacentHighIndex,
              firstAdjacentIndex]
  simpa [tFirst, target, returned] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_feasible_low_bisection_runs
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned
      (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
      (fun _ : Fin ((2 * m + 1) + 1) => (0 : ℝ))
      (fun i : Fin ((2 * m + 1) + 1) =>
        returned (adjacentHighIndex i) - grid)
      heps holdLevels holdEq hreturnedLevels
      (by
        intro x hx
        simpa [levelTarget] using
          EconCSLib.Optimization.realBisectionAboveTarget_true hx)
      (by
        intro x hx
        simpa [levelTarget] using
          EconCSLib.Optimization.realBisectionAboveTarget_false hx)
      hlevelLower0 hlevelUpper0
      (by simpa [levelLower0, delta] using hlevelWidth')
      (by simpa [levelLower0, levelTarget] using hreturnedLast')
      hfirst_ge hlast_ge
      (by
        dsimp
        rw [htarget_eq]
        intro i hi_first hi_last
        simpa [returned, tFirst, target] using
          hfeasible i hi_first hi_last)
      (by
        dsimp
        rw [htarget_eq]
        intro i hi_first hi_last
        have hmem :
            root i ∈ Set.Ioo tFirst (returned (adjacentHighIndex i)) := by
          simpa [root, returned, tFirst, target] using
            weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
              (hfeasible i hi_first hi_last)
        exact le_of_lt ((hfeasible i hi_first hi_last).hfloor0.trans hmem.1))
      (by
        dsimp
        rw [htarget_eq]
        intro i hi_first hi_last
        simpa [returned, root, tFirst, target] using
          hroot_le_grid_upper i hi_first hi_last)
      (by
        intro i hi_first hi_last
        simpa [returned, tFirst, target, delta] using
          hinnerWidth i hi_first hi_last)
      (by
        dsimp
        rw [htarget_eq]
        intro i hi_first hi_last
        simpa [returned, root, tFirst, target] using
          theorem32BackwardGridLowBisectionLevels_returnedLow
            (n := 2 * m + 1) (innerSteps := innerSteps)
            grid tFirst target lastLow i hi_first hi_last)
      houter hinner

/--
Calculated-recursion Theorem 3.2 endpoint for the source-grid version of
`CalculateOtherLevels`, using the weak clipped low-endpoint convention.  The
inner target may equal the fixed-floor rate; in that boundary case the shared
selector clips to the floor and still realizes the target rate.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_weak_floor_rate_grid_width
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 = lastLow)
    (htarget_le_floor_rate :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target ≤
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst)
    (hroot_le_grid_upper :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ returned (adjacentHighIndex i) - grid)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  let delta : ℝ :=
    eps /
      ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
        (((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
  have hoptimalLevels :
      BinaryEndpointLevelVector (uniformDoubledEndpointLevels oldLevels) := by
    simpa using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    exact uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have htFirst_pos : 0 < tFirst := by
    have hnot_first :
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
          0 := by
      simp [adjacentHighIndex, firstAdjacentIndex]
    simpa [tFirst] using
      BinaryEndpointLevelVector_pos_of_not_first
        hoptimalLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
        hnot_first
  have hreturnedLevels : BinaryEndpointLevelVector returned := by
    simpa [returned, tFirst, target] using
      theorem32BackwardGridLowBisectionLevels_isEndpointLevelVector_of_root_le_grid_upper
        (n := 2 * m + 1) (innerSteps := innerSteps)
        (by omega) grid tFirst target lastLow htFirst_pos hgrid_pos
        hlastLow_lt_one hroot_le_grid_upper
  have hlastLow_eq :
      returned
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) =
        lastLow := by
    simpa [returned, tFirst, target] using
      theorem32BackwardGridLowBisectionLevels_last_low
        (n := 2 * m + 1) (innerSteps := innerSteps) (by omega)
        grid tFirst target lastLow
  have htarget_eq :
      binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) = target := by
    have hlast_formula :
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) =
          -Real.log
            (returned
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))) := by
      have hfirst_last :
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)).val ≠ 0 := by
        simp
      have hlast_last :
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)).val =
            2 * m + 1 := by
        simp
      simpa using
        binaryEndpointAwareAdjacentRate_last
          returned (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
          hfirst_last hlast_last
    rw [hlast_formula, hlastLow_eq]
  let levelLower0 : ℝ :=
    1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
  let levelTarget : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hlevelLower0 :
      levelLower0 ≤ levelTarget := by
    simpa [levelLower0, levelTarget] using
      BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
        (m := 2 * m + 1) (by omega) hoptimalLevels hoptimalEq
  have hlevelUpper0 : levelTarget ≤ (1 : ℝ) := by
    simpa [levelTarget] using
      BinaryEndpointLevelVector_le_one hoptimalLevels
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hlevelWidth' :
      (1 - levelLower0) / (2 : ℝ) ^ outerSteps ≤ delta := by
    simpa [levelLower0, delta] using
      EconCSLib.Optimization.width_div_pow_two_le_of_le_delta_mul_pow_two
        hlevelWidth
  have hreturnedLast' :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 1).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
    rw [hlastLow_eq]
    simpa [levelTarget, levelLower0] using hreturnedLast
  have hlastBracket :
      EconCSLib.Optimization.RealBisectionBracket
        levelTarget
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 1).1
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 1).2
        delta :=
    EconCSLib.Optimization.realBisectionRun_bracket_aboveTarget_of_width_le
      (n := outerSteps) (lower := levelLower0) (upper := 1)
      (target := levelTarget) (delta := delta)
      hlevelLower0 hlevelUpper0 hlevelWidth'
  have hlast_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
    have hrun_upper := hlastBracket.target_le_upper
    rw [hreturnedLast'] at hrun_upper
    simpa [levelTarget] using hrun_upper
  have hlevelTarget_pos : 0 < levelTarget := by
    have hnot_first :
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
          0 := by
      simp [adjacentLowIndex, lastAdjacentIndex]
    simpa [levelTarget] using
      BinaryEndpointLevelVector_pos_of_not_first
        hoptimalLevels
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
        hnot_first
  have hlastLow_pos : 0 < lastLow := by
    rw [← hlastLow_eq]
    exact hlevelTarget_pos.trans_le hlast_ge
  have htarget_pos : 0 < target := by
    have hlog_neg : Real.log lastLow < 0 :=
      Real.log_neg hlastLow_pos hlastLow_lt_one
    dsimp [target]
    linarith
  have hroot0 :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        0 < root i := by
    intro i hi_first hi_last
    have hfloor_le_root : tFirst ≤ root i := by
      simpa [root] using
        (floor_le_weightedBernoulliLowEndpointOfRateOrFloor_unconditional
          (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
          (pHi := returned (adjacentHighIndex i)) (target := target))
    exact htFirst_pos.trans_le hfloor_le_root
  have htFirst_le_root :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
          root i := by
    intro i hi_first hi_last
    simpa [tFirst] using
      (floor_le_weightedBernoulliLowEndpointOfRateOrFloor_unconditional
        (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
        (pHi := returned (adjacentHighIndex i)) (target := target))
  let firstInterior : Fin ((2 * m + 1) + 1) := ⟨1, by omega⟩
  have hfirstInterior_not_first : firstInterior.val ≠ 0 := by
    simp [firstInterior]
  have hfirstInterior_not_last : firstInterior.val ≠ 2 * m + 1 := by
    simp [firstInterior]
    omega
  have hfirst_root_le_grid_upper :
      root firstInterior ≤
        returned (adjacentHighIndex firstInterior) - grid := by
    simpa [root, returned, tFirst, target] using
      hroot_le_grid_upper firstInterior hfirstInterior_not_first
        hfirstInterior_not_last
  have hfirst_run_target_le :
      root firstInterior ≤
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (root firstInterior))
          innerSteps 0
          (returned (adjacentHighIndex firstInterior) - grid)).2 :=
    EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
      (n := innerSteps) (lower := 0)
      (target := root firstInterior)
      (upper := returned (adjacentHighIndex firstInterior) - grid)
      (hroot0 firstInterior hfirstInterior_not_first
        hfirstInterior_not_last).le
      hfirst_root_le_grid_upper
  have hfirst_returned_low :
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget
          (root firstInterior))
        innerSteps 0 (returned (adjacentHighIndex firstInterior) - grid)).2 =
        returned (adjacentLowIndex firstInterior) := by
    simpa [returned, root, tFirst, target] using
      theorem32BackwardGridLowBisectionLevels_returnedLow
        (n := 2 * m + 1) (innerSteps := innerSteps)
        grid tFirst target lastLow firstInterior
        hfirstInterior_not_first hfirstInterior_not_last
  have hfirst_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
    calc
      uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
          root firstInterior := by
            exact htFirst_le_root firstInterior hfirstInterior_not_first
              hfirstInterior_not_last
      _ ≤ returned (adjacentLowIndex firstInterior) := by
            simpa [hfirst_returned_low] using hfirst_run_target_le
      _ =
          returned
            (adjacentHighIndex
              (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
            simp [firstInterior, adjacentLowIndex, adjacentHighIndex,
              firstAdjacentIndex]
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  have hmirror :
      1 -
          returned
            (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) :=
    BinaryEndpointAwareAdjacentRatesEqualize_uniform_endpoint_mirror_of_endpoint_ge
      (m := 2 * m + 1) (by omega) optimal returned
      (by simpa [optimal] using hoptimalLevels)
      (by simpa [optimal] using hoptimalEq)
      (by simpa [optimal] using hfirst_ge)
      (by simpa [optimal] using hlast_ge)
  have hfirstRate :
      binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin ((2 * m + 1) + 1)) :=
    binaryEndpointAwareAdjacentRate_uniform_last_le_first_of_one_sub_first_high_le_last_low
      (m := 2 * m + 1) (by omega) returned hreturnedLevels hmirror
  have hroot_rate :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i)) (root i) =
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) := by
    rw [htarget_eq]
    intro i hi_first hi_last
    have hroot_le :
        root i ≤ returned (adjacentHighIndex i) - grid := by
      simpa [root, returned, tFirst, target] using
        hroot_le_grid_upper i hi_first hi_last
    have hfloor_le_root : tFirst ≤ root i := by
      simpa [root] using
        (floor_le_weightedBernoulliLowEndpointOfRateOrFloor_unconditional
          (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
          (pHi := returned (adjacentHighIndex i)) (target := target))
    have hfloor_lt_high :
        tFirst < returned (adjacentHighIndex i) := by
      linarith
    have hhigh_lt_one :
        returned (adjacentHighIndex i) < 1 := by
      exact
        BinaryEndpointLevelVector_lt_one_of_not_last hreturnedLevels
          (adjacentHighIndex i)
          (by
            simp [adjacentHighIndex]
            omega)
    exact
      weightedBernoulliLowEndpointOfRateOrFloor_rate_of_target_le_floor_rate
        (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
        (pHi := returned (adjacentHighIndex i)) (target := target)
        (by norm_num) (by norm_num) htFirst_pos hfloor_lt_high
        hhigh_lt_one htarget_pos
        (by
          simpa [returned, tFirst, target] using
            htarget_le_floor_rate i hi_first hi_last)
  have hinnerWidth' :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (returned (adjacentHighIndex i) - grid - 0) /
            (2 : ℝ) ^ innerSteps ≤ delta := by
    intro i hi_first hi_last
    have hhigh_le_one :
        returned (adjacentHighIndex i) ≤ 1 :=
      BinaryEndpointLevelVector_le_one hreturnedLevels (adjacentHighIndex i)
    have hnum_le_one :
        returned (adjacentHighIndex i) - grid - 0 ≤ 1 := by
      linarith
    have hpow_nonneg : 0 ≤ (2 : ℝ) ^ innerSteps :=
      le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) innerSteps)
    have hlocal_le_unit :
        (returned (adjacentHighIndex i) - grid - 0) /
            (2 : ℝ) ^ innerSteps ≤
          (1 : ℝ) / (2 : ℝ) ^ innerSteps :=
      div_le_div_of_nonneg_right hnum_le_one hpow_nonneg
    have hunit_le_delta :
        (1 : ℝ) / (2 : ℝ) ^ innerSteps ≤ delta := by
      simpa [delta] using
        EconCSLib.Optimization.width_div_pow_two_le_of_le_delta_mul_pow_two
          hinnerWidth
    exact hlocal_le_unit.trans hunit_le_delta
  have hreturnedLow :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps (0 : ℝ) (returned (adjacentHighIndex i) - grid)).2 =
          returned (adjacentLowIndex i) := by
    intro i hi_first hi_last
    simpa [returned, root, tFirst, target] using
      theorem32BackwardGridLowBisectionLevels_returnedLow
        (n := 2 * m + 1) (innerSteps := innerSteps)
        grid tFirst target lastLow i hi_first hi_last
  simpa [tFirst, target, returned] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_low_bisection_runs
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned
      (lastBracketLower :=
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 1).1)
      heps holdLevels holdEq hreturnedLevels
      (by
        simpa [optimal, delta, hreturnedLast'] using hlastBracket)
      hfirstRate root
      (fun _ : Fin ((2 * m + 1) + 1) => (0 : ℝ))
      (fun i : Fin ((2 * m + 1) + 1) =>
        returned (adjacentHighIndex i) - grid)
      hroot0 htFirst_le_root hroot_rate
      (by
        intro i hi_first hi_last
        exact (hroot0 i hi_first hi_last).le)
      (by
        intro i hi_first hi_last
        simpa [root, returned, tFirst, target] using
          hroot_le_grid_upper i hi_first hi_last)
      hinnerWidth' hreturnedLow houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint from an already-certified outer
last-level bracket, using the weak clipped low-endpoint convention.  This
version is exact-hit compatible: the inner target may equal the fixed-floor
rate, and root placement is kept as the source small-grid support invariant.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_of_weak_floor_rate_from_bracket
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow lastBracketLower : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (hlastBracket :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      EconCSLib.Optimization.RealBisectionBracket
        (optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        lastBracketLower
        (returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        delta)
    (htarget_le_floor_rate :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target ≤
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst)
    (hroot_le_grid_upper :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ returned (adjacentHighIndex i) - grid)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  let delta : ℝ :=
    eps /
      ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
        (((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
  have hoptimalLevels :
      BinaryEndpointLevelVector (uniformDoubledEndpointLevels oldLevels) := by
    simpa using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    exact uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have htFirst_pos : 0 < tFirst := by
    have hnot_first :
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
          0 := by
      simp [adjacentHighIndex, firstAdjacentIndex]
    simpa [tFirst] using
      BinaryEndpointLevelVector_pos_of_not_first
        hoptimalLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
        hnot_first
  have hreturnedLevels : BinaryEndpointLevelVector returned := by
    simpa [returned, tFirst, target] using
      theorem32BackwardGridLowBisectionLevels_isEndpointLevelVector_of_root_le_grid_upper
        (n := 2 * m + 1) (innerSteps := innerSteps)
        (by omega) grid tFirst target lastLow htFirst_pos hgrid_pos
        hlastLow_lt_one hroot_le_grid_upper
  have hlastLow_eq :
      returned
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) =
        lastLow := by
    simpa [returned, tFirst, target] using
      theorem32BackwardGridLowBisectionLevels_last_low
        (n := 2 * m + 1) (innerSteps := innerSteps) (by omega)
        grid tFirst target lastLow
  have htarget_eq :
      binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) = target := by
    have hlast_formula :
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) =
          -Real.log
            (returned
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))) := by
      have hfirst_last :
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)).val ≠ 0 := by
        simp
      have hlast_last :
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)).val =
            2 * m + 1 := by
        simp
      simpa using
        binaryEndpointAwareAdjacentRate_last
          returned (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
          hfirst_last hlast_last
    rw [hlast_formula, hlastLow_eq]
  have hlast_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
    have hrun_upper := hlastBracket.target_le_upper
    simpa [tFirst, target, returned] using hrun_upper
  let levelTarget : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hlevelTarget_pos : 0 < levelTarget := by
    have hnot_first :
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
          0 := by
      simp [adjacentLowIndex, lastAdjacentIndex]
    simpa [levelTarget] using
      BinaryEndpointLevelVector_pos_of_not_first
        hoptimalLevels
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
        hnot_first
  have hlastLow_pos : 0 < lastLow := by
    rw [← hlastLow_eq]
    exact hlevelTarget_pos.trans_le hlast_ge
  have htarget_pos : 0 < target := by
    have hlog_neg : Real.log lastLow < 0 :=
      Real.log_neg hlastLow_pos hlastLow_lt_one
    dsimp [target]
    linarith
  have hroot0 :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        0 < root i := by
    intro i hi_first hi_last
    have hfloor_le_root : tFirst ≤ root i := by
      simpa [root] using
        (floor_le_weightedBernoulliLowEndpointOfRateOrFloor_unconditional
          (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
          (pHi := returned (adjacentHighIndex i)) (target := target))
    exact htFirst_pos.trans_le hfloor_le_root
  have htFirst_le_root :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
          root i := by
    intro i hi_first hi_last
    simpa [tFirst] using
      (floor_le_weightedBernoulliLowEndpointOfRateOrFloor_unconditional
        (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
        (pHi := returned (adjacentHighIndex i)) (target := target))
  let firstInterior : Fin ((2 * m + 1) + 1) := ⟨1, by omega⟩
  have hfirstInterior_not_first : firstInterior.val ≠ 0 := by
    simp [firstInterior]
  have hfirstInterior_not_last : firstInterior.val ≠ 2 * m + 1 := by
    simp [firstInterior]
    omega
  have hfirst_root_le_grid_upper :
      root firstInterior ≤
        returned (adjacentHighIndex firstInterior) - grid := by
    simpa [root, returned, tFirst, target] using
      hroot_le_grid_upper firstInterior hfirstInterior_not_first
        hfirstInterior_not_last
  have hfirst_run_target_le :
      root firstInterior ≤
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (root firstInterior))
          innerSteps 0
          (returned (adjacentHighIndex firstInterior) - grid)).2 :=
    EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
      (n := innerSteps) (lower := 0)
      (target := root firstInterior)
      (upper := returned (adjacentHighIndex firstInterior) - grid)
      (hroot0 firstInterior hfirstInterior_not_first
        hfirstInterior_not_last).le
      hfirst_root_le_grid_upper
  have hfirst_returned_low :
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget
          (root firstInterior))
        innerSteps 0 (returned (adjacentHighIndex firstInterior) - grid)).2 =
        returned (adjacentLowIndex firstInterior) := by
    simpa [returned, root, tFirst, target] using
      theorem32BackwardGridLowBisectionLevels_returnedLow
        (n := 2 * m + 1) (innerSteps := innerSteps)
        grid tFirst target lastLow firstInterior
        hfirstInterior_not_first hfirstInterior_not_last
  have hfirst_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
    calc
      uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
          root firstInterior := by
            exact htFirst_le_root firstInterior hfirstInterior_not_first
              hfirstInterior_not_last
      _ ≤ returned (adjacentLowIndex firstInterior) := by
            simpa [hfirst_returned_low] using hfirst_run_target_le
      _ =
          returned
            (adjacentHighIndex
              (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
            simp [firstInterior, adjacentLowIndex, adjacentHighIndex,
              firstAdjacentIndex]
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  have hmirror :
      1 -
          returned
            (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) :=
    BinaryEndpointAwareAdjacentRatesEqualize_uniform_endpoint_mirror_of_endpoint_ge
      (m := 2 * m + 1) (by omega) optimal returned
      (by simpa [optimal] using hoptimalLevels)
      (by simpa [optimal] using hoptimalEq)
      (by simpa [optimal] using hfirst_ge)
      (by simpa [optimal] using hlast_ge)
  have hfirstRate :
      binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (firstAdjacentIndex : Fin ((2 * m + 1) + 1)) :=
    binaryEndpointAwareAdjacentRate_uniform_last_le_first_of_one_sub_first_high_le_last_low
      (m := 2 * m + 1) (by omega) returned hreturnedLevels hmirror
  have hroot_rate :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i)) (root i) =
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) := by
    rw [htarget_eq]
    intro i hi_first hi_last
    have hroot_le :
        root i ≤ returned (adjacentHighIndex i) - grid := by
      simpa [root, returned, tFirst, target] using
        hroot_le_grid_upper i hi_first hi_last
    have hfloor_le_root : tFirst ≤ root i := by
      simpa [root] using
        (floor_le_weightedBernoulliLowEndpointOfRateOrFloor_unconditional
          (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
          (pHi := returned (adjacentHighIndex i)) (target := target))
    have hfloor_lt_high :
        tFirst < returned (adjacentHighIndex i) := by
      linarith
    have hhigh_lt_one :
        returned (adjacentHighIndex i) < 1 := by
      exact
        BinaryEndpointLevelVector_lt_one_of_not_last hreturnedLevels
          (adjacentHighIndex i)
          (by
            simp [adjacentHighIndex]
            omega)
    exact
      weightedBernoulliLowEndpointOfRateOrFloor_rate_of_target_le_floor_rate
        (gHi := (1 : ℝ)) (gLo := (1 : ℝ)) (floor := tFirst)
        (pHi := returned (adjacentHighIndex i)) (target := target)
        (by norm_num) (by norm_num) htFirst_pos hfloor_lt_high
        hhigh_lt_one htarget_pos
        (by
          simpa [returned, tFirst, target] using
            htarget_le_floor_rate i hi_first hi_last)
  have hinnerWidth' :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (returned (adjacentHighIndex i) - grid - 0) /
            (2 : ℝ) ^ innerSteps ≤ delta := by
    intro i hi_first hi_last
    have hhigh_le_one :
        returned (adjacentHighIndex i) ≤ 1 :=
      BinaryEndpointLevelVector_le_one hreturnedLevels (adjacentHighIndex i)
    have hnum_le_one :
        returned (adjacentHighIndex i) - grid - 0 ≤ 1 := by
      linarith
    have hpow_nonneg : 0 ≤ (2 : ℝ) ^ innerSteps :=
      le_of_lt (pow_pos (by norm_num : (0 : ℝ) < 2) innerSteps)
    have hlocal_le_unit :
        (returned (adjacentHighIndex i) - grid - 0) /
            (2 : ℝ) ^ innerSteps ≤
          (1 : ℝ) / (2 : ℝ) ^ innerSteps :=
      div_le_div_of_nonneg_right hnum_le_one hpow_nonneg
    have hunit_le_delta :
        (1 : ℝ) / (2 : ℝ) ^ innerSteps ≤ delta := by
      simpa [delta] using
        EconCSLib.Optimization.width_div_pow_two_le_of_le_delta_mul_pow_two
          hinnerWidth
    exact hlocal_le_unit.trans hunit_le_delta
  have hreturnedLow :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps (0 : ℝ) (returned (adjacentHighIndex i) - grid)).2 =
          returned (adjacentLowIndex i) := by
    intro i hi_first hi_last
    simpa [returned, root, tFirst, target] using
      theorem32BackwardGridLowBisectionLevels_returnedLow
        (n := 2 * m + 1) (innerSteps := innerSteps)
        grid tFirst target lastLow i hi_first hi_last
  simpa [tFirst, target, returned] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_low_bisection_runs
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned
      (lastBracketLower := lastBracketLower)
      heps holdLevels holdEq hreturnedLevels
      (by
        simpa [tFirst, target, returned, optimal, delta] using hlastBracket)
      hfirstRate root
      (fun _ : Fin ((2 * m + 1) + 1) => (0 : ℝ))
      (fun i : Fin ((2 * m + 1) + 1) =>
        returned (adjacentHighIndex i) - grid)
      hroot0 htFirst_le_root hroot_rate
      (by
        intro i hi_first hi_last
        exact (hroot0 i hi_first hi_last).le)
      (by
        intro i hi_first hi_last
        simpa [root, returned, tFirst, target] using
          hroot_le_grid_upper i hi_first hi_last)
      hinnerWidth' hreturnedLow houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint with Algorithm 1's outer upper
endpoint `1 - grid`, using the weak clipped low-endpoint convention.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_weak_floor_rate_grid_width
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_le_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        1 - grid)
    (hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow)
    (htarget_le_floor_rate :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target ≤
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst)
    (hroot_le_grid_upper :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ returned (adjacentHighIndex i) - grid)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let levelLower0 : ℝ :=
    1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
  let levelTarget : ℝ :=
    optimal
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let delta : ℝ :=
    eps /
      ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
        (((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
  have hoptimalLevels : BinaryEndpointLevelVector optimal := by
    simpa [optimal] using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    simpa [optimal] using uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have hlevelLower0 : levelLower0 ≤ levelTarget := by
    simpa [levelLower0, levelTarget, optimal] using
      BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
        (m := 2 * m + 1) (by omega) hoptimalLevels hoptimalEq
  have hlevelTarget_le : levelTarget ≤ 1 - grid := by
    simpa [levelTarget, optimal] using hlevelTarget_le_one_sub_grid
  have hlevelWidth' :
      ((1 - grid) - levelLower0) / (2 : ℝ) ^ outerSteps ≤ delta := by
    simpa [levelLower0, delta] using
      EconCSLib.Optimization.width_div_pow_two_le_of_le_delta_mul_pow_two
        hlevelWidth
  have hlastLow_eq :
      returned
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) =
        lastLow := by
    simpa [returned, tFirst, target] using
      theorem32BackwardGridLowBisectionLevels_last_low
        (n := 2 * m + 1) (innerSteps := innerSteps) (by omega)
        grid tFirst target lastLow
  have hreturnedLast' :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 (1 - grid)).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
    rw [hreturnedLast, hlastLow_eq]
  have hlastBracket :
      EconCSLib.Optimization.RealBisectionBracket
        levelTarget
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 (1 - grid)).1
        (returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
        delta := by
    have hbracket :=
      EconCSLib.Optimization.realBisectionRun_bracket_aboveTarget_of_width_le
        (n := outerSteps) (lower := levelLower0) (upper := 1 - grid)
        (target := levelTarget) (delta := delta)
        hlevelLower0 hlevelTarget_le hlevelWidth'
    simpa [hreturnedLast'] using hbracket
  simpa [tFirst, target, returned] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_of_weak_floor_rate_from_bracket
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      (lastLow := lastLow)
      (lastBracketLower :=
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 (1 - grid)).1)
      hm oldLevels heps holdLevels holdEq hgrid_pos
      (by
        have hrun_upper :
            (EconCSLib.Optimization.realBisectionRun
                (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
                outerSteps levelLower0 (1 - grid)).2 ≤
              1 - grid :=
          EconCSLib.Optimization.realBisectionRun_upper_le_initial
            (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
            (hlevelLower0.trans hlevelTarget_le)
        rw [hreturnedLast] at hrun_upper
        linarith)
      (by
        simpa [tFirst, target, returned, optimal, levelTarget, delta] using
          hlastBracket)
      htarget_le_floor_rate hroot_le_grid_upper hinnerWidth houter hinner

/--
Exact-hit-compatible source-grid Theorem 3.2 endpoint with the weak
floor-rate condition derived from the exact doubled comparison chain.  The
only remaining inner source-grid invariant is root placement inside
`[0, high - grid]`, the formal version of the supplement's small-grid
assumption for `BisectNextLevel`.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_weak_root_placement_source_grid
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_le_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        1 - grid)
    (hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow)
    (hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst)
    (hroot_le_grid_upper :
      let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let tFirst : ℝ :=
        comparison
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ returned (adjacentHighIndex i) - grid)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let tFirst : ℝ :=
    comparison
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  have hcomparisonLevels : BinaryEndpointLevelVector comparison := by
    simpa [comparison] using
      uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize comparison
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    simpa [comparison] using uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  let levelLower0 : ℝ :=
    1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
  let levelTarget : ℝ :=
    comparison
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hlevelLower0 : levelLower0 ≤ levelTarget := by
    simpa [levelLower0, levelTarget, comparison] using
      BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
        (m := 2 * m + 1) (by omega) hcomparisonLevels hoptimalEq
  have hlevelTarget_le : levelTarget ≤ 1 - grid := by
    simpa [levelTarget, comparison] using hlevelTarget_le_one_sub_grid
  have hreturnedLast_run :
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
        outerSteps levelLower0 (1 - grid)).2 = lastLow := by
    simpa [levelTarget, levelLower0, comparison] using hreturnedLast
  have hlevelTarget_le_lastLow : levelTarget ≤ lastLow := by
    have hrun :
        levelTarget ≤
          (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
            outerSteps levelLower0 (1 - grid)).2 :=
      EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
        (n := outerSteps) hlevelLower0 hlevelTarget_le
    rwa [hreturnedLast_run] at hrun
  have hlastLow_le_one_sub_grid : lastLow ≤ 1 - grid := by
    have hrun_upper :
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 (1 - grid)).2 ≤ 1 - grid :=
      EconCSLib.Optimization.realBisectionRun_upper_le_initial
        (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
        (hlevelLower0.trans hlevelTarget_le)
    rwa [hreturnedLast_run] at hrun_upper
  have hlevelTarget_pos : 0 < levelTarget := by
    have hnot_first :
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
          0 := by
      simp [adjacentLowIndex, lastAdjacentIndex]
    simpa [levelTarget, comparison] using
      BinaryEndpointLevelVector_pos_of_not_first
        hcomparisonLevels
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
        hnot_first
  have hlastLow_pos : 0 < lastLow :=
    hlevelTarget_pos.trans_le hlevelTarget_le_lastLow
  have hlastLow_lt_one : lastLow < 1 := by
    linarith
  have htFirst_pos : 0 < tFirst :=
    hgrid_pos.trans (by simpa [comparison, tFirst] using hgrid_lt_tFirst)
  have htarget_pos : 0 < target := by
    have hlog_neg : Real.log lastLow < 0 :=
      Real.log_neg hlastLow_pos hlastLow_lt_one
    dsimp [target]
    linarith
  have hreturnedLevels : BinaryEndpointLevelVector returned := by
    simpa [comparison, tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_isEndpointLevelVector_of_root_le_grid_upper
        (n := 2 * m + 1) (innerSteps := innerSteps)
        (by omega) grid tFirst target lastLow htFirst_pos hgrid_pos
        hlastLow_lt_one
        (by
          simpa [comparison, tFirst, target, returned] using
            hroot_le_grid_upper)
  have hreturned_high_lt_one :
      let returned :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        returned (adjacentHighIndex i) < 1 := by
    dsimp
    intro i _hi_first _hi_last
    exact
      BinaryEndpointLevelVector_lt_one_of_not_last hreturnedLevels
        (adjacentHighIndex i)
        (by
          simp [adjacentHighIndex]
          omega)
  have hfloor_le_comparison_low :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        tFirst ≤ comparison (adjacentLowIndex i) := by
    intro i hi_first _hi_last
    exact
      BinaryEndpointLevelVector_mono hcomparisonLevels
        (by
          simp [adjacentHighIndex, adjacentLowIndex, firstAdjacentIndex]
          omega)
  have htarget_le_comparison_rate :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target ≤
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (comparison (adjacentHighIndex i))
            (comparison (adjacentLowIndex i)) := by
    simpa [comparison, target] using
      theorem32_target_le_comparison_rate_of_uniform_doubled_lastLow_ge
        (m := m) hm oldLevels holdLevels holdEq
        (by simpa [comparison, levelTarget] using hlevelTarget_le_lastLow)
  have hcomparison_low_le_root :
      let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let tFirst : ℝ :=
        comparison
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        comparison (adjacentLowIndex i) ≤ root i := by
    simpa [comparison, tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_comparison_low_le_root_of_nested_comparison_weak
        (n := 2 * m + 1) (innerSteps := innerSteps)
        (by omega) comparison hcomparisonLevels grid tFirst target lastLow
        htFirst_pos htarget_pos
        (by simpa [comparison, levelTarget] using hlevelTarget_le_lastLow)
        (by
          simpa [comparison, tFirst, target, returned] using
            hroot_le_grid_upper)
        (by
          simpa [returned] using hreturned_high_lt_one)
        hfloor_le_comparison_low htarget_le_comparison_rate
  have hcomparison_high_le_returned_high :
      let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let tFirst : ℝ :=
        comparison
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        comparison (adjacentHighIndex i) ≤ returned (adjacentHighIndex i) := by
    simpa [comparison, tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_comparison_high_le_returned_high_of_comparison_low_le_root
        (n := 2 * m + 1) (innerSteps := innerSteps)
        (by omega) comparison hcomparisonLevels grid tFirst target lastLow
        (by simpa [comparison, levelTarget] using hlevelTarget_le_lastLow)
        (by
          simpa [comparison, tFirst, target, returned] using
            hroot_le_grid_upper)
        (by
          simpa [comparison, tFirst, target, returned] using
            hcomparison_low_le_root)
  have htarget_le_floor_rate :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target ≤
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst := by
    simpa [comparison, tFirst, target, returned] using
      theorem32_target_le_floor_rate_of_nested_comparison_intervals
        comparison returned hcomparisonLevels htFirst_pos
        hfloor_le_comparison_low
        (by
          simpa [comparison, tFirst, target, returned] using
            hcomparison_high_le_returned_high)
        (by
          simpa [returned] using hreturned_high_lt_one)
        htarget_le_comparison_rate
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_weak_floor_rate_grid_width
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos
      hlevelTarget_le_one_sub_grid hlevelWidth hreturnedLast
      htarget_le_floor_rate
      (by
        simpa [comparison, tFirst, target, returned] using
          hroot_le_grid_upper)
      hinnerWidth houter hinner

/--
Calculated-recursion Theorem 3.2 endpoint for the source-grid version of
`CalculateOtherLevels`, with the outer bisection upper endpoint left explicit.
This is the paper-shaped variant used when Algorithm 1 initializes the outer
search interval at `1 - grid` rather than at `1`.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_of_feasible_grid_source_lower_global_width
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow levelUpper0 : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (hlevelUpper0 :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        levelUpper0)
    (hlevelWidth :
      levelUpper0 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          levelUpper0).2 = lastLow)
    (hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hroot_le_grid_upper :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ returned (adjacentHighIndex i) - grid)
    (hinnerWidth :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (returned (adjacentHighIndex i) - grid - 0) /
            (2 : ℝ) ^ innerSteps ≤
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  let delta : ℝ :=
    eps /
      ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
        (((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
  have hreturnedLevels : BinaryEndpointLevelVector returned := by
    simpa [returned, tFirst, target] using
      theorem32BackwardGridLowBisectionLevels_isEndpointLevelVector_of_feasible_grid_auto_first
        (n := 2 * m + 1) (innerSteps := innerSteps)
        (by omega) grid tFirst target lastLow hgrid_pos hlastLow_lt_one
        hfeasible hroot_le_grid_upper
  have hlastLow_eq :
      returned
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) =
        lastLow := by
    simpa [returned, tFirst, target] using
      theorem32BackwardGridLowBisectionLevels_last_low
        (n := 2 * m + 1) (innerSteps := innerSteps) (by omega)
        grid tFirst target lastLow
  have htarget_eq :
      binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) = target := by
    have hlast_formula :
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) =
          -Real.log
            (returned
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))) := by
      have hfirst_last :
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)).val ≠ 0 := by
        simp
      have hlast_last :
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)).val =
            2 * m + 1 := by
        simp
      simpa using
        binaryEndpointAwareAdjacentRate_last
          returned (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
          hfirst_last hlast_last
    rw [hlast_formula, hlastLow_eq]
  have hoptimalLevels :
      BinaryEndpointLevelVector (uniformDoubledEndpointLevels oldLevels) := by
    simpa using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    exact uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  let levelLower0 : ℝ :=
    1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
  let levelTarget : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hlevelLower0 :
      levelLower0 ≤ levelTarget := by
    simpa [levelLower0, levelTarget] using
      BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
        (m := 2 * m + 1) (by omega) hoptimalLevels hoptimalEq
  have hlevelWidth' :
      (levelUpper0 - levelLower0) / (2 : ℝ) ^ outerSteps ≤ delta := by
    simpa [levelLower0, delta] using
      EconCSLib.Optimization.width_div_pow_two_le_of_le_delta_mul_pow_two
        hlevelWidth
  have hreturnedLast' :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 levelUpper0).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
    rw [hlastLow_eq]
    simpa [levelTarget, levelLower0] using hreturnedLast
  have hlastBracket :
      EconCSLib.Optimization.RealBisectionBracket
        levelTarget
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 levelUpper0).1
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 levelUpper0).2
        delta :=
    EconCSLib.Optimization.realBisectionRun_bracket_aboveTarget_of_width_le
      (n := outerSteps) (lower := levelLower0) (upper := levelUpper0)
      (target := levelTarget) (delta := delta)
      hlevelLower0 (by simpa [levelTarget] using hlevelUpper0) hlevelWidth'
  have hlast_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
    have hrun_upper := hlastBracket.target_le_upper
    rw [hreturnedLast'] at hrun_upper
    simpa [levelTarget] using hrun_upper
  let firstInterior : Fin ((2 * m + 1) + 1) := ⟨1, by omega⟩
  have hfirstInterior_not_first : firstInterior.val ≠ 0 := by
    simp [firstInterior]
  have hfirstInterior_not_last : firstInterior.val ≠ 2 * m + 1 := by
    simp [firstInterior]
    omega
  have hfirst_root_mem :
      root firstInterior ∈
        Set.Ioo tFirst (returned (adjacentHighIndex firstInterior)) := by
    simpa [root, returned, tFirst, target] using
      weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
        (hfeasible firstInterior hfirstInterior_not_first
          hfirstInterior_not_last)
  have hfirst_root_pos : 0 < root firstInterior :=
    (hfeasible firstInterior hfirstInterior_not_first
      hfirstInterior_not_last).hfloor0.trans hfirst_root_mem.1
  have hfirst_root_le_grid_upper :
      root firstInterior ≤
        returned (adjacentHighIndex firstInterior) - grid := by
    simpa [root, returned, tFirst, target] using
      hroot_le_grid_upper firstInterior hfirstInterior_not_first
        hfirstInterior_not_last
  have hfirst_run_target_le :
      root firstInterior ≤
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (root firstInterior))
          innerSteps 0
          (returned (adjacentHighIndex firstInterior) - grid)).2 :=
    EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
      (n := innerSteps) (lower := 0)
      (target := root firstInterior)
      (upper := returned (adjacentHighIndex firstInterior) - grid)
      hfirst_root_pos.le hfirst_root_le_grid_upper
  have hfirst_returned_low :
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget
          (root firstInterior))
        innerSteps 0 (returned (adjacentHighIndex firstInterior) - grid)).2 =
        returned (adjacentLowIndex firstInterior) := by
    simpa [returned, root, tFirst, target] using
      theorem32BackwardGridLowBisectionLevels_returnedLow
        (n := 2 * m + 1) (innerSteps := innerSteps)
        grid tFirst target lastLow firstInterior
        hfirstInterior_not_first hfirstInterior_not_last
  have hfirst_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
    calc
      uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
          root firstInterior := by
            simpa [tFirst] using hfirst_root_mem.1.le
      _ ≤ returned (adjacentLowIndex firstInterior) := by
            simpa [hfirst_returned_low] using hfirst_run_target_le
      _ =
          returned
            (adjacentHighIndex
              (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) := by
            simp [firstInterior, adjacentLowIndex, adjacentHighIndex,
              firstAdjacentIndex]
  simpa [tFirst, target, returned] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_feasible_low_bisection_runs
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned
      (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
      (fun _ : Fin ((2 * m + 1) + 1) => (0 : ℝ))
      (fun i : Fin ((2 * m + 1) + 1) =>
        returned (adjacentHighIndex i) - grid)
      heps holdLevels holdEq hreturnedLevels
      (by
        intro x hx
        simpa [levelTarget] using
          EconCSLib.Optimization.realBisectionAboveTarget_true hx)
      (by
        intro x hx
        simpa [levelTarget] using
          EconCSLib.Optimization.realBisectionAboveTarget_false hx)
      hlevelLower0 (by simpa [levelTarget] using hlevelUpper0)
      (by simpa [levelLower0, delta] using hlevelWidth')
      (by simpa [levelLower0, levelTarget] using hreturnedLast')
      hfirst_ge hlast_ge
      (by
        dsimp
        rw [htarget_eq]
        intro i hi_first hi_last
        simpa [returned, tFirst, target] using
          hfeasible i hi_first hi_last)
      (by
        dsimp
        rw [htarget_eq]
        intro i hi_first hi_last
        have hmem :
            root i ∈ Set.Ioo tFirst (returned (adjacentHighIndex i)) := by
          simpa [root, returned, tFirst, target] using
            weightedBernoulliLowEndpointOfRateOrFloor_mem_Ioo_of_feasible
              (hfeasible i hi_first hi_last)
        exact le_of_lt ((hfeasible i hi_first hi_last).hfloor0.trans hmem.1))
      (by
        dsimp
        rw [htarget_eq]
        intro i hi_first hi_last
        simpa [returned, root, tFirst, target] using
          hroot_le_grid_upper i hi_first hi_last)
      (by
        intro i hi_first hi_last
        simpa [returned, tFirst, target, delta] using
          hinnerWidth i hi_first hi_last)
      (by
        dsimp
        rw [htarget_eq]
        intro i hi_first hi_last
        simpa [returned, root, tFirst, target] using
          theorem32BackwardGridLowBisectionLevels_returnedLow
            (n := 2 * m + 1) (innerSteps := innerSteps)
            grid tFirst target lastLow i hi_first hi_last)
      houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint with Algorithm 1's outer upper
endpoint `1 - grid`.  The remaining source-shaped inner invariant is the
selector fact that each exact clipped low endpoint lies above the fixed first
floor; from that Lean derives feasibility, grid placement, and the target-rate
comparison used by the finite approximation certificate.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_outer_return_grid_lt_floor_width_floor_lt_root
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_le_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        1 - grid)
    (hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow)
    (hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst)
    (hfloor_lt_root :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        tFirst < root i)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
    weightedBernoulliLowEndpointOfRateOrFloor
      (1 : ℝ) (1 : ℝ) tFirst
      (returned (adjacentHighIndex i)) target
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let levelLower0 : ℝ :=
    1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
  let levelTarget : ℝ :=
    optimal
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hoptimalLevels : BinaryEndpointLevelVector optimal := by
    simpa [optimal] using
      uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    simpa [optimal] using uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have hlevelLower0 :
      levelLower0 ≤ levelTarget := by
    simpa [levelLower0, levelTarget, optimal] using
      BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
        (m := 2 * m + 1) (by omega) hoptimalLevels hoptimalEq
  have hlevelTarget_le :
      levelTarget ≤ 1 - grid := by
    simpa [levelTarget, optimal] using hlevelTarget_le_one_sub_grid
  have hreturnedLast' :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 (1 - grid)).2 = lastLow := by
    simpa [levelTarget, levelLower0, optimal] using hreturnedLast
  have hlastLow_le_one_sub_grid : lastLow ≤ 1 - grid := by
    have hrun_upper :
        (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
            outerSteps levelLower0 (1 - grid)).2 ≤
          1 - grid :=
      EconCSLib.Optimization.realBisectionRun_upper_le_initial
        (above := EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
        (n := outerSteps) (hlevelLower0.trans hlevelTarget_le)
    rwa [hreturnedLast'] at hrun_upper
  have hlevelTarget_le_lastLow : levelTarget ≤ lastLow := by
    have hrun :
        levelTarget ≤
          (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
            outerSteps levelLower0 (1 - grid)).2 :=
      EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
        (n := outerSteps) hlevelLower0 hlevelTarget_le
    rwa [hreturnedLast'] at hrun
  have hlevelTarget_pos : 0 < levelTarget := by
    have hnot_first :
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
          0 := by
      simp [adjacentLowIndex, lastAdjacentIndex]
    simpa [levelTarget, optimal] using
      BinaryEndpointLevelVector_pos_of_not_first
        hoptimalLevels
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
        hnot_first
  have hlastLow_pos : 0 < lastLow :=
    hlevelTarget_pos.trans_le hlevelTarget_le_lastLow
  have hlastLow_lt_one : lastLow < 1 := by
    linarith
  have hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target := by
    simpa [tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_feasible_of_floor_lt_lowEndpointOfRateOrFloor
        (n := 2 * m + 1) (innerSteps := innerSteps)
        grid tFirst target lastLow
        (by simpa [tFirst, target, returned] using hfloor_lt_root)
  have htarget_lt_floor_rate :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst := by
    dsimp at hfeasible ⊢
    intro i hi_first hi_last
    simpa [tFirst, target, returned] using
      (hfeasible i hi_first hi_last).htarget_lt_floor
  have htFirst_pos : 0 < tFirst := by
    exact hgrid_pos.trans (by simpa [tFirst] using hgrid_lt_tFirst)
  have htFirst_lt_lastLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      tFirst < lastLow := by
    have htFirst_le_half : tFirst ≤ (1 / 2 : ℝ) := by
      have htFirst_eq :
          tFirst = bernoulliFirstEndpointEqualSplit
            (oldLevels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))) := by
        simpa [tFirst, optimal] using
          uniformDoubledEndpointLevels_first_odd oldLevels
      rw [htFirst_eq]
      exact bernoulliFirstEndpointEqualSplit_le_half
    let oldLast : ℝ :=
      oldLevels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
    have holdLast_ge_half : (1 / 2 : ℝ) ≤ oldLast := by
      simpa [oldLast] using
        BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_half
          hm holdLevels holdEq
    have holdLast_nonneg : 0 ≤ oldLast := by
      linarith
    have holdLast_lt_one : oldLast < 1 := by
      have hnot_last :
          (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))).val ≠ m + 1 := by
        simp [adjacentLowIndex, lastAdjacentIndex]
      simpa [oldLast] using
        BinaryEndpointLevelVector_lt_one_of_not_last
          holdLevels
          (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
          hnot_last
    have hlevelTarget_eq :
        levelTarget = bernoulliLastEndpointEqualSplit oldLast := by
      simpa [levelTarget, optimal, oldLast, adjacentLowIndex, lastAdjacentIndex]
        using uniformDoubledEndpointLevels_last_odd hm oldLevels
    have hlevelTarget_gt_half : (1 / 2 : ℝ) < levelTarget := by
      have hsplit_mem :
          bernoulliLastEndpointEqualSplit oldLast ∈ Set.Ioo oldLast (1 : ℝ) :=
        bernoulliLastEndpointEqualSplit_mem_Ioo holdLast_nonneg holdLast_lt_one
      rw [hlevelTarget_eq]
      exact holdLast_ge_half.trans_lt hsplit_mem.1
    exact lt_of_le_of_lt htFirst_le_half
      (hlevelTarget_gt_half.trans_le hlevelTarget_le_lastLow)
  have hsupport :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      (∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
          tFirst < returned (adjacentHighIndex i)) ∧
        (∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
          0 < returned (adjacentHighIndex i) - grid) := by
    simpa [tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_floor_lt_high_and_grid_upper_pos_of_grid_lt_floor
        (n := 2 * m + 1) (innerSteps := innerSteps)
        grid tFirst lastLow htFirst_pos hgrid_pos
        (by simpa [tFirst] using hgrid_lt_tFirst)
        hlastLow_lt_one hlastLow_pos hlastLow_le_one_sub_grid
        (by simpa [tFirst] using htFirst_lt_lastLow)
        (by simpa [tFirst, target, returned] using htarget_lt_floor_rate)
  have hgrid_upper_pos :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        0 < returned (adjacentHighIndex i) - grid := by
    exact hsupport.2
  have hgrid_upper_rate_le_target :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i))
            (returned (adjacentHighIndex i) - grid) ≤
          target := by
    simpa [tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_grid_upper_rate_le_target_of_lastLow_le_one_sub_grid
        (n := 2 * m + 1) (innerSteps := innerSteps)
        grid tFirst lastLow hgrid_pos hlastLow_lt_one hlastLow_pos
        hlastLow_le_one_sub_grid
        (by simpa [tFirst, target, returned] using hgrid_upper_pos)
  have hroot_le_grid_upper :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ returned (adjacentHighIndex i) - grid := by
    simpa [tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_root_le_grid_upper_of_feasible_grid_upper_rate_le_target
        (n := 2 * m + 1) (innerSteps := innerSteps)
        grid tFirst target lastLow hgrid_pos
        (by simpa [tFirst, target, returned] using hfeasible)
        (by simpa [tFirst, target, returned] using hgrid_upper_pos)
        (by simpa [tFirst, target, returned] using hgrid_upper_rate_le_target)
  let delta : ℝ :=
    eps /
      ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
        (((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
  have hinnerWidth' :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (returned (adjacentHighIndex i) - grid - 0) /
            (2 : ℝ) ^ innerSteps ≤
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) := by
    simpa [tFirst, target, returned, delta] using
      theorem32BackwardGridLowBisectionLevels_innerWidth_of_feasible_grid_width
        (n := 2 * m + 1) (innerSteps := innerSteps)
        (by omega) grid tFirst target lastLow delta hgrid_pos
        hlastLow_lt_one hfeasible hroot_le_grid_upper
        (by simpa [delta] using hinnerWidth)
  simpa [tFirst, target, returned] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_of_feasible_grid_source_lower_global_width
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos hlastLow_lt_one
      (levelUpper0 := 1 - grid)
      (by simpa using hlevelTarget_le_one_sub_grid)
      hlevelWidth hreturnedLast hfeasible hroot_le_grid_upper
      hinnerWidth' houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint with a single global inner-depth
budget.  Since the calculated endpoint vector is endpoint-normalized, each
inner bisection interval `[0, high - grid]` has width at most `1`; hence the
source-style global `2^{-innerSteps}` budget implies the per-interval width
obligations used by the finite approximation theorem.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_feasible_grid_width
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 = lastLow)
    (hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hroot_le_grid_upper :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ returned (adjacentHighIndex i) - grid)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  let delta : ℝ :=
    eps /
      ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
        (((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
  have hinnerWidth' :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (returned (adjacentHighIndex i) - grid - 0) /
            (2 : ℝ) ^ innerSteps ≤
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) := by
    simpa [tFirst, target, returned, delta] using
      theorem32BackwardGridLowBisectionLevels_innerWidth_of_feasible_grid_width
        (n := 2 * m + 1) (innerSteps := innerSteps)
        (by omega) grid tFirst target lastLow delta hgrid_pos
        hlastLow_lt_one hfeasible hroot_le_grid_upper
        (by simpa [delta] using hinnerWidth)
  simpa [tFirst, target, returned] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_feasible_grid
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos hlastLow_lt_one
      hlevelWidth hreturnedLast hfeasible hroot_le_grid_upper
      hinnerWidth' houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint with root placement derived from
the source right-endpoint rate check for each feasible inner bisection call.
This removes the raw `root ≤ high - grid` obligation from callers that have
already proved the low-endpoint shooting feasibility certificates.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_feasible_grid_upper_rate_width
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 = lastLow)
    (hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hgrid_upper_pos :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        0 < returned (adjacentHighIndex i) - grid)
    (hgrid_upper_rate_le_target :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i))
            (returned (adjacentHighIndex i) - grid) ≤
          target)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  have hroot_le_grid_upper :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ returned (adjacentHighIndex i) - grid := by
    simpa [tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_root_le_grid_upper_of_feasible_grid_upper_rate_le_target
        (n := 2 * m + 1) (innerSteps := innerSteps)
        grid tFirst target lastLow hgrid_pos
        (by simpa [tFirst, target, returned] using hfeasible)
        (by simpa [tFirst, target, returned] using hgrid_upper_pos)
        (by simpa [tFirst, target, returned] using hgrid_upper_rate_le_target)
  simpa [tFirst, target, returned] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_feasible_grid_width
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos hlastLow_lt_one
      hlevelWidth hreturnedLast hfeasible hroot_le_grid_upper
      hinnerWidth houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint with the low-endpoint feasibility
certificate derived from source-shaped rate inequalities.  The remaining
inner-loop obligations are now the paper's floor-rate comparison and the
source grid placement `root ≤ high - grid`; endpoint normalization and
low-endpoint feasibility are derived internally.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_floor_rate_grid_width
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 = lastLow)
    (htarget_lt_floor_rate :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst)
    (hroot_le_grid_upper :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ returned (adjacentHighIndex i) - grid)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  have hoptimalLevels :
      BinaryEndpointLevelVector (uniformDoubledEndpointLevels oldLevels) := by
    simpa using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    exact uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have htFirst_pos : 0 < tFirst := by
    have hnot_first :
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
          0 := by
      simp [adjacentHighIndex, firstAdjacentIndex]
    simpa [tFirst] using
      BinaryEndpointLevelVector_pos_of_not_first
        hoptimalLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
        hnot_first
  let levelLower0 : ℝ :=
    1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
  let levelTarget : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hlevelLower0 :
      levelLower0 ≤ levelTarget := by
    simpa [levelLower0, levelTarget] using
      BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
        (m := 2 * m + 1) (by omega) hoptimalLevels hoptimalEq
  have hlevelUpper0 : levelTarget ≤ (1 : ℝ) := by
    simpa [levelTarget] using
      BinaryEndpointLevelVector_le_one hoptimalLevels
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let delta : ℝ :=
    eps /
      ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
        (((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
  have hlevelWidth' :
      (1 - levelLower0) / (2 : ℝ) ^ outerSteps ≤ delta := by
    simpa [levelLower0, delta] using
      EconCSLib.Optimization.width_div_pow_two_le_of_le_delta_mul_pow_two
        hlevelWidth
  have hreturnedLast' :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 1).2 = lastLow := by
    simpa [levelTarget, levelLower0] using hreturnedLast
  have hlastBracket :
      EconCSLib.Optimization.RealBisectionBracket
        levelTarget
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 1).1
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 1).2
        delta :=
    EconCSLib.Optimization.realBisectionRun_bracket_aboveTarget_of_width_le
      (n := outerSteps) (lower := levelLower0) (upper := 1)
      (target := levelTarget) (delta := delta)
      hlevelLower0 hlevelUpper0 hlevelWidth'
  have hlast_ge :
      levelTarget ≤ lastLow := by
    have hrun_upper := hlastBracket.target_le_upper
    rw [hreturnedLast'] at hrun_upper
    exact hrun_upper
  have hlevelTarget_pos : 0 < levelTarget := by
    have hnot_first :
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
          0 := by
      simp [adjacentLowIndex, lastAdjacentIndex]
    simpa [levelTarget] using
      BinaryEndpointLevelVector_pos_of_not_first
        hoptimalLevels
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
        hnot_first
  have hlastLow_pos : 0 < lastLow := hlevelTarget_pos.trans_le hlast_ge
  have htarget_pos : 0 < target := by
    have hlog_neg : Real.log lastLow < 0 :=
      Real.log_neg hlastLow_pos hlastLow_lt_one
    dsimp [target]
    linarith
  have hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target := by
    simpa [tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_feasible_of_root_le_grid_upper_and_target_lt_floor_rate
        (n := 2 * m + 1) (innerSteps := innerSteps)
        (by omega) grid tFirst target lastLow htFirst_pos hgrid_pos
        hlastLow_lt_one htarget_pos hroot_le_grid_upper
        htarget_lt_floor_rate
  simpa [tFirst, target, returned] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_feasible_grid_width
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos hlastLow_lt_one
      hlevelWidth hreturnedLast hfeasible hroot_le_grid_upper
      hinnerWidth houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint with root placement derived from
the Algorithm 1 right-endpoint rate condition.  The remaining inner source
obligations are now stated in terms of the bisection interval itself: the fixed
floor lies below `high - grid`, and the closed rate at `high - grid` is already
at most the target final rate.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_floor_rate_grid_upper_rate_width
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 = lastLow)
    (htarget_lt_floor_rate :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst)
    (hfloor_le_grid_upper :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        tFirst ≤ returned (adjacentHighIndex i) - grid)
    (hgrid_upper_rate_le_target :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i))
            (returned (adjacentHighIndex i) - grid) ≤
          target)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  have hroot_le_grid_upper :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ returned (adjacentHighIndex i) - grid := by
    simpa [tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_root_le_grid_upper_of_grid_upper_rate_le_target
        (n := 2 * m + 1) (innerSteps := innerSteps)
        grid tFirst target lastLow hgrid_pos
        (by simpa [tFirst, target, returned] using hfloor_le_grid_upper)
        (by simpa [tFirst, target, returned] using hgrid_upper_rate_le_target)
  simpa [tFirst, target, returned] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_floor_rate_grid_width
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos hlastLow_lt_one
      hlevelWidth hreturnedLast htarget_lt_floor_rate
      hroot_le_grid_upper hinnerWidth houter hinner

/--
The outer bisection return in the calculated Theorem 3.2 source-grid wrapper
is positive.  It remains above the old penultimate endpoint, which is positive
by endpoint normalization.
-/
theorem theorem32_calculated_grid_lastLow_pos_of_outer_return
    {m outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {grid lastLow : ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 = lastLow) :
    0 < lastLow := by
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let levelLower0 : ℝ :=
    1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
  let levelTarget : ℝ :=
    optimal (adjacentLowIndex
      (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hoptimalLevels : BinaryEndpointLevelVector optimal := by
    simpa [optimal] using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    simpa [optimal] using uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have hlevelLower0 :
      levelLower0 ≤ levelTarget := by
    simpa [levelLower0, levelTarget, optimal] using
      BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
        (m := 2 * m + 1) (by omega) hoptimalLevels hoptimalEq
  have hlevelUpper0 : levelTarget ≤ (1 : ℝ) := by
    simpa [levelTarget, optimal] using
      BinaryEndpointLevelVector_le_one hoptimalLevels
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hlevelTarget_le_lastLow : levelTarget ≤ lastLow := by
    have hrun :
        levelTarget ≤
          (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
            outerSteps levelLower0 1).2 :=
      EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
        (n := outerSteps) hlevelLower0 hlevelUpper0
    have hreturnedLast' :
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 1).2 = lastLow := by
      simpa [levelTarget, levelLower0, optimal] using hreturnedLast
    rw [hreturnedLast'] at hrun
    exact hrun
  have hlevelTarget_pos : 0 < levelTarget := by
    have hnot_first :
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
          0 := by
      simp [adjacentLowIndex, lastAdjacentIndex]
    simpa [levelTarget, optimal] using
      BinaryEndpointLevelVector_pos_of_not_first
        hoptimalLevels
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
        hnot_first
  exact hlevelTarget_pos.trans_le hlevelTarget_le_lastLow

/--
The calculated Theorem 3.2 outer bisection return is strictly above the first
refined endpoint.  The first refined endpoint is at most `1/2`, while the
outer target, the refined penultimate endpoint, is strictly above `1/2`; the
outer bisection returns an upper bracket endpoint.
-/
theorem theorem32_calculated_grid_tFirst_lt_lastLow_of_outer_return
    {m outerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {lastLow : ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 = lastLow) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    tFirst < lastLow := by
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let tFirst : ℝ :=
    optimal (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let levelLower0 : ℝ :=
    1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
  let levelTarget : ℝ :=
    optimal (adjacentLowIndex
      (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let oldLast : ℝ :=
    oldLevels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
  have htFirst_le_half : tFirst ≤ (1 / 2 : ℝ) := by
    have htFirst_eq :
        tFirst = bernoulliFirstEndpointEqualSplit
          (oldLevels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))) := by
      simpa [tFirst, optimal] using
        uniformDoubledEndpointLevels_first_odd oldLevels
    rw [htFirst_eq]
    exact bernoulliFirstEndpointEqualSplit_le_half
  have holdLast_ge_half : (1 / 2 : ℝ) ≤ oldLast := by
    simpa [oldLast] using
      BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_half
        hm holdLevels holdEq
  have holdLast_nonneg : 0 ≤ oldLast := by
    linarith
  have holdLast_lt_one : oldLast < 1 := by
    have hnot_last :
        (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))).val ≠ m + 1 := by
      simp [adjacentLowIndex, lastAdjacentIndex]
    simpa [oldLast] using
      BinaryEndpointLevelVector_lt_one_of_not_last
        holdLevels
        (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
        hnot_last
  have hlevelTarget_eq :
      levelTarget = bernoulliLastEndpointEqualSplit oldLast := by
    simpa [levelTarget, optimal, oldLast, adjacentLowIndex, lastAdjacentIndex]
      using uniformDoubledEndpointLevels_last_odd hm oldLevels
  have hlevelTarget_gt_half : (1 / 2 : ℝ) < levelTarget := by
    have hsplit_mem :
        bernoulliLastEndpointEqualSplit oldLast ∈ Set.Ioo oldLast (1 : ℝ) :=
      bernoulliLastEndpointEqualSplit_mem_Ioo holdLast_nonneg holdLast_lt_one
    rw [hlevelTarget_eq]
    exact holdLast_ge_half.trans_lt hsplit_mem.1
  have hoptimalLevels : BinaryEndpointLevelVector optimal := by
    simpa [optimal] using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    simpa [optimal] using uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have hlevelLower0 :
      levelLower0 ≤ levelTarget := by
    simpa [levelLower0, levelTarget, optimal] using
      BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
        (m := 2 * m + 1) (by omega) hoptimalLevels hoptimalEq
  have hlevelUpper0 : levelTarget ≤ (1 : ℝ) := by
    simpa [levelTarget, optimal] using
      BinaryEndpointLevelVector_le_one hoptimalLevels
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hlevelTarget_le_lastLow : levelTarget ≤ lastLow := by
    have hrun :
        levelTarget ≤
          (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
            outerSteps levelLower0 1).2 :=
      EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
        (n := outerSteps) hlevelLower0 hlevelUpper0
    have hreturnedLast' :
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 1).2 = lastLow := by
      simpa [levelTarget, levelLower0, optimal] using hreturnedLast
    rw [hreturnedLast'] at hrun
    exact hrun
  change tFirst < lastLow
  linarith

/--
The final-rate target in the calculated Theorem 3.2 source-grid wrapper is
positive.  The outer bisection returns an upper bracket endpoint, so it remains
above the old penultimate target level, which is positive by endpoint
normalization; together with `lastLow < 1`, this gives `0 < -log lastLow`.
-/
theorem theorem32_calculated_grid_target_pos_of_outer_return
    {m outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {grid lastLow : ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlastLow_lt_one : lastLow < 1)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 = lastLow) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let _returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    0 < target := by
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let levelLower0 : ℝ :=
    1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
  let levelTarget : ℝ :=
    optimal (adjacentLowIndex
      (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hoptimalLevels : BinaryEndpointLevelVector optimal := by
    simpa [optimal] using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    simpa [optimal] using uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have hlevelLower0 :
      levelLower0 ≤ levelTarget := by
    simpa [levelLower0, levelTarget, optimal] using
      BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
        (m := 2 * m + 1) (by omega) hoptimalLevels hoptimalEq
  have hlevelUpper0 : levelTarget ≤ (1 : ℝ) := by
    simpa [levelTarget, optimal] using
      BinaryEndpointLevelVector_le_one hoptimalLevels
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hlevelTarget_le_lastLow : levelTarget ≤ lastLow := by
    have hrun :
        levelTarget ≤
          (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
            outerSteps levelLower0 1).2 :=
      EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
        (n := outerSteps) hlevelLower0 hlevelUpper0
    have hreturnedLast' :
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 1).2 = lastLow := by
      simpa [levelTarget, levelLower0, optimal] using hreturnedLast
    rw [hreturnedLast'] at hrun
    exact hrun
  have hlevelTarget_pos : 0 < levelTarget := by
    have hnot_first :
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
          0 := by
      simp [adjacentLowIndex, lastAdjacentIndex]
    simpa [levelTarget, optimal] using
      BinaryEndpointLevelVector_pos_of_not_first
        hoptimalLevels
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
        hnot_first
  have hlastLow_pos : 0 < lastLow := hlevelTarget_pos.trans_le hlevelTarget_le_lastLow
  dsimp
  have hlog_neg : Real.log lastLow < 0 :=
    Real.log_neg hlastLow_pos hlastLow_lt_one
  linarith

/--
Source-shaped outer bisection upper bound for Theorem 3.2.  Algorithm 1
initializes the outer upper endpoint at `1 - grid`; executable bisection never
raises the upper endpoint, so the returned penultimate level is also at most
`1 - grid`.
-/
theorem theorem32_calculated_grid_lastLow_le_one_sub_grid_of_source_outer_return
    {m outerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {grid lastLow : ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlevelTarget_le_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        1 - grid)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow) :
    lastLow ≤ 1 - grid := by
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let levelLower0 : ℝ :=
    1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
  let levelTarget : ℝ :=
    optimal
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hoptimalLevels : BinaryEndpointLevelVector optimal := by
    simpa [optimal] using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    simpa [optimal] using uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have hlevelLower0 :
      levelLower0 ≤ levelTarget := by
    simpa [levelLower0, levelTarget, optimal] using
      BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
        (m := 2 * m + 1) (by omega) hoptimalLevels hoptimalEq
  have hlevelTarget_le :
      levelTarget ≤ 1 - grid := by
    simpa [levelTarget, optimal] using hlevelTarget_le_one_sub_grid
  have hrun_upper :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 (1 - grid)).2 ≤
        1 - grid :=
    EconCSLib.Optimization.realBisectionRun_upper_le_initial
      (above := EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
      (n := outerSteps) (hlevelLower0.trans hlevelTarget_le)
  have hreturnedLast' :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 (1 - grid)).2 = lastLow := by
    simpa [levelTarget, levelLower0, optimal] using hreturnedLast
  rwa [hreturnedLast'] at hrun_upper

/--
Source-shaped outer bisection positivity for Theorem 3.2.  When Algorithm 1's
upper endpoint `1 - grid` still brackets the refined penultimate optimum, the
returned upper endpoint remains above that positive target.
-/
theorem theorem32_calculated_grid_lastLow_pos_of_source_outer_return
    {m outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {grid lastLow : ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlevelTarget_le_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        1 - grid)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow) :
    0 < lastLow := by
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let levelLower0 : ℝ :=
    1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
  let levelTarget : ℝ :=
    optimal
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hoptimalLevels : BinaryEndpointLevelVector optimal := by
    simpa [optimal] using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    simpa [optimal] using uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have hlevelLower0 :
      levelLower0 ≤ levelTarget := by
    simpa [levelLower0, levelTarget, optimal] using
      BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
        (m := 2 * m + 1) (by omega) hoptimalLevels hoptimalEq
  have hlevelTarget_le :
      levelTarget ≤ 1 - grid := by
    simpa [levelTarget, optimal] using hlevelTarget_le_one_sub_grid
  have htarget_le_run :
      levelTarget ≤
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 (1 - grid)).2 :=
    EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
      (n := outerSteps) hlevelLower0 hlevelTarget_le
  have hreturnedLast' :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 (1 - grid)).2 = lastLow := by
    simpa [levelTarget, levelLower0, optimal] using hreturnedLast
  have hlevelTarget_pos : 0 < levelTarget := by
    have hnot_first :
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
          0 := by
      simp [adjacentLowIndex, lastAdjacentIndex]
    simpa [levelTarget, optimal] using
      BinaryEndpointLevelVector_pos_of_not_first
        hoptimalLevels
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
        hnot_first
  rw [hreturnedLast'] at htarget_le_run
  exact hlevelTarget_pos.trans_le htarget_le_run

/--
Source-shaped scalar grid bridge for Theorem 3.2.  In the uniform equalized
doubled chain, the first refined high endpoint and the penultimate refined low
endpoint are complements.  Hence the source small-grid condition
`grid < tFirst` is exactly the strict upper-bracket condition needed for the
outer bisection initialized at `1 - grid`.
-/
theorem theorem32_calculated_grid_levelTarget_lt_one_sub_grid_of_grid_lt_tFirst
    {m : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {grid : ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst) :
    let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
      uniformDoubledEndpointLevels oldLevels
    optimal
        (adjacentLowIndex
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) <
      1 - grid := by
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let tFirst : ℝ :=
    optimal (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let levelTarget : ℝ :=
    optimal (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hoptimalLevels : BinaryEndpointLevelVector optimal := by
    simpa [optimal] using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    simpa [optimal] using uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have hmirror :
      1 - tFirst = levelTarget := by
    simpa [tFirst, levelTarget, optimal] using
      BinaryEndpointAwareAdjacentRatesEqualize_uniform_one_sub_first_high_eq_last_low
        (m := 2 * m + 1) (by omega) optimal hoptimalLevels hoptimalEq
  have hgrid_lt : grid < tFirst := by
    simpa [tFirst, optimal] using hgrid_lt_tFirst
  change levelTarget < 1 - grid
  linarith

/--
Reverse source-grid bridge for Theorem 3.2.  The supplement assumes the
refined penultimate optimum lies below Algorithm 1's initial upper endpoint
`1 - grid`; by the equalized-chain mirror identity, this is equivalent to the
source small-grid condition `grid < tFirst`.
-/
theorem theorem32_calculated_grid_grid_lt_tFirst_of_levelTarget_lt_one_sub_grid
    {m : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {grid : ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlevelTarget_lt_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) <
        1 - grid) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    grid < tFirst := by
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let tFirst : ℝ :=
    optimal (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let levelTarget : ℝ :=
    optimal (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hoptimalLevels : BinaryEndpointLevelVector optimal := by
    simpa [optimal] using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    simpa [optimal] using uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have hmirror :
      1 - tFirst = levelTarget := by
    simpa [tFirst, levelTarget, optimal] using
      BinaryEndpointAwareAdjacentRatesEqualize_uniform_one_sub_first_high_eq_last_low
        (m := 2 * m + 1) (by omega) optimal hoptimalLevels hoptimalEq
  have hlevelTarget_lt : levelTarget < 1 - grid := by
    simpa [levelTarget, optimal] using hlevelTarget_lt_one_sub_grid
  change grid < tFirst
  linarith

/--
Source-grid bridge for Theorem 3.2.  Instead of exposing the internal first
refined endpoint, this uses the C.5/C.7/C.8 lower-bound package: if the grid is
strictly below half of the one-fifth old objective-rate lower bound, then it is
strictly below the first refined high endpoint.
-/
theorem theorem32_calculated_grid_lt_tFirst_of_grid_lt_objective_bound
    {m : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {grid : ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlower_le_one :
      (1 / 5 : ℝ) *
          binaryEndpointAwareAdjacentRateObjective oldLevels
            (fun _ : Fin (m + 2) => (1 : ℝ)) ≤ 1)
    (hgrid_lt_bound :
      grid <
        ((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    grid < tFirst := by
  let bound : ℝ :=
    ((1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ))) / 2
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hbound_le_tFirst : bound ≤ tFirst := by
    simpa [bound, tFirst] using
      uniformDoubledEndpointLevels_first_level_ge_one_tenth_old_objective_closed
        (m := m) hm holdLevels holdEq hlower_le_one
  have hgrid_lt_bound' : grid < bound := by
    simpa [bound] using hgrid_lt_bound
  exact hgrid_lt_bound'.trans_le hbound_le_tFirst

/--
Source-shaped strict outer-return bridge for Theorem 3.2.  If Algorithm 1's
outer bisection starts with a strict upper bracket and no tested midpoint
lands exactly on the refined penultimate optimum, then the returned upper
endpoint `lastLow` is strictly above that optimum.  This is the precise
Lean form of the usual source no-exact-hit convention for the outer bisection.
-/
theorem theorem32_calculated_grid_levelTarget_lt_lastLow_of_source_outer_return_no_exact_midpoint
    {m outerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {grid lastLow : ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlevelTarget_lt_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) <
        1 - grid)
    (hnoExact :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let levelLower0 : ℝ :=
        1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
      let levelTarget : ℝ :=
        optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
      ∀ k : ℕ, k < outerSteps →
        levelTarget ≠
          EconCSLib.Optimization.realBisectionMidpoint
            (EconCSLib.Optimization.realBisectionRun
              (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
              k levelLower0 (1 - grid)).1
            (EconCSLib.Optimization.realBisectionRun
              (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
              k levelLower0 (1 - grid)).2)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow) :
    let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
      uniformDoubledEndpointLevels oldLevels
    optimal
        (adjacentLowIndex
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) < lastLow := by
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let levelLower0 : ℝ :=
    1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
  let levelTarget : ℝ :=
    optimal
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hoptimalLevels : BinaryEndpointLevelVector optimal := by
    simpa [optimal] using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    simpa [optimal] using uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have hlevelLower0 :
      levelLower0 ≤ levelTarget := by
    simpa [levelLower0, levelTarget, optimal] using
      BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
        (m := 2 * m + 1) (by omega) hoptimalLevels hoptimalEq
  have htarget_lt_upper : levelTarget < 1 - grid := by
    simpa [levelTarget, optimal] using hlevelTarget_lt_one_sub_grid
  have hrun :
      levelTarget <
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 (1 - grid)).2 := by
    exact
      EconCSLib.Optimization.realBisectionRun_aboveTarget_target_lt_upper_of_no_exact_midpoint
        (n := outerSteps) hlevelLower0 htarget_lt_upper
        (by
          simpa [optimal, levelLower0, levelTarget] using hnoExact)
  have hreturnedLast' :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 (1 - grid)).2 = lastLow := by
    simpa [levelTarget, levelLower0, optimal] using hreturnedLast
  rwa [hreturnedLast'] at hrun

/--
Outer bisection dichotomy for the calculated Theorem 3.2 run.  Without a
separate no-exact-hit convention, the executable outer return either lands
exactly on the refined penultimate optimum or stays strictly above it.
-/
theorem theorem32_calculated_grid_levelTarget_eq_lastLow_or_lt_lastLow_of_source_outer_return
    {m outerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {grid lastLow : ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlevelTarget_lt_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) <
        1 - grid)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow) :
    let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
      uniformDoubledEndpointLevels oldLevels
    let levelTarget : ℝ :=
      optimal
        (adjacentLowIndex
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    levelTarget = lastLow ∨ levelTarget < lastLow := by
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let levelLower0 : ℝ :=
    1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
  let levelTarget : ℝ :=
    optimal
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hoptimalLevels : BinaryEndpointLevelVector optimal := by
    simpa [optimal] using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    simpa [optimal] using uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have hlevelLower0 :
      levelLower0 ≤ levelTarget := by
    simpa [levelLower0, levelTarget, optimal] using
      BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
        (m := 2 * m + 1) (by omega) hoptimalLevels hoptimalEq
  have htarget_lt_upper : levelTarget < 1 - grid := by
    simpa [levelTarget, optimal] using hlevelTarget_lt_one_sub_grid
  have hreturnedLast' :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 (1 - grid)).2 = lastLow := by
    simpa [levelTarget, levelLower0, optimal] using hreturnedLast
  rcases
      EconCSLib.Optimization.realBisectionRun_aboveTarget_upper_eq_or_target_lt_upper
        (n := outerSteps) hlevelLower0 htarget_lt_upper
      with hhit | hstrict
  · left
    rw [← hreturnedLast']
    exact hhit.symm
  · right
    rwa [hreturnedLast'] at hstrict

/--
Source-shaped outer bisection separation for Theorem 3.2.  With Algorithm 1's
upper endpoint `1 - grid`, the returned penultimate endpoint remains above the
first refined endpoint whenever `1 - grid` brackets the refined penultimate
optimum.
-/
theorem theorem32_calculated_grid_tFirst_lt_lastLow_of_source_outer_return
    {m outerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {grid lastLow : ℝ}
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlevelTarget_le_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        1 - grid)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    tFirst < lastLow := by
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let tFirst : ℝ :=
    optimal (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let levelLower0 : ℝ :=
    1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
  let levelTarget : ℝ :=
    optimal
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let oldLast : ℝ :=
    oldLevels (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
  have htFirst_le_half : tFirst ≤ (1 / 2 : ℝ) := by
    have htFirst_eq :
        tFirst = bernoulliFirstEndpointEqualSplit
          (oldLevels (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1)))) := by
      simpa [tFirst, optimal] using
        uniformDoubledEndpointLevels_first_odd oldLevels
    rw [htFirst_eq]
    exact bernoulliFirstEndpointEqualSplit_le_half
  have holdLast_ge_half : (1 / 2 : ℝ) ≤ oldLast := by
    simpa [oldLast] using
      BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_half
        hm holdLevels holdEq
  have holdLast_nonneg : 0 ≤ oldLast := by
    linarith
  have holdLast_lt_one : oldLast < 1 := by
    have hnot_last :
        (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))).val ≠ m + 1 := by
      simp [adjacentLowIndex, lastAdjacentIndex]
    simpa [oldLast] using
      BinaryEndpointLevelVector_lt_one_of_not_last
        holdLevels
        (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))
        hnot_last
  have hlevelTarget_eq :
      levelTarget = bernoulliLastEndpointEqualSplit oldLast := by
    simpa [levelTarget, optimal, oldLast, adjacentLowIndex, lastAdjacentIndex]
      using uniformDoubledEndpointLevels_last_odd hm oldLevels
  have hlevelTarget_gt_half : (1 / 2 : ℝ) < levelTarget := by
    have hsplit_mem :
        bernoulliLastEndpointEqualSplit oldLast ∈ Set.Ioo oldLast (1 : ℝ) :=
      bernoulliLastEndpointEqualSplit_mem_Ioo holdLast_nonneg holdLast_lt_one
    rw [hlevelTarget_eq]
    exact holdLast_ge_half.trans_lt hsplit_mem.1
  have hoptimalLevels : BinaryEndpointLevelVector optimal := by
    simpa [optimal] using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hoptimalEq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) := by
    simpa [optimal] using uniformDoubledEndpointLevels_equalizes hm holdLevels holdEq
  have hlevelLower0 :
      levelLower0 ≤ levelTarget := by
    simpa [levelLower0, levelTarget, optimal] using
      BinaryEndpointLevelVector_uniform_equalized_last_low_ge_one_sub_inv
        (m := 2 * m + 1) (by omega) hoptimalLevels hoptimalEq
  have hlevelTarget_le :
      levelTarget ≤ 1 - grid := by
    simpa [levelTarget, optimal] using hlevelTarget_le_one_sub_grid
  have htarget_le_run :
      levelTarget ≤
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 (1 - grid)).2 :=
    EconCSLib.Optimization.realBisectionRun_aboveTarget_target_le_upper
      (n := outerSteps) hlevelLower0 hlevelTarget_le
  have hreturnedLast' :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          outerSteps levelLower0 (1 - grid)).2 = lastLow := by
    simpa [levelTarget, levelLower0, optimal] using hreturnedLast
  change tFirst < lastLow
  rw [hreturnedLast'] at htarget_le_run
  linarith

/--
Calculated source-grid Theorem 3.2 endpoint with Algorithm 1's outer upper
endpoint `1 - grid`, stated in the source floor-rate form.  The strict
floor-rate comparison implies that each exact clipped low endpoint moves above
the fixed first floor, so this theorem avoids exposing the selector inequality
`floor < root` directly.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_outer_return_grid_lt_floor_width_floor_rate
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_le_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        1 - grid)
    (hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow)
    (hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst)
    (htarget_lt_floor_rate :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  have hlastLow_le_one_sub_grid : lastLow ≤ 1 - grid :=
    theorem32_calculated_grid_lastLow_le_one_sub_grid_of_source_outer_return
      (m := m) (outerSteps := outerSteps)
      hm oldLevels holdLevels holdEq hlevelTarget_le_one_sub_grid
      hreturnedLast
  have hlastLow_pos : 0 < lastLow :=
    theorem32_calculated_grid_lastLow_pos_of_source_outer_return
      (m := m) (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels holdLevels holdEq hlevelTarget_le_one_sub_grid
      hreturnedLast
  have hlastLow_lt_one : lastLow < 1 := by
    linarith
  have htFirst_pos : 0 < tFirst :=
    hgrid_pos.trans (by simpa [tFirst] using hgrid_lt_tFirst)
  have htFirst_lt_lastLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      tFirst < lastLow := by
    simpa [tFirst] using
      theorem32_calculated_grid_tFirst_lt_lastLow_of_source_outer_return
        (m := m) (outerSteps := outerSteps)
        hm oldLevels holdLevels holdEq hlevelTarget_le_one_sub_grid
        hreturnedLast
  have hsupport :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      (∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
          tFirst < returned (adjacentHighIndex i)) ∧
        (∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
          0 < returned (adjacentHighIndex i) - grid) := by
    simpa [tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_floor_lt_high_and_grid_upper_pos_of_grid_lt_floor
        (n := 2 * m + 1) (innerSteps := innerSteps)
        grid tFirst lastLow htFirst_pos hgrid_pos
        (by simpa [tFirst] using hgrid_lt_tFirst)
        hlastLow_lt_one hlastLow_pos hlastLow_le_one_sub_grid
        (by simpa [tFirst] using htFirst_lt_lastLow)
        (by simpa [tFirst, target, returned] using htarget_lt_floor_rate)
  have hfloor_lt_high :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        tFirst < returned (adjacentHighIndex i) := hsupport.1
  have hgrid_upper_pos :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        0 < returned (adjacentHighIndex i) - grid := hsupport.2
  have hhigh_lt_one :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        returned (adjacentHighIndex i) < 1 := by
    simpa [tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_high_lt_one_of_grid_upper_pos
        (n := 2 * m + 1) (innerSteps := innerSteps)
        grid tFirst target lastLow hgrid_pos hlastLow_lt_one
        (by simpa [tFirst, target, returned] using hgrid_upper_pos)
  have htarget_pos : 0 < target := by
    have hlog_neg : Real.log lastLow < 0 :=
      Real.log_neg hlastLow_pos hlastLow_lt_one
    dsimp [target]
    linarith
  have hfloor_lt_root :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        tFirst < root i := by
    simpa [tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_floor_lt_lowEndpointOfRateOrFloor_of_floor_rate
        (n := 2 * m + 1) (innerSteps := innerSteps)
        grid tFirst target lastLow htFirst_pos htarget_pos
        (by simpa [tFirst, target, returned] using hfloor_lt_high)
        (by simpa [tFirst, target, returned] using hhigh_lt_one)
        (by simpa [tFirst, target, returned] using htarget_lt_floor_rate)
  simpa [tFirst, target, returned] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_outer_return_grid_lt_floor_width_floor_lt_root
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos
      hlevelTarget_le_one_sub_grid hlevelWidth hreturnedLast
      hgrid_lt_tFirst hfloor_lt_root hinnerWidth houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint where the inner floor-rate
condition is discharged from a nested comparison invariant against the exact
doubled endpoint chain.  The remaining algorithmic obligation is to prove that
the backward bisection returned highs dominate the exact doubled highs and
that the target is below the corresponding exact comparison rates.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_outer_return_grid_lt_floor_width_nested_comparison
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_le_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        1 - grid)
    (hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow)
    (hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst)
    (hcomparison_high_le_returned_high :
      let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let tFirst : ℝ :=
        comparison
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        comparison (adjacentHighIndex i) ≤ returned (adjacentHighIndex i))
    (hreturned_high_lt_one :
      let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let tFirst : ℝ :=
        comparison
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        returned (adjacentHighIndex i) < 1)
    (htarget_lt_comparison_rate :
      let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let target : ℝ := -Real.log lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (comparison (adjacentHighIndex i))
            (comparison (adjacentLowIndex i)))
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let tFirst : ℝ :=
    comparison
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  have hcomparisonLevels : BinaryEndpointLevelVector comparison := by
    simpa [comparison] using
      uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have htFirst_pos : 0 < tFirst :=
    hgrid_pos.trans (by simpa [comparison, tFirst] using hgrid_lt_tFirst)
  have hfloor_le_comparison_low :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        tFirst ≤ comparison (adjacentLowIndex i) := by
    intro i hi_first _hi_last
    exact
      BinaryEndpointLevelVector_mono hcomparisonLevels
        (by
          simp [adjacentHighIndex, adjacentLowIndex,
            firstAdjacentIndex]
          omega)
  have htarget_lt_floor_rate :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst := by
    simpa [comparison, tFirst, target, returned] using
      theorem32_target_lt_floor_rate_of_nested_comparison_intervals
        comparison returned hcomparisonLevels htFirst_pos
        hfloor_le_comparison_low
        (by
          simpa [comparison, tFirst, target, returned] using
            hcomparison_high_le_returned_high)
        (by
          simpa [comparison, tFirst, target, returned] using
            hreturned_high_lt_one)
        (by
          simpa [comparison, target] using htarget_lt_comparison_rate)
  simpa [comparison, tFirst, target, returned] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_outer_return_grid_lt_floor_width_floor_rate
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos
      hlevelTarget_le_one_sub_grid hlevelWidth hreturnedLast
      hgrid_lt_tFirst htarget_lt_floor_rate hinnerWidth houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint where the exact comparison-rate
premise is derived from a single strict outer-return gap against the exact
doubled last lower endpoint.  The remaining inner-loop obligation is the
returned-high domination invariant against the exact doubled chain.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_strict_outer_return_nested_comparison
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_le_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        1 - grid)
    (hlevelTarget_lt_lastLow :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) < lastLow)
    (hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow)
    (hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst)
    (hcomparison_high_le_returned_high :
      let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let tFirst : ℝ :=
        comparison
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        comparison (adjacentHighIndex i) ≤ returned (adjacentHighIndex i))
    (hreturned_high_lt_one :
      let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let tFirst : ℝ :=
        comparison
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        returned (adjacentHighIndex i) < 1)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  have htarget_lt_comparison_rate :
      let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let target : ℝ := -Real.log lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (comparison (adjacentHighIndex i))
            (comparison (adjacentLowIndex i)) := by
    simpa using
      theorem32_target_lt_comparison_rate_of_uniform_doubled_lastLow_strict
        (m := m) hm oldLevels holdLevels holdEq hlevelTarget_lt_lastLow
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_outer_return_grid_lt_floor_width_nested_comparison
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos
      hlevelTarget_le_one_sub_grid hlevelWidth hreturnedLast
      hgrid_lt_tFirst hcomparison_high_le_returned_high
      hreturned_high_lt_one htarget_lt_comparison_rate hinnerWidth
      houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint with the returned-high domination
premise reduced to local root-placement invariants.  The remaining source
obligation is to show each exact successor low endpoint lies below the root
used by the corresponding inner bisection call.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_strict_outer_return_root_invariant
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_le_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        1 - grid)
    (hlevelTarget_lt_lastLow :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) < lastLow)
    (hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow)
    (hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst)
    (hroot_le_grid_upper :
      let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let tFirst : ℝ :=
        comparison
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ returned (adjacentHighIndex i) - grid)
    (hcomparison_low_le_root :
      let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let tFirst : ℝ :=
        comparison
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        comparison (adjacentLowIndex i) ≤ root i)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let tFirst : ℝ :=
    comparison
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  have hcomparisonLevels : BinaryEndpointLevelVector comparison := by
    simpa [comparison] using
      uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hlastLow_le_one_sub_grid : lastLow ≤ 1 - grid :=
    theorem32_calculated_grid_lastLow_le_one_sub_grid_of_source_outer_return
      (m := m) (outerSteps := outerSteps)
      hm oldLevels holdLevels holdEq hlevelTarget_le_one_sub_grid
      hreturnedLast
  have hlastLow_pos : 0 < lastLow :=
    theorem32_calculated_grid_lastLow_pos_of_source_outer_return
      (m := m) (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels holdLevels holdEq hlevelTarget_le_one_sub_grid
      hreturnedLast
  have hlastLow_lt_one : lastLow < 1 := by
    linarith
  have htFirst_pos : 0 < tFirst :=
    hgrid_pos.trans (by simpa [comparison, tFirst] using hgrid_lt_tFirst)
  have hreturnedLevels : BinaryEndpointLevelVector returned := by
    simpa [comparison, tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_isEndpointLevelVector_of_root_le_grid_upper
        (n := 2 * m + 1) (innerSteps := innerSteps)
        (by omega) grid tFirst target lastLow htFirst_pos hgrid_pos
        hlastLow_lt_one
        (by
          simpa [comparison, tFirst, target, returned] using
            hroot_le_grid_upper)
  have hcomparison_last_low_le_lastLow :
      comparison
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ lastLow := by
    exact le_of_lt (by
      simpa [comparison] using hlevelTarget_lt_lastLow)
  have hcomparison_high_le_returned_high :
      let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let tFirst : ℝ :=
        comparison
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        comparison (adjacentHighIndex i) ≤ returned (adjacentHighIndex i) := by
    simpa [comparison, tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_comparison_high_le_returned_high_of_comparison_low_le_root
        (n := 2 * m + 1) (innerSteps := innerSteps)
        (by omega) comparison hcomparisonLevels grid tFirst target lastLow
        hcomparison_last_low_le_lastLow
        (by
          simpa [comparison, tFirst, target, returned] using
            hroot_le_grid_upper)
        (by
          simpa [comparison, tFirst, target, returned] using
            hcomparison_low_le_root)
  have hreturned_high_lt_one :
      let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let tFirst : ℝ :=
        comparison
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        returned (adjacentHighIndex i) < 1 := by
    dsimp
    intro i _hi_first hi_last
    exact
      BinaryEndpointLevelVector_lt_one_of_not_last hreturnedLevels
        (adjacentHighIndex i)
        (by
          simp [adjacentHighIndex]
          omega)
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_strict_outer_return_nested_comparison
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos
      hlevelTarget_le_one_sub_grid hlevelTarget_lt_lastLow
      hlevelWidth hreturnedLast hgrid_lt_tFirst
      hcomparison_high_le_returned_high hreturned_high_lt_one
      hinnerWidth houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint with the local comparison-root
invariant derived by backward induction.  The only remaining inner-loop
certificate is the source-grid root-placement condition `root ≤ high - grid`.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_strict_outer_return_root_placement
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_le_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        1 - grid)
    (hlevelTarget_lt_lastLow :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) < lastLow)
    (hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow)
    (hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst)
    (hroot_le_grid_upper :
      let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let tFirst : ℝ :=
        comparison
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ returned (adjacentHighIndex i) - grid)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let tFirst : ℝ :=
    comparison
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  have hcomparisonLevels : BinaryEndpointLevelVector comparison := by
    simpa [comparison] using
      uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hlastLow_pos : 0 < lastLow :=
    theorem32_calculated_grid_lastLow_pos_of_source_outer_return
      (m := m) (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels holdLevels holdEq hlevelTarget_le_one_sub_grid
      hreturnedLast
  have hlastLow_le_one_sub_grid : lastLow ≤ 1 - grid :=
    theorem32_calculated_grid_lastLow_le_one_sub_grid_of_source_outer_return
      (m := m) (outerSteps := outerSteps)
      hm oldLevels holdLevels holdEq hlevelTarget_le_one_sub_grid
      hreturnedLast
  have hlastLow_lt_one : lastLow < 1 := by
    linarith
  have htarget_pos : 0 < target := by
    have hlog_neg : Real.log lastLow < 0 :=
      Real.log_neg hlastLow_pos hlastLow_lt_one
    dsimp [target]
    linarith
  have htFirst_pos : 0 < tFirst :=
    hgrid_pos.trans (by simpa [comparison, tFirst] using hgrid_lt_tFirst)
  have hreturnedLevels : BinaryEndpointLevelVector returned := by
    simpa [comparison, tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_isEndpointLevelVector_of_root_le_grid_upper
        (n := 2 * m + 1) (innerSteps := innerSteps)
        (by omega) grid tFirst target lastLow htFirst_pos hgrid_pos
        hlastLow_lt_one
        (by
          simpa [comparison, tFirst, target, returned] using
            hroot_le_grid_upper)
  have hreturned_high_lt_one :
      let returned :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        returned (adjacentHighIndex i) < 1 := by
    dsimp
    intro i _hi_first _hi_last
    exact
      BinaryEndpointLevelVector_lt_one_of_not_last hreturnedLevels
        (adjacentHighIndex i)
        (by
          simp [adjacentHighIndex]
          omega)
  have hcomparison_last_low_le_lastLow :
      comparison
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ lastLow := by
    exact le_of_lt (by
      simpa [comparison] using hlevelTarget_lt_lastLow)
  have hfloor_le_comparison_low :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        tFirst ≤ comparison (adjacentLowIndex i) := by
    intro i hi_first _hi_last
    exact
      BinaryEndpointLevelVector_mono hcomparisonLevels
        (by
          simp [adjacentHighIndex, adjacentLowIndex, firstAdjacentIndex]
          omega)
  have htarget_lt_comparison_rate :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (comparison (adjacentHighIndex i))
            (comparison (adjacentLowIndex i)) := by
    simpa [comparison, target] using
      theorem32_target_lt_comparison_rate_of_uniform_doubled_lastLow_strict
        (m := m) hm oldLevels holdLevels holdEq hlevelTarget_lt_lastLow
  have hcomparison_low_le_root :
      let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let tFirst : ℝ :=
        comparison
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        comparison (adjacentLowIndex i) ≤ root i := by
    simpa [comparison, tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_comparison_low_le_root_of_nested_comparison
        (n := 2 * m + 1) (innerSteps := innerSteps)
        (by omega) comparison hcomparisonLevels grid tFirst target lastLow
        htFirst_pos htarget_pos hcomparison_last_low_le_lastLow
        (by
          simpa [comparison, tFirst, target, returned] using
            hroot_le_grid_upper)
        (by
          simpa [returned] using hreturned_high_lt_one)
        hfloor_le_comparison_low htarget_lt_comparison_rate
  simpa [comparison, tFirst, target, returned] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_strict_outer_return_root_invariant
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos
      hlevelTarget_le_one_sub_grid hlevelTarget_lt_lastLow
      hlevelWidth hreturnedLast hgrid_lt_tFirst
      hroot_le_grid_upper hcomparison_low_le_root
      hinnerWidth houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint with the inner bisection
root-placement invariant derived from the exact doubled comparison chain and
the scalar source-grid hypotheses.  This is the current closest
source-shaped finite Theorem 3.2 endpoint: it no longer exposes per-inner
comparison/root certificates.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_strict_outer_return_source_grid
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_le_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        1 - grid)
    (hlevelTarget_lt_lastLow :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) < lastLow)
    (hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow)
    (hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let tFirst : ℝ :=
    comparison
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  have hcomparisonLevels : BinaryEndpointLevelVector comparison := by
    simpa [comparison] using
      uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hlastLow_pos : 0 < lastLow :=
    theorem32_calculated_grid_lastLow_pos_of_source_outer_return
      (m := m) (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels holdLevels holdEq hlevelTarget_le_one_sub_grid
      hreturnedLast
  have hlastLow_le_one_sub_grid : lastLow ≤ 1 - grid :=
    theorem32_calculated_grid_lastLow_le_one_sub_grid_of_source_outer_return
      (m := m) (outerSteps := outerSteps)
      hm oldLevels holdLevels holdEq hlevelTarget_le_one_sub_grid
      hreturnedLast
  have hlastLow_lt_one : lastLow < 1 := by
    linarith
  have htFirst_pos : 0 < tFirst :=
    hgrid_pos.trans (by simpa [comparison, tFirst] using hgrid_lt_tFirst)
  have hcomparison_last_low_le_lastLow :
      comparison
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ lastLow := by
    exact le_of_lt (by
      simpa [comparison] using hlevelTarget_lt_lastLow)
  have hfloor_le_comparison_low :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        tFirst ≤ comparison (adjacentLowIndex i) := by
    intro i hi_first _hi_last
    exact
      BinaryEndpointLevelVector_mono hcomparisonLevels
        (by
          simp [adjacentHighIndex, adjacentLowIndex, firstAdjacentIndex]
          omega)
  have htarget_lt_comparison_rate :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (comparison (adjacentHighIndex i))
            (comparison (adjacentLowIndex i)) := by
    simpa [comparison, target] using
      theorem32_target_lt_comparison_rate_of_uniform_doubled_lastLow_strict
        (m := m) hm oldLevels holdLevels holdEq hlevelTarget_lt_lastLow
  have hroot_le_grid_upper :
      let comparison : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let tFirst : ℝ :=
        comparison
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        root i ≤ returned (adjacentHighIndex i) - grid := by
    simpa [comparison, tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_root_le_grid_upper_of_nested_comparison
        (n := 2 * m + 1) (innerSteps := innerSteps)
        (by omega) comparison hcomparisonLevels grid tFirst lastLow
        htFirst_pos hgrid_pos
        (by simpa [comparison, tFirst] using hgrid_lt_tFirst)
        hlastLow_pos hlastLow_lt_one hlastLow_le_one_sub_grid
        hcomparison_last_low_le_lastLow hfloor_le_comparison_low
        (by simpa [target] using htarget_lt_comparison_rate)
  simpa [comparison, tFirst, target, returned] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_strict_outer_return_root_placement
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos
      hlevelTarget_le_one_sub_grid hlevelTarget_lt_lastLow
      hlevelWidth hreturnedLast hgrid_lt_tFirst
      hroot_le_grid_upper hinnerWidth houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint without imposing a no-exact-hit
outer-loop convention.  The executable outer return either hits the refined
penultimate optimum exactly, or the existing strict-return proof gives the
paper's additive-rate loss and operation-count certificate.
-/
theorem binaryEndpointAwareAdjacentRateObjective_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_grid
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_lt_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) <
        1 - grid)
    (hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow)
    (hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
      uniformDoubledEndpointLevels oldLevels
    let levelTarget : ℝ :=
      optimal
        (adjacentLowIndex
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let tFirst : ℝ :=
      optimal
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    levelTarget = lastLow ∨
      binaryEndpointAwareAdjacentRateObjective optimal
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
          binaryEndpointAwareAdjacentRateObjective returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
        nestedBisectionOperationCount M outerSteps innerSteps ≤
          EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let levelTarget : ℝ :=
    optimal
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let tFirst : ℝ :=
    optimal
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  have hlevelTarget_le_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        1 - grid := by
    exact le_of_lt (by simpa using hlevelTarget_lt_one_sub_grid)
  rcases
      theorem32_calculated_grid_levelTarget_eq_lastLow_or_lt_lastLow_of_source_outer_return
        (m := m) (outerSteps := outerSteps) hm oldLevels holdLevels holdEq
        hlevelTarget_lt_one_sub_grid hreturnedLast
      with hhit | hstrict
  · left
    simpa [optimal, levelTarget] using hhit
  · right
    simpa [optimal, levelTarget, tFirst, target, returned] using
      binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_strict_outer_return_source_grid
        (m := m) (M := M) (L := L)
        (outerSteps := outerSteps) (innerSteps := innerSteps)
        hm oldLevels heps holdLevels holdEq hgrid_pos
        hlevelTarget_le_one_sub_grid hstrict hlevelWidth hreturnedLast
        hgrid_lt_tFirst hinnerWidth houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint with an explicit exact-hit
tie convention.  If the outer bisection lands exactly on the refined
penultimate optimum, the source-level implementation may return the already
optimal doubled chain immediately; otherwise the checked strict-return
backward-grid proof gives the additive-rate loss and operation-count
certificate.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_grid_early_exact_return
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_lt_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) <
        1 - grid)
    (hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow)
    (hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
      uniformDoubledEndpointLevels oldLevels
    let levelTarget : ℝ :=
      optimal
        (adjacentLowIndex
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let tFirst : ℝ :=
      optimal
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let gridReturned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      if levelTarget = lastLow then optimal else gridReturned
    binaryEndpointAwareAdjacentRateObjective optimal
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let levelTarget : ℝ :=
    optimal
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let tFirst : ℝ :=
    optimal
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let gridReturned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    if levelTarget = lastLow then optimal else gridReturned
  by_cases hhit : levelTarget = lastLow
  · constructor
    · have hhit_raw :
          uniformDoubledEndpointLevels oldLevels
              (⟨2 * m + 1, by omega⟩ : Fin ((2 * m + 1) + 2)) =
            lastLow := by
        simpa [optimal, levelTarget, adjacentLowIndex, lastAdjacentIndex] using
          hhit
      simpa [optimal, levelTarget, tFirst, target, gridReturned, hhit_raw] using
        heps
    · exact nestedBisectionOperationCount_le_stepBound houter hinner
  · have hdisj :
        levelTarget = lastLow ∨
          ((binaryEndpointAwareAdjacentRateObjective optimal
                (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤
              eps +
                binaryEndpointAwareAdjacentRateObjective gridReturned
                  (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))) ∧
            nestedBisectionOperationCount M outerSteps innerSteps ≤
              EconCSLib.Optimization.nestedBisectionStepBound M L) := by
      simpa [optimal, levelTarget, tFirst, target, gridReturned] using
        binaryEndpointAwareAdjacentRateObjective_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_grid
          (m := m) (M := M) (L := L)
          (outerSteps := outerSteps) (innerSteps := innerSteps)
          hm oldLevels heps holdLevels holdEq hgrid_pos
          hlevelTarget_lt_one_sub_grid hlevelWidth hreturnedLast
          hgrid_lt_tFirst hinnerWidth houter hinner
    rcases hdisj with hhit' | hgood
    · exact False.elim (hhit hhit')
    · have hhit_raw_false :
          ¬ uniformDoubledEndpointLevels oldLevels
              (⟨2 * m + 1, by omega⟩ : Fin ((2 * m + 1) + 2)) =
            lastLow := by
        intro hraw
        exact hhit (by
          simpa [optimal, levelTarget, adjacentLowIndex, lastAdjacentIndex]
            using hraw)
      simpa [optimal, levelTarget, tFirst, target, gridReturned, returned,
        hhit_raw_false]
        using hgood

/--
Calculated source-grid Theorem 3.2 endpoint with the strict outer-return fact
derived from the source no-exact-hit bisection convention.  The visible
outer-loop obligations are now scalar: the refined penultimate target is
strictly below Algorithm 1's initial upper endpoint `1 - grid`, and the outer
bisection never tests that target exactly.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_source_grid
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_lt_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) <
        1 - grid)
    (houterNoExact :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let levelLower0 : ℝ :=
        1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
      let levelTarget : ℝ :=
        optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
      ∀ k : ℕ, k < outerSteps →
        levelTarget ≠
          EconCSLib.Optimization.realBisectionMidpoint
            (EconCSLib.Optimization.realBisectionRun
              (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
              k levelLower0 (1 - grid)).1
            (EconCSLib.Optimization.realBisectionRun
              (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
              k levelLower0 (1 - grid)).2)
    (hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow)
    (hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  have hlevelTarget_le_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        1 - grid := by
    exact le_of_lt (by simpa using hlevelTarget_lt_one_sub_grid)
  have hlevelTarget_lt_lastLow :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) < lastLow := by
    simpa using
      theorem32_calculated_grid_levelTarget_lt_lastLow_of_source_outer_return_no_exact_midpoint
        (m := m) (outerSteps := outerSteps) hm oldLevels holdLevels holdEq
        hlevelTarget_lt_one_sub_grid houterNoExact hreturnedLast
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_strict_outer_return_source_grid
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos
      hlevelTarget_le_one_sub_grid hlevelTarget_lt_lastLow
      hlevelWidth hreturnedLast hgrid_lt_tFirst hinnerWidth houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint with Algorithm 1's outer upper
endpoint `1 - grid`, where the small-grid premise is derived from the
supplement's explicit source assumption that the refined penultimate optimum
lies below `1 - grid`.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_source_upper_bound
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_lt_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) <
        1 - grid)
    (houterNoExact :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let levelLower0 : ℝ :=
        1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
      let levelTarget : ℝ :=
        optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
      ∀ k : ℕ, k < outerSteps →
        levelTarget ≠
          EconCSLib.Optimization.realBisectionMidpoint
            (EconCSLib.Optimization.realBisectionRun
              (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
              k levelLower0 (1 - grid)).1
            (EconCSLib.Optimization.realBisectionRun
              (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
              k levelLower0 (1 - grid)).2)
    (hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  have hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst := by
    simpa using
      theorem32_calculated_grid_grid_lt_tFirst_of_levelTarget_lt_one_sub_grid
        (m := m) hm oldLevels holdLevels holdEq hlevelTarget_lt_one_sub_grid
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_source_grid
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos
      hlevelTarget_lt_one_sub_grid houterNoExact hlevelWidth hreturnedLast
      hgrid_lt_tFirst hinnerWidth houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint at the source iteration depths,
using the supplement's source upper-bound assumption
`t^*_{M-2} < 1 - grid` to derive the internal small-grid fact.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_source_upper_bound_fixed_depths
    {m M L : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_lt_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) <
        1 - grid)
    (houterNoExact :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let levelLower0 : ℝ :=
        1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
      let levelTarget : ℝ :=
        optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
      ∀ k : ℕ, k < L + 1 →
        levelTarget ≠
          EconCSLib.Optimization.realBisectionMidpoint
            (EconCSLib.Optimization.realBisectionRun
              (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
              k levelLower0 (1 - grid)).1
            (EconCSLib.Optimization.realBisectionRun
              (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
              k levelLower0 (1 - grid)).2)
    (hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ (L + 1))
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          (L + 1)
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) L grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M (L + 1) L ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  simpa using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_source_upper_bound
      (m := m) (M := M) (L := L)
      (outerSteps := L + 1) (innerSteps := L)
      hm oldLevels heps holdLevels holdEq hgrid_pos
      hlevelTarget_lt_one_sub_grid houterNoExact hlevelWidth hreturnedLast
      hinnerWidth (Nat.le_refl (L + 1)) (Nat.le_refl L)

/--
Calculated source-grid Theorem 3.2 endpoint at the source iteration depths,
with the bisection-depth obligations stated in the standard post-run width
form `initial_width / 2^steps ≤ tolerance`.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_source_upper_bound_width_div_fixed_depths
    {m M L : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_lt_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) <
        1 - grid)
    (houterNoExact :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let levelLower0 : ℝ :=
        1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
      let levelTarget : ℝ :=
        optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
      ∀ k : ℕ, k < L + 1 →
        levelTarget ≠
          EconCSLib.Optimization.realBisectionMidpoint
            (EconCSLib.Optimization.realBisectionRun
              (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
              k levelLower0 (1 - grid)).1
            (EconCSLib.Optimization.realBisectionRun
              (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
              k levelLower0 (1 - grid)).2)
    (hlevelWidthDiv :
      ((1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) /
          (2 : ℝ) ^ (L + 1) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          (L + 1)
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow)
    (hinnerWidthDiv :
      1 / (2 : ℝ) ^ L ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) L grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M (L + 1) L ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  have hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ (L + 1) := by
    exact
      EconCSLib.Optimization.le_delta_mul_pow_two_of_width_div_pow_two_le
        (n := L + 1) hlevelWidthDiv
  have hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ L := by
    exact
      EconCSLib.Optimization.le_delta_mul_pow_two_of_width_div_pow_two_le
        (n := L) hinnerWidthDiv
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_source_upper_bound_fixed_depths
      (m := m) (M := M) (L := L)
      hm oldLevels heps holdLevels holdEq hgrid_pos
      hlevelTarget_lt_one_sub_grid houterNoExact hlevelWidth hreturnedLast
      hinnerWidth

/--
Calculated source-grid Theorem 3.2 endpoint where the returned outer endpoint
is the executable bisection run's upper endpoint by definition.  This removes
the separate source-interface equality that named `lastLow`; the remaining
finite assumptions are the source upper-bracket fact, the no-exact outer
midpoint convention, and the two post-run width bounds.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_source_upper_bound_width_div_fixed_depths_auto_lastLow
    {m M L : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_lt_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) <
        1 - grid)
    (houterNoExact :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let levelLower0 : ℝ :=
        1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
      let levelTarget : ℝ :=
        optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
      ∀ k : ℕ, k < L + 1 →
        levelTarget ≠
          EconCSLib.Optimization.realBisectionMidpoint
            (EconCSLib.Optimization.realBisectionRun
              (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
              k levelLower0 (1 - grid)).1
            (EconCSLib.Optimization.realBisectionRun
              (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
              k levelLower0 (1 - grid)).2)
    (hlevelWidthDiv :
      ((1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) /
          (2 : ℝ) ^ (L + 1) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hinnerWidthDiv :
      1 / (2 : ℝ) ^ L ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)) :
    let lastLow : ℝ :=
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget
          (uniformDoubledEndpointLevels oldLevels
            (adjacentLowIndex
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
        (L + 1)
        (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
        (1 - grid)).2
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) L grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M (L + 1) L ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let lastLow : ℝ :=
    (EconCSLib.Optimization.realBisectionRun
      (EconCSLib.Optimization.realBisectionAboveTarget
        (uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
      (L + 1)
      (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
      (1 - grid)).2
  have hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          (L + 1)
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow := by
    rfl
  simpa [lastLow] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_source_upper_bound_width_div_fixed_depths
      (m := m) (M := M) (L := L) (lastLow := lastLow)
      hm oldLevels heps holdLevels holdEq hgrid_pos
      hlevelTarget_lt_one_sub_grid houterNoExact hlevelWidthDiv
      hreturnedLast hinnerWidthDiv

/--
Fixed-depth source-grid Theorem 3.2 endpoint without a no-exact-hit
convention.  With `lastLow` defined as the executable outer bisection's
returned upper endpoint, the result is a precise dichotomy: either the outer
loop hit the refined penultimate optimum exactly, or the usual source
loss/runtime bound holds.
-/
theorem binaryEndpointAwareAdjacentRateObjective_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_upper_bound_width_div_fixed_depths_auto_lastLow
    {m M L : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_lt_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) <
        1 - grid)
    (hlevelWidthDiv :
      ((1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) /
          (2 : ℝ) ^ (L + 1) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hinnerWidthDiv :
      1 / (2 : ℝ) ^ L ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)) :
    let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
      uniformDoubledEndpointLevels oldLevels
    let levelTarget : ℝ :=
      optimal
        (adjacentLowIndex
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let lastLow : ℝ :=
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
        (L + 1)
        (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
        (1 - grid)).2
    let tFirst : ℝ :=
      optimal
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) L grid tFirst target lastLow
    levelTarget = lastLow ∨
      binaryEndpointAwareAdjacentRateObjective optimal
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
          binaryEndpointAwareAdjacentRateObjective returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
        nestedBisectionOperationCount M (L + 1) L ≤
          EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let levelTarget : ℝ :=
    optimal
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let lastLow : ℝ :=
    (EconCSLib.Optimization.realBisectionRun
      (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
      (L + 1)
      (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
      (1 - grid)).2
  have hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          (L + 1)
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow := by
    simpa [lastLow, levelTarget, optimal]
  have hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst := by
    simpa using
      theorem32_calculated_grid_grid_lt_tFirst_of_levelTarget_lt_one_sub_grid
        (m := m) hm oldLevels holdLevels holdEq hlevelTarget_lt_one_sub_grid
  have hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ (L + 1) := by
    exact
      EconCSLib.Optimization.le_delta_mul_pow_two_of_width_div_pow_two_le
        (n := L + 1) hlevelWidthDiv
  have hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ L := by
    exact
      EconCSLib.Optimization.le_delta_mul_pow_two_of_width_div_pow_two_le
        (n := L) hinnerWidthDiv
  simpa [optimal, levelTarget, lastLow] using
    binaryEndpointAwareAdjacentRateObjective_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_grid
      (m := m) (M := M) (L := L)
      (outerSteps := L + 1) (innerSteps := L) (lastLow := lastLow)
      hm oldLevels heps holdLevels holdEq hgrid_pos
      hlevelTarget_lt_one_sub_grid hlevelWidth hreturnedLast
      hgrid_lt_tFirst hinnerWidth (Nat.le_refl (L + 1)) (Nat.le_refl L)

/--
Fixed-depth source-grid Theorem 3.2 endpoint with a single source-shaped width
budget.  The max-budget premise simultaneously bounds the outer returned-width
term and the inner bisection width term.
-/
theorem binaryEndpointAwareAdjacentRateObjective_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_upper_bound_width_budget_fixed_depths_auto_lastLow
    {m M L : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_lt_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) <
        1 - grid)
    (hwidthBudget :
      max
          (((1 - grid) -
              (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) /
            (2 : ℝ) ^ (L + 1))
          (1 / (2 : ℝ) ^ L) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)) :
    let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
      uniformDoubledEndpointLevels oldLevels
    let levelTarget : ℝ :=
      optimal
        (adjacentLowIndex
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let lastLow : ℝ :=
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
        (L + 1)
        (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
        (1 - grid)).2
    let tFirst : ℝ :=
      optimal
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) L grid tFirst target lastLow
    levelTarget = lastLow ∨
      binaryEndpointAwareAdjacentRateObjective optimal
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
          binaryEndpointAwareAdjacentRateObjective returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
        nestedBisectionOperationCount M (L + 1) L ≤
          EconCSLib.Optimization.nestedBisectionStepBound M L := by
  have hlevelWidthDiv :
      ((1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) /
          (2 : ℝ) ^ (L + 1) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) :=
    (le_max_left
      (((1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) /
          (2 : ℝ) ^ (L + 1))
      (1 / (2 : ℝ) ^ L)).trans hwidthBudget
  have hinnerWidthDiv :
      1 / (2 : ℝ) ^ L ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) :=
    (le_max_right
      (((1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) /
          (2 : ℝ) ^ (L + 1))
      (1 / (2 : ℝ) ^ L)).trans hwidthBudget
  exact
    binaryEndpointAwareAdjacentRateObjective_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_upper_bound_width_div_fixed_depths_auto_lastLow
      (m := m) (M := M) (L := L) hm oldLevels heps holdLevels holdEq
      hgrid_pos hlevelTarget_lt_one_sub_grid hlevelWidthDiv hinnerWidthDiv

/--
Fixed-depth source-grid Theorem 3.2 endpoint with the source depth choice
stated before the two bisection runs.  The single scalar premise
`max (outerWidth / 2) 1 <= delta * 2^L` is the source-style "choose `L`
large enough" condition; the reusable bisection arithmetic converts it to the
post-run max-width budget consumed by the checked executable dichotomy.
-/
theorem binaryEndpointAwareAdjacentRateObjective_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_upper_bound_source_depth_fixed_depths_auto_lastLow
    {m M L : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_lt_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) <
        1 - grid)
    (hsourceDepth :
      max
          (((1 - grid) -
              (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) / 2)
          1 ≤
        (eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)) *
          (2 : ℝ) ^ L) :
    let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
      uniformDoubledEndpointLevels oldLevels
    let levelTarget : ℝ :=
      optimal
        (adjacentLowIndex
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let lastLow : ℝ :=
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
        (L + 1)
        (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
        (1 - grid)).2
    let tFirst : ℝ :=
      optimal
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) L grid tFirst target lastLow
    levelTarget = lastLow ∨
      binaryEndpointAwareAdjacentRateObjective optimal
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
          binaryEndpointAwareAdjacentRateObjective returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
        nestedBisectionOperationCount M (L + 1) L ≤
          EconCSLib.Optimization.nestedBisectionStepBound M L := by
  have hwidthBudget :
      max
          (((1 - grid) -
              (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) /
            (2 : ℝ) ^ (L + 1))
          (1 / (2 : ℝ) ^ L) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) :=
    EconCSLib.Optimization.max_outer_half_inner_width_div_pow_two_le_of_le_delta_mul_pow_two
      (outerWidth :=
        (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))))
      (delta :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
      (n := L)
      (by simpa using hsourceDepth)
  exact
    binaryEndpointAwareAdjacentRateObjective_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_upper_bound_width_budget_fixed_depths_auto_lastLow
      (m := m) (M := M) (L := L) hm oldLevels heps holdLevels holdEq
      hgrid_pos hlevelTarget_lt_one_sub_grid hwidthBudget

/--
Fixed-depth source-grid Theorem 3.2 endpoint with the exact-hit tie handled
by early return of the optimal doubled chain.  The single source-depth premise
is the paper's "choose `L` large enough" width condition.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_upper_bound_source_depth_fixed_depths_auto_lastLow_early_exact_return
    {m M L : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_lt_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) <
        1 - grid)
    (hsourceDepth :
      max
          (((1 - grid) -
              (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) / 2)
          1 ≤
        (eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)) *
          (2 : ℝ) ^ L) :
    let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
      uniformDoubledEndpointLevels oldLevels
    let levelTarget : ℝ :=
      optimal
        (adjacentLowIndex
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let lastLow : ℝ :=
      (EconCSLib.Optimization.realBisectionRun
        (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
        (L + 1)
        (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
        (1 - grid)).2
    let tFirst : ℝ :=
      optimal
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let gridReturned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) L grid tFirst target lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      if levelTarget = lastLow then optimal else gridReturned
    binaryEndpointAwareAdjacentRateObjective optimal
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M (L + 1) L ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
    uniformDoubledEndpointLevels oldLevels
  let levelTarget : ℝ :=
    optimal
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let lastLow : ℝ :=
    (EconCSLib.Optimization.realBisectionRun
      (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
      (L + 1)
      (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
      (1 - grid)).2
  have hwidthBudget :
      max
          (((1 - grid) -
              (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) /
            (2 : ℝ) ^ (L + 1))
          (1 / (2 : ℝ) ^ L) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) :=
    EconCSLib.Optimization.max_outer_half_inner_width_div_pow_two_le_of_le_delta_mul_pow_two
      (outerWidth :=
        (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))))
      (delta :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
      (n := L)
      (by simpa using hsourceDepth)
  have hlevelWidthDiv :
      ((1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) /
          (2 : ℝ) ^ (L + 1) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) :=
    (le_max_left
      (((1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) /
          (2 : ℝ) ^ (L + 1))
      (1 / (2 : ℝ) ^ L)).trans hwidthBudget
  have hinnerWidthDiv :
      1 / (2 : ℝ) ^ L ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) :=
    (le_max_right
      (((1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) /
          (2 : ℝ) ^ (L + 1))
      (1 / (2 : ℝ) ^ L)).trans hwidthBudget
  have hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ (L + 1) :=
    EconCSLib.Optimization.le_delta_mul_pow_two_of_width_div_pow_two_le
      (n := L + 1) hlevelWidthDiv
  have hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ L :=
    EconCSLib.Optimization.le_delta_mul_pow_two_of_width_div_pow_two_le
      (n := L) hinnerWidthDiv
  have hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          (L + 1)
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow := by
    simpa [lastLow, levelTarget, optimal]
  have hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst := by
    simpa using
      theorem32_calculated_grid_grid_lt_tFirst_of_levelTarget_lt_one_sub_grid
        (m := m) hm oldLevels holdLevels holdEq hlevelTarget_lt_one_sub_grid
  simpa [optimal, levelTarget, lastLow] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_grid_early_exact_return
      (m := m) (M := M) (L := L)
      (outerSteps := L + 1) (innerSteps := L) (lastLow := lastLow)
      hm oldLevels heps holdLevels holdEq hgrid_pos
      hlevelTarget_lt_one_sub_grid hlevelWidth hreturnedLast
      hgrid_lt_tFirst hinnerWidth (Nat.le_refl (L + 1)) (Nat.le_refl L)

/--
Source-grid Theorem 3.2 endpoint with a finite source-depth choice.  If the
source tolerance scale is positive, then some bisection depth satisfies the
source pre-run width condition, and the checked executable dichotomy follows
at that depth.
-/
theorem binaryEndpointAwareAdjacentRateObjective_exists_depth_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_upper_bound
    {m M : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_lt_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) <
        1 - grid)
    (hsourceDelta_pos :
      0 <
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)) :
    ∃ L : ℕ,
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let levelTarget : ℝ :=
        optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let lastLow : ℝ :=
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          (L + 1)
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2
      let tFirst : ℝ :=
        optimal
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) L grid tFirst target lastLow
      levelTarget = lastLow ∨
        binaryEndpointAwareAdjacentRateObjective optimal
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
            binaryEndpointAwareAdjacentRateObjective returned
              (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
          nestedBisectionOperationCount M (L + 1) L ≤
            EconCSLib.Optimization.nestedBisectionStepBound M L := by
  rcases
      EconCSLib.Optimization.exists_nat_le_delta_mul_pow_two
        (budget :=
          max
            (((1 - grid) -
                (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) / 2)
            1)
        (delta :=
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
        hsourceDelta_pos with
    ⟨L, hsourceDepth⟩
  refine ⟨L, ?_⟩
  exact
    binaryEndpointAwareAdjacentRateObjective_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_upper_bound_source_depth_fixed_depths_auto_lastLow
      (m := m) (M := M) (L := L) hm oldLevels heps holdLevels holdEq
      hgrid_pos hlevelTarget_lt_one_sub_grid hsourceDepth

/--
Source-grid Theorem 3.2 endpoint with a finite source-depth choice and the
source tolerance stated as `eps > 0`.  The positivity of the explicit grid
width is derived from feasibility of the old equalized levels.
-/
theorem binaryEndpointAwareAdjacentRateObjective_exists_depth_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_upper_bound_of_eps_pos
    {m M : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid : ℝ}
    (heps : 0 < eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlevelTarget_lt_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) <
        1 - grid) :
    ∃ L : ℕ,
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let levelTarget : ℝ :=
        optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let lastLow : ℝ :=
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          (L + 1)
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2
      let tFirst : ℝ :=
        optimal
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) L grid tFirst target lastLow
      levelTarget = lastLow ∨
        binaryEndpointAwareAdjacentRateObjective optimal
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
            binaryEndpointAwareAdjacentRateObjective returned
              (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
          nestedBisectionOperationCount M (L + 1) L ≤
            EconCSLib.Optimization.nestedBisectionStepBound M L := by
  exact
    binaryEndpointAwareAdjacentRateObjective_exists_depth_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_upper_bound
      (m := m) (M := M) hm oldLevels heps.le holdLevels holdEq
      hgrid_pos hlevelTarget_lt_one_sub_grid
      (theorem32_uniform_doubled_explicit_delta_pos
        (m := m) hm (oldLevels := oldLevels) (eps := eps) heps holdLevels)

/--
Source-grid Theorem 3.2 endpoint with the source small-grid condition stated
using the C.5/C.7/C.8 objective-rate lower-bound package.  This keeps the
exact-hit dichotomy while replacing the internal upper-bracket comparison by
`grid < ((1 / 5) * oldObjective) / 2`.
-/
theorem binaryEndpointAwareAdjacentRateObjective_exists_depth_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_objective_grid_of_eps_pos
    {m M : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid : ℝ}
    (heps : 0 < eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hgrid_lt_bound :
      grid <
        ((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2) :
    ∃ L : ℕ,
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let levelTarget : ℝ :=
        optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let lastLow : ℝ :=
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          (L + 1)
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2
      let tFirst : ℝ :=
        optimal
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) L grid tFirst target lastLow
      levelTarget = lastLow ∨
        binaryEndpointAwareAdjacentRateObjective optimal
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
            binaryEndpointAwareAdjacentRateObjective returned
              (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
          nestedBisectionOperationCount M (L + 1) L ≤
            EconCSLib.Optimization.nestedBisectionStepBound M L := by
  have hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst := by
    simpa using
      theorem32_calculated_grid_lt_tFirst_of_grid_lt_objective_bound
        (m := m) hm oldLevels holdLevels holdEq
        (BinaryEndpointLevelVector_uniform_equalized_one_fifth_objective_le_one
          hm holdLevels holdEq)
        hgrid_lt_bound
  have hlevelTarget_lt_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) <
        1 - grid := by
    simpa using
      theorem32_calculated_grid_levelTarget_lt_one_sub_grid_of_grid_lt_tFirst
        (m := m) hm oldLevels holdLevels holdEq hgrid_lt_tFirst
  exact
    binaryEndpointAwareAdjacentRateObjective_exists_depth_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_upper_bound_of_eps_pos
      (m := m) (M := M) hm oldLevels heps holdLevels holdEq
      hgrid_pos hlevelTarget_lt_one_sub_grid

/--
Source-grid Theorem 3.2 endpoint with finite grid and depth choices.  For
every positive source tolerance, the C.5/C.7/C.8 objective lower-bound package
provides a positive small grid, and finite dyadic depth then gives either an
exact outer hit or the additive-rate loss and runtime certificate.
-/
theorem binaryEndpointAwareAdjacentRateObjective_exists_grid_depth_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_eps_pos
    {m M : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 < eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    ∃ grid : ℝ,
      0 < grid ∧
      grid <
        ((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2 ∧
      ∃ L : ℕ,
        let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
          uniformDoubledEndpointLevels oldLevels
        let levelTarget : ℝ :=
          optimal
            (adjacentLowIndex
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
        let lastLow : ℝ :=
          (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
            (L + 1)
            (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
            (1 - grid)).2
        let tFirst : ℝ :=
          optimal
            (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
        let target : ℝ := -Real.log lastLow
        let returned : Fin ((2 * m + 1) + 2) → ℝ :=
          theorem32BackwardGridLowBisectionLevels
            (2 * m + 1) L grid tFirst target lastLow
        levelTarget = lastLow ∨
          binaryEndpointAwareAdjacentRateObjective optimal
              (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
              binaryEndpointAwareAdjacentRateObjective returned
                (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
            nestedBisectionOperationCount M (L + 1) L ≤
              EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let bound : ℝ :=
    ((1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ))) / 2
  have hobj_pos :
      0 <
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ)) := by
    unfold binaryEndpointAwareAdjacentRateObjective
    exact
      EconCSLib.finiteMin_pos
        (binaryEndpointAwareAdjacentRate oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ)))
        (fun i =>
          binaryEndpointAwareAdjacentRate_pos
            hm oldLevels (fun _ : Fin (m + 2) => (1 : ℝ)) holdLevels
            (by intro j; norm_num) (by intro j; norm_num) i)
  have hbound_pos : 0 < bound := by
    positivity
  let grid : ℝ := bound / 2
  have hgrid_pos : 0 < grid := by
    positivity
  have hgrid_lt_bound : grid < bound := by
    dsimp [grid]
    linarith
  have hcert :
      ∃ L : ℕ,
        let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
          uniformDoubledEndpointLevels oldLevels
        let levelTarget : ℝ :=
          optimal
            (adjacentLowIndex
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
        let lastLow : ℝ :=
          (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
            (L + 1)
            (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
            (1 - grid)).2
        let tFirst : ℝ :=
          optimal
            (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
        let target : ℝ := -Real.log lastLow
        let returned : Fin ((2 * m + 1) + 2) → ℝ :=
          theorem32BackwardGridLowBisectionLevels
            (2 * m + 1) L grid tFirst target lastLow
        levelTarget = lastLow ∨
          binaryEndpointAwareAdjacentRateObjective optimal
              (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
              binaryEndpointAwareAdjacentRateObjective returned
                (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
            nestedBisectionOperationCount M (L + 1) L ≤
              EconCSLib.Optimization.nestedBisectionStepBound M L := by
    exact
      binaryEndpointAwareAdjacentRateObjective_exists_depth_exact_outer_hit_or_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_objective_grid_of_eps_pos
        (m := m) (M := M) hm oldLevels heps holdLevels holdEq
        hgrid_pos (by simpa [bound, grid] using hgrid_lt_bound)
  exact ⟨grid, hgrid_pos, by simpa [bound, grid] using hgrid_lt_bound, hcert⟩

/--
Source-grid Theorem 3.2 endpoint with finite grid and depth choices, using
the exact-hit early-return convention.  For every positive source tolerance,
Lean constructs a positive small grid and a finite dyadic depth such that the
returned chain has additive-rate loss at most `eps` and satisfies the stated
nested-bisection step bound.
-/
theorem binaryEndpointAwareAdjacentRateObjective_exists_grid_depth_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_eps_pos
    {m M : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 < eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    ∃ grid : ℝ,
      0 < grid ∧
      grid <
        ((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2 ∧
      ∃ L : ℕ,
        let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
          uniformDoubledEndpointLevels oldLevels
        let levelTarget : ℝ :=
          optimal
            (adjacentLowIndex
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
        let lastLow : ℝ :=
          (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
            (L + 1)
            (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
            (1 - grid)).2
        let tFirst : ℝ :=
          optimal
            (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
        let target : ℝ := -Real.log lastLow
        let gridReturned : Fin ((2 * m + 1) + 2) → ℝ :=
          theorem32BackwardGridLowBisectionLevels
            (2 * m + 1) L grid tFirst target lastLow
        let returned : Fin ((2 * m + 1) + 2) → ℝ :=
          if levelTarget = lastLow then optimal else gridReturned
        binaryEndpointAwareAdjacentRateObjective optimal
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
            binaryEndpointAwareAdjacentRateObjective returned
              (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
          nestedBisectionOperationCount M (L + 1) L ≤
            EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let bound : ℝ :=
    ((1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ))) / 2
  have hobj_pos :
      0 <
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ)) := by
    unfold binaryEndpointAwareAdjacentRateObjective
    exact
      EconCSLib.finiteMin_pos
        (binaryEndpointAwareAdjacentRate oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ)))
        (fun i =>
          binaryEndpointAwareAdjacentRate_pos
            hm oldLevels (fun _ : Fin (m + 2) => (1 : ℝ)) holdLevels
            (by intro j; norm_num) (by intro j; norm_num) i)
  have hbound_pos : 0 < bound := by
    positivity
  let grid : ℝ := bound / 2
  have hgrid_pos : 0 < grid := by
    positivity
  have hgrid_lt_bound : grid < bound := by
    dsimp [grid]
    linarith
  have hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst := by
    simpa [bound, grid] using
      theorem32_calculated_grid_lt_tFirst_of_grid_lt_objective_bound
        (m := m) hm oldLevels holdLevels holdEq
        (BinaryEndpointLevelVector_uniform_equalized_one_fifth_objective_le_one
          hm holdLevels holdEq)
        (by simpa [bound, grid] using hgrid_lt_bound)
  have hlevelTarget_lt_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) <
        1 - grid := by
    simpa using
      theorem32_calculated_grid_levelTarget_lt_one_sub_grid_of_grid_lt_tFirst
        (m := m) hm oldLevels holdLevels holdEq hgrid_lt_tFirst
  have hsourceDelta_pos :
      0 <
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) :=
    theorem32_uniform_doubled_explicit_delta_pos
      (m := m) hm (oldLevels := oldLevels) (eps := eps) heps holdLevels
  rcases
      EconCSLib.Optimization.exists_nat_le_delta_mul_pow_two
        (budget :=
          max
            (((1 - grid) -
                (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) / 2)
            1)
        (delta :=
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
        hsourceDelta_pos with
    ⟨L, hsourceDepth⟩
  have hcert :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let levelTarget : ℝ :=
        optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let lastLow : ℝ :=
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          (L + 1)
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2
      let tFirst : ℝ :=
        optimal
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let gridReturned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) L grid tFirst target lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        if levelTarget = lastLow then optimal else gridReturned
      binaryEndpointAwareAdjacentRateObjective optimal
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
          binaryEndpointAwareAdjacentRateObjective returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
        nestedBisectionOperationCount M (L + 1) L ≤
          EconCSLib.Optimization.nestedBisectionStepBound M L := by
    exact
      binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_upper_bound_source_depth_fixed_depths_auto_lastLow_early_exact_return
        (m := m) (M := M) (L := L) hm oldLevels heps.le holdLevels holdEq
        hgrid_pos hlevelTarget_lt_one_sub_grid hsourceDepth
  exact ⟨grid, hgrid_pos, by simpa [bound, grid] using hgrid_lt_bound, L, hcert⟩

/--
Source-grid Theorem 3.2 endpoint with finite grid and depth choices, reported
in the paper's quadratic runtime shape.  The previous theorem supplies the
additive loss and the closed-form step bound; the reusable bisection arithmetic
then bounds that closed form by `M * (L + 1)^2`.
-/
theorem binaryEndpointAwareAdjacentRateObjective_exists_grid_depth_loss_and_runtime_quadratic_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_eps_pos
    {m M : ℕ} (hm : 0 < m) (hM : 0 < M)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 < eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    ∃ grid : ℝ,
      0 < grid ∧
      grid <
        ((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2 ∧
      ∃ L : ℕ,
        let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
          uniformDoubledEndpointLevels oldLevels
        let levelTarget : ℝ :=
          optimal
            (adjacentLowIndex
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
        let lastLow : ℝ :=
          (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
            (L + 1)
            (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
            (1 - grid)).2
        let tFirst : ℝ :=
          optimal
            (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
        let target : ℝ := -Real.log lastLow
        let gridReturned : Fin ((2 * m + 1) + 2) → ℝ :=
          theorem32BackwardGridLowBisectionLevels
            (2 * m + 1) L grid tFirst target lastLow
        let returned : Fin ((2 * m + 1) + 2) → ℝ :=
          if levelTarget = lastLow then optimal else gridReturned
        binaryEndpointAwareAdjacentRateObjective optimal
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
            binaryEndpointAwareAdjacentRateObjective returned
              (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
          nestedBisectionOperationCount M (L + 1) L ≤ M * (L + 1) ^ 2 := by
  rcases
      binaryEndpointAwareAdjacentRateObjective_exists_grid_depth_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_eps_pos
        (m := m) (M := M) hm oldLevels heps holdLevels holdEq with
    ⟨grid, hgrid_pos, hgrid_lt, L, hcert⟩
  refine ⟨grid, hgrid_pos, hgrid_lt, L, ?_⟩
  dsimp at hcert ⊢
  exact
    ⟨hcert.1,
      hcert.2.trans
        (EconCSLib.Optimization.nestedBisectionStepBound_le_mul_succ_sq
          (M := M) (L := L) hM)⟩

/--
Source-grid Theorem 3.2 endpoint with an explicit logarithmic depth witness.
The chosen dyadic depth satisfies the same source budget used by the finite
certificate and is bounded by `log₂(max(1, budget / delta)) + 2`; the runtime
is then bounded by the finite quadratic form `M * (L + 1)^2`.
-/
theorem binaryEndpointAwareAdjacentRateObjective_exists_grid_log_depth_loss_and_runtime_quadratic_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_eps_pos
    {m M : ℕ} (hm : 0 < m) (hM : 0 < M)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 < eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    ∃ grid : ℝ,
      0 < grid ∧
      grid <
        ((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2 ∧
      ∃ L : ℕ,
        let sourceDepthBudget : ℝ :=
          max
            (((1 - grid) -
                (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) / 2)
            1
        let sourceDelta : ℝ :=
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
        let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
          uniformDoubledEndpointLevels oldLevels
        let levelTarget : ℝ :=
          optimal
            (adjacentLowIndex
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
        let lastLow : ℝ :=
          (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
            (L + 1)
            (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
            (1 - grid)).2
        let tFirst : ℝ :=
          optimal
            (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
        let target : ℝ := -Real.log lastLow
        let gridReturned : Fin ((2 * m + 1) + 2) → ℝ :=
          theorem32BackwardGridLowBisectionLevels
            (2 * m + 1) L grid tFirst target lastLow
        let returned : Fin ((2 * m + 1) + 2) → ℝ :=
          if levelTarget = lastLow then optimal else gridReturned
        ((L + 1 : ℕ) : ℝ) ≤
            Real.logb 2 (max 1 (sourceDepthBudget / sourceDelta)) + 2 ∧
          binaryEndpointAwareAdjacentRateObjective optimal
              (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
              binaryEndpointAwareAdjacentRateObjective returned
                (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
            nestedBisectionOperationCount M (L + 1) L ≤ M * (L + 1) ^ 2 := by
  let bound : ℝ :=
    ((1 / 5 : ℝ) *
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ))) / 2
  have hobj_pos :
      0 <
        binaryEndpointAwareAdjacentRateObjective oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ)) := by
    unfold binaryEndpointAwareAdjacentRateObjective
    exact
      EconCSLib.finiteMin_pos
        (binaryEndpointAwareAdjacentRate oldLevels
          (fun _ : Fin (m + 2) => (1 : ℝ)))
        (fun i =>
          binaryEndpointAwareAdjacentRate_pos
            hm oldLevels (fun _ : Fin (m + 2) => (1 : ℝ)) holdLevels
            (by intro j; norm_num) (by intro j; norm_num) i)
  have hbound_pos : 0 < bound := by
    positivity
  let grid : ℝ := bound / 2
  have hgrid_pos : 0 < grid := by
    positivity
  have hgrid_lt_bound : grid < bound := by
    dsimp [grid]
    linarith
  have hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst := by
    simpa [bound, grid] using
      theorem32_calculated_grid_lt_tFirst_of_grid_lt_objective_bound
        (m := m) hm oldLevels holdLevels holdEq
        (BinaryEndpointLevelVector_uniform_equalized_one_fifth_objective_le_one
          hm holdLevels holdEq)
        (by simpa [bound, grid] using hgrid_lt_bound)
  have hlevelTarget_lt_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) <
        1 - grid := by
    simpa using
      theorem32_calculated_grid_levelTarget_lt_one_sub_grid_of_grid_lt_tFirst
        (m := m) hm oldLevels holdLevels holdEq hgrid_lt_tFirst
  have hsourceDelta_pos :
      0 <
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) :=
    theorem32_uniform_doubled_explicit_delta_pos
      (m := m) hm (oldLevels := oldLevels) (eps := eps) heps holdLevels
  rcases
      EconCSLib.Optimization.exists_nat_le_delta_mul_pow_two_and_succ_le_logb_max
        (budget :=
          max
            (((1 - grid) -
                (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) / 2)
            1)
        (delta :=
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
        hsourceDelta_pos with
    ⟨L, hsourceDepth, hLlog⟩
  have hcert :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let levelTarget : ℝ :=
        optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let lastLow : ℝ :=
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
          (L + 1)
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2
      let tFirst : ℝ :=
        optimal
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let gridReturned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) L grid tFirst target lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        if levelTarget = lastLow then optimal else gridReturned
      binaryEndpointAwareAdjacentRateObjective optimal
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
          binaryEndpointAwareAdjacentRateObjective returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
        nestedBisectionOperationCount M (L + 1) L ≤
          EconCSLib.Optimization.nestedBisectionStepBound M L := by
    exact
      binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_source_upper_bound_source_depth_fixed_depths_auto_lastLow_early_exact_return
        (m := m) (M := M) (L := L) hm oldLevels heps.le holdLevels holdEq
        hgrid_pos hlevelTarget_lt_one_sub_grid hsourceDepth
  refine ⟨grid, hgrid_pos, by simpa [bound, grid] using hgrid_lt_bound, L, ?_⟩
  dsimp at hcert hLlog ⊢
  exact
    ⟨hLlog, hcert.1,
      hcert.2.trans
        (EconCSLib.Optimization.nestedBisectionStepBound_le_mul_succ_sq
          (M := M) (L := L) hM)⟩

/--
Source-grid Theorem 3.2 endpoint in the paper's logarithmic runtime shape.
The previous theorem constructs a dyadic depth bounded by the source log
expression; this corollary reports the concrete operation count directly as a
real-valued `M * (log₂(...) + 2)^2` bound.
-/
theorem binaryEndpointAwareAdjacentRateObjective_exists_grid_log_depth_loss_and_runtime_real_log_quadratic_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_eps_pos
    {m M : ℕ} (hm : 0 < m) (hM : 0 < M)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 < eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    ∃ grid : ℝ,
      0 < grid ∧
      grid <
        ((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2 ∧
      ∃ L : ℕ,
        let sourceDepthBudget : ℝ :=
          max
            (((1 - grid) -
                (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) / 2)
            1
        let sourceDelta : ℝ :=
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
        let runtimeLog : ℝ :=
          Real.logb 2 (max 1 (sourceDepthBudget / sourceDelta)) + 2
        let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
          uniformDoubledEndpointLevels oldLevels
        let levelTarget : ℝ :=
          optimal
            (adjacentLowIndex
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
        let lastLow : ℝ :=
          (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
            (L + 1)
            (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
            (1 - grid)).2
        let tFirst : ℝ :=
          optimal
            (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
        let target : ℝ := -Real.log lastLow
        let gridReturned : Fin ((2 * m + 1) + 2) → ℝ :=
          theorem32BackwardGridLowBisectionLevels
            (2 * m + 1) L grid tFirst target lastLow
        let returned : Fin ((2 * m + 1) + 2) → ℝ :=
          if levelTarget = lastLow then optimal else gridReturned
        ((L + 1 : ℕ) : ℝ) ≤ runtimeLog ∧
          binaryEndpointAwareAdjacentRateObjective optimal
              (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
              binaryEndpointAwareAdjacentRateObjective returned
                (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
            ((nestedBisectionOperationCount M (L + 1) L : ℕ) : ℝ) ≤
              (M : ℝ) * runtimeLog ^ 2 := by
  rcases
      binaryEndpointAwareAdjacentRateObjective_exists_grid_log_depth_loss_and_runtime_quadratic_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_eps_pos
        (m := m) (M := M) hm hM oldLevels heps holdLevels holdEq with
    ⟨grid, hgrid_pos, hgrid_lt, L, hcert⟩
  refine ⟨grid, hgrid_pos, hgrid_lt, L, ?_⟩
  dsimp at hcert ⊢
  refine ⟨hcert.1, hcert.2.1, ?_⟩
  simpa [nestedBisectionOperationCount, Nat.mul_add, Nat.mul_one] using
    EconCSLib.Optimization.nestedBisection_operation_count_real_le_mul_sq_of_depth_le
      (M := M) (L := L) (outerSteps := L + 1) (innerSteps := L)
      (R :=
        Real.logb 2
          (max 1
            (max
                (((1 - grid) -
                    (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) / 2)
                1 /
              (eps /
                ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
                  (((1 / 5 : ℝ) *
                      binaryEndpointAwareAdjacentRateObjective oldLevels
                        (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)))) + 2)
      hM hcert.1 (Nat.le_refl (L + 1)) (Nat.le_refl L)

/--
Theorem 3.2 for the named uniform source-shaped `NestedBisection` output.
This is the same calculated-grid proof as the previous theorem, with the
returned vector packaged as `theorem32UniformDoubledNestedBisectionOutput`.
-/
theorem binaryEndpointAwareAdjacentRateObjective_exists_grid_depth_loss_and_runtime_le_of_theorem32_uniform_doubled_nested_bisection_output_of_eps_pos
    {m M : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 < eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    ∃ grid : ℝ,
      0 < grid ∧
      grid <
        ((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2 ∧
      ∃ L : ℕ,
        binaryEndpointAwareAdjacentRateObjective
            (uniformDoubledEndpointLevels oldLevels)
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
            binaryEndpointAwareAdjacentRateObjective
              (theorem32UniformDoubledNestedBisectionOutput m L oldLevels grid)
              (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
          nestedBisectionOperationCount M (L + 1) L ≤
            EconCSLib.Optimization.nestedBisectionStepBound M L := by
  rcases
    binaryEndpointAwareAdjacentRateObjective_exists_grid_depth_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_eps_pos
      (m := m) (M := M) hm oldLevels heps holdLevels holdEq with
    ⟨grid, hgrid_pos, hgrid_lt, L, hcert⟩
  exact
    ⟨grid, hgrid_pos, hgrid_lt, L, by
      simpa [theorem32UniformDoubledNestedBisectionOutput] using hcert⟩

/--
Theorem 3.2 for the named uniform source-shaped `NestedBisection` output in
the paper's logarithmic runtime form.  It reports the constructed output's
additive rate loss together with the real-valued operation-count bound
`M * (log₂(...) + 2)^2`.
-/
theorem binaryEndpointAwareAdjacentRateObjective_exists_grid_log_depth_loss_and_runtime_real_log_quadratic_le_of_theorem32_uniform_doubled_nested_bisection_output_of_eps_pos
    {m M : ℕ} (hm : 0 < m) (hM : 0 < M)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 < eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    ∃ grid : ℝ,
      0 < grid ∧
      grid <
        ((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2 ∧
      ∃ L : ℕ,
        let sourceDepthBudget : ℝ :=
          max
            (((1 - grid) -
                (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) / 2)
            1
        let sourceDelta : ℝ :=
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
        let runtimeLog : ℝ :=
          Real.logb 2 (max 1 (sourceDepthBudget / sourceDelta)) + 2
        ((L + 1 : ℕ) : ℝ) ≤ runtimeLog ∧
          binaryEndpointAwareAdjacentRateObjective
              (uniformDoubledEndpointLevels oldLevels)
              (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
              binaryEndpointAwareAdjacentRateObjective
                (theorem32UniformDoubledNestedBisectionOutput m L oldLevels grid)
                (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
            ((nestedBisectionOperationCount M (L + 1) L : ℕ) : ℝ) ≤
              (M : ℝ) * runtimeLog ^ 2 := by
  rcases
    binaryEndpointAwareAdjacentRateObjective_exists_grid_log_depth_loss_and_runtime_real_log_quadratic_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_eps_pos
      (m := m) (M := M) hm hM oldLevels heps holdLevels holdEq with
    ⟨grid, hgrid_pos, hgrid_lt, L, hcert⟩
  exact
    ⟨grid, hgrid_pos, hgrid_lt, L, by
      simpa [theorem32UniformDoubledNestedBisectionOutput] using hcert⟩

/--
Source-optimal Theorem 3.2 calculated-grid endpoint.  The paper states the
input chain as the optimal `M`-level binary rating system; finite Lemma 3.1
turns that optimality premise into the equalized-rate certificate consumed by
the bisection proof.
-/
theorem binaryEndpointAwareAdjacentRateObjective_exists_grid_depth_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_optimal_of_eps_pos
    {m M : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 < eps)
    (hoptimal :
      EconCSLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun levels : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective levels
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        oldLevels) :
    ∃ grid : ℝ,
      0 < grid ∧
      grid <
        ((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2 ∧
      ∃ L : ℕ,
        let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
          uniformDoubledEndpointLevels oldLevels
        let levelTarget : ℝ :=
          optimal
            (adjacentLowIndex
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
        let lastLow : ℝ :=
          (EconCSLib.Optimization.realBisectionRun
            (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
            (L + 1)
            (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
            (1 - grid)).2
        let tFirst : ℝ :=
          optimal
            (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
        let target : ℝ := -Real.log lastLow
        let gridReturned : Fin ((2 * m + 1) + 2) → ℝ :=
          theorem32BackwardGridLowBisectionLevels
            (2 * m + 1) L grid tFirst target lastLow
        let returned : Fin ((2 * m + 1) + 2) → ℝ :=
          if levelTarget = lastLow then optimal else gridReturned
        binaryEndpointAwareAdjacentRateObjective optimal
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
            binaryEndpointAwareAdjacentRateObjective returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
          nestedBisectionOperationCount M (L + 1) L ≤
            EconCSLib.Optimization.nestedBisectionStepBound M L := by
  have holdLevels : BinaryEndpointLevelVector oldLevels := hoptimal.1
  have holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)) :=
    binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn hoptimal
  exact
    binaryEndpointAwareAdjacentRateObjective_exists_grid_depth_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_eps_pos
      (m := m) (M := M) hm oldLevels heps holdLevels holdEq

/--
Source-optimal Theorem 3.2 for the named uniform source-shaped
`NestedBisection` output.  The finite equalized-rate certificate is derived
from finite optimality by Lemma 3.1.
-/
theorem binaryEndpointAwareAdjacentRateObjective_exists_grid_depth_loss_and_runtime_le_of_theorem32_uniform_doubled_nested_bisection_output_of_optimal_of_eps_pos
    {m M : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 < eps)
    (hoptimal :
      EconCSLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun levels : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective levels
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        oldLevels) :
    ∃ grid : ℝ,
      0 < grid ∧
      grid <
        ((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2 ∧
      ∃ L : ℕ,
        binaryEndpointAwareAdjacentRateObjective
            (uniformDoubledEndpointLevels oldLevels)
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
            binaryEndpointAwareAdjacentRateObjective
              (theorem32UniformDoubledNestedBisectionOutput m L oldLevels grid)
              (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
          nestedBisectionOperationCount M (L + 1) L ≤
            EconCSLib.Optimization.nestedBisectionStepBound M L := by
  rcases
    binaryEndpointAwareAdjacentRateObjective_exists_grid_depth_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_early_exact_return_of_optimal_of_eps_pos
      (m := m) (M := M) hm oldLevels heps hoptimal with
    ⟨grid, hgrid_pos, hgrid_lt, L, hcert⟩
  exact
    ⟨grid, hgrid_pos, hgrid_lt, L, by
      simpa [theorem32UniformDoubledNestedBisectionOutput] using hcert⟩

/--
Source-optimal Theorem 3.2 for the named uniform source-shaped
`NestedBisection` output in logarithmic runtime form.  Finite Lemma 3.1
derives the equalized-rate certificate from optimality, and the reusable
bisection runtime lemma reports the operation count as a quadratic in the
chosen logarithmic depth.
-/
theorem binaryEndpointAwareAdjacentRateObjective_exists_grid_log_depth_loss_and_runtime_real_log_quadratic_le_of_theorem32_uniform_doubled_nested_bisection_output_of_optimal_of_eps_pos
    {m M : ℕ} (hm : 0 < m) (hM : 0 < M)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 < eps)
    (hoptimal :
      EconCSLib.Optimization.IsMaximizerOn
        (BinaryEndpointLevelVector : (Fin (m + 2) → ℝ) → Prop)
        (fun levels : Fin (m + 2) → ℝ =>
          binaryEndpointAwareAdjacentRateObjective levels
            (fun _ : Fin (m + 2) => (1 : ℝ)))
        oldLevels) :
    ∃ grid : ℝ,
      0 < grid ∧
      grid <
        ((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2 ∧
      ∃ L : ℕ,
        let sourceDepthBudget : ℝ :=
          max
            (((1 - grid) -
                (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))) / 2)
            1
        let sourceDelta : ℝ :=
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
        let runtimeLog : ℝ :=
          Real.logb 2 (max 1 (sourceDepthBudget / sourceDelta)) + 2
        ((L + 1 : ℕ) : ℝ) ≤ runtimeLog ∧
          binaryEndpointAwareAdjacentRateObjective
              (uniformDoubledEndpointLevels oldLevels)
              (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
              binaryEndpointAwareAdjacentRateObjective
                (theorem32UniformDoubledNestedBisectionOutput m L oldLevels grid)
                (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
            ((nestedBisectionOperationCount M (L + 1) L : ℕ) : ℝ) ≤
              (M : ℝ) * runtimeLog ^ 2 := by
  have holdLevels : BinaryEndpointLevelVector oldLevels := hoptimal.1
  have holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)) :=
    binaryEndpointAwareAdjacentRatesEqualize_uniform_of_isMaximizerOn hoptimal
  exact
    binaryEndpointAwareAdjacentRateObjective_exists_grid_log_depth_loss_and_runtime_real_log_quadratic_le_of_theorem32_uniform_doubled_nested_bisection_output_of_eps_pos
      (m := m) (M := M) hm hM oldLevels heps holdLevels holdEq

/--
Theorem 3.2 runtime Landau bridge.  Any family of named nested-bisection runs
whose operation count satisfies the exact real-valued bound
`runtime ≤ M * runtimeLog^2` is `O(M * runtimeLog^2)`.
-/
theorem theorem32_runtime_isBigO_of_eventually_runtime_real_log_quadratic_le
    {α : Type*} {l : Filter α} {M : ℕ}
    {runtime runtimeLog : α → ℝ}
    (hruntime_nonneg : ∀ᶠ t in l, 0 ≤ runtime t)
    (hruntime_le :
      ∀ᶠ t in l, runtime t ≤ (M : ℝ) * runtimeLog t ^ 2) :
    Asymptotics.IsBigO l runtime
      (fun t : α => (M : ℝ) * runtimeLog t ^ 2) :=
  EconCSLib.Math.isBigO_of_eventually_le_mul_sq
    (C := (M : ℝ)) (by positivity) hruntime_nonneg hruntime_le

/--
Calculated source-grid Theorem 3.2 endpoint with the strict initial
outer-bracket condition derived from the source small-grid condition
`grid < tFirst`.  The visible finite-grid obligations are now the positive
grid, the no-exact outer-midpoint convention, the executable outer return,
the two bisection-depth width bounds, and the runtime step bounds.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_small_grid
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (houterNoExact :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let levelLower0 : ℝ :=
        1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
      let levelTarget : ℝ :=
        optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
      ∀ k : ℕ, k < outerSteps →
        levelTarget ≠
          EconCSLib.Optimization.realBisectionMidpoint
            (EconCSLib.Optimization.realBisectionRun
              (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
              k levelLower0 (1 - grid)).1
            (EconCSLib.Optimization.realBisectionRun
              (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
              k levelLower0 (1 - grid)).2)
    (hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow)
    (hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  have hlevelTarget_lt_one_sub_grid :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) <
        1 - grid := by
    simpa using
      theorem32_calculated_grid_levelTarget_lt_one_sub_grid_of_grid_lt_tFirst
        (m := m) hm oldLevels holdLevels holdEq hgrid_lt_tFirst
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_source_grid
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos
      hlevelTarget_lt_one_sub_grid houterNoExact hlevelWidth hreturnedLast
      hgrid_lt_tFirst hinnerWidth houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint at the source iteration depths.
The outer bisection uses `L + 1` iterations and each inner bisection uses `L`
iterations, so the nested-bisection operation bound is discharged internally.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_small_grid_fixed_depths
    {m M L : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (houterNoExact :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let levelLower0 : ℝ :=
        1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
      let levelTarget : ℝ :=
        optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
      ∀ k : ℕ, k < L + 1 →
        levelTarget ≠
          EconCSLib.Optimization.realBisectionMidpoint
            (EconCSLib.Optimization.realBisectionRun
              (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
              k levelLower0 (1 - grid)).1
            (EconCSLib.Optimization.realBisectionRun
              (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
              k levelLower0 (1 - grid)).2)
    (hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ (L + 1))
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          (L + 1)
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow)
    (hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) L grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M (L + 1) L ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  simpa using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_small_grid
      (m := m) (M := M) (L := L)
      (outerSteps := L + 1) (innerSteps := L)
      hm oldLevels heps holdLevels holdEq hgrid_pos houterNoExact
      hlevelWidth hreturnedLast hgrid_lt_tFirst hinnerWidth
      (Nat.le_refl (L + 1)) (Nat.le_refl L)

/--
Calculated source-grid Theorem 3.2 endpoint at the source iteration depths,
with the internal `grid < tFirst` premise discharged from the C.5/C.7/C.8
objective-rate lower-bound package.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_objective_grid_fixed_depths
    {m M L : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlower_le_one :
      (1 / 5 : ℝ) *
          binaryEndpointAwareAdjacentRateObjective oldLevels
            (fun _ : Fin (m + 2) => (1 : ℝ)) ≤ 1)
    (hgrid_lt_bound :
      grid <
        ((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)
    (houterNoExact :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let levelLower0 : ℝ :=
        1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
      let levelTarget : ℝ :=
        optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
      ∀ k : ℕ, k < L + 1 →
        levelTarget ≠
          EconCSLib.Optimization.realBisectionMidpoint
            (EconCSLib.Optimization.realBisectionRun
              (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
              k levelLower0 (1 - grid)).1
            (EconCSLib.Optimization.realBisectionRun
              (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
              k levelLower0 (1 - grid)).2)
    (hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ (L + 1))
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          (L + 1)
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) L grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M (L + 1) L ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  have hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst := by
    simpa using
      theorem32_calculated_grid_lt_tFirst_of_grid_lt_objective_bound
        (m := m) hm oldLevels holdLevels holdEq hlower_le_one hgrid_lt_bound
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_small_grid_fixed_depths
      (m := m) (M := M) (L := L)
      hm oldLevels heps holdLevels holdEq hgrid_pos houterNoExact
      hlevelWidth hreturnedLast hgrid_lt_tFirst hinnerWidth

/--
Calculated source-grid Theorem 3.2 endpoint at the source iteration depths,
with the C.7 `lower ≤ 1` side condition discharged from the uniform equalized
old chain.  The remaining small-grid input is stated as
`grid < ((1 / 5) * oldObjective) / 2`.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_objective_grid_auto_lower_fixed_depths
    {m M L : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hgrid_lt_bound :
      grid <
        ((1 / 5 : ℝ) *
            binaryEndpointAwareAdjacentRateObjective oldLevels
              (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)
    (houterNoExact :
      let optimal : Fin ((2 * m + 1) + 2) → ℝ :=
        uniformDoubledEndpointLevels oldLevels
      let levelLower0 : ℝ :=
        1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))
      let levelTarget : ℝ :=
        optimal
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
      ∀ k : ℕ, k < L + 1 →
        levelTarget ≠
          EconCSLib.Optimization.realBisectionMidpoint
            (EconCSLib.Optimization.realBisectionRun
              (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
              k levelLower0 (1 - grid)).1
            (EconCSLib.Optimization.realBisectionRun
              (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
              k levelLower0 (1 - grid)).2)
    (hlevelWidth :
      (1 - grid) -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ (L + 1))
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          (L + 1)
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          (1 - grid)).2 = lastLow)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) L grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M (L + 1) L ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_sub_grid_of_no_exact_outer_return_objective_grid_fixed_depths
      (m := m) (M := M) (L := L)
      hm oldLevels heps holdLevels holdEq hgrid_pos
      (BinaryEndpointLevelVector_uniform_equalized_one_fifth_objective_le_one
        hm holdLevels holdEq)
      hgrid_lt_bound houterNoExact hlevelWidth hreturnedLast hinnerWidth

/--
Calculated source-grid Theorem 3.2 endpoint with root placement and
low-endpoint feasibility both derived from source-shaped bisection facts.  In
contrast to
`..._of_floor_rate_grid_upper_rate_width`, this version does not require the
fixed floor to lie below `high - grid`; it only requires the floor to be below
the current high endpoint, the interval `[0, high - grid]` to be nonempty, and
the right endpoint to have rate at most the target.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_floor_high_grid_upper_rate_target_pos_width
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (htarget_pos : 0 < -Real.log lastLow)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 = lastLow)
    (htarget_lt_floor_rate :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst)
    (hfloor_lt_high :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        tFirst < returned (adjacentHighIndex i))
    (hgrid_upper_pos :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        0 < returned (adjacentHighIndex i) - grid)
    (hgrid_upper_rate_le_target :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i))
            (returned (adjacentHighIndex i) - grid) ≤
          target)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  have hoptimalLevels :
      BinaryEndpointLevelVector (uniformDoubledEndpointLevels oldLevels) := by
    simpa using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have htFirst_pos : 0 < tFirst := by
    have hnot_first :
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
          0 := by
      simp [adjacentHighIndex, firstAdjacentIndex]
    simpa [tFirst] using
      BinaryEndpointLevelVector_pos_of_not_first
        hoptimalLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
        hnot_first
  have hhigh_lt_one :
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        returned (adjacentHighIndex i) < 1 := by
    simpa [tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_high_lt_one_of_grid_upper_pos
        (n := 2 * m + 1) (innerSteps := innerSteps)
        grid tFirst target lastLow hgrid_pos hlastLow_lt_one
        (by simpa [tFirst, target, returned] using hgrid_upper_pos)
  have hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target := by
    simpa [tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_feasible_of_floor_lt_high_and_high_lt_one
        (n := 2 * m + 1) (innerSteps := innerSteps)
        grid tFirst target lastLow htFirst_pos
        (by simpa [target] using htarget_pos)
        (by simpa [tFirst, target, returned] using hfloor_lt_high)
        (by simpa [tFirst, target, returned] using hhigh_lt_one)
        (by simpa [tFirst, target, returned] using htarget_lt_floor_rate)
  simpa [tFirst, target, returned] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_feasible_grid_upper_rate_width
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos hlastLow_lt_one
      hlevelWidth hreturnedLast hfeasible hgrid_upper_pos
      hgrid_upper_rate_le_target hinnerWidth houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint with all low-endpoint feasibility,
root placement, and target-positivity facts derived internally from the outer
return and source-shaped inner-loop inequalities.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_floor_high_grid_upper_rate_width
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 = lastLow)
    (htarget_lt_floor_rate :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst)
    (hfloor_lt_high :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        tFirst < returned (adjacentHighIndex i))
    (hgrid_upper_pos :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        0 < returned (adjacentHighIndex i) - grid)
    (hgrid_upper_rate_le_target :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i))
            (returned (adjacentHighIndex i) - grid) ≤
          target)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  have htarget_pos :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let _returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      0 < target := by
    simpa using
      theorem32_calculated_grid_target_pos_of_outer_return
        (m := m) (outerSteps := outerSteps) (innerSteps := innerSteps)
        hm oldLevels (grid := grid) holdLevels holdEq hlastLow_lt_one
        hreturnedLast
  simpa using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_floor_high_grid_upper_rate_target_pos_width
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos hlastLow_lt_one
      (by simpa using htarget_pos)
      hlevelWidth hreturnedLast htarget_lt_floor_rate hfloor_lt_high
      hgrid_upper_pos hgrid_upper_rate_le_target hinnerWidth houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint with the per-interior
`high - grid` rate check derived from the scalar source-grid condition
`lastLow ≤ 1 - grid`.  The remaining inner-loop obligations are the floor-rate
strictness, the floor/high support inequality, and nonempty source-grid
intervals.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_floor_high_grid_width
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (hlastLow_le_one_sub_grid : lastLow ≤ 1 - grid)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 = lastLow)
    (htarget_lt_floor_rate :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst)
    (hfloor_lt_high :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        tFirst < returned (adjacentHighIndex i))
    (hgrid_upper_pos :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        0 < returned (adjacentHighIndex i) - grid)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  have hlastLow_pos : 0 < lastLow :=
    theorem32_calculated_grid_lastLow_pos_of_outer_return
      (m := m) (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels (grid := grid) holdLevels holdEq hreturnedLast
  have hgrid_upper_rate_le_target :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i))
            (returned (adjacentHighIndex i) - grid) ≤
          target := by
    simpa [tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_grid_upper_rate_le_target_of_lastLow_le_one_sub_grid
        (n := 2 * m + 1) (innerSteps := innerSteps)
        grid tFirst lastLow hgrid_pos hlastLow_lt_one hlastLow_pos
        hlastLow_le_one_sub_grid
        (by simpa [tFirst, target, returned] using hgrid_upper_pos)
  simpa [tFirst, target, returned] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_floor_high_grid_upper_rate_width
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos hlastLow_lt_one
      hlevelWidth hreturnedLast htarget_lt_floor_rate hfloor_lt_high
      hgrid_upper_pos hgrid_upper_rate_le_target hinnerWidth houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint with the floor/high support
invariant derived by induction from the scalar source condition
`tFirst < lastLow`.  The remaining per-inner-call assumptions are the
floor-rate strictness and nonempty source-grid intervals.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_lastLow_gt_floor_grid_width
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (hlastLow_le_one_sub_grid : lastLow ≤ 1 - grid)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 = lastLow)
    (htFirst_lt_lastLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      tFirst < lastLow)
    (htarget_lt_floor_rate :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst)
    (hgrid_upper_pos :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        0 < returned (adjacentHighIndex i) - grid)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  have hoptimalLevels :
      BinaryEndpointLevelVector (uniformDoubledEndpointLevels oldLevels) := by
    simpa using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have htFirst_pos : 0 < tFirst := by
    have hnot_first :
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
          0 := by
      simp [adjacentHighIndex, firstAdjacentIndex]
    simpa [tFirst] using
      BinaryEndpointLevelVector_pos_of_not_first
        hoptimalLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
        hnot_first
  have hlastLow_pos : 0 < lastLow :=
    theorem32_calculated_grid_lastLow_pos_of_outer_return
      (m := m) (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels (grid := grid) holdLevels holdEq hreturnedLast
  have hfloor_lt_high :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        tFirst < returned (adjacentHighIndex i) := by
    simpa [tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_floor_lt_high_of_lastLow_gt_floor
        (n := 2 * m + 1) (innerSteps := innerSteps)
        grid tFirst lastLow htFirst_pos hgrid_pos hlastLow_lt_one
        hlastLow_pos hlastLow_le_one_sub_grid
        (by simpa [tFirst] using htFirst_lt_lastLow)
        (by simpa [tFirst, target, returned] using hgrid_upper_pos)
        (by simpa [tFirst, target, returned] using htarget_lt_floor_rate)
  simpa [tFirst, target, returned] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_floor_high_grid_width
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos hlastLow_lt_one
      hlastLow_le_one_sub_grid hlevelWidth hreturnedLast
      htarget_lt_floor_rate hfloor_lt_high hgrid_upper_pos
      hinnerWidth houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint with the source-grid interval
nonemptiness derived from the scalar small-grid condition `grid < tFirst`.
The remaining inner-loop obligation is the source floor-rate strictness.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_lastLow_gt_floor_grid_lt_floor_width
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (hlastLow_le_one_sub_grid : lastLow ≤ 1 - grid)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 = lastLow)
    (htFirst_lt_lastLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      tFirst < lastLow)
    (hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst)
    (htarget_lt_floor_rate :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  have hoptimalLevels :
      BinaryEndpointLevelVector (uniformDoubledEndpointLevels oldLevels) := by
    simpa using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have htFirst_pos : 0 < tFirst := by
    have hnot_first :
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
          0 := by
      simp [adjacentHighIndex, firstAdjacentIndex]
    simpa [tFirst] using
      BinaryEndpointLevelVector_pos_of_not_first
        hoptimalLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
        hnot_first
  have hlastLow_pos : 0 < lastLow :=
    theorem32_calculated_grid_lastLow_pos_of_outer_return
      (m := m) (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels (grid := grid) holdLevels holdEq hreturnedLast
  have hsupport :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      (∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
          tFirst < returned (adjacentHighIndex i)) ∧
        (∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
          0 < returned (adjacentHighIndex i) - grid) := by
    simpa [tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_floor_lt_high_and_grid_upper_pos_of_grid_lt_floor
        (n := 2 * m + 1) (innerSteps := innerSteps)
        grid tFirst lastLow htFirst_pos hgrid_pos
        (by simpa [tFirst] using hgrid_lt_tFirst)
        hlastLow_lt_one hlastLow_pos hlastLow_le_one_sub_grid
        (by simpa [tFirst] using htFirst_lt_lastLow)
        (by simpa [tFirst, target, returned] using htarget_lt_floor_rate)
  have hfloor_lt_high :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        tFirst < returned (adjacentHighIndex i) := by
    exact hsupport.1
  have hgrid_upper_pos :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        0 < returned (adjacentHighIndex i) - grid := by
    exact hsupport.2
  simpa [tFirst, target, returned] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_floor_high_grid_width
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos hlastLow_lt_one
      hlastLow_le_one_sub_grid hlevelWidth hreturnedLast
      htarget_lt_floor_rate hfloor_lt_high hgrid_upper_pos
      hinnerWidth houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint with `tFirst < lastLow` derived
from the outer bisection return.  The visible source-side obligations are now
the scalar grid-gap condition, small-grid condition, floor-rate strictness, and
the standard bisection width/runtime bounds.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_outer_return_grid_lt_floor_width
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlastLow_lt_one : lastLow < 1)
    (hlastLow_le_one_sub_grid : lastLow ≤ 1 - grid)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 = lastLow)
    (hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst)
    (htarget_lt_floor_rate :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  have htFirst_lt_lastLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      tFirst < lastLow := by
    simpa using
      theorem32_calculated_grid_tFirst_lt_lastLow_of_outer_return
        (m := m) (outerSteps := outerSteps)
        hm oldLevels holdLevels holdEq hreturnedLast
  simpa using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_lastLow_gt_floor_grid_lt_floor_width
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos hlastLow_lt_one
      hlastLow_le_one_sub_grid hlevelWidth hreturnedLast
      htFirst_lt_lastLow hgrid_lt_tFirst htarget_lt_floor_rate
      hinnerWidth houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint with `lastLow < 1` derived from
the scalar grid-gap condition `lastLow <= 1 - grid` and `0 < grid`.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_outer_return_grid_gap_width
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlastLow_le_one_sub_grid : lastLow ≤ 1 - grid)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 = lastLow)
    (hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst)
    (htarget_lt_floor_rate :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  have hlastLow_lt_one : lastLow < 1 := by
    linarith
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_outer_return_grid_lt_floor_width
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos hlastLow_lt_one
      hlastLow_le_one_sub_grid hlevelWidth hreturnedLast
      hgrid_lt_tFirst htarget_lt_floor_rate hinnerWidth houter hinner

/--
Calculated source-grid Theorem 3.2 endpoint with the inner floor-rate
strictness recovered from the clipped low-endpoint selector moving strictly
above the common floor.  This is the bisection-selector form of the remaining
inner-loop source obligation.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_outer_return_grid_gap_width_floor_lt_root
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps grid lastLow : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hgrid_pos : 0 < grid)
    (hlastLow_le_one_sub_grid : lastLow ≤ 1 - grid)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 = lastLow)
    (hgrid_lt_tFirst :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      grid < tFirst)
    (hfloor_lt_root :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        tFirst < root i)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ := -Real.log lastLow
    let returned : Fin ((2 * m + 1) + 2) → ℝ :=
      theorem32BackwardGridLowBisectionLevels
        (2 * m + 1) innerSteps grid tFirst target lastLow
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let tFirst : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
  let target : ℝ := -Real.log lastLow
  let returned : Fin ((2 * m + 1) + 2) → ℝ :=
    theorem32BackwardGridLowBisectionLevels
      (2 * m + 1) innerSteps grid tFirst target lastLow
  have hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target := by
    simpa [tFirst, target, returned] using
      theorem32BackwardGridLowBisectionLevels_feasible_of_floor_lt_lowEndpointOfRateOrFloor
        (n := 2 * m + 1) (innerSteps := innerSteps)
        grid tFirst target lastLow
        (by simpa [tFirst, target, returned] using hfloor_lt_root)
  have htarget_lt_floor_rate :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ := -Real.log lastLow
      let returned : Fin ((2 * m + 1) + 2) → ℝ :=
        theorem32BackwardGridLowBisectionLevels
          (2 * m + 1) innerSteps grid tFirst target lastLow
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ) (returned (adjacentHighIndex i)) tFirst := by
    dsimp at hfeasible ⊢
    intro i hi_first hi_last
    simpa [tFirst, target, returned] using
      (hfeasible i hi_first hi_last).htarget_lt_floor
  simpa [tFirst, target, returned] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_calculated_grid_low_bisection_upper_one_of_outer_return_grid_gap_width
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels heps holdLevels holdEq hgrid_pos
      hlastLow_le_one_sub_grid hlevelWidth hreturnedLast
      hgrid_lt_tFirst htarget_lt_floor_rate hinnerWidth houter hinner

/--
Theorem 3.2 inner feasibility constructor.  The reusable low-endpoint inverse
requires a small feasibility certificate; for the source Algorithm 1 proof,
the nontrivial content of that certificate is exactly that the common first
floor is below the current high endpoint and that the target last rate is
below the interior rate evaluated at that floor.
-/
theorem theorem32_inner_lowEndpointTargetFeasible_of_floor_lt_high_and_target_lt_floor_rate
    {m : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hfloor_lt_high :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        tFirst < returned (adjacentHighIndex i))
    (htarget_lt_floor_rate :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i)) tFirst) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    let target : ℝ :=
      binaryEndpointAwareAdjacentRate returned
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
    ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
      WeightedBernoulliLowEndpointTargetFeasible
        (1 : ℝ) (1 : ℝ) tFirst
        (returned (adjacentHighIndex i)) target := by
  intro tFirst target i hi_first hi_last
  have hoptimalLevels :
      BinaryEndpointLevelVector (uniformDoubledEndpointLevels oldLevels) := by
    simpa using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have htFirst0 : 0 < tFirst := by
    have hnot_first :
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))).val ≠
          0 := by
      simp [adjacentHighIndex, firstAdjacentIndex]
    simpa [tFirst] using
      BinaryEndpointLevelVector_pos_of_not_first
        hoptimalLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
        hnot_first
  have hhi_lt_one :
      returned (adjacentHighIndex i) < 1 := by
    have hnot_last : (adjacentHighIndex i).val ≠ (2 * m + 1) + 1 := by
      simp [adjacentHighIndex]
      omega
    exact
      BinaryEndpointLevelVector_lt_one_of_not_last
        hreturnedLevels (adjacentHighIndex i) hnot_last
  have htarget_pos : 0 < target := by
    simpa [target] using
      binaryEndpointAwareAdjacentRate_pos
        (m := 2 * m + 1) (by omega)
        returned (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
        hreturnedLevels
        (by intro j; norm_num) (by intro j; norm_num)
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
  exact
    { hgHi := by norm_num
      hgLo := by norm_num
      hfloor0 := htFirst0
      hfloor_lt_hi := by
        simpa [tFirst] using hfloor_lt_high i hi_first hi_last
      hpHi1 := hhi_lt_one
      htarget_pos := htarget_pos
      htarget_lt_floor := by
        simpa [tFirst, target] using
          htarget_lt_floor_rate i hi_first hi_last }

/--
The source shifting invariant for Theorem 3.2 often gives only the first
returned endpoint lower bound.  Since returned endpoint vectors are strictly
ordered, that lower bound already places the fixed floor below every interior
high endpoint used by `BisectNextLevel`.
-/
theorem theorem32_floor_lt_high_of_first_ge
    {m : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hfirst_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))) :
    let tFirst : ℝ :=
      uniformDoubledEndpointLevels oldLevels
        (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
    ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
      tFirst < returned (adjacentHighIndex i) := by
  intro tFirst i hi_first _hi_last
  have hfirst_to_low :
      returned
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned (adjacentLowIndex i) := by
    exact
      BinaryEndpointLevelVector_mono hreturnedLevels
        (by
          simp [firstAdjacentIndex, adjacentHighIndex, adjacentLowIndex]
          omega)
  have hlow_lt_high :
      returned (adjacentLowIndex i) < returned (adjacentHighIndex i) :=
    hreturnedLevels.2.2 i
  exact lt_of_le_of_lt (hfirst_ge.trans hfirst_to_low) hlow_lt_high

/--
Theorem 3.2 source-lower wrapper with the inner feasibility certificate
expanded into the two source-shaped inequalities used by the shifting
argument.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_low_bisection_runs_from_source_lower_inner_floor_rate
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps levelUpper0 : ℝ}
    (levelAbove : ℝ → Bool)
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelAbove :
      ∀ x,
        levelAbove x = true →
          uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ x)
    (hlevelBelow :
      ∀ x,
        levelAbove x = false →
          x ≤
            uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlevelUpper0 :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ levelUpper0)
    (hlevelWidth :
      levelUpper0 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          levelAbove outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          levelUpper0).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfloor_lt_high :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        tFirst < returned (adjacentHighIndex i))
    (htarget_lt_floor_rate :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i)) tFirst)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (hreturnedLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  have hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target := by
    simpa using
      theorem32_inner_lowEndpointTargetFeasible_of_floor_lt_high_and_target_lt_floor_rate
        (m := m) hm oldLevels returned holdLevels hreturnedLevels
        hfloor_lt_high htarget_lt_floor_rate
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_feasible_low_bisection_runs_from_source_lower_global_width
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned levelAbove heps holdLevels holdEq hreturnedLevels
      hlevelAbove hlevelBelow hlevelUpper0 hlevelWidth hreturnedLast
      hfeasible hinnerWidth hreturnedLow houter hinner

/--
Canonical-threshold, upper-one Theorem 3.2 endpoint with the floor/high
ordering derived from the source first-endpoint lower invariant.  The remaining
inner source invariant is the rate comparison at the fixed floor.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_threshold_run_low_bisection_runs_from_source_lower_inner_floor_rate_upper_one_of_first_ge
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfirst_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (htarget_lt_floor_rate :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i)) tFirst)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (hreturnedLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let levelTarget : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hoptimalLevels :
      BinaryEndpointLevelVector (uniformDoubledEndpointLevels oldLevels) := by
    simpa using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hlevelUpper0 : levelTarget ≤ (1 : ℝ) := by
    simpa [levelTarget] using
      BinaryEndpointLevelVector_le_one hoptimalLevels
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_low_bisection_runs_from_source_lower_inner_floor_rate
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned
      (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
      heps holdLevels holdEq hreturnedLevels
      (by
        intro x hx
        simpa [levelTarget] using
          EconCSLib.Optimization.realBisectionAboveTarget_true hx)
      (by
        intro x hx
        simpa [levelTarget] using
          EconCSLib.Optimization.realBisectionAboveTarget_false hx)
      (by simpa [levelTarget] using hlevelUpper0)
      hlevelWidth (by simpa [levelTarget] using hreturnedLast)
      (theorem32_floor_lt_high_of_first_ge
        (m := m) hm oldLevels returned hreturnedLevels hfirst_ge)
      htarget_lt_floor_rate hinnerWidth hreturnedLow houter hinner

/--
Canonical-threshold, upper-one version of the source-lower feasible-floor
Theorem 3.2 endpoint.  This keeps the inner assumptions in the source proof's
floor-rate form while discharging the outer classifier and upper-bracket
obligations by using threshold bisection on `[1 - 1/(2m+2), 1]`.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_threshold_run_low_bisection_runs_from_source_lower_inner_floor_rate_upper_one_auto_first
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelWidth :
      1 -
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ))) ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ outerSteps)
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps
          (1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))
          1).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfloor_lt_high :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        tFirst < returned (adjacentHighIndex i))
    (htarget_lt_floor_rate :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        target <
          weightedBernoulliClosedThresholdRate
            (1 : ℝ) (1 : ℝ)
            (returned (adjacentHighIndex i)) tFirst)
    (hinnerWidth :
      1 ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹) *
          (2 : ℝ) ^ innerSteps)
    (hreturnedLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let levelTarget : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  have hoptimalLevels :
      BinaryEndpointLevelVector (uniformDoubledEndpointLevels oldLevels) := by
    simpa using uniformDoubledEndpointLevels_isEndpointLevelVector hm holdLevels
  have hlevelUpper0 : levelTarget ≤ (1 : ℝ) := by
    simpa [levelTarget] using
      BinaryEndpointLevelVector_le_one hoptimalLevels
        (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_low_bisection_runs_from_source_lower_inner_floor_rate
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned
      (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
      heps holdLevels holdEq hreturnedLevels
      (by
        intro x hx
        simpa [levelTarget] using
          EconCSLib.Optimization.realBisectionAboveTarget_true hx)
      (by
        intro x hx
        simpa [levelTarget] using
          EconCSLib.Optimization.realBisectionAboveTarget_false hx)
      (by simpa [levelTarget] using hlevelUpper0)
      hlevelWidth
      (by simpa [levelTarget] using hreturnedLast)
      hfloor_lt_high htarget_lt_floor_rate hinnerWidth hreturnedLow
      houter hinner

/--
Canonical-threshold outer-bisection version of the source-initial-bracket
Theorem 3.2 endpoint.  This discharges the outer midpoint-classifier
soundness using `realBisectionAboveTarget`; connecting the paper's
rate-comparison outer predicate to this threshold classifier is the remaining
source-loop invariant.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_threshold_run_feasible_low_bisection_runs_from_zero_to_high
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps levelLower0 levelUpper0 : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hreturnedLevels : BinaryEndpointLevelVector returned)
    (hlevelLower0 :
      levelLower0 ≤
        uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlevelUpper0 :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ levelUpper0)
    (hlevelWidth :
      (levelUpper0 - levelLower0) / (2 : ℝ) ^ outerSteps ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps levelLower0 levelUpper0).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfirst_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlast_ge :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤
        returned
          (adjacentLowIndex (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hfeasible :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        WeightedBernoulliLowEndpointTargetFeasible
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target)
    (hinnerWidth :
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (returned (adjacentHighIndex i) - 0) / (2 : ℝ) ^ innerSteps ≤
          eps /
            ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
              (((1 / 5 : ℝ) *
                  binaryEndpointAwareAdjacentRateObjective oldLevels
                    (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLow :
      let tFirst : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let target : ℝ :=
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin ((2 * m + 1) + 1))
      let root : Fin ((2 * m + 1) + 1) → ℝ := fun i =>
        weightedBernoulliLowEndpointOfRateOrFloor
          (1 : ℝ) (1 : ℝ) tFirst
          (returned (adjacentHighIndex i)) target
      ∀ i : Fin ((2 * m + 1) + 1), i.val ≠ 0 → i.val ≠ 2 * m + 1 →
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget (root i))
          innerSteps 0 (returned (adjacentHighIndex i))).2 =
          returned (adjacentLowIndex i))
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let levelTarget : ℝ :=
    uniformDoubledEndpointLevels oldLevels
      (adjacentLowIndex
        (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
  exact
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_outer_level_run_feasible_low_bisection_runs_from_zero_to_high
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned
      (EconCSLib.Optimization.realBisectionAboveTarget levelTarget)
      heps holdLevels holdEq hreturnedLevels
      (by
        intro x hx
        simpa [levelTarget] using
          EconCSLib.Optimization.realBisectionAboveTarget_true hx)
      (by
        intro x hx
        simpa [levelTarget] using
          EconCSLib.Optimization.realBisectionAboveTarget_false hx)
      hlevelLower0 hlevelUpper0 hlevelWidth
      (by simpa [levelTarget] using hreturnedLast)
      hfirst_ge hlast_ge hfeasible hinnerWidth hreturnedLow
      houter hinner

/--
Theorem 3.2 finite loss/runtime endpoint from canonical executable bisection
runs.  Compared with the raw certificate theorem, this discharges the
outer/inner midpoint-classifier soundness by using the reusable threshold
classifier from `EconCSLib.Foundations.Optimization.Bisection`.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_threshold_runs
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    (returned : Fin ((2 * m + 1) + 2) → ℝ)
    {eps lower0 upper0 : ℝ}
    (rateLower0 rateUpper0 : Fin ((2 * m + 1) + 1) → ℝ)
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hlevelLower0 :
      lower0 ≤
        uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hlevelUpper0 :
      uniformDoubledEndpointLevels oldLevels
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))) ≤ upper0)
    (hlevelWidth :
      (upper0 - lower0) / (2 : ℝ) ^ outerSteps ≤
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹))
    (hreturnedLast :
      (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (uniformDoubledEndpointLevels oldLevels
              (adjacentLowIndex
                (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))))
          outerSteps lower0 upper0).2 =
        returned
          (adjacentLowIndex
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
    (hinnerLower0 :
      ∀ i : Fin ((2 * m + 1) + 1),
        rateLower0 i ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)))
    (hinnerUpper0 :
      ∀ i : Fin ((2 * m + 1) + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin ((2 * m + 1) + 1)) ≤
          rateUpper0 i)
    (hinnerWidth :
      let tFirstStar : ℝ :=
        uniformDoubledEndpointLevels oldLevels
          (adjacentHighIndex (firstAdjacentIndex : Fin ((2 * m + 1) + 1)))
      let delta : ℝ :=
        eps /
          ((1 - 1 / ((((2 * m + 1) + 1 : ℕ) : ℝ)))⁻¹ +
            (((1 / 5 : ℝ) *
                binaryEndpointAwareAdjacentRateObjective oldLevels
                  (fun _ : Fin (m + 2) => (1 : ℝ))) / 2)⁻¹)
      ∀ i : Fin ((2 * m + 1) + 1),
        (rateUpper0 i - rateLower0 i) / (2 : ℝ) ^ innerSteps ≤
          Real.log ((tFirstStar + delta) / tFirstStar))
    (hreturnedRate :
      ∀ i : Fin ((2 * m + 1) + 1),
        (EconCSLib.Optimization.realBisectionRun
          (EconCSLib.Optimization.realBisectionAboveTarget
            (binaryEndpointAwareAdjacentRate returned
              (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ))
              (lastAdjacentIndex : Fin ((2 * m + 1) + 1))))
          innerSteps (rateLower0 i) (rateUpper0 i)).1 =
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  let run :=
    theorem32_run_certificate_of_outer_level_threshold_run_and_inner_rate_threshold_runs
      (m := m) (M := M) (L := L)
      (outerSteps := outerSteps) (innerSteps := innerSteps)
      hm oldLevels returned rateLower0 rateUpper0 holdLevels
      hlevelLower0 hlevelUpper0 hlevelWidth hreturnedLast
      hinnerLower0 hinnerUpper0 hinnerWidth hreturnedRate houter hinner
  simpa [run] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_run_certificate
      (m := m) (M := M) (L := L)
      hm oldLevels returned heps holdLevels holdEq run

/--
Exact-return corollary for the doubled equalized chain: if the returned vector
is the C.5 doubled chain itself, the finite Theorem 3.2 loss/runtime bound
holds with zero recorded bisection steps. This is not the source Algorithm 1
semantics, but it is a closed reference point for the certificate layer.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_uniform_doubled_exact_return
    {m M L : ℕ} (hm : 0 < m)
    (oldLevels : Fin (m + 2) → ℝ)
    {eps : ℝ}
    (heps : 0 ≤ eps)
    (holdLevels : BinaryEndpointLevelVector oldLevels)
    (holdEq :
      BinaryEndpointAwareAdjacentRatesEqualize oldLevels
        (fun _ : Fin (m + 2) => (1 : ℝ))) :
    binaryEndpointAwareAdjacentRateObjective
        (uniformDoubledEndpointLevels oldLevels)
        (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective
          (uniformDoubledEndpointLevels oldLevels)
          (fun _ : Fin ((2 * m + 1) + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M 0 0 ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  simpa [theorem32_uniform_doubled_exact_run_certificate] using
    binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_theorem32_run_certificate
      (m := m) (M := M) (L := L) hm oldLevels
      (uniformDoubledEndpointLevels oldLevels) heps holdLevels holdEq
      (theorem32_uniform_doubled_exact_run_certificate
        (m := m) (M := M) (L := L) hm oldLevels heps holdLevels holdEq)

/--
Uniform-matching Theorem 3.2 run certificate with the first-level lower bound
derived from a lower bound on the optimal equalized objective.
-/
theorem binaryEndpointAwareAdjacentRateObjective_loss_and_runtime_le_of_nested_bisection_uniform_equalized_objective_rate_lower_run
    {m M L outerSteps innerSteps : ℕ} (hm : 0 < m)
    (optimal returned : Fin (m + 2) → ℝ)
    {rateLower tFirstStar delta eps : ℝ}
    (heps : 0 ≤ eps)
    (hrateLower_pos : 0 < rateLower)
    (hrateLower_le_one : rateLower ≤ 1)
    (hoptimal_levels : BinaryEndpointLevelVector optimal)
    (heq :
      BinaryEndpointAwareAdjacentRatesEqualize optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)))
    (htFirstStar :
      tFirstStar =
        optimal (adjacentHighIndex (firstAdjacentIndex : Fin (m + 1))))
    (hrateLower_le_objective :
      rateLower ≤
        binaryEndpointAwareAdjacentRateObjective optimal
          (fun _ : Fin (m + 2) => (1 : ℝ)))
    (hdelta :
      delta =
        eps /
          ((1 - 1 / ((m + 1 : ℕ) : ℝ))⁻¹ + (rateLower / 2)⁻¹))
    (hlast :
      binaryEndpointAwareAdjacentRate optimal
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)) -
          Real.log
            ((optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1))) +
                  delta) /
              optimal (adjacentLowIndex (lastAdjacentIndex : Fin (m + 1)))) ≤
        binaryEndpointAwareAdjacentRate returned
          (fun _ : Fin (m + 2) => (1 : ℝ))
          (lastAdjacentIndex : Fin (m + 1)))
    (hgrid :
      ∀ i : Fin (m + 1),
        binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ))
            (lastAdjacentIndex : Fin (m + 1)) -
            Real.log ((tFirstStar + delta) / tFirstStar) ≤
          binaryEndpointAwareAdjacentRate returned
            (fun _ : Fin (m + 2) => (1 : ℝ)) i)
    (houter : outerSteps ≤ L + 1)
    (hinner : innerSteps ≤ L) :
    binaryEndpointAwareAdjacentRateObjective optimal
        (fun _ : Fin (m + 2) => (1 : ℝ)) -
        binaryEndpointAwareAdjacentRateObjective returned
          (fun _ : Fin (m + 2) => (1 : ℝ)) ≤ eps ∧
      nestedBisectionOperationCount M outerSteps innerSteps ≤
        EconCSLib.Optimization.nestedBisectionStepBound M L := by
  constructor
  · exact
      binaryEndpointAwareAdjacentRateObjective_loss_le_of_nested_bisection_uniform_equalized_objective_rate_lower
        hm optimal returned heps hrateLower_pos hrateLower_le_one
        hoptimal_levels heq htFirstStar hrateLower_le_objective hdelta hlast
        hgrid
  · exact nestedBisectionOperationCount_le_stepBound houter hinner

end

end GJ19OptimalBinaryRatingSystems
