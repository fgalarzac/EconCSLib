import PRPKG24AccuracyDiversity.GeneralRounding
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Appendix D.1(iv): exact power benchmark

This module records a direct, certificate-free benchmark for the positive-power
branch of Appendix D.1.  It is deliberately an exact-power result, not a
claim that the paper's asymptotic hypotheses have already been lifted through
the integer optimizer.  The key analytic step is proved from Holder's
inequality rather than accepted as a limiting-objective premise.
-/

open scoped BigOperators

namespace PRPKG24AccuracyDiversity
namespace AppendixD1GenericPower

/-- The positive-power continuous objective with target weights `w`. -/
noncomputable def weightedPowerObjective
    {κ : Type*} [Fintype κ] (w : κ -> ℝ) (sigma : ℝ) (x : κ -> ℝ) : ℝ :=
  ∑ i, w i ^ (1 - sigma) * x i ^ sigma

/-- The normalizer of positive target weights. -/
noncomputable def weightSum {κ : Type*} [Fintype κ] (w : κ -> ℝ) : ℝ :=
  ∑ i, w i

/-- The normalized target share associated with strictly positive weights. -/
noncomputable def targetShare {κ : Type*} [Fintype κ]
    (w : κ -> ℝ) (i : κ) : ℝ := w i / weightSum w

theorem weightSum_pos
    {κ : Type*} [Fintype κ] [Nonempty κ] (w : κ -> ℝ)
    (hw_pos : ∀ i, 0 < w i) :
    0 < weightSum w := by
  unfold weightSum
  exact Finset.sum_pos (fun i _ => hw_pos i) Finset.univ_nonempty

theorem targetShare_pos
    {κ : Type*} [Fintype κ] [Nonempty κ] (w : κ -> ℝ)
    (hw_pos : ∀ i, 0 < w i) (i : κ) :
    0 < targetShare w i :=
  div_pos (hw_pos i) (weightSum_pos w hw_pos)

theorem sum_targetShare_eq_one
    {κ : Type*} [Fintype κ] [Nonempty κ] (w : κ -> ℝ)
    (hw_pos : ∀ i, 0 < w i) :
    (∑ i, targetShare w i) = 1 := by
  have hsum_ne : weightSum w ≠ 0 := ne_of_gt (weightSum_pos w hw_pos)
  unfold targetShare
  rw [← Finset.sum_div]
  change weightSum w / weightSum w = 1
  field_simp

/-- The Holder bound is attained at the normalized weight profile. -/
theorem weightedPowerObjective_target
    {κ : Type*} [Fintype κ] [Nonempty κ] (w : κ -> ℝ)
    {sigma N : ℝ} (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (hw_pos : ∀ i, 0 < w i) (hN_nonneg : 0 ≤ N) :
    weightedPowerObjective w sigma (fun i => N * targetShare w i) =
      weightSum w ^ (1 - sigma) * N ^ sigma := by
  have hW_pos : 0 < weightSum w := weightSum_pos w hw_pos
  have hW_ne : weightSum w ≠ 0 := ne_of_gt hW_pos
  have hWpow_ne : weightSum w ^ sigma ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hW_pos sigma)
  have hWfactor : weightSum w =
      weightSum w ^ (1 - sigma) * weightSum w ^ sigma := by
    calc
      weightSum w = weightSum w ^ 1 := (Real.rpow_one _).symm
      _ = weightSum w ^ ((1 - sigma) + sigma) := by
        congr 1
        ring
      _ = weightSum w ^ (1 - sigma) * weightSum w ^ sigma :=
        Real.rpow_add hW_pos (1 - sigma) sigma
  calc
    weightedPowerObjective w sigma (fun i => N * targetShare w i) =
        ∑ i, (N ^ sigma / weightSum w ^ sigma) * w i := by
      unfold weightedPowerObjective targetShare
      refine Finset.sum_congr rfl ?_
      intro i _
      have hwi_factor : w i = w i ^ (1 - sigma) * w i ^ sigma := by
        calc
          w i = w i ^ 1 := (Real.rpow_one _).symm
          _ = w i ^ ((1 - sigma) + sigma) := by
            congr 1
            ring
          _ = w i ^ (1 - sigma) * w i ^ sigma :=
            Real.rpow_add (hw_pos i) (1 - sigma) sigma
      rw [Real.mul_rpow hN_nonneg
        (div_nonneg (hw_pos i).le hW_pos.le)]
      rw [Real.div_rpow (hw_pos i).le hW_pos.le]
      calc
        w i ^ (1 - sigma) * (N ^ sigma *
            (w i ^ sigma / weightSum w ^ sigma)) =
            (N ^ sigma / weightSum w ^ sigma) *
              (w i ^ (1 - sigma) * w i ^ sigma) := by ring
        _ = (N ^ sigma / weightSum w ^ sigma) * w i := by
          rw [← hwi_factor]
    _ = (N ^ sigma / weightSum w ^ sigma) * weightSum w := by
      unfold weightSum
      rw [Finset.mul_sum]
    _ = weightSum w ^ (1 - sigma) * N ^ sigma := by
      calc
        (N ^ sigma / weightSum w ^ sigma) * weightSum w =
            (N ^ sigma / weightSum w ^ sigma) *
              (weightSum w ^ (1 - sigma) * weightSum w ^ sigma) :=
          congrArg (fun z => (N ^ sigma / weightSum w ^ sigma) * z) hWfactor
        _ = weightSum w ^ (1 - sigma) * N ^ sigma := by
          field_simp

theorem target_nonneg
    {κ : Type*} [Fintype κ] [Nonempty κ] (w : κ -> ℝ) {N : ℝ}
    (hw_pos : ∀ i, 0 < w i) (hN_nonneg : 0 ≤ N) (i : κ) :
    0 ≤ N * targetShare w i :=
  mul_nonneg hN_nonneg (targetShare_pos w hw_pos i).le

theorem sum_target_allocation_eq
    {κ : Type*} [Fintype κ] [Nonempty κ] (w : κ -> ℝ) (N : ℝ)
    (hw_pos : ∀ i, 0 < w i) :
    (∑ i, N * targetShare w i) = N := by
  rw [← Finset.mul_sum, sum_targetShare_eq_one w hw_pos, mul_one]

/--
Holder gives the exact continuous upper bound behind the corrected
positive-power Appendix-D.1 target.  No optimization or convergence
certificate is an input: the conclusion follows from the displayed weights,
the exponent, and the fixed total alone.
-/
theorem weightedPowerObjective_le
    {κ : Type*} [Fintype κ] (w x : κ -> ℝ) {sigma N : ℝ}
    (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (hw_pos : ∀ i, 0 < w i) (hx_nonneg : ∀ i, 0 ≤ x i)
    (hx_sum : (∑ i, x i) = N) :
    weightedPowerObjective w sigma x ≤
      weightSum w ^ (1 - sigma) * N ^ sigma := by
  let q : ℝ := 1 / sigma
  have hq_one_lt : 1 < q := by
    dsimp [q]
    exact (one_lt_div hsigma_pos).2 hsigma_lt_one
  have hq : 1 ≤ q := hq_one_lt.le
  have hq_inv : q⁻¹ = sigma := by
    dsimp [q]
    field_simp [ne_of_gt hsigma_pos]
  have hpow : ∀ i, ((x i / w i) ^ sigma) ^ q = x i / w i := by
    intro i
    rw [← Real.rpow_mul (div_nonneg (hx_nonneg i) (hw_pos i).le)]
    have hmul : sigma * q = 1 := by
      dsimp [q]
      field_simp [ne_of_gt hsigma_pos]
    rw [hmul, Real.rpow_one]
  have hscaled_sum : ∑ i, w i * (x i / w i) = N := by
    calc
      ∑ i, w i * (x i / w i) = ∑ i, x i := by
        refine Finset.sum_congr rfl ?_
        intro i _
        field_simp [ne_of_gt (hw_pos i)]
      _ = N := hx_sum
  have hinner_pow : ∑ i, w i * (((x i / w i) ^ sigma) ^ q) = N := by
    calc
      ∑ i, w i * (((x i / w i) ^ sigma) ^ q) =
          ∑ i, w i * (x i / w i) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hpow]
      _ = N := hscaled_sum
  have hleft : ∑ i, w i * (x i / w i) ^ sigma =
      weightedPowerObjective w sigma x := by
    unfold weightedPowerObjective
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Real.div_rpow (hx_nonneg i) (hw_pos i).le]
    have hfactor : w i = w i ^ (1 - sigma) * w i ^ sigma := by
      calc
        w i = w i ^ 1 := (Real.rpow_one _).symm
        _ = w i ^ ((1 - sigma) + sigma) := by
          congr 1
          ring
        _ = w i ^ (1 - sigma) * w i ^ sigma :=
          Real.rpow_add (hw_pos i) (1 - sigma) sigma
    calc
      w i * (x i ^ sigma / w i ^ sigma) =
          (w i ^ (1 - sigma) * w i ^ sigma) *
            (x i ^ sigma / w i ^ sigma) :=
        congrArg (fun z => z * (x i ^ sigma / w i ^ sigma)) hfactor
      _ = w i ^ (1 - sigma) * x i ^ sigma := by
        field_simp [ne_of_gt (Real.rpow_pos_of_pos (hw_pos i) sigma)]
  have hholder := Real.inner_le_weight_mul_Lp_of_nonneg
    (s := Finset.univ) (p := q) hq w (fun i => (x i / w i) ^ sigma)
    (fun i => (hw_pos i).le)
    (fun i => Real.rpow_nonneg (div_nonneg (hx_nonneg i) (hw_pos i).le) sigma)
  calc
    weightedPowerObjective w sigma x = ∑ i, w i * (x i / w i) ^ sigma := hleft.symm
    _ ≤ (∑ i, w i) ^ (1 - q⁻¹) *
        (∑ i, w i * (((x i / w i) ^ sigma) ^ q)) ^ q⁻¹ := by
      simpa using hholder
    _ = weightSum w ^ (1 - sigma) * N ^ sigma := by
      rw [hinner_pow, hq_inv]
      rfl

/--
The explicit normalized weight vector is the real fixed-total maximizer of
the exact positive-power objective.
-/
theorem weightedPowerObjective_target_maximizes
    {κ : Type*} [Fintype κ] [Nonempty κ] (w : κ -> ℝ)
    {sigma N : ℝ} (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (hw_pos : ∀ i, 0 < w i) (z : κ -> ℝ)
    (hz_nonneg : ∀ i, 0 ≤ z i) (hz_sum : (∑ i, z i) = N) :
    weightedPowerObjective w sigma z ≤
      weightedPowerObjective w sigma (fun i => N * targetShare w i) := by
  have hN_nonneg : 0 ≤ N := by
    rw [← hz_sum]
    exact Finset.sum_nonneg fun i _ => hz_nonneg i
  calc
    weightedPowerObjective w sigma z ≤
        weightSum w ^ (1 - sigma) * N ^ sigma :=
      weightedPowerObjective_le w z hsigma_pos hsigma_lt_one hw_pos hz_nonneg hz_sum
    _ = weightedPowerObjective w sigma (fun i => N * targetShare w i) :=
      (weightedPowerObjective_target w hsigma_pos hsigma_lt_one hw_pos hN_nonneg).symm

theorem weightedPowerCoordinate_strictConcaveOn
    {κ : Type*} (w : κ -> ℝ) (i : κ) {sigma : ℝ}
    (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (hw_pos : 0 < w i) :
    StrictConcaveOn ℝ (Set.Ici 0)
      (fun z : ℝ => w i ^ (1 - sigma) * z ^ sigma) := by
  let c : ℝ := w i ^ (1 - sigma)
  have hc_pos : 0 < c := Real.rpow_pos_of_pos hw_pos (1 - sigma)
  have hbase : StrictConcaveOn ℝ (Set.Ici 0) (fun z : ℝ => z ^ sigma) :=
    Real.strictConcaveOn_rpow hsigma_pos hsigma_lt_one
  refine ⟨hbase.1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hstrict := hbase.2 hx hy hxy ha hb hab
  have hscaled := mul_lt_mul_of_pos_left hstrict hc_pos
  convert hscaled using 1
  · simp [c, smul_eq_mul]
    ring_nf

/--
Exact-power integer maximizers lie in the strict rounding window around the
corrected Lemma-D.1(iv) profile.  This is a direct finite optimization result:
the only optimality premise is the literal fixed-total integer objective.
-/
theorem exactPower_integer_maximizer_rounding_window
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (w : κ -> ℝ) {sigma : ℝ} (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1) (hw_pos : ∀ i, 0 < w i)
    (N : ℕ) (a : κ -> ℕ)
    (ha_sum : (∑ i, a i) = N)
    (ha_opt : ∀ b : κ -> ℕ, (∑ i, b i) = N ->
      weightedPowerObjective w sigma (fun i => (b i : ℝ)) ≤
        weightedPowerObjective w sigma (fun i => (a i : ℝ))) :
    ∀ t : κ,
      ⌊(N : ℝ) * targetShare w t⌋₊ < a t + Fintype.card κ ∧
        a t < ⌊(N : ℝ) * targetShare w t⌋₊ + Fintype.card κ := by
  let x : κ -> ℝ := fun i => (N : ℝ) * targetShare w i
  let g : κ -> ℝ -> ℝ := fun i z => w i ^ (1 - sigma) * z ^ sigma
  have hN_nonneg : 0 ≤ (N : ℝ) := by positivity
  have hx_nonneg : ∀ i, 0 ≤ x i := by
    intro i
    exact target_nonneg w hw_pos hN_nonneg i
  have hx_sum : (∑ i, x i) = (N : ℝ) := by
    exact sum_target_allocation_eq w (N : ℝ) hw_pos
  have hx_opt : ∀ z : κ -> ℝ,
      (∀ i, 0 ≤ z i) -> (∑ i, z i) = (N : ℝ) ->
        GeneralRounding.objective g z ≤ GeneralRounding.objective g x := by
    intro z hz_nonneg hz_sum
    have hmax := weightedPowerObjective_target_maximizes
      w hsigma_pos hsigma_lt_one hw_pos z hz_nonneg hz_sum
    simpa [GeneralRounding.objective, weightedPowerObjective, g, x] using hmax
  have hconc : ∀ i, StrictConcaveOn ℝ (Set.Ici 0) (g i) := by
    intro i
    exact weightedPowerCoordinate_strictConcaveOn w i hsigma_pos hsigma_lt_one (hw_pos i)
  have ha_opt' : ∀ b : κ -> ℕ, (∑ i, b i) = N ->
      GeneralRounding.objective g (fun i => (b i : ℝ)) ≤
        GeneralRounding.objective g (fun i => (a i : ℝ)) := by
    intro b hb
    have h := ha_opt b hb
    simpa [GeneralRounding.objective, weightedPowerObjective, g] using h
  simpa [x] using
    GeneralRounding.floor_count_close_of_strictConcave_maximizers
      g N x a hconc hx_nonneg hx_sum hx_opt ha_sum ha_opt'

/-- The source weight corresponding to the corrected D.1(iv) power profile. -/
noncomputable def sourcePowerWeight
    {κ : Type*} (p : κ -> ℝ) (sigma : ℝ) (i : κ) : ℝ :=
  p i ^ (1 / (1 - sigma))

/-- The exact positive-power source objective, with a common positive scale removed. -/
noncomputable def sourcePowerObjective
    {κ : Type*} [Fintype κ] (p : κ -> ℝ) (sigma : ℝ) (x : κ -> ℝ) : ℝ :=
  ∑ i, p i * x i ^ sigma

theorem sourcePowerWeight_pos
    {κ : Type*} (p : κ -> ℝ) {sigma : ℝ}
    (hsigma_lt_one : sigma < 1) (hp_pos : ∀ i, 0 < p i) (i : κ) :
    0 < sourcePowerWeight p sigma i := by
  unfold sourcePowerWeight
  exact Real.rpow_pos_of_pos (hp_pos i) _

theorem sourcePowerWeight_power_eq
    {κ : Type*} (p : κ -> ℝ) {sigma : ℝ}
    (hsigma_lt_one : sigma < 1) (hp_pos : ∀ i, 0 < p i) (i : κ) :
    sourcePowerWeight p sigma i ^ (1 - sigma) = p i := by
  have hexp_ne : 1 - sigma ≠ 0 := ne_of_gt (sub_pos.mpr hsigma_lt_one)
  simpa [sourcePowerWeight, one_div] using
    Real.rpow_inv_rpow (le_of_lt (hp_pos i)) hexp_ne

theorem sourcePowerObjective_eq_weightedPowerObjective
    {κ : Type*} [Fintype κ] (p : κ -> ℝ) {sigma : ℝ}
    (hsigma_lt_one : sigma < 1) (hp_pos : ∀ i, 0 < p i) (x : κ -> ℝ) :
    sourcePowerObjective p sigma x =
      weightedPowerObjective (sourcePowerWeight p sigma) sigma x := by
  unfold sourcePowerObjective weightedPowerObjective
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [sourcePowerWeight_power_eq p hsigma_lt_one hp_pos i]

/--
Exact corrected D.1(iv) route in the paper's `p_i` notation.

For `h(a) = B * a^sigma` with a common `B > 0`, positive `p_i`, and
`0 < sigma < 1`, the literal integer maximizers are in the finite rounding
window around shares proportional to `p_i^(1 / (1 - sigma))`.  The hypothesis
is the raw fixed-total objective; it is not a limiting-objective or FOC
certificate.
-/
theorem lemmaD1_iv_exactPower_integer_maximizer_rounding_window
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (p : κ -> ℝ) {sigma : ℝ} (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1) (hp_pos : ∀ i, 0 < p i)
    (N : ℕ) (a : κ -> ℕ)
    (ha_sum : (∑ i, a i) = N)
    (ha_opt : ∀ b : κ -> ℕ, (∑ i, b i) = N ->
      sourcePowerObjective p sigma (fun i => (b i : ℝ)) ≤
        sourcePowerObjective p sigma (fun i => (a i : ℝ))) :
    ∀ t : κ,
      ⌊(N : ℝ) * targetShare (sourcePowerWeight p sigma) t⌋₊ <
          a t + Fintype.card κ ∧
        a t < ⌊(N : ℝ) * targetShare (sourcePowerWeight p sigma) t⌋₊ +
          Fintype.card κ := by
  have hw_pos : ∀ i, 0 < sourcePowerWeight p sigma i :=
    fun i => sourcePowerWeight_pos p hsigma_lt_one hp_pos i
  have ha_opt' : ∀ b : κ -> ℕ, (∑ i, b i) = N ->
      weightedPowerObjective (sourcePowerWeight p sigma) sigma
          (fun i => (b i : ℝ)) ≤
        weightedPowerObjective (sourcePowerWeight p sigma) sigma
          (fun i => (a i : ℝ)) := by
    intro b hb
    have h := ha_opt b hb
    have hleft := sourcePowerObjective_eq_weightedPowerObjective
      p hsigma_lt_one hp_pos (fun i => (b i : ℝ))
    have hright := sourcePowerObjective_eq_weightedPowerObjective
      p hsigma_lt_one hp_pos (fun i => (a i : ℝ))
    rw [hleft, hright] at h
    exact h
  exact exactPower_integer_maximizer_rounding_window
    (sourcePowerWeight p sigma) hsigma_pos hsigma_lt_one hw_pos N a ha_sum ha_opt'

end AppendixD1GenericPower
end PRPKG24AccuracyDiversity
