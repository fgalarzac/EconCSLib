import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import EconCSLib.Foundations.Math.ExponentialBounds
import EconCSLib.Foundations.Math.LinearCompressedSensing
import EconCSLib.Foundations.Probability.FairCoin
import EconCSLib.Foundations.Probability.MeasureInequalities

/-!
# Scaled Rademacher Matrices

Reusable probability and deterministic wrappers for matrices with independent
entries in `{-1/sqrt d, 1/sqrt d}`.  These are the random incoherent matrix
constructions used by LRH-style linear compressed-sensing arguments.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace EconCSLib
namespace Probability
namespace RademacherMatrix

open EconCSLib.Math.LinearCompressedSensing

variable {Feature Coord : Type*}

/-- The symmetric Rademacher sign encoded by a Boolean. -/
def rademacherSign (b : Bool) : ℝ :=
  if b then 1 else -1

@[simp] theorem rademacherSign_sq (b : Bool) :
    rademacherSign b ^ 2 = (1 : ℝ) := by
  cases b <;> simp [rademacherSign]

@[simp] theorem rademacherSign_mul_self (b : Bool) :
    rademacherSign b * rademacherSign b = (1 : ℝ) := by
  simpa [pow_two] using rademacherSign_sq b

@[simp] theorem abs_rademacherSign (b : Bool) :
    |rademacherSign b| = (1 : ℝ) := by
  cases b <;> simp [rademacherSign]

/-- Product sign from two feature coordinates in a sampled row. -/
def pairSign (row : Feature → Bool) (i j : Feature) : ℝ :=
  rademacherSign (row i) * rademacherSign (row j)

@[simp] theorem pairSign_mem_Icc (row : Feature → Bool) (i j : Feature) :
    pairSign row i j ∈ Set.Icc (-1 : ℝ) 1 := by
  dsimp [pairSign]
  cases row i <;> cases row j <;> norm_num [rademacherSign]

/--
Row-product fair-coin law for a random `Coord × Feature` Boolean matrix.
Rows are sampled independently, and each row is a fair Boolean vector over
features.
-/
noncomputable def rowsMeasure (Feature Coord : Type*) :
    Measure (Coord → Feature → Bool) :=
  Measure.infinitePi fun _ : Coord => FairCoin.productMeasure Feature

theorem rowsMeasure_isProbabilityMeasure (Feature Coord : Type*) :
    IsProbabilityMeasure (rowsMeasure Feature Coord) := by
  let P : Coord → Measure (Feature → Bool) :=
    fun _ => FairCoin.productMeasure Feature
  let hP : ∀ r : Coord, IsProbabilityMeasure (P r) := by
    intro r
    simpa [P] using FairCoin.productMeasure_isProbabilityMeasure Feature
  simpa [rowsMeasure, P] using
    @MeasureTheory.Measure.instIsProbabilityMeasureForallInfinitePi
      (ι := Coord) (X := fun _ : Coord => Feature → Bool)
      (mX := fun _ => by infer_instance) (μ := P) hP

/-- The fair Boolean coordinates of one sampled row are independent. -/
theorem boolCoord_iIndepFun (Feature : Type*) :
    iIndepFun (fun i (row : Feature → Bool) => row i)
      (FairCoin.productMeasure Feature) := by
  let P : Feature → Measure Bool := fun _ => FairCoin.fairMeasure
  let hP : ∀ i : Feature, IsProbabilityMeasure (P i) := by
    intro i
    simpa [P] using FairCoin.fairMeasure_isProbabilityMeasure
  simpa [FairCoin.productMeasure, P] using
    @ProbabilityTheory.iIndepFun_infinitePi
      (ι := Feature) (𝓧 := fun _ : Feature => Bool)
      (m𝓧 := fun _ => by infer_instance)
      (Ω := fun _ : Feature => Bool) (mΩ := fun _ => by infer_instance)
      (P := P) hP (X := fun _ : Feature => id)
      (mX := fun _ => measurable_id)

/-- A single fair Rademacher sign has mean zero. -/
theorem integral_rademacherSign_fairMeasure :
    (∫ b : Bool, rademacherSign b ∂FairCoin.fairMeasure) = 0 := by
  simp [rademacherSign, FairCoin.fairMeasure, PMF.integral_eq_sum, PMF.bernoulli]

/-- A fair-product Boolean coordinate, mapped to a Rademacher sign, has mean zero. -/
theorem integral_rademacherSign_productMeasure
    (Feature : Type*) (i : Feature) :
    (∫ row : Feature → Bool,
        rademacherSign (row i) ∂FairCoin.productMeasure Feature) = 0 := by
  let P : Feature → Measure Bool := fun _ => FairCoin.fairMeasure
  let hP : ∀ i : Feature, IsProbabilityMeasure (P i) := by
    intro i
    simpa [P] using FairCoin.fairMeasure_isProbabilityMeasure
  let f : Bool → ℝ := rademacherSign
  have hf :
      AEStronglyMeasurable f
        (Measure.map (fun row : Feature → Bool => row i)
          (FairCoin.productMeasure Feature)) :=
    (measurable_of_finite f).aestronglyMeasurable
  calc
    (∫ row : Feature → Bool,
        rademacherSign (row i) ∂FairCoin.productMeasure Feature)
        = ∫ row : Feature → Bool, f (row i) ∂FairCoin.productMeasure Feature := by
          rfl
    _ = ∫ b : Bool, f b ∂Measure.map
          (fun row : Feature → Bool => row i)
          (FairCoin.productMeasure Feature) := by
          exact (integral_map
            (μ := FairCoin.productMeasure Feature)
            (φ := fun row : Feature → Bool => row i)
            (f := f) (measurable_pi_apply i).aemeasurable hf).symm
    _ = ∫ b : Bool, f b ∂FairCoin.fairMeasure := by
          rw [show
              Measure.map (fun row : Feature → Bool => row i)
                  (FairCoin.productMeasure Feature) =
                FairCoin.fairMeasure from by
              simpa [FairCoin.productMeasure, P] using
                (@MeasureTheory.Measure.infinitePi_map_eval
                  (ι := Feature) (X := fun _ : Feature => Bool)
                  (mX := fun _ => by infer_instance) (μ := P) hP i)]
    _ = 0 := integral_rademacherSign_fairMeasure

/-- Product signs from two distinct fair-product Boolean coordinates have mean zero. -/
theorem integral_pairSign_productMeasure
    [Fintype Feature] {i j : Feature} (hij : i ≠ j) :
    (∫ row : Feature → Bool,
        pairSign row i j ∂FairCoin.productMeasure Feature) = 0 := by
  have hcoord := boolCoord_iIndepFun Feature
  have hindep :
      (fun row : Feature → Bool => row i) ⟂ᵢ[FairCoin.productMeasure Feature]
        (fun row : Feature → Bool => row j) :=
    hcoord.indepFun hij
  have hX : AEMeasurable (fun row : Feature → Bool => row i)
      (FairCoin.productMeasure Feature) :=
    (measurable_pi_apply i).aemeasurable
  have hY : AEMeasurable (fun row : Feature → Bool => row j)
      (FairCoin.productMeasure Feature) :=
    (measurable_pi_apply j).aemeasurable
  have hf :
      AEStronglyMeasurable rademacherSign
        (Measure.map (fun row : Feature → Bool => row i)
          (FairCoin.productMeasure Feature)) :=
    (measurable_of_finite rademacherSign).aestronglyMeasurable
  have hg :
      AEStronglyMeasurable rademacherSign
        (Measure.map (fun row : Feature → Bool => row j)
          (FairCoin.productMeasure Feature)) :=
    (measurable_of_finite rademacherSign).aestronglyMeasurable
  have hmul :=
    hindep.integral_fun_comp_mul_comp hX hY hf hg
  rw [integral_rademacherSign_productMeasure Feature i,
    integral_rademacherSign_productMeasure Feature j] at hmul
  simpa [pairSign] using hmul

/-- Each row-product sign has mean zero under the row-product matrix law. -/
theorem integral_pairSign_rowsMeasure
    [Fintype Feature] {i j : Feature} (hij : i ≠ j) (r : Coord) :
    (∫ ω : Coord → Feature → Bool,
        pairSign (ω r) i j ∂rowsMeasure Feature Coord) = 0 := by
  let P : Coord → Measure (Feature → Bool) :=
    fun _ => FairCoin.productMeasure Feature
  let hP : ∀ r : Coord, IsProbabilityMeasure (P r) := by
    intro r
    simpa [P] using FairCoin.productMeasure_isProbabilityMeasure Feature
  let f : (Feature → Bool) → ℝ := fun row => pairSign row i j
  have hf :
      AEStronglyMeasurable f
        (Measure.map (fun ω : Coord → Feature → Bool => ω r)
          (rowsMeasure Feature Coord)) :=
    (measurable_of_finite f).aestronglyMeasurable
  calc
    (∫ ω : Coord → Feature → Bool,
        pairSign (ω r) i j ∂rowsMeasure Feature Coord)
        = ∫ row : Feature → Bool, f row ∂Measure.map
          (fun ω : Coord → Feature → Bool => ω r)
          (rowsMeasure Feature Coord) := by
          exact (integral_map
            (μ := rowsMeasure Feature Coord)
            (φ := fun ω : Coord → Feature → Bool => ω r)
            (f := f) (measurable_pi_apply r).aemeasurable hf).symm
    _ = ∫ row : Feature → Bool, f row ∂FairCoin.productMeasure Feature := by
          rw [show
              Measure.map (fun ω : Coord → Feature → Bool => ω r)
                  (rowsMeasure Feature Coord) =
                FairCoin.productMeasure Feature from by
              simpa [rowsMeasure, P] using
                (@MeasureTheory.Measure.infinitePi_map_eval
                  (ι := Coord) (X := fun _ : Coord => Feature → Bool)
                  (mX := fun _ => by infer_instance) (μ := P) hP r)]
    _ = 0 := integral_pairSign_productMeasure (Feature := Feature) hij

/-- A scaled Rademacher matrix, with columns indexed by `Feature`. -/
noncomputable def scaledMatrix [Fintype Coord]
    (ω : Coord → Feature → Bool) : Feature → Coord → ℝ :=
  fun j r =>
    (Real.sqrt (Fintype.card Coord : ℝ))⁻¹ * rademacherSign (ω r j)

/-- Every scaled Rademacher column has squared norm one when `Coord` is nonempty. -/
theorem inner_scaledMatrix_self [Fintype Coord]
    (hd : 0 < Fintype.card Coord) (ω : Coord → Feature → Bool)
    (i : Feature) :
    inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
      (scaledMatrix (Feature := Feature) (Coord := Coord) ω i) = 1 := by
  classical
  let dR : ℝ := Fintype.card Coord
  have hdR_pos : 0 < dR := by
    dsimp [dR]
    exact_mod_cast hd
  have hsqrt_sq : (Real.sqrt dR) ^ 2 = dR := by
    exact Real.sq_sqrt (le_of_lt hdR_pos)
  have hsqrt_ne : Real.sqrt dR ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.mpr hdR_pos)
  calc
    inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
        (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
        = ∑ r : Coord,
            ((Real.sqrt dR)⁻¹ * rademacherSign (ω r i)) *
              ((Real.sqrt dR)⁻¹ * rademacherSign (ω r i)) := by
          simp [EconCSLib.Math.LinearCompressedSensing.inner, scaledMatrix, dR]
    _ = ∑ _r : Coord, (Real.sqrt dR)⁻¹ * (Real.sqrt dR)⁻¹ := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          simp [mul_left_comm, mul_comm]
    _ = dR * ((Real.sqrt dR)⁻¹ * (Real.sqrt dR)⁻¹) := by
          simp [dR]
    _ = (Real.sqrt dR * Real.sqrt dR) *
          ((Real.sqrt dR)⁻¹ * (Real.sqrt dR)⁻¹) := by
          rw [show Real.sqrt dR * Real.sqrt dR = dR from by
            simpa [pow_two] using hsqrt_sq]
    _ = 1 := by
          field_simp [hsqrt_ne]

/-- Off-diagonal inner products are scaled sums of independent product signs. -/
theorem inner_scaledMatrix_eq_inv_card_mul_sum_pairSign [Fintype Coord]
    (hd : 0 < Fintype.card Coord) (ω : Coord → Feature → Bool)
    (i j : Feature) :
    inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
      (scaledMatrix (Feature := Feature) (Coord := Coord) ω j) =
        (Fintype.card Coord : ℝ)⁻¹ *
          ∑ r : Coord, pairSign (ω r) i j := by
  classical
  let dR : ℝ := Fintype.card Coord
  have hdR_pos : 0 < dR := by
    dsimp [dR]
    exact_mod_cast hd
  have hsqrt_sq : (Real.sqrt dR) ^ 2 = dR := by
    exact Real.sq_sqrt (le_of_lt hdR_pos)
  have hsqrt_ne : Real.sqrt dR ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.mpr hdR_pos)
  have hsqrt_mul : Real.sqrt dR * Real.sqrt dR = dR := by
    simpa [pow_two] using hsqrt_sq
  have hscale :
      (Real.sqrt dR)⁻¹ * (Real.sqrt dR)⁻¹ = dR⁻¹ := by
    calc
      (Real.sqrt dR)⁻¹ * (Real.sqrt dR)⁻¹ =
          (Real.sqrt dR * Real.sqrt dR)⁻¹ := by
            field_simp [hsqrt_ne]
      _ = dR⁻¹ := by
            rw [hsqrt_mul]
  calc
    inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
        (scaledMatrix (Feature := Feature) (Coord := Coord) ω j)
        = ∑ r : Coord,
            ((Real.sqrt dR)⁻¹ * rademacherSign (ω r i)) *
              ((Real.sqrt dR)⁻¹ * rademacherSign (ω r j)) := by
          simp [EconCSLib.Math.LinearCompressedSensing.inner, scaledMatrix, dR]
    _ = ∑ r : Coord,
          ((Real.sqrt dR)⁻¹ * (Real.sqrt dR)⁻¹) *
            pairSign (ω r) i j := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          dsimp [pairSign]
          ring
    _ = ((Real.sqrt dR)⁻¹ * (Real.sqrt dR)⁻¹) *
          ∑ r : Coord, pairSign (ω r) i j := by
          rw [Finset.mul_sum]
    _ = dR⁻¹ * ∑ r : Coord, pairSign (ω r) i j := by
          rw [hscale]
    _ = (Fintype.card Coord : ℝ)⁻¹ *
          ∑ r : Coord, pairSign (ω r) i j := by
          simp [dR]

/--
Deterministic package: once all off-diagonal inner products are bounded by
`mu`, a scaled Rademacher matrix is `mu`-incoherent.
-/
theorem scaledMatrix_muIncoherentLE_of_offdiag [Fintype Feature] [Fintype Coord]
    {μ : ℝ} (hd : 0 < Fintype.card Coord)
    (ω : Coord → Feature → Bool)
    (hoff :
      ∀ ⦃i j : Feature⦄, i ≠ j →
        |inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
            (scaledMatrix (Feature := Feature) (Coord := Coord) ω j)| ≤ μ) :
    MuIncoherentLE
      (scaledMatrix (Feature := Feature) (Coord := Coord) ω) μ where
  self_inner := inner_scaledMatrix_self (Feature := Feature) (Coord := Coord) hd ω
  offdiag_abs_le := hoff

/-- The row-product signs are independent across rows. -/
theorem pairSign_iIndepFun [Fintype Feature]
    (i j : Feature) :
    iIndepFun
      (fun r (ω : Coord → Feature → Bool) => pairSign (ω r) i j)
      (rowsMeasure Feature Coord) := by
  let P : Coord → Measure (Feature → Bool) :=
    fun _ => FairCoin.productMeasure Feature
  let hP : ∀ r : Coord, IsProbabilityMeasure (P r) := by
    intro r
    simpa [P] using FairCoin.productMeasure_isProbabilityMeasure Feature
  have hrow :
      iIndepFun (fun r (ω : Coord → Feature → Bool) => ω r)
        (Measure.infinitePi P) := by
    exact
      @ProbabilityTheory.iIndepFun_infinitePi
        (ι := Coord) (𝓧 := fun _ : Coord => Feature → Bool)
        (m𝓧 := fun _ => by infer_instance)
        (Ω := fun _ : Coord => Feature → Bool)
        (mΩ := fun _ => by infer_instance)
        (P := P) hP (X := fun _ : Coord => id)
        (mX := fun _ => measurable_id)
  simpa [rowsMeasure, P] using hrow.comp
    (fun _ row => pairSign row i j)
    (fun _ => measurable_of_finite _)

/--
Hoeffding upper tail for one fixed off-diagonal pair, stated for centered
row-product signs.  The mean-zero simplification is a separate reusable lemma.
-/
theorem measure_sum_centered_pairSign_ge_le_exp
    [Fintype Feature] [Fintype Coord]
    (i j : Feature) {ε : ℝ} (hε : 0 ≤ ε) :
    (rowsMeasure Feature Coord).real
        {ω | ε ≤
          ∑ r : Coord,
            (pairSign (ω r) i j -
              ∫ x, pairSign (x r) i j ∂rowsMeasure Feature Coord)} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ((∑ _r : Coord,
            ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  classical
  haveI : IsProbabilityMeasure (rowsMeasure Feature Coord) :=
    rowsMeasure_isProbabilityMeasure Feature Coord
  refine
    EconCSLib.measure_sum_centered_bounded_ge_le_exp_of_iIndepFun
      (μ := rowsMeasure Feature Coord)
      (X := fun r (ω : Coord → Feature → Bool) => pairSign (ω r) i j)
      (pairSign_iIndepFun (Feature := Feature) (Coord := Coord) i j)
      (s := Finset.univ) (a := (-1 : ℝ)) (b := 1) ?_ ?_ hε
  · intro r _hr
    exact (measurable_of_finite _).aemeasurable
  · intro r _hr
    exact ae_of_all _ fun ω => pairSign_mem_Icc (ω r) i j

/-- Hoeffding upper tail for the uncentered sum of one fixed off-diagonal pair. -/
theorem measure_sum_pairSign_ge_le_exp
    [Fintype Feature] [Fintype Coord]
    {i j : Feature} (hij : i ≠ j) {ε : ℝ} (hε : 0 ≤ ε) :
    (rowsMeasure Feature Coord).real
        {ω | ε ≤ ∑ r : Coord, pairSign (ω r) i j} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ((∑ _r : Coord,
            ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  classical
  haveI : IsProbabilityMeasure (rowsMeasure Feature Coord) :=
    rowsMeasure_isProbabilityMeasure Feature Coord
  have htail :=
    measure_sum_centered_pairSign_ge_le_exp
      (Feature := Feature) (Coord := Coord) i j hε
  refine le_trans ?_ htail
  refine measureReal_mono (μ := rowsMeasure Feature Coord) ?_
    (measure_ne_top _ _)
  intro ω hω
  have hcenter :
      (∑ r : Coord,
          (pairSign (ω r) i j -
            ∫ x, pairSign (x r) i j ∂rowsMeasure Feature Coord)) =
        ∑ r : Coord, pairSign (ω r) i j := by
    rw [Finset.sum_sub_distrib]
    simp [integral_pairSign_rowsMeasure (Feature := Feature) (Coord := Coord) hij]
  change ε ≤
    ∑ r : Coord,
      (pairSign (ω r) i j -
        ∫ x, pairSign (x r) i j ∂rowsMeasure Feature Coord)
  change ε ≤ ∑ r : Coord, pairSign (ω r) i j at hω
  rw [hcenter]
  exact hω

/-- Hoeffding lower tail for the uncentered sum of one fixed off-diagonal pair. -/
theorem measure_neg_sum_pairSign_ge_le_exp
    [Fintype Feature] [Fintype Coord]
    {i j : Feature} (hij : i ≠ j) {ε : ℝ} (hε : 0 ≤ ε) :
    (rowsMeasure Feature Coord).real
        {ω | ε ≤ -∑ r : Coord, pairSign (ω r) i j} ≤
      Real.exp
        (-ε ^ 2 /
          (2 * ((∑ _r : Coord,
            ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  classical
  haveI : IsProbabilityMeasure (rowsMeasure Feature Coord) :=
    rowsMeasure_isProbabilityMeasure Feature Coord
  have hindep :
      iIndepFun
        (fun r (ω : Coord → Feature → Bool) => -pairSign (ω r) i j)
        (rowsMeasure Feature Coord) := by
    exact (pairSign_iIndepFun (Feature := Feature) (Coord := Coord) i j).comp
      (fun _ x => -x) (fun _ => measurable_id.neg)
  have htail :
      (rowsMeasure Feature Coord).real
          {ω | ε ≤
            ∑ r : Coord,
              (-pairSign (ω r) i j -
                ∫ x, -pairSign (x r) i j ∂rowsMeasure Feature Coord)} ≤
        Real.exp
          (-ε ^ 2 /
            (2 * ((∑ _r : Coord,
              ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
    refine
      EconCSLib.measure_sum_centered_bounded_ge_le_exp_of_iIndepFun
        (μ := rowsMeasure Feature Coord)
        (X := fun r (ω : Coord → Feature → Bool) => -pairSign (ω r) i j)
        hindep
        (s := Finset.univ) (a := (-1 : ℝ)) (b := 1) ?_ ?_ hε
    · intro r _hr
      exact (measurable_of_finite _).aemeasurable
    · intro r _hr
      exact ae_of_all _ fun ω => by
        have h := pairSign_mem_Icc (ω r) i j
        change -1 ≤ -pairSign (ω r) i j ∧ -pairSign (ω r) i j ≤ 1
        constructor <;> linarith [h.1, h.2]
  refine le_trans ?_ htail
  refine measureReal_mono (μ := rowsMeasure Feature Coord) ?_
    (measure_ne_top _ _)
  intro ω hω
  have hcenter :
      (∑ r : Coord,
          (-pairSign (ω r) i j -
            ∫ x, -pairSign (x r) i j ∂rowsMeasure Feature Coord)) =
        -∑ r : Coord, pairSign (ω r) i j := by
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    simp [integral_neg, integral_pairSign_rowsMeasure
      (Feature := Feature) (Coord := Coord) hij]
  change ε ≤
    ∑ r : Coord,
      (-pairSign (ω r) i j -
        ∫ x, -pairSign (x r) i j ∂rowsMeasure Feature Coord)
  change ε ≤ -∑ r : Coord, pairSign (ω r) i j at hω
  rw [hcenter]
  exact hω

/-- Two-sided Hoeffding tail for the row-product sign sum. -/
theorem measure_abs_sum_pairSign_ge_le_two_mul_exp
    [Fintype Feature] [Fintype Coord]
    {i j : Feature} (hij : i ≠ j) {ε : ℝ} (hε : 0 ≤ ε) :
    (rowsMeasure Feature Coord).real
        {ω | ε ≤ |∑ r : Coord, pairSign (ω r) i j|} ≤
      2 *
        Real.exp
          (-ε ^ 2 /
            (2 * ((∑ _r : Coord,
              ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  classical
  haveI : IsProbabilityMeasure (rowsMeasure Feature Coord) :=
    rowsMeasure_isProbabilityMeasure Feature Coord
  let μM := rowsMeasure Feature Coord
  let posSet : Set (Coord → Feature → Bool) :=
    {ω | ε ≤ ∑ r : Coord, pairSign (ω r) i j}
  let negSet : Set (Coord → Feature → Bool) :=
    {ω | ε ≤ -∑ r : Coord, pairSign (ω r) i j}
  let absSet : Set (Coord → Feature → Bool) :=
    {ω | ε ≤ |∑ r : Coord, pairSign (ω r) i j|}
  have hsubset : absSet ⊆ posSet ∪ negSet := by
    intro ω hω
    dsimp [absSet, posSet, negSet] at hω ⊢
    by_cases hsum : 0 ≤ ∑ r : Coord, pairSign (ω r) i j
    · left
      simpa [abs_of_nonneg hsum] using hω
    · right
      have hsum' : ∑ r : Coord, pairSign (ω r) i j < 0 := lt_of_not_ge hsum
      simpa [abs_of_neg hsum'] using hω
  have hpos := measure_sum_pairSign_ge_le_exp
    (Feature := Feature) (Coord := Coord) hij hε
  have hneg := measure_neg_sum_pairSign_ge_le_exp
    (Feature := Feature) (Coord := Coord) hij hε
  calc
    μM.real absSet ≤ μM.real (posSet ∪ negSet) := by
      exact measureReal_mono (μ := μM) hsubset (measure_ne_top _ _)
    _ ≤ μM.real posSet + μM.real negSet := by
      exact measureReal_union_le (μ := μM) posSet negSet
    _ ≤
        Real.exp
          (-ε ^ 2 /
            (2 * ((∑ _r : Coord,
              ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) +
        Real.exp
          (-ε ^ 2 /
            (2 * ((∑ _r : Coord,
              ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
      exact add_le_add hpos hneg
    _ = 2 *
        Real.exp
          (-ε ^ 2 /
            (2 * ((∑ _r : Coord,
              ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
      ring

/--
Two-sided tail for one fixed off-diagonal inner product of the scaled
Rademacher matrix.
-/
theorem measure_abs_inner_scaledMatrix_ge_le_two_mul_exp
    [Fintype Feature] [Fintype Coord]
    (hd : 0 < Fintype.card Coord) {i j : Feature} (hij : i ≠ j)
    {μ : ℝ} (hμ : 0 ≤ μ) :
    (rowsMeasure Feature Coord).real
        {ω |
          μ ≤
            |inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω j)|} ≤
      2 *
        Real.exp
          (-((μ * (Fintype.card Coord : ℝ)) ^ 2) /
            (2 * ((∑ _r : Coord,
              ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ))) := by
  classical
  haveI : IsProbabilityMeasure (rowsMeasure Feature Coord) :=
    rowsMeasure_isProbabilityMeasure Feature Coord
  let dR : ℝ := Fintype.card Coord
  have hdR_pos : 0 < dR := by
    dsimp [dR]
    exact_mod_cast hd
  have hε : 0 ≤ μ * dR := mul_nonneg hμ hdR_pos.le
  have htail :=
    measure_abs_sum_pairSign_ge_le_two_mul_exp
      (Feature := Feature) (Coord := Coord) hij (ε := μ * dR) hε
  refine le_trans ?_ htail
  refine measureReal_mono (μ := rowsMeasure Feature Coord) ?_
    (measure_ne_top _ _)
  intro ω hω
  change μ * dR ≤ |∑ r : Coord, pairSign (ω r) i j|
  change μ ≤
    |inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
      (scaledMatrix (Feature := Feature) (Coord := Coord) ω j)| at hω
  have hinner :
      inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
        (scaledMatrix (Feature := Feature) (Coord := Coord) ω j) =
          dR⁻¹ * ∑ r : Coord, pairSign (ω r) i j := by
    simpa [dR] using
      inner_scaledMatrix_eq_inv_card_mul_sum_pairSign
        (Feature := Feature) (Coord := Coord) hd ω i j
  rw [hinner, abs_mul, abs_of_pos (inv_pos.mpr hdR_pos)] at hω
  have hprod : dR * dR⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hdR_pos)
  have habs_nonneg : 0 ≤ |∑ r : Coord, pairSign (ω r) i j| := abs_nonneg _
  nlinarith

/-- Ordered off-diagonal feature pairs. -/
noncomputable def offdiagPairFinset
    [Fintype Feature] [DecidableEq Feature] : Finset (Feature × Feature) :=
  ((Finset.univ : Finset Feature).product (Finset.univ : Finset Feature)).filter
    fun p => p.1 ≠ p.2

theorem mem_offdiagPairFinset
    [Fintype Feature] [DecidableEq Feature] {p : Feature × Feature} :
    p ∈ offdiagPairFinset (Feature := Feature) ↔ p.1 ≠ p.2 := by
  classical
  simp [offdiagPairFinset]

/-- Fixed-pair two-sided tail bound, as a reusable expression. -/
noncomputable def fixedPairTailBound (Coord : Type*) [Fintype Coord] (μ : ℝ) : ℝ :=
  2 *
    Real.exp
      (-((μ * (Fintype.card Coord : ℝ)) ^ 2) /
        (2 * ((∑ _r : Coord,
          ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2 : NNReal)) : ℝ)))

/-- The fixed-pair tail bound in the simplified `d mu^2 / 2` form. -/
theorem fixedPairTailBound_eq
    (Coord : Type*) [Fintype Coord] (μ : ℝ) :
    fixedPairTailBound Coord μ =
      2 * Real.exp (-((Fintype.card Coord : ℝ) * μ ^ 2) / 2) := by
  classical
  let dR : ℝ := Fintype.card Coord
  have hsum :
      (∑ _r : Coord, (|(1 : ℝ) - (-1)| / 2) ^ 2) = dR := by
    norm_num [dR]
  by_cases hdR : dR = 0
  · simp [fixedPairTailBound, dR, hdR]
  · dsimp [fixedPairTailBound]
    rw [hsum]
    congr 2
    field_simp [hdR]
    ring

/--
Logarithmic dimension form of the ordered-pair Rademacher union bound.  If
`log (2 * pairCount) < d * μ^2 / 2`, then
`pairCount * 2 * exp (-(d * μ^2) / 2) < 1`.
-/
theorem pair_count_mul_fixedPairTailBound_lt_one_of_log_lt
    (Coord : Type*) [Fintype Coord] {pairCount μ : ℝ}
    (hpair_pos : 0 < pairCount)
    (hlog :
      Real.log (2 * pairCount) <
        ((Fintype.card Coord : ℝ) * μ ^ 2) / 2) :
    pairCount * fixedPairTailBound Coord μ < 1 := by
  let x : ℝ := ((Fintype.card Coord : ℝ) * μ ^ 2) / 2
  have hP_pos : 0 < 2 * pairCount := by positivity
  have hP_lt_exp : 2 * pairCount < Real.exp x := by
    exact (Real.log_lt_iff_lt_exp hP_pos).mp (by simpa [x] using hlog)
  have hexp_neg_pos : 0 < Real.exp (-x) := Real.exp_pos _
  have hmul_lt :
      (2 * pairCount) * Real.exp (-x) <
        Real.exp x * Real.exp (-x) :=
    mul_lt_mul_of_pos_right hP_lt_exp hexp_neg_pos
  have hexp_cancel : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  calc
    pairCount * fixedPairTailBound Coord μ =
        (2 * pairCount) * Real.exp (-x) := by
          rw [fixedPairTailBound_eq]
          have hxarg :
              -((Fintype.card Coord : ℝ) * μ ^ 2) / 2 = -x := by
            dsimp [x]
            ring
          rw [hxarg]
          ring
    _ < Real.exp x * Real.exp (-x) := hmul_lt
    _ = 1 := hexp_cancel

/--
Logarithmic dimension form of the ordered-pair Rademacher union bound with an
explicit failure probability. If
`log ((2 * pairCount) / δ) <= d * μ^2 / 2`, then the union-bound tail is at
most `δ`.
-/
theorem pair_count_mul_fixedPairTailBound_le_delta_of_log_div_le
    (Coord : Type*) [Fintype Coord] {pairCount μ δ : ℝ}
    (hpair_pos : 0 < pairCount) (hδ_pos : 0 < δ)
    (hlog :
      Real.log ((2 * pairCount) / δ) ≤
        ((Fintype.card Coord : ℝ) * μ ^ 2) / 2) :
    pairCount * fixedPairTailBound Coord μ ≤ δ := by
  let x : ℝ := ((Fintype.card Coord : ℝ) * μ ^ 2) / 2
  have harg_pos : 0 < (2 * pairCount) / δ := by
    positivity
  have hP_div_le_exp : (2 * pairCount) / δ ≤ Real.exp x := by
    exact (Real.log_le_iff_le_exp harg_pos).mp (by simpa [x] using hlog)
  have hP_le_delta_exp : 2 * pairCount ≤ δ * Real.exp x := by
    have hmul :=
      mul_le_mul_of_nonneg_right hP_div_le_exp hδ_pos.le
    calc
      2 * pairCount = ((2 * pairCount) / δ) * δ := by
        field_simp [ne_of_gt hδ_pos]
      _ ≤ Real.exp x * δ := hmul
      _ = δ * Real.exp x := by ring
  have hexp_neg_nonneg : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hmul_le :
      (2 * pairCount) * Real.exp (-x) ≤
        (δ * Real.exp x) * Real.exp (-x) :=
    mul_le_mul_of_nonneg_right hP_le_delta_exp hexp_neg_nonneg
  have hexp_cancel : (δ * Real.exp x) * Real.exp (-x) = δ := by
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
    simp
  calc
    pairCount * fixedPairTailBound Coord μ =
        (2 * pairCount) * Real.exp (-x) := by
          rw [fixedPairTailBound_eq]
          have hxarg :
              -((Fintype.card Coord : ℝ) * μ ^ 2) / 2 = -x := by
            dsimp [x]
            ring
          rw [hxarg]
          ring
    _ ≤ (δ * Real.exp x) * Real.exp (-x) := hmul_le
    _ = δ := hexp_cancel

/--
High-probability strict off-diagonal incoherence for a scaled Rademacher
matrix.  This is the reusable finite union-bound form behind the standard
random incoherent-matrix lemma.
-/
theorem measure_forall_offdiag_abs_inner_scaledMatrix_lt_ge_one_sub_union_bound
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (hd : 0 < Fintype.card Coord) {μ : ℝ} (hμ : 0 ≤ μ) :
    measureProb (rowsMeasure Feature Coord)
        (fun ω =>
          ∀ ⦃i j : Feature⦄, i ≠ j →
            |inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω j)| < μ) ≥
      1 - ((offdiagPairFinset (Feature := Feature)).card : ℝ) *
          fixedPairTailBound Coord μ := by
  classical
  let μM := rowsMeasure Feature Coord
  haveI : IsProbabilityMeasure μM := by
    simpa [μM] using rowsMeasure_isProbabilityMeasure Feature Coord
  let pairs := offdiagPairFinset (Feature := Feature)
  let bad : Feature × Feature → (Coord → Feature → Bool) → Prop :=
    fun p ω =>
      μ ≤
        |inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω p.1)
          (scaledMatrix (Feature := Feature) (Coord := Coord) ω p.2)|
  let badUnion : Set (Coord → Feature → Bool) :=
    {ω | ∃ p ∈ pairs, bad p ω}
  let good : Set (Coord → Feature → Bool) :=
    {ω |
      ∀ ⦃i j : Feature⦄, i ≠ j →
        |inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
          (scaledMatrix (Feature := Feature) (Coord := Coord) ω j)| < μ}
  have hpair_le :
      ∀ p ∈ pairs,
        measureProb μM (bad p) ≤ fixedPairTailBound Coord μ := by
    intro p hp
    have hij : p.1 ≠ p.2 := by
      simpa [pairs] using (mem_offdiagPairFinset (Feature := Feature)).mp hp
    simpa [measureProb, μM, bad, fixedPairTailBound] using
      measure_abs_inner_scaledMatrix_ge_le_two_mul_exp
        (Feature := Feature) (Coord := Coord) hd hij hμ
  have hbad_union_le :
      measureProb μM (fun ω => ∃ p ∈ pairs, bad p ω) ≤
        ((pairs.card : ℕ) : ℝ) * fixedPairTailBound Coord μ := by
    have hunion :=
      measureProb_biUnion_finset_le
        (μ := μM) (s := pairs) (p := bad)
    have hsum_le :
        ∑ p ∈ pairs, measureProb μM (bad p) ≤
          ∑ _p ∈ pairs, fixedPairTailBound Coord μ := by
      exact Finset.sum_le_sum fun p hp => hpair_le p hp
    calc
      measureProb μM (fun ω => ∃ p ∈ pairs, bad p ω) ≤
          ∑ p ∈ pairs, measureProb μM (bad p) := hunion
      _ ≤ ∑ _p ∈ pairs, fixedPairTailBound Coord μ := hsum_le
      _ = ((pairs.card : ℕ) : ℝ) * fixedPairTailBound Coord μ := by
        simp
  have hgood_eq : good = badUnionᶜ := by
    ext ω
    constructor
    · intro hgood hbad
      rcases hbad with ⟨p, hp, hpbad⟩
      have hij : p.1 ≠ p.2 := by
        simpa [pairs] using (mem_offdiagPairFinset (Feature := Feature)).mp hp
      exact not_le_of_gt (hgood hij) hpbad
    · intro hnot i j hij
      by_contra hle
      exact hnot ⟨(i, j), by
        simpa [pairs] using
          (mem_offdiagPairFinset (Feature := Feature) (p := (i, j))).mpr hij,
        by simpa [bad] using hle⟩
  have hbad_meas : MeasurableSet badUnion := by
    exact Set.toFinite badUnion |>.measurableSet
  have hgood_prob :
      μM.real good = 1 - μM.real badUnion := by
    rw [hgood_eq, probReal_compl_eq_one_sub (μ := μM) hbad_meas]
  have hbad_bound :
      μM.real badUnion ≤
        ((offdiagPairFinset (Feature := Feature)).card : ℝ) *
          fixedPairTailBound Coord μ := by
    simpa [measureProb, μM, badUnion, pairs] using hbad_union_le
  rw [measureProb]
  change μM.real good ≥
    1 - ((offdiagPairFinset (Feature := Feature)).card : ℝ) *
        fixedPairTailBound Coord μ
  rw [hgood_prob]
  linarith

/--
High-probability strict off-diagonal incoherence in the standard `1 - δ` form:
the logarithmic row-dimension condition makes the union-bound failure
probability at most `δ`.
-/
theorem measure_forall_offdiag_abs_inner_scaledMatrix_lt_ge_one_sub_delta_of_log_div_le
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (hd : 0 < Fintype.card Coord) {μ δ : ℝ} (hμ : 0 ≤ μ)
    (hpair_pos : 0 < ((offdiagPairFinset (Feature := Feature)).card : ℝ))
    (hδ_pos : 0 < δ)
    (hlog :
      Real.log
          ((2 * ((offdiagPairFinset (Feature := Feature)).card : ℝ)) / δ) ≤
        ((Fintype.card Coord : ℝ) * μ ^ 2) / 2) :
    measureProb (rowsMeasure Feature Coord)
        (fun ω =>
          ∀ ⦃i j : Feature⦄, i ≠ j →
            |inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω j)| < μ) ≥
      1 - δ := by
  have hprob :=
    measure_forall_offdiag_abs_inner_scaledMatrix_lt_ge_one_sub_union_bound
      (Feature := Feature) (Coord := Coord) hd hμ
  have htail :
      ((offdiagPairFinset (Feature := Feature)).card : ℝ) *
          fixedPairTailBound Coord μ ≤ δ :=
    pair_count_mul_fixedPairTailBound_le_delta_of_log_div_le
      (Coord := Coord)
      (pairCount := ((offdiagPairFinset (Feature := Feature)).card : ℝ))
      (μ := μ) (δ := δ) hpair_pos hδ_pos hlog
  have hprob' :
      measureProb (rowsMeasure Feature Coord)
          (fun ω =>
            ∀ ⦃i j : Feature⦄, i ≠ j →
              |inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω i)
                (scaledMatrix (Feature := Feature) (Coord := Coord) ω j)| < μ) ≥
        1 - ((offdiagPairFinset (Feature := Feature)).card : ℝ) *
            (2 * Real.exp (-((Fintype.card Coord : ℝ) * μ ^ 2) / 2)) := by
    simpa [fixedPairTailBound_eq] using hprob
  rw [fixedPairTailBound_eq] at htail
  linarith

/--
Existence corollary from the finite union bound: if the ordered-pair failure
bound is below one, some scaled Rademacher matrix is `mu`-incoherent.
-/
theorem exists_scaledMatrix_muIncoherentLE_of_union_bound_lt_one
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (hd : 0 < Fintype.card Coord) {μ : ℝ} (hμ : 0 ≤ μ)
    (hbad_lt_one :
      ((offdiagPairFinset (Feature := Feature)).card : ℝ) *
          fixedPairTailBound Coord μ < 1) :
    ∃ A : Feature → Coord → ℝ, MuIncoherentLE A μ := by
  classical
  let μM := rowsMeasure Feature Coord
  haveI : IsProbabilityMeasure μM := by
    simpa [μM] using rowsMeasure_isProbabilityMeasure Feature Coord
  let pairs := offdiagPairFinset (Feature := Feature)
  let bad : Feature × Feature → (Coord → Feature → Bool) → Prop :=
    fun p ω =>
      μ ≤
        |inner (scaledMatrix (Feature := Feature) (Coord := Coord) ω p.1)
          (scaledMatrix (Feature := Feature) (Coord := Coord) ω p.2)|
  have hpair_le :
      ∀ p ∈ pairs,
        measureProb μM (bad p) ≤ fixedPairTailBound Coord μ := by
    intro p hp
    have hij : p.1 ≠ p.2 := by
      simpa [pairs] using (mem_offdiagPairFinset (Feature := Feature)).mp hp
    simpa [measureProb, μM, bad, fixedPairTailBound] using
      measure_abs_inner_scaledMatrix_ge_le_two_mul_exp
        (Feature := Feature) (Coord := Coord) hd hij hμ
  have hbad_union_le :
      measureProb μM (fun ω => ∃ p ∈ pairs, bad p ω) ≤
        ((pairs.card : ℕ) : ℝ) * fixedPairTailBound Coord μ := by
    have hunion :=
      measureProb_biUnion_finset_le
        (μ := μM) (s := pairs) (p := bad)
    have hsum_le :
        ∑ p ∈ pairs, measureProb μM (bad p) ≤
          ∑ _p ∈ pairs, fixedPairTailBound Coord μ := by
      exact Finset.sum_le_sum fun p hp => hpair_le p hp
    calc
      measureProb μM (fun ω => ∃ p ∈ pairs, bad p ω) ≤
          ∑ p ∈ pairs, measureProb μM (bad p) := hunion
      _ ≤ ∑ _p ∈ pairs, fixedPairTailBound Coord μ := hsum_le
      _ = ((pairs.card : ℕ) : ℝ) * fixedPairTailBound Coord μ := by
        simp
  by_contra hnone
  have huniv_subset :
      (Set.univ : Set (Coord → Feature → Bool)) ⊆
        {ω | ∃ p ∈ pairs, bad p ω} := by
    intro ω _hω
    by_contra hno_bad
    apply hnone
    refine ⟨scaledMatrix (Feature := Feature) (Coord := Coord) ω, ?_⟩
    refine scaledMatrix_muIncoherentLE_of_offdiag
      (Feature := Feature) (Coord := Coord) (μ := μ) hd ω ?_
    intro i j hij
    have hp : (i, j) ∈ pairs := by
      simpa [pairs] using
        (mem_offdiagPairFinset (Feature := Feature) (p := (i, j))).mpr hij
    have hnot : ¬ bad (i, j) ω := by
      intro hb
      exact hno_bad ⟨(i, j), hp, hb⟩
    exact le_of_lt (lt_of_not_ge hnot)
  have huniv_le :
      μM.real (Set.univ : Set (Coord → Feature → Bool)) ≤
        measureProb μM (fun ω => ∃ p ∈ pairs, bad p ω) := by
    exact measureReal_mono (μ := μM) huniv_subset (measure_ne_top _ _)
  have hbad_lt :
      measureProb μM (fun ω => ∃ p ∈ pairs, bad p ω) < 1 := by
    have hcard_eq :
        ((pairs.card : ℕ) : ℝ) =
          ((offdiagPairFinset (Feature := Feature)).card : ℝ) := by
      simp [pairs]
    rw [hcard_eq] at hbad_union_le
    exact lt_of_le_of_lt hbad_union_le hbad_lt_one
  have huniv_one :
      μM.real (Set.univ : Set (Coord → Feature → Bool)) = 1 := by
    simp [MeasureTheory.probReal_univ]
  linarith

/--
Existence corollary for exact basis-pursuit recovery from the same finite
Rademacher union bound.  This is the standard coherence-scale sufficient
condition; it is weaker than RIP-scale compressed sensing, but the deterministic
optimization step is fully internal.
-/
theorem exists_scaledMatrix_basisPursuitExactRecovery_of_union_bound_lt_one
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    (hd : 0 < Fintype.card Coord) {k : ℕ} {μ : ℝ} (hμ : 0 ≤ μ)
    (hbad_lt_one :
      ((offdiagPairFinset (Feature := Feature)).card : ℝ) *
          fixedPairTailBound Coord μ < 1)
    (hbound : (k : ℝ) * μ < 1 / 2) :
    ∃ A : Feature → Coord → ℝ, BasisPursuitExactRecovery A k := by
  rcases exists_scaledMatrix_muIncoherentLE_of_union_bound_lt_one
    (Feature := Feature) (Coord := Coord) hd hμ hbad_lt_one with
    ⟨A, hA⟩
  exact ⟨A, basisPursuitExactRecovery_of_muIncoherentLE hμ hA hbound⟩

/--
Supportwise union-bound skeleton for random RIP existence.  If the total
failure probability over the finite family of supports of size at most `s` is
below one, then some scaled Rademacher matrix has global RIP at order `s`.
The remaining analytic work in a full RIP proof is to bound each supportwise
failure probability.
-/
theorem exists_scaledMatrix_restrictedIsometryProperty_of_supportwise_failure_sum_lt_one
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {s : ℕ} {δ : ℝ}
    (hbad_lt_one :
      ∑ S ∈ supportFinsetsCardLe (Feature := Feature) s,
        measureProb (rowsMeasure Feature Coord)
          (fun ω =>
            ¬ RestrictedIsometryOnSupport
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ) <
        1) :
    ∃ A : Feature → Coord → ℝ, RestrictedIsometryProperty A s δ := by
  classical
  let μM := rowsMeasure Feature Coord
  haveI : IsProbabilityMeasure μM := by
    simpa [μM] using rowsMeasure_isProbabilityMeasure Feature Coord
  let supports := supportFinsetsCardLe (Feature := Feature) s
  let bad : Finset Feature → (Coord → Feature → Bool) → Prop :=
    fun S ω =>
      ¬ RestrictedIsometryOnSupport
        (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ
  have hbad_union_le :
      measureProb μM (fun ω => ∃ S ∈ supports, bad S ω) ≤
        ∑ S ∈ supports, measureProb μM (bad S) :=
    measureProb_biUnion_finset_le (μ := μM) (s := supports) (p := bad)
  by_contra hnone
  have huniv_subset :
      (Set.univ : Set (Coord → Feature → Bool)) ⊆
        {ω | ∃ S ∈ supports, bad S ω} := by
    intro ω _hω
    by_contra hno_bad
    apply hnone
    refine ⟨scaledMatrix (Feature := Feature) (Coord := Coord) ω, ?_⟩
    refine restrictedIsometryProperty_of_forall_supportFinsetsCardLe ?_
    intro S hS
    by_contra hbad
    exact hno_bad ⟨S, hS, hbad⟩
  have huniv_le :
      μM.real (Set.univ : Set (Coord → Feature → Bool)) ≤
        measureProb μM (fun ω => ∃ S ∈ supports, bad S ω) := by
    exact measureReal_mono (μ := μM) huniv_subset (measure_ne_top _ _)
  have hbad_lt :
      measureProb μM (fun ω => ∃ S ∈ supports, bad S ω) < 1 := by
    exact lt_of_le_of_lt hbad_union_le (by simpa [supports, bad, μM] using hbad_lt_one)
  have huniv_one :
      μM.real (Set.univ : Set (Coord → Feature → Bool)) = 1 := by
    simp [MeasureTheory.probReal_univ]
  linarith

/--
Uniform per-support failure adapter.  A full random RIP proof usually supplies
the same tail bound for each fixed support; this lemma converts that uniform
tail estimate and a cardinality/tail-product inequality into the failure-sum
condition used by
`exists_scaledMatrix_restrictedIsometryProperty_of_supportwise_failure_sum_lt_one`.
-/
theorem supportwise_failure_sum_lt_one_of_forall_le
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {s : ℕ} {δ η : ℝ}
    (hcard_mul :
      ((supportFinsetsCardLe (Feature := Feature) s).card : ℝ) * η < 1)
    (hfail :
      ∀ S ∈ supportFinsetsCardLe (Feature := Feature) s,
        measureProb (rowsMeasure Feature Coord)
          (fun ω =>
            ¬ RestrictedIsometryOnSupport
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ) ≤
          η) :
    ∑ S ∈ supportFinsetsCardLe (Feature := Feature) s,
      measureProb (rowsMeasure Feature Coord)
        (fun ω =>
          ¬ RestrictedIsometryOnSupport
            (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ) <
      1 := by
  classical
  let supports := supportFinsetsCardLe (Feature := Feature) s
  have hsum_le :
      ∑ S ∈ supports,
        measureProb (rowsMeasure Feature Coord)
          (fun ω =>
            ¬ RestrictedIsometryOnSupport
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ) ≤
        ∑ _S ∈ supports, η := by
    exact Finset.sum_le_sum fun S hS => by
      exact hfail S (by simpa [supports] using hS)
  calc
    ∑ S ∈ supportFinsetsCardLe (Feature := Feature) s,
      measureProb (rowsMeasure Feature Coord)
        (fun ω =>
          ¬ RestrictedIsometryOnSupport
            (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ)
        ≤ ∑ _S ∈ supports, η := by
          simpa [supports] using hsum_le
    _ = ((supportFinsetsCardLe (Feature := Feature) s).card : ℝ) * η := by
          simp [supports]
    _ < 1 := hcard_mul

/--
Existence form using a uniform per-support failure bound.  The only remaining
inputs are the fixed-support concentration estimate and the arithmetic showing
that the number of supports times that estimate is below one.
-/
theorem exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_lt_one
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {s : ℕ} {δ η : ℝ}
    (hcard_mul :
      ((supportFinsetsCardLe (Feature := Feature) s).card : ℝ) * η < 1)
    (hfail :
      ∀ S ∈ supportFinsetsCardLe (Feature := Feature) s,
        measureProb (rowsMeasure Feature Coord)
          (fun ω =>
            ¬ RestrictedIsometryOnSupport
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ) ≤
          η) :
    ∃ A : Feature → Coord → ℝ, RestrictedIsometryProperty A s δ :=
  exists_scaledMatrix_restrictedIsometryProperty_of_supportwise_failure_sum_lt_one
    (Feature := Feature) (Coord := Coord) (s := s) (δ := δ)
    (supportwise_failure_sum_lt_one_of_forall_le
      (Feature := Feature) (Coord := Coord) (s := s) (δ := δ) (η := η)
      hcard_mul hfail)

/--
Exponential-tail form of the uniform supportwise failure adapter.  If each
fixed support fails with probability at most `exp (-rate)` and the logarithm
of the support-family size is below `rate`, then the union bound is below one.
-/
theorem exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_exp_log_card_lt
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {s : ℕ} {δ rate : ℝ}
    (hcard_pos : 0 < ((supportFinsetsCardLe (Feature := Feature) s).card : ℝ))
    (hlog_card_lt :
      Real.log ((supportFinsetsCardLe (Feature := Feature) s).card : ℝ) <
        rate)
    (hfail :
      ∀ S ∈ supportFinsetsCardLe (Feature := Feature) s,
        measureProb (rowsMeasure Feature Coord)
          (fun ω =>
            ¬ RestrictedIsometryOnSupport
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ) ≤
          Real.exp (-rate)) :
    ∃ A : Feature → Coord → ℝ, RestrictedIsometryProperty A s δ := by
  have hcard_mul :
      ((supportFinsetsCardLe (Feature := Feature) s).card : ℝ) *
          Real.exp (-rate) < 1 :=
    EconCSLib.Math.mul_exp_neg_lt_one_of_log_lt hcard_pos hlog_card_lt
  exact
    exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_lt_one
      (Feature := Feature) (Coord := Coord) (s := s) (δ := δ)
      (η := Real.exp (-rate)) hcard_mul hfail

/--
Binomial-count version of the uniform supportwise failure adapter.  The
finite support family has cardinality at most
`sum_{r <= s} choose |Feature| r`, so a fixed-support tail bound whose product
with this binomial count is below one yields a sampled RIP matrix.
-/
theorem exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_sum_choose_lt_one
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {s : ℕ} {δ η : ℝ}
    (hη_nonneg : 0 ≤ η)
    (hcount_mul :
      ((∑ r ∈ Finset.range (s + 1), Nat.choose (Fintype.card Feature) r : ℕ) : ℝ) *
          η < 1)
    (hfail :
      ∀ S ∈ supportFinsetsCardLe (Feature := Feature) s,
        measureProb (rowsMeasure Feature Coord)
          (fun ω =>
            ¬ RestrictedIsometryOnSupport
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ) ≤
          η) :
    ∃ A : Feature → Coord → ℝ, RestrictedIsometryProperty A s δ := by
  have hcard_nat :
      (supportFinsetsCardLe (Feature := Feature) s).card ≤
        ∑ r ∈ Finset.range (s + 1), Nat.choose (Fintype.card Feature) r :=
    EconCSLib.Math.LinearCompressedSensing.supportFinsetsCardLe_card_le_sum_choose
      (Feature := Feature) s
  have hcard_real :
      ((supportFinsetsCardLe (Feature := Feature) s).card : ℝ) ≤
        ((∑ r ∈ Finset.range (s + 1),
          Nat.choose (Fintype.card Feature) r : ℕ) : ℝ) := by
    exact_mod_cast hcard_nat
  have hcard_mul :
      ((supportFinsetsCardLe (Feature := Feature) s).card : ℝ) * η < 1 := by
    exact (mul_le_mul_of_nonneg_right hcard_real hη_nonneg).trans_lt hcount_mul
  exact
    exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_lt_one
      (Feature := Feature) (Coord := Coord) (s := s) (δ := δ) (η := η)
      hcard_mul hfail

/--
Small-support binomial-count version.  When `s <= |Feature| / 2`, the number
of supports of size at most `s` is at most `(s+1) * choose |Feature| s`.
-/
theorem exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_succ_mul_choose_lt_one
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {s : ℕ} {δ η : ℝ}
    (hs_half : s ≤ Fintype.card Feature / 2)
    (hη_nonneg : 0 ≤ η)
    (hcount_mul :
      (((s + 1) * Nat.choose (Fintype.card Feature) s : ℕ) : ℝ) *
          η < 1)
    (hfail :
      ∀ S ∈ supportFinsetsCardLe (Feature := Feature) s,
        measureProb (rowsMeasure Feature Coord)
          (fun ω =>
            ¬ RestrictedIsometryOnSupport
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ) ≤
          η) :
    ∃ A : Feature → Coord → ℝ, RestrictedIsometryProperty A s δ := by
  have hcard_nat :
      (supportFinsetsCardLe (Feature := Feature) s).card ≤
        (s + 1) * Nat.choose (Fintype.card Feature) s :=
    EconCSLib.Math.LinearCompressedSensing.supportFinsetsCardLe_card_le_succ_mul_choose_of_le_half
      (Feature := Feature) hs_half
  have hcard_real :
      ((supportFinsetsCardLe (Feature := Feature) s).card : ℝ) ≤
        (((s + 1) * Nat.choose (Fintype.card Feature) s : ℕ) : ℝ) := by
    exact_mod_cast hcard_nat
  have hcard_mul :
      ((supportFinsetsCardLe (Feature := Feature) s).card : ℝ) * η < 1 := by
    exact (mul_le_mul_of_nonneg_right hcard_real hη_nonneg).trans_lt hcount_mul
  exact
    exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_lt_one
      (Feature := Feature) (Coord := Coord) (s := s) (δ := δ) (η := η)
      hcard_mul hfail

/--
Exponential-tail version of the small-support binomial-count adapter.  This is
the usual shape of a random RIP proof after the fixed-support concentration
estimate has been proved: a per-support tail `exp (-rate)` wins once the
logarithm of `(s+1) * choose |Feature| s` is below `rate`.
-/
theorem exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_succ_mul_choose_exp_log_count_lt
    [Fintype Feature] [DecidableEq Feature] [Fintype Coord]
    {s : ℕ} {δ rate : ℝ}
    (hs_half : s ≤ Fintype.card Feature / 2)
    (hcount_pos :
      0 < (((s + 1) * Nat.choose (Fintype.card Feature) s : ℕ) : ℝ))
    (hlog_count_lt :
      Real.log (((s + 1) * Nat.choose (Fintype.card Feature) s : ℕ) : ℝ) <
        rate)
    (hfail :
      ∀ S ∈ supportFinsetsCardLe (Feature := Feature) s,
        measureProb (rowsMeasure Feature Coord)
          (fun ω =>
            ¬ RestrictedIsometryOnSupport
              (scaledMatrix (Feature := Feature) (Coord := Coord) ω) S δ) ≤
          Real.exp (-rate)) :
    ∃ A : Feature → Coord → ℝ, RestrictedIsometryProperty A s δ := by
  have hcount_mul :
      (((s + 1) * Nat.choose (Fintype.card Feature) s : ℕ) : ℝ) *
          Real.exp (-rate) < 1 :=
    EconCSLib.Math.mul_exp_neg_lt_one_of_log_lt hcount_pos hlog_count_lt
  exact
    exists_scaledMatrix_restrictedIsometryProperty_of_uniform_supportwise_failure_succ_mul_choose_lt_one
      (Feature := Feature) (Coord := Coord) (s := s) (δ := δ)
      (η := Real.exp (-rate)) hs_half (Real.exp_pos _).le hcount_mul hfail

end RademacherMatrix
end Probability
end EconCSLib
