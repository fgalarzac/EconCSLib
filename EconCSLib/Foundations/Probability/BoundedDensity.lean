import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Bounded Density Measures

Reusable interfaces for measures represented by a density bounded above with
respect to a base measure.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace EconCSLib
namespace Probability

/--
`mu` has a density bounded by `C` with respect to the base measure `nu`.

The witness is intentionally `withDensity`-based so later paper proofs can use
mathlib's absolute-continuity and Lebesgue-integral APIs directly.
-/
def HasBoundedDensity
    {α : Type*} [MeasurableSpace α]
    (ν μ : Measure α) (C : ℝ≥0∞) : Prop :=
  ∃ D : α → ℝ≥0∞, μ = ν.withDensity D ∧ ∀ᵐ x ∂ν, D x ≤ C

namespace HasBoundedDensity

theorem absolutelyContinuous
    {α : Type*} [MeasurableSpace α] {ν μ : Measure α} {C : ℝ≥0∞}
    (h : HasBoundedDensity ν μ C) :
    μ ≪ ν := by
  rcases h with ⟨D, hμ, _hbound⟩
  rw [hμ]
  exact withDensity_absolutelyContinuous ν D

theorem measure_eq_zero_of_base_null
    {α : Type*} [MeasurableSpace α] {ν μ : Measure α} {C : ℝ≥0∞}
    (h : HasBoundedDensity ν μ C) {s : Set α} (hs : ν s = 0) :
    μ s = 0 :=
  h.absolutelyContinuous hs

theorem measure_le_const_mul
    {α : Type*} [MeasurableSpace α] {ν μ : Measure α} {C : ℝ≥0∞}
    (h : HasBoundedDensity ν μ C) {s : Set α} (hs : MeasurableSet s) :
    μ s ≤ C * ν s := by
  rcases h with ⟨D, hμ, hbound⟩
  rw [hμ, withDensity_apply D hs]
  calc
    ∫⁻ x in s, D x ∂ν
        ≤ ∫⁻ _x in s, C ∂ν := by
          exact setLIntegral_mono_ae' hs
            (hbound.mono fun _x hx _hxs => hx)
    _ = C * ν s := by
          rw [setLIntegral_const]

theorem measure_le_const_mul_of_base_null
    {α : Type*} [MeasurableSpace α] {ν μ : Measure α} {C : ℝ≥0∞}
    (h : HasBoundedDensity ν μ C) {s : Set α} (hs : MeasurableSet s)
    (hνs : ν s = 0) :
    μ s = 0 := by
  exact h.measure_eq_zero_of_base_null hνs

theorem measure_biUnion_finset_le_const_mul_sum
    {α ι : Type*} [MeasurableSpace α] {ν μ : Measure α} {C : ℝ≥0∞}
    (h : HasBoundedDensity ν μ C) (I : Finset ι) (s : ι → Set α)
    (hs : ∀ i, i ∈ I → MeasurableSet (s i)) :
    μ (⋃ i ∈ I, s i) ≤ C * ∑ i ∈ I, ν (s i) := by
  calc
    μ (⋃ i ∈ I, s i) ≤ ∑ i ∈ I, μ (s i) := by
      exact measure_biUnion_finset_le I s
    _ ≤ ∑ i ∈ I, C * ν (s i) := by
      exact Finset.sum_le_sum fun i hi => h.measure_le_const_mul (hs i hi)
    _ = C * ∑ i ∈ I, ν (s i) := by
      rw [Finset.mul_sum]

theorem measure_Icc_le_const_mul_length
    {μ : Measure ℝ} {C : ℝ≥0∞}
    (h : HasBoundedDensity StieltjesFunction.id.measure μ C) (a b : ℝ) :
    μ (Set.Icc a b) ≤ C * ENNReal.ofReal (b - a) := by
  have hlength :
      StieltjesFunction.id.measure (Set.Icc a b) = ENNReal.ofReal (b - a) := by
    rw [← Real.volume_eq_stieltjes_id]
    exact Real.volume_Icc
  simpa [hlength] using
    h.measure_le_const_mul (s := Set.Icc a b) measurableSet_Icc

theorem measure_Ioo_le_const_mul_length
    {μ : Measure ℝ} {C : ℝ≥0∞}
    (h : HasBoundedDensity StieltjesFunction.id.measure μ C) (a b : ℝ) :
    μ (Set.Ioo a b) ≤ C * ENNReal.ofReal (b - a) := by
  have hlength :
      StieltjesFunction.id.measure (Set.Ioo a b) = ENNReal.ofReal (b - a) := by
    rw [← Real.volume_eq_stieltjes_id]
    exact Real.volume_Ioo
  simpa [hlength] using
    h.measure_le_const_mul (s := Set.Ioo a b) measurableSet_Ioo

/--
A bounded-density measure on a finite-dimensional real coordinate space assigns
at most density-bound times Lebesgue volume to an axis-aligned closed box.
-/
theorem measure_Icc_pi_le_const_mul_volume
    {ι : Type*} [Fintype ι]
    {μ : Measure (ι → ℝ)} {C : ℝ≥0∞}
    (h : HasBoundedDensity (volume : Measure (ι → ℝ)) μ C)
    (a b : ι → ℝ) :
    μ (Set.Icc a b) ≤ C * ∏ i, ENNReal.ofReal (b i - a i) := by
  have hbox :=
    h.measure_le_const_mul (s := Set.Icc a b) measurableSet_Icc
  simpa [Real.volume_Icc_pi] using hbox

/--
Coordinate-slab bound inside an axis-aligned box.  The selected coordinate is
restricted to an interval of radius `r` around `center`; all other coordinates
are bounded by the ambient box.  This is the reusable geometric estimate behind
fixed-dimension small-slab probability bounds on bounded domains.
-/
theorem measure_coordinate_slab_Icc_le_const_mul_volume
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : Measure (ι → ℝ)} {C : ℝ≥0∞}
    (h : HasBoundedDensity (volume : Measure (ι → ℝ)) μ C)
    (a b : ι → ℝ) (i : ι) (center r : ℝ) :
    μ {x : ι → ℝ |
        x ∈ Set.Icc a b ∧ x i ∈ Set.Icc (center - r) (center + r)}
      ≤ C *
        ∏ j, ENNReal.ofReal
          ((Function.update b i (center + r)) j -
            (Function.update a i (center - r)) j) := by
  let lo : ι → ℝ := Function.update a i (center - r)
  let hi : ι → ℝ := Function.update b i (center + r)
  have hsubset :
      {x : ι → ℝ |
          x ∈ Set.Icc a b ∧ x i ∈ Set.Icc (center - r) (center + r)}
        ⊆ Set.Icc lo hi := by
    intro x hx
    rcases hx with ⟨hbox, hslab⟩
    constructor
    · intro j
      by_cases hji : j = i
      · subst hji
        simpa [lo] using hslab.1
      · simpa [lo, hji] using hbox.1 j
    · intro j
      by_cases hji : j = i
      · subst hji
        simpa [hi] using hslab.2
      · simpa [hi, hji] using hbox.2 j
  calc
    μ {x : ι → ℝ |
        x ∈ Set.Icc a b ∧ x i ∈ Set.Icc (center - r) (center + r)}
        ≤ μ (Set.Icc lo hi) := measure_mono hsubset
    _ ≤ C * ∏ j, ENNReal.ofReal (hi j - lo j) := by
        exact measure_Icc_pi_le_const_mul_volume h lo hi
    _ = C *
        ∏ j, ENNReal.ofReal
          ((Function.update b i (center + r)) j -
            (Function.update a i (center - r)) j) := by
        rfl

end HasBoundedDensity

end Probability
end EconCSLib
