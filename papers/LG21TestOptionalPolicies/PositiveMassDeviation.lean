import LG21TestOptionalPolicies.SelectedPopulationConditionalSupport

/-!
# Positive-mass deviation calculus for LG21

The paper's continuum model leaves a unilateral action change at a null
information fibre underspecified. This module separates two facts that must
not be conflated in an equilibrium repair:

* a cohort cannot all weakly prefer its own conditional mean when its
  *pre-deviation payoff* has that same cohort mean; and
* a **predecessor-profile/Pareto** comparison in the observed-access,
  report-required LG21 model does **not** satisfy that premise. Before a
  noisy score is drawn, its old all-take payoff is a shrunken affine function
  of latent skill, while a PBO recalibrated to a positive-mass no-take cohort
  is that cohort's mean latent skill. A bounded high-skill band can therefore
  strictly benefit every member under that different comparison.

The second result is only a diagnostic for predecessor-profile/Pareto
comparisons.  It is **not** a counterexample to the governing LG21
candidate-PBO fixed-point semantics: there, each member compares its actions
against the PBO induced by the candidate profile itself, and the strict
expected-payoff/individual-best-response argument rules out a bounded high
no-take band because lower types enter it.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-!
## A cohort cannot all weakly prefer its own mean
-/

/--
If an integrable payoff has mean `c` under a probability law and its `c` level
set is null, then a positive-mass set receives strictly more than `c`.

This is the core obstruction to a positive-mass pooling deviation only when
the new PBO is the deviating cohort's conditional mean *of the old payoff*.
That identity fails for LG21's pre-test taking decision: the old payoff is a
noisy-posterior expectation rather than latent skill itself.
-/
theorem positive_mass_above_mean_of_null_level
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hf : Integrable f μ) (c : ℝ)
    (hmean : (∫ x, f x ∂μ) = c)
    (hlevel : μ {x | f x = c} = 0) :
    0 < μ {x | c < f x} := by
  by_contra hnot
  have habove_zero : μ {x | c < f x} = 0 := by
    exact nonpos_iff_eq_zero.mp (not_lt.mp hnot)
  have hbelow : f ≤ᵐ[μ] fun _ => c := by
    change ∀ᵐ x ∂μ, f x ≤ c
    rw [ae_iff]
    simpa only [Set.mem_setOf_eq, not_le] using habove_zero
  have heq : f =ᵐ[μ] fun _ => c := by
    apply (integral_eq_iff_of_ae_le hf (integrable_const c) hbelow).mp
    simpa using hmean
  have hmember : ∀ᵐ x ∂μ, x ∈ {x | f x = c} := by
    simpa only [Set.mem_setOf_eq] using heq
  have hcomplement : μ ({x | f x = c}ᶜ) = 0 := mem_ae_iff.mp hmember
  have huniv : μ Set.univ = 0 := by
    rw [← Set.union_compl_self {x | f x = c}]
    exact measure_union_null hlevel hcomplement
  rw [IsProbabilityMeasure.measure_univ] at huniv
  norm_num at huniv

/--
A positive-mass cohort whose new payoff is its own conditional mean cannot be
a weakly blocking deviation when its old payoff has no atom at that mean.

The inequality is oriented as `oldPayoff ≤ newPBO`, which is exactly the
condition that every deviator weakly gains from moving into the pooled branch.
-/
def LG21PositiveMassWeakPoolingDeviation
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (cohort : Set α) (oldPayoff : α → ℝ) : Prop :=
  0 < μ cohort ∧
    let cohortLaw := lg21NormalizedRestriction μ cohort
    ∀ᵐ x ∂cohortLaw,
      oldPayoff x ≤ ∫ y, oldPayoff y ∂cohortLaw

/--
Under a finite source law, the preceding positive-mass weak pooling deviation
is impossible whenever the old payoff has a null level set at its cohort mean.
This is a reusable diagnostic certificate. It cannot be instantiated for the
LG21 report-required all-take profile without first proving the missing
old-payoff/latent-skill mean identity, which is false under nonzero test noise.
-/
theorem not_positiveMassWeakPoolingDeviation_of_null_mean_level
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (cohort : Set α) (oldPayoff : α → ℝ)
    (hintegrable : Integrable oldPayoff (lg21NormalizedRestriction μ cohort))
    (hlevel :
      (lg21NormalizedRestriction μ cohort)
        {x | oldPayoff x =
          ∫ y, oldPayoff y ∂lg21NormalizedRestriction μ cohort} = 0) :
    ¬ LG21PositiveMassWeakPoolingDeviation μ cohort oldPayoff := by
  intro hdeviation
  let cohortLaw := lg21NormalizedRestriction μ cohort
  letI : IsProbabilityMeasure cohortLaw :=
    lg21NormalizedRestriction_isProbability μ cohort
      (ne_of_gt hdeviation.1) (measure_ne_top _ _)
  have habove :
      0 < cohortLaw
        {x | (∫ y, oldPayoff y ∂cohortLaw) < oldPayoff x} := by
    exact positive_mass_above_mean_of_null_level cohortLaw oldPayoff
      (by simpa [cohortLaw] using hintegrable)
      (∫ y, oldPayoff y ∂cohortLaw) rfl (by simpa [cohortLaw] using hlevel)
  have hweak : ∀ᵐ x ∂cohortLaw,
      oldPayoff x ≤ ∫ y, oldPayoff y ∂cohortLaw := by
    simpa [LG21PositiveMassWeakPoolingDeviation, cohortLaw] using hdeviation.2
  have habove_zero : cohortLaw
      {x | (∫ y, oldPayoff y ∂cohortLaw) < oldPayoff x} = 0 := by
    change ∀ᵐ x ∂cohortLaw,
      oldPayoff x ≤ ∫ y, oldPayoff y ∂cohortLaw at hweak
    rw [ae_iff] at hweak
    simpa only [Set.mem_setOf_eq, not_le] using hweak
  exact (ne_of_gt habove) habove_zero

/-!
## The high-band predecessor-profile diagnostic for pre-test taking

For a fixed observed base fibre, the source model gives the all-take expected
payoff `mean + weight * (skill - mean)`, with `0 < weight < 1`. If a bounded
high-skill band jointly chooses not to take and each member is compared to the
*old* all-take payoff, the new no-take PBO is the band's conditional mean
latent skill. The following lemmas prove that every member of a sufficiently
high, sufficiently narrow band improves under that predecessor-profile
comparison. They are not an LG21 candidate-PBO equilibrium theorem: a
candidate-wide repair would have to recompute the candidate's selected-
reporter payoff and prove its outsider-closure condition. The required full
closure theorem remains open.
-/

/-- Normalized restriction is concentrated on its conditioning cohort. -/
theorem lg21NormalizedRestriction_ae_mem
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (cohort : Set α) (hmeasurable : MeasurableSet cohort)
    (hfinite : μ cohort ≠ ⊤) :
    ∀ᵐ x ∂lg21NormalizedRestriction μ cohort, x ∈ cohort := by
  unfold lg21NormalizedRestriction
  refine (Measure.ae_ennreal_smul_measure_iff ?_).2 ?_
  · exact ENNReal.inv_ne_zero.mpr hfinite
  · exact (ae_restrict_iff' hmeasurable).2 (ae_of_all _ fun _ hx => hx)

/-- The conditional mean of a positive-mass cohort lying strictly above a
lower bound also lies strictly above that bound. -/
theorem lg21NormalizedRestriction_mean_gt_lower
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (cohort : Set α) (skill : α → ℝ) (lower : ℝ)
    (hmeasurable : MeasurableSet cohort)
    (hpositive : 0 < μ cohort)
    (hintegrable : Integrable skill (lg21NormalizedRestriction μ cohort))
    (hlower : ∀ x ∈ cohort, lower < skill x) :
    lower < ∫ x, skill x ∂lg21NormalizedRestriction μ cohort := by
  let ν := lg21NormalizedRestriction μ cohort
  letI : IsProbabilityMeasure ν :=
    lg21NormalizedRestriction_isProbability μ cohort
      (ne_of_gt hpositive) (measure_ne_top _ _)
  have hsupport : ∀ᵐ x ∂ν, lower < skill x := by
    filter_upwards [lg21NormalizedRestriction_ae_mem μ cohort hmeasurable
      (measure_ne_top _ _)] with x hx
    exact hlower x hx
  have hconstant : (∫ _x, lower ∂ν) = lower := by simp
  rw [← hconstant]
  exact lg21_integral_lt_integral_of_ae_lt_probability
    ν (integrable_const lower) (by simpa [ν] using hintegrable) hsupport

/-- The conditional mean of a positive-mass cohort lying strictly below an
upper bound also lies strictly below that bound.  This is the order-dual
companion to `lg21NormalizedRestriction_mean_gt_lower`; both are used by the
positive-mass PBO route without selecting a named cutoff function. -/
theorem lg21NormalizedRestriction_mean_lt_upper
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (cohort : Set α) (skill : α → ℝ) (upper : ℝ)
    (hmeasurable : MeasurableSet cohort)
    (hpositive : 0 < μ cohort)
    (hintegrable : Integrable skill (lg21NormalizedRestriction μ cohort))
    (hupper : ∀ x ∈ cohort, skill x < upper) :
    (∫ x, skill x ∂lg21NormalizedRestriction μ cohort) < upper := by
  let ν := lg21NormalizedRestriction μ cohort
  letI : IsProbabilityMeasure ν :=
    lg21NormalizedRestriction_isProbability μ cohort
      (ne_of_gt hpositive) (measure_ne_top _ _)
  have hsupport : ∀ᵐ x ∂ν, skill x < upper := by
    filter_upwards [lg21NormalizedRestriction_ae_mem μ cohort hmeasurable
      (measure_ne_top _ _)] with x hx
    exact hupper x hx
  have hconstant : (∫ _x, upper ∂ν) = upper := by simp
  rw [← hconstant]
  exact lg21_integral_lt_integral_of_ae_lt_probability
    ν (by simpa [ν] using hintegrable) (integrable_const upper) hsupport

/-- A shrunken affine payoff lies below the lower edge of a sufficiently high
and narrow band. -/
theorem lg21_affine_shrunken_payoff_lt_band_lower
    (mean scale weight a width skill : ℝ)
    (hscale : 0 < scale) (hweight : 0 < weight)
    (hband : weight * (a + width) < a)
    (hupper : skill < mean + (a + width) * scale) :
    mean + weight * (skill - mean) < mean + a * scale := by
  have hskill : skill - mean < (a + width) * scale := by
    linarith
  have hweighted : weight * (skill - mean) <
      weight * ((a + width) * scale) :=
    mul_lt_mul_of_pos_left hskill hweight
  have hband_scaled : weight * ((a + width) * scale) < a * scale := by
    calc
      weight * ((a + width) * scale) = (weight * (a + width)) * scale := by
        ring
      _ < a * scale := mul_lt_mul_of_pos_right hband hscale
  linarith

/-- Every member of a positive-mass bounded high-skill cohort strictly gains
when the old taking payoff is a shrunken affine posterior and the new no-take
PBO is that cohort's conditional mean latent skill. -/
theorem lg21_affine_high_band_strictly_benefits
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (skill : α → ℝ) (mean scale weight a width : ℝ)
    (hskill_measurable : Measurable skill)
    (hscale : 0 < scale) (hweight : 0 < weight)
    (hband : weight * (a + width) < a)
    (hpositive :
      0 < μ {x | mean + a * scale < skill x ∧
        skill x < mean + (a + width) * scale})
    (hintegrable :
      Integrable skill
        (lg21NormalizedRestriction μ
          {x | mean + a * scale < skill x ∧
            skill x < mean + (a + width) * scale})) :
    ∀ᵐ x ∂lg21NormalizedRestriction μ
      {x | mean + a * scale < skill x ∧
        skill x < mean + (a + width) * scale},
      mean + weight * (skill x - mean) <
        ∫ y, skill y ∂lg21NormalizedRestriction μ
          {y | mean + a * scale < skill y ∧
            skill y < mean + (a + width) * scale} := by
  let cohort : Set α :=
    {x | mean + a * scale < skill x ∧
      skill x < mean + (a + width) * scale}
  have hcohort_measurable : MeasurableSet cohort := by
    change MeasurableSet
      (skill ⁻¹' Set.Ioo (mean + a * scale) (mean + (a + width) * scale))
    exact hskill_measurable measurableSet_Ioo
  have hmean : mean + a * scale <
      ∫ y, skill y ∂lg21NormalizedRestriction μ cohort := by
    apply lg21NormalizedRestriction_mean_gt_lower μ cohort skill
      (mean + a * scale) hcohort_measurable
      (by simpa [cohort] using hpositive)
      (by simpa [cohort] using hintegrable)
    intro x hx
    exact hx.1
  filter_upwards [lg21NormalizedRestriction_ae_mem μ cohort hcohort_measurable
    (measure_ne_top _ _)] with x hx
  exact lt_trans
    (lg21_affine_shrunken_payoff_lt_band_lower mean scale weight a width
      (skill x) hscale hweight hband hx.2)
    hmean

/-- Nonzero Gaussian posterior shrinkage always admits parameters for a
bounded high-skill blocking band. -/
theorem lg21_affine_shrinkage_admits_high_band
    (weight : ℝ) (hweight : 0 < weight) (hweight_lt_one : weight < 1) :
    ∃ a width : ℝ,
      0 < a ∧ 0 < width ∧ weight * (a + width) < a := by
  refine ⟨1, (1 - weight) / (2 * weight), by norm_num, ?_, ?_⟩
  · exact div_pos (by linarith) (by positivity)
  · calc
      weight * (1 + (1 - weight) / (2 * weight)) = (1 + weight) / 2 := by
        field_simp [ne_of_gt hweight]
        ring
      _ < 1 := by linarith

end

end LG21TestOptionalPolicies
