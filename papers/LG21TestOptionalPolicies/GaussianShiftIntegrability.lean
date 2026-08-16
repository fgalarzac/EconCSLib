import LG21TestOptionalPolicies.GaussianWeierstrassRigidity
import Mathlib.Probability.Moments.Tilted

/-!
# Shifted-Gaussian integrability consequences

This module derives the measure-theoretic side conditions used by the
Gaussian convolution rigidity argument from a single source-facing premise:
the deterministic reporting rule is integrable under every Gaussian shift
with a fixed nonzero variance.

The argument uses the proved identity that exponentially tilting the centered
Gaussian by `t * score` gives the Gaussian with mean `variance * t`.  It does
not introduce a density-reweighting axiom.
-/

namespace GaussianConvolutionRigidity

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

/--
Exponential tilting sends a centered real Gaussian to the corresponding
shifted Gaussian.  This is kept in the import-minimal regularity module so
the convolution-rigidity theorem can consume its consequences without an
import cycle.
-/
theorem tilted_centered_gaussian_eq_gaussianReal_for_shift_integrability
    (variance : NNReal) (tilt : ℝ) :
    (gaussianReal 0 variance).tilted (fun score ↦ tilt * score) =
      gaussianReal ((variance : ℝ) * tilt) variance := by
  let baseLaw : Measure ℝ := gaussianReal 0 variance
  let tiltedLaw : Measure ℝ := baseLaw.tilted (fun score ↦ tilt * score)
  let shiftedLaw : Measure ℝ := gaussianReal ((variance : ℝ) * tilt) variance
  letI : IsProbabilityMeasure baseLaw := by
    simpa [baseLaw] using
      (inferInstance : IsProbabilityMeasure (gaussianReal 0 variance))
  letI : NeZero baseLaw := ⟨IsProbabilityMeasure.ne_zero baseLaw⟩
  have htiltIntegrable :
      Integrable (fun score ↦ rexp (tilt * score)) baseLaw := by
    simpa [baseLaw] using
      (integrable_exp_mul_gaussianReal (μ := 0) (v := variance) tilt)
  letI : IsProbabilityMeasure tiltedLaw := by
    simpa [tiltedLaw] using
      (isProbabilityMeasure_tilted (μ := baseLaw) htiltIntegrable)
  letI : IsProbabilityMeasure shiftedLaw := by
    simpa [shiftedLaw] using
      (inferInstance : IsProbabilityMeasure
        (gaussianReal ((variance : ℝ) * tilt) variance))
  change tiltedLaw = shiftedLaw
  apply LG21TestOptionalPolicies.lg21_measure_eq_of_mgf_eq_of_all_real_exp_integrable
  · intro s
    rw [show tiltedLaw = baseLaw.tilted (fun score ↦ tilt * score) by rfl,
      integrable_tilted_iff htiltIntegrable]
    convert integrable_exp_mul_gaussianReal (μ := 0) (v := variance) (tilt + s) using 1
    ext score
    rw [smul_eq_mul, ← Real.exp_add]
    congr 1
    ring
  · ext s
    change mgf id tiltedLaw s = mgf id shiftedLaw s
    calc
      mgf id tiltedLaw s =
          mgf id baseLaw (tilt + s) / mgf id baseLaw tilt := by
        unfold mgf
        rw [show tiltedLaw = baseLaw.tilted (fun score ↦ tilt * score) by rfl,
          integral_exp_tilted]
        congr 1
        apply integral_congr_ae
        filter_upwards with score
        simp only [Pi.add_apply, id_eq]
        congr 1
        ring
      _ = rexp (((variance : ℝ) * tilt) * s + (variance : ℝ) * s ^ 2 / 2) := by
        rw [show baseLaw = gaussianReal 0 variance by rfl,
          mgf_id_gaussianReal]
        rw [← Real.exp_sub]
        congr 1
        ring
      _ = mgf id shiftedLaw s := by
        rw [show shiftedLaw = gaussianReal ((variance : ℝ) * tilt) variance by rfl,
          mgf_id_gaussianReal]

/-- Subtracting a constant preserves integrability under every Gaussian shift. -/
theorem integrable_sub_const_of_integrable_all_gaussian_shifts
    (f : ℝ → ℝ) (c : ℝ) (variance : NNReal)
    (hshift : ∀ mean, Integrable f (gaussianReal mean variance)) :
    ∀ mean, Integrable (fun score ↦ f score - c) (gaussianReal mean variance) := by
  intro mean
  exact (hshift mean).sub (integrable_const c)

/--
Integrability under every shift gives integrability after every real
exponential tilt of the centered Gaussian.  The shift `variance * tilt` is
not an additional assumption: it is supplied by the proved Gaussian tilt
identity.
-/
theorem integrable_exp_mul_sub_const_of_integrable_all_gaussian_shifts
    (f : ℝ → ℝ) (c : ℝ) (variance : NNReal)
    (hshift : ∀ mean, Integrable f (gaussianReal mean variance)) :
    ∀ tilt : ℝ,
      Integrable (fun score ↦ rexp (tilt * score) * (f score - c))
        (gaussianReal 0 variance) := by
  intro tilt
  let baseLaw : Measure ℝ := gaussianReal 0 variance
  have hExp : Integrable (fun score : ℝ ↦ rexp (tilt * score)) baseLaw := by
    simpa [baseLaw] using
      (integrable_exp_mul_gaussianReal (μ := 0) (v := variance) tilt)
  have hShifted :
      Integrable (fun score ↦ f score - c)
        (gaussianReal ((variance : ℝ) * tilt) variance) := by
    exact (hshift ((variance : ℝ) * tilt)).sub (integrable_const c)
  have hTilted :
      Integrable (fun score ↦ f score - c)
        (baseLaw.tilted (fun score ↦ tilt * score)) := by
    rw [show baseLaw = gaussianReal 0 variance by rfl,
      tilted_centered_gaussian_eq_gaussianReal_for_shift_integrability]
    exact hShifted
  have hWeighted :
      Integrable (fun score ↦ rexp (tilt * score) • (f score - c)) baseLaw :=
    (integrable_tilted_iff hExp _).mp hTilted
  simpa [baseLaw, smul_eq_mul] using hWeighted

/-- The positive density measure of a centered all-shifts-integrable rule is finite. -/
theorem isFiniteMeasure_positive_density_sub_const_of_integrable_all_gaussian_shifts
    (f : ℝ → ℝ) (c : ℝ) (variance : NNReal)
    (hshift : ∀ mean, Integrable f (gaussianReal mean variance)) :
    IsFiniteMeasure
      (LG21TestOptionalPolicies.lg21PositiveDensityMeasure
        (gaussianReal 0 variance) (fun score ↦ f score - c)) := by
  unfold LG21TestOptionalPolicies.lg21PositiveDensityMeasure
  exact isFiniteMeasure_withDensity_ofReal
    ((hshift 0).sub (integrable_const c)).hasFiniteIntegral.max_zero

/-- The negative density measure of a centered all-shifts-integrable rule is finite. -/
theorem isFiniteMeasure_negative_density_sub_const_of_integrable_all_gaussian_shifts
    (f : ℝ → ℝ) (c : ℝ) (variance : NNReal)
    (hshift : ∀ mean, Integrable f (gaussianReal mean variance)) :
    IsFiniteMeasure
      (LG21TestOptionalPolicies.lg21NegativeDensityMeasure
        (gaussianReal 0 variance) (fun score ↦ f score - c)) := by
  unfold LG21TestOptionalPolicies.lg21NegativeDensityMeasure
  exact isFiniteMeasure_withDensity_ofReal
    (((hshift 0).sub (integrable_const c)).neg.hasFiniteIntegral.max_zero)

/--
Every real exponential has finite integral against the positive density
measure of a rule integrable under every Gaussian shift.
-/
theorem integrable_exp_mul_positive_density_sub_const_of_integrable_all_gaussian_shifts
    (f : ℝ → ℝ) (c : ℝ) (variance : NNReal)
    (hshift : ∀ mean, Integrable f (gaussianReal mean variance)) :
    ∀ tilt : ℝ,
      Integrable (fun score : ℝ ↦ rexp (tilt * score))
        (LG21TestOptionalPolicies.lg21PositiveDensityMeasure
          (gaussianReal 0 variance) (fun score ↦ f score - c)) := by
  intro tilt
  let baseLaw : Measure ℝ := gaussianReal 0 variance
  let centered : ℝ → ℝ := fun score ↦ f score - c
  let density : ℝ → ENNReal := fun score ↦ ENNReal.ofReal (max (centered score) 0)
  have hdensityMeasurable : AEMeasurable density baseLaw := by
    dsimp [density, centered]
    fun_prop
  have hdensityFinite : ∀ᵐ score ∂baseLaw, density score < ∞ :=
    Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top
  rw [show LG21TestOptionalPolicies.lg21PositiveDensityMeasure baseLaw centered =
      baseLaw.withDensity density by rfl,
    integrable_withDensity_iff_integrable_smul₀' hdensityMeasurable hdensityFinite]
  have hWeighted :=
    integrable_exp_mul_sub_const_of_integrable_all_gaussian_shifts f c variance hshift tilt
  have hPositive :
      Integrable (fun score ↦ max (rexp (tilt * score) * centered score) 0) baseLaw := by
    simpa [baseLaw, centered] using hWeighted.pos_part
  convert hPositive using 1
  ext score
  change (ENNReal.ofReal (max (centered score) 0)).toReal * rexp (tilt * score) = _
  rw [ENNReal.toReal_ofReal (le_max_right _ _)]
  rw [max_mul_of_nonneg _ _ (Real.exp_nonneg _)]
  ring_nf

/--
Every real exponential has finite integral against the negative density
measure of a rule integrable under every Gaussian shift.
-/
theorem integrable_exp_mul_negative_density_sub_const_of_integrable_all_gaussian_shifts
    (f : ℝ → ℝ) (c : ℝ) (variance : NNReal)
    (hshift : ∀ mean, Integrable f (gaussianReal mean variance)) :
    ∀ tilt : ℝ,
      Integrable (fun score : ℝ ↦ rexp (tilt * score))
        (LG21TestOptionalPolicies.lg21NegativeDensityMeasure
          (gaussianReal 0 variance) (fun score ↦ f score - c)) := by
  intro tilt
  let baseLaw : Measure ℝ := gaussianReal 0 variance
  let centered : ℝ → ℝ := fun score ↦ f score - c
  let density : ℝ → ENNReal :=
    fun score ↦ ENNReal.ofReal (max (-centered score) 0)
  have hdensityMeasurable : AEMeasurable density baseLaw := by
    dsimp [density, centered]
    fun_prop
  have hdensityFinite : ∀ᵐ score ∂baseLaw, density score < ∞ :=
    Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top
  rw [show LG21TestOptionalPolicies.lg21NegativeDensityMeasure baseLaw centered =
      baseLaw.withDensity density by rfl,
    integrable_withDensity_iff_integrable_smul₀' hdensityMeasurable hdensityFinite]
  have hWeighted :=
    integrable_exp_mul_sub_const_of_integrable_all_gaussian_shifts f c variance hshift tilt
  have hNegative :
      Integrable (fun score ↦ max (-(rexp (tilt * score) * centered score)) 0) baseLaw := by
    simpa [baseLaw, centered, neg_mul] using hWeighted.neg.pos_part
  convert hNegative using 1
  ext score
  change (ENNReal.ofReal (max (-centered score) 0)).toReal * rexp (tilt * score) = _
  rw [ENNReal.toReal_ofReal (le_max_right _ _)]
  rw [max_mul_of_nonneg _ _ (Real.exp_nonneg _)]
  ring_nf

/--
The four regularity side conditions consumed by
`ae_eq_const_of_positive_mass_gaussian_convolution` follow from integrability
under every shift.  Nondegeneracy is retained in this interface because the
rigidity theorem also uses it for its analytic-identification step; the
integrability derivation itself is valid even at zero variance.
-/
theorem gaussian_convolution_regularities_of_integrable_all_gaussian_shifts
    (f : ℝ → ℝ) (c : ℝ) (variance : NNReal)
    (_hvariance : variance ≠ 0)
    (hshift : ∀ mean, Integrable f (gaussianReal mean variance)) :
    IsFiniteMeasure
        (LG21TestOptionalPolicies.lg21PositiveDensityMeasure
          (gaussianReal 0 variance) (fun score ↦ f score - c)) ∧
      IsFiniteMeasure
        (LG21TestOptionalPolicies.lg21NegativeDensityMeasure
          (gaussianReal 0 variance) (fun score ↦ f score - c)) ∧
      (∀ tilt : ℝ,
        Integrable (fun score : ℝ ↦ rexp (tilt * score))
          (LG21TestOptionalPolicies.lg21PositiveDensityMeasure
            (gaussianReal 0 variance) (fun score ↦ f score - c))) ∧
      ∀ tilt : ℝ,
        Integrable (fun score : ℝ ↦ rexp (tilt * score))
          (LG21TestOptionalPolicies.lg21NegativeDensityMeasure
            (gaussianReal 0 variance) (fun score ↦ f score - c)) := by
  exact ⟨
    isFiniteMeasure_positive_density_sub_const_of_integrable_all_gaussian_shifts
      f c variance hshift,
    isFiniteMeasure_negative_density_sub_const_of_integrable_all_gaussian_shifts
      f c variance hshift,
    integrable_exp_mul_positive_density_sub_const_of_integrable_all_gaussian_shifts
      f c variance hshift,
    integrable_exp_mul_negative_density_sub_const_of_integrable_all_gaussian_shifts
      f c variance hshift⟩

end

end GaussianConvolutionRigidity
