import LG21TestOptionalPolicies.GaussianConvolutionRigidity
import Mathlib.Probability.Moments.Tilted

/-!
# Exponential tilting of a Gaussian law

This module proves the measure identity behind the Gaussian reweighting step:
exponentially tilting `N(0, v)` by `x ↦ t * x` produces `N(v * t, v)`.
The proof uses real MGFs, Mathlib's tilted-integral formula, and the verified
complex-MGF extensionality route from `GaussianWeierstrassRigidity`.
-/

namespace GaussianConvolutionRigidity

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

/--
At a real tilt, the signed complex MGF is the exponentially weighted integral
of the underlying signed density.  The positive and negative density measures
keep the argument within ordinary positive-measure APIs.
-/
theorem signedDensityComplexMGF_ofReal_eq_integral
    {μ : Measure ℝ} [SigmaFinite μ]
    (f : ℝ → ℝ) (hf : AEMeasurable f μ) (t : ℝ)
    (hposExp : Integrable (fun score : ℝ ↦ rexp (t * score))
      (LG21TestOptionalPolicies.lg21PositiveDensityMeasure μ f))
    (hnegExp : Integrable (fun score : ℝ ↦ rexp (t * score))
      (LG21TestOptionalPolicies.lg21NegativeDensityMeasure μ f)) :
    signedDensityComplexMGF μ f (t : ℂ) =
      (∫ score, rexp (t * score) * f score ∂μ : ℂ) := by
  let positiveDensity : ℝ → ENNReal :=
    fun score ↦ ENNReal.ofReal (max (f score) 0)
  let negativeDensity : ℝ → ENNReal :=
    fun score ↦ ENNReal.ofReal (max (-f score) 0)
  let positiveLaw : Measure ℝ := μ.withDensity positiveDensity
  let negativeLaw : Measure ℝ := μ.withDensity negativeDensity
  have hpositiveDensityMeasurable : AEMeasurable positiveDensity μ := by
    dsimp [positiveDensity]
    fun_prop
  have hnegativeDensityMeasurable : AEMeasurable negativeDensity μ := by
    dsimp [negativeDensity]
    fun_prop
  have hpositiveDensityFinite : ∀ᵐ score ∂μ, positiveDensity score < ∞ :=
    Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have hnegativeDensityFinite : ∀ᵐ score ∂μ, negativeDensity score < ∞ :=
    Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have hpositiveExpBase :
      Integrable (fun score ↦ max (f score) 0 * rexp (t * score)) μ := by
    have h :=
      (integrable_withDensity_iff_integrable_smul₀'
        hpositiveDensityMeasurable hpositiveDensityFinite).mp (by
          simpa [positiveLaw,
            LG21TestOptionalPolicies.lg21PositiveDensityMeasure,
            positiveDensity] using hposExp)
    convert h using 1
    ext score
    change max (f score) 0 * rexp (t * score) =
      (ENNReal.ofReal (max (f score) 0)).toReal * rexp (t * score)
    rw [ENNReal.toReal_ofReal (le_max_right _ _)]
  have hnegativeExpBase :
      Integrable (fun score ↦ max (-f score) 0 * rexp (t * score)) μ := by
    have h :=
      (integrable_withDensity_iff_integrable_smul₀'
        hnegativeDensityMeasurable hnegativeDensityFinite).mp (by
          simpa [negativeLaw,
            LG21TestOptionalPolicies.lg21NegativeDensityMeasure,
            negativeDensity] using hnegExp)
    convert h using 1
    ext score
    change max (-f score) 0 * rexp (t * score) =
      (ENNReal.ofReal (max (-f score) 0)).toReal * rexp (t * score)
    rw [ENNReal.toReal_ofReal (le_max_right _ _)]
  have hpositiveMGF :
      mgf id positiveLaw t =
        ∫ score, max (f score) 0 * rexp (t * score) ∂μ := by
    unfold mgf
    rw [integral_withDensity_eq_integral_toReal_smul₀
      hpositiveDensityMeasurable hpositiveDensityFinite]
    apply integral_congr_ae
    filter_upwards with score
    change (ENNReal.ofReal (max (f score) 0)).toReal * rexp (t * score) =
      max (f score) 0 * rexp (t * score)
    rw [ENNReal.toReal_ofReal (le_max_right _ _)]
  have hnegativeMGF :
      mgf id negativeLaw t =
        ∫ score, max (-f score) 0 * rexp (t * score) ∂μ := by
    unfold mgf
    rw [integral_withDensity_eq_integral_toReal_smul₀
      hnegativeDensityMeasurable hnegativeDensityFinite]
    apply integral_congr_ae
    filter_upwards with score
    change (ENNReal.ofReal (max (-f score) 0)).toReal * rexp (t * score) =
      max (-f score) 0 * rexp (t * score)
    rw [ENNReal.toReal_ofReal (le_max_right _ _)]
  have hsplit :
      (∫ score, max (f score) 0 * rexp (t * score) ∂μ) -
          ∫ score, max (-f score) 0 * rexp (t * score) ∂μ =
        ∫ score, rexp (t * score) * f score ∂μ := by
    rw [← integral_sub hpositiveExpBase hnegativeExpBase]
    apply integral_congr_ae
    filter_upwards with score
    calc
      max (f score) 0 * rexp (t * score) -
          max (-f score) 0 * rexp (t * score) =
        (max (f score) 0 - max (-f score) 0) * rexp (t * score) := by ring
      _ = f score * rexp (t * score) := by
        rw [LG21TestOptionalPolicies.lg21_sub_pos_neg_eq_self]
      _ = rexp (t * score) * f score := by ring
  rw [signedDensityComplexMGF]
  change complexMGF id positiveLaw (t : ℂ) -
      complexMGF id negativeLaw (t : ℂ) = _
  rw [complexMGF_ofReal, complexMGF_ofReal, hpositiveMGF, hnegativeMGF]
  exact_mod_cast hsplit

/-- Exponential tilting sends a centered real Gaussian to the corresponding shifted Gaussian. -/
theorem tilted_centered_gaussian_eq_gaussianReal
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

/--
The Gaussian convolution at mean `v * t` is the centered signed MGF at `t`,
multiplied by the Gaussian normalizing factor.  This is the exact reweighting
identity used by the source-agnostic rigidity theorem.
-/
theorem gaussianConvolution_reweighting_identity
    (variance : NNReal) (tilt : ℝ) (f : ℝ → ℝ)
    (hf : AEMeasurable f (gaussianReal 0 variance))
    (hposExp : Integrable (fun score : ℝ ↦ rexp (tilt * score))
      (LG21TestOptionalPolicies.lg21PositiveDensityMeasure
        (gaussianReal 0 variance) f))
    (hnegExp : Integrable (fun score : ℝ ↦ rexp (tilt * score))
      (LG21TestOptionalPolicies.lg21NegativeDensityMeasure
        (gaussianReal 0 variance) f)) :
    (rexp (-((variance : ℝ) * tilt ^ 2 / 2)) : ℂ) *
        signedDensityComplexMGF (gaussianReal 0 variance) f (tilt : ℂ) =
      (gaussianConvolution f variance ((variance : ℝ) * tilt) : ℂ) := by
  let baseLaw : Measure ℝ := gaussianReal 0 variance
  let tiltedLaw : Measure ℝ := baseLaw.tilted (fun score ↦ tilt * score)
  let shiftedLaw : Measure ℝ := gaussianReal ((variance : ℝ) * tilt) variance
  have htiltedEq : tiltedLaw = shiftedLaw := by
    simpa [tiltedLaw, shiftedLaw, baseLaw] using
      tilted_centered_gaussian_eq_gaussianReal variance tilt
  have hmgfBase : mgf id baseLaw tilt =
      rexp ((variance : ℝ) * tilt ^ 2 / 2) := by
    rw [show baseLaw = gaussianReal 0 variance by rfl, mgf_id_gaussianReal]
    ring_nf
  have hconvolutionTilted :
      gaussianConvolution f variance ((variance : ℝ) * tilt) =
        ∫ score, f score ∂tiltedLaw := by
    unfold gaussianConvolution
    rw [htiltedEq]
  have htiltedIntegral :
      (∫ score, f score ∂tiltedLaw) =
        ∫ score,
          (rexp (tilt * score) / mgf id baseLaw tilt) • f score ∂baseLaw := by
    rw [show tiltedLaw = baseLaw.tilted (fun score ↦ tilt * score) by rfl]
    simpa [id_eq] using
      (integral_tilted_mul_eq_mgf (μ := baseLaw) (X := id) (t := tilt) f)
  have hweightedIntegral :
      (∫ score,
          (rexp (tilt * score) / mgf id baseLaw tilt) * f score ∂baseLaw) =
        rexp (-((variance : ℝ) * tilt ^ 2 / 2)) *
          ∫ score, rexp (tilt * score) * f score ∂baseLaw := by
    rw [hmgfBase]
    calc
      (∫ score,
          (rexp (tilt * score) / rexp ((variance : ℝ) * tilt ^ 2 / 2)) *
              f score ∂baseLaw) =
          ∫ score,
            rexp (-((variance : ℝ) * tilt ^ 2 / 2)) *
              (rexp (tilt * score) * f score) ∂baseLaw := by
        apply integral_congr_ae
        filter_upwards with score
        calc
          (rexp (tilt * score) /
              rexp ((variance : ℝ) * tilt ^ 2 / 2)) * f score =
              rexp (tilt * score - (variance : ℝ) * tilt ^ 2 / 2) * f score := by
            rw [← Real.exp_sub]
          _ = (rexp (-((variance : ℝ) * tilt ^ 2 / 2)) *
              rexp (tilt * score)) * f score := by
            congr 1
            rw [← Real.exp_add]
            congr 1
            ring
          _ = rexp (-((variance : ℝ) * tilt ^ 2 / 2)) *
              (rexp (tilt * score) * f score) := by ring
      _ = _ := integral_const_mul _ _
  have hsignedMGF :=
    signedDensityComplexMGF_ofReal_eq_integral (μ := baseLaw) f
      (by simpa [baseLaw] using hf) tilt
      (by simpa [baseLaw] using hposExp)
      (by simpa [baseLaw] using hnegExp)
  have hconvolution :
      gaussianConvolution f variance ((variance : ℝ) * tilt) =
        rexp (-((variance : ℝ) * tilt ^ 2 / 2)) *
          ∫ score, rexp (tilt * score) * f score ∂baseLaw := by
    calc
      gaussianConvolution f variance ((variance : ℝ) * tilt) =
          ∫ score, f score ∂tiltedLaw := hconvolutionTilted
      _ = ∫ score,
          (rexp (tilt * score) / mgf id baseLaw tilt) • f score ∂baseLaw :=
        htiltedIntegral
      _ = ∫ score,
          (rexp (tilt * score) / mgf id baseLaw tilt) * f score ∂baseLaw := by
        apply integral_congr_ae
        filter_upwards with score
        simp only [smul_eq_mul]
      _ = _ := hweightedIntegral
  rw [hsignedMGF]
  exact_mod_cast hconvolution.symm

/--
The reweighting identity at an arbitrary shifted-Gaussian mean.  This is the
exact equation consumed by `ae_eq_const_of_positive_mass_gaussian_convolution`.
-/
theorem gaussianConvolution_reweighting_identity_at_mean
    (variance : NNReal) (hvariance : variance ≠ 0) (mean : ℝ) (f : ℝ → ℝ)
    (hf : AEMeasurable f (gaussianReal 0 variance))
    (hposExp : Integrable
      (fun score : ℝ ↦ rexp ((mean / (variance : ℝ)) * score))
      (LG21TestOptionalPolicies.lg21PositiveDensityMeasure
        (gaussianReal 0 variance) f))
    (hnegExp : Integrable
      (fun score : ℝ ↦ rexp ((mean / (variance : ℝ)) * score))
      (LG21TestOptionalPolicies.lg21NegativeDensityMeasure
        (gaussianReal 0 variance) f)) :
    (rexp (-(mean ^ 2) / (2 * (variance : ℝ))) : ℂ) *
        signedDensityComplexMGF (gaussianReal 0 variance) f
          (gaussianTiltParameter variance mean) =
      (gaussianConvolution f variance mean : ℂ) := by
  have hvarianceReal : (variance : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hvariance
  have hmean : (variance : ℝ) * (mean / (variance : ℝ)) = mean := by
    field_simp
  have hsquare :
      (variance : ℝ) * (mean / (variance : ℝ)) ^ 2 / 2 =
        mean ^ 2 / (2 * (variance : ℝ)) := by
    field_simp
  have hnegSquare :
      -(mean ^ 2 / (2 * (variance : ℝ))) =
        -mean ^ 2 / (2 * (variance : ℝ)) := by ring
  simpa [gaussianTiltParameter, hmean, hsquare, hnegSquare] using
    (gaussianConvolution_reweighting_identity variance
      (mean / (variance : ℝ)) f hf hposExp hnegExp)

end

end GaussianConvolutionRigidity
