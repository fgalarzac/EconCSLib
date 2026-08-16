import LG21TestOptionalPolicies.SelectedGaussianLikelihoodRegularity
import Mathlib.Analysis.Convex.Integral

/-!
# Gaussian-shift integrability of a selected Gaussian posterior

This module discharges the integrability side condition for the canonical
Gaussian selected posterior.  The proof uses the actual fixed quadratic
likelihood factor: after selection, that factor makes the latent likelihood
base strictly sub-Gaussian.  It therefore cannot be replaced by a generic
``posterior integrable'' model field.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

/-! ## Reusable quadratic Gaussian estimates -/

/-- A real exponential with a strictly negative quadratic coefficient is
integrable against Lebesgue measure. -/
private theorem lg21_integrable_exp_quadratic_volume
    (quadratic linear constant : ℝ) (hquadratic : quadratic < 0) :
    Integrable (fun x : ℝ =>
      Real.exp (quadratic * x ^ 2 + linear * x + constant)) := by
  let decay : ℝ := -quadratic
  have hdecay : 0 < decay := neg_pos.mpr hquadratic
  have hbase : Integrable (fun x : ℝ => Real.exp (-decay * x ^ 2)) :=
    integrable_exp_neg_mul_sq hdecay
  have hshift : Integrable (fun x : ℝ =>
      Real.exp (-decay * (x - linear / (2 * decay)) ^ 2)) :=
    hbase.comp_sub_right (linear / (2 * decay))
  have hscaled := hshift.const_mul
    (Real.exp (constant + linear ^ 2 / (4 * decay)))
  convert hscaled using 1
  ext x
  rw [← Real.exp_add]
  congr 1
  dsimp [decay]
  have hquadratic_ne : quadratic ≠ 0 := ne_of_lt hquadratic
  field_simp [hquadratic_ne]
  ring

/-- A Gaussian has every exponential quadratic moment whose positive
quadratic coefficient remains below its density decay. -/
private theorem lg21_integrable_exp_quadratic_gaussian
    (mean quadratic linear : ℝ) (variance : NNReal)
    (hvariance : variance ≠ 0)
    (hquadratic : quadratic < 1 / (2 * (variance : ℝ))) :
    Integrable (fun x : ℝ => Real.exp (quadratic * x ^ 2 + linear * x))
      (gaussianReal mean variance) := by
  rw [gaussianReal_of_var_ne_zero mean hvariance,
    integrable_withDensity_iff
      (measurable_gaussianPDF mean variance)
      (Filter.Eventually.of_forall fun _ => gaussianPDF_lt_top)]
  have hcoefficient : quadratic - 1 / (2 * (variance : ℝ)) < 0 := by
    linarith
  have hquadraticIntegral := lg21_integrable_exp_quadratic_volume
    (quadratic - 1 / (2 * (variance : ℝ)))
    (linear + mean / variance) (-mean ^ 2 / (2 * variance)) hcoefficient
  convert hquadraticIntegral.const_mul
    ((Real.sqrt (2 * Real.pi * (variance : ℝ)))⁻¹) using 1
  ext x
  simp only [toReal_gaussianPDF, gaussianPDFReal]
  rw [← mul_assoc, mul_comm (Real.exp (quadratic * x ^ 2 + linear * x)),
    mul_assoc, ← Real.exp_add]
  congr 1
  field_simp [hvariance]
  ring_nf

/-! ## Selected likelihood-base envelopes -/

/-- Jensen's lower bound on the exponential moment of an integrable real
random variable under a probability law. -/
private theorem lg21_exp_integral_le_mgf
    (law : Measure ℝ) [IsProbabilityMeasure law]
    (hintegrable : Integrable id law)
    (tilt : ℝ)
    (hexp : Integrable (fun skill : ℝ => Real.exp (tilt * skill)) law) :
    Real.exp (tilt * (∫ skill, skill ∂law)) ≤
      ∫ skill, Real.exp (tilt * skill) ∂law := by
  have hlinear : Integrable (fun skill : ℝ => tilt * skill) law := by
    simpa [id_eq] using hintegrable.const_mul tilt
  have hjensen := convexOn_exp.map_integral_le
    (μ := law) (f := fun skill : ℝ => tilt * skill)
    Real.continuous_exp.continuousOn isClosed_univ
    (Filter.Eventually.of_forall fun skill => Set.mem_univ skill)
    hlinear hexp
  rw [integral_const_mul] at hjensen
  exact hjensen

/-- Exponential moments at `-1` and `1` give first-moment integrability of
the selected likelihood base. -/
private theorem lg21_selectedGaussianLikelihoodBase_integrable_id
    (priorMean : ℝ) (priorVariance : NNReal) (selected : Set ℝ)
    (noiseVariance : ℝ)
    (hselected : 0 < gaussianReal priorMean priorVariance selected)
    (hnoise : 0 < noiseVariance) :
    Integrable id
      (lg21GaussianLikelihoodBase
        (lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected)
        noiseVariance) := by
  let likelihoodBase : Measure ℝ :=
    lg21GaussianLikelihoodBase
      (lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected)
      noiseVariance
  have hplus : Integrable (fun skill : ℝ => Real.exp skill) likelihoodBase := by
    simpa [likelihoodBase] using
      (lg21_selectedGaussianLikelihoodBase_integrable_exp
        priorMean priorVariance selected noiseVariance 1 hselected hnoise)
  have hminus : Integrable (fun skill : ℝ => Real.exp (-skill)) likelihoodBase := by
    simpa [likelihoodBase] using
      (lg21_selectedGaussianLikelihoodBase_integrable_exp
        priorMean priorVariance selected noiseVariance (-1) hselected hnoise)
  have hsum : Integrable (fun skill : ℝ =>
      Real.exp skill + Real.exp (-skill)) likelihoodBase := hplus.add hminus
  change Integrable (fun skill : ℝ => skill) likelihoodBase
  apply Integrable.mono' hsum (by fun_prop)
  filter_upwards with skill
  rw [Real.norm_eq_abs]
  by_cases hskill : 0 ≤ skill
  · rw [abs_of_nonneg hskill]
    have hle : skill ≤ Real.exp skill := by
      nlinarith [Real.add_one_le_exp skill]
    exact hle.trans (le_add_of_nonneg_right (Real.exp_nonneg _))
  · rw [abs_of_neg (lt_of_not_ge hskill)]
    have hle : -skill ≤ Real.exp (-skill) := by
      nlinarith [Real.add_one_le_exp (-skill)]
    exact hle.trans (le_add_of_nonneg_left (Real.exp_nonneg _))

/-- A first-degree factor is absorbed by neighboring exponential tilts. -/
private theorem lg21_abs_le_exp_add_exp_neg (x : ℝ) :
    |x| ≤ Real.exp x + Real.exp (-x) := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    have hle : x ≤ Real.exp x := by
      nlinarith [Real.add_one_le_exp x]
    exact hle.trans (le_add_of_nonneg_right (Real.exp_nonneg _))
  · rw [abs_of_neg (lt_of_not_ge hx)]
    have hle : -x ≤ Real.exp (-x) := by
      nlinarith [Real.add_one_le_exp (-x)]
    exact hle.trans (le_add_of_nonneg_left (Real.exp_nonneg _))

/-- Pointwise envelope for the absolute tilted first moment. -/
private theorem lg21_tilted_weighted_abs_le
    (tilt skill normalizer : ℝ) (hnormalizer : 0 < normalizer) :
    ‖(Real.exp (tilt * skill) / normalizer) • skill‖ ≤
      Real.exp ((tilt + 1) * skill) / normalizer +
        Real.exp ((tilt - 1) * skill) / normalizer := by
  simp only [smul_eq_mul, Real.norm_eq_abs]
  rw [abs_mul, abs_of_nonneg (div_nonneg (Real.exp_nonneg _) hnormalizer.le),
    ← add_div]
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff_of_pos_right hnormalizer).mpr
  calc
    Real.exp (tilt * skill) * |skill| ≤
        Real.exp (tilt * skill) *
          (Real.exp skill + Real.exp (-skill)) :=
      mul_le_mul_of_nonneg_left (lg21_abs_le_exp_add_exp_neg skill)
        (Real.exp_nonneg _)
    _ = Real.exp ((tilt + 1) * skill) +
        Real.exp ((tilt - 1) * skill) := by
      rw [mul_add, ← Real.exp_add, ← Real.exp_add]
      congr 2 <;> ring

/-- A sub-Gaussian exponential-moment envelope controls the absolute mean
under every further exponential tilt.  Jensen supplies the normalizer lower
bound, so this estimate does not use a pointwise conditional-distribution
choice. -/
private theorem lg21_tiltedMean_abs_le_of_mgf_envelope
    (law : Measure ℝ) [IsProbabilityMeasure law]
    (hintegrable : Integrable id law)
    (hexp : ∀ tilt : ℝ,
      Integrable (fun skill : ℝ => Real.exp (tilt * skill)) law)
    (constant beta : ℝ) (hconstant : 0 ≤ constant)
    (hmoment : ∀ tilt : ℝ,
      (∫ skill, Real.exp (tilt * skill) ∂law) ≤
        constant * Real.exp (beta * tilt ^ 2 / 2)) :
    ∀ tilt : ℝ,
      |∫ skill, skill ∂law.tilted (fun skill => tilt * skill)| ≤
        constant * Real.exp
          (beta * (tilt + 1) ^ 2 / 2 -
            tilt * (∫ skill, skill ∂law)) +
        constant * Real.exp
          (beta * (tilt - 1) ^ 2 / 2 -
            tilt * (∫ skill, skill ∂law)) := by
  let mean : ℝ := ∫ skill, skill ∂law
  intro tilt
  have htiltExp := hexp tilt
  have hdenomPos : 0 < ∫ skill, Real.exp (tilt * skill) ∂law := by
    letI : NeZero law := ⟨IsProbabilityMeasure.ne_zero law⟩
    exact integral_exp_pos htiltExp
  have hplus : Integrable (fun skill : ℝ =>
      Real.exp ((tilt + 1) * skill) /
        ∫ q, Real.exp (tilt * q) ∂law) law :=
    (hexp (tilt + 1)).div_const _
  have hminus : Integrable (fun skill : ℝ =>
      Real.exp ((tilt - 1) * skill) /
        ∫ q, Real.exp (tilt * q) ∂law) law :=
    (hexp (tilt - 1)).div_const _
  have hright : Integrable (fun skill : ℝ =>
      Real.exp ((tilt + 1) * skill) /
          ∫ q, Real.exp (tilt * q) ∂law +
        Real.exp ((tilt - 1) * skill) /
          ∫ q, Real.exp (tilt * q) ∂law) law :=
    hplus.add hminus
  have hweighted : Integrable (fun skill : ℝ =>
      (Real.exp (tilt * skill) /
        ∫ q, Real.exp (tilt * q) ∂law) • skill) law := by
    apply Integrable.mono' hright (by fun_prop)
    filter_upwards with skill
    exact lg21_tilted_weighted_abs_le tilt skill _ hdenomPos
  have hleftNorm : Integrable (fun skill : ℝ =>
      ‖(Real.exp (tilt * skill) /
        ∫ q, Real.exp (tilt * q) ∂law) • skill‖) law :=
    hweighted.norm
  rw [integral_tilted]
  calc
    |∫ skill, (Real.exp (tilt * skill) /
      ∫ q, Real.exp (tilt * q) ∂law) • skill ∂law| ≤
        ∫ skill, ‖(Real.exp (tilt * skill) /
          ∫ q, Real.exp (tilt * q) ∂law) • skill‖ ∂law :=
      by
        simpa [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm
            (fun skill : ℝ =>
              (Real.exp (tilt * skill) /
                ∫ q, Real.exp (tilt * q) ∂law) • skill))
    _ ≤ ∫ skill,
        Real.exp ((tilt + 1) * skill) /
            ∫ q, Real.exp (tilt * q) ∂law +
          Real.exp ((tilt - 1) * skill) /
            ∫ q, Real.exp (tilt * q) ∂law ∂law :=
      integral_mono hleftNorm hright
        (fun skill => lg21_tilted_weighted_abs_le tilt skill _ hdenomPos)
    _ =
        ((∫ skill, Real.exp ((tilt + 1) * skill) ∂law) /
          ∫ q, Real.exp (tilt * q) ∂law) +
        ((∫ skill, Real.exp ((tilt - 1) * skill) ∂law) /
          ∫ q, Real.exp (tilt * q) ∂law) := by
      rw [integral_add hplus hminus, integral_div, integral_div]
    _ ≤ constant * Real.exp
          (beta * (tilt + 1) ^ 2 / 2 - tilt * mean) +
        constant * Real.exp
          (beta * (tilt - 1) ^ 2 / 2 - tilt * mean) := by
      have hjensen := lg21_exp_integral_le_mgf law hintegrable tilt htiltExp
      change _ ≤ constant * Real.exp
          (beta * (tilt + 1) ^ 2 / 2 - tilt * mean) +
        constant * Real.exp
          (beta * (tilt - 1) ^ 2 / 2 - tilt * mean)
      have hplusRatio :
          (∫ skill, Real.exp ((tilt + 1) * skill) ∂law) /
            ∫ q, Real.exp (tilt * q) ∂law ≤
            constant * Real.exp
              (beta * (tilt + 1) ^ 2 / 2 - tilt * mean) := by
        calc
          (∫ skill, Real.exp ((tilt + 1) * skill) ∂law) /
              ∫ q, Real.exp (tilt * q) ∂law ≤
              (constant * Real.exp (beta * (tilt + 1) ^ 2 / 2)) /
                ∫ q, Real.exp (tilt * q) ∂law :=
            div_le_div_of_nonneg_right (hmoment (tilt + 1)) hdenomPos.le
          _ ≤ (constant * Real.exp (beta * (tilt + 1) ^ 2 / 2)) /
                Real.exp (tilt * mean) :=
            div_le_div_of_nonneg_left
              (mul_nonneg hconstant (Real.exp_nonneg _))
              (Real.exp_pos _) (by simpa [mean] using hjensen)
          _ = constant * Real.exp
              (beta * (tilt + 1) ^ 2 / 2 - tilt * mean) := by
            rw [mul_div_assoc, ← Real.exp_sub]
      have hminusRatio :
          (∫ skill, Real.exp ((tilt - 1) * skill) ∂law) /
            ∫ q, Real.exp (tilt * q) ∂law ≤
            constant * Real.exp
              (beta * (tilt - 1) ^ 2 / 2 - tilt * mean) := by
        calc
          (∫ skill, Real.exp ((tilt - 1) * skill) ∂law) /
              ∫ q, Real.exp (tilt * q) ∂law ≤
              (constant * Real.exp (beta * (tilt - 1) ^ 2 / 2)) /
                ∫ q, Real.exp (tilt * q) ∂law :=
            div_le_div_of_nonneg_right (hmoment (tilt - 1)) hdenomPos.le
          _ ≤ (constant * Real.exp (beta * (tilt - 1) ^ 2 / 2)) /
                Real.exp (tilt * mean) :=
            div_le_div_of_nonneg_left
              (mul_nonneg hconstant (Real.exp_nonneg _))
              (Real.exp_pos _) (by simpa [mean] using hjensen)
          _ = constant * Real.exp
              (beta * (tilt - 1) ^ 2 / 2 - tilt * mean) := by
            rw [mul_div_assoc, ← Real.exp_sub]
      linarith

/-- A positive-mass Gaussian selection inherits every subcritical positive
quadratic exponential moment. -/
private theorem lg21_selectedGaussian_integrable_exp_quadratic
    (priorMean quadratic : ℝ) (priorVariance : NNReal) (selected : Set ℝ)
    (hprior : priorVariance ≠ 0)
    (hselected : 0 < gaussianReal priorMean priorVariance selected)
    (hquadratic : quadratic < 1 / (2 * (priorVariance : ℝ))) :
    Integrable (fun skill : ℝ => Real.exp (quadratic * skill ^ 2))
      (lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected) := by
  have hpriorQuadratic : Integrable
      (fun skill : ℝ => Real.exp (quadratic * skill ^ 2))
      (gaussianReal priorMean priorVariance) := by
    simpa using
      (lg21_integrable_exp_quadratic_gaussian
        priorMean quadratic 0 priorVariance hprior hquadratic)
  unfold lg21NormalizedRestriction
  exact hpriorQuadratic.restrict.smul_measure
    (ENNReal.inv_ne_top.mpr (ne_of_gt hselected))

/-- The selected likelihood base has a finite positive quadratic exponential
moment whenever the exponent stays below the prior Gaussian density decay. -/
private theorem lg21_selectedGaussianLikelihoodBase_integrable_exp_quadratic
    (priorMean quadratic : ℝ) (priorVariance : NNReal) (selected : Set ℝ)
    (noiseVariance : ℝ)
    (hprior : priorVariance ≠ 0)
    (hselected : 0 < gaussianReal priorMean priorVariance selected)
    (hnoise : 0 < noiseVariance)
    (hquadratic : quadratic < 1 / (2 * (priorVariance : ℝ))) :
    Integrable (fun skill : ℝ => Real.exp (quadratic * skill ^ 2))
      (lg21GaussianLikelihoodBase
        (lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected)
        noiseVariance) := by
  let selectedLaw : Measure ℝ :=
    lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected
  let likelihoodBase : Measure ℝ :=
    lg21GaussianLikelihoodBase selectedLaw noiseVariance
  let fixedLikelihood : ℝ → ℝ :=
    fun skill => -skill ^ 2 / (2 * noiseVariance)
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability
      (gaussianReal priorMean priorVariance) selected (ne_of_gt hselected)
      (measure_ne_top _ _)
  have hfixed : Integrable (fun skill : ℝ => Real.exp (fixedLikelihood skill))
      selectedLaw := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with skill
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_one_iff.mpr
    dsimp [fixedLikelihood]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg skill))
      (by positivity)
  have hselectedQuadratic : Integrable
      (fun skill : ℝ => Real.exp (quadratic * skill ^ 2)) selectedLaw := by
    simpa [selectedLaw] using
      (lg21_selectedGaussian_integrable_exp_quadratic
        priorMean quadratic priorVariance selected hprior hselected hquadratic)
  change Integrable (fun skill : ℝ => Real.exp (quadratic * skill ^ 2))
    likelihoodBase
  rw [show likelihoodBase = selectedLaw.tilted fixedLikelihood by rfl,
    integrable_tilted_iff hfixed]
  apply Integrable.mono' hselectedQuadratic
    (by fun_prop : AEStronglyMeasurable
      (fun skill : ℝ =>
        Real.exp (fixedLikelihood skill) •
          Real.exp (quadratic * skill ^ 2)) selectedLaw)
  filter_upwards with skill
  rw [Real.norm_eq_abs]
  have hnonneg : 0 ≤ Real.exp (fixedLikelihood skill) *
      Real.exp (quadratic * skill ^ 2) := by positivity
  rw [smul_eq_mul, abs_of_nonneg hnonneg]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp [fixedLikelihood]
  have hfixed_nonpos : -skill ^ 2 / (2 * noiseVariance) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg skill))
      (by positivity)
  nlinarith

/-- The fixed Gaussian likelihood factor supplies the strict quadratic
improvement in the likelihood-base moment bound. -/
private theorem lg21_likelihood_tilt_pointwise_le
    (noiseVariance beta tilt skill : ℝ) (hbeta : 0 < beta) :
    Real.exp (-skill ^ 2 / (2 * noiseVariance) + tilt * skill) ≤
      Real.exp (beta * tilt ^ 2 / 2) *
        Real.exp ((1 / (2 * beta) - 1 / (2 * noiseVariance)) * skill ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hyoung : tilt * skill ≤ beta * tilt ^ 2 / 2 + skill ^ 2 / (2 * beta) := by
    field_simp [ne_of_gt hbeta]
    nlinarith [sq_nonneg (beta * tilt - skill)]
  calc
    -skill ^ 2 / (2 * noiseVariance) + tilt * skill =
        tilt * skill + -skill ^ 2 / (2 * noiseVariance) := by ring
    _ ≤ (beta * tilt ^ 2 / 2 + skill ^ 2 / (2 * beta)) +
          -skill ^ 2 / (2 * noiseVariance) :=
      by linarith
    _ = beta * tilt ^ 2 / 2 +
        (1 / (2 * beta) - 1 / (2 * noiseVariance)) * skill ^ 2 := by
      ring

/-- Uniform sub-Gaussian moment envelope for the selected likelihood base.
The only free coefficient is explicitly required to remain below the prior
Gaussian density decay. -/
private theorem lg21_selectedGaussianLikelihoodBase_mgf_le
    (priorMean : ℝ) (priorVariance : NNReal) (selected : Set ℝ)
    (noiseVariance beta : ℝ)
    (hprior : priorVariance ≠ 0)
    (hselected : 0 < gaussianReal priorMean priorVariance selected)
    (hnoise : 0 < noiseVariance) (hbeta : 0 < beta)
    (hquadratic :
      1 / (2 * beta) - 1 / (2 * noiseVariance) <
        1 / (2 * (priorVariance : ℝ))) :
    let selectedLaw :=
      lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected
    let likelihoodBase :=
      lg21GaussianLikelihoodBase selectedLaw noiseVariance
    ∀ tilt : ℝ,
      (∫ skill, Real.exp (tilt * skill) ∂likelihoodBase) ≤
        ((∫ skill, Real.exp
          ((1 / (2 * beta) - 1 / (2 * noiseVariance)) * skill ^ 2)
          ∂selectedLaw) /
          (∫ skill, Real.exp (-skill ^ 2 / (2 * noiseVariance)) ∂selectedLaw)) *
          Real.exp (beta * tilt ^ 2 / 2) := by
  let selectedLaw : Measure ℝ :=
    lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected
  let likelihoodBase : Measure ℝ :=
    lg21GaussianLikelihoodBase selectedLaw noiseVariance
  let fixedLikelihood : ℝ → ℝ :=
    fun skill => -skill ^ 2 / (2 * noiseVariance)
  let quadratic : ℝ := 1 / (2 * beta) - 1 / (2 * noiseVariance)
  change ∀ tilt : ℝ,
    (∫ skill, Real.exp (tilt * skill) ∂likelihoodBase) ≤
      ((∫ skill, Real.exp (quadratic * skill ^ 2) ∂selectedLaw) /
        (∫ skill, Real.exp (fixedLikelihood skill) ∂selectedLaw)) *
        Real.exp (beta * tilt ^ 2 / 2)
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability
      (gaussianReal priorMean priorVariance) selected (ne_of_gt hselected)
      (measure_ne_top _ _)
  letI : NeZero selectedLaw := ⟨IsProbabilityMeasure.ne_zero selectedLaw⟩
  have hfixed : Integrable (fun skill : ℝ => Real.exp (fixedLikelihood skill))
      selectedLaw := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with skill
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_one_iff.mpr
    dsimp [fixedLikelihood]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg skill))
      (by positivity)
  have hquadraticIntegral : Integrable
      (fun skill : ℝ => Real.exp (quadratic * skill ^ 2)) selectedLaw := by
    simpa [selectedLaw, quadratic] using
      (lg21_selectedGaussian_integrable_exp_quadratic
        priorMean quadratic priorVariance selected hprior hselected
        (by simpa [quadratic] using hquadratic))
  have hdenominatorPos : 0 <
      ∫ skill, Real.exp (fixedLikelihood skill) ∂selectedLaw :=
    integral_exp_pos hfixed
  intro tilt
  have hupper : Integrable (fun skill : ℝ =>
      Real.exp (beta * tilt ^ 2 / 2) *
        Real.exp (quadratic * skill ^ 2)) selectedLaw :=
    hquadraticIntegral.const_mul _
  have hnumerator : Integrable (fun skill : ℝ =>
      Real.exp ((fixedLikelihood + fun q => tilt * q) skill)) selectedLaw := by
    apply Integrable.mono' hupper (by fun_prop)
    filter_upwards with skill
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_nonneg _)]
    simpa [fixedLikelihood, quadratic, Pi.add_apply] using
      (lg21_likelihood_tilt_pointwise_le
        noiseVariance beta tilt skill hbeta)
  have hnumeratorLe :
      (∫ skill, Real.exp ((fixedLikelihood + fun q => tilt * q) skill)
        ∂selectedLaw) ≤
        Real.exp (beta * tilt ^ 2 / 2) *
          ∫ skill, Real.exp (quadratic * skill ^ 2) ∂selectedLaw := by
    calc
      (∫ skill, Real.exp ((fixedLikelihood + fun q => tilt * q) skill)
        ∂selectedLaw) ≤
          ∫ skill, Real.exp (beta * tilt ^ 2 / 2) *
            Real.exp (quadratic * skill ^ 2) ∂selectedLaw :=
        integral_mono hnumerator hupper (fun skill => by
          simpa [fixedLikelihood, quadratic, Pi.add_apply] using
            (lg21_likelihood_tilt_pointwise_le
              noiseVariance beta tilt skill hbeta))
      _ = Real.exp (beta * tilt ^ 2 / 2) *
          ∫ skill, Real.exp (quadratic * skill ^ 2) ∂selectedLaw := by
        rw [integral_const_mul]
  rw [show likelihoodBase = selectedLaw.tilted fixedLikelihood by rfl,
    integral_exp_tilted]
  calc
    (∫ skill, Real.exp ((fixedLikelihood + fun q => tilt * q) skill)
      ∂selectedLaw) /
        (∫ skill, Real.exp (fixedLikelihood skill) ∂selectedLaw) ≤
        (Real.exp (beta * tilt ^ 2 / 2) *
          ∫ skill, Real.exp (quadratic * skill ^ 2) ∂selectedLaw) /
          (∫ skill, Real.exp (fixedLikelihood skill) ∂selectedLaw) :=
      div_le_div_of_nonneg_right hnumeratorLe hdenominatorPos.le
    _ = ((∫ skill, Real.exp (quadratic * skill ^ 2) ∂selectedLaw) /
      (∫ skill, Real.exp (fixedLikelihood skill) ∂selectedLaw)) *
        Real.exp (beta * tilt ^ 2 / 2) := by
      field_simp [ne_of_gt hdenominatorPos]

/-- Instantiate the generic tilted-mean envelope for a positive-mass Gaussian
selection and its fixed Gaussian likelihood factor. -/
private theorem lg21_selectedGaussianLikelihoodBase_tiltedMean_abs_envelope
    (priorMean : ℝ) (priorVariance : NNReal) (selected : Set ℝ)
    (noiseVariance beta : ℝ)
    (hprior : priorVariance ≠ 0)
    (hselected : 0 < gaussianReal priorMean priorVariance selected)
    (hnoise : 0 < noiseVariance) (hbeta : 0 < beta)
    (hquadratic :
      1 / (2 * beta) - 1 / (2 * noiseVariance) <
        1 / (2 * (priorVariance : ℝ))) :
    let selectedLaw :=
      lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected
    let likelihoodBase :=
      lg21GaussianLikelihoodBase selectedLaw noiseVariance
    ∀ tilt : ℝ,
      |lg21SelectedTiltedMean likelihoodBase tilt| ≤
        ((∫ skill, Real.exp
          ((1 / (2 * beta) - 1 / (2 * noiseVariance)) * skill ^ 2)
          ∂selectedLaw) /
          (∫ skill, Real.exp (-skill ^ 2 / (2 * noiseVariance)) ∂selectedLaw)) *
          Real.exp
            (beta * (tilt + 1) ^ 2 / 2 -
              tilt * (∫ skill, skill ∂likelihoodBase)) +
        ((∫ skill, Real.exp
          ((1 / (2 * beta) - 1 / (2 * noiseVariance)) * skill ^ 2)
          ∂selectedLaw) /
          (∫ skill, Real.exp (-skill ^ 2 / (2 * noiseVariance)) ∂selectedLaw)) *
          Real.exp
            (beta * (tilt - 1) ^ 2 / 2 -
              tilt * (∫ skill, skill ∂likelihoodBase)) := by
  let selectedLaw : Measure ℝ :=
    lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected
  let likelihoodBase : Measure ℝ :=
    lg21GaussianLikelihoodBase selectedLaw noiseVariance
  let fixedLikelihood : ℝ → ℝ :=
    fun skill => -skill ^ 2 / (2 * noiseVariance)
  let quadratic : ℝ := 1 / (2 * beta) - 1 / (2 * noiseVariance)
  change ∀ tilt : ℝ,
    |lg21SelectedTiltedMean likelihoodBase tilt| ≤
      ((∫ skill, Real.exp (quadratic * skill ^ 2) ∂selectedLaw) /
        (∫ skill, Real.exp (fixedLikelihood skill) ∂selectedLaw)) *
        Real.exp
          (beta * (tilt + 1) ^ 2 / 2 -
            tilt * (∫ skill, skill ∂likelihoodBase)) +
      ((∫ skill, Real.exp (quadratic * skill ^ 2) ∂selectedLaw) /
        (∫ skill, Real.exp (fixedLikelihood skill) ∂selectedLaw)) *
        Real.exp
          (beta * (tilt - 1) ^ 2 / 2 -
            tilt * (∫ skill, skill ∂likelihoodBase))
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability
      (gaussianReal priorMean priorVariance) selected (ne_of_gt hselected)
      (measure_ne_top _ _)
  have hfixed : Integrable (fun skill : ℝ => Real.exp (fixedLikelihood skill))
      selectedLaw := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with skill
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_one_iff.mpr
    dsimp [fixedLikelihood]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg skill))
      (by positivity)
  letI : IsProbabilityMeasure likelihoodBase := by
    rw [show likelihoodBase = selectedLaw.tilted fixedLikelihood by rfl]
    exact isProbabilityMeasure_tilted hfixed
  have hbaseId : Integrable id likelihoodBase := by
    simpa [likelihoodBase, selectedLaw] using
      (lg21_selectedGaussianLikelihoodBase_integrable_id
        priorMean priorVariance selected noiseVariance hselected hnoise)
  have hconstantNonneg : 0 ≤
      (∫ skill, Real.exp (quadratic * skill ^ 2) ∂selectedLaw) /
        ∫ skill, Real.exp (fixedLikelihood skill) ∂selectedLaw := by
    apply div_nonneg
    · exact integral_nonneg (fun skill => Real.exp_nonneg _)
    · exact (integral_exp_pos hfixed).le
  have hmgf : ∀ tilt : ℝ,
      (∫ skill, Real.exp (tilt * skill) ∂likelihoodBase) ≤
        ((∫ skill, Real.exp (quadratic * skill ^ 2) ∂selectedLaw) /
          (∫ skill, Real.exp (fixedLikelihood skill) ∂selectedLaw)) *
          Real.exp (beta * tilt ^ 2 / 2) := by
    simpa [likelihoodBase, selectedLaw, fixedLikelihood, quadratic] using
      (lg21_selectedGaussianLikelihoodBase_mgf_le
        priorMean priorVariance selected noiseVariance beta hprior hselected hnoise hbeta
        (by simpa [quadratic] using hquadratic))
  have hbaseExp : ∀ tilt : ℝ,
      Integrable (fun skill : ℝ => Real.exp (tilt * skill)) likelihoodBase := by
    intro tilt
    simpa [likelihoodBase, selectedLaw] using
      (lg21_selectedGaussianLikelihoodBase_integrable_exp
        priorMean priorVariance selected noiseVariance tilt hselected hnoise)
  simpa [lg21SelectedTiltedMean] using
    (lg21_tiltedMean_abs_le_of_mgf_envelope likelihoodBase hbaseId hbaseExp
      ((∫ skill, Real.exp (quadratic * skill ^ 2) ∂selectedLaw) /
        (∫ skill, Real.exp (fixedLikelihood skill) ∂selectedLaw)) beta
      hconstantNonneg hmgf)

/-- The canonical selected Gaussian posterior mean is integrable under every
Gaussian score shift whenever the displayed sub-Gaussian envelope coefficient
lies strictly below the noise variance. -/
theorem lg21_selectedGaussian_canonicalPosteriorMean_integrable_gaussianShift_of_beta
    (priorMean : ℝ) (priorVariance : NNReal) (selected : Set ℝ)
    (noiseVariance : NNReal) (beta : ℝ)
    (hprior : priorVariance ≠ 0)
    (hselected : 0 < gaussianReal priorMean priorVariance selected)
    (hnoise : 0 < (noiseVariance : ℝ))
    (hbeta : 0 < beta) (hbetaNoise : beta < (noiseVariance : ℝ))
    (hquadratic :
      1 / (2 * beta) - 1 / (2 * (noiseVariance : ℝ)) <
        1 / (2 * (priorVariance : ℝ))) :
    ∀ skill : ℝ,
      Integrable
        (lg21CanonicalSelectedGaussianPosteriorMean
          (lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected)
          (noiseVariance : ℝ))
        (gaussianReal skill noiseVariance) := by
  let selectedLaw : Measure ℝ :=
    lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected
  let likelihoodBase : Measure ℝ :=
    lg21GaussianLikelihoodBase selectedLaw (noiseVariance : ℝ)
  let fixedLikelihood : ℝ → ℝ :=
    fun latentSkill => -latentSkill ^ 2 / (2 * (noiseVariance : ℝ))
  let quadratic : ℝ := beta / (2 * (noiseVariance : ℝ) ^ 2)
  let posteriorMean : ℝ → ℝ :=
    lg21CanonicalSelectedGaussianPosteriorMean selectedLaw (noiseVariance : ℝ)
  let normalization : ℝ :=
    (∫ latentSkill, Real.exp
      ((1 / (2 * beta) - 1 / (2 * (noiseVariance : ℝ))) * latentSkill ^ 2)
      ∂selectedLaw) /
      (∫ latentSkill, Real.exp (fixedLikelihood latentSkill) ∂selectedLaw)
  let baseMean : ℝ := ∫ latentSkill, latentSkill ∂likelihoodBase
  have hnoiseNe : (noiseVariance : ℝ) ≠ 0 := ne_of_gt hnoise
  have hnoiseNeNN : noiseVariance ≠ 0 := NNReal.coe_ne_zero.mp hnoiseNe
  have hquadraticLt : quadratic < 1 / (2 * (noiseVariance : ℝ)) := by
    dsimp [quadratic]
    field_simp [hnoiseNe]
    nlinarith
  have hstrict : StrictMono posteriorMean := by
    simpa [posteriorMean, selectedLaw] using
      (lg21_selectedGaussian_canonicalPosteriorMean_strictMono
        priorMean priorVariance selected (noiseVariance : ℝ)
        hprior hselected hnoise)
  have hposteriorMeasurable : Measurable posteriorMean :=
    hstrict.monotone.measurable
  have henvelope : ∀ tilt : ℝ,
      |lg21SelectedTiltedMean likelihoodBase tilt| ≤
        normalization * Real.exp
          (beta * (tilt + 1) ^ 2 / 2 - tilt * baseMean) +
        normalization * Real.exp
          (beta * (tilt - 1) ^ 2 / 2 - tilt * baseMean) := by
    simpa [selectedLaw, likelihoodBase, fixedLikelihood, normalization, baseMean] using
      (lg21_selectedGaussianLikelihoodBase_tiltedMean_abs_envelope
        priorMean priorVariance selected (noiseVariance : ℝ) beta
        hprior hselected hnoise hbeta hquadratic)
  intro skill
  let upperPlus : ℝ → ℝ := fun score => normalization * Real.exp
    (beta * ((noiseVariance : ℝ)⁻¹ * score + 1) ^ 2 / 2 -
      ((noiseVariance : ℝ)⁻¹ * score) * baseMean)
  let upperMinus : ℝ → ℝ := fun score => normalization * Real.exp
    (beta * ((noiseVariance : ℝ)⁻¹ * score - 1) ^ 2 / 2 -
      ((noiseVariance : ℝ)⁻¹ * score) * baseMean)
  have hplusQuadratic : Integrable (fun score : ℝ =>
      Real.exp (quadratic * score ^ 2 +
        ((beta - baseMean) / (noiseVariance : ℝ)) * score))
      (gaussianReal skill noiseVariance) :=
    lg21_integrable_exp_quadratic_gaussian skill quadratic
      ((beta - baseMean) / (noiseVariance : ℝ)) noiseVariance hnoiseNeNN
      hquadraticLt
  have hminusQuadratic : Integrable (fun score : ℝ =>
      Real.exp (quadratic * score ^ 2 +
        ((-beta - baseMean) / (noiseVariance : ℝ)) * score))
      (gaussianReal skill noiseVariance) :=
    lg21_integrable_exp_quadratic_gaussian skill quadratic
      ((-beta - baseMean) / (noiseVariance : ℝ)) noiseVariance hnoiseNeNN
      hquadraticLt
  have hupperPlus : Integrable upperPlus (gaussianReal skill noiseVariance) := by
    convert (hplusQuadratic.const_mul (normalization * Real.exp (beta / 2))) using 1
    ext score
    dsimp [upperPlus, quadratic]
    conv_rhs => rw [mul_assoc, ← Real.exp_add]
    congr 1
    field_simp [hnoiseNe]
    ring_nf
  have hupperMinus : Integrable upperMinus (gaussianReal skill noiseVariance) := by
    convert (hminusQuadratic.const_mul (normalization * Real.exp (beta / 2))) using 1
    ext score
    dsimp [upperMinus, quadratic]
    conv_rhs => rw [mul_assoc, ← Real.exp_add]
    congr 1
    field_simp [hnoiseNe]
    ring_nf
  have hupper : Integrable (fun score => upperPlus score + upperMinus score)
      (gaussianReal skill noiseVariance) := hupperPlus.add hupperMinus
  change Integrable posteriorMean (gaussianReal skill noiseVariance)
  apply Integrable.mono' hupper hposteriorMeasurable.aestronglyMeasurable
  filter_upwards with score
  rw [Real.norm_eq_abs]
  change |lg21CanonicalSelectedGaussianPosteriorMean selectedLaw
      (noiseVariance : ℝ) score| ≤ upperPlus score + upperMinus score
  simpa [lg21CanonicalSelectedGaussianPosteriorMean, posteriorMean,
    upperPlus, upperMinus] using
    (henvelope ((noiseVariance : ℝ)⁻¹ * score))

/-- Between the Gaussian likelihood precision and the prior precision there
is always a strict sub-Gaussian envelope coefficient. -/
private theorem lg21_exists_selectedGaussian_envelope_coefficient
    (priorVariance noiseVariance : ℝ)
    (hprior : 0 < priorVariance) (hnoise : 0 < noiseVariance) :
    ∃ beta : ℝ, 0 < beta ∧ beta < noiseVariance ∧
      1 / (2 * beta) - 1 / (2 * noiseVariance) <
        1 / (2 * priorVariance) := by
  have hsum : 0 < priorVariance + noiseVariance := by linarith
  let lower : ℝ := priorVariance * noiseVariance /
    (priorVariance + noiseVariance)
  have hlowerPos : 0 < lower := by
    dsimp [lower]
    positivity
  have hlowerLt : lower < noiseVariance := by
    dsimp [lower]
    apply (div_lt_iff₀ hsum).mpr
    nlinarith
  obtain ⟨beta, hlowerBeta, hbetaNoise⟩ := exists_between hlowerLt
  have hbeta : 0 < beta := lt_trans hlowerPos hlowerBeta
  refine ⟨beta, hbeta, hbetaNoise, ?_⟩
  have hlowerBeta' : priorVariance * noiseVariance <
      beta * (priorVariance + noiseVariance) := by
    exact (div_lt_iff₀ hsum).mp (by simpa [lower] using hlowerBeta)
  field_simp [ne_of_gt hprior, ne_of_gt hnoise, ne_of_gt hbeta]
  nlinarith

/-- Every positive-mass selection from a nondegenerate Gaussian prior has a
canonical Gaussian posterior mean integrable under each latent-skill score
law.  This closes the Gaussian-shift definedness premise without making it a
source-model field. -/
theorem lg21_selectedGaussian_canonicalPosteriorMean_integrable_gaussianShift
    (priorMean : ℝ) (priorVariance : NNReal) (selected : Set ℝ)
    (noiseVariance : NNReal)
    (hprior : priorVariance ≠ 0)
    (hselected : 0 < gaussianReal priorMean priorVariance selected)
    (hnoise : 0 < (noiseVariance : ℝ)) :
    ∀ skill : ℝ,
      Integrable
        (lg21CanonicalSelectedGaussianPosteriorMean
          (lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected)
          (noiseVariance : ℝ))
        (gaussianReal skill noiseVariance) := by
  have hpriorPos : 0 < (priorVariance : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hprior)
  obtain ⟨beta, hbeta, hbetaNoise, hquadratic⟩ :=
    lg21_exists_selectedGaussian_envelope_coefficient
      (priorVariance : ℝ) (noiseVariance : ℝ) hpriorPos hnoise
  exact lg21_selectedGaussian_canonicalPosteriorMean_integrable_gaussianShift_of_beta
    priorMean priorVariance selected noiseVariance beta
    hprior hselected hnoise hbeta hbetaNoise hquadratic

end

end LG21TestOptionalPolicies
