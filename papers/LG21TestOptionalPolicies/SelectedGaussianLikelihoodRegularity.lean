import LG21TestOptionalPolicies.SelectedPosteriorTiltMonotonicity
import LG21TestOptionalPolicies.SelectedGaussianExponentialTiltMonotonicity

/-!
# Regularity of a selected Gaussian likelihood base

For any positive-mass restriction of a nondegenerate Gaussian prior, the
score-independent quadratic Gaussian likelihood factor leaves enough
integrability and nondegeneracy to use the selected-posterior monotonicity
theorem.  This module proves those analytic facts directly.  It does not
identify the resulting expression with an LG21 conditional expectation; that
requires the separate public-action source-law bridge.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set

private theorem lg21_selectedGaussian_fixedLikelihood_integrable
    (priorMean : ℝ) (priorVariance : NNReal) (selected : Set ℝ)
    (noiseVariance : ℝ)
    (hselected : 0 < gaussianReal priorMean priorVariance selected)
    (hnoise : 0 < noiseVariance) :
    Integrable
      (fun skill : ℝ => Real.exp (-skill ^ 2 / (2 * noiseVariance)))
      (lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected) := by
  let law := lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected
  letI : IsProbabilityMeasure law :=
    lg21NormalizedRestriction_isProbability
      (gaussianReal priorMean priorVariance) selected (ne_of_gt hselected)
      (measure_ne_top _ _)
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards with skill
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg skill))
    (by positivity)

/--
Every exponential moment of the selected Gaussian likelihood base is finite.
The square-completion bound is explicit, so this does not assume a posterior
formula or an integrability certificate.
-/
theorem lg21_selectedGaussianLikelihoodBase_integrable_exp
    (priorMean : ℝ) (priorVariance : NNReal) (selected : Set ℝ)
    (noiseVariance tilt : ℝ)
    (hselected : 0 < gaussianReal priorMean priorVariance selected)
    (hnoise : 0 < noiseVariance) :
    Integrable (fun skill : ℝ => Real.exp (tilt * skill))
      (lg21GaussianLikelihoodBase
        (lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected)
        noiseVariance) := by
  let law := lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected
  letI : IsProbabilityMeasure law :=
    lg21NormalizedRestriction_isProbability
      (gaussianReal priorMean priorVariance) selected (ne_of_gt hselected)
      (measure_ne_top _ _)
  have hfixed : Integrable
      (fun skill : ℝ => Real.exp (-skill ^ 2 / (2 * noiseVariance))) law := by
    exact lg21_selectedGaussian_fixedLikelihood_integrable
      priorMean priorVariance selected noiseVariance hselected hnoise
  change Integrable (fun skill : ℝ => Real.exp (tilt * skill))
    (law.tilted (fun skill => -skill ^ 2 / (2 * noiseVariance)))
  rw [integrable_tilted_iff hfixed]
  apply Integrable.of_bound (by fun_prop)
    (Real.exp (noiseVariance * tilt ^ 2 / 2))
  filter_upwards with skill
  rw [Real.norm_eq_abs]
  have hnonneg : 0 ≤
      Real.exp (-skill ^ 2 / (2 * noiseVariance)) • Real.exp (tilt * skill) := by
    positivity
  rw [abs_of_nonneg hnonneg]
  change Real.exp (-skill ^ 2 / (2 * noiseVariance)) *
      Real.exp (tilt * skill) ≤ Real.exp (noiseVariance * tilt ^ 2 / 2)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hdenom : 0 < 2 * noiseVariance := by positivity
  calc
    -skill ^ 2 / (2 * noiseVariance) + tilt * skill =
        (-skill ^ 2 + (2 * noiseVariance) * (tilt * skill)) /
          (2 * noiseVariance) := by
          field_simp [ne_of_gt hnoise]
    _ ≤ (noiseVariance ^ 2 * tilt ^ 2) / (2 * noiseVariance) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hdenom)
      nlinarith [sq_nonneg (skill - noiseVariance * tilt)]
    _ = noiseVariance * tilt ^ 2 / 2 := by
      field_simp [ne_of_gt hnoise]

/--
All real tilts lie in the interior of the likelihood base's exponential
integrability set.
-/
theorem lg21_selectedGaussianLikelihoodBase_all_exp_interior
    (priorMean : ℝ) (priorVariance : NNReal) (selected : Set ℝ)
    (noiseVariance : ℝ)
    (hselected : 0 < gaussianReal priorMean priorVariance selected)
    (hnoise : 0 < noiseVariance) :
    ∀ tilt : ℝ,
      tilt ∈ interior (integrableExpSet id
        (lg21GaussianLikelihoodBase
          (lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected)
          noiseVariance)) := by
  intro tilt
  have hall : integrableExpSet id
      (lg21GaussianLikelihoodBase
        (lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected)
        noiseVariance) = Set.univ := by
    ext candidate
    simpa [integrableExpSet] using
      (lg21_selectedGaussianLikelihoodBase_integrable_exp
        priorMean priorVariance selected noiseVariance candidate hselected hnoise)
  simp [hall]

/--
Every further exponential tilt of the selected likelihood base has positive
latent-skill variance.  Positive selection mass and a nondegenerate Gaussian
prior rule out the only zero-variance case.
-/
theorem lg21_selectedGaussianLikelihoodBase_tilt_variance_pos
    (priorMean : ℝ) (priorVariance : NNReal) (selected : Set ℝ)
    (noiseVariance : ℝ)
    (hprior : priorVariance ≠ 0)
    (hselected : 0 < gaussianReal priorMean priorVariance selected)
    (hnoise : 0 < noiseVariance) :
    ∀ tilt : ℝ,
      0 < Var[id;
        (lg21GaussianLikelihoodBase
          (lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected)
          noiseVariance).tilted (fun skill => tilt * skill)] := by
  intro tilt
  let law := lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected
  let base := lg21GaussianLikelihoodBase law noiseVariance
  letI : IsProbabilityMeasure law :=
    lg21NormalizedRestriction_isProbability
      (gaussianReal priorMean priorVariance) selected (ne_of_gt hselected)
      (measure_ne_top _ _)
  letI : NoAtoms law := by
    simpa [law] using
      (lg21_noAtoms_normalizedRestriction_gaussian
        priorMean priorVariance selected hprior)
  have hfixed : Integrable
      (fun skill : ℝ => Real.exp (-skill ^ 2 / (2 * noiseVariance))) law := by
    exact lg21_selectedGaussian_fixedLikelihood_integrable
      priorMean priorVariance selected noiseVariance hselected hnoise
  letI : IsProbabilityMeasure base := by
    exact isProbabilityMeasure_tilted hfixed
  letI : NoAtoms base := by
    constructor
    intro skill
    exact tilted_absolutelyContinuous law
      (fun skill => -skill ^ 2 / (2 * noiseVariance))
      (measure_singleton skill)
  apply lg21_canonical_tilt_variance_pos base
  intro laterTilt
  exact lg21_selectedGaussianLikelihoodBase_integrable_exp
    priorMean priorVariance selected noiseVariance laterTilt hselected hnoise

/--
The canonical selected Gaussian posterior mean is strictly increasing for
every positive-mass measurable public selection of a nondegenerate Gaussian
prior and a positive test-noise variance.  No moment or variance condition is
left as a caller-provided model field.
-/
theorem lg21_selectedGaussian_canonicalPosteriorMean_strictMono
    (priorMean : ℝ) (priorVariance : NNReal) (selected : Set ℝ)
    (noiseVariance : ℝ)
    (hprior : priorVariance ≠ 0)
    (hselected : 0 < gaussianReal priorMean priorVariance selected)
    (hnoise : 0 < noiseVariance) :
    StrictMono
      (lg21CanonicalSelectedGaussianPosteriorMean
        (lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected)
        noiseVariance) := by
  apply lg21_canonicalSelectedGaussianPosteriorMean_strictMono
  · exact hnoise
  · exact lg21_selectedGaussianLikelihoodBase_all_exp_interior
      priorMean priorVariance selected noiseVariance hselected hnoise
  · exact lg21_selectedGaussianLikelihoodBase_tilt_variance_pos
      priorMean priorVariance selected noiseVariance hprior hselected hnoise

end

end LG21TestOptionalPolicies
