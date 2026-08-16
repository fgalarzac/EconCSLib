import LG21TestOptionalPolicies.SelectedPosteriorTiltMonotonicity
import LG21TestOptionalPolicies.GaussianShiftExpectedPayoff
import LG21TestOptionalPolicies.SelectedGaussianPosteriorShiftIntegrability

/-!
# Ex-ante payoff from a selected Gaussian posterior

This is the selected-posterior specialization of the existing source-neutral
Gaussian-shift monotonicity result.  It adds no duplicate convolution proof.
The source-facing bridge must still identify the public-action-selected PBO
with this canonical likelihood family.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory

/--
The ex-ante payoff induced by the canonical Gaussian-likelihood posterior of
a selected latent population.  The selected law is explicit, so no hidden
claim equates it with a source PBO.
-/
def lg21CanonicalSelectedGaussianExpectedPBO
    (selectedSkillLaw : Measure ℝ) (noiseVariance : NNReal) (skill : ℝ) : ℝ :=
  lg21GaussianShiftExpectedPayoff
    (lg21CanonicalSelectedGaussianPosteriorMean
      selectedSkillLaw (noiseVariance : ℝ))
    noiseVariance skill

/--
Once the selected posterior is identified with the correct Gaussian
likelihood family and has its displayed moment/variance regularity, its
ex-ante payoff is strictly increasing in latent skill.

The remaining source-law work is intentionally not a premise hidden behind a
name: it must prove that the public report action induces `selectedSkillLaw`
and that the school PBO is this canonical posterior almost everywhere.
-/
theorem lg21CanonicalSelectedGaussianExpectedPBO_strictMono
    (selectedSkillLaw : Measure ℝ) (noiseVariance : NNReal)
    (hnoiseVariance : 0 < (noiseVariance : ℝ))
    (hinterior :
      ∀ tilt : ℝ,
        tilt ∈ interior (integrableExpSet id
          (lg21GaussianLikelihoodBase selectedSkillLaw
            (noiseVariance : ℝ))))
    (hvariance :
      ∀ tilt : ℝ,
        0 < Var[id;
          (lg21GaussianLikelihoodBase selectedSkillLaw
            (noiseVariance : ℝ)).tilted
              (fun skill => tilt * skill)])
    (hintegrable : ∀ skill,
      Integrable
        (lg21CanonicalSelectedGaussianPosteriorMean selectedSkillLaw
          (noiseVariance : ℝ))
        (gaussianReal skill noiseVariance)) :
    StrictMono
      (lg21CanonicalSelectedGaussianExpectedPBO
        selectedSkillLaw noiseVariance) := by
  apply lg21_gaussianShiftExpectedPayoff_strictMono
  · exact lg21_canonicalSelectedGaussianPosteriorMean_strictMono
      selectedSkillLaw (noiseVariance : ℝ) hnoiseVariance hinterior hvariance
  · exact hintegrable

/-- For a positive-mass public selection of a nondegenerate Gaussian prior,
the canonical selected-posterior expected reported payoff is strictly
increasing before Gaussian test noise is realized.  All analytic moment,
variance, and shifted-score integrability obligations are derived here rather
than supplied by a source-model record. -/
theorem lg21_selectedGaussianExpectedPBO_strictMono
    (priorMean : ℝ) (priorVariance : NNReal) (selected : Set ℝ)
    (noiseVariance : NNReal)
    (hprior : priorVariance ≠ 0)
    (hselected : 0 < gaussianReal priorMean priorVariance selected)
    (hnoise : 0 < (noiseVariance : ℝ)) :
    StrictMono
      (lg21CanonicalSelectedGaussianExpectedPBO
        (lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected)
        noiseVariance) := by
  apply lg21CanonicalSelectedGaussianExpectedPBO_strictMono
  · exact hnoise
  · exact lg21_selectedGaussianLikelihoodBase_all_exp_interior
      priorMean priorVariance selected (noiseVariance : ℝ) hselected hnoise
  · exact lg21_selectedGaussianLikelihoodBase_tilt_variance_pos
      priorMean priorVariance selected (noiseVariance : ℝ)
      hprior hselected hnoise
  · exact lg21_selectedGaussian_canonicalPosteriorMean_integrable_gaussianShift
      priorMean priorVariance selected noiseVariance hprior hselected hnoise

end

end LG21TestOptionalPolicies
