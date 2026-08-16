import KR21Monoculture.AppendixBGaussianMixtureDefinition1
import KR21Monoculture.GaussianDensityRegularity

/-!
# Global `W^{1,1}` regularity of finite Gaussian mixtures

This module proves the analytic inputs needed by the corrected Appendix A
Definition 1 route for the explicit finite Gaussian mixtures used in Appendix
B.  The proofs are generic over the finite component carrier; the later
source-law transport remains a separate measure equality.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace KR21Monoculture

noncomputable section

/-- The ordinary derivative of a finite, common-variance Gaussian mixture. -/
noncomputable def finiteGaussianMixtureDerivative
    {α : Type*} [Fintype α] (law : PMF α) (center : α → ℝ) (s : ℝ) (x : ℝ) : ℝ :=
  ∑ a, (law a).toReal * appendixBGaussianPDFDerivative
    (center a) (appendixBGaussianVariance s) x

/-- The finite Gaussian-mixture derivative is integrable at every positive
component scale. -/
theorem integrable_finiteGaussianMixtureDerivative
    {α : Type*} [Fintype α] (law : PMF α) (center : α → ℝ) (s : ℝ)
    (hs : 0 < s) :
    Integrable (finiteGaussianMixtureDerivative law center s) volume := by
  unfold finiteGaussianMixtureDerivative
  apply integrable_finset_sum
  intro a _
  have hcomponent : Integrable
      (appendixBGaussianPDFDerivative (center a) (appendixBGaussianVariance s))
        volume := by
    simpa only [appendixBGaussianPDFDerivative, gaussianPDFRealDerivative] using
      (integrable_gaussianPDFRealDerivative (center a)
        (appendixBGaussianVariance s) (appendixBGaussianVariance_ne_zero hs))
  exact hcomponent.const_mul (law a).toReal

/-- The finite Gaussian-mixture density itself is integrable. -/
theorem integrable_finiteGaussianMixtureDensity
    {α : Type*} [Fintype α] (law : PMF α) (center : α → ℝ) (s : ℝ) :
    Integrable (finiteGaussianMixtureDensity law center s) volume := by
  unfold finiteGaussianMixtureDensity
  apply integrable_finset_sum
  intro a _
  exact (ProbabilityTheory.integrable_gaussianPDFReal
    (center a) (appendixBGaussianVariance s)).const_mul (law a).toReal

/-- A finite positive-variance Gaussian mixture has a positive density at
every real point, because a PMF has at least one positive-mass component. -/
theorem finiteGaussianMixtureDensity_pos
    {α : Type*} [Fintype α] (law : PMF α) (center : α → ℝ) (s x : ℝ)
    (hs : 0 < s) :
    0 < finiteGaussianMixtureDensity law center s x := by
  rcases law.support_nonempty with ⟨a, ha⟩
  have hmass : 0 < (law a).toReal :=
    ENNReal.toReal_pos ((law.mem_support_iff a).mp ha) (law.apply_ne_top a)
  have hgaussian : 0 < ProbabilityTheory.gaussianPDFReal
      (center a) (appendixBGaussianVariance s) x :=
    ProbabilityTheory.gaussianPDFReal_pos _ _ _
      (appendixBGaussianVariance_ne_zero hs)
  unfold finiteGaussianMixtureDensity
  refine Finset.sum_pos' ?_ ?_
  · intro b _
    exact mul_nonneg ENNReal.toReal_nonneg
      (ProbabilityTheory.gaussianPDFReal_nonneg _ _ _)
  · exact ⟨a, Finset.mem_univ a, mul_pos hmass hgaussian⟩

/-- Finite Gaussian mixtures are absolutely continuous on every real
interval. -/
theorem finiteGaussianMixtureDensity_absolutelyContinuousOnInterval
    {α : Type*} [Fintype α] (law : PMF α) (center : α → ℝ) (s a b : ℝ) :
    AbsolutelyContinuousOnInterval (finiteGaussianMixtureDensity law center s) a b := by
  have hcont : ContDiff ℝ 1 (finiteGaussianMixtureDensity law center s) := by
    unfold finiteGaussianMixtureDensity
    apply ContDiff.sum
    intro component _
    simpa only [smul_eq_mul] using
      ((gaussianPDFReal_contDiff (center component)
        (appendixBGaussianVariance s)).of_le (by simp)).const_smul
        (law component).toReal
  exact hcont.contDiffOn.absolutelyContinuousOnInterval

/-- The displayed finite-mixture derivative is the genuine derivative of the
density at every point, not merely a separately named function. -/
theorem finiteGaussianMixtureDensity_hasDerivAt
    {α : Type*} [Fintype α] (law : PMF α) (center : α → ℝ) (s : ℝ)
    (hs : 0 < s) (x : ℝ) :
    HasDerivAt (finiteGaussianMixtureDensity law center s)
      (finiteGaussianMixtureDerivative law center s x) x := by
  unfold finiteGaussianMixtureDensity finiteGaussianMixtureDerivative
  apply HasDerivAt.fun_sum
  intro a _
  simpa only [smul_eq_mul] using
    (gaussianPDFReal_hasDerivAt (center a) (appendixBGaussianVariance s)
      (appendixBGaussianVariance_ne_zero hs) x).const_mul (law a).toReal

/-- The finite-mixture derivative agrees almost everywhere with `deriv`. -/
theorem finiteGaussianMixtureDerivative_ae_eq_deriv
    {α : Type*} [Fintype α] (law : PMF α) (center : α → ℝ) (s : ℝ)
    (hs : 0 < s) :
    finiteGaussianMixtureDerivative law center s =ᵐ[volume]
      deriv (finiteGaussianMixtureDensity law center s) := by
  filter_upwards with x
  exact (finiteGaussianMixtureDensity_hasDerivAt law center s hs x).deriv.symm

/-- A finite positive-variance Gaussian mixture integrates to one under its
displayed density. -/
theorem lintegral_finiteGaussianMixtureDensity_eq_one
    {α : Type*} [Fintype α] (law : PMF α) (center : α → ℝ) (s : ℝ)
    (hs : 0 < s) :
    ∫⁻ x, ENNReal.ofReal (finiteGaussianMixtureDensity law center s x) = 1 := by
  calc
    ∫⁻ x, ENNReal.ofReal (finiteGaussianMixtureDensity law center s x) =
        ∫⁻ x, ∑ a, law a * ProbabilityTheory.gaussianPDF
          (center a) (appendixBGaussianVariance s) x := by
            apply lintegral_congr
            intro x
            exact ennreal_finiteGaussianMixtureDensity law center s x
    _ = ∑ a, ∫⁻ x, law a * ProbabilityTheory.gaussianPDF
          (center a) (appendixBGaussianVariance s) x := by
            rw [lintegral_finset_sum]
            intro a _
            exact measurable_const.mul
              (ProbabilityTheory.measurable_gaussianPDF _ _)
    _ = ∑ a, law a * ∫⁻ x, ProbabilityTheory.gaussianPDF
          (center a) (appendixBGaussianVariance s) x := by
            apply Finset.sum_congr rfl
            intro a _
            rw [lintegral_const_mul _
              (ProbabilityTheory.measurable_gaussianPDF _ _)]
    _ = ∑ a, law a := by
            simp [ProbabilityTheory.lintegral_gaussianPDF_eq_one _
              (appendixBGaussianVariance_ne_zero hs)]
    _ = 1 := by
            simpa only [tsum_fintype] using law.tsum_coe

/-- The complete analytic package needed to instantiate the corrected
`W^{1,1}` Definition 1 theorem with a finite Gaussian mixture. -/
structure FiniteGaussianMixtureW11Regularity
    {α : Type*} [Fintype α] (law : PMF α) (center : α → ℝ) (s : ℝ) : Prop where
  density_integrable : Integrable (finiteGaussianMixtureDensity law center s) volume
  derivative_integrable : Integrable (finiteGaussianMixtureDerivative law center s) volume
  density_measurable : Measurable (finiteGaussianMixtureDensity law center s)
  density_positive : ∀ x, 0 < finiteGaussianMixtureDensity law center s x
  absolute_continuity : ∀ a b,
    AbsolutelyContinuousOnInterval (finiteGaussianMixtureDensity law center s) a b
  derivative_ae_eq : finiteGaussianMixtureDerivative law center s =ᵐ[volume]
    deriv (finiteGaussianMixtureDensity law center s)
  normalized : ∫⁻ x, ENNReal.ofReal (finiteGaussianMixtureDensity law center s x) = 1

/-- Finite Gaussian mixtures at positive scale satisfy the complete global
`W^{1,1}` regularity package. -/
theorem finiteGaussianMixture_w11Regularity
    {α : Type*} [Fintype α] (law : PMF α) (center : α → ℝ) (s : ℝ)
    (hs : 0 < s) :
    FiniteGaussianMixtureW11Regularity law center s := by
  exact {
    density_integrable := integrable_finiteGaussianMixtureDensity law center s
    derivative_integrable := integrable_finiteGaussianMixtureDerivative law center s hs
    density_measurable := measurable_finiteGaussianMixtureDensity law center s
    density_positive := fun x => finiteGaussianMixtureDensity_pos law center s x hs
    absolute_continuity := fun a b =>
      finiteGaussianMixtureDensity_absolutelyContinuousOnInterval law center s a b
    derivative_ae_eq := finiteGaussianMixtureDerivative_ae_eq_deriv law center s hs
    normalized := lintegral_finiteGaussianMixtureDensity_eq_one law center s hs
  }

end

end KR21Monoculture
