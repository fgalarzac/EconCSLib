import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian density regularity

Small analytic lemmas for the explicit finite Gaussian-mixture constructions
used in the KR21 Appendix B repair.  These are stated for a single
nondegenerate Gaussian component so finite-mixture assembly can use them
without referring to a particular counterexample or latent carrier.
-/

open MeasureTheory
open scoped NNReal

namespace KR21Monoculture

noncomputable section

/-- The ordinary derivative of a nondegenerate real Gaussian density. -/
noncomputable def gaussianPDFRealDerivative
    (mean : ℝ) (variance : ℝ≥0) (x : ℝ) : ℝ :=
  -((x - mean) / variance) * ProbabilityTheory.gaussianPDFReal mean variance x

/-- The derivative of every nondegenerate real Gaussian density is integrable.

This is the global `W^{1,1}` analytic primitive needed for a finite mixture:
after translating by the mean, the derivative is a constant multiple of
`x * exp (-b * x^2)` for a positive `b`.
-/
theorem integrable_gaussianPDFRealDerivative
    (mean : ℝ) (variance : ℝ≥0) (hvariance : variance ≠ 0) :
    Integrable (gaussianPDFRealDerivative mean variance) volume := by
  have hvariance_pos : 0 < (variance : ℝ) := by
    exact_mod_cast (lt_of_le_of_ne (zero_le variance) (Ne.symm hvariance))
  have hvariance_real_ne : (variance : ℝ) ≠ 0 := ne_of_gt hvariance_pos
  let b : ℝ := (2 * (variance : ℝ))⁻¹
  have hb : 0 < b := by
    dsimp [b]
    exact inv_pos.mpr (mul_pos (by norm_num) hvariance_pos)
  have hbase : Integrable (fun x : ℝ => x * Real.exp (-b * x ^ 2)) volume :=
    integrable_mul_exp_neg_mul_sq hb
  have htranslated : Integrable
      (fun x : ℝ => (x - mean) * Real.exp (-b * (x - mean) ^ 2)) volume := by
    simpa [Function.comp_def] using hbase.comp_sub_right mean
  have hscaled := htranslated.const_mul
    (-((variance : ℝ)⁻¹ * (Real.sqrt (2 * Real.pi * (variance : ℝ)))⁻¹))
  refine hscaled.congr ?_
  filter_upwards with x
  unfold gaussianPDFRealDerivative
  rw [ProbabilityTheory.gaussianPDFReal_def]
  dsimp [b]
  field_simp [hvariance_real_ne]

end

end KR21Monoculture
