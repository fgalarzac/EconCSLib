import LG21TestOptionalPolicies.SelectedPopulationConditionalSupport
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian-shift monotonicity of expected PBO payoff

The pre-test LG21 action is evaluated before the additive Gaussian test noise
is drawn. This file proves the semantic bridge needed for the report-required
protocol: if a source-derived selected PBO is strictly increasing in the
reported score, then its expectation under `score = skill + noise` is strictly
increasing in latent skill.

No action strategy, posterior formula, or equilibrium conclusion is assumed
here. Callers must separately derive the selected PBO from the literal action
profile and prove its integrability under every Gaussian score shift.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-- Expected reported payoff for a latent skill type before its Gaussian test
noise is realized. -/
def lg21GaussianShiftExpectedPayoff
    (reportedPBO : ℝ -> ℝ) (noiseVariance : NNReal) (skill : ℝ) : ℝ :=
  ∫ score, reportedPBO score ∂gaussianReal skill noiseVariance

/-- A strictly increasing score-contingent PBO has a strictly increasing
pre-test expected payoff under any fixed additive Gaussian noise law. -/
theorem lg21_gaussianShiftExpectedPayoff_strictMono
    (reportedPBO : ℝ -> ℝ) (noiseVariance : NNReal)
    (hreportedPBO : StrictMono reportedPBO)
    (hintegrable : ∀ skill,
      Integrable reportedPBO (gaussianReal skill noiseVariance)) :
    StrictMono (lg21GaussianShiftExpectedPayoff reportedPBO noiseVariance) := by
  intro low high hlowhigh
  let baseLaw : Measure ℝ := gaussianReal 0 noiseVariance
  have hmapLow : baseLaw.map (fun noise : ℝ => noise + low) =
      gaussianReal low noiseVariance := by
    simpa [baseLaw] using
      (gaussianReal_map_add_const (μ := (0 : ℝ)) (v := noiseVariance) low)
  have hmapHigh : baseLaw.map (fun noise : ℝ => noise + high) =
      gaussianReal high noiseVariance := by
    simpa [baseLaw] using
      (gaussianReal_map_add_const (μ := (0 : ℝ)) (v := noiseVariance) high)
  have hlowMapIntegrable :
      Integrable reportedPBO (baseLaw.map (fun noise : ℝ => noise + low)) := by
    rw [hmapLow]
    exact hintegrable low
  have hhighMapIntegrable :
      Integrable reportedPBO (baseLaw.map (fun noise : ℝ => noise + high)) := by
    rw [hmapHigh]
    exact hintegrable high
  have hlowIntegrable :
      Integrable (fun noise : ℝ => reportedPBO (noise + low)) baseLaw := by
    change Integrable (reportedPBO ∘ fun noise : ℝ => noise + low) baseLaw
    apply (integrable_map_measure hlowMapIntegrable.aestronglyMeasurable
      (by fun_prop : AEMeasurable (fun noise : ℝ => noise + low) baseLaw)).mp
    exact hlowMapIntegrable
  have hhighIntegrable :
      Integrable (fun noise : ℝ => reportedPBO (noise + high)) baseLaw := by
    change Integrable (reportedPBO ∘ fun noise : ℝ => noise + high) baseLaw
    apply (integrable_map_measure hhighMapIntegrable.aestronglyMeasurable
      (by fun_prop : AEMeasurable (fun noise : ℝ => noise + high) baseLaw)).mp
    exact hhighMapIntegrable
  letI : IsProbabilityMeasure baseLaw := by
    simpa [baseLaw] using
      (inferInstance : IsProbabilityMeasure (gaussianReal 0 noiseVariance))
  have hpoint : ∀ᵐ noise ∂baseLaw,
      reportedPBO (noise + low) < reportedPBO (noise + high) :=
    Filter.Eventually.of_forall fun noise =>
      hreportedPBO (by linarith)
  have hstrict :
      (∫ noise, reportedPBO (noise + low) ∂baseLaw) <
        ∫ noise, reportedPBO (noise + high) ∂baseLaw :=
    lg21_integral_lt_integral_of_ae_lt_probability
      baseLaw hlowIntegrable hhighIntegrable hpoint
  unfold lg21GaussianShiftExpectedPayoff
  rw [← hmapLow, ← hmapHigh]
  rw [MeasureTheory.integral_map
    (by fun_prop : AEMeasurable (fun noise : ℝ => noise + low) baseLaw)
    hlowMapIntegrable.aestronglyMeasurable]
  rw [MeasureTheory.integral_map
    (by fun_prop : AEMeasurable (fun noise : ℝ => noise + high) baseLaw)
    hhighMapIntegrable.aestronglyMeasurable]
  exact hstrict

end

end LG21TestOptionalPolicies
