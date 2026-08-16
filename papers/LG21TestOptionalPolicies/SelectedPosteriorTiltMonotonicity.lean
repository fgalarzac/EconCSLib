import Mathlib.Probability.Moments.Tilted

/-!
# Strict monotonicity for selected exponential-tilt posterior means

After a Gaussian score likelihood is multiplied by an arbitrary fixed
selection law on latent skill, the score enters the posterior density through
an exponential tilt.  This module proves the analytic core of that statement:
the latent-skill mean under a nondegenerate exponential tilt is strictly
increasing in its tilt parameter, and hence in a score with positive noise
variance.

The hypotheses are intentionally explicit.  In particular, this file neither
claims that an LG21 equilibrium produces the selected base law nor identifies a
regular conditional distribution with the displayed tilt.  A source-facing
bridge must establish those identities, exponential integrability, and
positive tilted variance from the literal Gaussian population and sequential
actions.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory
open ProbabilityTheory
open Set

/-- The latent-skill mean under an exponential tilt of a selected base law. -/
def lg21SelectedTiltedMean (law : Measure ℝ) (tilt : ℝ) : ℝ :=
  ∫ skill, skill ∂law.tilted (fun skill => tilt * skill)

/--
The score-independent part of a Gaussian signal likelihood.  If `law` is the
latent law after a taking/reporting selection and a realized signal has density
proportional to `exp (-(score - skill)^2 / (2 * noiseVariance))`, then the
remaining score-dependent factor is an exponential tilt of this base law.
-/
def lg21GaussianLikelihoodBase
    (law : Measure ℝ) (noiseVariance : ℝ) : Measure ℝ :=
  law.tilted (fun skill => -skill ^ 2 / (2 * noiseVariance))

/--
The canonical selected Gaussian posterior mean, written as its fixed
likelihood-base tilt followed by the score tilt.  This is intentionally a
measure expression, not an assertion that it equals an LG21 `condDistrib`.
-/
def lg21CanonicalSelectedGaussianPosteriorMean
    (law : Measure ℝ) (noiseVariance score : ℝ) : ℝ :=
  lg21SelectedTiltedMean (lg21GaussianLikelihoodBase law noiseVariance)
    (noiseVariance⁻¹ * score)

/--
For a law with exponential moments on the whole real line and nonzero tilted
variance at every tilt, the selected posterior mean is strictly increasing in
the tilt parameter.

The variance hypothesis is semantic: it rules out a selected population
concentrated at one latent skill.  It is not inferred from a function name or
from the fact that the source mentioned a Gaussian signal.
-/
theorem lg21_selectedTiltedMean_strictMono
    (law : Measure ℝ)
    (hinterior :
      ∀ tilt : ℝ, tilt ∈ interior (integrableExpSet id law))
    (hvariance :
      ∀ tilt : ℝ,
        0 < Var[id; law.tilted (fun skill => tilt * skill)]) :
    StrictMono (lg21SelectedTiltedMean law) := by
  have hmean :
      ∀ tilt : ℝ,
        lg21SelectedTiltedMean law tilt = deriv (cgf id law) tilt := by
    intro tilt
    simpa [lg21SelectedTiltedMean, id_eq] using
      (integral_tilted_mul_self (X := id) (μ := law) (t := tilt)
        (hinterior tilt))
  have hderiv_pos :
      ∀ tilt : ℝ,
        0 < deriv (fun t => deriv (cgf id law) t) tilt := by
    intro tilt
    rw [show deriv (fun t => deriv (cgf id law) t) tilt =
      iteratedDeriv 2 (cgf id law) tilt by
        simp only [iteratedDeriv_succ, iteratedDeriv_zero]]
    rw [← variance_tilted_mul (X := id) (μ := law) (t := tilt)
      (hinterior tilt)]
    exact hvariance tilt
  have hcgf : StrictMono (fun tilt => deriv (cgf id law) tilt) :=
    strictMono_of_deriv_pos hderiv_pos
  intro left right hleftRight
  rw [hmean left, hmean right]
  exact hcgf hleftRight

/--
Score specialization of the tilted-mean theorem.  A Gaussian likelihood with
positive variance has a tilt parameter proportional to the observed score;
the source bridge supplies that proportionality and the posterior identity.
-/
theorem lg21_selectedTiltedMean_strictMono_score
    (law : Measure ℝ)
    (hinterior :
      ∀ tilt : ℝ, tilt ∈ interior (integrableExpSet id law))
    (hvariance :
      ∀ tilt : ℝ,
        0 < Var[id; law.tilted (fun skill => tilt * skill)])
    (noiseVariance : ℝ) (hnoiseVariance : 0 < noiseVariance) :
    StrictMono (fun score =>
      lg21SelectedTiltedMean law (score / noiseVariance)) := by
  have htilt := lg21_selectedTiltedMean_strictMono law hinterior hvariance
  intro left right hleftRight
  apply htilt
  exact (div_lt_div_iff_of_pos_right hnoiseVariance).2 hleftRight

/--
Strict monotonicity for the correct Gaussian-likelihood selected-posterior
family.  The fixed quadratic tilt is essential: using the raw selected law
with only `score / noiseVariance` would omit a likelihood factor and prove a
statement about a different posterior.

The hypotheses remain source-bridge obligations.  In particular, a future
proof must derive this family as an a.e. RCD of the literal selected
Gaussian-noise joint law, rather than assuming the identity from a function
named `posterior` or `PBO`.
-/
theorem lg21_canonicalSelectedGaussianPosteriorMean_strictMono
    (law : Measure ℝ) (noiseVariance : ℝ) (hnoiseVariance : 0 < noiseVariance)
    (hinterior :
      ∀ tilt : ℝ,
        tilt ∈ interior (integrableExpSet id
          (lg21GaussianLikelihoodBase law noiseVariance)))
    (hvariance :
      ∀ tilt : ℝ,
        0 < Var[id;
          (lg21GaussianLikelihoodBase law noiseVariance).tilted
            (fun skill => tilt * skill)]) :
    StrictMono
      (lg21CanonicalSelectedGaussianPosteriorMean law noiseVariance) := by
  have htilt := lg21_selectedTiltedMean_strictMono
    (lg21GaussianLikelihoodBase law noiseVariance) hinterior hvariance
  intro left right hleftRight
  apply htilt
  exact mul_lt_mul_of_pos_left hleftRight (inv_pos.mpr hnoiseVariance)

end

end LG21TestOptionalPolicies
