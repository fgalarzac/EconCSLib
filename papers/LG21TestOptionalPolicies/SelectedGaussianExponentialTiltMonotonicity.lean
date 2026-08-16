import LG21TestOptionalPolicies.ObservedAccessContinuous
import Mathlib.Probability.Moments.Tilted

/-!
# Strict monotonicity of a selected Gaussian exponential-tilt mean

This module proves an analytic fact used by the selected-population repair:
after restricting a nondegenerate Gaussian law to any positive-mass event,
the mean under a raw exponential tilt is strictly increasing in its tilt
parameter whenever the coefficient is positive.

The result is deliberately a law-level statement. It is not yet the Gaussian
likelihood posterior: that posterior first applies the score-independent
quadratic tilt `exp (-q^2 / (2 * noiseVariance))`. The correct family is
defined in `SelectedPosteriorTiltMonotonicity.lean`; a source-facing bridge
must establish its RCD identity separately.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory
open ProbabilityTheory
open Set

/-- The mean of a law after a one-dimensional exponential tilt. -/
def lg21ExponentialTiltMean (law : Measure ℝ) (tilt : ℝ) : ℝ :=
  ∫ latentSkill, latentSkill ∂law.tilted (fun latentSkill => tilt * latentSkill)

/--
The raw exponential-tilt mean of a selected Gaussian law. This deliberately
does not include the fixed quadratic factor of a Gaussian score likelihood.
-/
def lg21SelectedGaussianExponentialTiltMean
    (priorMean : ℝ) (priorVariance : NNReal) (selected : Set ℝ)
    (tiltCoefficient : ℝ) (score : ℝ) : ℝ :=
  lg21ExponentialTiltMean
    (lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected)
    (tiltCoefficient * score)

/--
Under an atomless probability law with all real exponential moments, every
canonical tilt has strictly positive variance.  The atomlessness matters: it
rules out the only way an integrable real variable can have variance zero.
-/
theorem lg21_canonical_tilt_variance_pos
    (law : Measure ℝ) [IsProbabilityMeasure law] [NoAtoms law]
    (hexp : ∀ tilt : ℝ,
      Integrable (fun latentSkill : ℝ => Real.exp (tilt * latentSkill)) law)
    (tilt : ℝ) :
    0 < Var[id; law.tilted (fun latentSkill => tilt * latentSkill)] := by
  have hmem : tilt ∈ interior (integrableExpSet id law) := by
    have hset : integrableExpSet id law = Set.univ := by
      ext t
      simpa [integrableExpSet] using hexp t
    simp [hset]
  have htiltExp :
      Integrable (fun latentSkill : ℝ => Real.exp (tilt * latentSkill)) law :=
    hexp tilt
  letI : NeZero law := ⟨IsProbabilityMeasure.ne_zero law⟩
  letI : IsProbabilityMeasure
      (law.tilted (fun latentSkill => tilt * latentSkill)) :=
    isProbabilityMeasure_tilted htiltExp
  have hvariance_ne_zero :
      Var[id; law.tilted (fun latentSkill => tilt * latentSkill)] ≠ 0 := by
    intro hzero
    have hae :
        ∀ᵐ latentSkill ∂law.tilted (fun latentSkill => tilt * latentSkill),
          id latentSkill =
            ∫ latentSkill,
              id latentSkill ∂law.tilted
                (fun latentSkill => tilt * latentSkill) := by
      exact ae_eq_integral_of_variance_eq_zero
        (memLp_tilted_mul hmem 2) hzero
    let posteriorMean : ℝ :=
      ∫ latentSkill,
        id latentSkill ∂law.tilted (fun latentSkill => tilt * latentSkill)
    have hsingleton_ae :
        ∀ᵐ latentSkill ∂law.tilted (fun latentSkill => tilt * latentSkill),
          latentSkill ∈ ({posteriorMean} : Set ℝ) := by
      filter_upwards [hae] with latentSkill hmean
      simpa [posteriorMean] using hmean
    have hsingleton_compl :
        law.tilted (fun latentSkill => tilt * latentSkill)
          ({posteriorMean} : Set ℝ)ᶜ = 0 :=
      mem_ae_iff.mp hsingleton_ae
    have htilted_no_atoms :
        NoAtoms (law.tilted (fun latentSkill => tilt * latentSkill)) := by
      constructor
      intro latentSkill
      exact tilted_absolutelyContinuous law
        (fun latentSkill => tilt * latentSkill) (measure_singleton latentSkill)
    letI : NoAtoms (law.tilted (fun latentSkill => tilt * latentSkill)) :=
      htilted_no_atoms
    have huniv :
        law.tilted (fun latentSkill => tilt * latentSkill) Set.univ = 0 := by
      rw [← Set.union_compl_self ({posteriorMean} : Set ℝ)]
      exact measure_union_null (measure_singleton posteriorMean) hsingleton_compl
    rw [IsProbabilityMeasure.measure_univ] at huniv
    norm_num at huniv
  exact lt_of_le_of_ne (variance_nonneg _ _) hvariance_ne_zero.symm

/--
The exponential-tilted mean of an atomless law with all real exponential moments
is strictly increasing in its tilt parameter.
-/
theorem lg21_exponentialTiltMean_strictMono
    (law : Measure ℝ) [IsProbabilityMeasure law] [NoAtoms law]
    (hexp : ∀ tilt : ℝ,
      Integrable (fun latentSkill : ℝ => Real.exp (tilt * latentSkill)) law) :
    StrictMono (lg21ExponentialTiltMean law) := by
  have hinterior : ∀ tilt : ℝ, tilt ∈ interior (integrableExpSet id law) := by
    intro tilt
    have hset : integrableExpSet id law = Set.univ := by
      ext t
      simpa [integrableExpSet] using hexp t
    simp [hset]
  have hmean_eq :
      lg21ExponentialTiltMean law = deriv (cgf id law) := by
    funext tilt
    exact integral_tilted_mul_self (hinterior tilt)
  apply strictMono_of_deriv_pos
  intro tilt
  rw [hmean_eq]
  calc
    0 < Var[id; law.tilted (fun latentSkill => tilt * latentSkill)] :=
      lg21_canonical_tilt_variance_pos law hexp tilt
    _ = iteratedDeriv 2 (cgf id law) tilt :=
      variance_tilted_mul (hinterior tilt)
    _ = deriv (deriv (cgf id law)) tilt := by
      rw [show 2 = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]

/--
Restricting a nondegenerate Gaussian to a positive-mass event preserves all
real exponential moments.  This is a direct measure restriction fact, not a
conditional-distribution assertion.
-/
theorem lg21_selectedGaussian_integrable_exp
    (priorMean : ℝ) (priorVariance : NNReal) (selected : Set ℝ)
    (hselected : 0 < gaussianReal priorMean priorVariance selected)
    (tilt : ℝ) :
    Integrable (fun latentSkill : ℝ => Real.exp (tilt * latentSkill))
      (lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected) := by
  unfold lg21NormalizedRestriction
  exact (integrable_exp_mul_gaussianReal (μ := priorMean) (v := priorVariance) tilt).restrict
    |>.smul_measure (ENNReal.inv_ne_top.mpr (ne_of_gt hselected))

/-- A positive-mass restriction of a nondegenerate Gaussian has no atoms. -/
theorem lg21_noAtoms_normalizedRestriction_gaussian
    (priorMean : ℝ) (priorVariance : NNReal) (selected : Set ℝ)
    (hvariance : priorVariance ≠ 0) :
    NoAtoms
      (lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected) := by
  letI : NoAtoms (gaussianReal priorMean priorVariance) :=
    noAtoms_gaussianReal hvariance
  constructor
  intro latentSkill
  rw [lg21NormalizedRestriction_apply
    (law := gaussianReal priorMean priorVariance)
    (event := selected) (target := {latentSkill})
    (measurableSet_singleton latentSkill)]
  rw [measure_mono_null inter_subset_left
    (measure_singleton latentSkill :
      gaussianReal priorMean priorVariance {latentSkill} = 0)]
  simp

/--
For a positive-mass selected subpopulation of a nondegenerate Gaussian, the
raw exponential-tilt mean is strictly increasing whenever its coefficient is
positive. This is not a Gaussian likelihood posterior theorem: the omitted
fixed quadratic likelihood tilt is material and is retained as an open
source/RCD bridge obligation elsewhere.

This theorem is intentionally conditional only on the displayed likelihood
family.  It does not identify that family with an LG21 source PBO or RCD.
-/
theorem lg21_selectedGaussianExponentialTiltMean_strictMono
    (priorMean : ℝ) (priorVariance : NNReal) (selected : Set ℝ)
    (tiltCoefficient : ℝ)
    (hvariance : priorVariance ≠ 0)
    (hselected : 0 < gaussianReal priorMean priorVariance selected)
    (hcoefficient : 0 < tiltCoefficient) :
    StrictMono
      (lg21SelectedGaussianExponentialTiltMean
        priorMean priorVariance selected tiltCoefficient) := by
  let selectedLaw : Measure ℝ :=
    lg21NormalizedRestriction (gaussianReal priorMean priorVariance) selected
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability
      (gaussianReal priorMean priorVariance) selected (ne_of_gt hselected)
      (measure_ne_top _ _)
  letI : NoAtoms selectedLaw := by
    simpa [selectedLaw] using
      (lg21_noAtoms_normalizedRestriction_gaussian
        priorMean priorVariance selected hvariance)
  have htilt : StrictMono (lg21ExponentialTiltMean selectedLaw) :=
    lg21_exponentialTiltMean_strictMono selectedLaw
      (fun tilt => by
        simpa [selectedLaw] using
          (lg21_selectedGaussian_integrable_exp
            priorMean priorVariance selected hselected tilt))
  change StrictMono
    (fun score => lg21ExponentialTiltMean selectedLaw
      (tiltCoefficient * score))
  exact htilt.comp (strictMono_mul_left_of_pos hcoefficient)

end

end LG21TestOptionalPolicies
