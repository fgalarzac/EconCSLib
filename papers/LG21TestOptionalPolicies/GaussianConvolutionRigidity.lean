import LG21TestOptionalPolicies.GaussianWeierstrassRigidity

/-!
# Gaussian convolution rigidity

This module is source-agnostic.  It packages the parts of the classical
Weierstrass-transform argument that Mathlib can presently verify directly:

* subtracting a constant from a Gaussian convolution;
* transporting a positive-mass zero set through the nondegenerate Gaussian
  tilt parameter map;
* analytic continuation of the signed complex MGF; and
* recovery of almost-everywhere equality from the two density measures.

The only deliberately explicit bridge is the Gaussian reweighting identity
in the main theorem.  It is the elementary density calculation relating a
shifted Gaussian convolution to the centered exponential tilt.  Mathlib has
the Gaussian MGF and density ingredients, but not this general signed-density
identity in a reusable form yet.  Keeping it as a hypothesis prevents that
calculation from becoming an unreviewed source-model assumption.
-/

namespace GaussianConvolutionRigidity

noncomputable section

open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

/-- The Gaussian smoothing of a real function at a latent mean. -/
def gaussianConvolution (f : ℝ → ℝ) (noiseVariance : NNReal) (mean : ℝ) : ℝ :=
  ∫ score, f score ∂gaussianReal mean noiseVariance

/--
The complex signed MGF of the positive and negative density measures of a
real function.  It is the analytic object identified by Gaussian smoothing.
-/
def signedDensityComplexMGF (μ : Measure ℝ) (f : ℝ → ℝ) : ℂ → ℂ :=
  complexMGF id (LG21TestOptionalPolicies.lg21PositiveDensityMeasure μ f) -
    complexMGF id (LG21TestOptionalPolicies.lg21NegativeDensityMeasure μ f)

/-- The tilt parameter induced by a nonzero Gaussian noise variance. -/
def gaussianTiltParameter (noiseVariance : NNReal) (mean : ℝ) : ℂ :=
  ((mean / (noiseVariance : ℝ) : ℝ) : ℂ)

theorem gaussianTiltParameter_measurable (noiseVariance : NNReal) :
    Measurable (gaussianTiltParameter noiseVariance) := by
  unfold gaussianTiltParameter
  fun_prop

theorem gaussianTiltParameter_injective
    {noiseVariance : NNReal} (hnoise : noiseVariance ≠ 0) :
    Function.Injective (gaussianTiltParameter noiseVariance) := by
  intro x y hxy
  have hreal : x / (noiseVariance : ℝ) = y / (noiseVariance : ℝ) :=
    Complex.ofReal_injective hxy
  exact (div_left_inj' (NNReal.coe_ne_zero.mpr hnoise)).mp hreal

/-- A nondegenerate Gaussian remains atomless after the tilt-parameter embedding. -/
theorem noAtoms_map_gaussianTiltParameter
    {populationMean : ℝ} {populationVariance noiseVariance : NNReal}
    (hpopulation : populationVariance ≠ 0)
    (hnoise : noiseVariance ≠ 0) :
    NoAtoms
      ((gaussianReal populationMean populationVariance).map
        (gaussianTiltParameter noiseVariance)) := by
  letI : NoAtoms (gaussianReal populationMean populationVariance) :=
    noAtoms_gaussianReal hpopulation
  constructor
  intro z
  rw [Measure.map_apply (gaussianTiltParameter_measurable noiseVariance)
    (measurableSet_singleton z)]
  apply Set.Subsingleton.measure_zero
  intro x hx y hy
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx hy
  exact gaussianTiltParameter_injective hnoise (hx.trans hy.symm)

/-- Subtracting a constant commutes with convolution by a probability Gaussian. -/
theorem gaussianConvolution_sub_const
    (f : ℝ → ℝ) (c mean : ℝ) (noiseVariance : NNReal)
    (hf : Integrable f (gaussianReal mean noiseVariance)) :
    gaussianConvolution (fun score ↦ f score - c) noiseVariance mean =
      gaussianConvolution f noiseVariance mean - c := by
  unfold gaussianConvolution
  rw [integral_sub hf (integrable_const c)]
  simp

/--
Rigidity of a deterministic Gaussian-smoothed rule from a positive-mass
constant-convolution set, conditional on the explicit Gaussian reweighting
identity below.

`hGaussianReweight` is the remaining library-level density calculation:
the shifted Gaussian law `N(q, v)` equals the centered law `N(0, v)` tilted
by `exp(q * score / v)` and multiplied by `exp(-q^2 / (2v))`.  Every other
step of the usual Weierstrass-transform proof is verified here.
-/
theorem ae_eq_const_of_positive_mass_gaussian_convolution
    (f : ℝ → ℝ) (c populationMean : ℝ)
    (populationVariance noiseVariance : NNReal)
    (hpopulation : populationVariance ≠ 0)
    (hnoise : noiseVariance ≠ 0)
    (hshiftIntegrable : ∀ mean,
      Integrable f (gaussianReal mean noiseVariance))
    (hpositive : 0 < (gaussianReal populationMean populationVariance)
      {mean | gaussianConvolution f noiseVariance mean = c})
    (hposFinite : IsFiniteMeasure
      (LG21TestOptionalPolicies.lg21PositiveDensityMeasure
        (gaussianReal 0 noiseVariance) (fun score ↦ f score - c)))
    (hnegFinite : IsFiniteMeasure
      (LG21TestOptionalPolicies.lg21NegativeDensityMeasure
        (gaussianReal 0 noiseVariance) (fun score ↦ f score - c)))
    (hposExp : ∀ t : ℝ,
      Integrable (fun score : ℝ ↦ rexp (t * score))
        (LG21TestOptionalPolicies.lg21PositiveDensityMeasure
          (gaussianReal 0 noiseVariance) (fun score ↦ f score - c)))
    (hnegExp : ∀ t : ℝ,
      Integrable (fun score : ℝ ↦ rexp (t * score))
        (LG21TestOptionalPolicies.lg21NegativeDensityMeasure
          (gaussianReal 0 noiseVariance) (fun score ↦ f score - c)))
    (hGaussianReweight : ∀ mean,
      (rexp (-(mean ^ 2) / (2 * (noiseVariance : ℝ))) : ℂ) *
          signedDensityComplexMGF (gaussianReal 0 noiseVariance)
            (fun score ↦ f score - c)
            (gaussianTiltParameter noiseVariance mean) =
        (gaussianConvolution (fun score ↦ f score - c) noiseVariance mean : ℂ)) :
    f =ᵐ[gaussianReal 0 noiseVariance] fun _ ↦ c := by
  let baseLaw : Measure ℝ := gaussianReal 0 noiseVariance
  let centered : ℝ → ℝ := fun score ↦ f score - c
  let positiveLaw : Measure ℝ :=
    LG21TestOptionalPolicies.lg21PositiveDensityMeasure baseLaw centered
  let negativeLaw : Measure ℝ :=
    LG21TestOptionalPolicies.lg21NegativeDensityMeasure baseLaw centered
  let analyticDifference : ℂ → ℂ := signedDensityComplexMGF baseLaw centered
  have hcenteredMeasurable : AEMeasurable centered baseLaw := by
    exact (hshiftIntegrable 0).aestronglyMeasurable.aemeasurable.sub
      measurable_const.aemeasurable
  letI : IsFiniteMeasure positiveLaw := by
    simpa [positiveLaw, baseLaw, centered] using hposFinite
  letI : IsFiniteMeasure negativeLaw := by
    simpa [negativeLaw, baseLaw, centered] using hnegFinite
  have hpositiveExp : ∀ t : ℝ,
      Integrable (fun score : ℝ ↦ rexp (t * score)) positiveLaw := by
    intro t
    simpa [positiveLaw, baseLaw, centered] using hposExp t
  have hnegativeExp : ∀ t : ℝ,
      Integrable (fun score : ℝ ↦ rexp (t * score)) negativeLaw := by
    intro t
    simpa [negativeLaw, baseLaw, centered] using hnegExp t
  have hpositiveUniv : integrableExpSet id positiveLaw = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    exact hpositiveExp t
  have hnegativeUniv : integrableExpSet id negativeLaw = Set.univ := by
    apply Set.eq_univ_of_forall
    intro t
    exact hnegativeExp t
  have hpositiveAnalytic :
      AnalyticOnNhd ℂ (complexMGF id positiveLaw) Set.univ := by
    have h := analyticOnNhd_complexMGF (X := id) (μ := positiveLaw)
    rw [hpositiveUniv] at h
    simpa using h
  have hnegativeAnalytic :
      AnalyticOnNhd ℂ (complexMGF id negativeLaw) Set.univ := by
    have h := analyticOnNhd_complexMGF (X := id) (μ := negativeLaw)
    rw [hnegativeUniv] at h
    simpa using h
  have hanalyticDifference : AnalyticOnNhd ℂ analyticDifference Set.univ := by
    simpa [analyticDifference, signedDensityComplexMGF, positiveLaw, negativeLaw]
      using hpositiveAnalytic.sub hnegativeAnalytic
  let latentLaw : Measure ℝ := gaussianReal populationMean populationVariance
  let tiltLaw : Measure ℂ := latentLaw.map (gaussianTiltParameter noiseVariance)
  letI : NoAtoms tiltLaw := by
    simpa [tiltLaw, latentLaw] using
      noAtoms_map_gaussianTiltParameter hpopulation hnoise
  have hzeroSetMeasurable :
      MeasurableSet {z | analyticDifference z = 0} := by
    exact hanalyticDifference.continuous.measurable (measurableSet_singleton 0)
  have hzeroSetPositive : 0 < tiltLaw {z | analyticDifference z = 0} := by
    rw [show tiltLaw = latentLaw.map (gaussianTiltParameter noiseVariance) by rfl,
      Measure.map_apply (gaussianTiltParameter_measurable noiseVariance)
        hzeroSetMeasurable]
    apply lt_of_lt_of_le hpositive
    apply measure_mono
    intro mean hmean
    have hcenteredZero : gaussianConvolution centered noiseVariance mean = 0 := by
      rw [gaussianConvolution_sub_const f c mean noiseVariance
        (hshiftIntegrable mean)]
      exact sub_eq_zero.mpr hmean
    have hfactor_ne_zero :
        (rexp (-(mean ^ 2) / (2 * (noiseVariance : ℝ))) : ℂ) ≠ 0 := by
      exact_mod_cast Real.exp_ne_zero _
    have hrawCenteredZero :
        gaussianConvolution (fun score ↦ f score - c) noiseVariance mean = 0 := by
      simpa [centered] using hcenteredZero
    have hproduct :
        (rexp (-(mean ^ 2) / (2 * (noiseVariance : ℝ))) : ℂ) *
            analyticDifference (gaussianTiltParameter noiseVariance mean) = 0 := by
      calc
        (rexp (-(mean ^ 2) / (2 * (noiseVariance : ℝ))) : ℂ) *
            analyticDifference (gaussianTiltParameter noiseVariance mean) =
            (gaussianConvolution (fun score ↦ f score - c)
              noiseVariance mean : ℂ) := by
          simpa [analyticDifference, baseLaw, centered] using hGaussianReweight mean
        _ = 0 := by simp [hrawCenteredZero]
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    exact (mul_eq_zero.mp hproduct).resolve_left hfactor_ne_zero
  have hanalyticZero : analyticDifference = 0 := by
    exact LG21TestOptionalPolicies.lg21_entire_analytic_eq_of_pos_measure_eq
      hanalyticDifference analyticOnNhd_const hzeroSetPositive
  have hmgf : mgf id positiveLaw = mgf id negativeLaw := by
    ext t
    have hzeroAt := congrFun hanalyticZero (t : ℂ)
    have hsub :
        (mgf id positiveLaw t : ℂ) - (mgf id negativeLaw t : ℂ) = 0 := by
      simpa [analyticDifference, signedDensityComplexMGF,
        complexMGF_ofReal] using hzeroAt
    exact_mod_cast sub_eq_zero.mp hsub
  have hcenteredZeroAE : centered =ᵐ[baseLaw] 0 := by
    exact LG21TestOptionalPolicies.lg21_ae_eq_zero_of_pos_neg_density_mgf_eq
      centered hcenteredMeasurable (by infer_instance) (by infer_instance)
      hpositiveExp hmgf
  filter_upwards [hcenteredZeroAE] with score hscore
  dsimp [centered] at hscore
  linarith

end

end GaussianConvolutionRigidity
