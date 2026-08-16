import LG21TestOptionalPolicies.Theorem32ReportRequiredDeterministicReporterRepair
import LG21TestOptionalPolicies.GaussianConvolutionRigidity
import LG21TestOptionalPolicies.GaussianShiftIntegrability
import LG21TestOptionalPolicies.GaussianTiltIdentity

/-!
# Report-required Gaussian conclusion for LG21 Theorem 3.2

This scratch module joins the checked game-theoretic reduction with the
Gaussian convolution-rigidity argument.  It deliberately models only the
reporting branch as deterministic: the no-report outcome remains the
arbitrary probability law `baseLaw`.

The first theorem transports a centered-Gaussian almost-everywhere conclusion
to every shifted Gaussian score law.  The second turns that pointwise-in-skill
fact into the point-mass reporter law required by the operational mixture
cancellation lemma.  The final theorem leaves the Gaussian reweighting
identity explicit only while that library identity is being supplied by the
dedicated Gaussian module; it is a proof obligation, not a source-model
assumption.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal MeasureTheory ProbabilityTheory Topology

/-- A centered Gaussian a.e. equality holds under every nondegenerate shift. -/
theorem lg21_ae_eq_const_under_all_gaussian_shifts_of_centered
    (f : ℝ -> ℝ) (c : ℝ) (noiseVariance : NNReal)
    (hnoise : noiseVariance ≠ 0)
    (hCentered : f =ᵐ[gaussianReal 0 noiseVariance] fun _ => c) :
    ∀ mean, f =ᵐ[gaussianReal mean noiseVariance] fun _ => c := by
  intro mean
  have hVolume : f =ᵐ[volume] fun _ => c :=
    (gaussianReal_absolutelyContinuous' 0 hnoise).ae_eq hCentered
  exact (gaussianReal_absolutelyContinuous mean hnoise).ae_eq hVolume

/-- A deterministic score rule which is constant under every shifted score law has a Dirac law. -/
theorem lg21_gaussian_reported_law_eq_dirac_of_centered_ae
    (f : ℝ -> ℝ) (c : ℝ) (noiseVariance : NNReal)
    (hnoise : noiseVariance ≠ 0)
    (hCentered : f =ᵐ[gaussianReal 0 noiseVariance] fun _ => c) :
    ∀ mean, (gaussianReal mean noiseVariance).map f = Measure.dirac c := by
  intro mean
  have hShifted :=
    lg21_ae_eq_const_under_all_gaussian_shifts_of_centered
      f c noiseVariance hnoise hCentered mean
  calc
    (gaussianReal mean noiseVariance).map f =
        (gaussianReal mean noiseVariance).map (fun _ => c) :=
      Measure.map_congr hShifted
    _ = Measure.dirac c := by simp

/--
The report-required deterministic-reporter conclusion, conditional only on
the explicitly named Gaussian density identity.  The conclusion is
operational: an arbitrary common no-report law collapses to the same point
mass, and the actual output kernel equals it almost everywhere.
-/
theorem lg21_report_required_operational_blank_ae_of_deterministic_gaussian_reporters_of_reweighting
    (baseLaw : Measure ℝ) [IsProbabilityMeasure baseLaw]
    (populationMean : ℝ) (populationVariance noiseVariance : NNReal)
    (hpopulation : populationVariance ≠ 0)
    (hnoise : noiseVariance ≠ 0)
    (takerSet : Set ℝ) (hTakerSet : MeasurableSet takerSet)
    (reportedKernel : Kernel ℝ ℝ) (f : ℝ -> ℝ)
    (hReportedKernel : ∀ skill,
      reportedKernel skill = (gaussianReal skill noiseVariance).map f)
    (hshiftIntegrable : ∀ mean,
      Integrable f (gaussianReal mean noiseVariance))
    (hOperationalMeanIntegrable :
      Integrable
        (fun skill =>
          ∫ estimate, estimate ∂lg21ReportRequiredOperationalKernel
            takerSet hTakerSet reportedKernel baseLaw skill)
        (gaussianReal populationMean populationVariance))
    (hMeanTower :
      (∫ skill,
          ∫ estimate, estimate ∂lg21ReportRequiredOperationalKernel
            takerSet hTakerSet reportedKernel baseLaw skill
          ∂(gaussianReal populationMean populationVariance)) =
        ∫ estimate, estimate ∂(gaussianReal populationMean populationVariance).bind
          (lg21ReportRequiredOperationalKernel
            takerSet hTakerSet reportedKernel baseLaw))
    (hOperationalFairness :
      (gaussianReal populationMean populationVariance).bind
        (lg21ReportRequiredOperationalKernel
          takerSet hTakerSet reportedKernel baseLaw) = baseLaw)
    (hTakerBestResponse :
      ∀ᵐ skill ∂(gaussianReal populationMean populationVariance).restrict takerSet,
        (∫ estimate, estimate ∂baseLaw) <=
          GaussianConvolutionRigidity.gaussianConvolution f noiseVariance skill)
    (hPositiveTaking :
      0 < (gaussianReal populationMean populationVariance) takerSet)
    (hGaussianReweight : ∀ mean,
      (rexp (-(mean ^ 2) / (2 * (noiseVariance : ℝ))) : ℂ) *
          GaussianConvolutionRigidity.signedDensityComplexMGF
            (gaussianReal 0 noiseVariance) (fun score => f score - ∫ estimate, estimate ∂baseLaw)
            (GaussianConvolutionRigidity.gaussianTiltParameter noiseVariance mean) =
        (GaussianConvolutionRigidity.gaussianConvolution
          (fun score => f score - ∫ estimate, estimate ∂baseLaw)
          noiseVariance mean : ℂ)) :
    baseLaw = Measure.dirac (∫ estimate, estimate ∂baseLaw) ∧
      ∀ᵐ skill ∂(gaussianReal populationMean populationVariance),
        lg21ReportRequiredOperationalKernel
          takerSet hTakerSet reportedKernel baseLaw skill = baseLaw := by
  let baseMean : ℝ := ∫ estimate, estimate ∂baseLaw
  have hSelectedMean : ∀ skill,
      (∫ estimate, estimate ∂reportedKernel skill) =
        GaussianConvolutionRigidity.gaussianConvolution f noiseVariance skill := by
    intro skill
    rw [hReportedKernel skill]
    simpa [GaussianConvolutionRigidity.gaussianConvolution] using
      (MeasureTheory.integral_map
        (μ := gaussianReal skill noiseVariance) (φ := f)
        (hshiftIntegrable skill).aemeasurable aestronglyMeasurable_id
        (f := fun estimate : ℝ => estimate))
  have hTakerMean :
      ∀ᵐ skill ∂(gaussianReal populationMean populationVariance).restrict takerSet,
        GaussianConvolutionRigidity.gaussianConvolution f noiseVariance skill = baseMean := by
    simpa [baseMean] using
      lg21_report_required_taker_mean_eq_base_mean_ae_of_operational_fairness
        (gaussianReal populationMean populationVariance) baseLaw takerSet hTakerSet
        reportedKernel
        (GaussianConvolutionRigidity.gaussianConvolution f noiseVariance)
        hSelectedMean hOperationalMeanIntegrable hMeanTower hOperationalFairness
        hTakerBestResponse
  have hPositiveConvolution :
      0 < (gaussianReal populationMean populationVariance)
        {skill | GaussianConvolutionRigidity.gaussianConvolution f noiseVariance skill = baseMean} :=
    lg21_positive_convolution_equality_mass_of_taker_mean_eq_ae
      (gaussianReal populationMean populationVariance) takerSet hTakerSet
      (GaussianConvolutionRigidity.gaussianConvolution f noiseVariance) baseMean
      hPositiveTaking hTakerMean
  obtain ⟨hposFinite, hnegFinite, hposExp, hnegExp⟩ :=
    GaussianConvolutionRigidity.gaussian_convolution_regularities_of_integrable_all_gaussian_shifts
      f baseMean noiseVariance hnoise hshiftIntegrable
  have hCentered : f =ᵐ[gaussianReal 0 noiseVariance] fun _ => baseMean := by
    apply GaussianConvolutionRigidity.ae_eq_const_of_positive_mass_gaussian_convolution
      f baseMean populationMean populationVariance noiseVariance hpopulation hnoise
      hshiftIntegrable hPositiveConvolution hposFinite hnegFinite hposExp hnegExp
    simpa [baseMean] using hGaussianReweight
  have hReportedLaw : ∀ skill,
      reportedKernel skill = Measure.dirac baseMean := by
    intro skill
    rw [hReportedKernel skill]
    exact lg21_gaussian_reported_law_eq_dirac_of_centered_ae
      f baseMean noiseVariance hnoise hCentered skill
  have hTakerLaw :
      ∀ᵐ skill ∂(gaussianReal populationMean populationVariance).restrict takerSet,
        reportedKernel skill = Measure.dirac baseMean :=
    Filter.Eventually.of_forall hReportedLaw
  simpa [baseMean] using
    lg21_report_required_operational_blank_ae_of_common_taker_law
      (gaussianReal populationMean populationVariance) baseLaw takerSet hTakerSet
      reportedKernel baseMean hPositiveTaking hTakerLaw hOperationalFairness

/--
The Gaussian reweighting equation used by convolution rigidity follows from
the reporting rule's integrability under every Gaussian shift.  This is a
proved analytic bridge, rather than an additional source-model condition.
-/
theorem lg21_gaussian_reweighting_of_integrable_all_gaussian_shifts
    (f : ℝ -> ℝ) (c : ℝ) (noiseVariance : NNReal)
    (hnoise : noiseVariance ≠ 0)
    (hshiftIntegrable : ∀ mean,
      Integrable f (gaussianReal mean noiseVariance)) :
    ∀ mean,
      (rexp (-(mean ^ 2) / (2 * (noiseVariance : ℝ))) : ℂ) *
          GaussianConvolutionRigidity.signedDensityComplexMGF
            (gaussianReal 0 noiseVariance) (fun score => f score - c)
            (GaussianConvolutionRigidity.gaussianTiltParameter noiseVariance mean) =
        (GaussianConvolutionRigidity.gaussianConvolution
          (fun score => f score - c) noiseVariance mean : ℂ) := by
  intro mean
  obtain ⟨_hposFinite, _hnegFinite, hposExp, hnegExp⟩ :=
    GaussianConvolutionRigidity.gaussian_convolution_regularities_of_integrable_all_gaussian_shifts
      f c noiseVariance hnoise hshiftIntegrable
  exact GaussianConvolutionRigidity.gaussianConvolution_reweighting_identity_at_mean
    noiseVariance hnoise mean (fun score => f score - c)
    ((hshiftIntegrable 0).sub (integrable_const c)).aemeasurable
    (hposExp (mean / (noiseVariance : ℝ)))
    (hnegExp (mean / (noiseVariance : ℝ)))

/--
The fully discharged report-required branch for deterministic reporting after
the test.  The no-report branch is still an arbitrary common probability law;
the conclusion proves that operational fairness and equilibrium collapse it to
the same point mass as the reporting branch.
-/
theorem lg21_report_required_operational_blank_ae_of_deterministic_gaussian_reporters
    (baseLaw : Measure ℝ) [IsProbabilityMeasure baseLaw]
    (populationMean : ℝ) (populationVariance noiseVariance : NNReal)
    (hpopulation : populationVariance ≠ 0)
    (hnoise : noiseVariance ≠ 0)
    (takerSet : Set ℝ) (hTakerSet : MeasurableSet takerSet)
    (reportedKernel : Kernel ℝ ℝ) (f : ℝ -> ℝ)
    (hReportedKernel : ∀ skill,
      reportedKernel skill = (gaussianReal skill noiseVariance).map f)
    (hshiftIntegrable : ∀ mean,
      Integrable f (gaussianReal mean noiseVariance))
    (hOperationalMeanIntegrable :
      Integrable
        (fun skill =>
          ∫ estimate, estimate ∂lg21ReportRequiredOperationalKernel
            takerSet hTakerSet reportedKernel baseLaw skill)
        (gaussianReal populationMean populationVariance))
    (hMeanTower :
      (∫ skill,
          ∫ estimate, estimate ∂lg21ReportRequiredOperationalKernel
            takerSet hTakerSet reportedKernel baseLaw skill
          ∂(gaussianReal populationMean populationVariance)) =
        ∫ estimate, estimate ∂(gaussianReal populationMean populationVariance).bind
          (lg21ReportRequiredOperationalKernel
            takerSet hTakerSet reportedKernel baseLaw))
    (hOperationalFairness :
      (gaussianReal populationMean populationVariance).bind
        (lg21ReportRequiredOperationalKernel
          takerSet hTakerSet reportedKernel baseLaw) = baseLaw)
    (hTakerBestResponse :
      ∀ᵐ skill ∂(gaussianReal populationMean populationVariance).restrict takerSet,
        (∫ estimate, estimate ∂baseLaw) <=
          GaussianConvolutionRigidity.gaussianConvolution f noiseVariance skill)
    (hPositiveTaking :
      0 < (gaussianReal populationMean populationVariance) takerSet) :
    baseLaw = Measure.dirac (∫ estimate, estimate ∂baseLaw) ∧
      ∀ᵐ skill ∂(gaussianReal populationMean populationVariance),
        lg21ReportRequiredOperationalKernel
          takerSet hTakerSet reportedKernel baseLaw skill = baseLaw := by
  apply lg21_report_required_operational_blank_ae_of_deterministic_gaussian_reporters_of_reweighting
    baseLaw populationMean populationVariance noiseVariance hpopulation hnoise
    takerSet hTakerSet reportedKernel f hReportedKernel hshiftIntegrable
    hOperationalMeanIntegrable hMeanTower hOperationalFairness hTakerBestResponse
    hPositiveTaking
  exact lg21_gaussian_reweighting_of_integrable_all_gaussian_shifts
    f (∫ estimate, estimate ∂baseLaw) noiseVariance hnoise hshiftIntegrable

end

end LG21TestOptionalPolicies
