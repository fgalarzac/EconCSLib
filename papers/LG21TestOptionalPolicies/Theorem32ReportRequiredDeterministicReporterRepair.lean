import LG21TestOptionalPolicies.Theorem32ContinuousDeterministicReporterRepair

/-!
# Report-required operational reduction for LG21 Theorem 3.2

This module handles the game-theoretic portion of the report-required branch
of the deterministic-reporter repair.  Taking is chosen before the noisy test
score is realized, so its payoff is the conditional expected reporting output.
Operational fairness and best response force that expected reporting output to
equal the no-test mean almost everywhere on any positive-mass taking set.

The Gaussian rigidity step which turns this equality on takers into
score-level blankness is kept in `GaussianConvolutionRigidity.lean`.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory

/--
The actual output kernel for report-required-after-taking.  Takers receive the
score-generated `reportedKernel`; non-takers receive the unrestricted
no-report law `baseLaw`.
-/
def lg21ReportRequiredOperationalKernel
    (takerSet : Set ℝ) (hTakerSet : MeasurableSet takerSet)
    (reportedKernel : Kernel ℝ ℝ) (baseLaw : Measure ℝ) : Kernel ℝ ℝ := by
  classical
  exact Kernel.piecewise hTakerSet reportedKernel (Kernel.const ℝ baseLaw)

/--
At report-required timing, operational fairness and equilibrium best response
identify the expected reporting output on takers.  Unlike the previous
mean-identification repair, this conclusion does not assume that an equality
of means identifies an output law.
-/
theorem lg21_report_required_taker_mean_eq_base_mean_ae_of_operational_fairness
    (skillLaw : Measure ℝ) (baseLaw : Measure ℝ)
    [IsProbabilityMeasure skillLaw] [IsProbabilityMeasure baseLaw]
    (takerSet : Set ℝ) (hTakerSet : MeasurableSet takerSet)
    (reportedKernel : Kernel ℝ ℝ) (selectedMean : ℝ -> ℝ)
    (hSelectedMean :
      ∀ skill, (∫ estimate, estimate ∂reportedKernel skill) = selectedMean skill)
    (hOperationalMeanIntegrable :
      Integrable
        (fun skill =>
          ∫ estimate, estimate ∂lg21ReportRequiredOperationalKernel
            takerSet hTakerSet reportedKernel baseLaw skill)
        skillLaw)
    (hMeanTower :
      (∫ skill,
          ∫ estimate, estimate ∂lg21ReportRequiredOperationalKernel
            takerSet hTakerSet reportedKernel baseLaw skill
          ∂skillLaw) =
        ∫ estimate, estimate ∂skillLaw.bind
          (lg21ReportRequiredOperationalKernel
            takerSet hTakerSet reportedKernel baseLaw))
    (hOperationalFairness :
      skillLaw.bind (lg21ReportRequiredOperationalKernel
        takerSet hTakerSet reportedKernel baseLaw) = baseLaw)
    (hTakerBestResponse :
      ∀ᵐ skill ∂skillLaw.restrict takerSet,
        (∫ estimate, estimate ∂baseLaw) <= selectedMean skill) :
    ∀ᵐ skill ∂skillLaw.restrict takerSet,
      selectedMean skill = ∫ estimate, estimate ∂baseLaw := by
  classical
  let baseMean : ℝ := ∫ estimate, estimate ∂baseLaw
  let operationalKernel :=
    lg21ReportRequiredOperationalKernel takerSet hTakerSet reportedKernel baseLaw
  let operationalMean : ℝ -> ℝ :=
    fun skill => ∫ estimate, estimate ∂operationalKernel skill
  have hMeanFormula : ∀ skill,
      operationalMean skill =
        if skill ∈ takerSet then selectedMean skill else baseMean := by
    intro skill
    dsimp [operationalMean, operationalKernel,
      lg21ReportRequiredOperationalKernel]
    rw [Kernel.integral_piecewise]
    rw [hSelectedMean]
    simp [baseMean]
  have hBestResponseGlobal :
      ∀ᵐ skill ∂skillLaw,
        skill ∈ takerSet -> baseMean <= selectedMean skill := by
    simpa [baseMean] using ae_imp_of_ae_restrict hTakerBestResponse
  have hOperationalMeanGe :
      (fun _ : ℝ => baseMean) ≤ᵐ[skillLaw] operationalMean := by
    filter_upwards [hBestResponseGlobal] with skill hbest
    by_cases htakes : skill ∈ takerSet
    · rw [hMeanFormula skill, if_pos htakes]
      exact hbest htakes
    · rw [hMeanFormula skill, if_neg htakes]
  have hOperationalIntegral :
      (∫ skill, operationalMean skill ∂skillLaw) = baseMean := by
    calc
      (∫ skill, operationalMean skill ∂skillLaw) =
          ∫ estimate, estimate ∂skillLaw.bind operationalKernel := by
        simpa [operationalMean, operationalKernel] using hMeanTower
      _ = ∫ estimate, estimate ∂baseLaw := by rw [hOperationalFairness]
      _ = baseMean := rfl
  have hConstIntegral :
      (∫ _skill : ℝ, baseMean ∂skillLaw) = baseMean := by
    simp
  have hIntegralEq :
      (∫ skill : ℝ, baseMean ∂skillLaw) =
        ∫ skill, operationalMean skill ∂skillLaw := by
    rw [hConstIntegral, hOperationalIntegral]
  have hOperationalMeanEq :
      (fun _ : ℝ => baseMean) =ᵐ[skillLaw] operationalMean :=
    (integral_eq_iff_of_ae_le (integrable_const _)
      hOperationalMeanIntegrable hOperationalMeanGe).mp hIntegralEq
  rw [ae_restrict_iff' hTakerSet]
  filter_upwards [hOperationalMeanEq] with skill hmean htakes
  rw [hMeanFormula skill, if_pos htakes] at hmean
  exact hmean.symm

/-- A positive-mass taking set remains a positive-mass equality set. -/
theorem lg21_positive_convolution_equality_mass_of_taker_mean_eq_ae
    (skillLaw : Measure ℝ) (takerSet : Set ℝ) (hTakerSet : MeasurableSet takerSet)
    (selectedMean : ℝ -> ℝ) (baseMean : ℝ)
    (hPositiveTaking : 0 < skillLaw takerSet)
    (hTakerMean :
      ∀ᵐ skill ∂skillLaw.restrict takerSet,
        selectedMean skill = baseMean) :
    0 < skillLaw {skill | selectedMean skill = baseMean} := by
  have hSubsetAE :
      takerSet ≤ᵐ[skillLaw] {skill | selectedMean skill = baseMean} := by
    rw [ae_restrict_iff' hTakerSet] at hTakerMean
    exact hTakerMean
  exact lt_of_lt_of_le hPositiveTaking (measure_mono_ae hSubsetAE)

/--
Once every taking type's realized output law is a common point mass almost
everywhere, the same positive-mixture cancellation used for optional reporting
collapses the arbitrary no-take law.  This is independent of how the common
point-mass conclusion was obtained (Gaussian rigidity supplies it below).
-/
theorem lg21_report_required_operational_blank_ae_of_common_taker_law
    (skillLaw : Measure ℝ) (baseLaw : Measure ℝ)
    [IsProbabilityMeasure skillLaw] [IsProbabilityMeasure baseLaw]
    (takerSet : Set ℝ) (hTakerSet : MeasurableSet takerSet)
    (reportedKernel : Kernel ℝ ℝ) (commonEstimate : ℝ)
    (hPositiveTaking : 0 < skillLaw takerSet)
    (hTakerLaw :
      ∀ᵐ skill ∂skillLaw.restrict takerSet,
        reportedKernel skill = Measure.dirac commonEstimate)
    (hOperationalFairness :
      skillLaw.bind (lg21ReportRequiredOperationalKernel
        takerSet hTakerSet reportedKernel baseLaw) = baseLaw) :
    baseLaw = Measure.dirac commonEstimate ∧
      ∀ᵐ skill ∂skillLaw,
        lg21ReportRequiredOperationalKernel
          takerSet hTakerSet reportedKernel baseLaw skill = baseLaw := by
  classical
  let operationalKernel :=
    lg21ReportRequiredOperationalKernel takerSet hTakerSet reportedKernel baseLaw
  have hTakerBind :
      (skillLaw.restrict takerSet).bind reportedKernel =
        skillLaw takerSet • Measure.dirac commonEstimate := by
    calc
      (skillLaw.restrict takerSet).bind reportedKernel =
          (skillLaw.restrict takerSet).bind
            (fun _ => Measure.dirac commonEstimate) := by
        apply Measure.bind_congr_right
        filter_upwards [hTakerLaw] with skill hskill
        exact hskill
      _ = (skillLaw.restrict takerSet) Set.univ •
          Measure.dirac commonEstimate := Measure.bind_const
      _ = skillLaw takerSet • Measure.dirac commonEstimate := by
        rw [Measure.restrict_apply_univ]
  have hNoTakerBind :
      (skillLaw.restrict takerSetᶜ).bind (Kernel.const ℝ baseLaw) =
        skillLaw takerSetᶜ • baseLaw := by
    change (skillLaw.restrict takerSetᶜ).bind (fun _ => baseLaw) = _
    rw [Measure.bind_const, Measure.restrict_apply_univ]
  have hOperationalMixture :
      skillLaw.bind operationalKernel =
        skillLaw takerSet • Measure.dirac commonEstimate +
          skillLaw takerSetᶜ • baseLaw := by
    calc
      skillLaw.bind operationalKernel =
          (skillLaw.restrict takerSet).bind reportedKernel +
            (skillLaw.restrict takerSetᶜ).bind (Kernel.const ℝ baseLaw) := by
        simpa [operationalKernel, lg21ReportRequiredOperationalKernel]
          using lg21_measure_bind_piecewise_kernel
            skillLaw takerSet hTakerSet reportedKernel (Kernel.const ℝ baseLaw)
      _ = skillLaw takerSet • Measure.dirac commonEstimate +
            skillLaw takerSetᶜ • baseLaw := by
        rw [hTakerBind, hNoTakerBind]
  have hFixedPoint :
      baseLaw = skillLaw takerSet • Measure.dirac commonEstimate +
        skillLaw takerSetᶜ • baseLaw := by
    calc
      baseLaw = skillLaw.bind operationalKernel := hOperationalFairness.symm
      _ = skillLaw takerSet • Measure.dirac commonEstimate +
            skillLaw takerSetᶜ • baseLaw := hOperationalMixture
  have hBaseLaw : baseLaw = Measure.dirac commonEstimate :=
    lg21_base_law_eq_dirac_of_positive_operational_reporter_mixture
      skillLaw baseLaw takerSet hTakerSet commonEstimate
      hPositiveTaking hFixedPoint
  refine ⟨hBaseLaw, ?_⟩
  have hTakerLawGlobal :
      ∀ᵐ skill ∂skillLaw,
        skill ∈ takerSet -> reportedKernel skill = Measure.dirac commonEstimate :=
    ae_imp_of_ae_restrict hTakerLaw
  filter_upwards [hTakerLawGlobal] with skill hskill
  by_cases htakes : skill ∈ takerSet
  · calc
      lg21ReportRequiredOperationalKernel
          takerSet hTakerSet reportedKernel baseLaw skill = reportedKernel skill := by
            rw [lg21ReportRequiredOperationalKernel, Kernel.piecewise_apply,
              if_pos htakes]
      _ = Measure.dirac commonEstimate := hskill htakes
      _ = baseLaw := hBaseLaw.symm
  · rw [lg21ReportRequiredOperationalKernel, Kernel.piecewise_apply,
      if_neg htakes, Kernel.const_apply]

end

end LG21TestOptionalPolicies
