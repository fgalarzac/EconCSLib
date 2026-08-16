import LG21TestOptionalPolicies.Theorem32GaussianKernelCounterexample
import Mathlib.Probability.Kernel.Integral

/-!
# Continuous operational repair for LG21 Theorem 3.2

The printed theorem permits arbitrary randomized policy outputs.  For the
optional-reporting stage, a narrower source-compatible condition is enough:
the output conditional on a reported score is deterministic.  The no-report
branch remains an arbitrary probability law.

This module states the resulting conclusion at the operational level.  It
does not claim equality of a raw score-indexed policy at scores that have zero
probability under the equilibrium score law.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory

/--
The actual optional-reporting output kernel.  Reporting uses the deterministic
estimate `reportedValue`; not reporting uses the arbitrary `baseLaw`.
-/
def lg21OptionalDeterministicReporterKernel
    {Score : Type*} [MeasurableSpace Score]
    (reporterSet : Set Score) (hReporterSet : MeasurableSet reporterSet)
    (reportedValue : Score → ℝ) (hReportedValue : Measurable reportedValue)
    (baseLaw : Measure ℝ) : Kernel Score ℝ := by
  classical
  exact Kernel.piecewise hReporterSet
    (Kernel.deterministic reportedValue hReportedValue)
    (Kernel.const Score baseLaw)

/--
Measure cancellation for the operational optional-reporting mixture.  If a
positive-mass reporting set emits one fixed estimate, and no-reporters receive
the baseline law, fairness makes that baseline law the same point mass.
-/
theorem lg21_base_law_eq_dirac_of_positive_operational_reporter_mixture
    {Score : Type*} [MeasurableSpace Score]
    (scoreLaw : Measure Score) (baseLaw : Measure ℝ)
    [IsProbabilityMeasure scoreLaw] [IsProbabilityMeasure baseLaw]
    (reporterSet : Set Score) (hReporterSet : MeasurableSet reporterSet)
    (commonEstimate : ℝ)
    (hPositive : 0 < scoreLaw reporterSet)
    (hFixedPoint :
      baseLaw = scoreLaw reporterSet • Measure.dirac commonEstimate +
        scoreLaw reporterSetᶜ • baseLaw) :
    baseLaw = Measure.dirac commonEstimate := by
  let complement : Set ℝ := ({commonEstimate} : Set ℝ)ᶜ
  have hComplement : MeasurableSet complement := by
    exact measurableSet_singleton _ |>.compl
  have hFixedComplement :
      baseLaw complement = scoreLaw reporterSetᶜ * baseLaw complement := by
    calc
      baseLaw complement =
          (scoreLaw reporterSet • Measure.dirac commonEstimate +
            scoreLaw reporterSetᶜ • baseLaw) complement := by
        exact congrArg (fun law : Measure ℝ => law complement) hFixedPoint
      _ = scoreLaw reporterSetᶜ * baseLaw complement := by
        rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
        simp [complement, hComplement]
  have hReporterLeOne : scoreLaw reporterSet ≤ 1 := by
    calc
      scoreLaw reporterSet ≤ scoreLaw Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := IsProbabilityMeasure.measure_univ
  have hComplementScore :
      scoreLaw reporterSetᶜ = 1 - scoreLaw reporterSet := by
    calc
      scoreLaw reporterSetᶜ = scoreLaw Set.univ - scoreLaw reporterSet :=
        measure_compl hReporterSet (measure_ne_top scoreLaw reporterSet)
      _ = 1 - scoreLaw reporterSet := by rw [IsProbabilityMeasure.measure_univ]
  have hFixedComplement' :
      baseLaw complement =
        (1 - scoreLaw reporterSet) * baseLaw complement := by
    rw [← hComplementScore]
    exact hFixedComplement
  have hComplementZero : baseLaw complement = 0 := by
    have hFixedReal := congrArg ENNReal.toReal hFixedComplement'
    rw [ENNReal.toReal_mul, ENNReal.toReal_sub_of_le hReporterLeOne
      ENNReal.one_ne_top, ENNReal.toReal_one] at hFixedReal
    have hPositiveReal : 0 < (scoreLaw reporterSet).toReal :=
      ENNReal.toReal_pos (ne_of_gt hPositive)
        (measure_ne_top scoreLaw reporterSet)
    have hComplementNonneg : 0 ≤ (baseLaw complement).toReal := ENNReal.toReal_nonneg
    have hRealZero : (baseLaw complement).toReal = 0 := by nlinarith
    exact ((ENNReal.toReal_eq_zero_iff _).mp hRealZero).resolve_right
      (measure_ne_top baseLaw complement)
  apply Measure.ext
  intro target htarget
  by_cases hmem : commonEstimate ∈ target
  · have hDirac : Measure.dirac commonEstimate target = 1 :=
      dirac_eq_one_iff_mem htarget |>.mpr hmem
    rw [hDirac]
    apply le_antisymm
    · calc
        baseLaw target ≤ baseLaw Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := IsProbabilityMeasure.measure_univ
    · have hTargetComplZero : baseLaw targetᶜ = 0 := by
        apply measure_mono_null
        · intro x hx
          have hxne : x ≠ commonEstimate := by
            intro hxc
            subst x
            exact hx hmem
          simpa [complement] using hxne
        · exact hComplementZero
      have hAdd := measure_add_measure_compl (μ := baseLaw) htarget
      rw [hTargetComplZero, add_zero, IsProbabilityMeasure.measure_univ] at hAdd
      exact hAdd.symm.le
  · have hTargetZero : baseLaw target = 0 := by
      apply measure_mono_null
      · intro x hx
        have hxne : x ≠ commonEstimate := by
          intro hxc
          subst x
          exact hmem hx
        simpa [complement] using hxne
      · exact hComplementZero
    have hDiracZero : Measure.dirac commonEstimate target = 0 :=
      dirac_eq_zero_iff_not_mem htarget |>.mpr hmem
    rw [hTargetZero, hDiracZero]

/--
Under operational fairness, deterministic reported-score outputs, and ex-post
best response, every reporter receives the baseline expected estimate almost
everywhere.  The explicit tower and integrability hypotheses make this a
continuous-population result rather than a finite-support argument.
-/
theorem lg21_reporter_value_eq_base_mean_ae_of_operational_fairness
    {Score : Type*} [MeasurableSpace Score]
    (scoreLaw : Measure Score) (baseLaw : Measure ℝ)
    [IsProbabilityMeasure scoreLaw] [IsProbabilityMeasure baseLaw]
    (reporterSet : Set Score) (hReporterSet : MeasurableSet reporterSet)
    (reportedValue : Score → ℝ) (hReportedValue : Measurable reportedValue)
    (hBaseIntegrable : Integrable id baseLaw)
    (hOperationalMeanIntegrable :
      Integrable
        (fun score =>
          ∫ estimate,
            estimate ∂lg21OptionalDeterministicReporterKernel
              reporterSet hReporterSet reportedValue hReportedValue baseLaw score)
        scoreLaw)
    (hMeanTower :
      (∫ score,
          ∫ estimate,
            estimate ∂lg21OptionalDeterministicReporterKernel
              reporterSet hReporterSet reportedValue hReportedValue baseLaw score
          ∂scoreLaw) =
        ∫ estimate,
          estimate ∂scoreLaw.bind
            (lg21OptionalDeterministicReporterKernel
              reporterSet hReporterSet reportedValue hReportedValue baseLaw))
    (hOperationalFairness :
      scoreLaw.bind
          (lg21OptionalDeterministicReporterKernel
            reporterSet hReporterSet reportedValue hReportedValue baseLaw) =
        baseLaw)
    (hReportedBestResponse :
      ∀ᵐ score ∂scoreLaw.restrict reporterSet,
        (∫ estimate, estimate ∂baseLaw) ≤ reportedValue score) :
    ∀ᵐ score ∂scoreLaw.restrict reporterSet,
      reportedValue score = ∫ estimate, estimate ∂baseLaw := by
  classical
  let baseMean : ℝ := ∫ estimate, estimate ∂baseLaw
  let operationalKernel :=
    lg21OptionalDeterministicReporterKernel
      reporterSet hReporterSet reportedValue hReportedValue baseLaw
  let operationalMean : Score → ℝ :=
    fun score => ∫ estimate, estimate ∂operationalKernel score
  have hMeanFormula : ∀ score,
      operationalMean score =
        if score ∈ reporterSet then reportedValue score else baseMean := by
    intro score
    dsimp [operationalMean, operationalKernel,
      lg21OptionalDeterministicReporterKernel]
    rw [Kernel.integral_piecewise]
    simp [baseMean]
  have hBestResponseGlobal :
      ∀ᵐ score ∂scoreLaw,
        score ∈ reporterSet → baseMean ≤ reportedValue score := by
    simpa [baseMean] using ae_imp_of_ae_restrict hReportedBestResponse
  have hOperationalMeanGe :
      (fun _ : Score => baseMean) ≤ᵐ[scoreLaw] operationalMean := by
    filter_upwards [hBestResponseGlobal] with score hbest
    by_cases hreport : score ∈ reporterSet
    · rw [hMeanFormula score, if_pos hreport]
      exact hbest hreport
    · rw [hMeanFormula score, if_neg hreport]
  have hOperationalIntegral :
      (∫ score, operationalMean score ∂scoreLaw) = baseMean := by
    calc
      (∫ score, operationalMean score ∂scoreLaw) =
          ∫ estimate, estimate ∂scoreLaw.bind operationalKernel := by
        simpa [operationalMean, operationalKernel] using hMeanTower
      _ = ∫ estimate, estimate ∂baseLaw := by rw [hOperationalFairness]
      _ = baseMean := rfl
  have hConstIntegral :
      (∫ _score : Score, baseMean ∂scoreLaw) = baseMean := by
    simp
  have hWellDefinedOperationalMean :
      Integrable id baseLaw ∧
        (∫ score, operationalMean score ∂scoreLaw) = baseMean :=
    ⟨hBaseIntegrable, hOperationalIntegral⟩
  have hIntegralEq :
      (∫ score : Score, baseMean ∂scoreLaw) =
        ∫ score, operationalMean score ∂scoreLaw := by
    rw [hConstIntegral, hWellDefinedOperationalMean.2]
  have hOperationalMeanEq :
      (fun _ : Score => baseMean) =ᵐ[scoreLaw] operationalMean :=
    (integral_eq_iff_of_ae_le (integrable_const _) hOperationalMeanIntegrable
      hOperationalMeanGe).mp hIntegralEq
  rw [ae_restrict_iff' hReporterSet]
  filter_upwards [hOperationalMeanEq] with score hmean hreport
  rw [hMeanFormula score, if_pos hreport] at hmean
  exact hmean.symm

/--
Continuous optional-reporting operational blankness with deterministic reporter
outputs and an arbitrary no-report law.  The conclusion is deliberately
almost-everywhere in the equilibrium score law; it makes no off-support claim
about the raw policy at null scores.
-/
theorem lg21_optional_reporting_operational_blank_ae_of_deterministic_reporters
    {Score : Type*} [MeasurableSpace Score]
    (scoreLaw : Measure Score) (baseLaw : Measure ℝ)
    [IsProbabilityMeasure scoreLaw] [IsProbabilityMeasure baseLaw]
    (reporterSet : Set Score) (hReporterSet : MeasurableSet reporterSet)
    (reportedValue : Score → ℝ) (hReportedValue : Measurable reportedValue)
    (hPositiveReportingMass : 0 < scoreLaw reporterSet)
    (hBaseIntegrable : Integrable id baseLaw)
    (hOperationalMeanIntegrable :
      Integrable
        (fun score =>
          ∫ estimate,
            estimate ∂lg21OptionalDeterministicReporterKernel
              reporterSet hReporterSet reportedValue hReportedValue baseLaw score)
        scoreLaw)
    (hMeanTower :
      (∫ score,
          ∫ estimate,
            estimate ∂lg21OptionalDeterministicReporterKernel
              reporterSet hReporterSet reportedValue hReportedValue baseLaw score
          ∂scoreLaw) =
        ∫ estimate,
          estimate ∂scoreLaw.bind
            (lg21OptionalDeterministicReporterKernel
              reporterSet hReporterSet reportedValue hReportedValue baseLaw))
    (hOperationalFairness :
      scoreLaw.bind
          (lg21OptionalDeterministicReporterKernel
            reporterSet hReporterSet reportedValue hReportedValue baseLaw) =
        baseLaw)
    (hReportedBestResponse :
      ∀ᵐ score ∂scoreLaw.restrict reporterSet,
        (∫ estimate, estimate ∂baseLaw) ≤ reportedValue score) :
    baseLaw = Measure.dirac (∫ estimate, estimate ∂baseLaw) ∧
      ∀ᵐ score ∂scoreLaw,
        lg21OptionalDeterministicReporterKernel
          reporterSet hReporterSet reportedValue hReportedValue baseLaw score =
          Measure.dirac (∫ estimate, estimate ∂baseLaw) := by
  classical
  let baseMean : ℝ := ∫ estimate, estimate ∂baseLaw
  let operationalKernel :=
    lg21OptionalDeterministicReporterKernel
      reporterSet hReporterSet reportedValue hReportedValue baseLaw
  have hReporterValue :
      ∀ᵐ score ∂scoreLaw.restrict reporterSet,
        reportedValue score = baseMean := by
    simpa [baseMean] using
      lg21_reporter_value_eq_base_mean_ae_of_operational_fairness
        scoreLaw baseLaw reporterSet hReporterSet reportedValue hReportedValue
        hBaseIntegrable hOperationalMeanIntegrable hMeanTower
        hOperationalFairness hReportedBestResponse
  have hReporterBind :
      (scoreLaw.restrict reporterSet).bind
          (Kernel.deterministic reportedValue hReportedValue) =
        scoreLaw reporterSet • Measure.dirac baseMean := by
    calc
      (scoreLaw.restrict reporterSet).bind
          (Kernel.deterministic reportedValue hReportedValue) =
          (scoreLaw.restrict reporterSet).bind
            (fun _ => Measure.dirac baseMean) := by
        apply Measure.bind_congr_right
        filter_upwards [hReporterValue] with score hvalue
        rw [Kernel.deterministic_apply, hvalue]
      _ = (scoreLaw.restrict reporterSet) Set.univ •
          Measure.dirac baseMean := Measure.bind_const
      _ = scoreLaw reporterSet • Measure.dirac baseMean := by
        rw [Measure.restrict_apply_univ]
  have hNoReporterBind :
      (scoreLaw.restrict reporterSetᶜ).bind
          (Kernel.const Score baseLaw) =
        scoreLaw reporterSetᶜ • baseLaw := by
    change (scoreLaw.restrict reporterSetᶜ).bind (fun _ => baseLaw) = _
    rw [Measure.bind_const, Measure.restrict_apply_univ]
  have hOperationalMixture :
      scoreLaw.bind operationalKernel =
        scoreLaw reporterSet • Measure.dirac baseMean +
          scoreLaw reporterSetᶜ • baseLaw := by
    calc
      scoreLaw.bind operationalKernel =
          (scoreLaw.restrict reporterSet).bind
              (Kernel.deterministic reportedValue hReportedValue) +
            (scoreLaw.restrict reporterSetᶜ).bind (Kernel.const Score baseLaw) := by
        simpa [operationalKernel, lg21OptionalDeterministicReporterKernel]
          using lg21_measure_bind_piecewise_kernel
            scoreLaw reporterSet hReporterSet
            (Kernel.deterministic reportedValue hReportedValue)
            (Kernel.const Score baseLaw)
      _ = scoreLaw reporterSet • Measure.dirac baseMean +
            scoreLaw reporterSetᶜ • baseLaw := by
        rw [hReporterBind, hNoReporterBind]
  have hFixedPoint :
      baseLaw = scoreLaw reporterSet • Measure.dirac baseMean +
        scoreLaw reporterSetᶜ • baseLaw := by
    calc
      baseLaw = scoreLaw.bind operationalKernel := hOperationalFairness.symm
      _ = scoreLaw reporterSet • Measure.dirac baseMean +
            scoreLaw reporterSetᶜ • baseLaw := hOperationalMixture
  have hBaseLaw : baseLaw = Measure.dirac baseMean :=
    lg21_base_law_eq_dirac_of_positive_operational_reporter_mixture
      scoreLaw baseLaw reporterSet hReporterSet baseMean
      hPositiveReportingMass hFixedPoint
  refine ⟨by simpa [baseMean] using hBaseLaw, ?_⟩
  have hReporterValueGlobal :
      ∀ᵐ score ∂scoreLaw,
        score ∈ reporterSet → reportedValue score = baseMean :=
    ae_imp_of_ae_restrict hReporterValue
  filter_upwards [hReporterValueGlobal] with score hvalue
  by_cases hreport : score ∈ reporterSet
  · rw [lg21OptionalDeterministicReporterKernel, Kernel.piecewise_apply,
      if_pos hreport, Kernel.deterministic_apply, hvalue hreport]
  · have hNoReportKernel :
        lg21OptionalDeterministicReporterKernel
            reporterSet hReporterSet reportedValue hReportedValue baseLaw score =
          baseLaw := by
      rw [lg21OptionalDeterministicReporterKernel, Kernel.piecewise_apply,
        if_neg hreport, Kernel.const_apply]
    calc
      lg21OptionalDeterministicReporterKernel
          reporterSet hReporterSet reportedValue hReportedValue baseLaw score =
          baseLaw := hNoReportKernel
      _ = Measure.dirac baseMean := hBaseLaw
      _ = Measure.dirac (∫ estimate, estimate ∂baseLaw) := rfl

/--
The source's operational notion of test blankness for optional reporting.  If
no score is reported with positive mass, reporting is unused in equilibrium.
Otherwise the actual output kernel must agree with the no-report law almost
everywhere under the equilibrium score law.
-/
def LG21OptionalOperationalTestBlank
    {Score : Type*} [MeasurableSpace Score]
    (scoreLaw : Measure Score) (baseLaw : Measure ℝ)
    (reporterSet : Set Score) (operationalKernel : Kernel Score ℝ) : Prop :=
  scoreLaw reporterSet = 0 ∨
    ∀ᵐ score ∂scoreLaw, operationalKernel score = baseLaw

/--
The deterministic-reporter repair, including the source convention that an
equilibrium with zero reporter mass is operationally test-blank.  In the
positive-mass branch, the preceding theorem proves the stronger collapse of
the base law to a point mass before deriving operational blankness.
-/
theorem lg21_optional_reporting_operational_test_blank_of_deterministic_reporters
    {Score : Type*} [MeasurableSpace Score]
    (scoreLaw : Measure Score) (baseLaw : Measure ℝ)
    [IsProbabilityMeasure scoreLaw] [IsProbabilityMeasure baseLaw]
    (reporterSet : Set Score) (hReporterSet : MeasurableSet reporterSet)
    (reportedValue : Score → ℝ) (hReportedValue : Measurable reportedValue)
    (hBaseIntegrable : Integrable id baseLaw)
    (hOperationalMeanIntegrable :
      Integrable
        (fun score =>
          ∫ estimate,
            estimate ∂lg21OptionalDeterministicReporterKernel
              reporterSet hReporterSet reportedValue hReportedValue baseLaw score)
        scoreLaw)
    (hMeanTower :
      (∫ score,
          ∫ estimate,
            estimate ∂lg21OptionalDeterministicReporterKernel
              reporterSet hReporterSet reportedValue hReportedValue baseLaw score
          ∂scoreLaw) =
        ∫ estimate,
          estimate ∂scoreLaw.bind
            (lg21OptionalDeterministicReporterKernel
              reporterSet hReporterSet reportedValue hReportedValue baseLaw))
    (hOperationalFairness :
      scoreLaw.bind
          (lg21OptionalDeterministicReporterKernel
            reporterSet hReporterSet reportedValue hReportedValue baseLaw) =
        baseLaw)
    (hReportedBestResponse :
      ∀ᵐ score ∂scoreLaw.restrict reporterSet,
        (∫ estimate, estimate ∂baseLaw) ≤ reportedValue score) :
    LG21OptionalOperationalTestBlank scoreLaw baseLaw reporterSet
      (lg21OptionalDeterministicReporterKernel
        reporterSet hReporterSet reportedValue hReportedValue baseLaw) := by
  by_cases hZeroReporting : scoreLaw reporterSet = 0
  · exact Or.inl hZeroReporting
  · right
    have hPositiveReporting : 0 < scoreLaw reporterSet :=
      pos_iff_ne_zero.mpr hZeroReporting
    rcases lg21_optional_reporting_operational_blank_ae_of_deterministic_reporters
        scoreLaw baseLaw reporterSet hReporterSet reportedValue hReportedValue
        hPositiveReporting hBaseIntegrable hOperationalMeanIntegrable hMeanTower
        hOperationalFairness hReportedBestResponse with
      ⟨hBaseLaw, hOperationalBlank⟩
    filter_upwards [hOperationalBlank] with score hscore
    exact hscore.trans hBaseLaw.symm

end

end LG21TestOptionalPolicies
