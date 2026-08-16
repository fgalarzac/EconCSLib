import LG21TestOptionalPolicies.ReportRequiredHiddenAccessMixtureRoot
import LG21TestOptionalPolicies.ReportRequiredLocalGaussianCandidate
import LG21TestOptionalPolicies.HiddenAccessTheorem31SourceTimedCandidateEntry
import LG21TestOptionalPolicies.SelectedObservationConditionalInvariance

/-!
# Local report-required hidden-access tail entry

This file packages the report-required candidate used only on a positive
public-base region with no current takers.  The candidate keeps the incumbent
actions outside that region.  On the region it takes on a literal latent
upper tail and reports every realized score.  Its displayed values are the
literal selected reporter posterior and the raw `X = 0` mixture value.

The local PBO proofs below are deliberately kept separate from the action
patch: conditioning on a public base region is harmless only after the actual
candidate action law has been formed.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open EconCSLib MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology
open Probability

/-- Patch a report-required latent-tail candidate into a public base region.
Outside that region it keeps the incumbent pre-score action exactly. -/
noncomputable def lg21HiddenAccessLocalTailTake
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ) :
    ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool := by
  classical
  exact fun latentSkill publicBase =>
    if publicBase ∈ region then decide (threshold publicBase ≤ latentSkill)
    else E.takeDecision latentSkill publicBase

/-- Patch the report-required action into the same public base region.
Every candidate tester reports there; outside it the incumbent report action
is retained exactly. -/
noncomputable def lg21HiddenAccessLocalTailReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ)) :
    (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool := by
  classical
  exact fun publicBase _observedScore =>
    if publicBase ∈ region then true else E.reportDecision publicBase _observedScore

/-- The localized candidate uses globally defined literal tail values, while
only its actions are patched on the changed region.  Local PBO claims below
are still made solely on the positive local action laws. -/
noncomputable def lg21HiddenAccessLocalTailCandidate
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (baseMean threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance) (hnoiseVariance : 0 < noiseVariance)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) :
    LG21OptionalCandidateBranchData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ where
  testLaw := fun latentSkill _publicBase =>
    gaussianReal latentSkill noiseVariance.toNNReal
  testLaw_isProbability := by
    intro latentSkill publicBase
    infer_instance
  reportDecision := lg21HiddenAccessLocalTailReport E region
  reportedValue := fun publicBase observedScore =>
    lg21SelectedGaussianUpperTailReporterPBO
      (baseMean publicBase) baseVariance noiseVariance
      (threshold publicBase) observedScore
  noReportValue := fun publicBase =>
    lg21HiddenAccessTailCandidateNoReportValue
      (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
      noAccessMass accessMass hnoAccessFinite haccessFinite threshold publicBase
  continuationValue_integrable := by
    intro latentSkill publicBase
    by_cases hreport : lg21HiddenAccessLocalTailReport E region publicBase = true
    · simp only [hreport, ↓reduceIte]
      exact lg21SelectedGaussianUpperTailReporterPBO_integrable
        (baseMean publicBase) baseVariance noiseVariance
        (threshold publicBase) latentSkill hbaseVariance hnoiseVariance
    · simp [hreport]

theorem lg21HiddenAccessLocalTailTake_eq_candidateTail_on_region
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    {publicBase : LG21NonTestFeature Feature testFeature -> ℝ}
    (hregion : publicBase ∈ region) (latentSkill : ℝ) :
    lg21HiddenAccessLocalTailTake E region threshold latentSkill publicBase = true ↔
      threshold publicBase ≤ latentSkill := by
  simp [lg21HiddenAccessLocalTailTake, hregion]

theorem lg21HiddenAccessLocalTailTake_eq_incumbent_outside_region
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    {publicBase : LG21NonTestFeature Feature testFeature -> ℝ}
    (hregion : publicBase ∉ region) (latentSkill : ℝ) :
    lg21HiddenAccessLocalTailTake E region threshold latentSkill publicBase =
      E.takeDecision latentSkill publicBase := by
  simp [lg21HiddenAccessLocalTailTake, hregion]

theorem lg21HiddenAccessLocalTailReport_eq_true_on_region
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    {publicBase : LG21NonTestFeature Feature testFeature -> ℝ}
    (hregion : publicBase ∈ region) (observedScore : ℝ) :
    lg21HiddenAccessLocalTailReport E region publicBase observedScore = true := by
  simp [lg21HiddenAccessLocalTailReport, hregion]

theorem lg21HiddenAccessLocalTailReport_eq_incumbent_outside_region
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    {publicBase : LG21NonTestFeature Feature testFeature -> ℝ}
    (hregion : publicBase ∉ region) (observedScore : ℝ) :
    lg21HiddenAccessLocalTailReport E region publicBase observedScore =
      E.reportDecision publicBase observedScore := by
  simp [lg21HiddenAccessLocalTailReport, hregion]

theorem lg21HiddenAccessLocalTailCandidate_reportedValue_eq_selected_on_region
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (baseMean threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance) (hnoiseVariance : 0 < noiseVariance)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    {publicBase : LG21NonTestFeature Feature testFeature -> ℝ}
    (hregion : publicBase ∈ region) (observedScore : ℝ) :
    (lg21HiddenAccessLocalTailCandidate E region baseMean threshold hbaseMean
      baseVariance noiseVariance hbaseVariance hnoiseVariance
      noAccessMass accessMass hnoAccessFinite haccessFinite).reportedValue
        publicBase observedScore =
      lg21SelectedGaussianUpperTailReporterPBO
        (baseMean publicBase) baseVariance noiseVariance
        (threshold publicBase) observedScore := by
  simp [lg21HiddenAccessLocalTailCandidate, hregion]

theorem lg21HiddenAccessLocalTailCandidate_noReportValue_eq_raw_on_region
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (baseMean threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance) (hnoiseVariance : 0 < noiseVariance)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    {publicBase : LG21NonTestFeature Feature testFeature -> ℝ}
    (hregion : publicBase ∈ region) :
    (lg21HiddenAccessLocalTailCandidate E region baseMean threshold hbaseMean
      baseVariance noiseVariance hbaseVariance hnoiseVariance
      noAccessMass accessMass hnoAccessFinite haccessFinite).noReportValue
        publicBase =
      lg21HiddenAccessTailCandidateNoReportValue
        (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
        noAccessMass accessMass hnoAccessFinite haccessFinite threshold publicBase := by
  simp [lg21HiddenAccessLocalTailCandidate, hregion]

/-- The local pre-score patch is measurable whenever its tail threshold is
measurable.  This is needed before forming literal raw action events; it is
not inferred from the name of the candidate. -/
theorem lg21HiddenAccessLocalTailTake_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hthreshold : Measurable threshold) :
    Measurable (fun pair : ℝ × (LG21NonTestFeature Feature testFeature -> ℝ) =>
      lg21HiddenAccessLocalTailTake E region threshold pair.1 pair.2) := by
  classical
  have htail : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      decide (threshold pair.2 ≤ pair.1)) := by
    apply measurable_to_bool
    change MeasurableSet {pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) |
      decide (threshold pair.2 ≤ pair.1) = true}
    have hset : {pair : ℝ ×
        (LG21NonTestFeature Feature testFeature -> ℝ) |
        decide (threshold pair.2 ≤ pair.1) = true} =
        (fun pair : ℝ × (LG21NonTestFeature Feature testFeature -> ℝ) =>
          pair.1 - threshold pair.2) ⁻¹' Set.Ici 0 := by
      ext pair
      simp
    rw [hset]
    exact measurableSet_Ici.preimage
      (measurable_fst.sub (hthreshold.comp measurable_snd))
  unfold lg21HiddenAccessLocalTailTake
  apply Measurable.ite (hregion.preimage measurable_snd)
  · exact htail
  · exact E.takeDecision_measurable

/-- The local post-score patch is measurable.  In the changed region it is
constant `true`; outside that region it is literally the incumbent action. -/
theorem lg21HiddenAccessLocalTailReport_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region) :
    Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      lg21HiddenAccessLocalTailReport E region pair.1 pair.2) := by
  classical
  unfold lg21HiddenAccessLocalTailReport
  apply Measurable.ite (hregion.preimage measurable_fst)
  · exact measurable_const
  · exact E.reportDecision_measurable

/-- On the changed public-base region, the local action is exactly the
global literal latent-tail action used to calculate the candidate PBOs. -/
theorem lg21HiddenAccessLocalTailTake_eq_globalTail_on_region
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    {publicBase : LG21NonTestFeature Feature testFeature -> ℝ}
    (hregion : publicBase ∈ region) (latentSkill : ℝ) :
    lg21HiddenAccessLocalTailTake E region threshold latentSkill publicBase =
      lg21HiddenAccessConditionalMeanTailTake testFeature threshold
        latentSkill publicBase := by
  simp [lg21HiddenAccessLocalTailTake,
    lg21HiddenAccessConditionalMeanTailTake, hregion]

/-! ## Base-dependent selected latent tails -/

/-- The latent upper-tail action event on the full `(base, score, skill)`
Gaussian source carrier.  Unlike a score threshold, this event is selected
before the score is drawn. -/
def lg21ReportRequiredBaseDependentTailTakeEvent
    {Base : Type*} [MeasurableSpace Base]
    (threshold : Base -> ℝ) : Set (Base × (ℝ × ℝ)) :=
  {baseScoreSkill | threshold baseScoreSkill.1 ≤ baseScoreSkill.2.2}

theorem lg21ReportRequiredBaseDependentTailTakeEvent_measurable
    {Base : Type*} [MeasurableSpace Base]
    (threshold : Base -> ℝ) (hthreshold : Measurable threshold) :
    MeasurableSet (lg21ReportRequiredBaseDependentTailTakeEvent threshold) := by
  exact measurableSet_le (hthreshold.comp measurable_fst)
    (measurable_snd.comp measurable_snd)

/-- The same action selection after exposing only `(base, score)` and keeping
skill as the latent coordinate for a regular conditional distribution. -/
def lg21ReportRequiredBaseDependentTailObservationEvent
    {Base : Type*} [MeasurableSpace Base]
    (threshold : Base -> ℝ) : Set ((Base × ℝ) × ℝ) :=
  {observationSkill | threshold observationSkill.1.1 ≤ observationSkill.2}

theorem lg21ReportRequiredBaseDependentTailObservationEvent_measurable
    {Base : Type*} [MeasurableSpace Base]
    (threshold : Base -> ℝ) (hthreshold : Measurable threshold) :
    MeasurableSet (lg21ReportRequiredBaseDependentTailObservationEvent threshold) := by
  exact measurableSet_le
    (hthreshold.comp (measurable_fst.comp measurable_fst)) measurable_snd

theorem lg21ReportRequiredBaseDependentTailTakeEvent_selectedFiber
    {Base : Type*} [MeasurableSpace Base]
    (threshold : Base -> ℝ) (publicBase : Base) :
    selectedFiber (lg21ReportRequiredBaseDependentTailTakeEvent threshold)
      publicBase = Set.univ ×ˢ Set.Ici (threshold publicBase) := by
  ext scoreSkill
  simp [selectedFiber, lg21ReportRequiredBaseDependentTailTakeEvent]

theorem lg21ReportRequiredBaseDependentTailObservationEvent_selectedFiber
    {Base : Type*} [MeasurableSpace Base]
    (threshold : Base -> ℝ) (publicObservation : Base × ℝ) :
    selectedFiber (lg21ReportRequiredBaseDependentTailObservationEvent threshold)
      publicObservation = Set.Ici (threshold publicObservation.1) := by
  ext latentSkill
  simp [selectedFiber, lg21ReportRequiredBaseDependentTailObservationEvent]

/-- The selected latent conditional kernel induced by a base-dependent
candidate tail.  Its input is the school's observable `(base, score)` pair. -/
noncomputable def lg21ReportRequiredBaseDependentTailSelectedTakeKernel
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ) (threshold : Base -> ℝ) :
    Kernel (Base × ℝ) ℝ := by
  letI : IsMarkovKernel
      (gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean priorVariance noiseVariance) :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  exact selectedNormalizedKernel
    (gaussianSignalPosteriorBaseKernel
      baseMean hbaseMean priorVariance noiseVariance)
    (lg21ReportRequiredBaseDependentTailObservationEvent threshold)

theorem lg21ReportRequiredBaseDependentTailSelectedTakeKernel_apply
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ) (threshold : Base -> ℝ)
    (hthreshold : Measurable threshold)
    (publicBase : Base) (observedScore : ℝ) :
    lg21ReportRequiredBaseDependentTailSelectedTakeKernel
      baseMean hbaseMean priorVariance noiseVariance threshold
        (publicBase, observedScore) =
      lg21NormalizedRestriction
        (gaussianSignalPosteriorKernel
          (baseMean publicBase) priorVariance noiseVariance observedScore)
        (Set.Ici (threshold publicBase)) := by
  let posteriorKernel := gaussianSignalPosteriorBaseKernel
    baseMean hbaseMean priorVariance noiseVariance
  let event := lg21ReportRequiredBaseDependentTailObservationEvent threshold
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  change selectedNormalizedKernel posteriorKernel event
      (publicBase, observedScore) = _
  rw [selectedNormalizedKernel_apply
    (lg21ReportRequiredBaseDependentTailObservationEvent_measurable
      threshold hthreshold)]
  rw [gaussianSignalPosteriorBaseKernel_apply,
    gaussianSignalPosteriorKernel_apply]
  congr 1
  ext latentSkill
  simp [event, lg21ReportRequiredBaseDependentTailObservationEvent,
    selectedFiber]

private theorem lg21ReportRequiredBaseDependentTail_selectedTake_fibre_positive
    {Base : Type*} [MeasurableSpace Base]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (threshold : Base -> ℝ)
    (publicObservation : Base × ℝ) :
    selectionMass
      (gaussianSignalPosteriorBaseKernel
        baseMean hbaseMean priorVariance noiseVariance)
      (lg21ReportRequiredBaseDependentTailObservationEvent threshold)
      publicObservation ≠ 0 := by
  unfold selectionMass
  rw [gaussianSignalPosteriorBaseKernel_apply]
  have hpriorVarianceNN : priorVariance.toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr hpriorVariance)
  have htail : 0 < gaussianReal (baseMean publicObservation.1)
      priorVariance.toNNReal (Set.Ioi (threshold publicObservation.1)) :=
    lg21_gaussianReal_Ioi_pos
      (baseMean publicObservation.1) (threshold publicObservation.1)
      hpriorVarianceNN
  have hselected : 0 < gaussianSignalPosteriorKernel
      (baseMean publicObservation.1) priorVariance noiseVariance publicObservation.2
      (Set.Ici (threshold publicObservation.1)) :=
    lt_of_lt_of_le
      (lg21_gaussianSignalPosterior_selected_pos
        (baseMean publicObservation.1) priorVariance noiseVariance
        (Set.Ioi (threshold publicObservation.1))
        hpriorVariance hnoiseVariance htail publicObservation.2)
      (measure_mono Set.Ioi_subset_Ici_self)
  have hfibre : selectedFiber
      (lg21ReportRequiredBaseDependentTailObservationEvent threshold)
      publicObservation = Set.Ici (threshold publicObservation.1) := by
    exact lg21ReportRequiredBaseDependentTailObservationEvent_selectedFiber
      threshold publicObservation
  have hkernelEq : gaussianReal
      (EconCSLib.Probability.gaussianSignalWeight priorVariance noiseVariance *
          publicObservation.2 +
        EconCSLib.Probability.gaussianSignalPriorWeight priorVariance noiseVariance *
          baseMean publicObservation.1)
      (EconCSLib.Probability.gaussianSignalPosteriorVariance
        priorVariance noiseVariance)
      (selectedFiber
        (lg21ReportRequiredBaseDependentTailObservationEvent threshold)
        publicObservation) =
      gaussianSignalPosteriorKernel
        (baseMean publicObservation.1) priorVariance noiseVariance publicObservation.2
        (Set.Ici (threshold publicObservation.1)) := by
    rw [gaussianSignalPosteriorKernel_apply]
    rw [hfibre]
  rw [hkernelEq]
  exact ne_of_gt hselected

/-- Every measurable base-dependent latent upper tail has positive mass under
the nondegenerate Gaussian score/skill source. -/
theorem lg21ReportRequiredBaseDependentTail_take_positive
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (threshold : Base -> ℝ) (hthreshold : Measurable threshold) :
    0 < (baseLaw ⊗ₘ
      gaussianSignalJointKernel baseMean hbaseMean priorVariance noiseVariance)
        (lg21ReportRequiredBaseDependentTailTakeEvent threshold) := by
  let rawKernel := gaussianSignalJointKernel
    baseMean hbaseMean priorVariance noiseVariance
  let event := lg21ReportRequiredBaseDependentTailTakeEvent threshold
  letI : IsMarkovKernel rawKernel :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  have hevent : MeasurableSet event := by
    simpa [event] using
      (lg21ReportRequiredBaseDependentTailTakeEvent_measurable
        threshold hthreshold)
  have hfibre : ∀ publicBase,
      0 < rawKernel publicBase (selectedFiber event publicBase) := by
    intro publicBase
    have hpriorVarianceNN : priorVariance.toNNReal ≠ 0 :=
      ne_of_gt (Real.toNNReal_pos.mpr hpriorVariance)
    have hupper : 0 < gaussianReal (baseMean publicBase)
        priorVariance.toNNReal (Set.Ici (threshold publicBase)) := by
      exact lt_of_lt_of_le
        (lg21_gaussianReal_Ioi_pos
          (baseMean publicBase) (threshold publicBase) hpriorVarianceNN)
        (measure_mono Set.Ioi_subset_Ici_self)
    calc
      0 < gaussianReal (baseMean publicBase)
          priorVariance.toNNReal (Set.Ici (threshold publicBase)) := hupper
      _ = (rawKernel publicBase).map Prod.snd
          (Set.Ici (threshold publicBase)) := by
        rw [lg21_gaussianSignalJointKernel_skill_marginal
          baseMean hbaseMean priorVariance noiseVariance publicBase]
      _ = rawKernel publicBase
          (selectedFiber event publicBase) := by
        rw [Measure.map_apply measurable_snd measurableSet_Ici]
        rw [lg21ReportRequiredBaseDependentTailTakeEvent_selectedFiber]
        congr 1
        ext scoreSkill
        simp
  have hmassMeasurable : Measurable
      (fun publicBase => rawKernel publicBase
        (selectedFiber event publicBase)) := by
    exact Kernel.measurable_kernel_prodMk_left hevent
  change 0 < (baseLaw ⊗ₘ rawKernel) event
  rw [Measure.compProd_apply hevent]
  apply (lintegral_pos_iff_support hmassMeasurable).2
  have hsupp : Function.support
      (fun publicBase => rawKernel publicBase
        (selectedFiber event publicBase)) = Set.univ := by
    ext publicBase
    simp [Function.mem_support, ne_of_gt (hfibre publicBase)]
  rw [hsupp, IsProbabilityMeasure.measure_univ]

/-- Conditioning a Gaussian score/skill source on a base-dependent latent
tail gives the selected posterior kernel at the actual observable
`(base, score)` record.  In particular, the selection event may depend on
the unobserved skill, but the posterior never conditions on a latent band as
if it had been publicly observed. -/
theorem lg21ReportRequiredBaseDependentTail_selectedTake_condDistrib_ae
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (priorVariance noiseVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (threshold : Base -> ℝ) (hthreshold : Measurable threshold) :
    letI : IsMarkovKernel (gaussianSignalJointKernel
      baseMean hbaseMean priorVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean priorVariance noiseVariance
    let selectedLaw := lg21NormalizedRestriction
      (baseLaw ⊗ₘ gaussianSignalJointKernel
        baseMean hbaseMean priorVariance noiseVariance)
      (lg21ReportRequiredBaseDependentTailTakeEvent threshold)
    letI : IsProbabilityMeasure selectedLaw :=
      lg21NormalizedRestriction_isProbability _ _
        (ne_of_gt
          (lg21ReportRequiredBaseDependentTail_take_positive
            baseLaw baseMean hbaseMean priorVariance noiseVariance
            hpriorVariance hnoiseVariance threshold hthreshold))
        (measure_ne_top _ _)
    letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
    condDistrib
      (fun scoreSkill : Base × (ℝ × ℝ) => scoreSkill.2.2)
      (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1))
      selectedLaw =ᵐ[selectedLaw.map
        (fun scoreSkill : Base × (ℝ × ℝ) => (scoreSkill.1, scoreSkill.2.1))]
      lg21ReportRequiredBaseDependentTailSelectedTakeKernel
        baseMean hbaseMean priorVariance noiseVariance threshold := by
  intro selectedLaw
  let rawLaw := baseLaw ⊗ₘ gaussianSignalJointKernel
    baseMean hbaseMean priorVariance noiseVariance
  let scoreKernel := gaussianLocationKernel baseMean hbaseMean
    (priorVariance + noiseVariance).toNNReal
  let posteriorKernel := gaussianSignalPosteriorBaseKernel
    baseMean hbaseMean priorVariance noiseVariance
  let observedLaw := baseLaw ⊗ₘ scoreKernel
  let selectedEvent := lg21ReportRequiredBaseDependentTailTakeEvent threshold
  let observedEvent := lg21ReportRequiredBaseDependentTailObservationEvent threshold
  let association : Base × (ℝ × ℝ) → (Base × ℝ) × ℝ :=
    fun scoreSkill => ((scoreSkill.1, scoreSkill.2.1), scoreSkill.2.2)
  let observation : Base × (ℝ × ℝ) → Base × ℝ :=
    fun scoreSkill => (scoreSkill.1, scoreSkill.2.1)
  let latent : Base × (ℝ × ℝ) → ℝ := fun scoreSkill => scoreSkill.2.2
  letI : IsMarkovKernel (gaussianSignalJointKernel
      baseMean hbaseMean priorVariance noiseVariance) :=
    gaussianSignalJointKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  letI : IsMarkovKernel scoreKernel :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean
      (priorVariance + noiseVariance).toNNReal
  letI : IsMarkovKernel posteriorKernel :=
    gaussianSignalPosteriorBaseKernel_isMarkov
      baseMean hbaseMean priorVariance noiseVariance
  letI : IsProbabilityMeasure observedLaw := by
    dsimp [observedLaw]
    infer_instance
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability rawLaw selectedEvent
      (ne_of_gt
        (lg21ReportRequiredBaseDependentTail_take_positive
          baseLaw baseMean hbaseMean priorVariance noiseVariance
          hpriorVariance hnoiseVariance threshold hthreshold))
      (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  have hselectedEvent : MeasurableSet selectedEvent :=
    lg21ReportRequiredBaseDependentTailTakeEvent_measurable
      threshold hthreshold
  have hobservedEvent : MeasurableSet observedEvent :=
    lg21ReportRequiredBaseDependentTailObservationEvent_measurable
      threshold hthreshold
  have hassociation : Measurable association := by
    dsimp [association]
    fun_prop
  have hobservation : Measurable observation := by
    dsimp [observation]
    fun_prop
  have hlatent : Measurable latent := by
    dsimp [latent]
    fun_prop
  have hselectionPositive : ∀ publicObservation,
      selectionMass posteriorKernel observedEvent publicObservation ≠ 0 := by
    intro publicObservation
    simpa [posteriorKernel, observedEvent] using
      (lg21ReportRequiredBaseDependentTail_selectedTake_fibre_positive
        baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance threshold publicObservation)
  letI : IsMarkovKernel
      (selectedNormalizedKernel posteriorKernel observedEvent) :=
    selectedNormalizedKernel_isMarkov hobservedEvent hselectionPositive
  have hselectedPreimage :
      selectedEvent = association ⁻¹' observedEvent := by
    ext scoreSkill
    simp [selectedEvent, association, observedEvent,
      lg21ReportRequiredBaseDependentTailTakeEvent,
      lg21ReportRequiredBaseDependentTailObservationEvent]
  have hrawAssoc : rawLaw.map association = observedLaw ⊗ₘ posteriorKernel := by
    simpa [rawLaw, association, observedLaw, posteriorKernel,
      gaussianSignalBaseScoreLatentLaw] using
      (gaussianSignalBaseScoreLatentLaw_factorization
        baseLaw baseMean hbaseMean priorVariance noiseVariance
        hpriorVariance hnoiseVariance)
  have hselectedAssoc :
      selectedLaw.map association =
        lg21NormalizedRestriction (rawLaw.map association) observedEvent := by
    rw [show selectedLaw = lg21NormalizedRestriction rawLaw selectedEvent by rfl,
      hselectedPreimage]
    exact lg21_normalizedRestriction_map_preimage
      rawLaw association hassociation observedEvent hobservedEvent
  have hselectedFactor :
      selectedLaw.map association =
        normalizedSelectedBase observedLaw posteriorKernel observedEvent ⊗ₘ
          selectedNormalizedKernel posteriorKernel observedEvent := by
    calc
      selectedLaw.map association =
          lg21NormalizedRestriction (rawLaw.map association) observedEvent := hselectedAssoc
      _ = lg21NormalizedRestriction (observedLaw ⊗ₘ posteriorKernel)
            observedEvent := by rw [hrawAssoc]
      _ = normalizedSelectedBase observedLaw posteriorKernel observedEvent ⊗ₘ
          selectedNormalizedKernel posteriorKernel observedEvent :=
        normalizedRestriction_compProd_selectedNormalizedKernel
          (μ := observedLaw) (κ := posteriorKernel)
          hobservedEvent hselectionPositive
  letI : SFinite (normalizedSelectedBase observedLaw posteriorKernel observedEvent) := by
    unfold normalizedSelectedBase selectedBase
    infer_instance
  have hselectedObservation :
      selectedLaw.map observation =
        normalizedSelectedBase observedLaw posteriorKernel observedEvent := by
    calc
      selectedLaw.map observation = (selectedLaw.map association).map Prod.fst := by
        rw [Measure.map_map measurable_fst hassociation]
        rfl
      _ = (normalizedSelectedBase observedLaw posteriorKernel observedEvent ⊗ₘ
          selectedNormalizedKernel posteriorKernel observedEvent).map Prod.fst := by
        rw [hselectedFactor]
      _ = normalizedSelectedBase observedLaw posteriorKernel observedEvent :=
        Measure.fst_compProd _ _
  have hselectedJoint :
      selectedLaw.map (fun scoreSkill => (observation scoreSkill, latent scoreSkill)) =
        selectedLaw.map observation ⊗ₘ
          selectedNormalizedKernel posteriorKernel observedEvent := by
    calc
      selectedLaw.map (fun scoreSkill =>
          (observation scoreSkill, latent scoreSkill)) =
          selectedLaw.map association := by rfl
      _ = normalizedSelectedBase observedLaw posteriorKernel observedEvent ⊗ₘ
          selectedNormalizedKernel posteriorKernel observedEvent := hselectedFactor
      _ = selectedLaw.map observation ⊗ₘ
          selectedNormalizedKernel posteriorKernel observedEvent := by
        rw [hselectedObservation]
  change condDistrib latent observation selectedLaw =ᵐ[selectedLaw.map observation]
    lg21ReportRequiredBaseDependentTailSelectedTakeKernel
      baseMean hbaseMean priorVariance noiseVariance threshold
  simpa [posteriorKernel, observedEvent,
    lg21ReportRequiredBaseDependentTailSelectedTakeKernel] using
    (condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      hobservation hlatent hselectedJoint)

/-! ## Literal hidden-access report branch -/

/-- The raw report event of the source-timed latent-tail candidate is exactly
positive access together with its latent-tail selection.  The public record
on the right intentionally does not contain the access bit. -/
theorem lg21HiddenAccessConditionalMeanTail_rawCandidateReportEvent_eq_access_inter_preimage
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ) :
    lg21HiddenAccessRawCandidateReportEvent testFeature
      (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
      (fun _ _ => true) =
      {student : Bool × (ℝ × (Feature -> ℝ)) | student.1 = true} ∩
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) ⁻¹'
          (lg21ReportRequiredBaseDependentTailTakeEvent threshold) := by
  ext student
  rcases student with ⟨access, primitive⟩
  rcases primitive with ⟨latentSkill, noise⟩
  cases access <;>
    simp [lg21HiddenAccessRawCandidateReportEvent,
      lg21HiddenAccessOptionalObservedAction,
      lg21HiddenAccessConditionalMeanTailTake,
      lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport,
      lg21HiddenAccessBaseScoreSkillObservation,
      lg21ReportRequiredBaseDependentTailTakeEvent]

/-- After normalizing the literal raw candidate report event, forgetting the
hidden access coordinate gives precisely the Gaussian source law selected by
the candidate's latent upper tail. -/
theorem lg21HiddenAccessConditionalMeanTail_rawCandidateReportBaseScoreSkillLaw_eq_normalizedTail
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hthreshold : Measurable threshold)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance) :
    letI : IsMarkovKernel
        (gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance) :=
      gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance
    (lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
        (fun _ _ => true))).map
      (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
      lg21NormalizedRestriction
        (baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance noiseVariance)
        (lg21ReportRequiredBaseDependentTailTakeEvent threshold) := by
  intro
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  let observation := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let tailEvent := lg21ReportRequiredBaseDependentTailTakeEvent threshold
  let reportEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
    (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
    (fun _ _ => true)
  let joint := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure accessLaw := by
    simpa [accessLaw] using
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  have haccessEvent : MeasurableSet accessEvent := by
    change MeasurableSet {student : Bool × (ℝ × (Feature -> ℝ)) |
      student.1 = true}
    exact (measurableSet_singleton true).preimage measurable_fst
  have htailEvent : MeasurableSet tailEvent := by
    simpa [tailEvent] using
      (lg21ReportRequiredBaseDependentTailTakeEvent_measurable
        threshold hthreshold)
  have hobservation : Measurable observation := by
    simpa [observation] using
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature)
  have haccessLaw : accessLaw = lg21NormalizedRestriction rawLaw accessEvent := by
    rfl
  have hreportEvent : reportEvent =
      accessEvent ∩ observation ⁻¹' tailEvent := by
    simpa [reportEvent, accessEvent, observation, tailEvent] using
      (lg21HiddenAccessConditionalMeanTail_rawCandidateReportEvent_eq_access_inter_preimage
        testFeature threshold)
  have hnormalizedRaw :
      lg21NormalizedRestriction rawLaw reportEvent =
        lg21NormalizedRestriction accessLaw (observation ⁻¹' tailEvent) := by
    calc
      lg21NormalizedRestriction rawLaw reportEvent =
          lg21NormalizedRestriction rawLaw
            (accessEvent ∩ observation ⁻¹' tailEvent) := by rw [hreportEvent]
      _ = lg21NormalizedRestriction
          (lg21NormalizedRestriction rawLaw accessEvent)
          (observation ⁻¹' tailEvent) := by
          symm
          exact lg21_normalizedRestriction_normalizedRestriction_eq_inter
            rawLaw accessEvent (observation ⁻¹' tailEvent) haccessEvent
            (htailEvent.preimage hobservation)
      _ = lg21NormalizedRestriction accessLaw
          (observation ⁻¹' tailEvent) := by rw [haccessLaw]
  have haccessScoreSkill : accessLaw.map observation = baseLaw ⊗ₘ joint := by
    calc
      accessLaw.map observation = rawLaw.map observation := by
        symm
        simpa [rawLaw, accessLaw, observation] using
          (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
            M haccess testFeature)
      _ = baseLaw ⊗ₘ joint := by
        simpa [rawLaw, observation, joint] using hsourceFactor
  change (lg21NormalizedRestriction rawLaw reportEvent).map observation =
    lg21NormalizedRestriction (baseLaw ⊗ₘ joint) tailEvent
  rw [hnormalizedRaw]
  calc
    (lg21NormalizedRestriction accessLaw
      (observation ⁻¹' tailEvent)).map observation =
        lg21NormalizedRestriction (accessLaw.map observation) tailEvent := by
          exact lg21_normalizedRestriction_map_preimage accessLaw
            observation hobservation tailEvent htailEvent
    _ = lg21NormalizedRestriction (baseLaw ⊗ₘ joint) tailEvent := by
          rw [haccessScoreSkill]

/-- The literal raw report branch of a base-dependent latent-tail candidate
has positive mass whenever access has positive mass.  Positivity is proved
from the actual access-and-tail intersection, before normalization. -/
theorem lg21HiddenAccessConditionalMeanTail_rawCandidateReport_positive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hthreshold : Measurable threshold)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance) :
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
        (fun _ _ => true)) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  let observation := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let tailEvent := lg21ReportRequiredBaseDependentTailTakeEvent threshold
  let reportEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
    (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
    (fun _ _ => true)
  let joint := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure accessLaw := by
    simpa [accessLaw] using
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  have haccessEvent : MeasurableSet accessEvent := by
    change MeasurableSet {student : Bool × (ℝ × (Feature -> ℝ)) |
      student.1 = true}
    exact (measurableSet_singleton true).preimage measurable_fst
  have htailEvent : MeasurableSet tailEvent := by
    simpa [tailEvent] using
      (lg21ReportRequiredBaseDependentTailTakeEvent_measurable
        threshold hthreshold)
  have hobservation : Measurable observation := by
    simpa [observation] using
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature)
  have haccessScoreSkill : accessLaw.map observation = baseLaw ⊗ₘ joint := by
    calc
      accessLaw.map observation = rawLaw.map observation := by
        symm
        simpa [rawLaw, accessLaw, observation] using
          (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
            M haccess testFeature)
      _ = baseLaw ⊗ₘ joint := by
        simpa [rawLaw, observation, joint] using hsourceFactor
  have htailPositive : 0 < (baseLaw ⊗ₘ joint) tailEvent := by
    simpa [joint, tailEvent] using
      (lg21ReportRequiredBaseDependentTail_take_positive
        baseLaw baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance threshold hthreshold)
  have haccessTailPositive : 0 < accessLaw (observation ⁻¹' tailEvent) := by
    rw [← Measure.map_apply hobservation htailEvent, haccessScoreSkill]
    exact htailPositive
  have hintersectionPositive : 0 < rawLaw
      (accessEvent ∩ observation ⁻¹' tailEvent) := by
    change 0 < lg21NormalizedRestriction rawLaw accessEvent
      (observation ⁻¹' tailEvent) at haccessTailPositive
    rw [lg21NormalizedRestriction_apply rawLaw
      (htailEvent.preimage hobservation)] at haccessTailPositive
    have hraw : 0 < rawLaw
        ((observation ⁻¹' tailEvent) ∩ accessEvent) :=
      (ENNReal.mul_pos_iff.mp haccessTailPositive).2
    simpa [inter_comm] using hraw
  have hreportEvent : reportEvent =
      accessEvent ∩ observation ⁻¹' tailEvent := by
    simpa [reportEvent, accessEvent, observation, tailEvent] using
      (lg21HiddenAccessConditionalMeanTail_rawCandidateReportEvent_eq_access_inter_preimage
        testFeature threshold)
  simpa [rawLaw, reportEvent] using (by
    rw [hreportEvent]
    exact hintersectionPositive)

/-- The literal selected reporter value is a PBO on the candidate's actual
positive raw report action law.  This theorem is the source bridge for the
report branch: it does not use an arbitrary value from the predecessor's
empty report branch. -/
theorem lg21HiddenAccessConditionalMeanTail_reportedValue_eq_condDistribMean_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hthreshold : Measurable threshold)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance) :
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let reportEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
      (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
      (fun _ _ => true)
    let actionLaw := (lg21NormalizedRestriction rawLaw reportEvent).map
      (lg21HiddenAccessBaseScoreSkillObservation testFeature)
    letI : IsProbabilityMeasure rawLaw :=
      lg21ContinuousGaussianPopulationLaw_isProbability M
    letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
    letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw reportEvent) :=
      lg21NormalizedRestriction_isProbability rawLaw reportEvent
        (ne_of_gt
          (lg21HiddenAccessConditionalMeanTail_rawCandidateReport_positive
            M haccess testFeature baseLaw baseMean hbaseMean
            baseVariance noiseVariance hbaseVariance hnoiseVariance
            threshold hthreshold hsourceFactor))
        (measure_ne_top _ _)
    letI : IsProbabilityMeasure actionLaw :=
      Measure.isProbabilityMeasure_map
        (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature).aemeasurable
    letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
    ∀ᵐ publicObservation ∂actionLaw.map
      (fun scoreSkill :
        (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
        (scoreSkill.1, scoreSkill.2.1)),
      lg21SelectedGaussianUpperTailReporterPBO
        (baseMean publicObservation.1) baseVariance noiseVariance
        (threshold publicObservation.1) publicObservation.2 =
        ∫ latentSkill, latentSkill ∂condDistrib
          (fun scoreSkill :
            (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
            scoreSkill.2.2)
          (fun scoreSkill :
            (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
            (scoreSkill.1, scoreSkill.2.1))
          actionLaw publicObservation := by
  intro rawLaw reportEvent actionLaw
  let joint := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  let tailEvent := lg21ReportRequiredBaseDependentTailTakeEvent threshold
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hreportPositive : 0 < rawLaw reportEvent := by
    simpa [rawLaw, reportEvent] using
      (lg21HiddenAccessConditionalMeanTail_rawCandidateReport_positive
        M haccess testFeature baseLaw baseMean hbaseMean
        baseVariance noiseVariance hbaseVariance hnoiseVariance
        threshold hthreshold hsourceFactor)
  letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw reportEvent) :=
    lg21NormalizedRestriction_isProbability rawLaw reportEvent
      (ne_of_gt hreportPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure actionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
  let selectedLaw := lg21NormalizedRestriction
    (baseLaw ⊗ₘ joint) tailEvent
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability _ _
      (ne_of_gt
        (lg21ReportRequiredBaseDependentTail_take_positive
          baseLaw baseMean hbaseMean baseVariance noiseVariance
          hbaseVariance hnoiseVariance threshold hthreshold))
      (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  have hactionLaw : actionLaw = selectedLaw := by
    simpa [actionLaw, rawLaw, reportEvent, selectedLaw, tailEvent, joint] using
      (lg21HiddenAccessConditionalMeanTail_rawCandidateReportBaseScoreSkillLaw_eq_normalizedTail
        M haccess testFeature baseLaw baseMean hbaseMean
        baseVariance noiseVariance threshold hthreshold hsourceFactor)
  have hRCD := lg21ReportRequiredBaseDependentTail_selectedTake_condDistrib_ae
    baseLaw baseMean hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance threshold hthreshold
  have hRCDAction : condDistrib
      (fun scoreSkill :
        (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
        scoreSkill.2.2)
      (fun scoreSkill :
        (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
        (scoreSkill.1, scoreSkill.2.1))
      actionLaw =ᵐ[actionLaw.map
        (fun scoreSkill :
          (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
          (scoreSkill.1, scoreSkill.2.1))]
      lg21ReportRequiredBaseDependentTailSelectedTakeKernel
        baseMean hbaseMean baseVariance noiseVariance threshold := by
    simpa only [hactionLaw] using hRCD
  filter_upwards [hRCDAction] with publicObservation hkernel
  rw [← lg21_gaussianSignalPosterior_selectedUpperTailMean_eq_explicit
    (baseMean publicObservation.1) baseVariance noiseVariance
    publicObservation.2 (threshold publicObservation.1)
    hbaseVariance hnoiseVariance]
  rw [← lg21ReportRequiredBaseDependentTailSelectedTakeKernel_apply
    baseMean hbaseMean baseVariance noiseVariance threshold hthreshold
    publicObservation.1 publicObservation.2]
  rw [hkernel]

/-! ## Local action-law transport -/

/-- Inside the localized population, the patched raw report event is exactly
the global latent-tail report event.  The equality is deliberately after
intersection with the public base region, so it makes no assertion about
the incumbent's actions outside the deviation. -/
theorem lg21HiddenAccessBaseRegion_inter_localTailReportEvent_eq_globalTail
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ) :
    lg21HiddenAccessBaseRegionEvent testFeature region ∩
      lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessLocalTailTake E region threshold)
        (lg21HiddenAccessLocalTailReport E region) =
      lg21HiddenAccessBaseRegionEvent testFeature region ∩
        lg21HiddenAccessRawCandidateReportEvent testFeature
          (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
          (fun _ _ => true) := by
  ext student
  rcases student with ⟨access, primitive⟩
  rcases primitive with ⟨latentSkill, noise⟩
  by_cases hregion :
      lg21HiddenAccessStudentBase testFeature (latentSkill, noise) ∈ region
  · cases access <;>
      simp [lg21HiddenAccessBaseRegionEvent,
        lg21HiddenAccessRawCandidateReportEvent,
        lg21HiddenAccessOptionalObservedAction,
        lg21HiddenAccessLocalTailTake,
        lg21HiddenAccessLocalTailReport,
        lg21HiddenAccessConditionalMeanTailTake,
        lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport, hregion]
  · simp [lg21HiddenAccessBaseRegionEvent, hregion]

/-- The analogous event identity for the literal raw `X = 0` branch.  This
keeps the no-access component because it is an equality of raw action events. -/
theorem lg21HiddenAccessBaseRegion_inter_localTailNoReportEvent_eq_globalTail
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ) :
    lg21HiddenAccessBaseRegionEvent testFeature region ∩
      lg21HiddenAccessRawCandidateNoReportEvent testFeature
        (lg21HiddenAccessLocalTailTake E region threshold)
        (lg21HiddenAccessLocalTailReport E region) =
      lg21HiddenAccessBaseRegionEvent testFeature region ∩
        lg21HiddenAccessRawCandidateNoReportEvent testFeature
          (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
          (fun _ _ => true) := by
  ext student
  rcases student with ⟨access, primitive⟩
  rcases primitive with ⟨latentSkill, noise⟩
  by_cases hregion :
      lg21HiddenAccessStudentBase testFeature (latentSkill, noise) ∈ region
  · cases access <;>
      simp [lg21HiddenAccessBaseRegionEvent,
        lg21HiddenAccessRawCandidateNoReportEvent,
        lg21HiddenAccessOptionalObservedAction,
        lg21HiddenAccessLocalTailTake,
        lg21HiddenAccessLocalTailReport,
        lg21HiddenAccessConditionalMeanTailTake,
        lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport, hregion]
  · simp [lg21HiddenAccessBaseRegionEvent, hregion]

theorem lg21HiddenAccessRawCandidateReportEvent_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool)
    (hcandidateTake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) => candidateTake pair.1 pair.2))
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2)) :
    MeasurableSet (lg21HiddenAccessRawCandidateReportEvent testFeature
      candidateTake candidateReport) := by
  change MeasurableSet
    ((lg21HiddenAccessOptionalObservedAction testFeature
      candidateTake candidateReport) ⁻¹' ({true} : Set Bool))
  exact (measurableSet_singleton true).preimage
    (lg21HiddenAccessOptionalObservedAction_measurable testFeature
      candidateTake candidateReport hcandidateTake hcandidateReport)

theorem lg21HiddenAccessRawCandidateNoReportEvent_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (candidateReport : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool)
    (hcandidateTake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) => candidateTake pair.1 pair.2))
    (hcandidateReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      candidateReport pair.1 pair.2)) :
    MeasurableSet (lg21HiddenAccessRawCandidateNoReportEvent testFeature
      candidateTake candidateReport) := by
  change MeasurableSet
    ((lg21HiddenAccessOptionalObservedAction testFeature
      candidateTake candidateReport) ⁻¹' ({false} : Set Bool))
  exact (measurableSet_singleton false).preimage
    (lg21HiddenAccessOptionalObservedAction_measurable testFeature
      candidateTake candidateReport hcandidateTake hcandidateReport)

/-- The local report action law is the global literal tail report law
conditioned only on the retained public base. -/
theorem lg21HiddenAccessLocalTail_localReportActionLaw_eq_selectedGlobal
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hthreshold : Measurable threshold) :
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
    let localEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
      (lg21HiddenAccessLocalTailTake E region threshold)
      (lg21HiddenAccessLocalTailReport E region)
    let globalEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
      (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
      (fun _ _ => true)
    let globalActionLaw := (lg21NormalizedRestriction rawLaw globalEvent).map
      (lg21HiddenAccessBaseScoreSkillObservation testFeature)
    let localActionLaw := (lg21NormalizedRestriction localLaw localEvent).map
      (lg21HiddenAccessBaseScoreSkillObservation testFeature)
    localActionLaw =
      lg21NormalizedRestriction globalActionLaw (Prod.fst ⁻¹' region) := by
  intro rawLaw localLaw localEvent globalEvent globalActionLaw localActionLaw
  let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let record := lg21HiddenAccessBaseScoreSkillObservation testFeature
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hregionEvent : MeasurableSet regionEvent := by
    simpa [regionEvent] using
      (lg21HiddenAccessBaseRegionEvent_measurable testFeature region hregion)
  have hlocalTake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      lg21HiddenAccessLocalTailTake E region threshold pair.1 pair.2) :=
    lg21HiddenAccessLocalTailTake_measurable E region hregion threshold hthreshold
  have hlocalReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      lg21HiddenAccessLocalTailReport E region pair.1 pair.2) :=
    lg21HiddenAccessLocalTailReport_measurable E region hregion
  have hglobalTake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      lg21HiddenAccessConditionalMeanTailTake testFeature threshold pair.1 pair.2) :=
    lg21HiddenAccessConditionalMeanTailTake_measurable testFeature threshold hthreshold
  have hlocalEvent : MeasurableSet localEvent := by
    simpa [localEvent] using
      (lg21HiddenAccessRawCandidateReportEvent_measurable testFeature
        (lg21HiddenAccessLocalTailTake E region threshold)
        (lg21HiddenAccessLocalTailReport E region) hlocalTake hlocalReport)
  have hglobalEvent : MeasurableSet globalEvent := by
    simpa [globalEvent] using
      (lg21HiddenAccessRawCandidateReportEvent_measurable testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
        (fun _ _ => true) hglobalTake measurable_const)
  have hlocalActionLaw :
      lg21NormalizedRestriction localLaw localEvent =
        lg21NormalizedRestriction localLaw globalEvent := by
    change lg21NormalizedRestriction
        (lg21NormalizedRestriction rawLaw regionEvent) localEvent =
      lg21NormalizedRestriction
        (lg21NormalizedRestriction rawLaw regionEvent) globalEvent
    rw [lg21_normalizedRestriction_normalizedRestriction_eq_inter
      rawLaw regionEvent localEvent hregionEvent hlocalEvent,
      lg21_normalizedRestriction_normalizedRestriction_eq_inter
        rawLaw regionEvent globalEvent hregionEvent hglobalEvent,
      lg21HiddenAccessBaseRegion_inter_localTailReportEvent_eq_globalTail]
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hrecord : Measurable record := by
    simpa [record] using
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature)
  calc
    localActionLaw =
        (lg21NormalizedRestriction localLaw globalEvent).map record := by
      rw [hlocalActionLaw]
    _ = lg21NormalizedRestriction globalActionLaw (Prod.fst ⁻¹' region) := by
      simpa [localLaw, globalActionLaw, rawLaw, base, record] using
        (lg21_normalizedLocalBaseActionLaw_eq_normalizedGlobalActionLaw
          rawLaw base record Prod.fst hbase hrecord measurable_fst
          (fun student => rfl) region hregion globalEvent hglobalEvent)

/-- The local raw no-report action law is the global literal tail no-report
law conditioned only on the retained public base.  The global law on the
right continues to contain its no-access component. -/
theorem lg21HiddenAccessLocalTail_localNoReportActionLaw_eq_selectedGlobal
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hthreshold : Measurable threshold) :
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
    let localEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
      (lg21HiddenAccessLocalTailTake E region threshold)
      (lg21HiddenAccessLocalTailReport E region)
    let globalEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
      (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
      (fun _ _ => true)
    let globalActionLaw := (lg21NormalizedRestriction rawLaw globalEvent).map
      (lg21HiddenAccessBaseSkillObservation testFeature)
    let localActionLaw := (lg21NormalizedRestriction localLaw localEvent).map
      (lg21HiddenAccessBaseSkillObservation testFeature)
    localActionLaw =
      lg21NormalizedRestriction globalActionLaw (Prod.fst ⁻¹' region) := by
  intro rawLaw localLaw localEvent globalEvent globalActionLaw localActionLaw
  let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let record := lg21HiddenAccessBaseSkillObservation testFeature
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hregionEvent : MeasurableSet regionEvent := by
    simpa [regionEvent] using
      (lg21HiddenAccessBaseRegionEvent_measurable testFeature region hregion)
  have hlocalTake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      lg21HiddenAccessLocalTailTake E region threshold pair.1 pair.2) :=
    lg21HiddenAccessLocalTailTake_measurable E region hregion threshold hthreshold
  have hlocalReport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      lg21HiddenAccessLocalTailReport E region pair.1 pair.2) :=
    lg21HiddenAccessLocalTailReport_measurable E region hregion
  have hglobalTake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      lg21HiddenAccessConditionalMeanTailTake testFeature threshold pair.1 pair.2) :=
    lg21HiddenAccessConditionalMeanTailTake_measurable testFeature threshold hthreshold
  have hlocalEvent : MeasurableSet localEvent := by
    simpa [localEvent] using
      (lg21HiddenAccessRawCandidateNoReportEvent_measurable testFeature
        (lg21HiddenAccessLocalTailTake E region threshold)
        (lg21HiddenAccessLocalTailReport E region) hlocalTake hlocalReport)
  have hglobalEvent : MeasurableSet globalEvent := by
    simpa [globalEvent] using
      (lg21HiddenAccessRawCandidateNoReportEvent_measurable testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
        (fun _ _ => true) hglobalTake measurable_const)
  have hlocalActionLaw :
      lg21NormalizedRestriction localLaw localEvent =
        lg21NormalizedRestriction localLaw globalEvent := by
    change lg21NormalizedRestriction
        (lg21NormalizedRestriction rawLaw regionEvent) localEvent =
      lg21NormalizedRestriction
        (lg21NormalizedRestriction rawLaw regionEvent) globalEvent
    rw [lg21_normalizedRestriction_normalizedRestriction_eq_inter
      rawLaw regionEvent localEvent hregionEvent hlocalEvent,
      lg21_normalizedRestriction_normalizedRestriction_eq_inter
        rawLaw regionEvent globalEvent hregionEvent hglobalEvent,
      lg21HiddenAccessBaseRegion_inter_localTailNoReportEvent_eq_globalTail]
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hrecord : Measurable record := by
    simpa [record] using
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature)
  calc
    localActionLaw =
        (lg21NormalizedRestriction localLaw globalEvent).map record := by
      rw [hlocalActionLaw]
    _ = lg21NormalizedRestriction globalActionLaw (Prod.fst ⁻¹' region) := by
      simpa [localLaw, globalActionLaw, rawLaw, base, record] using
        (lg21_normalizedLocalBaseActionLaw_eq_normalizedGlobalActionLaw
          rawLaw base record Prod.fst hbase hrecord measurable_fst
          (fun student => rfl) region hregion globalEvent hglobalEvent)

/-- Localized report-branch PBO transport.  The only extra positivity input
is the actual selected global action law restricted to the public base
region; later source lemmas discharge it from Gaussian full support. -/
theorem lg21HiddenAccessLocalTail_reportPBO_of_global
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (haccess : 0 < M.accessLaw {true})
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hthreshold : Measurable threshold)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance)
    (hlocalPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessLocalTailTake E region threshold)
        (lg21HiddenAccessLocalTailReport E region)))
    (hglobalRegionPositive : 0 <
      ((lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
        (lg21HiddenAccessRawCandidateReportEvent testFeature
          (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
          (fun _ _ => true))).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature))
          (Prod.fst ⁻¹' region)) :
    LG21HiddenAccessSourceTimedCandidateReportPBOOn M testFeature region
      hregionPositive
      (lg21HiddenAccessLocalTailTake E region threshold)
      (lg21HiddenAccessLocalTailReport E region)
      (lg21HiddenAccessLocalTailCandidate E region baseMean threshold hbaseMean
        baseVariance noiseVariance hbaseVariance hnoiseVariance
        noAccessMass accessMass hnoAccessFinite haccessFinite)
      hlocalPositive := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
  let localEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
    (lg21HiddenAccessLocalTailTake E region threshold)
    (lg21HiddenAccessLocalTailReport E region)
  let globalEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
    (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
    (fun _ _ => true)
  let record := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let observation :
      (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun scoreSkill => (scoreSkill.1, scoreSkill.2.1)
  let latent :
      (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) -> ℝ :=
    fun scoreSkill => scoreSkill.2.2
  let candidate := lg21HiddenAccessLocalTailCandidate E region
    baseMean threshold hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance noAccessMass accessMass
    hnoAccessFinite haccessFinite
  let globalActionLaw := (lg21NormalizedRestriction rawLaw globalEvent).map record
  let localActionLaw := (lg21NormalizedRestriction localLaw localEvent).map record
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure localLaw :=
    lg21NormalizedRestriction_isProbability rawLaw
      (lg21HiddenAccessBaseRegionEvent testFeature region)
      (ne_of_gt hregionPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure (lg21NormalizedRestriction localLaw localEvent) :=
    lg21NormalizedRestriction_isProbability localLaw localEvent
      (ne_of_gt hlocalPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure localActionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure localActionLaw := ⟨by simp⟩
  have hglobalPositive : 0 < rawLaw globalEvent := by
    simpa [rawLaw, globalEvent] using
      (lg21HiddenAccessConditionalMeanTail_rawCandidateReport_positive
        M haccess testFeature baseLaw baseMean hbaseMean
        baseVariance noiseVariance hbaseVariance hnoiseVariance
        threshold hthreshold hsourceFactor)
  letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw globalEvent) :=
    lg21NormalizedRestriction_isProbability rawLaw globalEvent
      (ne_of_gt hglobalPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure globalActionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure globalActionLaw := ⟨by simp⟩
  have hrecord : Measurable record := by
    simpa [record] using
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature)
  have hobservation : Measurable observation := by
    dsimp [observation]
    fun_prop
  have hlatent : Measurable latent := by
    dsimp [latent]
    fun_prop
  have hlocalLaw : localActionLaw =
      lg21NormalizedRestriction globalActionLaw (Prod.fst ⁻¹' region) := by
    simpa [rawLaw, localLaw, localEvent, globalEvent, globalActionLaw,
      localActionLaw, record] using
      (lg21HiddenAccessLocalTail_localReportActionLaw_eq_selectedGlobal
        E region hregion threshold hthreshold)
  have hglobalPBO : ∀ᵐ publicObservation ∂globalActionLaw.map observation,
      lg21SelectedGaussianUpperTailReporterPBO
        (baseMean publicObservation.1) baseVariance noiseVariance
        (threshold publicObservation.1) publicObservation.2 =
        ∫ latentSkill, latentSkill ∂condDistrib latent observation
          globalActionLaw publicObservation := by
    simpa [rawLaw, globalEvent, globalActionLaw, record, observation, latent] using
      (lg21HiddenAccessConditionalMeanTail_reportedValue_eq_condDistribMean_ae
        M haccess testFeature baseLaw baseMean hbaseMean
        baseVariance noiseVariance hbaseVariance hnoiseVariance
        threshold hthreshold hsourceFactor)
  have hselectedPBO := lg21_selectedObservation_condDistribMean_eq_raw_ae
    globalActionLaw observation latent
    (fun publicObservation =>
      lg21SelectedGaussianUpperTailReporterPBO
        (baseMean publicObservation.1) baseVariance noiseVariance
        (threshold publicObservation.1) publicObservation.2)
    hobservation hlatent hglobalPBO (Prod.fst ⁻¹' region)
    (hregion.preimage measurable_fst) hglobalRegionPositive
  unfold LG21HiddenAccessSourceTimedCandidateReportPBOOn
  dsimp only
  change ∀ᵐ publicObservation ∂localActionLaw.map observation,
    candidate.reportedValue publicObservation.1 publicObservation.2 =
      ∫ latentSkill, latentSkill ∂condDistrib latent observation
        localActionLaw publicObservation
  rw [hlocalLaw]
  simpa [candidate, observation, latent] using hselectedPBO

/-- Localized no-report PBO transport for the literal raw hidden-access
mixture.  The supplied full-base factorization is the source identity that
keeps no-access students in the `X = 0` conditional law. -/
theorem lg21HiddenAccessLocalTail_noReportPBO_of_global
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (gap : ℝ)
    (hnoAccess : 0 < M.accessLaw {false})
    (haccess : 0 < M.accessLaw {true})
    (hfullBaseFactor :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
          baseVariance.toNNReal)
    (hlocalPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessRawCandidateNoReportEvent testFeature
        (lg21HiddenAccessLocalTailTake E region
          (fun publicBase => baseMean publicBase + gap))
        (lg21HiddenAccessLocalTailReport E region)))
    (hglobalRegionPositive : 0 <
      ((lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
        (lg21HiddenAccessRawCandidateNoReportEvent testFeature
          (lg21HiddenAccessConditionalMeanTailTake testFeature
            (fun publicBase => baseMean publicBase + gap))
          (fun _ _ => true))).map
        (lg21HiddenAccessBaseSkillObservation testFeature))
          (Prod.fst ⁻¹' region)) :
    LG21HiddenAccessSourceTimedCandidateNoReportPBOOn M testFeature region
      hregionPositive
      (lg21HiddenAccessLocalTailTake E region
        (fun publicBase => baseMean publicBase + gap))
      (lg21HiddenAccessLocalTailReport E region)
      (lg21HiddenAccessLocalTailCandidate E region baseMean
        (fun publicBase => baseMean publicBase + gap) hbaseMean
        baseVariance noiseVariance hbaseVariance hnoiseVariance
        (M.accessLaw {false}) (M.accessLaw {true})
        (measure_ne_top _ _) (measure_ne_top _ _))
      hlocalPositive := by
  let threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ :=
    fun publicBase => baseMean publicBase + gap
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
  let localEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    (lg21HiddenAccessLocalTailTake E region threshold)
    (lg21HiddenAccessLocalTailReport E region)
  let globalEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
    (fun _ _ => true)
  let record := lg21HiddenAccessBaseSkillObservation testFeature
  let candidate := lg21HiddenAccessLocalTailCandidate E region baseMean threshold
    hbaseMean baseVariance noiseVariance hbaseVariance hnoiseVariance
    (M.accessLaw {false}) (M.accessLaw {true})
    (measure_ne_top _ _) (measure_ne_top _ _)
  let globalActionLaw := (lg21NormalizedRestriction rawLaw globalEvent).map record
  let localActionLaw := (lg21NormalizedRestriction localLaw localEvent).map record
  letI : IsMarkovKernel
      (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal) :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance.toNNReal
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure localLaw :=
    lg21NormalizedRestriction_isProbability rawLaw
      (lg21HiddenAccessBaseRegionEvent testFeature region)
      (ne_of_gt hregionPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure (lg21NormalizedRestriction localLaw localEvent) :=
    lg21NormalizedRestriction_isProbability localLaw localEvent
      (ne_of_gt hlocalPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure localActionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure localActionLaw := ⟨by simp⟩
  have hglobalPositive : 0 < rawLaw globalEvent := by
    simpa [rawLaw, globalEvent, threshold] using
      (lg21HiddenAccessRawCandidate_noReport_positive_of_noAccess
        M testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
        (fun _ _ => true) hnoAccess)
  letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw globalEvent) :=
    lg21NormalizedRestriction_isProbability rawLaw globalEvent
      (ne_of_gt hglobalPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure globalActionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure globalActionLaw := ⟨by simp⟩
  have hrecord : Measurable record := by
    simpa [record] using
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature)
  have hlocalLaw : localActionLaw =
      lg21NormalizedRestriction globalActionLaw (Prod.fst ⁻¹' region) := by
    simpa [rawLaw, localLaw, localEvent, globalEvent, globalActionLaw,
      localActionLaw, record, threshold] using
      (lg21HiddenAccessLocalTail_localNoReportActionLaw_eq_selectedGlobal
        E region hregion threshold (hbaseMean.add measurable_const))
  have hglobalPBO : ∀ᵐ publicBase ∂globalActionLaw.map Prod.fst,
      lg21HiddenAccessTailCandidateNoReportValue
        (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
        (M.accessLaw {false}) (M.accessLaw {true})
        (measure_ne_top _ _) (measure_ne_top _ _) threshold publicBase =
        ∫ latentSkill, latentSkill ∂condDistrib Prod.snd Prod.fst
          globalActionLaw publicBase := by
    simpa [rawLaw, globalEvent, globalActionLaw, record, threshold] using
      (lg21HiddenAccessConditionalMeanTail_noReportValue_eq_condDistribMean_ae
        M hnoAccess haccess testFeature baseLaw baseMean hbaseMean
        baseVariance.toNNReal hfullBaseFactor gap
        (measure_ne_top _ _) (measure_ne_top _ _))
  have hselectedPBO := lg21_selectedObservation_condDistribMean_eq_raw_ae
    globalActionLaw Prod.fst Prod.snd
    (fun publicBase =>
      lg21HiddenAccessTailCandidateNoReportValue
        (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
        (M.accessLaw {false}) (M.accessLaw {true})
        (measure_ne_top _ _) (measure_ne_top _ _) threshold publicBase)
    measurable_fst measurable_snd hglobalPBO (Prod.fst ⁻¹' region)
    (hregion.preimage measurable_fst) hglobalRegionPositive
  unfold LG21HiddenAccessSourceTimedCandidateNoReportPBOOn
  dsimp only
  change ∀ᵐ publicBase ∂localActionLaw.map Prod.fst,
    candidate.noReportValue publicBase =
      ∫ skill, skill ∂condDistrib Prod.snd Prod.fst localActionLaw publicBase
  rw [hlocalLaw]
  simpa [candidate, threshold] using hselectedPBO

/-- Positive no-access mass makes the localized literal `X = 0` branch
positive for every tail patch.  This is a raw-population inclusion, not an
access-conditioned no-report calculation. -/
theorem lg21HiddenAccessLocalTail_localNoReport_positive_of_noAccess
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (hnoAccess : 0 < M.accessLaw {false})
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hthreshold : Measurable threshold) :
    0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessRawCandidateNoReportEvent testFeature
        (lg21HiddenAccessLocalTailTake E region threshold)
        (lg21HiddenAccessLocalTailReport E region)) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
  let noAccessEvent := lg21HiddenAccessNoAccessEvent (Feature := Feature)
  let localEvent := lg21HiddenAccessRawCandidateNoReportEvent testFeature
    (lg21HiddenAccessLocalTailTake E region threshold)
    (lg21HiddenAccessLocalTailReport E region)
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hregionEvent : MeasurableSet regionEvent := by
    simpa [regionEvent] using
      (lg21HiddenAccessBaseRegionEvent_measurable testFeature region hregion)
  have htake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      lg21HiddenAccessLocalTailTake E region threshold pair.1 pair.2) :=
    lg21HiddenAccessLocalTailTake_measurable E region hregion threshold hthreshold
  have hreport : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      lg21HiddenAccessLocalTailReport E region pair.1 pair.2) :=
    lg21HiddenAccessLocalTailReport_measurable E region hregion
  have hlocalEvent : MeasurableSet localEvent := by
    simpa [localEvent] using
      (lg21HiddenAccessRawCandidateNoReportEvent_measurable testFeature
        (lg21HiddenAccessLocalTailTake E region threshold)
        (lg21HiddenAccessLocalTailReport E region) htake hreport)
  have hcomponentPositive : 0 < rawLaw (noAccessEvent ∩ regionEvent) := by
    simpa [rawLaw, noAccessEvent, regionEvent] using
      (lg21HiddenAccess_noAccess_inter_baseRegion_positive
        M testFeature region hnoAccess hregionPositive)
  have hsubset : noAccessEvent ∩ regionEvent ⊆ localEvent ∩ regionEvent := by
    intro student hstudent
    rcases hstudent with ⟨hnoAccessStudent, hregionStudent⟩
    refine ⟨?_, hregionStudent⟩
    rcases student with ⟨access, primitive⟩
    cases access <;>
      simp [localEvent, noAccessEvent,
        lg21HiddenAccessRawCandidateNoReportEvent,
        lg21HiddenAccessOptionalObservedAction,
        lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport] at hnoAccessStudent ⊢
  have htargetPositive : 0 < rawLaw (localEvent ∩ regionEvent) :=
    lt_of_lt_of_le hcomponentPositive (measure_mono hsubset)
  change 0 < lg21NormalizedRestriction rawLaw regionEvent localEvent
  rw [lg21NormalizedRestriction_apply rawLaw hlocalEvent]
  exact ENNReal.mul_pos
    (ENNReal.inv_ne_zero.mpr (measure_ne_top rawLaw regionEvent))
    htargetPositive

/-- A positive public-base region contains a positive literal report branch
for the localized latent-tail candidate.  The proof first obtains positive
Gaussian tail mass after restricting the base law, then restores the hidden
positive-access coordinate at the raw source level. -/
theorem lg21HiddenAccessLocalTail_localReport_and_globalRegion_positive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (haccess : 0 < M.accessLaw {true})
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hthreshold : Measurable threshold)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance) :
    0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessRawCandidateReportEvent testFeature
        (lg21HiddenAccessLocalTailTake E region threshold)
        (lg21HiddenAccessLocalTailReport E region)) ∧
    0 <
      ((lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
        (lg21HiddenAccessRawCandidateReportEvent testFeature
          (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
          (fun _ _ => true))).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature))
          (Prod.fst ⁻¹' region) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let observation := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
  let tailEvent := lg21ReportRequiredBaseDependentTailTakeEvent threshold
  let regionProduct : Set ((LG21NonTestFeature Feature testFeature -> ℝ) ×
      (ℝ × ℝ)) := region ×ˢ Set.univ
  let localEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
    (lg21HiddenAccessLocalTailTake E region threshold)
    (lg21HiddenAccessLocalTailReport E region)
  let globalEvent := lg21HiddenAccessRawCandidateReportEvent testFeature
    (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
    (fun _ _ => true)
  let joint := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure accessLaw := by
    simpa [accessLaw] using
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hobservation : Measurable observation := by
    simpa [observation] using
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature)
  have hregionEvent : MeasurableSet regionEvent := by
    simpa [regionEvent] using
      (lg21HiddenAccessBaseRegionEvent_measurable testFeature region hregion)
  have htailEvent : MeasurableSet tailEvent := by
    simpa [tailEvent] using
      (lg21ReportRequiredBaseDependentTailTakeEvent_measurable
        threshold hthreshold)
  have hregionProduct : MeasurableSet regionProduct := by
    simpa [regionProduct] using hregion.prod MeasurableSet.univ
  have hregionPreimage : observation ⁻¹' regionProduct = regionEvent := by
    ext student
    simp [observation, regionProduct, regionEvent, base]
  have hbaseMap : rawLaw.map base = baseLaw := by
    calc
      rawLaw.map base = (rawLaw.map observation).map Prod.fst := by
        rw [Measure.map_map measurable_fst hobservation]
        rfl
      _ = (baseLaw ⊗ₘ joint).map Prod.fst := by
        rw [show rawLaw.map observation = baseLaw ⊗ₘ joint by
          simpa [rawLaw, observation, joint] using hsourceFactor]
      _ = baseLaw := by
        change (baseLaw ⊗ₘ joint).fst = baseLaw
        rw [Measure.fst_compProd]
  have hbaseRegionPositive : 0 < baseLaw region := by
    have hrawRegionPositive : 0 < rawLaw (base ⁻¹' region) := by
      simpa [rawLaw, base, regionEvent] using hregionPositive
    rw [← Measure.map_apply hbase hregion, hbaseMap] at hrawRegionPositive
    exact hrawRegionPositive
  let localBaseLaw := lg21NormalizedRestriction baseLaw region
  letI : IsProbabilityMeasure localBaseLaw :=
    lg21NormalizedRestriction_isProbability baseLaw region
      (ne_of_gt hbaseRegionPositive) (measure_ne_top _ _)
  have htailLocalPositive : 0 < (localBaseLaw ⊗ₘ joint) tailEvent := by
    simpa [localBaseLaw, joint, tailEvent] using
      (lg21ReportRequiredBaseDependentTail_take_positive
        localBaseLaw baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance threshold hthreshold)
  have htailNormalizedPositive : 0 <
      (lg21NormalizedRestriction (baseLaw ⊗ₘ joint) regionProduct) tailEvent := by
    rw [lg21_normalizedRestriction_compProd_left baseLaw joint region hregion]
    simpa [localBaseLaw] using htailLocalPositive
  have hjointIntersectionPositive : 0 < (baseLaw ⊗ₘ joint)
      (tailEvent ∩ regionProduct) := by
    rw [lg21NormalizedRestriction_apply (baseLaw ⊗ₘ joint) htailEvent]
      at htailNormalizedPositive
    exact (ENNReal.mul_pos_iff.mp htailNormalizedPositive).2
  have haccessScoreSkill : accessLaw.map observation = baseLaw ⊗ₘ joint := by
    calc
      accessLaw.map observation = rawLaw.map observation := by
        symm
        simpa [rawLaw, accessLaw, observation] using
          (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
            M haccess testFeature)
      _ = baseLaw ⊗ₘ joint := by
        simpa [rawLaw, observation, joint] using hsourceFactor
  have haccessIntersectionPositive : 0 < accessLaw
      (observation ⁻¹' (tailEvent ∩ regionProduct)) := by
    rw [← Measure.map_apply hobservation (htailEvent.inter hregionProduct),
      haccessScoreSkill]
    exact hjointIntersectionPositive
  have hrawAccessIntersectionPositive : 0 < rawLaw
      (accessEvent ∩ observation ⁻¹' (tailEvent ∩ regionProduct)) := by
    change 0 < lg21NormalizedRestriction rawLaw accessEvent
      (observation ⁻¹' (tailEvent ∩ regionProduct)) at haccessIntersectionPositive
    rw [lg21NormalizedRestriction_apply rawLaw
      ((htailEvent.inter hregionProduct).preimage hobservation)]
      at haccessIntersectionPositive
    have hraw : 0 < rawLaw
        ((observation ⁻¹' (tailEvent ∩ regionProduct)) ∩ accessEvent) :=
      (ENNReal.mul_pos_iff.mp haccessIntersectionPositive).2
    simpa [inter_comm] using hraw
  have hglobalEvent : globalEvent = accessEvent ∩ observation ⁻¹' tailEvent := by
    simpa [globalEvent, accessEvent, observation, tailEvent] using
      (lg21HiddenAccessConditionalMeanTail_rawCandidateReportEvent_eq_access_inter_preimage
        testFeature threshold)
  have hglobalIntersectionPositive : 0 < rawLaw
      (globalEvent ∩ regionEvent) := by
    rw [hglobalEvent, ← hregionPreimage]
    have hset : (accessEvent ∩ observation ⁻¹' tailEvent) ∩
        observation ⁻¹' regionProduct =
        accessEvent ∩ observation ⁻¹' (tailEvent ∩ regionProduct) := by
      ext student
      simp
    rw [hset]
    exact hrawAccessIntersectionPositive
  have hlocalIntersectionPositive : 0 < rawLaw
      (regionEvent ∩ localEvent) := by
    rw [lg21HiddenAccessBaseRegion_inter_localTailReportEvent_eq_globalTail]
    simpa [inter_comm] using hglobalIntersectionPositive
  have hlocalPositive : 0 < lg21NormalizedRestriction rawLaw regionEvent
      localEvent := by
    have htake : Measurable (fun pair : ℝ ×
        (LG21NonTestFeature Feature testFeature -> ℝ) =>
        lg21HiddenAccessLocalTailTake E region threshold pair.1 pair.2) :=
      lg21HiddenAccessLocalTailTake_measurable E region hregion threshold hthreshold
    have hreport : Measurable (fun pair :
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
        lg21HiddenAccessLocalTailReport E region pair.1 pair.2) :=
      lg21HiddenAccessLocalTailReport_measurable E region hregion
    have hlocalEvent : MeasurableSet localEvent := by
      simpa [localEvent] using
        (lg21HiddenAccessRawCandidateReportEvent_measurable testFeature
          (lg21HiddenAccessLocalTailTake E region threshold)
          (lg21HiddenAccessLocalTailReport E region) htake hreport)
    exact lg21_normalizedRestriction_pos_of_inter_pos rawLaw regionEvent
      localEvent hregionEvent (by simpa [inter_comm] using hlocalIntersectionPositive)
  have hglobalPositive : 0 < rawLaw globalEvent :=
    lt_of_lt_of_le hglobalIntersectionPositive
      (measure_mono (by intro student hstudent; exact hstudent.1))
  let globalActionLaw := (lg21NormalizedRestriction rawLaw globalEvent).map observation
  letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw globalEvent) :=
    lg21NormalizedRestriction_isProbability rawLaw globalEvent
      (ne_of_gt hglobalPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure globalActionLaw :=
    Measure.isProbabilityMeasure_map hobservation.aemeasurable
  have hglobalRegionPositive : 0 < globalActionLaw (Prod.fst ⁻¹' region) := by
    rw [show globalActionLaw =
      (lg21NormalizedRestriction rawLaw globalEvent).map observation by rfl,
      Measure.map_apply hobservation (hregion.preimage measurable_fst),
      lg21NormalizedRestriction_apply rawLaw
        ((hregion.preimage measurable_fst).preimage hobservation)]
    have hpreimage : observation ⁻¹' (Prod.fst ⁻¹' region) = regionEvent := by
      ext student
      simp [observation, regionEvent, base]
    rw [hpreimage]
    exact ENNReal.mul_pos
      (ENNReal.inv_ne_zero.mpr (measure_ne_top rawLaw globalEvent))
      hglobalIntersectionPositive
  refine ⟨?_, ?_⟩
  · simpa [rawLaw, regionEvent, localEvent] using hlocalPositive
  · simpa [rawLaw, globalEvent, observation, globalActionLaw] using
      hglobalRegionPositive

/-! ## Source-faithful report-required local entries -/

/-- The literal report branch of a report-required candidate.  The only
strategic candidate action is the pre-score take decision; a candidate access
student who takes necessarily reports. -/
def lg21HiddenAccessReportRequiredCandidateReportEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool) :
    Set (Bool × (ℝ × (Feature -> ℝ))) :=
  lg21HiddenAccessRawCandidateReportEvent testFeature candidateTake (fun _ _ => true)

/-- The literal no-report branch of a report-required candidate.  It retains
both no-access students and access students whose pre-score action is not to
take; no score-contingent withholding branch is introduced. -/
def lg21HiddenAccessReportRequiredCandidateNoReportEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (candidateTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool) :
    Set (Bool × (ℝ × (Feature -> ℝ))) :=
  lg21HiddenAccessRawCandidateNoReportEvent testFeature candidateTake (fun _ _ => true)

/-- Access students whose report-required pre-score action changes from no
test to test in a local candidate.  This is defined extensionally from the
two actions and never from a strategy name. -/
def lg21HiddenAccessReportRequiredChangedTesterEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (currentTake candidateTake :
      ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool) :
    Set (Bool × (ℝ × (Feature -> ℝ))) :=
  {student | student.1 = true ∧
    currentTake (lg21ContinuousPopulationSkill student)
      (lg21HiddenAccessStudentBase testFeature student.2) = false ∧
    candidateTake (lg21ContinuousPopulationSkill student)
      (lg21HiddenAccessStudentBase testFeature student.2) = true}

/-- The data needed by a report-required local recalibration candidate.  This
deliberately omits `estimationConsistent` and every global-equilibrium field:
the source-local carrier below records its own literal branch PBOs instead. -/
structure LG21ReportRequiredCandidateBranchData
    (Skill Base Test : Type*) [MeasurableSpace Test] where
  testLaw : Skill -> Base -> Measure Test
  testLaw_isProbability : ∀ skill base, IsProbabilityMeasure (testLaw skill base)
  takeDecision : Skill -> Base -> Bool
  reportedPayoff : Base -> Test -> ℝ
  noReportPayoff : Base -> ℝ
  reportedPayoff_integrable : ∀ skill base,
    Integrable (reportedPayoff base) (testLaw skill base)

/-- The only payoff relevant to a report-required pre-score candidate. -/
def lg21ReportRequiredCandidateTakeExpectedPayoff
    {Skill Base Test : Type*} [MeasurableSpace Test]
    (candidate : LG21ReportRequiredCandidateBranchData Skill Base Test)
    (skill : Skill) (base : Base) : ℝ :=
  ∫ test, candidate.reportedPayoff base test ∂candidate.testLaw skill base

/-- Literal report-branch PBO for a local report-required candidate.  The
action law is built from its one pre-score decision and the forced-report
timing, so no optional post-score action is present in this obligation. -/
def LG21HiddenAccessReportRequiredCandidateReportPBOOn
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (candidate : LG21ReportRequiredCandidateBranchData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hreportPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessReportRequiredCandidateReportEvent testFeature
        candidate.takeDecision)) : Prop :=
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
  let reportEvent := lg21HiddenAccessReportRequiredCandidateReportEvent
    testFeature candidate.takeDecision
  let actionLaw := (lg21NormalizedRestriction localLaw reportEvent).map
    (lg21HiddenAccessBaseScoreSkillObservation testFeature)
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure localLaw :=
    lg21NormalizedRestriction_isProbability rawLaw
      (lg21HiddenAccessBaseRegionEvent testFeature region)
      (ne_of_gt hregionPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure (lg21NormalizedRestriction localLaw reportEvent) :=
    lg21NormalizedRestriction_isProbability localLaw reportEvent
      (ne_of_gt hreportPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure actionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
  ∀ᵐ publicObservation ∂actionLaw.map
      (fun scoreSkill :
        (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
        (scoreSkill.1, scoreSkill.2.1)),
    candidate.reportedPayoff publicObservation.1 publicObservation.2 =
      ∫ latentSkill, latentSkill ∂condDistrib
        (fun scoreSkill :
          (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
          scoreSkill.2.2)
        (fun scoreSkill :
          (LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ) =>
          (scoreSkill.1, scoreSkill.2.1))
        actionLaw publicObservation

/-- Literal no-report PBO for a local report-required candidate.  In
particular, this branch is normalized from the raw population and therefore
keeps the no-access component. -/
def LG21HiddenAccessReportRequiredCandidateNoReportPBOOn
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (candidate : LG21ReportRequiredCandidateBranchData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hnoReportPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessReportRequiredCandidateNoReportEvent testFeature
        candidate.takeDecision)) : Prop :=
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
  let noReportEvent := lg21HiddenAccessReportRequiredCandidateNoReportEvent
    testFeature candidate.takeDecision
  let actionLaw := (lg21NormalizedRestriction localLaw noReportEvent).map
    (lg21HiddenAccessBaseSkillObservation testFeature)
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure localLaw :=
    lg21NormalizedRestriction_isProbability rawLaw
      (lg21HiddenAccessBaseRegionEvent testFeature region)
      (ne_of_gt hregionPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure (lg21NormalizedRestriction localLaw noReportEvent) :=
    lg21NormalizedRestriction_isProbability localLaw noReportEvent
      (ne_of_gt hnoReportPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure actionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure actionLaw := ⟨by simp⟩
  ∀ᵐ publicBase ∂actionLaw.map Prod.fst,
    candidate.noReportPayoff publicBase =
      ∫ latentSkill, latentSkill ∂condDistrib Prod.snd Prod.fst
        actionLaw publicBase

/-- A source-local candidate for report-required testing under hidden access.
The candidate carries exactly one student decision, `takeDecision`; report is
forced after taking.  Its two PBOs are literal raw-population conditional
means on positive branches, and the only profitability obligation is
pre-score. -/
structure LG21HiddenAccessReportRequiredLocalCandidateEntry
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (currentTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool) where
  region : Set (LG21NonTestFeature Feature testFeature -> ℝ)
  region_measurable : MeasurableSet region
  region_positive : 0 < lg21ContinuousGaussianPopulationLaw M
    (lg21HiddenAccessBaseRegionEvent testFeature region)
  current_take_measurable : Measurable (fun pair : ℝ ×
    (LG21NonTestFeature Feature testFeature -> ℝ) => currentTake pair.1 pair.2)
  current_take_zero : lg21HiddenAccessLocalRawLaw M testFeature region
    {student | student.1 = true ∧
      currentTake (lg21ContinuousPopulationSkill student)
        (lg21HiddenAccessStudentBase testFeature student.2) = true} = 0
  candidate : LG21ReportRequiredCandidateBranchData ℝ
    (LG21NonTestFeature Feature testFeature -> ℝ) ℝ
  candidate_take_measurable : Measurable (fun pair : ℝ ×
    (LG21NonTestFeature Feature testFeature -> ℝ) =>
      candidate.takeDecision pair.1 pair.2)
  candidate_changed_taker_positive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
    (lg21HiddenAccessReportRequiredChangedTesterEvent testFeature currentTake
      candidate.takeDecision)
  candidate_report_positive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
    (lg21HiddenAccessReportRequiredCandidateReportEvent testFeature
      candidate.takeDecision)
  candidate_noReport_positive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
    (lg21HiddenAccessReportRequiredCandidateNoReportEvent testFeature
      candidate.takeDecision)
  candidate_report_pbo : LG21HiddenAccessReportRequiredCandidateReportPBOOn
    M testFeature region region_positive candidate candidate_report_positive
  candidate_noReport_pbo : LG21HiddenAccessReportRequiredCandidateNoReportPBOOn
    M testFeature region region_positive candidate candidate_noReport_positive
  candidate_changed_tester_strict_gain : ∀ᵐ student ∂
      (lg21HiddenAccessLocalRawLaw M testFeature region).restrict
        (lg21HiddenAccessReportRequiredChangedTesterEvent testFeature currentTake
          candidate.takeDecision),
      candidate.noReportPayoff (lg21HiddenAccessStudentBase testFeature student.2) <
        lg21ReportRequiredCandidateTakeExpectedPayoff candidate
          (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2)

/-- Stability against literal positive-mass report-required local entries.
Unlike the optional carrier, this predicate has no score-contingent reporting
action and no ex-post reporting best-response field. -/
def LG21HiddenAccessReportRequiredStableAgainstLocalCandidateEntry
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (currentTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool) : Prop :=
  ¬ Nonempty (LG21HiddenAccessReportRequiredLocalCandidateEntry
    (M := M) (testFeature := testFeature) currentTake)

theorem lg21HiddenAccessReportRequired_not_stable_of_localCandidateEntry
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (currentTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (hentry : LG21HiddenAccessReportRequiredLocalCandidateEntry
      (M := M) (testFeature := testFeature) currentTake) :
    ¬ LG21HiddenAccessReportRequiredStableAgainstLocalCandidateEntry
      (M := M) (testFeature := testFeature) currentTake := by
  intro hstable
  exact hstable ⟨hentry⟩

/-- The concrete report-required hidden-access tail candidate.  It has one
pre-score action and uses the literal raw no-report mixture for its outside
option. -/
noncomputable def lg21HiddenAccessReportRequiredLocalTailCandidate
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {testFeature : Feature}
    (baseMean threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance) (hnoiseVariance : 0 < noiseVariance)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) :
    LG21ReportRequiredCandidateBranchData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ where
  testLaw := fun latentSkill _publicBase =>
    gaussianReal latentSkill noiseVariance.toNNReal
  testLaw_isProbability := by
    intro latentSkill publicBase
    infer_instance
  takeDecision := fun latentSkill publicBase =>
    decide (threshold publicBase ≤ latentSkill)
  reportedPayoff := fun publicBase observedScore =>
    lg21SelectedGaussianUpperTailReporterPBO
      (baseMean publicBase) baseVariance noiseVariance
      (threshold publicBase) observedScore
  noReportPayoff := fun publicBase =>
    lg21HiddenAccessTailCandidateNoReportValue
      (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
      noAccessMass accessMass hnoAccessFinite haccessFinite threshold publicBase
  reportedPayoff_integrable := by
    intro latentSkill publicBase
    exact lg21SelectedGaussianUpperTailReporterPBO_integrable
      (baseMean publicBase) baseVariance noiseVariance
      (threshold publicBase) latentSkill hbaseVariance hnoiseVariance

theorem lg21HiddenAccessReportRequiredLocalTailCandidate_take_eq_true_iff
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {testFeature : Feature}
    (baseMean threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance) (hnoiseVariance : 0 < noiseVariance)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (latentSkill : ℝ)
    (publicBase : LG21NonTestFeature Feature testFeature -> ℝ) :
    (lg21HiddenAccessReportRequiredLocalTailCandidate
      baseMean threshold hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance noAccessMass accessMass
      hnoAccessFinite haccessFinite).takeDecision latentSkill publicBase = true ↔
      threshold publicBase ≤ latentSkill := by
  simp [lg21HiddenAccessReportRequiredLocalTailCandidate]

theorem lg21HiddenAccessReportRequiredLocalTailCandidate_reportedPayoff
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {testFeature : Feature}
    (baseMean threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance) (hnoiseVariance : 0 < noiseVariance)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (publicBase : LG21NonTestFeature Feature testFeature -> ℝ) (observedScore : ℝ) :
    (lg21HiddenAccessReportRequiredLocalTailCandidate
      baseMean threshold hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance noAccessMass accessMass
      hnoAccessFinite haccessFinite).reportedPayoff publicBase observedScore =
      lg21SelectedGaussianUpperTailReporterPBO
        (baseMean publicBase) baseVariance noiseVariance
        (threshold publicBase) observedScore := by
  rfl

theorem lg21HiddenAccessReportRequiredLocalTailCandidate_noReportPayoff
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {testFeature : Feature}
    (baseMean threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance) (hnoiseVariance : 0 < noiseVariance)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (publicBase : LG21NonTestFeature Feature testFeature -> ℝ) :
    (lg21HiddenAccessReportRequiredLocalTailCandidate
      baseMean threshold hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance noAccessMass accessMass
      hnoAccessFinite haccessFinite).noReportPayoff publicBase =
      lg21HiddenAccessTailCandidateNoReportValue
        (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
        noAccessMass accessMass hnoAccessFinite haccessFinite threshold publicBase := by
  rfl

/-- Positive no-access mass makes the local report-required candidate's
literal no-report branch positive on every positive base region. -/
theorem lg21HiddenAccessReportRequiredLocalTail_noReport_positive_of_noAccess
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (hnoAccess : 0 < M.accessLaw {false})
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hthreshold : Measurable threshold) :
    0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessReportRequiredCandidateNoReportEvent testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
  let noAccessEvent := lg21HiddenAccessNoAccessEvent (Feature := Feature)
  let noReportEvent := lg21HiddenAccessReportRequiredCandidateNoReportEvent
    testFeature (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hregionEvent : MeasurableSet regionEvent := by
    simpa [regionEvent] using
      (lg21HiddenAccessBaseRegionEvent_measurable testFeature region hregion)
  have htake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      lg21HiddenAccessConditionalMeanTailTake testFeature threshold pair.1 pair.2) :=
    lg21HiddenAccessConditionalMeanTailTake_measurable testFeature threshold hthreshold
  have hnoReportEvent : MeasurableSet noReportEvent := by
    simpa [noReportEvent, lg21HiddenAccessReportRequiredCandidateNoReportEvent] using
      (lg21HiddenAccessRawCandidateNoReportEvent_measurable testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
        (fun _ _ => true) htake measurable_const)
  have hcomponentPositive : 0 < rawLaw (noAccessEvent ∩ regionEvent) := by
    simpa [rawLaw, noAccessEvent, regionEvent] using
      (lg21HiddenAccess_noAccess_inter_baseRegion_positive
        M testFeature region hnoAccess hregionPositive)
  have hsubset : noAccessEvent ∩ regionEvent ⊆ noReportEvent ∩ regionEvent := by
    intro student hstudent
    rcases hstudent with ⟨hnoAccessStudent, hregionStudent⟩
    refine ⟨?_, hregionStudent⟩
    rcases student with ⟨access, primitive⟩
    cases access <;>
      simp [noReportEvent, lg21HiddenAccessReportRequiredCandidateNoReportEvent,
        lg21HiddenAccessRawCandidateNoReportEvent,
        lg21HiddenAccessOptionalObservedAction,
        lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport] at hnoAccessStudent ⊢
  have htargetPositive : 0 < rawLaw (noReportEvent ∩ regionEvent) :=
    lt_of_lt_of_le hcomponentPositive (measure_mono hsubset)
  change 0 < lg21NormalizedRestriction rawLaw regionEvent noReportEvent
  rw [lg21NormalizedRestriction_apply rawLaw hnoReportEvent]
  exact ENNReal.mul_pos
    (ENNReal.inv_ne_zero.mpr (measure_ne_top rawLaw regionEvent))
    htargetPositive

/-- A positive base region has positive report-required tail mass.  The
second conclusion is the same fact on the global selected action law and is
used to transport the literal report PBO to the local recalibration. -/
theorem lg21HiddenAccessReportRequiredLocalTail_report_and_globalRegion_positive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (haccess : 0 < M.accessLaw {true})
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hthreshold : Measurable threshold)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance) :
    0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessReportRequiredCandidateReportEvent testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)) ∧
    0 <
      ((lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
        (lg21HiddenAccessReportRequiredCandidateReportEvent testFeature
          (lg21HiddenAccessConditionalMeanTailTake testFeature threshold))).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature))
          (Prod.fst ⁻¹' region) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  let base : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) :=
    fun student => lg21HiddenAccessStudentBase testFeature student.2
  let observation := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
  let tailEvent := lg21ReportRequiredBaseDependentTailTakeEvent threshold
  let regionProduct : Set ((LG21NonTestFeature Feature testFeature -> ℝ) ×
      (ℝ × ℝ)) := region ×ˢ Set.univ
  let reportEvent := lg21HiddenAccessReportRequiredCandidateReportEvent
    testFeature (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
  let joint := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure accessLaw := by
    simpa [accessLaw] using
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  have hbase : Measurable base := by
    simpa [base] using
      ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd)
  have hobservation : Measurable observation := by
    simpa [observation] using
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature)
  have hregionEvent : MeasurableSet regionEvent := by
    simpa [regionEvent] using
      (lg21HiddenAccessBaseRegionEvent_measurable testFeature region hregion)
  have htailEvent : MeasurableSet tailEvent := by
    simpa [tailEvent] using
      (lg21ReportRequiredBaseDependentTailTakeEvent_measurable
        threshold hthreshold)
  have hregionProduct : MeasurableSet regionProduct := by
    simpa [regionProduct] using hregion.prod MeasurableSet.univ
  have hregionPreimage : observation ⁻¹' regionProduct = regionEvent := by
    ext student
    simp [observation, regionProduct, regionEvent, base]
  have hbaseMap : rawLaw.map base = baseLaw := by
    calc
      rawLaw.map base = (rawLaw.map observation).map Prod.fst := by
        rw [Measure.map_map measurable_fst hobservation]
        rfl
      _ = (baseLaw ⊗ₘ joint).map Prod.fst := by
        rw [show rawLaw.map observation = baseLaw ⊗ₘ joint by
          simpa [rawLaw, observation, joint] using hsourceFactor]
      _ = baseLaw := by
        change (baseLaw ⊗ₘ joint).fst = baseLaw
        rw [Measure.fst_compProd]
  have hbaseRegionPositive : 0 < baseLaw region := by
    have hrawRegionPositive : 0 < rawLaw (base ⁻¹' region) := by
      simpa [rawLaw, base, regionEvent] using hregionPositive
    rw [← Measure.map_apply hbase hregion, hbaseMap] at hrawRegionPositive
    exact hrawRegionPositive
  let localBaseLaw := lg21NormalizedRestriction baseLaw region
  letI : IsProbabilityMeasure localBaseLaw :=
    lg21NormalizedRestriction_isProbability baseLaw region
      (ne_of_gt hbaseRegionPositive) (measure_ne_top _ _)
  have htailLocalPositive : 0 < (localBaseLaw ⊗ₘ joint) tailEvent := by
    simpa [localBaseLaw, joint, tailEvent] using
      (lg21ReportRequiredBaseDependentTail_take_positive
        localBaseLaw baseMean hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance threshold hthreshold)
  have htailNormalizedPositive : 0 <
      (lg21NormalizedRestriction (baseLaw ⊗ₘ joint) regionProduct) tailEvent := by
    rw [lg21_normalizedRestriction_compProd_left baseLaw joint region hregion]
    simpa [localBaseLaw] using htailLocalPositive
  have hjointIntersectionPositive : 0 < (baseLaw ⊗ₘ joint)
      (tailEvent ∩ regionProduct) := by
    rw [lg21NormalizedRestriction_apply (baseLaw ⊗ₘ joint) htailEvent]
      at htailNormalizedPositive
    exact (ENNReal.mul_pos_iff.mp htailNormalizedPositive).2
  have haccessScoreSkill : accessLaw.map observation = baseLaw ⊗ₘ joint := by
    calc
      accessLaw.map observation = rawLaw.map observation := by
        symm
        simpa [rawLaw, accessLaw, observation] using
          (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
            M haccess testFeature)
      _ = baseLaw ⊗ₘ joint := by
        simpa [rawLaw, observation, joint] using hsourceFactor
  have haccessIntersectionPositive : 0 < accessLaw
      (observation ⁻¹' (tailEvent ∩ regionProduct)) := by
    rw [← Measure.map_apply hobservation (htailEvent.inter hregionProduct),
      haccessScoreSkill]
    exact hjointIntersectionPositive
  have hrawAccessIntersectionPositive : 0 < rawLaw
      (accessEvent ∩ observation ⁻¹' (tailEvent ∩ regionProduct)) := by
    change 0 < lg21NormalizedRestriction rawLaw accessEvent
      (observation ⁻¹' (tailEvent ∩ regionProduct)) at haccessIntersectionPositive
    rw [lg21NormalizedRestriction_apply rawLaw
      ((htailEvent.inter hregionProduct).preimage hobservation)]
      at haccessIntersectionPositive
    have hraw : 0 < rawLaw
        ((observation ⁻¹' (tailEvent ∩ regionProduct)) ∩ accessEvent) :=
      (ENNReal.mul_pos_iff.mp haccessIntersectionPositive).2
    simpa [inter_comm] using hraw
  have hreportEvent : reportEvent = accessEvent ∩ observation ⁻¹' tailEvent := by
    simpa [reportEvent, accessEvent, observation, tailEvent,
      lg21HiddenAccessReportRequiredCandidateReportEvent] using
      (lg21HiddenAccessConditionalMeanTail_rawCandidateReportEvent_eq_access_inter_preimage
        testFeature threshold)
  have hreportIntersectionPositive : 0 < rawLaw (reportEvent ∩ regionEvent) := by
    rw [hreportEvent, ← hregionPreimage]
    have hset : (accessEvent ∩ observation ⁻¹' tailEvent) ∩
        observation ⁻¹' regionProduct =
        accessEvent ∩ observation ⁻¹' (tailEvent ∩ regionProduct) := by
      ext student
      simp
    rw [hset]
    exact hrawAccessIntersectionPositive
  have hlocalPositive : 0 < lg21NormalizedRestriction rawLaw regionEvent
      reportEvent :=
    lg21_normalizedRestriction_pos_of_inter_pos rawLaw regionEvent
      reportEvent hregionEvent (by simpa [inter_comm] using hreportIntersectionPositive)
  have hglobalPositive : 0 < rawLaw reportEvent :=
    lt_of_lt_of_le hreportIntersectionPositive
      (measure_mono (by intro student hstudent; exact hstudent.1))
  let globalActionLaw := (lg21NormalizedRestriction rawLaw reportEvent).map observation
  letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw reportEvent) :=
    lg21NormalizedRestriction_isProbability rawLaw reportEvent
      (ne_of_gt hglobalPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure globalActionLaw :=
    Measure.isProbabilityMeasure_map hobservation.aemeasurable
  have hglobalRegionPositive : 0 < globalActionLaw (Prod.fst ⁻¹' region) := by
    rw [show globalActionLaw =
      (lg21NormalizedRestriction rawLaw reportEvent).map observation by rfl,
      Measure.map_apply hobservation (hregion.preimage measurable_fst),
      lg21NormalizedRestriction_apply rawLaw
        ((hregion.preimage measurable_fst).preimage hobservation)]
    have hpreimage : observation ⁻¹' (Prod.fst ⁻¹' region) = regionEvent := by
      ext student
      simp [observation, regionEvent, base]
    rw [hpreimage]
    exact ENNReal.mul_pos
      (ENNReal.inv_ne_zero.mpr (measure_ne_top rawLaw reportEvent))
      hreportIntersectionPositive
  refine ⟨?_, ?_⟩
  · simpa [rawLaw, regionEvent, reportEvent] using hlocalPositive
  · simpa [rawLaw, reportEvent, observation, globalActionLaw] using
      hglobalRegionPositive

/-- Transport the literal selected reporter PBO to a positive local base
region for the report-required tail candidate.  The transport first proves an
equality of action laws and then uses conditional-distribution invariance;
it does not reuse a global PBO representative by name. -/
theorem lg21HiddenAccessReportRequiredLocalTail_reportPBO_of_global
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (haccess : 0 < M.accessLaw {true})
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (hthreshold : Measurable threshold)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance)
    (hlocalPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessReportRequiredCandidateReportEvent testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)))
    (hglobalRegionPositive : 0 <
      ((lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
        (lg21HiddenAccessReportRequiredCandidateReportEvent testFeature
          (lg21HiddenAccessConditionalMeanTailTake testFeature threshold))).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature))
          (Prod.fst ⁻¹' region))
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤) :
    LG21HiddenAccessReportRequiredCandidateReportPBOOn M testFeature region
      hregionPositive
      (lg21HiddenAccessReportRequiredLocalTailCandidate
        baseMean threshold hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance noAccessMass accessMass
        hnoAccessFinite haccessFinite)
      (by simpa [lg21HiddenAccessReportRequiredLocalTailCandidate] using hlocalPositive) := by
  let candidate := lg21HiddenAccessReportRequiredLocalTailCandidate
    baseMean threshold hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance noAccessMass accessMass
    hnoAccessFinite haccessFinite
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
  let reportEvent := lg21HiddenAccessReportRequiredCandidateReportEvent
    testFeature candidate.takeDecision
  let globalEvent := lg21HiddenAccessReportRequiredCandidateReportEvent
    testFeature (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
  let record := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let observation : ((LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun scoreSkill => (scoreSkill.1, scoreSkill.2.1)
  let latent : ((LG21NonTestFeature Feature testFeature -> ℝ) × (ℝ × ℝ)) -> ℝ :=
    fun scoreSkill => scoreSkill.2.2
  let globalActionLaw := (lg21NormalizedRestriction rawLaw globalEvent).map record
  let localActionLaw := (lg21NormalizedRestriction localLaw reportEvent).map record
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure localLaw :=
    lg21NormalizedRestriction_isProbability rawLaw
      (lg21HiddenAccessBaseRegionEvent testFeature region)
      (ne_of_gt hregionPositive) (measure_ne_top _ _)
  have hglobalPositive : 0 < rawLaw globalEvent := by
    have hlocalPositiveRaw : 0 < rawLaw
        (lg21HiddenAccessBaseRegionEvent testFeature region ∩ globalEvent) := by
      have hnormalized : 0 < lg21NormalizedRestriction rawLaw
          (lg21HiddenAccessBaseRegionEvent testFeature region) globalEvent := by
        simpa [rawLaw, localLaw, globalEvent,
          lg21HiddenAccessReportRequiredCandidateReportEvent] using hlocalPositive
      rw [lg21NormalizedRestriction_apply rawLaw
        (by
          simpa [globalEvent, lg21HiddenAccessReportRequiredCandidateReportEvent] using
            (lg21HiddenAccessRawCandidateReportEvent_measurable testFeature
              (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
              (fun _ _ => true)
              (lg21HiddenAccessConditionalMeanTailTake_measurable
                testFeature threshold hthreshold) measurable_const))]
        at hnormalized
      exact (ENNReal.mul_pos_iff.mp hnormalized).2
    exact lt_of_lt_of_le hlocalPositiveRaw
      (measure_mono (by intro student hstudent; exact hstudent.2))
  letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw globalEvent) :=
    lg21NormalizedRestriction_isProbability rawLaw globalEvent
      (ne_of_gt hglobalPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure localActionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure localActionLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure globalActionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure globalActionLaw := ⟨by simp⟩
  have hrecord : Measurable record := by
    simpa [record] using
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature)
  have hbase : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      lg21HiddenAccessStudentBase testFeature student.2) := by
    exact (lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd
  have hrecordBase : Measurable Prod.fst := measurable_fst
  have hrecordBaseEq : ∀ student,
      Prod.fst (record student) =
        lg21HiddenAccessStudentBase testFeature student.2 := by
    intro student
    rfl
  have hglobalEventMeasurable : MeasurableSet globalEvent := by
    simpa [globalEvent, lg21HiddenAccessReportRequiredCandidateReportEvent] using
      (lg21HiddenAccessRawCandidateReportEvent_measurable testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
        (fun _ _ => true)
        (lg21HiddenAccessConditionalMeanTailTake_measurable
          testFeature threshold hthreshold) measurable_const)
  have hlocalLaw : localActionLaw =
      lg21NormalizedRestriction globalActionLaw (Prod.fst ⁻¹' region) := by
    simpa [rawLaw, localLaw, globalActionLaw, localActionLaw,
      reportEvent, globalEvent, candidate,
      lg21HiddenAccessReportRequiredCandidateReportEvent] using
      (lg21_normalizedLocalBaseActionLaw_eq_normalizedGlobalActionLaw rawLaw
        (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
          lg21HiddenAccessStudentBase testFeature student.2)
        record Prod.fst hbase hrecord hrecordBase hrecordBaseEq
        region hregion globalEvent hglobalEventMeasurable)
  have hglobalPBO : ∀ᵐ publicObservation ∂globalActionLaw.map observation,
      lg21SelectedGaussianUpperTailReporterPBO
        (baseMean publicObservation.1) baseVariance noiseVariance
        (threshold publicObservation.1) publicObservation.2 =
        ∫ latentSkill, latentSkill ∂condDistrib latent observation
          globalActionLaw publicObservation := by
    simpa [rawLaw, globalEvent, globalActionLaw, record, observation, latent,
      lg21HiddenAccessReportRequiredCandidateReportEvent] using
      (lg21HiddenAccessConditionalMeanTail_reportedValue_eq_condDistribMean_ae
        M haccess testFeature baseLaw baseMean hbaseMean
        baseVariance noiseVariance hbaseVariance hnoiseVariance
        threshold hthreshold hsourceFactor)
  have hselectedPBO := lg21_selectedObservation_condDistribMean_eq_raw_ae
    globalActionLaw observation latent
    (fun publicObservation =>
      lg21SelectedGaussianUpperTailReporterPBO
        (baseMean publicObservation.1) baseVariance noiseVariance
        (threshold publicObservation.1) publicObservation.2)
    (by
      dsimp [observation]
      fun_prop)
    (by
      dsimp [latent]
      fun_prop)
    hglobalPBO (Prod.fst ⁻¹' region)
    (hregion.preimage measurable_fst)
    (by simpa [rawLaw, globalEvent, globalActionLaw, record,
      lg21HiddenAccessReportRequiredCandidateReportEvent] using hglobalRegionPositive)
  unfold LG21HiddenAccessReportRequiredCandidateReportPBOOn
  dsimp only
  change ∀ᵐ publicObservation ∂localActionLaw.map observation,
    candidate.reportedPayoff publicObservation.1 publicObservation.2 =
      ∫ latentSkill, latentSkill ∂condDistrib latent observation
        localActionLaw publicObservation
  rw [hlocalLaw]
  simpa [candidate, observation, latent] using hselectedPBO

/-- The literal no-report branch is positive both locally and after forming
the global candidate action law.  Its proof uses the raw no-access component,
not an access-only posterior. -/
theorem lg21HiddenAccessReportRequiredLocalTail_noReport_and_globalRegion_positive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (hnoAccess : 0 < M.accessLaw {false})
    (threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hthreshold : Measurable threshold) :
    0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessReportRequiredCandidateNoReportEvent testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)) ∧
    0 <
      ((lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
        (lg21HiddenAccessReportRequiredCandidateNoReportEvent testFeature
          (lg21HiddenAccessConditionalMeanTailTake testFeature threshold))).map
        (lg21HiddenAccessBaseSkillObservation testFeature))
          (Prod.fst ⁻¹' region) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let regionEvent := lg21HiddenAccessBaseRegionEvent testFeature region
  let noAccessEvent := lg21HiddenAccessNoAccessEvent (Feature := Feature)
  let noReportEvent := lg21HiddenAccessReportRequiredCandidateNoReportEvent
    testFeature (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
  let record := lg21HiddenAccessBaseSkillObservation testFeature
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hlocalPositive : 0 < lg21NormalizedRestriction rawLaw regionEvent
      noReportEvent := by
    simpa [rawLaw, regionEvent, noReportEvent] using
      (lg21HiddenAccessReportRequiredLocalTail_noReport_positive_of_noAccess
        (M := M) region hregion hregionPositive hnoAccess threshold hthreshold)
  have hnoReportEventMeasurable : MeasurableSet noReportEvent := by
    simpa [noReportEvent, lg21HiddenAccessReportRequiredCandidateNoReportEvent] using
      (lg21HiddenAccessRawCandidateNoReportEvent_measurable testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
        (fun _ _ => true)
        (lg21HiddenAccessConditionalMeanTailTake_measurable
          testFeature threshold hthreshold) measurable_const)
  have hregionEventMeasurable : MeasurableSet regionEvent := by
    simpa [regionEvent] using
      (lg21HiddenAccessBaseRegionEvent_measurable testFeature region hregion)
  have hlocalRawPositive : 0 < rawLaw (noReportEvent ∩ regionEvent) := by
    rw [lg21NormalizedRestriction_apply rawLaw hnoReportEvent] at hlocalPositive
    exact (ENNReal.mul_pos_iff.mp hlocalPositive).2
  have hglobalPositive : 0 < rawLaw noReportEvent :=
    lt_of_lt_of_le hlocalRawPositive
      (measure_mono (by intro student hstudent; exact hstudent.1))
  let globalActionLaw :=
    (lg21NormalizedRestriction rawLaw noReportEvent).map record
  letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw noReportEvent) :=
    lg21NormalizedRestriction_isProbability rawLaw noReportEvent
      (ne_of_gt hglobalPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure globalActionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature).aemeasurable
  have hrecord : Measurable record := by
    simpa [record] using
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature)
  have hregionPreimage : record ⁻¹' (Prod.fst ⁻¹' region) = regionEvent := by
    ext student
    simp [record, regionEvent, lg21HiddenAccessBaseSkillObservation,
      lg21HiddenAccessStudentBase]
  have hglobalRegionPositive : 0 < globalActionLaw (Prod.fst ⁻¹' region) := by
    rw [show globalActionLaw =
      (lg21NormalizedRestriction rawLaw noReportEvent).map record by rfl,
      Measure.map_apply hrecord (hregion.preimage measurable_fst),
      lg21NormalizedRestriction_apply rawLaw
        ((hregion.preimage measurable_fst).preimage hrecord),
      hregionPreimage]
    exact ENNReal.mul_pos
      (ENNReal.inv_ne_zero.mpr (measure_ne_top rawLaw noReportEvent))
      (by simpa [inter_comm] using hlocalRawPositive)
  refine ⟨?_, ?_⟩
  · simpa [rawLaw, regionEvent, noReportEvent] using hlocalPositive
  · simpa [rawLaw, noReportEvent, record, globalActionLaw] using
      hglobalRegionPositive

/-- Transport the literal raw no-report PBO to a positive local base region
for the report-required tail candidate.  The full base/skill factorization is
an explicit premise because it is what preserves the hidden no-access mixture
when the score coordinate is forgotten. -/
theorem lg21HiddenAccessReportRequiredLocalTail_noReportPBO_of_global
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance)
    (hnoiseVariance : 0 < noiseVariance)
    (gap : ℝ)
    (hnoAccess : 0 < M.accessLaw {false})
    (haccess : 0 < M.accessLaw {true})
    (hfullBaseFactor :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
          baseVariance.toNNReal)
    (hlocalPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessReportRequiredCandidateNoReportEvent testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature
          (fun publicBase => baseMean publicBase + gap))))
    (hglobalRegionPositive : 0 <
      ((lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
        (lg21HiddenAccessReportRequiredCandidateNoReportEvent testFeature
          (lg21HiddenAccessConditionalMeanTailTake testFeature
            (fun publicBase => baseMean publicBase + gap)))).map
        (lg21HiddenAccessBaseSkillObservation testFeature))
          (Prod.fst ⁻¹' region)) :
    LG21HiddenAccessReportRequiredCandidateNoReportPBOOn M testFeature region
      hregionPositive
      (lg21HiddenAccessReportRequiredLocalTailCandidate
        baseMean (fun publicBase => baseMean publicBase + gap) hbaseMean
        baseVariance noiseVariance hbaseVariance hnoiseVariance
        (M.accessLaw {false}) (M.accessLaw {true})
        (measure_ne_top _ _) (measure_ne_top _ _))
      (by simpa [lg21HiddenAccessReportRequiredLocalTailCandidate] using hlocalPositive) := by
  let threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ :=
    fun publicBase => baseMean publicBase + gap
  let candidate := lg21HiddenAccessReportRequiredLocalTailCandidate
    baseMean threshold hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance (M.accessLaw {false}) (M.accessLaw {true})
    (measure_ne_top _ _) (measure_ne_top _ _)
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
  let noReportEvent := lg21HiddenAccessReportRequiredCandidateNoReportEvent
    testFeature candidate.takeDecision
  let globalEvent := lg21HiddenAccessReportRequiredCandidateNoReportEvent
    testFeature (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
  let record := lg21HiddenAccessBaseSkillObservation testFeature
  let globalActionLaw := (lg21NormalizedRestriction rawLaw globalEvent).map record
  let localActionLaw := (lg21NormalizedRestriction localLaw noReportEvent).map record
  letI : IsMarkovKernel
      (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal) :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance.toNNReal
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure localLaw :=
    lg21NormalizedRestriction_isProbability rawLaw
      (lg21HiddenAccessBaseRegionEvent testFeature region)
      (ne_of_gt hregionPositive) (measure_ne_top _ _)
  have hglobalPositive : 0 < rawLaw globalEvent := by
    simpa [rawLaw, globalEvent, threshold,
      lg21HiddenAccessReportRequiredCandidateNoReportEvent] using
      (lg21HiddenAccessRawCandidate_noReport_positive_of_noAccess
        M testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
        (fun _ _ => true) hnoAccess)
  letI : IsProbabilityMeasure (lg21NormalizedRestriction rawLaw globalEvent) :=
    lg21NormalizedRestriction_isProbability rawLaw globalEvent
      (ne_of_gt hglobalPositive) (measure_ne_top _ _)
  letI : IsProbabilityMeasure localActionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure localActionLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure globalActionLaw :=
    Measure.isProbabilityMeasure_map
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature).aemeasurable
  letI : IsFiniteMeasure globalActionLaw := ⟨by simp⟩
  have hrecord : Measurable record := by
    simpa [record] using
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature)
  have hbase : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      lg21HiddenAccessStudentBase testFeature student.2) := by
    exact (lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd
  have hrecordBase : Measurable Prod.fst := measurable_fst
  have hrecordBaseEq : ∀ student,
      Prod.fst (record student) =
        lg21HiddenAccessStudentBase testFeature student.2 := by
    intro student
    rfl
  have hglobalEventMeasurable : MeasurableSet globalEvent := by
    simpa [globalEvent, lg21HiddenAccessReportRequiredCandidateNoReportEvent] using
      (lg21HiddenAccessRawCandidateNoReportEvent_measurable testFeature
        (lg21HiddenAccessConditionalMeanTailTake testFeature threshold)
        (fun _ _ => true)
        (lg21HiddenAccessConditionalMeanTailTake_measurable
          testFeature threshold (hbaseMean.add measurable_const)) measurable_const)
  have hlocalLaw : localActionLaw =
      lg21NormalizedRestriction globalActionLaw (Prod.fst ⁻¹' region) := by
    simpa [rawLaw, localLaw, globalActionLaw, localActionLaw,
      noReportEvent, globalEvent, candidate, threshold,
      lg21HiddenAccessReportRequiredCandidateNoReportEvent] using
      (lg21_normalizedLocalBaseActionLaw_eq_normalizedGlobalActionLaw rawLaw
        (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
          lg21HiddenAccessStudentBase testFeature student.2)
        record Prod.fst hbase hrecord hrecordBase hrecordBaseEq
        region hregion globalEvent hglobalEventMeasurable)
  have hglobalPBO : ∀ᵐ publicBase ∂globalActionLaw.map Prod.fst,
      lg21HiddenAccessTailCandidateNoReportValue
        (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
        (M.accessLaw {false}) (M.accessLaw {true})
        (measure_ne_top _ _) (measure_ne_top _ _) threshold publicBase =
        ∫ latentSkill, latentSkill ∂condDistrib Prod.snd Prod.fst
          globalActionLaw publicBase := by
    simpa [rawLaw, globalEvent, globalActionLaw, record, threshold,
      lg21HiddenAccessReportRequiredCandidateNoReportEvent] using
      (lg21HiddenAccessConditionalMeanTail_noReportValue_eq_condDistribMean_ae
        M hnoAccess haccess testFeature baseLaw baseMean hbaseMean
        baseVariance.toNNReal hfullBaseFactor gap
        (measure_ne_top _ _) (measure_ne_top _ _))
  have hselectedPBO := lg21_selectedObservation_condDistribMean_eq_raw_ae
    globalActionLaw Prod.fst Prod.snd
    (fun publicBase =>
      lg21HiddenAccessTailCandidateNoReportValue
        (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
        (M.accessLaw {false}) (M.accessLaw {true})
        (measure_ne_top _ _) (measure_ne_top _ _) threshold publicBase)
    measurable_fst measurable_snd hglobalPBO (Prod.fst ⁻' region)
    (hregion.preimage measurable_fst)
    (by simpa [rawLaw, globalEvent, globalActionLaw, record, threshold,
      lg21HiddenAccessReportRequiredCandidateNoReportEvent] using hglobalRegionPositive)
  unfold LG21HiddenAccessReportRequiredCandidateNoReportPBOOn
  dsimp only
  change ∀ᵐ publicBase ∂localActionLaw.map Prod.fst,
    candidate.noReportPayoff publicBase =
      ∫ skill, skill ∂condDistrib Prod.snd Prod.fst localActionLaw publicBase
  rw [hlocalLaw]
  simpa [candidate, threshold] using hselectedPBO

/-- Forgetting score in the raw Gaussian source factorization gives the
full-base latent Gaussian factorization required by the raw no-report PBO. -/
theorem lg21HiddenAccess_fullBaseLatent_eq_gaussianLocation_of_scoreFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance) :
    lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
      baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
        baseVariance.toNNReal := by
  let joint := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  have hscoreMarginal : joint.map Prod.snd =
      gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal := by
    apply Kernel.ext
    intro publicBase
    change (joint publicBase).map Prod.snd = _
    rw [lg21HiddenAccess_gaussianSignalJointKernel_skill_marginal
      baseMean hbaseMean baseVariance noiseVariance publicBase,
      gaussianLocationKernel_apply]
  calc
    lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ joint.map Prod.snd := by
          simpa [joint] using
            (lg21HiddenAccess_fullBaseLatent_eq_scoreJointSkillFactor
              M haccess testFeature baseLaw baseMean hbaseMean
              baseVariance noiseVariance hsourceFactor)
    _ = baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
          baseVariance.toNNReal := by rw [hscoreMarginal]

/-- If the incumbent has zero local current-taker mass, every positive-mass
report-required candidate report branch contains a positive mass of students
whose pre-score action actually changes. -/
theorem lg21HiddenAccessReportRequired_changedTaker_positive_of_currentTake_zero
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (currentTake candidateTake :
      ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (hcurrentZero : lg21HiddenAccessLocalRawLaw M testFeature region
      {student | student.1 = true ∧
        currentTake (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = true} = 0)
    (hcandidateReportPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessReportRequiredCandidateReportEvent testFeature candidateTake)) :
    0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessReportRequiredChangedTesterEvent testFeature
        currentTake candidateTake) := by
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
  let currentTakeEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true ∧
      currentTake (lg21ContinuousPopulationSkill student)
        (lg21HiddenAccessStudentBase testFeature student.2) = true}
  let candidateReportEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    lg21HiddenAccessReportRequiredCandidateReportEvent testFeature candidateTake
  let changedEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    lg21HiddenAccessReportRequiredChangedTesterEvent testFeature
      currentTake candidateTake
  have hcandidateReportEventEq : candidateReportEvent =
      {student | student.1 = true ∧
        candidateTake (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = true} := by
    ext student
    rcases student with ⟨access, primitive⟩
    rcases primitive with ⟨latentSkill, noise⟩
    cases access <;>
      simp [candidateReportEvent,
        lg21HiddenAccessReportRequiredCandidateReportEvent,
        lg21HiddenAccessRawCandidateReportEvent,
        lg21HiddenAccessOptionalObservedAction,
        lg21HiddenAccessStudentTake, lg21HiddenAccessStudentReport,
        lg21ContinuousPopulationSkill]
  by_contra hnotPositive
  have hchangedZero : localLaw changedEvent = 0 :=
    le_antisymm (not_lt.mp hnotPositive) (zero_le _)
  have hunionZero : localLaw (changedEvent ∪ currentTakeEvent) = 0 :=
    measure_union_null hchangedZero (by simpa [localLaw, currentTakeEvent] using hcurrentZero)
  have hsubset : candidateReportEvent ⊆ changedEvent ∪ currentTakeEvent := by
    intro student hreport
    rw [hcandidateReportEventEq] at hreport
    by_cases hcurrent : currentTake
        (lg21ContinuousPopulationSkill student)
        (lg21HiddenAccessStudentBase testFeature student.2) = false
    · left
      exact ⟨hreport.1, hcurrent, hreport.2⟩
    · right
      have hcurrentTrue : currentTake
          (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = true := by
        cases hdecision : currentTake
            (lg21ContinuousPopulationSkill student)
            (lg21HiddenAccessStudentBase testFeature student.2) <;>
          simp_all
      exact ⟨hreport.1, hcurrentTrue⟩
  have hcandidateReportZero : localLaw candidateReportEvent = 0 :=
    measure_mono_null hsubset hunionZero
  exact (ne_of_gt hcandidateReportPositive)
    (by simpa [localLaw, candidateReportEvent] using hcandidateReportZero)

/-- A measurable graph has zero mass under a nondegenerate Gaussian location
kernel.  This is the boundary-null fact used to turn the tail candidate's
weak cutoff response into strict gain almost everywhere on its changed branch. -/
theorem lg21_gaussianLocation_graph_measure_zero
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [SFinite baseLaw]
    (baseMean : Base -> ℝ) (hbaseMean : Measurable baseMean)
    (baseVariance : ℝ) (hbaseVariance : 0 < baseVariance)
    (threshold : Base -> ℝ) (hthreshold : Measurable threshold) :
    (baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
      {baseSkill | baseSkill.2 = threshold baseSkill.1} = 0 := by
  let graph : Set (Base × ℝ) :=
    {baseSkill | baseSkill.2 = threshold baseSkill.1}
  let kernel := gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal
  letI : IsMarkovKernel kernel := by
    simpa [kernel] using
      (gaussianLocationKernel_isMarkov
        baseMean hbaseMean baseVariance.toNNReal)
  have hgraph : MeasurableSet graph := by
    simpa [graph] using
      measurableSet_eq_fun measurable_snd (hthreshold.comp measurable_fst)
  have hvariance : baseVariance.toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr hbaseVariance)
  have hfiberZero : ∀ publicBase,
      kernel publicBase (Prod.mk publicBase ⁻¹' graph) = 0 := by
    intro publicBase
    have hfiber : Prod.mk publicBase ⁻¹' graph = {threshold publicBase} := by
      ext latentSkill
      simp [graph]
    rw [hfiber, gaussianLocationKernel_apply,
      gaussianReal_singleton_eq_zero (baseMean publicBase) hvariance]
  rw [Measure.compProd_apply hgraph]
  have hzero : (fun publicBase =>
      kernel publicBase (Prod.mk publicBase ⁻¹' graph)) = 0 := by
    funext publicBase
    exact hfiberZero publicBase
  rw [hzero]
  exact lintegral_zero

/-- The raw hidden-access population has the same base/skill Gaussian
factorization obtained by forgetting score from its raw base/score/skill
factorization.  This statement is about the raw law, so it is valid before
selecting either public action branch. -/
theorem lg21HiddenAccess_rawBaseSkill_eq_gaussianLocation_of_scoreFactor
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance) :
    (lg21ContinuousGaussianPopulationLaw M).map
      (lg21HiddenAccessBaseSkillObservation testFeature) =
        baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
          baseVariance.toNNReal := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let scoreSkill := lg21HiddenAccessBaseScoreSkillObservation testFeature
  let baseSkill := lg21HiddenAccessBaseSkillObservation testFeature
  let projection : ((LG21NonTestFeature Feature testFeature -> ℝ) ×
      (ℝ × ℝ)) -> (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun scoreSkill => (scoreSkill.1, scoreSkill.2.2)
  let joint := gaussianSignalJointKernel
    baseMean hbaseMean baseVariance noiseVariance
  letI : IsMarkovKernel joint := by
    simpa [joint] using
      (gaussianSignalJointKernel_isMarkov
        baseMean hbaseMean baseVariance noiseVariance)
  have hscoreSkill : Measurable scoreSkill := by
    simpa [scoreSkill] using
      (lg21HiddenAccessBaseScoreSkillObservation_measurable testFeature)
  have hprojection : Measurable projection := by
    dsimp [projection]
    fun_prop
  have hjointMarginal : joint.map Prod.snd =
      gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal := by
    apply Kernel.ext
    intro publicBase
    change (joint publicBase).map Prod.snd = _
    rw [lg21HiddenAccess_gaussianSignalJointKernel_skill_marginal
      baseMean hbaseMean baseVariance noiseVariance publicBase,
      gaussianLocationKernel_apply]
  calc
    rawLaw.map baseSkill = (rawLaw.map scoreSkill).map projection := by
      rw [Measure.map_map hprojection hscoreSkill]
      rfl
    _ = (baseLaw ⊗ₘ joint).map projection := by
      rw [show rawLaw.map scoreSkill = baseLaw ⊗ₘ joint by
        simpa [rawLaw, scoreSkill, joint] using hsourceFactor]
    _ = baseLaw ⊗ₘ joint.map Prod.snd := by
      simpa [projection, joint] using
        (map_compProd_eq_compProd_map measurable_snd
          (μ := baseLaw) (κ := joint))
    _ = baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
          baseVariance.toNNReal := by rw [hjointMarginal]

/-- Away from its null cutoff boundary, a report-required latent-tail
candidate gives every taking type a strict ex-ante gain at a literal raw
mixture root. -/
theorem lg21HiddenAccessReportRequiredLocalTail_strictGain_of_take_off_boundary
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {testFeature : Feature}
    (baseMean threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance) (hnoiseVariance : 0 < noiseVariance)
    (noAccessMass accessMass : ENNReal)
    (hnoAccessFinite : noAccessMass ≠ ⊤)
    (haccessFinite : accessMass ≠ ⊤)
    (hroot : ∀ publicBase,
      lg21SelectedGaussianCutoffBoundaryPayoff
        (baseMean publicBase) baseVariance noiseVariance
        (threshold publicBase) =
      lg21HiddenAccessTailCandidateNoReportValue
        (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
        noAccessMass accessMass hnoAccessFinite haccessFinite threshold publicBase)
    (latentSkill : ℝ)
    (publicBase : LG21NonTestFeature Feature testFeature -> ℝ)
    (htake :
      (lg21HiddenAccessReportRequiredLocalTailCandidate
        baseMean threshold hbaseMean baseVariance noiseVariance
        hbaseVariance hnoiseVariance noAccessMass accessMass
        hnoAccessFinite haccessFinite).takeDecision latentSkill publicBase = true)
    (hboundary : latentSkill ≠ threshold publicBase) :
    (lg21HiddenAccessReportRequiredLocalTailCandidate
      baseMean threshold hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance noAccessMass accessMass
      hnoAccessFinite haccessFinite).noReportPayoff publicBase <
      lg21ReportRequiredCandidateTakeExpectedPayoff
        (lg21HiddenAccessReportRequiredLocalTailCandidate
          baseMean threshold hbaseMean baseVariance noiseVariance
          hbaseVariance hnoiseVariance noAccessMass accessMass
          hnoAccessFinite haccessFinite)
        latentSkill publicBase := by
  let candidate := lg21HiddenAccessReportRequiredLocalTailCandidate
    baseMean threshold hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance noAccessMass accessMass
    hnoAccessFinite haccessFinite
  have hcutoff : threshold publicBase ≤ latentSkill := by
    exact (lg21HiddenAccessReportRequiredLocalTailCandidate_take_eq_true_iff
      baseMean threshold hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance noAccessMass accessMass
      hnoAccessFinite haccessFinite latentSkill publicBase).1 htake
  have hstrictCutoff : threshold publicBase < latentSkill := by
    exact lt_of_le_of_ne hcutoff (Ne.symm hboundary)
  have hstrict : StrictMono (fun skill =>
      lg21ReportRequiredCandidateTakeExpectedPayoff candidate skill publicBase) := by
    simpa [candidate, lg21ReportRequiredCandidateTakeExpectedPayoff,
      lg21HiddenAccessReportRequiredLocalTailCandidate] using
      (lg21ReportRequiredSelectedUpperTailCandidate_takeExpectedPayoff_strictMono
        baseMean threshold
        (fun base =>
          lg21HiddenAccessTailCandidateNoReportValue
            (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
            noAccessMass accessMass hnoAccessFinite haccessFinite threshold base)
        baseVariance noiseVariance hbaseVariance hnoiseVariance publicBase)
  have hcutoffValue :
      lg21ReportRequiredCandidateTakeExpectedPayoff candidate
        (threshold publicBase) publicBase =
        candidate.noReportPayoff publicBase := by
    calc
      lg21ReportRequiredCandidateTakeExpectedPayoff candidate
          (threshold publicBase) publicBase =
          lg21SelectedGaussianCutoffBoundaryPayoff
            (baseMean publicBase) baseVariance noiseVariance
            (threshold publicBase) := by
              simpa [candidate, lg21ReportRequiredCandidateTakeExpectedPayoff,
                lg21HiddenAccessReportRequiredLocalTailCandidate] using
                (lg21ReportRequiredSelectedUpperTailCandidate_takeExpectedPayoff_at_cutoff_eq_boundary
                  baseMean threshold
                  (fun base =>
                    lg21HiddenAccessTailCandidateNoReportValue
                      (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
                      noAccessMass accessMass hnoAccessFinite haccessFinite threshold base)
                  baseVariance noiseVariance hbaseVariance hnoiseVariance publicBase)
      _ = candidate.noReportPayoff publicBase := by
        simpa [candidate, lg21HiddenAccessReportRequiredLocalTailCandidate] using
          hroot publicBase
  calc
    candidate.noReportPayoff publicBase =
        lg21ReportRequiredCandidateTakeExpectedPayoff candidate
          (threshold publicBase) publicBase := hcutoffValue.symm
    _ < lg21ReportRequiredCandidateTakeExpectedPayoff candidate
          latentSkill publicBase := hstrict hstrictCutoff

/-- The only non-strict point of the report-required tail candidate is its
base-dependent cutoff graph, which has zero Gaussian mass.  Thus strict
pre-score gain holds almost everywhere on any changed local tail branch. -/
theorem lg21HiddenAccessReportRequiredLocalTail_changedTaker_strictGain_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (currentTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (hcurrentTake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) => currentTake pair.1 pair.2))
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (baseVariance noiseVariance : ℝ)
    (hbaseVariance : 0 < baseVariance) (hnoiseVariance : 0 < noiseVariance)
    (gap : ℝ)
    (hsourceFactor :
      (lg21ContinuousGaussianPopulationLaw M).map
        (lg21HiddenAccessBaseScoreSkillObservation testFeature) =
          baseLaw ⊗ₘ gaussianSignalJointKernel
            baseMean hbaseMean baseVariance noiseVariance)
    (hroot : ∀ publicBase,
      lg21SelectedGaussianCutoffBoundaryPayoff
        (baseMean publicBase) baseVariance noiseVariance
        (baseMean publicBase + gap) =
      lg21HiddenAccessTailCandidateNoReportValue
        (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
        (M.accessLaw {false}) (M.accessLaw {true})
        (measure_ne_top _ _) (measure_ne_top _ _)
        (fun publicBase => baseMean publicBase + gap) publicBase) :
    ∀ᵐ student ∂
      (lg21HiddenAccessLocalRawLaw M testFeature region).restrict
        (lg21HiddenAccessReportRequiredChangedTesterEvent testFeature currentTake
          (lg21HiddenAccessReportRequiredLocalTailCandidate
            baseMean (fun publicBase => baseMean publicBase + gap) hbaseMean
            baseVariance noiseVariance hbaseVariance hnoiseVariance
            (M.accessLaw {false}) (M.accessLaw {true})
            (measure_ne_top _ _) (measure_ne_top _ _)).takeDecision),
      (lg21HiddenAccessReportRequiredLocalTailCandidate
        baseMean (fun publicBase => baseMean publicBase + gap) hbaseMean
        baseVariance noiseVariance hbaseVariance hnoiseVariance
        (M.accessLaw {false}) (M.accessLaw {true})
        (measure_ne_top _ _) (measure_ne_top _ _)).noReportPayoff
          (lg21HiddenAccessStudentBase testFeature student.2) <
        lg21ReportRequiredCandidateTakeExpectedPayoff
          (lg21HiddenAccessReportRequiredLocalTailCandidate
            baseMean (fun publicBase => baseMean publicBase + gap) hbaseMean
            baseVariance noiseVariance hbaseVariance hnoiseVariance
            (M.accessLaw {false}) (M.accessLaw {true})
            (measure_ne_top _ _) (measure_ne_top _ _))
          (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) := by
  let threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ :=
    fun publicBase => baseMean publicBase + gap
  let candidate := lg21HiddenAccessReportRequiredLocalTailCandidate
    baseMean threshold hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance (M.accessLaw {false}) (M.accessLaw {true})
    (measure_ne_top _ _) (measure_ne_top _ _)
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let localLaw := lg21HiddenAccessLocalRawLaw M testFeature region
  let baseSkill := lg21HiddenAccessBaseSkillObservation testFeature
  let graph : Set ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) :=
    {baseSkill | baseSkill.2 = threshold baseSkill.1}
  let boundaryEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    baseSkill ⁻¹' graph
  let changedEvent := lg21HiddenAccessReportRequiredChangedTesterEvent
    testFeature currentTake candidate.takeDecision
  have hthreshold : Measurable threshold := hbaseMean.add measurable_const
  have hbaseSkill : Measurable baseSkill := by
    simpa [baseSkill] using
      (lg21HiddenAccessBaseSkillObservation_measurable testFeature)
  have hgraph : MeasurableSet graph := by
    simpa [graph] using
      measurableSet_eq_fun measurable_snd (hthreshold.comp measurable_fst)
  have hboundaryEvent : MeasurableSet boundaryEvent :=
    hgraph.preimage hbaseSkill
  have hrawBaseSkillFactor : rawLaw.map baseSkill =
      baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
        baseVariance.toNNReal := by
    simpa [rawLaw, baseSkill] using
      (lg21HiddenAccess_rawBaseSkill_eq_gaussianLocation_of_scoreFactor
        M testFeature baseLaw baseMean hbaseMean baseVariance noiseVariance
        hsourceFactor)
  have hrawBoundary : rawLaw boundaryEvent = 0 := by
    calc
      rawLaw boundaryEvent = rawLaw.map baseSkill graph := by
        symm
        exact Measure.map_apply hbaseSkill hgraph
      _ = (baseLaw ⊗ₘ gaussianLocationKernel
          baseMean hbaseMean baseVariance.toNNReal) graph := by
            rw [hrawBaseSkillFactor]
      _ = 0 := lg21_gaussianLocation_graph_measure_zero
        baseLaw baseMean hbaseMean baseVariance hbaseVariance threshold hthreshold
  have hboundaryLocal : localLaw boundaryEvent = 0 := by
    change (lg21NormalizedRestriction rawLaw
      (lg21HiddenAccessBaseRegionEvent testFeature region)) boundaryEvent = 0
    rw [lg21NormalizedRestriction_apply rawLaw hboundaryEvent]
    have hintersectionZero : rawLaw
        (boundaryEvent ∩ lg21HiddenAccessBaseRegionEvent testFeature region) = 0 :=
      measure_mono_null inter_subset_left hrawBoundary
    rw [hintersectionZero]
    simp
  have hbase : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      lg21HiddenAccessStudentBase testFeature student.2) :=
    (lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd
  have hskill : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      lg21ContinuousPopulationSkill student) := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have htailTake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      candidate.takeDecision pair.1 pair.2) := by
    simpa [candidate, threshold] using
      (lg21HiddenAccessConditionalMeanTailTake_measurable
        testFeature threshold hthreshold)
  have hcurrentRaw : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      currentTake (lg21ContinuousPopulationSkill student)
        (lg21HiddenAccessStudentBase testFeature student.2)) :=
    hcurrentTake.comp (hskill.prodMk hbase)
  have htailRaw : Measurable (fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      candidate.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21HiddenAccessStudentBase testFeature student.2)) :=
    htailTake.comp (hskill.prodMk hbase)
  have hchangedEvent : MeasurableSet changedEvent := by
    change MeasurableSet ({student : Bool × (ℝ × (Feature -> ℝ)) |
      student.1 = true} ∩
        {student | currentTake (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = false} ∩
        {student | candidate.takeDecision (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = true})
    exact ((measurableSet_singleton true).preimage measurable_fst).inter
      (((measurableSet_singleton false).preimage hcurrentRaw).inter
        ((measurableSet_singleton true).preimage htailRaw))
  have hboundaryChanged : (localLaw.restrict changedEvent) boundaryEvent = 0 := by
    rw [Measure.restrict_apply hboundaryEvent]
    exact measure_mono_null inter_subset_left hboundaryLocal
  have hnotBoundary : ∀ᵐ student ∂localLaw.restrict changedEvent,
      student ∉ boundaryEvent := by
    rw [ae_iff]
    simpa using hboundaryChanged
  have hchangedMember : ∀ᵐ student ∂localLaw.restrict changedEvent,
      student ∈ changedEvent := ae_restrict_mem hchangedEvent
  filter_upwards [hnotBoundary, hchangedMember] with student hnotBoundary hchanged
  have htake : candidate.takeDecision (lg21ContinuousPopulationSkill student)
      (lg21HiddenAccessStudentBase testFeature student.2) = true := hchanged.2.2
  have hnotEqual : lg21ContinuousPopulationSkill student ≠
      threshold (lg21HiddenAccessStudentBase testFeature student.2) := by
    intro heq
    apply hnotBoundary
    change lg21ContinuousPopulationSkill student =
      threshold (lg21HiddenAccessStudentBase testFeature student.2)
    exact heq
  simpa [candidate, threshold] using
    (lg21HiddenAccessReportRequiredLocalTail_strictGain_of_take_off_boundary
      baseMean threshold hbaseMean baseVariance noiseVariance
      hbaseVariance hnoiseVariance (M.accessLaw {false}) (M.accessLaw {true})
      (measure_ne_top _ _) (measure_ne_top _ _)
      (by simpa [threshold] using hroot)
      (lg21ContinuousPopulationSkill student)
      (lg21HiddenAccessStudentBase testFeature student.2) htake hnotEqual)

/-- A positive public-base region on which the incumbent has no current
testers admits a literal report-required hidden-access local entry.  The
candidate's only strategic action is its pre-score upper-tail test decision;
its report and no-report PBOs are both conditioned on the candidate's actual
raw action branches.  In particular, the latter retains the no-access mass.

This is deliberately a *local* entry certificate, not a claim that the
candidate completes an equilibrium outside the changed region. -/
theorem lg21HiddenAccessReportRequiredLocalCandidateEntry_of_zeroCurrentTakeRegion
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (hnoAccess : 0 < M.accessLaw {false})
    (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (currentTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (hcurrentTake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) => currentTake pair.1 pair.2))
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (hcurrentTakeZero : lg21HiddenAccessLocalRawLaw M testFeature region
      {student | student.1 = true ∧
        currentTake (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = true} = 0) :
    LG21HiddenAccessReportRequiredLocalCandidateEntry
      (M := M) (testFeature := testFeature) currentTake := by
  classical
  rcases
      lg21ContinuousGaussianPopulation_exists_fullBaseGaussian_scoreSkill_factorization
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
          htestNoiseVariance with
    ⟨baseLaw, baseMean, baseVariance, hbaseMean,
      hbaseLaw, hbaseVariance, hsourceFactor⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  let noiseVariance : ℝ := (M.noiseVariance testFeature : ℝ)
  have hnoiseVariance : 0 < noiseVariance := by
    simpa [noiseVariance] using htestNoiseVariance
  have hbaseVarianceNN : baseVariance.toNNReal ≠ 0 :=
    ne_of_gt (Real.toNNReal_pos.mpr hbaseVariance)
  letI : IsMarkovKernel
      (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal) :=
    gaussianLocationKernel_isMarkov baseMean hbaseMean baseVariance.toNNReal
  have hnoAccessFinite : M.accessLaw {false} ≠ ⊤ := measure_ne_top _ _
  have haccessFinite : M.accessLaw {true} ≠ ⊤ := measure_ne_top _ _
  obtain ⟨gap, hroot⟩ :=
    lg21ReportRequiredHiddenAccessMixture_exists_uniform_raw_root
      baseMean hbaseMean baseVariance.toNNReal hbaseVarianceNN
      (M.accessLaw {false}) (M.accessLaw {true}) hnoAccess haccess
      hnoAccessFinite haccessFinite noiseVariance hnoiseVariance
  let threshold : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ :=
    fun publicBase => baseMean publicBase + gap
  have hthreshold : Measurable threshold := hbaseMean.add measurable_const
  have hroot' : ∀ publicBase,
      lg21SelectedGaussianCutoffBoundaryPayoff
        (baseMean publicBase) baseVariance noiseVariance
        (threshold publicBase) =
      lg21HiddenAccessTailCandidateNoReportValue
        (gaussianLocationKernel baseMean hbaseMean baseVariance.toNNReal)
        (M.accessLaw {false}) (M.accessLaw {true})
        hnoAccessFinite haccessFinite threshold publicBase := by
    intro publicBase
    simpa [threshold, noiseVariance,
      Real.coe_toNNReal _ hbaseVariance.le] using hroot publicBase
  let candidate := lg21HiddenAccessReportRequiredLocalTailCandidate
    baseMean threshold hbaseMean baseVariance noiseVariance
    hbaseVariance hnoiseVariance (M.accessLaw {false}) (M.accessLaw {true})
    hnoAccessFinite haccessFinite
  have hcandidateTakeMeasurable : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) =>
      candidate.takeDecision pair.1 pair.2) := by
    simpa [candidate, lg21HiddenAccessReportRequiredLocalTailCandidate] using
      (lg21HiddenAccessConditionalMeanTailTake_measurable
        testFeature threshold hthreshold)
  have hreportBranches :=
    lg21HiddenAccessReportRequiredLocalTail_report_and_globalRegion_positive
      (M := M) region hregion hregionPositive haccess baseLaw baseMean hbaseMean
      baseVariance noiseVariance hbaseVariance hnoiseVariance threshold hthreshold
      hsourceFactor
  have hreportPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessReportRequiredCandidateReportEvent testFeature
        candidate.takeDecision) := by
    simpa [candidate, lg21HiddenAccessReportRequiredLocalTailCandidate] using
      hreportBranches.1
  have hnoReportBranches :=
    lg21HiddenAccessReportRequiredLocalTail_noReport_and_globalRegion_positive
      (M := M) region hregion hregionPositive hnoAccess threshold hthreshold
  have hnoReportPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessReportRequiredCandidateNoReportEvent testFeature
        candidate.takeDecision) := by
    simpa [candidate, lg21HiddenAccessReportRequiredLocalTailCandidate] using
      hnoReportBranches.1
  have hreportPBO : LG21HiddenAccessReportRequiredCandidateReportPBOOn
      M testFeature region hregionPositive candidate hreportPositive := by
    simpa [candidate, lg21HiddenAccessReportRequiredLocalTailCandidate] using
      (lg21HiddenAccessReportRequiredLocalTail_reportPBO_of_global
        (M := M) region hregion hregionPositive haccess baseLaw baseMean threshold
        hbaseMean baseVariance noiseVariance hbaseVariance hnoiseVariance hthreshold
        hsourceFactor hreportBranches.1 hreportBranches.2
        (M.accessLaw {false}) (M.accessLaw {true}) hnoAccessFinite haccessFinite)
  have hfullBaseFactor :
      lg21ContinuousGaussianFullBaseLatentPrimitiveLaw M testFeature =
        baseLaw ⊗ₘ gaussianLocationKernel baseMean hbaseMean
          baseVariance.toNNReal :=
    lg21HiddenAccess_fullBaseLatent_eq_gaussianLocation_of_scoreFactor
      M haccess testFeature baseLaw baseMean hbaseMean baseVariance noiseVariance
      hsourceFactor
  have hnoReportPBO : LG21HiddenAccessReportRequiredCandidateNoReportPBOOn
      M testFeature region hregionPositive candidate hnoReportPositive := by
    simpa [candidate, lg21HiddenAccessReportRequiredLocalTailCandidate] using
      (lg21HiddenAccessReportRequiredLocalTail_noReportPBO_of_global
        (M := M) region hregion hregionPositive baseLaw baseMean hbaseMean
        baseVariance noiseVariance hbaseVariance hnoiseVariance gap hnoAccess haccess
        hfullBaseFactor hnoReportBranches.1 hnoReportBranches.2)
  have hchangedPositive : 0 < lg21HiddenAccessLocalRawLaw M testFeature region
      (lg21HiddenAccessReportRequiredChangedTesterEvent testFeature currentTake
        candidate.takeDecision) :=
    lg21HiddenAccessReportRequired_changedTaker_positive_of_currentTake_zero
      region currentTake candidate.takeDecision hcurrentTakeZero hreportPositive
  have hstrictGain : ∀ᵐ student ∂
      (lg21HiddenAccessLocalRawLaw M testFeature region).restrict
        (lg21HiddenAccessReportRequiredChangedTesterEvent testFeature currentTake
          candidate.takeDecision),
      candidate.noReportPayoff (lg21HiddenAccessStudentBase testFeature student.2) <
        lg21ReportRequiredCandidateTakeExpectedPayoff candidate
          (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) := by
    simpa [candidate, threshold] using
      (lg21HiddenAccessReportRequiredLocalTail_changedTaker_strictGain_ae
        region hregion hregionPositive currentTake hcurrentTake baseLaw baseMean hbaseMean
        baseVariance noiseVariance hbaseVariance hnoiseVariance gap hsourceFactor hroot')
  exact
    { region := region
      region_measurable := hregion
      region_positive := hregionPositive
      current_take_measurable := hcurrentTake
      current_take_zero := hcurrentTakeZero
      candidate := candidate
      candidate_take_measurable := hcandidateTakeMeasurable
      candidate_changed_taker_positive := hchangedPositive
      candidate_report_positive := hreportPositive
      candidate_noReport_positive := hnoReportPositive
      candidate_report_pbo := hreportPBO
      candidate_noReport_pbo := hnoReportPBO
      candidate_changed_tester_strict_gain := hstrictGain }

/-- Consequently, a current report-required action with such a zero-taker
positive base region is not stable against literal raw-PBO local entries. -/
theorem lg21HiddenAccessReportRequired_not_stable_of_zeroCurrentTakeRegion
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (hnoAccess : 0 < M.accessLaw {false})
    (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (currentTake : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (hcurrentTake : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) => currentTake pair.1 pair.2))
    (region : Set (LG21NonTestFeature Feature testFeature -> ℝ))
    (hregion : MeasurableSet region)
    (hregionPositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessBaseRegionEvent testFeature region))
    (hcurrentTakeZero : lg21HiddenAccessLocalRawLaw M testFeature region
      {student | student.1 = true ∧
        currentTake (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = true} = 0) :
    ¬ LG21HiddenAccessReportRequiredStableAgainstLocalCandidateEntry
      (M := M) (testFeature := testFeature) currentTake := by
  exact lg21HiddenAccessReportRequired_not_stable_of_localCandidateEntry
    currentTake
    (lg21HiddenAccessReportRequiredLocalCandidateEntry_of_zeroCurrentTakeRegion
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance currentTake hcurrentTake region hregion hregionPositive
      hcurrentTakeZero)

end

end LG21TestOptionalPolicies
