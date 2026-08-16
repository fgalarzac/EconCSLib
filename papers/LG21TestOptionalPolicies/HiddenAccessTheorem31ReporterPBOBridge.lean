import LG21TestOptionalPolicies.HiddenAccessTheorem31PopulationMassTransport
import LG21TestOptionalPolicies.SelectedObservationConditionalInvariance

/-!
# On-path public-PBO bridge for LG21 Theorem 3.1

The literal Section 3 PBO is a conditional expectation under the full
population and the complete tagged public record.  A reporter reaches a
positive-mass public event; on that event the PBO must be recalibrated from
the actual population, rather than read from an arbitrary version on a null
history.

This module first performs that restriction at the conditional-distribution
level.  The result is deliberately source-neutral: it says that a literal
public PBO agrees, almost everywhere on any attained public event, with the
conditional mean under the normalized attained population.  The subsequent
LG21-specific result instantiates the event ``a score is publicly reported''.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-! ## Generic public-event restriction -/

/--
Successively normalizing a finite population on two measurable events is
normalization on their intersection.  This is the measure-level chronology
needed when a pre-score action selects a latent population and a later action
selects an event determined by the resulting public observation.
-/
theorem lg21_normalizedRestriction_normalizedRestriction_eq_inter
    {Omega : Type*} [MeasurableSpace Omega]
    (law : Measure Omega) [IsFiniteMeasure law]
    (first second : Set Omega)
    (hfirst : MeasurableSet first) (hsecond : MeasurableSet second) :
    lg21NormalizedRestriction (lg21NormalizedRestriction law first) second =
      lg21NormalizedRestriction law (first ∩ second) := by
  simpa only [lg21NormalizedRestriction, ProbabilityTheory.cond] using
    (cond_cond_eq_cond_inter hfirst hsecond law)

/-- A positive intersection stays positive after normalizing on its first
measurable component. -/
theorem lg21_normalizedRestriction_pos_of_inter_pos
    {Omega : Type*} [MeasurableSpace Omega]
    (law : Measure Omega) [IsFiniteMeasure law]
    (first second : Set Omega) (hfirst : MeasurableSet first)
    (hpositive : 0 < law (first ∩ second)) :
    0 < lg21NormalizedRestriction law first second := by
  simpa only [lg21NormalizedRestriction, ProbabilityTheory.cond] using
    (cond_pos_of_inter_ne_zero (μ := law) (s := first) (t := second)
      hfirst (ne_of_gt hpositive))

/--
Restricting a literal conditional-expectation PBO to a positive event that is
measurable in its public observation preserves its conditional mean.  Both
the PBO and the regular conditional distribution remain a.e. objects; no
value is assigned to an unreached public observation.
-/
theorem lg21_publicPBO_condDistrib_on_positive_publicEvent_ae
    {Omega Public : Type*} [MeasurableSpace Omega] [MeasurableSpace Public]
    [StandardBorelSpace Omega]
    (rawLaw : Measure Omega) [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    (publicObservation : Omega -> Public) (skill payoff : Omega -> ℝ)
    (hpublicObservation : Measurable publicObservation) (hskill : Measurable skill)
    (hskillIntegrable : Integrable skill rawLaw)
    (hpublicPBO : payoff =ᵐ[rawLaw]
      rawLaw[skill | MeasurableSpace.comap publicObservation inferInstance])
    (selected : Set Public) (hselected : MeasurableSet selected)
    (hpositive : 0 < rawLaw (publicObservation ⁻¹' selected)) :
    let selectedLaw := lg21NormalizedRestriction rawLaw (publicObservation ⁻¹' selected)
    letI : IsProbabilityMeasure selectedLaw :=
      lg21NormalizedRestriction_isProbability rawLaw (publicObservation ⁻¹' selected)
        (ne_of_gt hpositive) (measure_ne_top _ _)
    letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
    payoff =ᵐ[selectedLaw]
      fun omega => ∫ latentSkill, latentSkill ∂
        condDistrib skill publicObservation selectedLaw (publicObservation omega) := by
  intro selectedLaw
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability rawLaw (publicObservation ⁻¹' selected)
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  have hrawMean : payoff =ᵐ[rawLaw]
      fun omega => ∫ latentSkill, latentSkill ∂
        condDistrib skill publicObservation rawLaw (publicObservation omega) := by
    exact hpublicPBO.trans
      (condExp_ae_eq_integral_condDistrib' hpublicObservation hskillIntegrable)
  have hrawMeanSelected : payoff =ᵐ[selectedLaw]
      fun omega => ∫ latentSkill, latentSkill ∂
        condDistrib skill publicObservation rawLaw (publicObservation omega) := by
    change payoff =ᵐ[(rawLaw (publicObservation ⁻¹' selected))⁻¹ •
        rawLaw.restrict (publicObservation ⁻¹' selected)] _
    exact Measure.ae_smul_measure (ae_restrict_of_ae hrawMean) _
  have hinvariant :
      condDistrib skill publicObservation selectedLaw =ᵐ[selectedLaw.map publicObservation]
        condDistrib skill publicObservation rawLaw := by
    exact lg21_selectedObservation_condDistrib_latent_eq_raw_ae
      rawLaw publicObservation skill hpublicObservation hskill selected hselected hpositive
  have hinvariantPullback : ∀ᵐ omega ∂selectedLaw,
      condDistrib skill publicObservation selectedLaw (publicObservation omega) =
        condDistrib skill publicObservation rawLaw (publicObservation omega) := by
    exact ae_of_ae_map hpublicObservation.aemeasurable hinvariant
  filter_upwards [hrawMeanSelected, hinvariantPullback] with omega hmean hinvariantAt
  rw [hmean, hinvariantAt]

/-! ## Conditional-law transport through an attained record embedding -/

/-- Pushing the observed coordinate of a joint law through an embedding and
then decoding it inside the conditional kernel leaves the joint law
unchanged.  The retraction is only required on the embedded range, which is
the precise information relation used by a tagged reporter record. -/
theorem lg21_compProd_map_left_embedding
    {Base Public Latent : Type*}
    [MeasurableSpace Base] [MeasurableSpace Public] [MeasurableSpace Latent]
    (baseLaw : Measure Base) [SFinite baseLaw]
    (kernel : Kernel Base Latent) [IsSFiniteKernel kernel]
    (embed : Base -> Public) (decode : Public -> Base)
    (hembed : Measurable embed) (hdecode : Measurable decode)
    (hdecodeEmbed : ∀ base, decode (embed base) = base) :
    (baseLaw.map embed) ⊗ₘ (kernel.comap decode hdecode) =
      (baseLaw ⊗ₘ kernel).map (Prod.map embed id) := by
  ext target htarget
  have hleftIntegrand : Measurable fun publicRecord : Public =>
      (kernel.comap decode hdecode) publicRecord
        (Prod.mk publicRecord ⁻¹' target) := by
    exact Kernel.measurable_kernel_prodMk_left htarget
  have htargetPreimage : MeasurableSet ((Prod.map embed id) ⁻¹' target) := by
    exact htarget.preimage (hembed.prodMap measurable_id)
  rw [Measure.compProd_apply htarget,
    lintegral_map hleftIntegrand hembed,
    Measure.map_apply (hembed.prodMap measurable_id) htarget,
    Measure.compProd_apply htargetPreimage]
  congr with base
  rw [Kernel.comap_apply]
  congr 1
  ext latent
  simp [hdecodeEmbed]

/--
If an attained public record is almost everywhere an injective encoding of an
observation, its conditional latent law is the original observation's
conditional kernel composed with the record decoder.  This theorem works at
the level of joint laws and is therefore independent of strategy or function
names.
-/
theorem lg21_condDistrib_recordEmbedding_eq_observationKernel_ae
    {Omega Base Public : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Base] [MeasurableSpace Public]
    (law : Measure Omega) [IsProbabilityMeasure law] [IsFiniteMeasure law]
    (observation : Omega -> Base) (record : Omega -> Public) (skill : Omega -> ℝ)
    (hobservation : Measurable observation) (hrecord : Measurable record)
    (hskill : Measurable skill)
    (embed : Base -> Public) (decode : Public -> Base)
    (hembed : Measurable embed) (hdecode : Measurable decode)
    (hdecodeEmbed : ∀ base, decode (embed base) = base)
    (hrecordEmbedding : record =ᵐ[law] embed ∘ observation)
    (posterior : Kernel Base ℝ) [IsFiniteKernel posterior]
    (hfactor : law.map (fun omega => (observation omega, skill omega)) =
      law.map observation ⊗ₘ posterior) :
    condDistrib skill record law =ᵐ[law.map record]
      posterior.comap decode hdecode := by
  have hpairEmbedding :
      (fun omega => (record omega, skill omega)) =ᵐ[law]
        (Prod.map embed id ∘ fun omega => (observation omega, skill omega)) := by
    filter_upwards [hrecordEmbedding] with omega hrecordAt
    simp [hrecordAt]
  have hrecordMarginal : law.map record = (law.map observation).map embed := by
    calc
      law.map record = law.map (embed ∘ observation) := by
        exact Measure.map_congr hrecordEmbedding
      _ = (law.map observation).map embed := by
        rw [Measure.map_map hembed hobservation]
  have hpair : law.map (fun omega => (record omega, skill omega)) =
      law.map record ⊗ₘ posterior.comap decode hdecode := by
    calc
      law.map (fun omega => (record omega, skill omega)) =
          law.map (Prod.map embed id ∘ fun omega =>
            (observation omega, skill omega)) := by
            exact Measure.map_congr hpairEmbedding
      _ = (law.map (fun omega => (observation omega, skill omega))).map
          (Prod.map embed id) := by
            rw [Measure.map_map (hembed.prodMap measurable_id)
              (hobservation.prodMk hskill)]
      _ = (law.map observation ⊗ₘ posterior).map (Prod.map embed id) := by
            rw [hfactor]
      _ = (law.map observation).map embed ⊗ₘ posterior.comap decode hdecode := by
            symm
            exact lg21_compProd_map_left_embedding
              (law.map observation) posterior embed decode hembed hdecode hdecodeEmbed
      _ = law.map record ⊗ₘ posterior.comap decode hdecode := by
            rw [hrecordMarginal]
  exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    hrecord hskill hpair

/-! ## Literal reporter event -/

/-- The public-record values that explicitly contain a reported test score. -/
def lg21HiddenAccessPublicReporterSet
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Set ((LG21NonTestFeature Feature testFeature -> ℝ) × (Bool × ℝ)) :=
  {record | record.2.1 = true}

theorem lg21HiddenAccessPublicReporterSet_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    MeasurableSet (lg21HiddenAccessPublicReporterSet (Feature := Feature) testFeature) := by
  change MeasurableSet
    ((fun record : (LG21NonTestFeature Feature testFeature -> ℝ) × (Bool × ℝ) =>
      record.2.1) ⁻¹' ({true} : Set Bool))
  exact (measurableSet_singleton true).preimage
    (measurable_fst.comp measurable_snd)

/-- The actual literal population event on which a score is reported. -/
def lg21HiddenAccessOptionalReportEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (takeDecision : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool) :
    Set (Bool × (ℝ × (Feature -> ℝ))) :=
  {student | lg21HiddenAccessOptionalObservedAction
    testFeature takeDecision reportDecision student = true}

/-- The pre-score source event on which an access student takes the test. -/
def lg21HiddenAccessTakerEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (takeDecision : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool) :
    Set (Bool × (ℝ × (Feature -> ℝ))) :=
  {student | lg21HiddenAccessStudentTake testFeature takeDecision student.2 = true}

/-- The post-score report action, represented directly on the observable
`(base, score)` carrier. -/
def lg21HiddenAccessReportSet
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool) :
    Set ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) :=
  {profile | reportDecision profile.1 profile.2 = true}

theorem lg21HiddenAccessTakerEvent_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (takeDecision : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (htakeDecision : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) => takeDecision pair.1 pair.2)) :
    MeasurableSet (lg21HiddenAccessTakerEvent testFeature takeDecision) := by
  change MeasurableSet
    ((fun student : Bool × (ℝ × (Feature -> ℝ)) =>
      lg21HiddenAccessStudentTake testFeature takeDecision student.2) ⁻¹'
      ({true} : Set Bool))
  exact (measurableSet_singleton true).preimage
    ((lg21HiddenAccessStudentTake_measurable testFeature takeDecision htakeDecision).comp
      measurable_snd)

theorem lg21HiddenAccessReportSet_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool)
    (hreportDecision : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      reportDecision pair.1 pair.2)) :
    MeasurableSet (lg21HiddenAccessReportSet testFeature reportDecision) := by
  change MeasurableSet
    ((fun profile : (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      reportDecision profile.1 profile.2) ⁻¹' ({true} : Set Bool))
  exact (measurableSet_singleton true).preimage hreportDecision

/-- A report decision is a measurable selection on `(base, score)`, even
though the preceding taking decision may depend on latent skill. -/
theorem lg21HiddenAccessReportEvent_eq_baseScore_preimage
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool) :
    {student : Bool × (ℝ × (Feature -> ℝ)) |
      lg21HiddenAccessStudentReport testFeature reportDecision student.2 = true} =
      (fun student => (lg21HiddenAccessStudentBase testFeature student.2,
        lg21HiddenAccessStudentScore testFeature student.2)) ⁻¹'
        lg21HiddenAccessReportSet testFeature reportDecision := by
  rfl

/-- The literal actual reporter population has precisely the source timing:
access, then a latent pre-score take action, then a public `(base, score)`
report action. -/
theorem lg21HiddenAccessOptionalReportEvent_eq_access_inter_taker_inter_report
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (takeDecision : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool) :
    lg21HiddenAccessOptionalReportEvent testFeature takeDecision reportDecision =
      {student : Bool × (ℝ × (Feature -> ℝ)) | student.1 = true} ∩
        lg21HiddenAccessTakerEvent testFeature takeDecision ∩
          (fun student => (lg21HiddenAccessStudentBase testFeature student.2,
            lg21HiddenAccessStudentScore testFeature student.2)) ⁻¹'
            lg21HiddenAccessReportSet testFeature reportDecision := by
  ext student
  rcases student with ⟨access, primitive⟩
  cases haccess : access <;>
    cases htake : lg21HiddenAccessStudentTake testFeature takeDecision primitive <;>
    cases hreport : lg21HiddenAccessStudentReport testFeature reportDecision primitive <;>
    simp [lg21HiddenAccessOptionalReportEvent,
      lg21HiddenAccessOptionalObservedAction,
      lg21HiddenAccessTakerEvent,
      lg21HiddenAccessReportSet,
      lg21HiddenAccessStudentReport,
      htake]

/-- The normalized law of literal actual reporters is exactly obtained by
first conditioning on access, then on the source-timed taking action, and
finally on the report event that is measurable in the observable
`(base, score)` record.  This is an equality of population laws, not an
identification of a PBO on an unreached history. -/
theorem lg21HiddenAccess_reporterLaw_eq_accessTakerReportLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature) :
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
      {student | student.1 = true}
    let accessLaw := lg21NormalizedRestriction rawLaw accessEvent
    let takeEvent := lg21HiddenAccessTakerEvent testFeature E.takeDecision
    let takerLaw := lg21NormalizedRestriction accessLaw takeEvent
    let baseScore : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
      fun student => (lg21HiddenAccessStudentBase testFeature student.2,
        lg21HiddenAccessStudentScore testFeature student.2)
    let reportSet := lg21HiddenAccessReportSet testFeature E.reportDecision
    lg21NormalizedRestriction rawLaw
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision) =
      lg21NormalizedRestriction takerLaw (baseScore ⁻¹' reportSet) := by
  intro rawLaw accessEvent accessLaw takeEvent takerLaw baseScore reportSet
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have haccess : MeasurableSet accessEvent := by
    change MeasurableSet
      ((fun student : Bool × (ℝ × (Feature -> ℝ)) => student.1) ⁻¹'
        ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage measurable_fst
  have htake : MeasurableSet takeEvent := by
    exact lg21HiddenAccessTakerEvent_measurable testFeature E.takeDecision
      E.takeDecision_measurable
  have hbaseScore : Measurable baseScore := by
    exact lg21HiddenAccessBaseScoreObservation_measurable testFeature
  have hreport : MeasurableSet (baseScore ⁻¹' reportSet) := by
    exact (lg21HiddenAccessReportSet_measurable testFeature E.reportDecision
      E.reportDecision_measurable).preimage hbaseScore
  have hactual :
      lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision =
        accessEvent ∩ takeEvent ∩ baseScore ⁻¹' reportSet := by
    simpa only [accessEvent, takeEvent, baseScore, reportSet] using
      (lg21HiddenAccessOptionalReportEvent_eq_access_inter_taker_inter_report
        testFeature E.takeDecision E.reportDecision)
  change lg21NormalizedRestriction rawLaw
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision) =
    lg21NormalizedRestriction
      (lg21NormalizedRestriction
        (lg21NormalizedRestriction rawLaw accessEvent) takeEvent)
      (baseScore ⁻¹' reportSet)
  rw [lg21_normalizedRestriction_normalizedRestriction_eq_inter
    rawLaw accessEvent takeEvent haccess htake]
  rw [lg21_normalizedRestriction_normalizedRestriction_eq_inter
    rawLaw (accessEvent ∩ takeEvent) (baseScore ⁻¹' reportSet)
    (haccess.inter htake) hreport]
  rw [hactual]

/-- Any positive literal reporter population contains a positive mass of
access students who took the test.  The conclusion is deliberately about the
actual access-conditioned law, before any report-event posterior is chosen. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.accessLaw_takerEvent_positive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hpositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)) :
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
      {student | student.1 = true}
    let accessLaw := lg21NormalizedRestriction rawLaw accessEvent
    let takeEvent := lg21HiddenAccessTakerEvent testFeature E.takeDecision
    0 < accessLaw takeEvent := by
  intro rawLaw accessEvent accessLaw takeEvent
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have haccess : MeasurableSet accessEvent := by
    change MeasurableSet
      ((fun student : Bool × (ℝ × (Feature -> ℝ)) => student.1) ⁻¹'
        ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage measurable_fst
  have htake : MeasurableSet takeEvent := by
    exact lg21HiddenAccessTakerEvent_measurable testFeature E.takeDecision
      E.takeDecision_measurable
  let baseScore : Bool × (ℝ × (Feature -> ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
    fun student => (lg21HiddenAccessStudentBase testFeature student.2,
      lg21HiddenAccessStudentScore testFeature student.2)
  let reportSet := lg21HiddenAccessReportSet testFeature E.reportDecision
  have hactual :
      lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision =
        accessEvent ∩ takeEvent ∩ baseScore ⁻¹' reportSet := by
    simpa only [accessEvent, takeEvent, baseScore, reportSet] using
      (lg21HiddenAccessOptionalReportEvent_eq_access_inter_taker_inter_report
        testFeature E.takeDecision E.reportDecision)
  have hwhole : 0 < rawLaw
      ((accessEvent ∩ takeEvent) ∩ (baseScore ⁻¹' reportSet)) := by
    rw [← hactual]
    exact hpositive
  have haccessTake : 0 < rawLaw (accessEvent ∩ takeEvent) := by
    exact lt_of_lt_of_le hwhole (measure_mono (by
      intro student hstudent
      exact hstudent.1))
  change 0 < lg21NormalizedRestriction rawLaw accessEvent takeEvent
  exact lg21_normalizedRestriction_pos_of_inter_pos
    rawLaw accessEvent takeEvent haccess haccessTake

/-- Positive literal reporter mass yields positive mass for the later
observable report selection under the actual access-and-taker population.
This is the positivity premise needed to transfer a regular conditional law
through the report decision without assigning a posterior on an empty branch.
-/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.takerLaw_reportEvent_positive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hpositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)) :
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
      {student | student.1 = true}
    let accessLaw := lg21NormalizedRestriction rawLaw accessEvent
    let takeEvent := lg21HiddenAccessTakerEvent testFeature E.takeDecision
    let takerLaw := lg21NormalizedRestriction accessLaw takeEvent
    let baseScore : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
      fun student => (lg21HiddenAccessStudentBase testFeature student.2,
        lg21HiddenAccessStudentScore testFeature student.2)
    let reportSet := lg21HiddenAccessReportSet testFeature E.reportDecision
    0 < takerLaw (baseScore ⁻¹' reportSet) := by
  intro rawLaw accessEvent accessLaw takeEvent takerLaw baseScore reportSet
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have haccess : MeasurableSet accessEvent := by
    change MeasurableSet
      ((fun student : Bool × (ℝ × (Feature -> ℝ)) => student.1) ⁻¹'
        ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage measurable_fst
  have htake : MeasurableSet takeEvent := by
    exact lg21HiddenAccessTakerEvent_measurable testFeature E.takeDecision
      E.takeDecision_measurable
  have hactual :
      lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision =
        accessEvent ∩ takeEvent ∩ baseScore ⁻¹' reportSet := by
    simpa only [accessEvent, takeEvent, baseScore, reportSet] using
      (lg21HiddenAccessOptionalReportEvent_eq_access_inter_taker_inter_report
        testFeature E.takeDecision E.reportDecision)
  have hwhole : 0 < rawLaw
      ((accessEvent ∩ takeEvent) ∩ (baseScore ⁻¹' reportSet)) := by
    rw [← hactual]
    exact hpositive
  have haccessTake : 0 < rawLaw (accessEvent ∩ takeEvent) := by
    exact lt_of_lt_of_le hwhole (measure_mono (by
      intro student hstudent
      exact hstudent.1))
  have htakerPositive : 0 < accessLaw takeEvent := by
    change 0 < lg21NormalizedRestriction rawLaw accessEvent takeEvent
    exact lg21_normalizedRestriction_pos_of_inter_pos
      rawLaw accessEvent takeEvent haccess haccessTake
  letI : IsProbabilityMeasure accessLaw := by
    change IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M)
    exact lg21ContinuousGaussianAccessPopulationLaw_isProbability M E.access_positive
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  have htakeReportPositive : 0 < accessLaw
      (takeEvent ∩ (baseScore ⁻¹' reportSet)) := by
    change 0 < lg21NormalizedRestriction rawLaw accessEvent
      (takeEvent ∩ (baseScore ⁻¹' reportSet))
    have hwholeRight : 0 < rawLaw
        (accessEvent ∩ (takeEvent ∩ (baseScore ⁻¹' reportSet))) := by
      simpa only [Set.inter_assoc] using hwhole
    exact lg21_normalizedRestriction_pos_of_inter_pos
      rawLaw accessEvent (takeEvent ∩ (baseScore ⁻¹' reportSet)) haccess hwholeRight
  have htakerFinite : IsFiniteMeasure takerLaw := by
    exact ⟨by
      change (lg21NormalizedRestriction accessLaw takeEvent) Set.univ < ∞
      rw [show (lg21NormalizedRestriction accessLaw takeEvent) Set.univ = 1 by
        have := lg21NormalizedRestriction_isProbability accessLaw takeEvent
          (ne_of_gt htakerPositive) (measure_ne_top _ _)
        exact IsProbabilityMeasure.measure_univ]
      simp⟩
  letI : IsFiniteMeasure takerLaw := htakerFinite
  exact lg21_normalizedRestriction_pos_of_inter_pos
    accessLaw takeEvent (baseScore ⁻¹' reportSet) htake htakeReportPositive

theorem lg21HiddenAccessOptionalReportEvent_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (takeDecision : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool)
    (htakeDecision : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature -> ℝ) => takeDecision pair.1 pair.2))
    (hreportDecision : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
      reportDecision pair.1 pair.2)) :
    MeasurableSet
      (lg21HiddenAccessOptionalReportEvent testFeature takeDecision reportDecision) := by
  change MeasurableSet
    ((lg21HiddenAccessOptionalObservedAction testFeature takeDecision reportDecision) ⁻¹'
      ({true} : Set Bool))
  exact (measurableSet_singleton true).preimage
    (lg21HiddenAccessOptionalObservedAction_measurable testFeature takeDecision
      reportDecision htakeDecision hreportDecision)

/-- The literal reporter event is exactly the preimage of the report-tagged
public-record event. -/
theorem lg21HiddenAccessOptionalReportEvent_eq_publicReporter_preimage
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (takeDecision : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool) :
    lg21HiddenAccessOptionalReportEvent testFeature takeDecision reportDecision =
      (lg21HiddenAccessOptionalPublicObservation testFeature takeDecision reportDecision) ⁻¹'
        lg21HiddenAccessPublicReporterSet testFeature := by
  ext student
  rfl

/-- The report-tagged public record associated to an actually observed
`(base, score)` pair. -/
def lg21HiddenAccessReporterRecordEmbedding
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × (Bool × ℝ) :=
  fun profile => (profile.1, (true, profile.2))

/-- The `(base, score)` decoder for a tagged public record.  On the reporter
tag this is inverse to `lg21HiddenAccessReporterRecordEmbedding`; its value
on the no-report tag is deliberately not used as an observed score. -/
def lg21HiddenAccessReporterRecordDecode
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    ((LG21NonTestFeature Feature testFeature -> ℝ) × (Bool × ℝ)) ->
      (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
  fun record => (record.1, record.2.2)

theorem lg21HiddenAccessReporterRecordEmbedding_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Measurable (lg21HiddenAccessReporterRecordEmbedding (Feature := Feature) testFeature) := by
  exact measurable_fst.prodMk (measurable_const.prodMk measurable_snd)

theorem lg21HiddenAccessReporterRecordDecode_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Measurable (lg21HiddenAccessReporterRecordDecode (Feature := Feature) testFeature) := by
  exact measurable_fst.prodMk (measurable_snd.comp measurable_snd)

theorem lg21HiddenAccessReporterRecordDecode_embedding
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    lg21HiddenAccessReporterRecordDecode testFeature ∘
      lg21HiddenAccessReporterRecordEmbedding testFeature = id := by
  funext profile
  rfl

/-- On an actual report, the complete public record is exactly the tagged
embedding of the literal `(base, score)` observation. -/
theorem lg21HiddenAccessOptionalPublicObservation_eq_reporterEmbedding_of_report
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (takeDecision : ℝ -> (LG21NonTestFeature Feature testFeature -> ℝ) -> Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool)
    (student : Bool × (ℝ × (Feature -> ℝ)))
    (hreport : lg21HiddenAccessOptionalObservedAction testFeature takeDecision
      reportDecision student = true) :
    lg21HiddenAccessOptionalPublicObservation testFeature takeDecision reportDecision student =
      lg21HiddenAccessReporterRecordEmbedding testFeature
        (lg21HiddenAccessStudentBase testFeature student.2,
          lg21HiddenAccessStudentScore testFeature student.2) := by
  simp [lg21HiddenAccessOptionalPublicObservation, hreport,
    lg21HiddenAccessReporterRecordEmbedding]

/-- The actual literal source PBO, restricted to the positive reporter
population, is the reporter population's conditional skill mean given the
same complete public record.  This is the on-path bridge needed before the
reporter record can be identified with `(base, score)`.
-/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.reportedPayoff_eq_reporterCondMean_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hpositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)) :
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let publicObservation := lg21HiddenAccessOptionalPublicObservation testFeature E.takeDecision
      E.reportDecision
    let reporterLaw := lg21NormalizedRestriction rawLaw
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)
    letI : IsProbabilityMeasure rawLaw :=
      lg21ContinuousGaussianPopulationLaw_isProbability M
    letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
    letI : IsProbabilityMeasure reporterLaw :=
      lg21NormalizedRestriction_isProbability rawLaw
        (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)
        (ne_of_gt hpositive) (measure_ne_top _ _)
    letI : IsFiniteMeasure reporterLaw := ⟨by simp⟩
    (fun student => E.reportedPayoff
      (lg21HiddenAccessStudentBase testFeature student.2)
      (lg21HiddenAccessStudentScore testFeature student.2)) =ᵐ[reporterLaw]
      fun student => ∫ latentSkill, latentSkill ∂
        condDistrib lg21ContinuousPopulationSkill publicObservation reporterLaw
          (publicObservation student) := by
  intro rawLaw publicObservation reporterLaw
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure reporterLaw :=
    lg21NormalizedRestriction_isProbability rawLaw
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure reporterLaw := ⟨by simp⟩
  have hpublicObservation : Measurable publicObservation := by
    exact lg21HiddenAccessOptionalPublicObservation_measurable testFeature
      E.takeDecision E.reportDecision E.takeDecision_measurable E.reportDecision_measurable
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hrawPBO :
      lg21HiddenAccessOptionalPublicPayoff testFeature E.takeDecision E.reportDecision
        E.reportedPayoff E.noReportPayoff =ᵐ[rawLaw]
        rawLaw[lg21ContinuousPopulationSkill |
          MeasurableSpace.comap publicObservation inferInstance] := by
    exact E.public_pbo
  have hmean := lg21_publicPBO_condDistrib_on_positive_publicEvent_ae
      rawLaw publicObservation lg21ContinuousPopulationSkill
      (lg21HiddenAccessOptionalPublicPayoff testFeature E.takeDecision E.reportDecision
        E.reportedPayoff E.noReportPayoff)
      hpublicObservation hskill (lg21ContinuousGaussianPopulation_skill_integrable M)
      hrawPBO (lg21HiddenAccessPublicReporterSet testFeature)
      (lg21HiddenAccessPublicReporterSet_measurable testFeature) (by
        rw [← lg21HiddenAccessOptionalReportEvent_eq_publicReporter_preimage
          testFeature E.takeDecision E.reportDecision]
        exact hpositive)
  have hreportEvent : publicObservation ⁻¹'
      lg21HiddenAccessPublicReporterSet testFeature =
      lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision := by
    exact (lg21HiddenAccessOptionalReportEvent_eq_publicReporter_preimage
      testFeature E.takeDecision E.reportDecision).symm
  have hmeanReporter :
      lg21HiddenAccessOptionalPublicPayoff testFeature E.takeDecision E.reportDecision
        E.reportedPayoff E.noReportPayoff =ᵐ[reporterLaw]
        fun student => ∫ latentSkill, latentSkill ∂
          condDistrib lg21ContinuousPopulationSkill publicObservation reporterLaw
            (publicObservation student) := by
    simpa only [hreportEvent] using hmean
  have hreporterMem : ∀ᵐ student ∂reporterLaw,
      student ∈ lg21HiddenAccessOptionalReportEvent testFeature
        E.takeDecision E.reportDecision := by
    change ∀ᵐ student ∂(lg21NormalizedRestriction rawLaw
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)), _
    unfold lg21NormalizedRestriction
    refine Measure.ae_smul_measure ?_ _
    exact (ae_restrict_iff'
      (lg21HiddenAccessOptionalReportEvent_measurable testFeature E.takeDecision
        E.reportDecision E.takeDecision_measurable E.reportDecision_measurable)).2
      (ae_of_all _ fun student hstudent => hstudent)
  filter_upwards [hmeanReporter, hreporterMem] with student hmean hmember
  rw [← hmean]
  simp only [lg21HiddenAccessOptionalPublicPayoff]
  have hreport : lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
      E.reportDecision student = true := hmember
  simp [hreport]

/-- The complete literal public record contains precisely the `(base, score)`
information on the actual reporter population.  This is an a.e. transport
under the attained reporter law, not a global equality that would expose a
redacted score on no-report states. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.publicObservation_eq_reporterEmbedding_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hpositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)) :
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let reporterLaw := lg21NormalizedRestriction rawLaw
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)
    let publicObservation := lg21HiddenAccessOptionalPublicObservation testFeature
      E.takeDecision E.reportDecision
    let baseScore : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
      fun student => (lg21HiddenAccessStudentBase testFeature student.2,
        lg21HiddenAccessStudentScore testFeature student.2)
    letI : IsProbabilityMeasure rawLaw :=
      lg21ContinuousGaussianPopulationLaw_isProbability M
    letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
    letI : IsProbabilityMeasure reporterLaw :=
      lg21NormalizedRestriction_isProbability rawLaw
        (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)
        (ne_of_gt hpositive) (measure_ne_top _ _)
    letI : IsFiniteMeasure reporterLaw := ⟨by simp⟩
    ∀ᵐ student ∂reporterLaw,
      publicObservation student =
        lg21HiddenAccessReporterRecordEmbedding testFeature (baseScore student) := by
  intro rawLaw reporterLaw publicObservation baseScore
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure reporterLaw :=
    lg21NormalizedRestriction_isProbability rawLaw
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure reporterLaw := ⟨by simp⟩
  have hreporterMem : ∀ᵐ student ∂reporterLaw,
      student ∈ lg21HiddenAccessOptionalReportEvent testFeature
        E.takeDecision E.reportDecision := by
    change ∀ᵐ student ∂(lg21NormalizedRestriction rawLaw
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)), _
    unfold lg21NormalizedRestriction
    refine Measure.ae_smul_measure ?_ _
    exact (ae_restrict_iff'
      (lg21HiddenAccessOptionalReportEvent_measurable testFeature E.takeDecision
        E.reportDecision E.takeDecision_measurable E.reportDecision_measurable)).2
      (ae_of_all _ fun student hstudent => hstudent)
  filter_upwards [hreporterMem] with student hmember
  exact lg21HiddenAccessOptionalPublicObservation_eq_reporterEmbedding_of_report
    testFeature E.takeDecision E.reportDecision student hmember

/-- Mapping the attained reporter law to its complete public record is the
same as first mapping it to `(base, score)` and then applying the reporter
tag embedding. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.reporterLaw_map_publicObservation_eq
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hpositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)) :
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let reporterLaw := lg21NormalizedRestriction rawLaw
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)
    let publicObservation := lg21HiddenAccessOptionalPublicObservation testFeature
      E.takeDecision E.reportDecision
    let baseScore : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
      fun student => (lg21HiddenAccessStudentBase testFeature student.2,
        lg21HiddenAccessStudentScore testFeature student.2)
    letI : IsProbabilityMeasure rawLaw :=
      lg21ContinuousGaussianPopulationLaw_isProbability M
    letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
    letI : IsProbabilityMeasure reporterLaw :=
      lg21NormalizedRestriction_isProbability rawLaw
        (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)
        (ne_of_gt hpositive) (measure_ne_top _ _)
    letI : IsFiniteMeasure reporterLaw := ⟨by simp⟩
    reporterLaw.map publicObservation =
      (reporterLaw.map baseScore).map
        (lg21HiddenAccessReporterRecordEmbedding testFeature) := by
  intro rawLaw reporterLaw publicObservation baseScore
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure reporterLaw :=
    lg21NormalizedRestriction_isProbability rawLaw
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure reporterLaw := ⟨by simp⟩
  have hbaseScore : Measurable baseScore := by
    exact lg21HiddenAccessBaseScoreObservation_measurable testFeature
  have hpublicEq := E.publicObservation_eq_reporterEmbedding_ae hpositive
  calc
    reporterLaw.map publicObservation =
        reporterLaw.map
          (lg21HiddenAccessReporterRecordEmbedding testFeature ∘ baseScore) := by
          exact Measure.map_congr hpublicEq
    _ = (reporterLaw.map baseScore).map
        (lg21HiddenAccessReporterRecordEmbedding testFeature) := by
          rw [Measure.map_map
            (lg21HiddenAccessReporterRecordEmbedding_measurable testFeature) hbaseScore]

/-- On the attained reporter branch, the literal school payoff is the
conditional skill mean given the actual `(base, score)` record.  This is the
source PBO endpoint before any Gaussian calculation: the tag is eliminated
by a proved record embedding, while the conditional law remains the literal
reporter-population law.
-/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.reportedPayoff_eq_reporterBaseScoreCondMean_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hpositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)) :
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let reporterLaw := lg21NormalizedRestriction rawLaw
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)
    let publicObservation := lg21HiddenAccessOptionalPublicObservation testFeature
      E.takeDecision E.reportDecision
    let baseScore : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
      fun student => (lg21HiddenAccessStudentBase testFeature student.2,
        lg21HiddenAccessStudentScore testFeature student.2)
    letI : IsProbabilityMeasure rawLaw :=
      lg21ContinuousGaussianPopulationLaw_isProbability M
    letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
    letI : IsProbabilityMeasure reporterLaw :=
      lg21NormalizedRestriction_isProbability rawLaw
        (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)
        (ne_of_gt hpositive) (measure_ne_top _ _)
    letI : IsFiniteMeasure reporterLaw := ⟨by simp⟩
    (fun student => E.reportedPayoff
      (lg21HiddenAccessStudentBase testFeature student.2)
      (lg21HiddenAccessStudentScore testFeature student.2)) =ᵐ[reporterLaw]
      fun student => ∫ latentSkill, latentSkill ∂
        condDistrib lg21ContinuousPopulationSkill baseScore reporterLaw
          (baseScore student) := by
  intro rawLaw reporterLaw publicObservation baseScore
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure reporterLaw :=
    lg21NormalizedRestriction_isProbability rawLaw
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure reporterLaw := ⟨by simp⟩
  have hbaseScore : Measurable baseScore := by
    exact lg21HiddenAccessBaseScoreObservation_measurable testFeature
  have hpublicObservation : Measurable publicObservation := by
    exact lg21HiddenAccessOptionalPublicObservation_measurable testFeature
      E.takeDecision E.reportDecision E.takeDecision_measurable E.reportDecision_measurable
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  let posterior : Kernel
      ((LG21NonTestFeature Feature testFeature -> ℝ) × ℝ) ℝ :=
    condDistrib lg21ContinuousPopulationSkill baseScore reporterLaw
  have hfactor : reporterLaw.map
      (fun student => (baseScore student, lg21ContinuousPopulationSkill student)) =
        reporterLaw.map baseScore ⊗ₘ posterior := by
    dsimp [posterior]
    exact (compProd_map_condDistrib hskill.aemeasurable).symm
  have hrecordEmbedding := E.publicObservation_eq_reporterEmbedding_ae hpositive
  have hrecordRCD :
      condDistrib lg21ContinuousPopulationSkill publicObservation reporterLaw =ᵐ[
        reporterLaw.map publicObservation]
        posterior.comap (lg21HiddenAccessReporterRecordDecode testFeature)
          (lg21HiddenAccessReporterRecordDecode_measurable testFeature) := by
    exact lg21_condDistrib_recordEmbedding_eq_observationKernel_ae
      reporterLaw baseScore publicObservation lg21ContinuousPopulationSkill
      hbaseScore hpublicObservation hskill
      (lg21HiddenAccessReporterRecordEmbedding testFeature)
      (lg21HiddenAccessReporterRecordDecode testFeature)
      (lg21HiddenAccessReporterRecordEmbedding_measurable testFeature)
      (lg21HiddenAccessReporterRecordDecode_measurable testFeature)
      (by
        intro profile
        rfl)
      hrecordEmbedding posterior hfactor
  have hrecordRCDPullback : ∀ᵐ student ∂reporterLaw,
      condDistrib lg21ContinuousPopulationSkill publicObservation reporterLaw
          (publicObservation student) =
        posterior.comap (lg21HiddenAccessReporterRecordDecode testFeature)
          (lg21HiddenAccessReporterRecordDecode_measurable testFeature)
          (publicObservation student) := by
    exact ae_of_ae_map hpublicObservation.aemeasurable hrecordRCD
  have hdecodeRecord : ∀ᵐ student ∂reporterLaw,
      lg21HiddenAccessReporterRecordDecode testFeature (publicObservation student) =
        baseScore student := by
    filter_upwards [hrecordEmbedding] with student hrecord
    change lg21HiddenAccessReporterRecordDecode testFeature
        (lg21HiddenAccessOptionalPublicObservation testFeature E.takeDecision
          E.reportDecision student) =
      (lg21HiddenAccessStudentBase testFeature student.2,
        lg21HiddenAccessStudentScore testFeature student.2)
    rw [hrecord]
    rfl
  have hmean := E.reportedPayoff_eq_reporterCondMean_ae hpositive
  filter_upwards [hmean, hrecordRCDPullback, hdecodeRecord] with
      student hmean hrcd hdecode
  rw [hmean, hrcd]
  change (∫ latentSkill, latentSkill ∂posterior
      (lg21HiddenAccessReporterRecordDecode testFeature (publicObservation student))) =
    ∫ latentSkill, latentSkill ∂posterior (baseScore student)
  rw [hdecode]

/--
On the literal positive reporter branch, the reported PBO is the conditional
skill mean under the *actual access-and-taker population*, given `(base,
score)`.  The final report selection disappears because it is measurable in
that observation; the prior taking selection deliberately remains.  Thus the
statement neither substitutes an unselected Gaussian posterior nor evaluates
an arbitrary PBO version off the attained reporter branch.
-/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.reportedPayoff_eq_takerBaseScoreCondMean_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hpositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)) :
    let rawLaw := lg21ContinuousGaussianPopulationLaw M
    let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
      {student | student.1 = true}
    let accessLaw := lg21NormalizedRestriction rawLaw accessEvent
    let takeEvent := lg21HiddenAccessTakerEvent testFeature E.takeDecision
    let takerLaw := lg21NormalizedRestriction accessLaw takeEvent
    let baseScore : Bool × (ℝ × (Feature -> ℝ)) ->
        (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ :=
      fun student => (lg21HiddenAccessStudentBase testFeature student.2,
        lg21HiddenAccessStudentScore testFeature student.2)
    let reportSet := lg21HiddenAccessReportSet testFeature E.reportDecision
    let reporterLaw := lg21NormalizedRestriction rawLaw
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)
    letI : IsProbabilityMeasure rawLaw :=
      lg21ContinuousGaussianPopulationLaw_isProbability M
    letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
    letI : IsProbabilityMeasure accessLaw :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M E.access_positive
    letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
    letI : IsProbabilityMeasure takerLaw :=
      lg21NormalizedRestriction_isProbability accessLaw takeEvent
        (ne_of_gt (E.accessLaw_takerEvent_positive hpositive)) (measure_ne_top _ _)
    letI : IsFiniteMeasure takerLaw := ⟨by simp⟩
    letI : IsProbabilityMeasure reporterLaw :=
      lg21NormalizedRestriction_isProbability rawLaw
        (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)
        (ne_of_gt hpositive) (measure_ne_top _ _)
    letI : IsFiniteMeasure reporterLaw := ⟨by simp⟩
    (fun student => E.reportedPayoff
      (lg21HiddenAccessStudentBase testFeature student.2)
      (lg21HiddenAccessStudentScore testFeature student.2)) =ᵐ[reporterLaw]
      fun student => ∫ latentSkill, latentSkill ∂
        condDistrib lg21ContinuousPopulationSkill baseScore takerLaw
          (baseScore student) := by
  intro rawLaw accessEvent accessLaw takeEvent takerLaw baseScore reportSet reporterLaw
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure accessLaw := by
    change IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M)
    exact lg21ContinuousGaussianAccessPopulationLaw_isProbability M E.access_positive
  letI : IsFiniteMeasure accessLaw := ⟨by simp⟩
  have htakerPositive : 0 < accessLaw takeEvent := by
    exact E.accessLaw_takerEvent_positive hpositive
  letI : IsProbabilityMeasure takerLaw :=
    lg21NormalizedRestriction_isProbability accessLaw takeEvent
      (ne_of_gt htakerPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure takerLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure reporterLaw :=
    lg21NormalizedRestriction_isProbability rawLaw
      (lg21HiddenAccessOptionalReportEvent testFeature E.takeDecision E.reportDecision)
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure reporterLaw := ⟨by simp⟩
  have hbaseScore : Measurable baseScore := by
    exact lg21HiddenAccessBaseScoreObservation_measurable testFeature
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature -> ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hreportSet : MeasurableSet reportSet := by
    exact lg21HiddenAccessReportSet_measurable testFeature E.reportDecision
      E.reportDecision_measurable
  have hreportPositive : 0 < takerLaw (baseScore ⁻¹' reportSet) := by
    exact E.takerLaw_reportEvent_positive hpositive
  let selectedReporterLaw :=
    lg21NormalizedRestriction takerLaw (baseScore ⁻¹' reportSet)
  letI : IsProbabilityMeasure selectedReporterLaw :=
    lg21NormalizedRestriction_isProbability takerLaw (baseScore ⁻¹' reportSet)
      (ne_of_gt hreportPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedReporterLaw := ⟨by simp⟩
  have hreporterLaw : reporterLaw = selectedReporterLaw := by
    simpa only [selectedReporterLaw] using
      (lg21HiddenAccess_reporterLaw_eq_accessTakerReportLaw E)
  have hinvariantNested :
      condDistrib lg21ContinuousPopulationSkill baseScore
          selectedReporterLaw =ᵐ[selectedReporterLaw.map baseScore]
        condDistrib lg21ContinuousPopulationSkill baseScore takerLaw := by
    exact lg21_selectedObservation_condDistrib_latent_eq_raw_ae
      takerLaw baseScore lg21ContinuousPopulationSkill hbaseScore hskill
      reportSet hreportSet hreportPositive
  have hfactorSelected : selectedReporterLaw.map
      (fun student => (baseScore student, lg21ContinuousPopulationSkill student)) =
        selectedReporterLaw.map baseScore ⊗ₘ
          condDistrib lg21ContinuousPopulationSkill baseScore takerLaw := by
    calc
      selectedReporterLaw.map
          (fun student => (baseScore student, lg21ContinuousPopulationSkill student)) =
          selectedReporterLaw.map baseScore ⊗ₘ
            condDistrib lg21ContinuousPopulationSkill baseScore selectedReporterLaw := by
            exact (compProd_map_condDistrib hskill.aemeasurable).symm
      _ = selectedReporterLaw.map baseScore ⊗ₘ
            condDistrib lg21ContinuousPopulationSkill baseScore takerLaw := by
            exact Measure.compProd_congr hinvariantNested
  have hfactorReporter : reporterLaw.map
      (fun student => (baseScore student, lg21ContinuousPopulationSkill student)) =
        reporterLaw.map baseScore ⊗ₘ
          condDistrib lg21ContinuousPopulationSkill baseScore takerLaw := by
    calc
      reporterLaw.map
          (fun student => (baseScore student, lg21ContinuousPopulationSkill student)) =
          selectedReporterLaw.map
            (fun student => (baseScore student, lg21ContinuousPopulationSkill student)) := by
            rw [hreporterLaw]
      _ = selectedReporterLaw.map baseScore ⊗ₘ
            condDistrib lg21ContinuousPopulationSkill baseScore takerLaw := hfactorSelected
      _ = reporterLaw.map baseScore ⊗ₘ
            condDistrib lg21ContinuousPopulationSkill baseScore takerLaw := by
            rw [← hreporterLaw]
  have hinvariant :
      condDistrib lg21ContinuousPopulationSkill baseScore reporterLaw =ᵐ[
        reporterLaw.map baseScore]
        condDistrib lg21ContinuousPopulationSkill baseScore takerLaw := by
    exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      hbaseScore hskill hfactorReporter
  have hinvariantPullback : ∀ᵐ student ∂reporterLaw,
      condDistrib lg21ContinuousPopulationSkill baseScore reporterLaw
          (baseScore student) =
        condDistrib lg21ContinuousPopulationSkill baseScore takerLaw
          (baseScore student) := by
    exact ae_of_ae_map hbaseScore.aemeasurable hinvariant
  have hreported := E.reportedPayoff_eq_reporterBaseScoreCondMean_ae hpositive
  filter_upwards [hreported, hinvariantPullback] with student hreportedAt hinvariantAt
  rw [hreportedAt, hinvariantAt]


end

end LG21TestOptionalPolicies
