import LG21TestOptionalPolicies.SelectedSignalPosteriorBridge
import LG21TestOptionalPolicies.ContinuousAccessConditionedPopulation
import LG21TestOptionalPolicies.ContinuousObservedAccessActualPBOBridge
import Mathlib.Probability.Kernel.Condexp

/-!
# Full-public-action bridge for report-required LG21 testing

The report-required action is selected before test noise from the complete
non-test profile and latent skill.  The school later observes the complete
non-test profile and reported score, not a latent skill band.  This module
therefore keeps both copies of the profile in the joint law:

* latent state: `(base, skill)`;
* public observation: `(base, score)`.

The central factorization is derived from the raw population law through its
canonical conditional signal kernel.  It has no supplied posterior, PBO, or
fixed continuous-base fibre.  After action selection, the posterior is the
canonical `signal dagger selectedLatentLaw` kernel.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

/-! ## Full public action event -/

/--
The report-required reporter event on the complete public/latent joint
coordinate.  Its latent component contains the profile needed by the known
taking rule; its public component is retained because the school conditions
on the full reported profile and score.
-/
def lg21ReportRequiredFullPublicReporterEvent
    {Base : Type*} [MeasurableSpace Base]
    (takeDecision : Base → ℝ → Bool) : Set ((Base × ℝ) × (Base × ℝ)) :=
  {pair | takeDecision pair.2.1 pair.2.2 = true}

/-- Measurability of the complete report-required action event. -/
theorem lg21ReportRequiredFullPublicReporterEvent_measurable
    {Base : Type*} [MeasurableSpace Base]
    (takeDecision : Base → ℝ → Bool)
    (htakeDecision : Measurable (fun pair : Base × ℝ => takeDecision pair.1 pair.2)) :
    MeasurableSet (lg21ReportRequiredFullPublicReporterEvent takeDecision) := by
  change MeasurableSet
    ((fun pair : (Base × ℝ) × (Base × ℝ) =>
      takeDecision pair.2.1 pair.2.2) ⁻¹' ({true} : Set Bool))
  exact (measurableSet_singleton true).preimage
    (htakeDecision.comp (measurable_fst.comp measurable_snd |>.prodMk
      (measurable_snd.comp measurable_snd)))

/--
The literal observed report action in the report-required protocol is exactly
the preimage of the complete public action event.  This is an equality of
events, not a label assigned to a hidden skill cohort.
-/
theorem lg21_reportRequired_observedReporter_eq_fullPublicEvent_preimage
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (base : Omega → Base) (score skill : Omega → ℝ)
    (takeDecision : Base → ℝ → Bool) (observedReport : Omega → Bool)
    (hrequired : ∀ omega,
      observedReport omega = takeDecision (base omega) (skill omega)) :
    {omega | observedReport omega = true} =
      (fun omega => ((base omega, score omega), (base omega, skill omega))) ⁻¹'
        lg21ReportRequiredFullPublicReporterEvent takeDecision := by
  ext omega
  change observedReport omega = true ↔ takeDecision (base omega) (skill omega) = true
  rw [hrequired omega]

/-! ## Generic selected full-observation posterior -/

/--
Public latent selection commutes with a signal experiment for arbitrary
latent and public-observation types.  This is the full-profile version of the
score-only selected-signal lemma: the posterior is canonical at every public
observation, including observations with zero selected mass.
-/
theorem lg21_normalizedRestriction_selectedSignalJoint_eq_posterior_full
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [StandardBorelSpace Alpha] [Nonempty Alpha]
    [MeasurableSpace Beta]
    (latentLaw : Measure Alpha) [IsProbabilityMeasure latentLaw]
    (signal : Kernel Alpha Beta) [IsFiniteKernel signal] [IsMarkovKernel signal]
    (selected : Set Alpha) (hselectedMeasurable : MeasurableSet selected)
    (hselectedPositive : 0 < latentLaw selected) :
    let selectedLaw := lg21NormalizedRestriction latentLaw selected
    letI : IsProbabilityMeasure selectedLaw :=
      lg21NormalizedRestriction_isProbability latentLaw selected
        (ne_of_gt hselectedPositive) (measure_ne_top _ _)
    letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
    let rawObservationLatentLaw := (latentLaw ⊗ₘ signal).map Prod.swap
    let publicEvent : Set (Beta × Alpha) := {pair | pair.2 ∈ selected}
    lg21NormalizedRestriction rawObservationLatentLaw publicEvent =
      (signal ∘ₘ selectedLaw) ⊗ₘ (signal†selectedLaw) := by
  let selectedLaw : Measure Alpha := lg21NormalizedRestriction latentLaw selected
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability latentLaw selected
      (ne_of_gt hselectedPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  let rawObservationLatentLaw : Measure (Beta × Alpha) :=
    (latentLaw ⊗ₘ signal).map Prod.swap
  let publicEvent : Set (Beta × Alpha) := {pair | pair.2 ∈ selected}
  change lg21NormalizedRestriction rawObservationLatentLaw publicEvent =
    (signal ∘ₘ selectedLaw) ⊗ₘ (signal†selectedLaw)
  have hpublicEvent : MeasurableSet publicEvent := by
    change MeasurableSet (Prod.snd ⁻¹' selected)
    exact hselectedMeasurable.preimage measurable_snd
  have hpreimage : Prod.swap ⁻¹' publicEvent = selected ×ˢ Set.univ := by
    ext pair
    simp [publicEvent]
  calc
    lg21NormalizedRestriction rawObservationLatentLaw publicEvent =
        (lg21NormalizedRestriction (latentLaw ⊗ₘ signal)
          (Prod.swap ⁻¹' publicEvent)).map Prod.swap := by
      symm
      exact lg21_normalizedRestriction_map_preimage
        (latentLaw ⊗ₘ signal) Prod.swap measurable_swap publicEvent hpublicEvent
    _ = (selectedLaw ⊗ₘ signal).map Prod.swap := by
      rw [hpreimage]
      congr 1
      exact lg21_normalizedRestriction_compProd_left latentLaw signal selected
        hselectedMeasurable
    _ = (signal ∘ₘ selectedLaw) ⊗ₘ (signal†selectedLaw) := by
      exact ProbabilityTheory.compProd_posterior_eq_map_swap.symm

/--
Derive the complete action-selected public joint law from an actual raw law.
`signal` is the raw law's canonical conditional distribution of the full
public observation given the full latent state.  In particular, this theorem
does not accept a posterior/PBO identity as an input.
-/
theorem lg21_literal_fullPublicAction_selectedJoint_eq_signalPosterior
    {Omega Alpha Beta : Type*} [MeasurableSpace Omega]
    [MeasurableSpace Alpha] [StandardBorelSpace Alpha] [Nonempty Alpha]
    [MeasurableSpace Beta] [StandardBorelSpace Beta] [Nonempty Beta]
    (rawLaw : Measure Omega) [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    (observation : Omega → Beta) (latent : Omega → Alpha)
    (hobservation : Measurable observation) (hlatent : Measurable latent)
    (takeDecision : Alpha → Bool) (htakeDecision : Measurable takeDecision)
    (hselectedPositive :
      0 < rawLaw {omega | takeDecision (latent omega) = true}) :
    let latentLaw := rawLaw.map latent
    letI : IsProbabilityMeasure latentLaw :=
      Measure.isProbabilityMeasure_map hlatent.aemeasurable
    let signal := condDistrib observation latent rawLaw
    let selected : Set Alpha := {alpha | takeDecision alpha = true}
    let selectedLaw := lg21NormalizedRestriction latentLaw selected
    letI : IsProbabilityMeasure selectedLaw :=
      lg21NormalizedRestriction_isProbability latentLaw selected
        (by
          change rawLaw.map latent (takeDecision ⁻¹' ({true} : Set Bool)) ≠ 0
          rw [Measure.map_apply hlatent
            ((measurableSet_singleton true).preimage htakeDecision)]
          exact ne_of_gt hselectedPositive)
        (measure_ne_top _ _)
    letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
    (lg21NormalizedRestriction rawLaw
      {omega | takeDecision (latent omega) = true}).map
        (fun omega => (observation omega, latent omega)) =
      (signal ∘ₘ selectedLaw) ⊗ₘ (signal†selectedLaw) := by
  let latentLaw : Measure Alpha := rawLaw.map latent
  letI : IsProbabilityMeasure latentLaw :=
    Measure.isProbabilityMeasure_map hlatent.aemeasurable
  letI : IsFiniteMeasure latentLaw := ⟨by simp⟩
  let signal : Kernel Alpha Beta := condDistrib observation latent rawLaw
  let selected : Set Alpha := {alpha | takeDecision alpha = true}
  let selectedLaw : Measure Alpha := lg21NormalizedRestriction latentLaw selected
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability latentLaw selected
      (by
        change rawLaw.map latent (takeDecision ⁻¹' ({true} : Set Bool)) ≠ 0
        rw [Measure.map_apply hlatent
          ((measurableSet_singleton true).preimage htakeDecision)]
        exact ne_of_gt hselectedPositive)
      (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  let publicEvent : Set (Beta × Alpha) := {pair | takeDecision pair.2 = true}
  have hselectedMeasurable : MeasurableSet selected := by
    change MeasurableSet (takeDecision ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage htakeDecision
  have hrawJoint : rawLaw.map (fun omega => (observation omega, latent omega)) =
      (latentLaw ⊗ₘ signal).map Prod.swap := by
    calc
      rawLaw.map (fun omega => (observation omega, latent omega)) =
          (rawLaw.map (fun omega => (latent omega, observation omega))).map Prod.swap := by
            rw [Measure.map_map measurable_swap (hlatent.prodMk hobservation)]
            rfl
      _ = (latentLaw ⊗ₘ signal).map Prod.swap := by
            rw [← ProbabilityTheory.compProd_map_condDistrib
              hobservation.aemeasurable]
  have hpublicEvent : publicEvent = {pair | pair.2 ∈ selected} := by
    ext pair
    rfl
  let sourceEvent : Set Omega := {omega | takeDecision (latent omega) = true}
  let observedLatent : Omega → Beta × Alpha :=
    fun omega => (observation omega, latent omega)
  have hsourceEvent : sourceEvent = observedLatent ⁻¹' publicEvent := by
    ext omega
    rfl
  calc
    (lg21NormalizedRestriction rawLaw sourceEvent).map observedLatent =
        lg21NormalizedRestriction (rawLaw.map observedLatent) publicEvent := by
          exact lg21_normalizedRestriction_map_preimage rawLaw observedLatent
            (hobservation.prodMk hlatent) publicEvent
            (by rw [hpublicEvent]; exact hselectedMeasurable.preimage measurable_snd)
    _ = lg21NormalizedRestriction ((latentLaw ⊗ₘ signal).map Prod.swap) publicEvent := by
          rw [hrawJoint]
    _ = (signal ∘ₘ selectedLaw) ⊗ₘ (signal†selectedLaw) := by
          rw [hpublicEvent]
          exact lg21_normalizedRestriction_selectedSignalJoint_eq_posterior_full
            latentLaw signal selected hselectedMeasurable
            (by
              change 0 < rawLaw.map latent
                (takeDecision ⁻¹' ({true} : Set Bool))
              rw [Measure.map_apply hlatent
                ((measurableSet_singleton true).preimage htakeDecision)]
              exact hselectedPositive)

/-! ## Full-observation PBO consequence -/

/--
For the actual report-required reporter population, the conditional expected
skill given the full public observation `(base, score)` is the skill
projection of the canonical selected posterior.  The conclusion is only
almost everywhere under the actual reporter law; no value is asserted on an
unreached public observation.
-/
theorem lg21_reportRequired_fullPublicAction_condExp_eq_signalPosteriorMean_ae
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    [StandardBorelSpace Base] [Nonempty Base]
    (rawLaw : Measure Omega) [IsProbabilityMeasure rawLaw] [IsFiniteMeasure rawLaw]
    (base : Omega → Base) (score skill : Omega → ℝ)
    (hbase : Measurable base) (hscore : Measurable score) (hskill : Measurable skill)
    (signal : Kernel (Base × ℝ) (Base × ℝ)) [IsFiniteKernel signal]
    (selectedLatentLaw : Measure (Base × ℝ)) [IsProbabilityMeasure selectedLatentLaw]
    (takeDecision : Base → ℝ → Bool) (observedReport : Omega → Bool)
    (hrequired : ∀ omega,
      observedReport omega = takeDecision (base omega) (skill omega))
    (hpositive : 0 < rawLaw {omega | observedReport omega = true})
    (hselectedJoint :
      (lg21NormalizedRestriction rawLaw
        ((fun omega => ((base omega, score omega), (base omega, skill omega))) ⁻¹'
          lg21ReportRequiredFullPublicReporterEvent takeDecision)).map
        (fun omega => ((base omega, score omega), (base omega, skill omega))) =
      (signal ∘ₘ selectedLatentLaw) ⊗ₘ (signal†selectedLatentLaw))
    (hintegrable : Integrable skill
      (lg21NormalizedRestriction rawLaw {omega | observedReport omega = true})) :
    let reporterLaw := lg21NormalizedRestriction rawLaw
      {omega | observedReport omega = true}
    reporterLaw[skill |
      MeasurableSpace.comap (fun omega => (base omega, score omega)) inferInstance] =ᵐ[
        reporterLaw]
      fun omega => ∫ latentSkill, latentSkill.2 ∂
        (signal†selectedLatentLaw) (base omega, score omega) := by
  intro reporterLaw
  let publicEvent : Set ((Base × ℝ) × (Base × ℝ)) :=
    lg21ReportRequiredFullPublicReporterEvent takeDecision
  let observation : Omega → Base × ℝ := fun omega => (base omega, score omega)
  let latent : Omega → Base × ℝ := fun omega => (base omega, skill omega)
  let observedLatent : Omega → (Base × ℝ) × (Base × ℝ) :=
    fun omega => (observation omega, latent omega)
  have hobservation : Measurable observation := hbase.prodMk hscore
  have hlatent : Measurable latent := hbase.prodMk hskill
  have hobservedLatent : Measurable observedLatent := hobservation.prodMk hlatent
  have hactionEvent :
      {omega | observedReport omega = true} = observedLatent ⁻¹' publicEvent := by
    simpa [publicEvent, observation, latent, observedLatent] using
      (lg21_reportRequired_observedReporter_eq_fullPublicEvent_preimage
        base score skill takeDecision observedReport hrequired)
  letI : IsProbabilityMeasure reporterLaw := by
    dsimp [reporterLaw]
    exact lg21NormalizedRestriction_isProbability rawLaw
      {omega | observedReport omega = true} (ne_of_gt hpositive)
      (measure_ne_top _ _)
  letI : IsFiniteMeasure reporterLaw := ⟨by simp⟩
  letI : IsFiniteMeasure selectedLatentLaw := ⟨by simp⟩
  let posterior : Kernel (Base × ℝ) (Base × ℝ) := signal†selectedLatentLaw
  have hselectedJointReporter :
      reporterLaw.map observedLatent =
        (signal ∘ₘ selectedLatentLaw) ⊗ₘ posterior := by
    rw [show reporterLaw = lg21NormalizedRestriction rawLaw
      (observedLatent ⁻¹' publicEvent) by
      rw [show reporterLaw = lg21NormalizedRestriction rawLaw
        {omega | observedReport omega = true} by rfl, hactionEvent]]
    simpa [publicEvent, observation, latent, observedLatent, posterior] using hselectedJoint
  have hreporterObservationLaw : reporterLaw.map observation =
      signal ∘ₘ selectedLatentLaw := by
    calc
      reporterLaw.map observation = (reporterLaw.map observedLatent).map Prod.fst := by
        rw [Measure.map_map measurable_fst hobservedLatent]
        rfl
      _ = ((signal ∘ₘ selectedLatentLaw) ⊗ₘ posterior).map Prod.fst := by
        rw [hselectedJointReporter]
      _ = signal ∘ₘ selectedLatentLaw := Measure.fst_compProd _ _
  have hfactor : reporterLaw.map observedLatent =
      reporterLaw.map observation ⊗ₘ posterior := by
    rw [hselectedJointReporter, hreporterObservationLaw]
  have hcondDistribLatent :
      condDistrib latent observation reporterLaw =ᵐ[reporterLaw.map observation] posterior := by
    exact condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      hobservation hlatent hfactor
  have hcondDistribSkill :
      condDistrib skill observation reporterLaw =ᵐ[reporterLaw.map observation]
        posterior.map Prod.snd := by
    have hcomp :
        condDistrib (Prod.snd ∘ latent) observation reporterLaw =ᵐ[
          reporterLaw.map observation]
          (condDistrib latent observation reporterLaw).map Prod.snd := by
      exact condDistrib_comp observation hlatent.aemeasurable measurable_snd
    filter_upwards [hcomp, hcondDistribLatent] with observed hcompEq hlatentEq
    have hmapEq :
        (condDistrib latent observation reporterLaw).map Prod.snd observed =
          posterior.map Prod.snd observed :=
      by
        rw [Kernel.map_apply _ measurable_snd, Kernel.map_apply _ measurable_snd]
        exact congrArg (fun law : Measure (Base × ℝ) => law.map Prod.snd) hlatentEq
    simpa [latent, Function.comp_def] using hcompEq.trans hmapEq
  have hcondExp := condExp_ae_eq_integral_condDistrib' hobservation hintegrable
  have hcondDistribPullback :
      ∀ᵐ omega ∂reporterLaw,
        condDistrib skill observation reporterLaw (observation omega) =
          posterior.map Prod.snd (observation omega) := by
    exact ae_of_ae_map hobservation.aemeasurable hcondDistribSkill
  filter_upwards [hcondExp, hcondDistribPullback] with omega hExp hKernel
  rw [hExp, hKernel]
  change (∫ latentSkill : ℝ, latentSkill ∂
      posterior.map Prod.snd (observation omega)) =
    ∫ latentSkill : Base × ℝ, latentSkill.2 ∂posterior (observation omega)
  rw [Kernel.map_apply _ measurable_snd]
  exact integral_map_of_stronglyMeasurable measurable_snd stronglyMeasurable_id

/-! ## Literal LG21 source instantiation -/

/--
The literal positive-access Gaussian population supplies the full action
factorization with no source-side posterior premise.  The conditional signal
is the raw law's canonical `(base, score) | (base, skill)` kernel; its use is
valid only under the selected law, so no pointwise belief is assigned to a
zero-mass profile/score combination.
-/
theorem lg21ContinuousGaussianAccessPopulation_reportRequired_fullPublicAction_selectedJoint_eq_signalPosterior
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (takeDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (htakeDecision :
      Measurable (fun pair : (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
        takeDecision pair.1 pair.2))
    (hselectedPositive :
      0 < (lg21ContinuousGaussianAccessPopulationLaw M)
        {student | takeDecision (lg21ContinuousPopulationBase testFeature student)
          (lg21ContinuousPopulationSkill student) = true}) :
    let rawLaw := lg21ContinuousGaussianAccessPopulationLaw M
    let observation : Bool × (ℝ × (Feature → ℝ)) →
        (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
      fun student =>
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationFeature testFeature student)
    let latent : Bool × (ℝ × (Feature → ℝ)) →
        (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
      fun student =>
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationSkill student)
    letI : IsProbabilityMeasure rawLaw :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
    let latentLaw := rawLaw.map latent
    letI : IsProbabilityMeasure latentLaw :=
      Measure.isProbabilityMeasure_map (by
        apply Measurable.aemeasurable
        exact (lg21ContinuousPopulationBase_measurable testFeature).prodMk
          (by
            change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
            exact measurable_fst.comp measurable_snd))
    let signal := condDistrib observation latent rawLaw
    let selected : Set ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) :=
      {profileSkill | takeDecision profileSkill.1 profileSkill.2 = true}
    let selectedLaw := lg21NormalizedRestriction latentLaw selected
    letI : IsProbabilityMeasure selectedLaw :=
      lg21NormalizedRestriction_isProbability latentLaw selected
        (by
          change rawLaw.map latent
            ((fun profileSkill => takeDecision profileSkill.1 profileSkill.2) ⁻¹'
              ({true} : Set Bool)) ≠ 0
          rw [Measure.map_apply
            ((lg21ContinuousPopulationBase_measurable testFeature).prodMk
              (by
                change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
                exact measurable_fst.comp measurable_snd))
            ((measurableSet_singleton true).preimage htakeDecision)]
          exact ne_of_gt hselectedPositive)
        (measure_ne_top _ _)
    letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
    (lg21NormalizedRestriction rawLaw
      ((fun student => (observation student, latent student)) ⁻¹'
        lg21ReportRequiredFullPublicReporterEvent takeDecision)).map
        (fun student => (observation student, latent student)) =
      (signal ∘ₘ selectedLaw) ⊗ₘ (signal†selectedLaw) := by
  let rawLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let observation : Bool × (ℝ × (Feature → ℝ)) →
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
    fun student =>
      (lg21ContinuousPopulationBase testFeature student,
        lg21ContinuousPopulationFeature testFeature student)
  let latent : Bool × (ℝ × (Feature → ℝ)) →
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
    fun student =>
      (lg21ContinuousPopulationBase testFeature student,
        lg21ContinuousPopulationSkill student)
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hscore : Measurable
      (lg21ContinuousPopulationFeature (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact hskill.add ((measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd))
  have hbase : Measurable (lg21ContinuousPopulationBase testFeature) :=
    lg21ContinuousPopulationBase_measurable testFeature
  have hobservation : Measurable observation := hbase.prodMk hscore
  have hlatent : Measurable latent := hbase.prodMk hskill
  let fullTakeDecision :
      ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) → Bool :=
    fun profileSkill => takeDecision profileSkill.1 profileSkill.2
  have hfullTakeDecision : Measurable fullTakeDecision := htakeDecision
  have hselected :
      0 < rawLaw {student | fullTakeDecision (latent student) = true} := by
    simpa [rawLaw, latent, fullTakeDecision] using hselectedPositive
  simpa [rawLaw, observation, latent, fullTakeDecision,
    lg21ReportRequiredFullPublicReporterEvent] using
    (lg21_literal_fullPublicAction_selectedJoint_eq_signalPosterior
      rawLaw observation latent hobservation hlatent fullTakeDecision
      hfullTakeDecision hselected)

/--
The literal positive-access Gaussian source population also supplies the
integrability needed for the full-public selected-PBO conclusion.  This theorem
is a source-law and conditional-expectation bridge only: it starts from a
measurable pre-score taking rule and the actual observed report action, derives
the selected joint law and reporter integrability from the same population,
and concludes only almost everywhere under the actual reporter law.  It does
not assume an equilibrium, a cutoff, a pointwise posterior value, or a
selection-free reported payoff.
-/
theorem lg21ContinuousGaussianAccessPopulation_reportRequired_fullPublicAction_condExp_eq_signalPosteriorMean_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (takeDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (htakeDecision :
      Measurable (fun pair : (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
        takeDecision pair.1 pair.2))
    (observedReport : Bool × (ℝ × (Feature → ℝ)) → Bool)
    (hrequired : ∀ student,
      observedReport student = takeDecision
        (lg21ContinuousPopulationBase testFeature student)
        (lg21ContinuousPopulationSkill student))
    (hselectedPositive :
      0 < (lg21ContinuousGaussianAccessPopulationLaw M)
        {student | takeDecision (lg21ContinuousPopulationBase testFeature student)
          (lg21ContinuousPopulationSkill student) = true}) :
    let rawLaw := lg21ContinuousGaussianAccessPopulationLaw M
    let observation : Bool × (ℝ × (Feature → ℝ)) →
        (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
      fun student =>
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationFeature testFeature student)
    let latent : Bool × (ℝ × (Feature → ℝ)) →
        (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
      fun student =>
        (lg21ContinuousPopulationBase testFeature student,
          lg21ContinuousPopulationSkill student)
    letI : IsProbabilityMeasure rawLaw :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
    let latentLaw := rawLaw.map latent
    letI : IsProbabilityMeasure latentLaw :=
      Measure.isProbabilityMeasure_map (by
        apply Measurable.aemeasurable
        exact (lg21ContinuousPopulationBase_measurable testFeature).prodMk
          (by
            change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
            exact measurable_fst.comp measurable_snd))
    let selected : Set ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) :=
      {profileSkill | takeDecision profileSkill.1 profileSkill.2 = true}
    let selectedLaw := lg21NormalizedRestriction latentLaw selected
    letI : IsProbabilityMeasure selectedLaw :=
      lg21NormalizedRestriction_isProbability latentLaw selected
        (by
          change rawLaw.map latent
            ((fun profileSkill => takeDecision profileSkill.1 profileSkill.2) ⁻¹'
              ({true} : Set Bool)) ≠ 0
          rw [Measure.map_apply
            ((lg21ContinuousPopulationBase_measurable testFeature).prodMk
              (by
                change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
                exact measurable_fst.comp measurable_snd))
            ((measurableSet_singleton true).preimage htakeDecision)]
          exact ne_of_gt hselectedPositive)
        (measure_ne_top _ _)
    letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
    let signal := condDistrib observation latent rawLaw
    let reporterLaw := lg21NormalizedRestriction rawLaw
      {student | observedReport student = true}
    reporterLaw[lg21ContinuousPopulationSkill |
      MeasurableSpace.comap observation inferInstance] =ᵐ[reporterLaw]
      fun student => ∫ latentSkill, latentSkill.2 ∂
        (signal†selectedLaw) (observation student) := by
  intro rawLaw observation latent
  letI : IsProbabilityMeasure rawLaw :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hskill : Measurable (lg21ContinuousPopulationSkill (Feature := Feature)) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) => student.2.1
    exact measurable_fst.comp measurable_snd
  have hscore : Measurable
      (lg21ContinuousPopulationFeature (Feature := Feature) testFeature) := by
    change Measurable fun student : Bool × (ℝ × (Feature → ℝ)) =>
      student.2.1 + student.2.2 testFeature
    exact hskill.add ((measurable_pi_apply testFeature).comp
      (measurable_snd.comp measurable_snd))
  have hbase : Measurable (lg21ContinuousPopulationBase testFeature) :=
    lg21ContinuousPopulationBase_measurable testFeature
  have hobservation : Measurable observation := hbase.prodMk hscore
  have hlatent : Measurable latent := hbase.prodMk hskill
  let fullTakeDecision :
      ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) → Bool :=
    fun profileSkill => takeDecision profileSkill.1 profileSkill.2
  have hfullTakeDecision : Measurable fullTakeDecision := htakeDecision
  have hselected :
      0 < rawLaw {student | fullTakeDecision (latent student) = true} := by
    simpa [rawLaw, latent, fullTakeDecision] using hselectedPositive
  let latentLaw : Measure ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) :=
    rawLaw.map latent
  letI : IsProbabilityMeasure latentLaw :=
    Measure.isProbabilityMeasure_map hlatent.aemeasurable
  letI : IsFiniteMeasure latentLaw := ⟨by simp⟩
  let selected : Set ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) :=
    {profileSkill | fullTakeDecision profileSkill = true}
  let selectedLaw : Measure ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) :=
    lg21NormalizedRestriction latentLaw selected
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability latentLaw selected
      (by
        change rawLaw.map latent
          (fullTakeDecision ⁻¹' ({true} : Set Bool)) ≠ 0
        rw [Measure.map_apply hlatent
          ((measurableSet_singleton true).preimage hfullTakeDecision)]
        exact ne_of_gt hselected)
      (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  let signal : Kernel
      ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ)
      ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) :=
    condDistrib observation latent rawLaw
  have hactualReporter :
      {student | observedReport student = true} =
        {student | fullTakeDecision (latent student) = true} := by
    ext student
    change observedReport student = true ↔
      takeDecision (lg21ContinuousPopulationBase testFeature student)
        (lg21ContinuousPopulationSkill student) = true
    rw [hrequired student]
  have hreporterPositive :
      0 < rawLaw {student | observedReport student = true} := by
    rw [hactualReporter]
    exact hselected
  have hselectedJoint :
      (lg21NormalizedRestriction rawLaw
        ((fun student => (observation student, latent student)) ⁻¹'
          lg21ReportRequiredFullPublicReporterEvent takeDecision)).map
          (fun student => (observation student, latent student)) =
        (signal ∘ₘ selectedLaw) ⊗ₘ (signal†selectedLaw) := by
    simpa [rawLaw, observation, latent, fullTakeDecision, selected, selectedLaw,
      signal] using
      (lg21ContinuousGaussianAccessPopulation_reportRequired_fullPublicAction_selectedJoint_eq_signalPosterior
        M haccess testFeature takeDecision htakeDecision hselectedPositive)
  have hsourceSkillIntegrable :
      Integrable (lg21ContinuousPopulationSkill (Feature := Feature)) rawLaw := by
    change Integrable (lg21ContinuousPopulationSkill (Feature := Feature))
      (lg21ContinuousGaussianAccessPopulationLaw M)
    exact lg21ContinuousGaussianAccessPopulation_skill_integrable M haccess
  have hreporterIntegrable :
      Integrable (lg21ContinuousPopulationSkill (Feature := Feature))
        (lg21NormalizedRestriction rawLaw
          {student | observedReport student = true}) := by
    unfold lg21NormalizedRestriction
    exact hsourceSkillIntegrable.restrict.smul_measure
      (ENNReal.inv_ne_top.mpr (ne_of_gt hreporterPositive))
  simpa [rawLaw, observation, latent, fullTakeDecision, selected, selectedLaw,
    signal] using
    (lg21_reportRequired_fullPublicAction_condExp_eq_signalPosteriorMean_ae
      rawLaw (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      (lg21ContinuousPopulationSkill (Feature := Feature))
      hbase hscore hskill signal selectedLaw takeDecision observedReport
      hrequired hreporterPositive hselectedJoint hreporterIntegrable)

end

end LG21TestOptionalPolicies
