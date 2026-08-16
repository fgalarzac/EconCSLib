import LG21TestOptionalPolicies.ContinuousObservedAccessSourceConditionalKernel
import LG21TestOptionalPolicies.ObservedAccessSequentialActions

/-!
# Actual sequential-action transport for the LG21 observed-access population

This module ties the source's two action times to the literal continuous
positive-access population.  A taking rule is evaluated from the non-test
profile and latent skill before test noise is used; a reporting rule is
evaluated from the non-test profile and realized score; and the observable
report action is their feasible conjunction.

The main result is a law identity.  If taking has actually been proved almost
everywhere, pushing the literal `X = 0` cohort through
`(base, score, skill)` gives exactly the normalized restriction of the
source-derived score/skill conditional experiment to the reporting event.
It is not an all-taking theorem, a PBO identity, or an equilibrium claim.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace LG21ObservedAccessSourceConditionalKernel

variable {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]

/-- The complete observed/latent coordinate used by the optional-reporting
conditional experiment. -/
def observedScoreSkill
    (M : LG21ObservedAccessSourceConditionalKernel Omega Base) :
    Omega -> Base × (ℝ × ℝ) :=
  fun omega => (M.base omega, (M.score omega, M.skill omega))

theorem observedScoreSkill_measurable
    (M : LG21ObservedAccessSourceConditionalKernel Omega Base) :
    Measurable M.observedScoreSkill :=
  M.base_measurable.prodMk (M.score_measurable.prodMk M.skill_measurable)

/-- The score-only no-report event in the conditional score/skill experiment.
Its definition retains the base profile, so it does not silently turn a
base-dependent reporting policy into a score-only policy. -/
def scoreNoReportEvent
    (M : LG21ObservedAccessSourceConditionalKernel Omega Base)
    (A : ObservedAccessSequentialActions M) :
    Set (Base × (ℝ × ℝ)) :=
  {pair | A.reportDecision pair.1 pair.2.1 = false}

theorem scoreNoReportEvent_measurable
    (M : LG21ObservedAccessSourceConditionalKernel Omega Base)
    (A : ObservedAccessSequentialActions M) :
    MeasurableSet (M.scoreNoReportEvent A) := by
  change MeasurableSet
    ((fun pair : Base × (ℝ × ℝ) => A.reportDecision pair.1 pair.2.1) ⁻¹'
      ({false} : Set Bool))
  exact (measurableSet_singleton false).preimage
    (A.reportDecision_measurable.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))

theorem observedScoreSkill_preimage_scoreNoReportEvent
    (M : LG21ObservedAccessSourceConditionalKernel Omega Base)
    (A : ObservedAccessSequentialActions M) :
    M.observedScoreSkill ⁻¹' M.scoreNoReportEvent A =
      {omega | A.reportDecision (M.base omega) (M.score omega) = false} := by
  rfl

/-- The actual `X = 0` action event is measurable because it is the union of
the pre-score refusal event and the take-then-withhold event. -/
theorem observedNoReport_measurableSet
    (M : LG21ObservedAccessSourceConditionalKernel Omega Base)
    (A : ObservedAccessSequentialActions M) :
    MeasurableSet {omega | A.observedReport omega = false} := by
  have htakeFalse : MeasurableSet {omega | A.take omega = false} :=
    (measurableSet_singleton false).preimage A.take_measurable
  have htakeTrue : MeasurableSet {omega | A.take omega = true} :=
    (measurableSet_singleton true).preimage A.take_measurable
  have hreportFalse :
      MeasurableSet
        {omega | A.reportDecision (M.base omega) (M.score omega) = false} :=
    (measurableSet_singleton false).preimage
      (A.reportDecision_measurable.comp
        (M.base_measurable.prodMk M.score_measurable))
  rw [show {omega | A.observedReport omega = false} =
      {omega | A.take omega = false} ∪
        ({omega | A.take omega = true} ∩
          {omega | A.reportDecision (M.base omega) (M.score omega) = false}) by
        ext omega
        exact A.observedReport_eq_false_iff omega]
  exact htakeFalse.union (htakeTrue.inter hreportFalse)

/-- Normalizing before or after pushing a measurable preimage event forward
is the same measure-level operation. -/
theorem normalizedRestriction_map_preimage
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    (law : Measure Alpha) (f : Alpha -> Beta) (hf : Measurable f)
    (event : Set Beta) (hevent : MeasurableSet event) :
    (lg21NormalizedRestriction law (f ⁻¹' event)).map f =
      lg21NormalizedRestriction (law.map f) event := by
  unfold lg21NormalizedRestriction
  calc
    ((law (f ⁻¹' event))⁻¹ • law.restrict (f ⁻¹' event)).map f =
        (law (f ⁻¹' event))⁻¹ • (law.restrict (f ⁻¹' event)).map f := by
          rw [Measure.map_smul]
    _ = (law (f ⁻¹' event))⁻¹ • (law.map f).restrict event := by
          rw [← Measure.restrict_map hf hevent]
    _ = ((law.map f) event)⁻¹ • (law.map f).restrict event := by
          rw [Measure.map_apply hf hevent]

/-- Once the pre-score taking action has actually been shown to be true almost
everywhere, the mapped literal no-report cohort is exactly the selection of
the source-derived `(base, score, skill)` conditional experiment by the
post-score reporting rule. -/
theorem actualNoReport_mappedLaw_eq_selectedScoreSkillLaw_of_all_take
    (M : LG21ObservedAccessSourceConditionalKernel Omega Base)
    (A : ObservedAccessSequentialActions M)
    (hallTake : ∀ᵐ omega ∂M.populationLaw, A.take omega = true) :
    (lg21NormalizedRestriction M.populationLaw
      {omega | A.observedReport omega = false}).map M.observedScoreSkill =
      lg21NormalizedRestriction
        (M.populationLaw.map M.base ⊗ₘ M.scoreSkillGivenBase)
        (M.scoreNoReportEvent A) := by
  rw [A.normalizedRestriction_observedNoReport_eq_scoreNoReport_of_all_take
    hallTake]
  rw [← M.observedScoreSkill_preimage_scoreNoReportEvent A]
  rw [normalizedRestriction_map_preimage M.populationLaw
    M.observedScoreSkill M.observedScoreSkill_measurable
    (M.scoreNoReportEvent A) (M.scoreNoReportEvent_measurable A)]
  exact congrArg (fun law => lg21NormalizedRestriction law
    (M.scoreNoReportEvent A)) M.raw_score_skill_disintegration

/-! ## Literal continuous-population specialization -/

/-- Instantiate the two source-timed actions on LG21's literal positive-access
Gaussian population.  The measurable decision maps are input data here; the
definition does not replace them with an equilibrium conclusion. -/
def lg21ContinuousObservedAccessSequentialActions
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (takeDecision : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool)
    (takeDecision_measurable :
      Measurable (fun pair : (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
        takeDecision pair.1 pair.2))
    (reportDecision : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool)
    (reportDecision_measurable :
      Measurable (fun pair : (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
        reportDecision pair.1 pair.2)) :
    ObservedAccessSequentialActions
      (lg21ContinuousObservedAccessSourceConditionalKernel M haccess testFeature) := by
  let source :=
    lg21ContinuousObservedAccessSourceConditionalKernel M haccess testFeature
  change ObservedAccessSequentialActions source
  exact
    { takeDecision := takeDecision
      takeDecision_measurable := takeDecision_measurable
      reportDecision := reportDecision
      reportDecision_measurable := reportDecision_measurable
      take := fun student =>
        takeDecision (source.base student) (source.skill student)
      report := fun student =>
        reportDecision (source.base student) (source.score student)
      observedReport := fun student =>
        takeDecision (source.base student) (source.skill student) &&
          reportDecision (source.base student) (source.score student)
      take_eq_source_timing := by intro student; rfl
      report_eq_source_timing := by intro student; rfl
      observedReport_eq_source_actions := by intro student; rfl }

/-- Concrete source-law specialization of the sequential-action transport.
The right-hand side is built from the literal continuous population's actual
conditional score/skill kernel, not a supplied posterior or action-selected
PBO.  The all-taking premise remains explicit because proving it is a
separate strategic obligation. -/
theorem lg21Continuous_actualNoReport_mappedLaw_eq_selectedScoreSkillLaw_of_all_take
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (takeDecision : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool)
    (takeDecision_measurable :
      Measurable (fun pair : (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
        takeDecision pair.1 pair.2))
    (reportDecision : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ -> Bool)
    (reportDecision_measurable :
      Measurable (fun pair : (LG21NonTestFeature Feature testFeature -> ℝ) × ℝ =>
        reportDecision pair.1 pair.2)) :
    let source :=
      lg21ContinuousObservedAccessSourceConditionalKernel M haccess testFeature
    let actions := lg21ContinuousObservedAccessSequentialActions M haccess testFeature
      takeDecision takeDecision_measurable reportDecision reportDecision_measurable
    (∀ᵐ student ∂source.populationLaw, actions.take student = true) ->
    (lg21NormalizedRestriction source.populationLaw
      {student | actions.observedReport student = false}).map
        source.observedScoreSkill =
      lg21NormalizedRestriction
        (source.populationLaw.map source.base ⊗ₘ source.scoreSkillGivenBase)
        (source.scoreNoReportEvent actions) := by
  intro source actions hallTake
  exact actualNoReport_mappedLaw_eq_selectedScoreSkillLaw_of_all_take
    source actions hallTake

end LG21ObservedAccessSourceConditionalKernel

end

end LG21TestOptionalPolicies
