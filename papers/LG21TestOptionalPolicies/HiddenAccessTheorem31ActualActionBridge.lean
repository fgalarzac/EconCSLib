import LG21TestOptionalPolicies.ContinuousAccessConditionedPopulation
import Mathlib.Probability.Kernel.Condexp

/-!
# Literal hidden-access action bridge for LG21 Theorem 3.1

This module puts the source-timed Section 3 actions on the literal continuous
Gaussian population.  It is deliberately narrower than a closeout theorem:
it neither supplies a cutoff nor identifies a closed-form posterior.  Instead
it proves the facts a later posterior calculation must use without smuggling
them through an abstract equilibrium field:

* a measurable `Y(q, base)` is evaluated before the test score;
* a measurable `X(base, score)` is evaluated after that score is drawn;
* the school's public record contains `base`, `X`, and the score only when
  `X = 1`;
* once the behavioral argument has established all taking, the literal
  `X = 0` population is exactly the union of no-access students and
  access students whose post-score report action is false; and
* the no-report PBO is the conditional expectation on that actual normalized
  action population, almost everywhere in the base-profile law.

No result here chooses a value on an unreached information set.  In
particular, the conditional-expectation conclusion is an a.e. statement.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-! ## Source-timed actions on the literal population -/

/-- The complete non-test observed profile of a primitive source student. -/
def lg21HiddenAccessStudentBase
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) (student : ℝ × (Feature → ℝ)) :
    LG21NonTestFeature Feature testFeature → ℝ :=
  fun feature => student.1 + student.2 feature.1

/-- The raw designated test score of a primitive source student. -/
def lg21HiddenAccessStudentScore
    {Feature : Type*} [Fintype Feature]
    (testFeature : Feature) (student : ℝ × (Feature → ℝ)) : ℝ :=
  student.1 + student.2 testFeature

/-- The source's pre-score taking decision, evaluated on one primitive student. -/
def lg21HiddenAccessStudentTake
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (student : ℝ × (Feature → ℝ)) : Bool :=
  takeDecision student.1 (lg21HiddenAccessStudentBase testFeature student)

/-- The source's post-score reporting decision, evaluated on one primitive student. -/
def lg21HiddenAccessStudentReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (student : ℝ × (Feature → ℝ)) : Bool :=
  reportDecision (lg21HiddenAccessStudentBase testFeature student)
    (lg21HiddenAccessStudentScore testFeature student)

/--
The literal Section 3 observed report action.  A student without access cannot
report; an access student can report only after the source-timed taking action.
-/
def lg21HiddenAccessOptionalObservedAction
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (student : Bool × (ℝ × (Feature → ℝ))) : Bool :=
  if student.1 = true then
    if lg21HiddenAccessStudentTake testFeature takeDecision student.2 = true then
      lg21HiddenAccessStudentReport testFeature reportDecision student.2
    else false
  else false

/-- The actual `X = 0` event in the hidden-access optional protocol. -/
def lg21HiddenAccessOptionalNoReportEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool) :
    Set (Bool × (ℝ × (Feature → ℝ))) :=
  {student |
    lg21HiddenAccessOptionalObservedAction testFeature takeDecision reportDecision student = false}

/-- The literal no-access component of the `X = 0` population. -/
def lg21HiddenAccessNoAccessEvent
    {Feature : Type*} : Set (Bool × (ℝ × (Feature → ℝ))) :=
  {student | student.1 = false}

/-- The primitive access-student event on which a post-score action withholds. -/
def lg21HiddenAccessStudentNoReportEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool) :
    Set (ℝ × (Feature → ℝ)) :=
  {student | lg21HiddenAccessStudentReport testFeature reportDecision student = false}

/-- The access-and-withhold component of the literal `X = 0` population. -/
def lg21HiddenAccessAccessNoReportEvent
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool) :
    Set (Bool × (ℝ × (Feature → ℝ))) :=
  {student |
    student.1 = true ∧
      lg21HiddenAccessStudentReport testFeature reportDecision student.2 = false}

/--
The literal public information record in Section 3.  The final real coordinate
is deliberately redacted to `0` when `X = 0`; the preceding Boolean records
whether that coordinate is an observed score, so this adds no score
information to the no-report branch.
-/
def lg21HiddenAccessOptionalPublicObservation
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (student : Bool × (ℝ × (Feature → ℝ))) :
    (LG21NonTestFeature Feature testFeature → ℝ) × (Bool × ℝ) :=
  let observedAction :=
    lg21HiddenAccessOptionalObservedAction testFeature takeDecision reportDecision student
  (lg21HiddenAccessStudentBase testFeature student.2,
    (observedAction,
      if observedAction = true then
        lg21HiddenAccessStudentScore testFeature student.2
      else 0))

theorem lg21HiddenAccessStudentBase_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Measurable (lg21HiddenAccessStudentBase (Feature := Feature) testFeature) := by
  apply measurable_pi_lambda
  intro feature
  exact measurable_fst.add ((measurable_pi_apply feature.1).comp measurable_snd)

theorem lg21HiddenAccessStudentScore_measurable
    {Feature : Type*} [Fintype Feature]
    (testFeature : Feature) :
    Measurable (lg21HiddenAccessStudentScore (Feature := Feature) testFeature) := by
  exact measurable_fst.add ((measurable_pi_apply testFeature).comp measurable_snd)

theorem lg21HiddenAccessStudentTake_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (htakeDecision : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature → ℝ) =>
      takeDecision pair.1 pair.2)) :
    Measurable (lg21HiddenAccessStudentTake testFeature takeDecision) := by
  unfold lg21HiddenAccessStudentTake
  exact htakeDecision.comp
    (measurable_fst.prodMk (lg21HiddenAccessStudentBase_measurable testFeature))

theorem lg21HiddenAccessStudentReport_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (hreportDecision : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      reportDecision pair.1 pair.2)) :
    Measurable (lg21HiddenAccessStudentReport testFeature reportDecision) := by
  unfold lg21HiddenAccessStudentReport
  exact hreportDecision.comp
    ((lg21HiddenAccessStudentBase_measurable testFeature).prodMk
      (lg21HiddenAccessStudentScore_measurable testFeature))

theorem lg21HiddenAccessOptionalObservedAction_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (htakeDecision : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature → ℝ) =>
      takeDecision pair.1 pair.2))
    (hreportDecision : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      reportDecision pair.1 pair.2)) :
    Measurable
      (lg21HiddenAccessOptionalObservedAction testFeature takeDecision reportDecision) := by
  have haccess : Measurable (fun student : Bool × (ℝ × (Feature → ℝ)) => student.1) :=
    measurable_fst
  have htake : Measurable (fun student : Bool × (ℝ × (Feature → ℝ)) =>
      lg21HiddenAccessStudentTake testFeature takeDecision student.2) :=
    (lg21HiddenAccessStudentTake_measurable testFeature takeDecision htakeDecision).comp
      measurable_snd
  have hreport : Measurable (fun student : Bool × (ℝ × (Feature → ℝ)) =>
      lg21HiddenAccessStudentReport testFeature reportDecision student.2) :=
    (lg21HiddenAccessStudentReport_measurable testFeature reportDecision hreportDecision).comp
      measurable_snd
  unfold lg21HiddenAccessOptionalObservedAction
  apply Measurable.ite ((measurableSet_singleton true).preimage haccess)
  · apply Measurable.ite ((measurableSet_singleton true).preimage htake)
    · exact hreport
    · exact measurable_const
  · exact measurable_const

theorem lg21HiddenAccessOptionalNoReportEvent_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (htakeDecision : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature → ℝ) =>
      takeDecision pair.1 pair.2))
    (hreportDecision : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      reportDecision pair.1 pair.2)) :
    MeasurableSet
      (lg21HiddenAccessOptionalNoReportEvent testFeature takeDecision reportDecision) := by
  change MeasurableSet
    ((lg21HiddenAccessOptionalObservedAction testFeature takeDecision reportDecision) ⁻¹'
      ({false} : Set Bool))
  exact (measurableSet_singleton false).preimage
    (lg21HiddenAccessOptionalObservedAction_measurable testFeature takeDecision
      reportDecision htakeDecision hreportDecision)

theorem lg21HiddenAccessOptionalPublicObservation_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (htakeDecision : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature → ℝ) =>
      takeDecision pair.1 pair.2))
    (hreportDecision : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      reportDecision pair.1 pair.2)) :
    Measurable
      (lg21HiddenAccessOptionalPublicObservation testFeature takeDecision reportDecision) := by
  let action :=
    lg21HiddenAccessOptionalObservedAction testFeature takeDecision reportDecision
  have hbase : Measurable (fun student : Bool × (ℝ × (Feature → ℝ)) =>
      lg21HiddenAccessStudentBase testFeature student.2) :=
    (lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd
  have hscore : Measurable (fun student : Bool × (ℝ × (Feature → ℝ)) =>
      lg21HiddenAccessStudentScore testFeature student.2) :=
    (lg21HiddenAccessStudentScore_measurable testFeature).comp measurable_snd
  have haction : Measurable action :=
    lg21HiddenAccessOptionalObservedAction_measurable testFeature takeDecision
      reportDecision htakeDecision hreportDecision
  have hredacted : Measurable (fun student : Bool × (ℝ × (Feature → ℝ)) =>
      if action student = true then
        lg21HiddenAccessStudentScore testFeature student.2
      else 0) := by
    apply Measurable.ite ((measurableSet_singleton true).preimage haction)
    · exact hscore
    · exact measurable_const
  exact hbase.prodMk (haction.prodMk hredacted)

/-! ## Exact actual no-report population after all taking -/

theorem lg21HiddenAccessOptionalNoReportEvent_eq_noAccess_union_accessNoReport
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (hallTake : ∀ student,
      lg21HiddenAccessStudentTake testFeature takeDecision student = true) :
    lg21HiddenAccessOptionalNoReportEvent testFeature takeDecision reportDecision =
      lg21HiddenAccessNoAccessEvent ∪
      lg21HiddenAccessAccessNoReportEvent testFeature reportDecision := by
  ext student
  rcases student with ⟨access, primitive⟩
  cases access <;>
    simp [lg21HiddenAccessOptionalNoReportEvent,
      lg21HiddenAccessOptionalObservedAction, lg21HiddenAccessNoAccessEvent,
      lg21HiddenAccessAccessNoReportEvent, hallTake primitive]

/-- A universal behavioral all-taking conclusion applies to every literal source student. -/
theorem lg21HiddenAccessStudentTake_eq_true_of_all_take
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (hallTake : ∀ skill base, takeDecision skill base = true) :
    ∀ student,
      lg21HiddenAccessStudentTake testFeature takeDecision student = true := by
  intro student
  exact hallTake student.1 (lg21HiddenAccessStudentBase testFeature student)

theorem lg21HiddenAccessNoAccessEvent_eq_false_rectangle
    {Feature : Type*} :
    (lg21HiddenAccessNoAccessEvent (Feature := Feature)) =
      ({false} : Set Bool) ×ˢ Set.univ := by
  ext student
  rcases student with ⟨access, primitive⟩
  simp [lg21HiddenAccessNoAccessEvent]

theorem lg21HiddenAccessAccessNoReportEvent_eq_true_rectangle
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool) :
    lg21HiddenAccessAccessNoReportEvent testFeature reportDecision =
      ({true} : Set Bool) ×ˢ
        lg21HiddenAccessStudentNoReportEvent testFeature reportDecision := by
  ext student
  rcases student with ⟨access, primitive⟩
  simp [lg21HiddenAccessAccessNoReportEvent,
    lg21HiddenAccessStudentNoReportEvent]

theorem lg21HiddenAccessStudentNoReportEvent_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (hreportDecision : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      reportDecision pair.1 pair.2)) :
    MeasurableSet
      (lg21HiddenAccessStudentNoReportEvent testFeature reportDecision) := by
  change MeasurableSet
    ((lg21HiddenAccessStudentReport testFeature reportDecision) ⁻¹'
      ({false} : Set Bool))
  exact (measurableSet_singleton false).preimage
    (lg21HiddenAccessStudentReport_measurable testFeature reportDecision hreportDecision)

/--
The exact population mass of the actual `X = 0` branch after all taking.
The two displayed terms are not abstract mixture weights: they are the
no-access and access-and-withhold events in the literal product population.
-/
theorem lg21ContinuousGaussianPopulation_hiddenAccessOptional_noReport_mass
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (hallTake : ∀ student,
      lg21HiddenAccessStudentTake testFeature takeDecision student = true)
    (hreportDecision : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      reportDecision pair.1 pair.2)) :
    lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessOptionalNoReportEvent testFeature takeDecision reportDecision) =
      M.accessLaw ({false} : Set Bool) *
          lg21ContinuousGaussianStudentPrimitiveLaw M Set.univ +
        M.accessLaw ({true} : Set Bool) *
          lg21ContinuousGaussianStudentPrimitiveLaw M
            (lg21HiddenAccessStudentNoReportEvent testFeature reportDecision) := by
  rw [lg21HiddenAccessOptionalNoReportEvent_eq_noAccess_union_accessNoReport
    testFeature takeDecision reportDecision hallTake]
  rw [lg21HiddenAccessNoAccessEvent_eq_false_rectangle,
    lg21HiddenAccessAccessNoReportEvent_eq_true_rectangle]
  rw [MeasureTheory.measure_union]
  · rw [lg21ContinuousGaussianPopulation_access_student_factorization,
      lg21ContinuousGaussianPopulation_access_student_factorization]
  · apply Set.disjoint_left.2
    rintro ⟨access, primitive⟩ hfalse htrue
    simp only [Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true] at hfalse htrue
    simp_all
  · exact (measurableSet_singleton true).prod
      (lg21HiddenAccessStudentNoReportEvent_measurable testFeature reportDecision
        hreportDecision)

/-! ## Actual conditional-expectation semantics -/

/-- The literal full-population marginal of latent skill is the source prior. -/
theorem lg21ContinuousGaussianPopulation_skill_marginal
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature) :
    (lg21ContinuousGaussianPopulationLaw M).map
        (lg21ContinuousPopulationSkill (Feature := Feature)) =
      gaussianReal M.priorMean M.priorVariance := by
  letI : IsProbabilityMeasure M.accessLaw := M.accessLaw_isProbability
  letI : IsProbabilityMeasure (lg21ContinuousGaussianNoiseLaw M) := by
    unfold lg21ContinuousGaussianNoiseLaw
    infer_instance
  letI : IsProbabilityMeasure (lg21ContinuousGaussianStudentPrimitiveLaw M) := by
    unfold lg21ContinuousGaussianStudentPrimitiveLaw
    infer_instance
  calc
    (lg21ContinuousGaussianPopulationLaw M).map
        (lg21ContinuousPopulationSkill (Feature := Feature)) =
      ((lg21ContinuousGaussianPopulationLaw M).map Prod.snd).map Prod.fst := by
        rw [Measure.map_map measurable_fst measurable_snd]
        rfl
    _ = (lg21ContinuousGaussianStudentPrimitiveLaw M).map Prod.fst := by
        change Measure.map Prod.fst
          (M.accessLaw.prod (lg21ContinuousGaussianStudentPrimitiveLaw M)).snd =
            Measure.map Prod.fst (lg21ContinuousGaussianStudentPrimitiveLaw M)
        rw [Measure.snd_prod]
    _ = gaussianReal M.priorMean M.priorVariance := by
        ext event hevent
        rw [Measure.map_apply measurable_fst hevent]
        have hpreimage :
            (Prod.fst : ℝ × (Feature → ℝ) → ℝ) ⁻¹' event =
              event ×ˢ (Set.univ : Set (Feature → ℝ)) := by
          ext primitive
          simp
        rw [hpreimage]
        exact lg21ContinuousGaussianStudentPrimitiveLaw_skill_marginal M event

/-- Integrability of latent skill under the literal full source population. -/
theorem lg21ContinuousGaussianPopulation_skill_integrable
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature) :
    Integrable (lg21ContinuousPopulationSkill (Feature := Feature))
      (lg21ContinuousGaussianPopulationLaw M) := by
  have hgaussian : Integrable (fun skill : ℝ => skill)
      (gaussianReal M.priorMean M.priorVariance) := by
    apply integrable_of_mem_interior_integrableExpSet
    simp
  rw [← lg21ContinuousGaussianPopulation_skill_marginal M] at hgaussian
  exact (integrable_map_measure stronglyMeasurable_id.aestronglyMeasurable
    (by
      exact (measurable_fst.comp measurable_snd).aemeasurable)).mp
    (by simpa [Function.comp_def] using hgaussian)

/--
The source's Bayesian-optimal estimate is the conditional expectation under
the literal complete public record.  This exposes the action/PBO semantics
without a replacement equilibrium, a cutoff, or an opaque consistency field.
-/
theorem lg21HiddenAccessOptional_publicPBO_condExp_eq_actual_condDistrib_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (htakeDecision : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature → ℝ) =>
      takeDecision pair.1 pair.2))
    (hreportDecision : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      reportDecision pair.1 pair.2)) :
    let law := lg21ContinuousGaussianPopulationLaw M
    let observation := lg21HiddenAccessOptionalPublicObservation testFeature
      takeDecision reportDecision
    letI : IsProbabilityMeasure law :=
      lg21ContinuousGaussianPopulationLaw_isProbability M
    letI : IsFiniteMeasure law := ⟨by simp⟩
    law[lg21ContinuousPopulationSkill |
      MeasurableSpace.comap observation inferInstance] =ᵐ[law]
      fun student =>
        ∫ latentSkill, latentSkill ∂
          condDistrib lg21ContinuousPopulationSkill observation law
            (observation student) := by
  intro law observation
  letI : IsProbabilityMeasure law :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure law := ⟨by simp⟩
  exact condExp_ae_eq_integral_condDistrib'
    (lg21HiddenAccessOptionalPublicObservation_measurable testFeature
      takeDecision reportDecision htakeDecision hreportDecision)
    (lg21ContinuousGaussianPopulation_skill_integrable M)

/-- The literal population law restricted and normalized to the actual `X = 0` branch. -/
def lg21HiddenAccessOptionalNoReportLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool) :
    Measure (Bool × (ℝ × (Feature → ℝ))) :=
  lg21NormalizedRestriction (lg21ContinuousGaussianPopulationLaw M)
    (lg21HiddenAccessOptionalNoReportEvent testFeature takeDecision reportDecision)

/--
The actual hidden-access no-report PBO is the conditional expectation of
latent skill under the normalized literal `X = 0` population, conditioned on
the non-test profile.  This is the semantic input needed by the later
no-report-mixture calculation; it neither assumes a cutoff nor inserts a
pointwise value at a zero-mass base fibre.
-/
theorem lg21HiddenAccessOptional_noReport_condExp_eq_actual_condDistrib_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (hpositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalNoReportEvent testFeature takeDecision reportDecision)) :
    let law := lg21ContinuousGaussianPopulationLaw M
    letI : IsProbabilityMeasure law :=
      lg21ContinuousGaussianPopulationLaw_isProbability M
    letI : IsFiniteMeasure law := ⟨by simp⟩
    let noReportLaw := lg21HiddenAccessOptionalNoReportLaw M testFeature
      takeDecision reportDecision
    let base : Bool × (ℝ × (Feature → ℝ)) →
        (LG21NonTestFeature Feature testFeature → ℝ) :=
      fun student => lg21HiddenAccessStudentBase testFeature student.2
    letI : IsProbabilityMeasure noReportLaw :=
      lg21NormalizedRestriction_isProbability law
        (lg21HiddenAccessOptionalNoReportEvent testFeature takeDecision reportDecision)
        (ne_of_gt hpositive) (measure_ne_top _ _)
    letI : IsFiniteMeasure noReportLaw := ⟨by simp⟩
    noReportLaw[lg21ContinuousPopulationSkill |
      MeasurableSpace.comap base inferInstance] =ᵐ[noReportLaw]
      fun student =>
        ∫ latentSkill, latentSkill ∂
          condDistrib lg21ContinuousPopulationSkill base noReportLaw
            (base student) := by
  intro law noReportLaw base
  letI : IsProbabilityMeasure law :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure law := ⟨by simp⟩
  letI : IsProbabilityMeasure noReportLaw :=
    lg21NormalizedRestriction_isProbability law
      (lg21HiddenAccessOptionalNoReportEvent testFeature takeDecision reportDecision)
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure noReportLaw := ⟨by simp⟩
  have hbase : Measurable base := by
    exact (lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd
  have hskill : Integrable (lg21ContinuousPopulationSkill (Feature := Feature))
      noReportLaw := by
    unfold noReportLaw lg21HiddenAccessOptionalNoReportLaw
    exact (lg21ContinuousGaussianPopulation_skill_integrable M).restrict.smul_measure
      (ENNReal.inv_ne_top.mpr (ne_of_gt hpositive))
  exact condExp_ae_eq_integral_condDistrib' hbase hskill

end

end LG21TestOptionalPolicies
