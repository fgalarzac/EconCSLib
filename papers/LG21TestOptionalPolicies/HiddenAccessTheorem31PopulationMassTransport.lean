import LG21TestOptionalPolicies.HiddenAccessTheorem31LiteralSourceEquilibrium

/-!
# Literal action-mass transport for LG21 Theorem 3.1

This module transports score-action facts proved under the actual positive
access law back to the literal hidden-access population.  It keeps the action
event explicit throughout, so a withholding conclusion is not inferred from a
strategy name or a pointwise representative of a conditional distribution.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- The post-score `(base, score)` observation on a primitive source student. -/
def lg21HiddenAccessPrimitiveBaseScoreObservation
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) (student : ℝ × (Feature → ℝ)) :
    (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
  (lg21HiddenAccessStudentBase testFeature student,
    lg21HiddenAccessStudentScore testFeature student)

theorem lg21HiddenAccessPrimitiveBaseScoreObservation_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Measurable (lg21HiddenAccessPrimitiveBaseScoreObservation
      (Feature := Feature) testFeature) := by
  exact (lg21HiddenAccessStudentBase_measurable testFeature).prodMk
    (lg21HiddenAccessStudentScore_measurable testFeature)

/-- The semantic score-action event "withhold" in the actual `(base, score)`
decision space. -/
def lg21HiddenAccessBaseScoreNoReportSet
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool) :
    Set ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) :=
  {profile | reportDecision profile.1 profile.2 = false}

theorem lg21HiddenAccessBaseScoreNoReportSet_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (hreportDecision : Measurable (fun profile :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      reportDecision profile.1 profile.2)) :
    MeasurableSet
      (lg21HiddenAccessBaseScoreNoReportSet testFeature reportDecision) := by
  exact (measurableSet_singleton false).preimage hreportDecision

/-- Conditioning the literal population on positive access and then observing
`(base, score)` is exactly the primitive source law mapped to those same
coordinates. -/
theorem lg21HiddenAccessAccessBaseScoreLaw_eq_primitiveBaseScoreLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature) :
    lg21HiddenAccessAccessBaseScoreLaw M testFeature =
      (lg21ContinuousGaussianStudentPrimitiveLaw M).map
        (lg21HiddenAccessPrimitiveBaseScoreObservation testFeature) := by
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let primitiveLaw := lg21ContinuousGaussianStudentPrimitiveLaw M
  let fullObservation : Bool × (ℝ × (Feature → ℝ)) →
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
    fun student =>
      (lg21HiddenAccessStudentBase testFeature student.2,
        lg21HiddenAccessStudentScore testFeature student.2)
  let primitiveObservation : ℝ × (Feature → ℝ) →
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
    lg21HiddenAccessPrimitiveBaseScoreObservation testFeature
  have hprimitiveObservation : Measurable primitiveObservation := by
    exact lg21HiddenAccessPrimitiveBaseScoreObservation_measurable testFeature
  calc
    lg21HiddenAccessAccessBaseScoreLaw M testFeature =
        accessLaw.map fullObservation := by rfl
    _ = (accessLaw.map Prod.snd).map primitiveObservation := by
      exact (Measure.map_map hprimitiveObservation measurable_snd).symm
    _ = primitiveLaw.map primitiveObservation := by
      rw [lg21ContinuousGaussianAccessPopulation_map_student_eq M haccess]
    _ = (lg21ContinuousGaussianStudentPrimitiveLaw M).map
        (lg21HiddenAccessPrimitiveBaseScoreObservation testFeature) := by
      rfl

/-- The actual `Z = 1` score-action withholding mass is exactly the primitive
source mass of the same semantic event. -/
theorem lg21HiddenAccessAccessBaseScoreLaw_noReport_mass_eq_primitive
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (hreportDecision : Measurable (fun profile :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      reportDecision profile.1 profile.2)) :
    lg21HiddenAccessAccessBaseScoreLaw M testFeature
        (lg21HiddenAccessBaseScoreNoReportSet testFeature reportDecision) =
      lg21ContinuousGaussianStudentPrimitiveLaw M
        (lg21HiddenAccessStudentNoReportEvent testFeature reportDecision) := by
  rw [lg21HiddenAccessAccessBaseScoreLaw_eq_primitiveBaseScoreLaw M haccess testFeature]
  rw [Measure.map_apply
    (lg21HiddenAccessPrimitiveBaseScoreObservation_measurable testFeature)
    (lg21HiddenAccessBaseScoreNoReportSet_measurable testFeature
      reportDecision hreportDecision)]
  rfl

/-- Exact literal-population mass of access students who withhold a score.
The result uses the actual score-action event and no cutoff representation. -/
theorem lg21ContinuousGaussianPopulation_hiddenAccess_accessNoReport_mass_eq
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (hreportDecision : Measurable (fun profile :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      reportDecision profile.1 profile.2)) :
    lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessAccessNoReportEvent testFeature reportDecision) =
      M.accessLaw ({true} : Set Bool) *
        lg21HiddenAccessAccessBaseScoreLaw M testFeature
          (lg21HiddenAccessBaseScoreNoReportSet testFeature reportDecision) := by
  calc
    lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessAccessNoReportEvent testFeature reportDecision) =
      M.accessLaw ({true} : Set Bool) *
        lg21ContinuousGaussianStudentPrimitiveLaw M
          (lg21HiddenAccessStudentNoReportEvent testFeature reportDecision) := by
        rw [lg21HiddenAccessAccessNoReportEvent_eq_true_rectangle,
          lg21ContinuousGaussianPopulation_access_student_factorization]
    _ = M.accessLaw ({true} : Set Bool) *
        lg21HiddenAccessAccessBaseScoreLaw M testFeature
          (lg21HiddenAccessBaseScoreNoReportSet testFeature reportDecision) := by
        rw [lg21HiddenAccessAccessBaseScoreLaw_noReport_mass_eq_primitive
          M haccess testFeature reportDecision hreportDecision]

/-- A positive withholding set under the actual access score-action law has
positive literal population mass. -/
theorem lg21ContinuousGaussianPopulation_hiddenAccess_accessNoReport_positive_of_baseScore
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (hreportDecision : Measurable (fun profile :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      reportDecision profile.1 profile.2))
    (hwithhold : 0 < lg21HiddenAccessAccessBaseScoreLaw M testFeature
      (lg21HiddenAccessBaseScoreNoReportSet testFeature reportDecision)) :
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportEvent testFeature reportDecision) := by
  rw [lg21ContinuousGaussianPopulation_hiddenAccess_accessNoReport_mass_eq
    M haccess testFeature reportDecision hreportDecision]
  exact ENNReal.mul_pos (ne_of_gt haccess) (ne_of_gt hwithhold)

/-- If the literal access-withholding event has zero mass, the actual
positive-access `(base, score)` action is report-a.e.  This is the direction
used to turn a semantic no-withholding conclusion into a literal one. -/
theorem lg21HiddenAccess_allReport_ae_of_accessNoReport_mass_zero
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (hreportDecision : Measurable (fun profile :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      reportDecision profile.1 profile.2))
    (hzero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportEvent testFeature reportDecision) = 0) :
    ∀ᵐ profile ∂lg21HiddenAccessAccessBaseScoreLaw M testFeature,
      reportDecision profile.1 profile.2 = true := by
  have hscoreZero : lg21HiddenAccessAccessBaseScoreLaw M testFeature
      (lg21HiddenAccessBaseScoreNoReportSet testFeature reportDecision) = 0 := by
    rw [lg21ContinuousGaussianPopulation_hiddenAccess_accessNoReport_mass_eq
      M haccess testFeature reportDecision hreportDecision] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (ne_of_gt haccess)
  have hbadSet :
      {profile : (LG21NonTestFeature Feature testFeature → ℝ) × ℝ |
        ¬ reportDecision profile.1 profile.2 = true} =
        lg21HiddenAccessBaseScoreNoReportSet testFeature reportDecision := by
    ext profile
    cases haction : reportDecision profile.1 profile.2 <;> simp [haction,
      lg21HiddenAccessBaseScoreNoReportSet]
  rw [ae_iff, hbadSet]
  exact hscoreZero

/-- Conversely, any failure of report-a.e. under the literal positive-access
score-action law has positive literal access-withholding mass. -/
theorem lg21ContinuousGaussianPopulation_hiddenAccess_accessNoReport_positive_of_not_allReport_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (hreportDecision : Measurable (fun profile :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      reportDecision profile.1 profile.2))
    (hnotAllReport : ¬ ∀ᵐ profile ∂lg21HiddenAccessAccessBaseScoreLaw M testFeature,
      reportDecision profile.1 profile.2 = true) :
    0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportEvent testFeature reportDecision) := by
  apply lg21ContinuousGaussianPopulation_hiddenAccess_accessNoReport_positive_of_baseScore
    M haccess testFeature reportDecision hreportDecision
  by_contra hnotPositive
  have hzero : lg21HiddenAccessAccessBaseScoreLaw M testFeature
      (lg21HiddenAccessBaseScoreNoReportSet testFeature reportDecision) = 0 :=
    bot_unique (le_of_not_gt hnotPositive)
  apply hnotAllReport
  have hbadSet :
      {profile : (LG21NonTestFeature Feature testFeature → ℝ) × ℝ |
        ¬ reportDecision profile.1 profile.2 = true} =
        lg21HiddenAccessBaseScoreNoReportSet testFeature reportDecision := by
    ext profile
    cases haction : reportDecision profile.1 profile.2 <;> simp [haction,
      lg21HiddenAccessBaseScoreNoReportSet]
  rw [ae_iff, hbadSet]
  exact hzero

/-- Under the approved a.e. reading of the pre-score action, literal `X = 0`
mass has the same two-component source decomposition as in the pointwise
presentation.  The only discarded states are the null actual access/no-take
event; no action is changed on a positive-mass population. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.hiddenAccess_noReport_mass_eq_after_allTake_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0) :
    lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessOptionalNoReportEvent testFeature E.takeDecision E.reportDecision) =
      M.accessLaw ({false} : Set Bool) *
          lg21ContinuousGaussianStudentPrimitiveLaw M Set.univ +
        M.accessLaw ({true} : Set Bool) *
          lg21HiddenAccessAccessBaseScoreLaw M testFeature
            (lg21HiddenAccessBaseScoreNoReportSet testFeature E.reportDecision) := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let noReport := lg21HiddenAccessOptionalNoReportEvent testFeature
    E.takeDecision E.reportDecision
  let noAccess := lg21HiddenAccessNoAccessEvent (Feature := Feature)
  let accessNoReport := lg21HiddenAccessAccessNoReportEvent testFeature E.reportDecision
  have hactiveNull : ∀ᵐ student ∂rawLaw, student ∉ E.activeNoTakeEvent := by
    rw [ae_iff]
    simpa [rawLaw] using hactiveNoTakeZero
  have hsets : noReport =ᵐ[rawLaw] (Set.union noAccess accessNoReport) := by
    filter_upwards [hactiveNull] with student hnot
    rcases student with ⟨access, primitive⟩
    cases access with
    | false =>
        apply propext
        change
          lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
              E.reportDecision (false, primitive) = false ↔
            (false = false ∨ false = true ∧
              lg21HiddenAccessStudentReport testFeature E.reportDecision primitive = false)
        simp [lg21HiddenAccessOptionalObservedAction]
    | true =>
        by_cases htake :
          lg21HiddenAccessStudentTake testFeature E.takeDecision primitive = true
        · apply propext
          change
            lg21HiddenAccessOptionalObservedAction testFeature E.takeDecision
                E.reportDecision (true, primitive) = false ↔
              (true = false ∨ true = true ∧
                lg21HiddenAccessStudentReport testFeature E.reportDecision primitive = false)
          simp [lg21HiddenAccessOptionalObservedAction, htake]
        · have htakeFalse :
            lg21HiddenAccessStudentTake testFeature E.takeDecision primitive = false := by
            cases htakeAction :
                lg21HiddenAccessStudentTake testFeature E.takeDecision primitive <;>
              simp_all
          exact (hnot (by
            simp [LG21HiddenAccessLiteralSourceEquilibriumAE.activeNoTakeEvent,
              htakeFalse])).elim
  have hdisjoint : Disjoint noAccess accessNoReport := by
    apply Set.disjoint_left.2
    rintro ⟨access, primitive⟩ hfalse htrue
    change access = false at hfalse
    change access = true ∧ _ at htrue
    simp_all
  have haccessNoReportMeasurable : MeasurableSet accessNoReport := by
    change MeasurableSet
      (lg21HiddenAccessAccessNoReportEvent testFeature E.reportDecision)
    rw [lg21HiddenAccessAccessNoReportEvent_eq_true_rectangle]
    exact (measurableSet_singleton true).prod
      (lg21HiddenAccessStudentNoReportEvent_measurable testFeature E.reportDecision
        E.reportDecision_measurable)
  calc
    lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessOptionalNoReportEvent testFeature E.takeDecision E.reportDecision) =
      rawLaw noReport := by rfl
    _ = rawLaw (noAccess ∪ accessNoReport) := measure_congr hsets
    _ = rawLaw noAccess + rawLaw accessNoReport := by
      exact MeasureTheory.measure_union hdisjoint haccessNoReportMeasurable
    _ = M.accessLaw ({false} : Set Bool) *
          lg21ContinuousGaussianStudentPrimitiveLaw M Set.univ +
        M.accessLaw ({true} : Set Bool) *
          lg21ContinuousGaussianStudentPrimitiveLaw M
            (lg21HiddenAccessStudentNoReportEvent testFeature E.reportDecision) := by
      rw [show noAccess = lg21HiddenAccessNoAccessEvent (Feature := Feature) by rfl,
        show accessNoReport =
          lg21HiddenAccessAccessNoReportEvent testFeature E.reportDecision by rfl,
        lg21HiddenAccessNoAccessEvent_eq_false_rectangle,
        lg21HiddenAccessAccessNoReportEvent_eq_true_rectangle,
        lg21ContinuousGaussianPopulation_access_student_factorization,
        lg21ContinuousGaussianPopulation_access_student_factorization]
    _ = M.accessLaw ({false} : Set Bool) *
          lg21ContinuousGaussianStudentPrimitiveLaw M Set.univ +
        M.accessLaw ({true} : Set Bool) *
          lg21HiddenAccessAccessBaseScoreLaw M testFeature
            (lg21HiddenAccessBaseScoreNoReportSet testFeature E.reportDecision) := by
      rw [← lg21HiddenAccessAccessBaseScoreLaw_noReport_mass_eq_primitive
        M E.access_positive testFeature E.reportDecision E.reportDecision_measurable]

end

end LG21TestOptionalPolicies
