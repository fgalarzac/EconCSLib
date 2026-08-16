import LG21TestOptionalPolicies.HiddenAccessTheorem31LiteralSourceEquilibrium

/-!
# Transport of the literal optional all-taking conclusion

The source closeout derives all-taking as a raw-population null-event result.
This module transports that result to the positive-access decision law without
choosing a pointwise representative on the discarded null set.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- A null raw active-no-take event is exactly an a.e. all-taking conclusion
under the literal positive-access population. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.access_take_ae_of_activeNoTake_measure_zero
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hactive : lg21ContinuousGaussianPopulationLaw M E.activeNoTakeEvent = 0) :
    ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      E.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21HiddenAccessStudentBase testFeature student.2) = true := by
  let rawLaw := lg21ContinuousGaussianPopulationLaw M
  let accessEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true}
  let accessLaw := lg21ContinuousGaussianAccessPopulationLaw M
  let noTakeEvent := E.accessNoTakeEvent
  letI : IsProbabilityMeasure rawLaw := by
    simpa [rawLaw] using lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  have hnoTakeMeasurable : MeasurableSet noTakeEvent := by
    simpa [noTakeEvent] using E.accessNoTakeEvent_measurable
  have hactiveEq : E.activeNoTakeEvent = noTakeEvent ∩ accessEvent := by
    ext student
    simp [LG21HiddenAccessLiteralSourceEquilibriumAE.activeNoTakeEvent,
      LG21HiddenAccessLiteralSourceEquilibriumAE.accessNoTakeEvent,
      noTakeEvent, accessEvent, and_comm]
  have hnormalizedZero :
      lg21NormalizedRestriction rawLaw accessEvent noTakeEvent = 0 := by
    rw [lg21NormalizedRestriction_apply rawLaw hnoTakeMeasurable]
    have hintersection : rawLaw (noTakeEvent ∩ accessEvent) = 0 := by
      simpa [hactiveEq] using hactive
    rw [hintersection]
    simp
  have hnoTakeZero : accessLaw noTakeEvent = 0 := by
    simpa [accessLaw, lg21ContinuousGaussianAccessPopulationLaw] using
      hnormalizedZero
  have hbad :
      {student : Bool × (ℝ × (Feature -> ℝ)) |
        ¬ E.takeDecision (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = true} = noTakeEvent := by
    ext student
    cases htake : E.takeDecision (lg21ContinuousPopulationSkill student)
      (lg21HiddenAccessStudentBase testFeature student.2) <;>
      simp [noTakeEvent,
        LG21HiddenAccessLiteralSourceEquilibriumAE.accessNoTakeEvent,
        lg21HiddenAccessStudentTake, lg21ContinuousPopulationSkill]
  rw [ae_iff, hbad]
  exact hnoTakeZero

end

end LG21TestOptionalPolicies
