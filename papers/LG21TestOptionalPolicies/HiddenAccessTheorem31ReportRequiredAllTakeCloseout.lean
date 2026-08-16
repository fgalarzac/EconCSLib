import LG21TestOptionalPolicies.HiddenAccessTheorem31AllTakeWithholdingCloseout

/-!
# Report-required all-taking closeout for LG21 Theorem 3.1

In the report-required protocol an access student who takes must report.  The
literal all-taking source argument already proves that a nondegenerate hidden
access population must contain a positive mass of access students who do not
report.  These facts are incompatible, so the all-taking case is unavailable
without assigning a payoff to an off-path history.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open EconCSLib EconCSLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- A literal report-required source equilibrium cannot have all access
students taking almost everywhere.  The contradiction is entirely on-path:
all taking would force a positive literal access-withholding branch, while the
report-required action rule makes that branch empty. -/
theorem LG21HiddenAccessLiteralSourceEquilibriumAE.reportRequired_allTake_contradiction
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    {M : LG21ContinuousGaussianPopulation Feature} {testFeature : Feature}
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hnoAccess : 0 < M.accessLaw {false})
    (hreportRequired : ∀ publicBase score,
      E.reportDecision publicBase score = true)
    (hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0)
    (baseLaw : Measure (LG21NonTestFeature Feature testFeature -> ℝ))
    [IsProbabilityMeasure baseLaw]
    (baseMean : (LG21NonTestFeature Feature testFeature -> ℝ) -> ℝ)
    (hbaseMean : Measurable baseMean)
    (priorVariance : ℝ)
    (hpriorVariance : 0 < priorVariance)
    (hnoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (hsourceFactor :
      (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21HiddenAccessStudentBase testFeature student.2,
            (lg21HiddenAccessStudentScore testFeature student.2,
              lg21ContinuousPopulationSkill student))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean priorVariance (M.noiseVariance testFeature : ℝ)) :
    False := by
  have haccessNoReportEmpty :
      lg21HiddenAccessAccessNoReportEvent testFeature E.reportDecision = ∅ := by
    ext student
    simp [lg21HiddenAccessAccessNoReportEvent,
      lg21HiddenAccessStudentReport, hreportRequired]
  have haccessNoReportZero : lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessAccessNoReportEvent testFeature E.reportDecision) = 0 := by
    rw [haccessNoReportEmpty]
    simp
  have hpositive := E.accessNoReportEvent_positive_of_allTake
    hnoAccess hactiveNoTakeZero baseLaw baseMean hbaseMean priorVariance
    hpriorVariance hnoiseVariance hsourceFactor
  rw [haccessNoReportZero] at hpositive
  exact lt_irrefl 0 hpositive

end

end LG21TestOptionalPolicies
