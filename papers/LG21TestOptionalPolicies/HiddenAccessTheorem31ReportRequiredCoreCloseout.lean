import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredAllTakeCloseout
import LG21TestOptionalPolicies.HiddenAccessTheorem31ReportRequiredLocalTailCloseout

/-!
# Literal report-required core for LG21 Theorem 3.1

This module closes the two degenerate action endpoints for hidden-access
report-required testing.  It uses the literal source PBO at the all-taking
endpoint and literal positive-mass candidate PBOs at the all-no-taking
endpoint.  Neither argument selects a value for an unattained information
set.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open EconCSLib EconCSLib.Probability MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- With report required after taking, the literal hidden-access source
equilibrium has a positive mass of access students who do not take.  If that
mass were zero, all access students would take almost everywhere; the literal
all-taking argument then forces a positive access-withholding branch, which
forced reporting makes empty. -/
theorem lg21HiddenAccess_reportRequired_positiveNoTake_of_literalSource
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hreportRequired : ∀ publicBase score,
      E.reportDecision publicBase score = true) :
    0 < lg21ContinuousGaussianPopulationLaw M E.activeNoTakeEvent := by
  by_contra hnotPositive
  have hactiveNoTakeZero : lg21ContinuousGaussianPopulationLaw M
      E.activeNoTakeEvent = 0 :=
    bot_unique (le_of_not_gt hnotPositive)
  rcases
      lg21ContinuousGaussianPopulation_exists_fullBaseGaussian_scoreSkill_factorization
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance with
    ⟨baseLaw, baseMean, baseVariance, hbaseMean,
      hbaseLaw, hbaseVariance, hsourceFactor⟩
  letI : IsProbabilityMeasure baseLaw := hbaseLaw
  have haccessFactor :
      (lg21ContinuousGaussianAccessPopulationLaw M).map
        (fun student =>
          (lg21HiddenAccessStudentBase testFeature student.2,
            (lg21HiddenAccessStudentScore testFeature student.2,
              lg21ContinuousPopulationSkill student))) =
        baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) := by
    calc
      (lg21ContinuousGaussianAccessPopulationLaw M).map
          (fun student =>
            (lg21HiddenAccessStudentBase testFeature student.2,
              (lg21HiddenAccessStudentScore testFeature student.2,
                lg21ContinuousPopulationSkill student))) =
          (lg21ContinuousGaussianPopulationLaw M).map
            (lg21HiddenAccessBaseScoreSkillObservation testFeature) := by
              simpa [lg21HiddenAccessBaseScoreSkillObservation] using
                (lg21HiddenAccess_rawBaseScoreSkillLaw_eq_accessBaseScoreSkillLaw
                  M haccess testFeature).symm
      _ = baseLaw ⊗ₘ gaussianSignalJointKernel
          baseMean hbaseMean baseVariance (M.noiseVariance testFeature : ℝ) :=
        hsourceFactor
  exact E.reportRequired_allTake_contradiction hnoAccess hreportRequired
    hactiveNoTakeZero baseLaw baseMean hbaseMean baseVariance hbaseVariance
    htestNoiseVariance haccessFactor

/-- Literal stability against positive-mass report-required local entries
also rules out the all-no-taking endpoint.  The candidate is constructed on
the entire public-base region, so this conclusion does not presume a named
threshold or a positive individual base fibre. -/
theorem lg21HiddenAccess_reportRequired_positiveTake_of_literalSourceStability
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (E : LG21HiddenAccessLiteralSourceEquilibriumAE M testFeature)
    (hstable : LG21ReportRequiredStableAgainstLocalTailEntry
      (M := M) (testFeature := testFeature) E.takeDecision) :
    0 < lg21ContinuousGaussianPopulationLaw M
      {student | student.1 = true ∧
        E.takeDecision (lg21ContinuousPopulationSkill student)
          (lg21HiddenAccessStudentBase testFeature student.2) = true} := by
  by_contra hnotPositive
  let currentTakeEvent : Set (Bool × (ℝ × (Feature -> ℝ))) :=
    {student | student.1 = true ∧
      E.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21HiddenAccessStudentBase testFeature student.2) = true}
  have hcurrentTakeZero : lg21ContinuousGaussianPopulationLaw M
      currentTakeEvent = 0 := by
    exact bot_unique (le_of_not_gt (by simpa [currentTakeEvent] using hnotPositive))
  exact
    (lg21ReportRequired_not_stable_of_globalCurrentTake_zero_of_source
      M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
      htestNoiseVariance E.takeDecision E.takeDecision_measurable
      hcurrentTakeZero) hstable

end

end LG21TestOptionalPolicies
