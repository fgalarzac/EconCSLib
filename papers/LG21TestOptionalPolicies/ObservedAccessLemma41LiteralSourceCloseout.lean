import LG21TestOptionalPolicies.MandatoryGivenAccessLiteralSourceCloseout
import LG21TestOptionalPolicies.ObservedAccessOptionalSourceCloseout
import LG21TestOptionalPolicies.ObservedAccessOptionalSourceTimedCloseout
import LG21TestOptionalPolicies.ReportRequiredLiteralSelectedGaussianBridge

/-!
# Literal source closeout for LG21 Lemma 4.1

This module combines the three source-timed protocol endpoints on the same
literal positive-access Gaussian population.  Each protocol keeps its actual
action timing:

* mandatory-given-access has a feasible literal action;
* optional reporting has separate pre-score taking and post-score reporting;
* report-required testing has only the pre-score taking decision because
  taking itself entails reporting.

The result uses the inspectable literal source carriers.  It does not expose
the legacy `estimationConsistent` placeholder as an input or assign a payoff
to an unattained action branch.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory

/-- The concrete source action carrier for mandatory-given-access testing.
Feasibility is the complete behavioral requirement in that protocol. -/
structure LG21MandatoryGivenAccessLiteralSourceEquilibrium
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature) where
  action : Bool × (ℝ × (Feature → ℝ)) → LG21AccessAction
  feasible : ∀ student,
    LG21RequirementPolicy.feasibleAction
      LG21RequirementPolicy.reportRequiredGivenAccess
      (lg21ContinuousPopulationAccessStatus student) (action student)

/-- The behavioral conclusion of Lemma 4.1 under its three literal
observed-access requirement protocols.  The last field is all-taking only,
because reporting is required whenever a student takes in that protocol. -/
structure LG21ObservedAccessLemma41LiteralSourceCloseout
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
    (optional : LG21ObservedAccessOptionalLiteralSourceEquilibrium
      M haccess testFeature)
    (reportRequired : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature → ℝ) ℝ) : Prop where
  mandatory_all_take_and_report_ae :
    ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      mandatory.action student = LG21AccessAction.takeAndReport
  optional_all_take_and_report_ae :
    ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      optional.data.takeDecision (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase testFeature student) = true ∧
        optional.data.reportDecision
          (lg21ContinuousPopulationBase testFeature student)
          (lg21ContinuousPopulationFeature testFeature student) = true
  reportRequired_all_take_ae :
    ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      reportRequired.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true

/--
Literal source-facing Lemma 4.1 endpoint for all three observed-access
protocols.  The optional and report-required branches use their separate,
inspectable source equilibrium carriers and positive-mass candidate-stability
conditions.  No conditional-route theorem, standalone consistency placeholder,
or off-path PBO value is supplied to this result.
-/
theorem lg21ContinuousGaussianAccessPopulation_lemma4_1_all_protocols_of_literalSource
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false})
    (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
    (optional : LG21ObservedAccessOptionalLiteralSourceEquilibrium
      M haccess testFeature)
    (reportRequired : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature → ℝ) ℝ)
    (hreportRequiredTestLaw : ∀ latentSkill publicBase,
      reportRequired.testLaw latentSkill publicBase = gaussianReal latentSkill
        ((M.noiseVariance testFeature : ℝ).toNNReal)) :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    ∀ (reportRequiredSource : LG21FullPublicReportRequiredSourceEquilibrium
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      lg21ContinuousPopulationSkill reportRequired),
      LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        lg21ContinuousPopulationSkill
        (reportRequiredSource.base_measurable.prodMk
          (reportRequiredSource.score_measurable.prodMk
            reportRequiredSource.skill_measurable))
        (fun latentSkill publicBase =>
          reportRequired.takeDecision latentSkill publicBase) →
      LG21ObservedAccessLemma41LiteralSourceCloseout
        M haccess testFeature mandatory optional reportRequired := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  intro reportRequiredSource hreportRequiredStable
  refine ⟨?_, ?_, ?_⟩
  · exact
      (lg21_mandatoryGivenAccess_literal_source_closeout
        M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance mandatory.action mandatory.feasible).1
  · exact
      lg21ContinuousGaussianAccessPopulation_optional_all_take_and_report_ae
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance optional
  · have hnoTakeZero :
        (lg21ContinuousGaussianAccessPopulationLaw M)
          {student | reportRequired.takeDecision
            (lg21ContinuousPopulationSkill student)
            (lg21ContinuousPopulationBase testFeature student) = false} = 0 :=
      lg21ContinuousGaussianAccessPopulation_reportRequired_allTake_of_literalSource
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance reportRequired hreportRequiredTestLaw
        reportRequiredSource hreportRequiredStable
    have htakeBad :
        {student | ¬ reportRequired.takeDecision
          (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase testFeature student) = true} =
        {student | reportRequired.takeDecision
          (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase testFeature student) = false} := by
      ext student
      cases htake : reportRequired.takeDecision
          (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase testFeature student) <;>
        simp [htake]
    rw [ae_iff, htakeBad]
    exact hnoTakeZero

/-- Credit-bearing Lemma 4.1 source carrier with the optional protocol stated
in its literal source-timed form.  It does not route optional reporting
through the legacy generic sequential-equilibrium wrapper. -/
structure LG21ObservedAccessLemma41SourceTimedCloseout
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
    (optional : LG21ObservedAccessOptionalSourceTimedEquilibrium
      M haccess testFeature)
    (reportRequired : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature → ℝ) ℝ) : Prop where
  mandatory_all_take_and_report_ae :
    ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      mandatory.action student = LG21AccessAction.takeAndReport
  optional_all_take_and_report_ae :
    ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      optional.actions.takeDecision (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase testFeature student) = true ∧
        optional.actions.reportDecision
          (lg21ContinuousPopulationBase testFeature student)
          (lg21ContinuousPopulationFeature testFeature student) = true
  reportRequired_all_take_ae :
    ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      reportRequired.takeDecision (lg21ContinuousPopulationSkill student)
        (lg21ContinuousPopulationBase testFeature student) = true

/-- Literal source-facing Lemma 4.1 endpoint whose optional-reporting branch
uses explicit action data, literal actual-branch PBOs, and the two exact
best-response implications used in the proof. -/
theorem lg21ContinuousGaussianAccessPopulation_lemma4_1_all_protocols_of_sourceTimed
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (hnoAccess : 0 < M.accessLaw {false})
    (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
    (optional : LG21ObservedAccessOptionalSourceTimedEquilibrium
      M haccess testFeature)
    (reportRequired : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature → ℝ) ℝ)
    (hreportRequiredTestLaw : ∀ latentSkill publicBase,
      reportRequired.testLaw latentSkill publicBase = gaussianReal latentSkill
        ((M.noiseVariance testFeature : ℝ).toNNReal)) :
    letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
      lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
    ∀ (reportRequiredSource : LG21FullPublicReportRequiredSourceEquilibrium
      (lg21ContinuousGaussianAccessPopulationLaw M)
      (lg21ContinuousPopulationBase testFeature)
      (lg21ContinuousPopulationFeature testFeature)
      lg21ContinuousPopulationSkill reportRequired),
      LG21ReportRequiredSourceStableAgainstPositiveMassLocalRecalibratedEntry
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        lg21ContinuousPopulationSkill
        (reportRequiredSource.base_measurable.prodMk
          (reportRequiredSource.score_measurable.prodMk
            reportRequiredSource.skill_measurable))
        (fun latentSkill publicBase =>
          reportRequired.takeDecision latentSkill publicBase) →
      LG21ObservedAccessLemma41SourceTimedCloseout
        M haccess testFeature mandatory optional reportRequired := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  intro reportRequiredSource hreportRequiredStable
  refine ⟨?_, ?_, ?_⟩
  · exact
      (lg21_mandatoryGivenAccess_literal_source_closeout
        M haccess hnoAccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance mandatory.action mandatory.feasible).1
  · exact
      lg21ContinuousGaussianAccessPopulation_optional_all_take_and_report_ae_of_sourceTimed
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance optional
  · have hnoTakeZero :
        (lg21ContinuousGaussianAccessPopulationLaw M)
          {student | reportRequired.takeDecision
            (lg21ContinuousPopulationSkill student)
            (lg21ContinuousPopulationBase testFeature student) = false} = 0 :=
      lg21ContinuousGaussianAccessPopulation_reportRequired_allTake_of_literalSource
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance reportRequired hreportRequiredTestLaw
        reportRequiredSource hreportRequiredStable
    have htakeBad :
        {student | ¬ reportRequired.takeDecision
          (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase testFeature student) = true} =
        {student | reportRequired.takeDecision
          (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase testFeature student) = false} := by
      ext student
      cases htake : reportRequired.takeDecision
          (lg21ContinuousPopulationSkill student)
          (lg21ContinuousPopulationBase testFeature student) <;>
        simp [htake]
    rw [ae_iff, htakeBad]
    exact hnoTakeZero

end

end LG21TestOptionalPolicies
