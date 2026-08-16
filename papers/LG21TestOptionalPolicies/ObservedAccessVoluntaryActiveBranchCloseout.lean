import LG21TestOptionalPolicies.ObservedAccessVoluntaryActiveBranchSelection
import LG21TestOptionalPolicies.ObservedAccessLemma41LiteralSourceCloseout

/-!
# Lemma 4.1 closeout under the explicit voluntary selection

This module packages the three observed-access protocol conclusions at their
actual decision times. The optional and report-required conclusions use the
visible fibrewise active-branch selection from the source's unraveling
interpretation. The mandatory protocol follows directly from feasibility.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory

/-- The behavioral content of Lemma 4.1 after making the voluntary
active-branch/unravelling selection explicit. -/
structure LG21ObservedAccessLemma41ActiveBranchCloseout
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
    (optional : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
      M haccess testFeature)
    (reportRequired : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ) : Prop where
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

/-- Source-facing Lemma 4.1 behavior under the declared fibrewise
active-branch selection. The result has no finite null-branch value, cutoff,
or hidden candidate label as an input. -/
theorem lg21ContinuousGaussianAccessPopulation_lemma4_1_all_protocols_of_activeBranchSelection
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) (testFeature : Feature)
    (hpriorVariance : 0 < (M.priorVariance : ℝ))
    (hnonTestNoiseVariance : ∀ feature : LG21NonTestFeature Feature testFeature,
      0 < (M.noiseVariance feature.1 : ℝ))
    (htestNoiseVariance : 0 < (M.noiseVariance testFeature : ℝ))
    (mandatory : LG21MandatoryGivenAccessLiteralSourceEquilibrium M)
    (optional : LG21ObservedAccessOptionalPositiveMassRefinedEquilibrium
      M haccess testFeature)
    (hoptionalSelection : LG21OptionalFibrewiseActiveBranchSelection
      M haccess testFeature optional)
    (reportRequired : LG21ReportRequiredSequentialEquilibriumData ℝ
      (LG21NonTestFeature Feature testFeature -> ℝ) ℝ)
    (hreportRequiredSource :
      letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
        lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
      LG21ReportRequiredPositiveMassRefinedSourceEquilibrium
        (lg21ContinuousGaussianAccessPopulationLaw M)
        (lg21ContinuousPopulationBase testFeature)
        (lg21ContinuousPopulationFeature testFeature)
        (lg21ContinuousPopulationSkill (Feature := Feature)) reportRequired
        (M.noiseVariance testFeature))
    (hreportRequiredSelection :
      LG21ReportRequiredFibrewiseActiveBranchSelection
        M haccess testFeature reportRequired hreportRequiredSource) :
    LG21ObservedAccessLemma41ActiveBranchCloseout
      M haccess testFeature mandatory optional reportRequired := by
  letI : IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) :=
    lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  refine ⟨?_, ?_, ?_⟩
  · exact lg21MandatoryGivenAccess_accessPopulation_ae_takeAndReport
      M haccess mandatory.action mandatory.feasible
  · exact
      lg21ContinuousGaussianAccessPopulation_optional_allTakeAllReport_of_fibrewiseActiveBranchSelection
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance optional hoptionalSelection
  · exact
      lg21ContinuousGaussianAccessPopulation_reportRequired_allTake_of_fibrewiseActiveBranchSelection
        M haccess testFeature hpriorVariance hnonTestNoiseVariance
        htestNoiseVariance reportRequired hreportRequiredSource
        hreportRequiredSelection

end

end LG21TestOptionalPolicies
