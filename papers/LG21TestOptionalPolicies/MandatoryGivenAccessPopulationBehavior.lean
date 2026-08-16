import LG21TestOptionalPolicies.ContinuousAccessConditionedPopulation

/-!
# Mandatory-given-access behavior on the literal LG21 population

This module is deliberately source-neutral mathematical support.  It connects
the literal Boolean access coordinate of `LG21ContinuousGaussianPopulation`
to Definition 1's feasibility predicate for the mandatory protocol.  Given
only pointwise feasibility, that protocol forces `(Z, Y, X) = (1, 1, 1)` on
access students and `(0, 0, 0)` on non-access students.  The final theorem
then transfers the forced access behavior to the normalized positive-access
population.

No posterior identity, PBO claim, equilibrium-consistency claim, or
paper-facing theorem is made here.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory
open ProbabilityTheory

/-- Interpret the literal Boolean source access coordinate as the action-model status. -/
def lg21ContinuousPopulationAccessStatus
    {Feature : Type*} : Bool × (ℝ × (Feature → ℝ)) → LG21AccessStatus :=
  fun student =>
    if lg21ContinuousPopulationAccess student = true then
      LG21AccessStatus.access
    else
      LG21AccessStatus.noAccess

theorem lg21ContinuousPopulationAccessStatus_eq_access
    {Feature : Type*} (student : Bool × (ℝ × (Feature → ℝ)))
    (haccess : lg21ContinuousPopulationAccess student = true) :
    lg21ContinuousPopulationAccessStatus student = LG21AccessStatus.access := by
  simp [lg21ContinuousPopulationAccessStatus, haccess]

theorem lg21ContinuousPopulationAccessStatus_eq_noAccess
    {Feature : Type*} (student : Bool × (ℝ × (Feature → ℝ)))
    (haccess : lg21ContinuousPopulationAccess student = false) :
    lg21ContinuousPopulationAccessStatus student = LG21AccessStatus.noAccess := by
  simp [lg21ContinuousPopulationAccessStatus, haccess]

/--
Definition 1 feasibility under `Z = Y = X` determines the literal action at
every source-population point.  This is a feasibility consequence only: it
does not choose an estimator or establish an equilibrium.
-/
theorem lg21MandatoryGivenAccess_feasibleAction_forces_action
    {Feature : Type*}
    (action : Bool × (ℝ × (Feature → ℝ)) → LG21AccessAction)
    (hfeasible : ∀ student,
      LG21RequirementPolicy.feasibleAction
        LG21RequirementPolicy.reportRequiredGivenAccess
        (lg21ContinuousPopulationAccessStatus student) (action student)) :
    ∀ student,
      action student =
        if lg21ContinuousPopulationAccess student = true then
          LG21AccessAction.takeAndReport
        else
          LG21AccessAction.noTake := by
  intro student
  by_cases haccess : lg21ContinuousPopulationAccess student = true
  · have hstatus :
        lg21ContinuousPopulationAccessStatus student = LG21AccessStatus.access :=
      lg21ContinuousPopulationAccessStatus_eq_access student haccess
    have haction := hfeasible student
    rw [hstatus] at haction
    have hforced : action student = LG21AccessAction.takeAndReport :=
      (LG21RequirementPolicy.feasibleAction_access_reportRequiredGivenAccess_iff
        (action student)).mp haction
    rw [hforced, if_pos haccess]
  · have hnotAccess : lg21ContinuousPopulationAccess student = false := by
      cases hvalue : lg21ContinuousPopulationAccess student
      · rfl
      · exact False.elim (haccess hvalue)
    have hstatus :
        lg21ContinuousPopulationAccessStatus student = LG21AccessStatus.noAccess :=
      lg21ContinuousPopulationAccessStatus_eq_noAccess student hnotAccess
    have haction := hfeasible student
    rw [hstatus] at haction
    have hforced : action student = LG21AccessAction.noTake :=
      (LG21RequirementPolicy.feasibleAction_noAccess_iff
        LG21RequirementPolicy.reportRequiredGivenAccess (action student)).mp haction
    rw [hforced, if_neg haccess]

/-- The forced literal action realizes `Z = Y = X` pointwise. -/
theorem lg21MandatoryGivenAccess_feasibleAction_forces_ZYX
    {Feature : Type*}
    (action : Bool × (ℝ × (Feature → ℝ)) → LG21AccessAction)
    (hfeasible : ∀ student,
      LG21RequirementPolicy.feasibleAction
        LG21RequirementPolicy.reportRequiredGivenAccess
        (lg21ContinuousPopulationAccessStatus student) (action student)) :
    ∀ student,
      (action student).takesTest = lg21ContinuousPopulationAccess student ∧
        (action student).reportsScore = lg21ContinuousPopulationAccess student := by
  intro student
  rw [lg21MandatoryGivenAccess_feasibleAction_forces_action action hfeasible student]
  cases haccess : lg21ContinuousPopulationAccess student <;>
    simp [LG21AccessAction.takeAndReport, LG21AccessAction.noTake]

/-- The positive-access normalized population is a probability law supported on literal `Z = 1`. -/
theorem lg21ContinuousGaussianAccessPopulationLaw_isProbability_and_ae_access
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true}) :
    IsProbabilityMeasure (lg21ContinuousGaussianAccessPopulationLaw M) ∧
      ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
        lg21ContinuousPopulationAccess student = true := by
  constructor
  · exact lg21ContinuousGaussianAccessPopulationLaw_isProbability M haccess
  · unfold lg21ContinuousGaussianAccessPopulationLaw lg21NormalizedRestriction
    exact Measure.ae_smul_measure
      (ae_restrict_mem
        (MeasurableSet.preimage (MeasurableSet.singleton true) measurable_fst)) _

/--
Under pointwise Definition 1 feasibility for the mandatory protocol, every
student in the literal positive-access conditional population takes and
reports almost surely.  This is the population-level forced-action bridge;
it contains no PBO or estimator-consistency premise.
-/
theorem lg21MandatoryGivenAccess_accessPopulation_ae_takeAndReport
    {Feature : Type*} [Fintype Feature]
    (M : LG21ContinuousGaussianPopulation Feature)
    (haccess : 0 < M.accessLaw {true})
    (action : Bool × (ℝ × (Feature → ℝ)) → LG21AccessAction)
    (hfeasible : ∀ student,
      LG21RequirementPolicy.feasibleAction
        LG21RequirementPolicy.reportRequiredGivenAccess
        (lg21ContinuousPopulationAccessStatus student) (action student)) :
    ∀ᵐ student ∂lg21ContinuousGaussianAccessPopulationLaw M,
      action student = LG21AccessAction.takeAndReport := by
  filter_upwards [
    (lg21ContinuousGaussianAccessPopulationLaw_isProbability_and_ae_access M haccess).2] with
      student haccess
  rw [lg21MandatoryGivenAccess_feasibleAction_forces_action action hfeasible student,
    if_pos haccess]

end

end LG21TestOptionalPolicies
