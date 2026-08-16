import LG21TestOptionalPolicies.ObservedAccessSourceConditionalKernel

/-!
# Sequential action carrier for observed-access LG21 protocols

The source has two distinct actions for students with observed access: `Y`,
whether to take before seeing the test score, and `X`, whether to report after
seeing it.  This carrier keeps their timing and the complete observed action
history explicit.  In particular, `X = 0` is not treated as a score-only event
until all-taking has been proved.

The declarations here are source-model plumbing, not paper-facing credit.  A
future bridge must instantiate the carrier from the literal source population
and Definition 1 equilibrium; it cannot substitute an arbitrary score rule for
the pre-score action.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory
open ProbabilityTheory

namespace LG21ObservedAccessSourceConditionalKernel

variable {Ω Base : Type*} [MeasurableSpace Ω] [MeasurableSpace Base]

/--
Literal sequential actions on the access-conditioned source population.

`take` is determined before test noise from `(base, skill)`, while `report` is
determined after the score from `(base, score)`.  The observed report action is
the feasible conjunction `X = Y && r`.  The equations are fields rather than
names or comments so that later PBO conditioning proofs must retain both
action stages.
-/
structure ObservedAccessSequentialActions
    (M : LG21ObservedAccessSourceConditionalKernel Ω Base) where
  takeDecision : Base → ℝ → Bool
  takeDecision_measurable :
    Measurable (fun pair : Base × ℝ => takeDecision pair.1 pair.2)
  reportDecision : Base → ℝ → Bool
  reportDecision_measurable :
    Measurable (fun pair : Base × ℝ => reportDecision pair.1 pair.2)
  take : Ω → Bool
  report : Ω → Bool
  observedReport : Ω → Bool
  take_eq_source_timing :
    ∀ ω, take ω = takeDecision (M.base ω) (M.skill ω)
  report_eq_source_timing :
    ∀ ω, report ω = reportDecision (M.base ω) (M.score ω)
  observedReport_eq_source_actions :
    ∀ ω, observedReport ω = (take ω && report ω)

namespace ObservedAccessSequentialActions

variable {M : LG21ObservedAccessSourceConditionalKernel Ω Base}

/-- The pre-score taking action is measurable on the literal carrier. -/
theorem take_measurable
    (A : ObservedAccessSequentialActions M) : Measurable A.take := by
  have htiming : A.take = fun ω => A.takeDecision (M.base ω) (M.skill ω) :=
    funext
      (ObservedAccessSequentialActions.take_eq_source_timing A)
  rw [htiming]
  exact A.takeDecision_measurable.comp
    (M.base_measurable.prodMk M.skill_measurable)

/-- The post-score reporting action is measurable on the literal carrier. -/
theorem report_measurable
    (A : ObservedAccessSequentialActions M) : Measurable A.report := by
  have htiming : A.report = fun ω => A.reportDecision (M.base ω) (M.score ω) :=
    funext
      (ObservedAccessSequentialActions.report_eq_source_timing A)
  rw [htiming]
  exact A.reportDecision_measurable.comp
    (M.base_measurable.prodMk M.score_measurable)

/-- The observed action has the source's complete no-report decomposition. -/
theorem observedReport_eq_false_iff
    (A : ObservedAccessSequentialActions M) (ω : Ω) :
    A.observedReport ω = false ↔
      A.take ω = false ∨
        (A.take ω = true ∧
          A.reportDecision (M.base ω) (M.score ω) = false) := by
  rw [ObservedAccessSequentialActions.observedReport_eq_source_actions A ω,
    ObservedAccessSequentialActions.report_eq_source_timing A ω]
  cases A.take ω <;>
    cases A.reportDecision (M.base ω) (M.score ω) <;>
    simp

/--
Once taking is proved almost everywhere, the literal `X = 0` event becomes the
score-selected no-report event almost everywhere.  This is the only point at
which the earlier taking action may be removed from the optional PBO carrier.
-/
theorem observedNoReport_ae_eq_scoreNoReport_of_all_take
    (A : ObservedAccessSequentialActions M)
    (hallTake : ∀ᵐ ω ∂M.populationLaw, A.take ω = true) :
    {ω | A.observedReport ω = false} =ᵐ[M.populationLaw]
      {ω | A.reportDecision (M.base ω) (M.score ω) = false} := by
  filter_upwards [hallTake] with ω htake
  apply propext
  change A.observedReport ω = false ↔
    A.reportDecision (M.base ω) (M.score ω) = false
  rw [ObservedAccessSequentialActions.observedReport_eq_source_actions A ω,
    htake, ObservedAccessSequentialActions.report_eq_source_timing A ω]
  simp

/--
The normalized conditional law of the actual `X = 0` cohort agrees with the
score-selected law after the all-taking theorem.  No PBO identity is assumed:
this is only the action-history reduction needed before applying an RCD/tower
calculation.
-/
theorem normalizedRestriction_observedNoReport_eq_scoreNoReport_of_all_take
    (A : ObservedAccessSequentialActions M)
    (hallTake : ∀ᵐ ω ∂M.populationLaw, A.take ω = true) :
    lg21NormalizedRestriction M.populationLaw
        {ω | A.observedReport ω = false} =
      lg21NormalizedRestriction M.populationLaw
        {ω | A.reportDecision (M.base ω) (M.score ω) = false} := by
  have heq :=
    ObservedAccessSequentialActions.observedNoReport_ae_eq_scoreNoReport_of_all_take
      A hallTake
  unfold lg21NormalizedRestriction
  rw [measure_congr heq, Measure.restrict_congr_set heq]

/-- Positive mass of the actual no-report action transfers to score selection
only after the all-taking event has been derived. -/
theorem observedNoReport_positive_iff_scoreNoReport_positive_of_all_take
    (A : ObservedAccessSequentialActions M)
    (hallTake : ∀ᵐ ω ∂M.populationLaw, A.take ω = true) :
    0 < M.populationLaw {ω | A.observedReport ω = false} ↔
      0 < M.populationLaw
        {ω | A.reportDecision (M.base ω) (M.score ω) = false} := by
  rw [measure_congr
    (ObservedAccessSequentialActions.observedNoReport_ae_eq_scoreNoReport_of_all_take
      A hallTake)]

end ObservedAccessSequentialActions

end LG21ObservedAccessSourceConditionalKernel

end

end LG21TestOptionalPolicies
