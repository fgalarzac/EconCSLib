import LG21TestOptionalPolicies.TwoSidedPositiveMassClosedCandidateProfile
import LG21TestOptionalPolicies.ObservedAccessOptionalSourceTimedCloseout
import LG21TestOptionalPolicies.SequentialEquilibrium

/-!
# Source-timed adapters for two-sided positive-mass candidates

`TwoSidedPositiveMassClosedCandidateProfile` deliberately abstracts over the
meaning of its two Boolean branches.  This module supplies the literal LG21
action meanings without supplying the economic closure proof which remains
open for Section 4.

For optional testing, the true branch is the complete observed action
``take && report``.  Its false branch therefore contains both students who
did not take and students who took but withheld their score.  For
report-required testing, the true branch is the pre-score taking action and
the false branch is no-take.  The two adapters keep those interpretations
separate, so a score-only argument cannot silently replace the optional
pre-score action.

The behavioral predicates are deliberately parameters.  A source-facing
proof must provide literal member response and two-sided outsider closure;
this adapter only ensures that such a proof is applied to the source-timed
actions, observations, and output channels.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace PositiveMassPBOCandidateProfile

variable
    {Omega Base : Type*}
    [MeasurableSpace Omega] [MeasurableSpace Base]
    {mu : Measure Omega} [IsFiniteMeasure mu] {skill : Omega -> ℝ}

abbrev LG21SourceTimedCandidate : Type _ :=
  Candidate (ReportInfo := Base × ℝ) (NoReportInfo := Base)
    (μ := mu) (skill := skill)

/--
The semantic (rather than merely named) behavioral inputs for a literal
two-branch source action.  The source-specific adapter below fixes what the
two branches *are*; a later proof supplies the appropriate response and
strict-gain relations for the protocol and its timing.
-/
structure LG21TwoSidedCandidateBehavior
    (mu : Measure Omega) [IsFiniteMeasure mu] (skill : Omega -> ℝ) where
  report_action_eligible :
    LG21SourceTimedCandidate (Base := Base) (mu := mu) (skill := skill) ->
      Omega -> Prop
  noReport_action_eligible :
    LG21SourceTimedCandidate (Base := Base) (mu := mu) (skill := skill) ->
      Omega -> Prop
  report_member_weak_response :
    (P : LG21SourceTimedCandidate (Base := Base) (mu := mu) (skill := skill)) ->
    (hpositive : 0 < P.reportMass) ->
    PositiveMassBranchPBOCertificate mu skill P.reportBranch
      P.reportObservation P.reportPBO.estimate hpositive -> Omega -> Prop
  noReport_member_weak_response :
    (P : LG21SourceTimedCandidate (Base := Base) (mu := mu) (skill := skill)) ->
    (hpositive : 0 < P.noReportMass) ->
    PositiveMassBranchPBOCertificate mu skill P.noReportBranch
      P.noReportObservation P.noReportPBO.estimate hpositive -> Omega -> Prop
  report_strict_gain :
    (P : LG21SourceTimedCandidate (Base := Base) (mu := mu) (skill := skill)) ->
    (hpositive : 0 < P.reportMass) ->
    PositiveMassBranchPBOCertificate mu skill P.reportBranch
      P.reportObservation P.reportPBO.estimate hpositive -> Omega -> Prop
  noReport_strict_gain :
    (P : LG21SourceTimedCandidate (Base := Base) (mu := mu) (skill := skill)) ->
    (hpositive : 0 < P.noReportMass) ->
    PositiveMassBranchPBOCertificate mu skill P.noReportBranch
      P.noReportObservation P.noReportPBO.estimate hpositive -> Omega -> Prop

/--
The candidate's positive branch is the literal optional full action:
pre-score take followed by post-score report.  This equality prevents the
generic binary carrier from treating the optional no-report cohort as a
score-only selection before all-taking has been proved.
-/
def LG21OptionalCandidateMatchesFullAction
    (base : Omega -> Base) (score : Omega -> ℝ)
    (A : LG21OptionalSourceTimedActions Base)
    (P : LG21SourceTimedCandidate (Base := Base) (mu := mu) (skill := skill)) : Prop :=
  ∀ omega, P.reports omega =
    (A.takeDecision (skill omega) (base omega) &&
      A.reportDecision (base omega) (score omega))

/--
The candidate uses exactly the public observations and output functions of
the optional source protocol.  These equalities do not assert a conditional
mean at a null branch; the generic positive-mass certificate remains the
only route to such a conclusion.
-/
def LG21OptionalCandidateMatchesSourceChannels
    (base : Omega -> Base) (score : Omega -> ℝ)
    (A : LG21OptionalSourceTimedActions Base)
    (P : LG21SourceTimedCandidate (Base := Base) (mu := mu) (skill := skill)) : Prop :=
  P.reportObservation = (fun omega => (base omega, score omega)) ∧
    P.noReportObservation = base ∧
      P.reportPBO.estimate = (fun publicObservation =>
        A.reportedPayoff publicObservation.1 publicObservation.2) ∧
        P.noReportPBO.estimate = A.noReportPayoff

/--
Turn literal optional source actions into the protocol-neutral two-sided
closure interface.  This is an adapter only: `behavior` contains the
unproved sequential response and two-sided candidate-closure obligations.
-/
def lg21OptionalSourceTimedTwoSidedAdapter
    (base : Omega -> Base) (score : Omega -> ℝ)
    (A : LG21OptionalSourceTimedActions Base)
    (behavior : LG21TwoSidedCandidateBehavior (Base := Base) mu skill) :
    TwoSidedCandidateProfileAdapter
      (ReportInfo := Base × ℝ) (NoReportInfo := Base) (mu := mu)
      (skill := skill) where
  source_actions_feasible := LG21OptionalCandidateMatchesFullAction base score A
  source_timing_respected := LG21OptionalCandidateMatchesSourceChannels base score A
  report_action_eligible := behavior.report_action_eligible
  noReport_action_eligible := behavior.noReport_action_eligible
  report_member_weak_response := behavior.report_member_weak_response
  noReport_member_weak_response := behavior.noReport_member_weak_response
  report_strict_gain := behavior.report_strict_gain
  noReport_strict_gain := behavior.noReport_strict_gain

/-- A closed optional candidate has the source's full `take && report`
action, rather than a score-only action chosen after taking has been assumed.
-/
theorem lg21Optional_closedCandidate_matches_fullAction
    (base : Omega -> Base) (score : Omega -> ℝ)
    (A : LG21OptionalSourceTimedActions Base)
    (behavior : LG21TwoSidedCandidateBehavior (Base := Base) mu skill)
    (P : LG21SourceTimedCandidate (Base := Base) (mu := mu) (skill := skill))
    (H : TwoSidedPositiveMassClosedCandidateProfile
      (lg21OptionalSourceTimedTwoSidedAdapter base score A behavior) P) :
    LG21OptionalCandidateMatchesFullAction base score A P := by
  simpa [lg21OptionalSourceTimedTwoSidedAdapter] using H.source_actions_feasible

/-- The optional report branch is feasible only through both source stages. -/
theorem lg21Optional_candidate_reports_iff_take_and_report
    (base : Omega -> Base) (score : Omega -> ℝ)
    (A : LG21OptionalSourceTimedActions Base)
    (P : LG21SourceTimedCandidate (Base := Base) (mu := mu) (skill := skill))
    (hsource : LG21OptionalCandidateMatchesFullAction base score A P)
    (omega : Omega) :
    P.reports omega = true ↔
      A.takeDecision (skill omega) (base omega) = true ∧
        A.reportDecision (base omega) (score omega) = true := by
  rw [hsource omega]
  simp

/-- The optional no-report branch retains both literal source histories. -/
theorem lg21Optional_candidate_noReport_iff_no_take_or_withhold
    (base : Omega -> Base) (score : Omega -> ℝ)
    (A : LG21OptionalSourceTimedActions Base)
    (P : LG21SourceTimedCandidate (Base := Base) (mu := mu) (skill := skill))
    (hsource : LG21OptionalCandidateMatchesFullAction base score A P)
    (omega : Omega) :
    P.reports omega = false ↔
      A.takeDecision (skill omega) (base omega) = false ∨
        (A.takeDecision (skill omega) (base omega) = true ∧
          A.reportDecision (base omega) (score omega) = false) := by
  rw [hsource omega]
  cases htake : A.takeDecision (skill omega) (base omega) <;>
    cases hreport : A.reportDecision (base omega) (score omega) <;>
    simp

/-- A closed optional candidate retains the literal optional public channels.
This projection exposes no null-branch PBO conclusion. -/
theorem lg21Optional_closedCandidate_matches_sourceChannels
    (base : Omega -> Base) (score : Omega -> ℝ)
    (A : LG21OptionalSourceTimedActions Base)
    (behavior : LG21TwoSidedCandidateBehavior (Base := Base) mu skill)
    (P : LG21SourceTimedCandidate (Base := Base) (mu := mu) (skill := skill))
    (H : TwoSidedPositiveMassClosedCandidateProfile
      (lg21OptionalSourceTimedTwoSidedAdapter base score A behavior) P) :
    LG21OptionalCandidateMatchesSourceChannels base score A P := by
  simpa [lg21OptionalSourceTimedTwoSidedAdapter] using H.source_timing_respected

/--
For report-required testing, the positive branch is exactly the pre-score
taking action.  There is no post-score withholding action in this protocol.
-/
def LG21ReportRequiredCandidateMatchesTakeAction
    (base : Omega -> Base)
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ)
    (P : LG21SourceTimedCandidate (Base := Base) (mu := mu) (skill := skill)) : Prop :=
  ∀ omega, P.reports omega = E.takeDecision (skill omega) (base omega)

/--
The report-required candidate uses `(base, score)` on the take branch and
`base` on the no-take branch, together with the source output functions.  As
for optional testing, this is an output-channel identity rather than a
conditional-mean assertion at an unreached branch.
-/
def LG21ReportRequiredCandidateMatchesSourceChannels
    (base : Omega -> Base) (score : Omega -> ℝ)
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ)
    (P : LG21SourceTimedCandidate (Base := Base) (mu := mu) (skill := skill)) : Prop :=
  P.reportObservation = (fun omega => (base omega, score omega)) ∧
    P.noReportObservation = base ∧
      P.reportPBO.estimate = (fun publicObservation =>
        E.reportedPayoff publicObservation.1 publicObservation.2) ∧
        P.noReportPBO.estimate = E.noReportPayoff

/--
Turn literal report-required source actions into the generic two-sided
closure interface.  `behavior` remains an explicit proof obligation: this
definition does not convert the existing one-direction local-entry carrier
into the required two-sided closed-profile proof.
-/
def lg21ReportRequiredSourceTimedTwoSidedAdapter
    (base : Omega -> Base) (score : Omega -> ℝ)
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ)
    (behavior : LG21TwoSidedCandidateBehavior (Base := Base) mu skill) :
    TwoSidedCandidateProfileAdapter
      (ReportInfo := Base × ℝ) (NoReportInfo := Base) (mu := mu)
      (skill := skill) where
  source_actions_feasible := LG21ReportRequiredCandidateMatchesTakeAction base E
  source_timing_respected := LG21ReportRequiredCandidateMatchesSourceChannels base score E
  report_action_eligible := behavior.report_action_eligible
  noReport_action_eligible := behavior.noReport_action_eligible
  report_member_weak_response := behavior.report_member_weak_response
  noReport_member_weak_response := behavior.noReport_member_weak_response
  report_strict_gain := behavior.report_strict_gain
  noReport_strict_gain := behavior.noReport_strict_gain

/-- A closed report-required candidate uses the literal pre-score take rule. -/
theorem lg21ReportRequired_closedCandidate_matches_takeAction
    (base : Omega -> Base) (score : Omega -> ℝ)
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ)
    (behavior : LG21TwoSidedCandidateBehavior (Base := Base) mu skill)
    (P : LG21SourceTimedCandidate (Base := Base) (mu := mu) (skill := skill))
    (H : TwoSidedPositiveMassClosedCandidateProfile
      (lg21ReportRequiredSourceTimedTwoSidedAdapter base score E behavior) P) :
    LG21ReportRequiredCandidateMatchesTakeAction base E P := by
  simpa [lg21ReportRequiredSourceTimedTwoSidedAdapter] using H.source_actions_feasible

/-- In report-required testing the binary report branch is exactly taking. -/
theorem lg21ReportRequired_candidate_reports_iff_take
    (base : Omega -> Base)
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ)
    (P : LG21SourceTimedCandidate (Base := Base) (mu := mu) (skill := skill))
    (hsource : LG21ReportRequiredCandidateMatchesTakeAction base E P)
    (omega : Omega) :
    P.reports omega = true ↔ E.takeDecision (skill omega) (base omega) = true := by
  rw [hsource omega]

/-- In report-required testing the binary no-report branch is exactly no-take. -/
theorem lg21ReportRequired_candidate_noReport_iff_noTake
    (base : Omega -> Base)
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ)
    (P : LG21SourceTimedCandidate (Base := Base) (mu := mu) (skill := skill))
    (hsource : LG21ReportRequiredCandidateMatchesTakeAction base E P)
    (omega : Omega) :
    P.reports omega = false ↔ E.takeDecision (skill omega) (base omega) = false := by
  rw [hsource omega]

/-- A closed report-required candidate retains its literal source channels. -/
theorem lg21ReportRequired_closedCandidate_matches_sourceChannels
    (base : Omega -> Base) (score : Omega -> ℝ)
    (E : LG21ReportRequiredSequentialEquilibriumData ℝ Base ℝ)
    (behavior : LG21TwoSidedCandidateBehavior (Base := Base) mu skill)
    (P : LG21SourceTimedCandidate (Base := Base) (mu := mu) (skill := skill))
    (H : TwoSidedPositiveMassClosedCandidateProfile
      (lg21ReportRequiredSourceTimedTwoSidedAdapter base score E behavior) P) :
    LG21ReportRequiredCandidateMatchesSourceChannels base score E P := by
  simpa [lg21ReportRequiredSourceTimedTwoSidedAdapter] using H.source_timing_respected

end PositiveMassPBOCandidateProfile

end

end LG21TestOptionalPolicies
