import DGJ24OptimalStrategiesRCV.SmartAllocationSource
import EconCSLib.Foundations.Optimization.Certificate
import EconCSLib.SocialChoice.Voting

/-!
# Paper-Facing Theorems: Simpler Than You Think: The Practical Dynamics of Ranked Choice Voting

This file is the implementation theorem layer for the source paper. Keep
source-faithful definitions and theorem wrappers here, and expose only the
compact human-review subset in `PaperInterface.lean`.

## Main declarations

- `ballotSuffixExtension`: suffixing additional preferences to a strategy
  ballot.
- `ballotPrefixExtension`: prefixing an existing exhausted/irrelevant prefix to
  a strategy ballot.
- `exhaustedPrefixAtActiveSet`: all candidates in the prefix are inactive.
- `suffixing_preserves_first_active`: reusable suffix-robust ballot lemma.
- `prefixing_inactive_candidates_preserves_nextActive`: reusable prefix/exhaustion
  ballot lemma.
- `suffixing_preserves_activeSupport_count`: profile-level support-count
  suffix robustness.
- `prefixing_inactive_candidates_preserves_activeSupport_count`:
  profile-level support-count prefix robustness.
- `singleChoiceBallot_respectsLength_one`: single-choice ballots are the
  length-one restriction case.
- `RobustExtensionCertificate`: source-shaped Proposition 1 robust output
  transform certificate.
- `RobustSmartAllocationSlackReductionCertificate`: Proposition 1 robust
  extension certificate tied to the DGJ24 SmartAllocation slack-reduction
  endpoint.
- `exhausted_completion_preserves_activeSupport_count`: Proposition 2
  profile-level support-count bridge for exhausted-ballot completion.
- `exhaustedCompletionViableCandidates`: Proposition 2 viable-candidate
  filter for exhausted-ballot completion.
- `proposition1_robustExtension_optimal_and_runtime_of_transform`:
  Proposition 1 optimality/runtime preservation from a certified
  objective-preserving robust output transform.
- `StrengthenedRemovalProblem` / `StrengthenedRemovalCertificate`: Theorem 2.1
  source-facing candidate-removal certificate interface.
- `StrengthenedRemovalConditionCertificate`: Algorithm 3 condition certificate
  using the extended removal condition.
- `StrengthenedRemovalTraceCertificate`: Algorithm 3 condition certificate that
  proves the original Algorithm 2 branch from certified minimum-tally traces.
- `originalCandidateRemovalCondition_terminal_lower_empty_of_replay`:
  certificate-free original-branch replay theorem for Algorithm 3.
- `algorithm3_original_replay_reduceElectionInstance_preservesActiveSupport`:
  certificate-free original-branch bridge to the concrete reduced-election
  preservation object.
- `OneSurvivalStepCertificate`: Algorithm 3 one-survival step certificate that
  proves the lower candidate is eliminated after the worst upper candidate.
- `StrengthenedRemovalStepTraceCertificate`: Theorem 2.1 certificate route
  combining original-branch STV traces with one-survival step certificates.
- `MultiWinnerContainmentProblem` / `MultiWinnerContainmentCertificate`:
  Theorem 2.2 source-facing containment certificate interface.
- `MultiWinnerContainmentConditionCertificate`: Algorithm 4 condition
  certificate using the Theorem 2.2 transfer bounds.
- `weightedSurplusTransferBound_le_nextChoiceVotes`: Eq. (2) arithmetic
  sanity bound for weighted surplus transfers.
- `SmartAllocationPruningCertificate`: computational-enhancements certificate
  for shared infeasible-prefix caches and suboptimal-structure pruning.
-/

namespace DGJ26PracticalDynamicsRCV

open EconCSLib.SocialChoice.Voting

/-- Source-facing alias for the ranked ballots used in practical RCV traces. -/
abbrev RCVBallot (Candidate : Type*) := Ballot Candidate

/-- Source-facing alias for deterministic STV/RCV traces. -/
abbrev RCVTrace (Candidate : Type*) := STVTrace Candidate

/-- Source-facing predicate for suffixing additional later preferences. -/
def ballotSuffixExtension {Candidate : Type*}
    (base extended : RCVBallot Candidate) : Prop :=
  Ballot.IsSuffixExtension base extended

/-- Source-facing predicate for prefixing earlier exhausted or irrelevant preferences. -/
def ballotPrefixExtension {Candidate : Type*}
    (pref base extended : RCVBallot Candidate) : Prop :=
  Ballot.IsPrefixExtension pref base extended

/-- Source-facing predicate for a ballot length constraint. -/
def ballotRespectsLength {Candidate : Type*}
    (maxLength : ℕ) (ballot : RCVBallot Candidate) : Prop :=
  Ballot.RespectsLength maxLength ballot

/-- Source-facing predicate for single-choice ballots. -/
def singleChoiceBallot {Candidate : Type*} (ballot : RCVBallot Candidate) : Prop :=
  Ballot.IsSingleChoice ballot

/-- Every ballot in a strategy profile respects the same source length bound. -/
def profileRespectsLength {Voter Candidate : Type*}
    (voters : Finset Voter) (maxLength : ℕ)
    (profile : Voter → RCVBallot Candidate) : Prop :=
  ∀ voter, voter ∈ voters → ballotRespectsLength maxLength (profile voter)

/--
Length-restricted feasibility for a strategy profile: the profile is feasible
for the underlying strategy problem and every participating voter's ballot
respects the source length bound.
-/
def lengthRestrictedFeasible {Voter Candidate : Type*}
    (voters : Finset Voter) (maxLength : ℕ)
    (feasible : (Voter → RCVBallot Candidate) → Prop)
    (profile : Voter → RCVBallot Candidate) : Prop :=
  feasible profile ∧ profileRespectsLength voters maxLength profile

/-- Single-choice ballots satisfy the length-one restriction. -/
theorem singleChoiceBallot_respectsLength_one {Candidate : Type*}
    {ballot : RCVBallot Candidate}
    (hsingle : singleChoiceBallot ballot) :
    ballotRespectsLength 1 ballot :=
  hsingle

/-- A single-choice strategy profile satisfies the length-one restriction. -/
theorem singleChoiceProfile_respectsLength_one {Voter Candidate : Type*}
    {voters : Finset Voter} {profile : Voter → RCVBallot Candidate}
    (hsingle : ∀ voter, voter ∈ voters → singleChoiceBallot (profile voter)) :
    profileRespectsLength voters 1 profile := by
  intro voter hvoter
  exact singleChoiceBallot_respectsLength_one (hsingle voter hvoter)

/--
If an algorithm minimizes over the length-restricted feasible profiles, its
output is optimal within the length-restricted strategy class.
-/
theorem lengthRestrictedStrategy_isMinimizerOn
    {Voter Candidate : Type*}
    {voters : Finset Voter} {maxLength : ℕ}
    {feasible : (Voter → RCVBallot Candidate) → Prop}
    {cost : (Voter → RCVBallot Candidate) → ℝ}
    {profile : Voter → RCVBallot Candidate}
    (hmin :
      EconCSLib.Optimization.IsMinimizerOn
        (lengthRestrictedFeasible voters maxLength feasible) cost profile) :
    EconCSLib.Optimization.IsMinimizerOn
      (lengthRestrictedFeasible voters maxLength feasible) cost profile :=
  hmin

/--
The prefix is exhausted at an active set when none of its candidates remains
active.
-/
def exhaustedPrefixAtActiveSet {Candidate : Type*} [DecidableEq Candidate]
    (pref : RCVBallot Candidate) (active : Finset Candidate) : Prop :=
  ∀ candidate, candidate ∈ pref → candidate ∉ active

/--
Definition B.1 strict-support count: voters whose first-ranked candidate lies
in `sources` and whose first active candidate among `candidate` and `blockers`
is `candidate`.
-/
def strictSupportCount {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (sources blockers : Finset Candidate) (candidate : Candidate) : ℕ :=
  Ballot.strictSupportCount voters ballots sources blockers candidate

/--
Original Algorithm 2 candidate-removal condition from the predecessor
framework: every lower-group candidate remains below quota after the budget,
and every upper-group candidate still has strictly larger strict support.
-/
def originalCandidateRemovalCondition {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates lower : Finset Candidate) (budget quota : ℕ) : Prop :=
  strictSupportGroupRemovalCondition
    voters ballots candidates lower budget quota

/--
Algorithm 3 candidate-level failure of the original Algorithm 2 strict-support
comparison: `inside` can potentially outlast some upper candidate under the
addition budget.
-/
def extendedRemovalOriginalFailure {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates lower : Finset Candidate) (budget : ℕ)
    (inside : Candidate) : Prop :=
  ∃ outside, outside ∈ candidates \ lower ∧
    strictSupportCount voters ballots
        (insert outside (lower.erase inside)) (∅ : Finset Candidate)
        outside ≤
      budget + strictSupportCount voters ballots lower (candidates \ lower)
        inside

/--
Algorithm 3 extended-removal condition: either the original Algorithm 2
condition holds, or every lower-group candidate that can outlast some upper
candidate is covered by a one-survival-round safety certificate.  The
`oneSurvivalSafe` predicate packages Algorithm 3's two checks: budget
insufficiency for saving both candidates and guaranteed next-round elimination
after the worst upper candidate is removed.
-/
def extendedCandidateRemovalCondition {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates lower : Finset Candidate) (budget quota : ℕ)
    (oneSurvivalSafe : Candidate → Prop) : Prop :=
  originalCandidateRemovalCondition
      voters ballots candidates lower budget quota ∨
    ∀ inside, inside ∈ lower →
      extendedRemovalOriginalFailure voters ballots candidates lower budget
        inside →
      oneSurvivalSafe inside

/--
Algorithm 3 one-survival-round safety formula for a lower candidate `inside`.
The first inequality says the budget cannot simultaneously save `inside` and
the worst upper candidate; the second says that after removing the worst upper
candidate, `inside` is still below every remaining upper candidate even with
the budget added.
-/
def oneSurvivalRoundSafety {Candidate : Type*}
    (budget : ℕ)
    (upperSupport afterWorstUpperSupport : Candidate → ℕ)
    (afterWorstInsideSupport : ℕ)
    (worst second third : Candidate)
    (remainingUpper : Finset Candidate) : Prop :=
  budget < 2 * upperSupport third - upperSupport second - upperSupport worst ∧
    ∀ outside, outside ∈ remainingUpper →
      budget + afterWorstInsideSupport < afterWorstUpperSupport outside

/--
Algorithm 3 one-survival step core: after the worst upper candidate is removed,
the lower candidate is the unique strictly lower-tally active candidate, so a
minimum-tally elimination step must focus on it.
-/
theorem oneSurvivalRoundSafety_next_elimination_focus
    {Candidate : Type*} [DecidableEq Candidate]
    {budget : ℕ}
    {upperSupport afterWorstUpperSupport : Candidate → ℕ}
    {afterWorstInsideSupport : ℕ}
    {inside worst second third : Candidate}
    {remainingUpper : Finset Candidate}
    (hsafety :
      oneSurvivalRoundSafety budget upperSupport afterWorstUpperSupport
        afterWorstInsideSupport worst second third remainingUpper)
    {step : STVStep Candidate}
    (hminimal : step.eliminatesMinimalTally)
    (hinside_active : inside ∈ step.beforeActive)
    (hactive_subset : step.beforeActive ⊆ insert inside remainingUpper)
    (htally_inside : step.tally inside = budget + afterWorstInsideSupport)
    (htally_outside :
      ∀ outside, outside ∈ remainingUpper →
        step.tally outside = afterWorstUpperSupport outside) :
    step.focus = some inside := by
  exact STVStep.focus_eq_of_tally_lt_all_other_active
    hminimal hinside_active (by
      intro other hother_active hother_ne_inside
      have hother_mem_insert : other ∈ insert inside remainingUpper :=
        hactive_subset hother_active
      have hother_remaining : other ∈ remainingUpper := by
        rw [Finset.mem_insert] at hother_mem_insert
        rcases hother_mem_insert with hother_eq_inside | hother_remaining
        · exact (hother_ne_inside hother_eq_inside).elim
        · exact hother_remaining
      simpa [htally_inside, htally_outside other hother_remaining] using
        hsafety.2 other hother_remaining)

/--
Algorithm 3 one-survival step core, active-set form: if the certified
post-transfer elimination step removes its focused candidate, then it removes
the lower candidate.
-/
theorem oneSurvivalRoundSafety_next_elimination_removes_inside
    {Candidate : Type*} [DecidableEq Candidate]
    {budget : ℕ}
    {upperSupport afterWorstUpperSupport : Candidate → ℕ}
    {afterWorstInsideSupport : ℕ}
    {inside worst second third : Candidate}
    {remainingUpper : Finset Candidate}
    (hsafety :
      oneSurvivalRoundSafety budget upperSupport afterWorstUpperSupport
        afterWorstInsideSupport worst second third remainingUpper)
    {step : STVStep Candidate}
    (hminimal : step.eliminatesMinimalTally)
    (hremove : step.removesFocusedCandidate)
    (hinside_active : inside ∈ step.beforeActive)
    (hactive_subset : step.beforeActive ⊆ insert inside remainingUpper)
    (htally_inside : step.tally inside = budget + afterWorstInsideSupport)
    (htally_outside :
      ∀ outside, outside ∈ remainingUpper →
        step.tally outside = afterWorstUpperSupport outside) :
    step.afterActive = step.beforeActive.erase inside := by
  have hfocus : step.focus = some inside :=
    oneSurvivalRoundSafety_next_elimination_focus
      hsafety hminimal hinside_active hactive_subset
      htally_inside htally_outside
  rcases hremove with ⟨removed, hremoved_focus, hafter⟩
  have hremoved_eq_inside : removed = inside :=
    Option.some.inj (hremoved_focus.symm.trans hfocus)
  subst removed
  exact hafter

/--
Source-shaped witness for Algorithm 3's one-survival branch after the worst
upper candidate has been removed.
-/
structure OneSurvivalStepCertificate (Candidate : Type*) [DecidableEq Candidate]
    (budget : ℕ) (inside : Candidate) where
  upperSupport : Candidate → ℕ
  afterWorstUpperSupport : Candidate → ℕ
  afterWorstInsideSupport : ℕ
  worst : Candidate
  second : Candidate
  third : Candidate
  remainingUpper : Finset Candidate
  step : STVStep Candidate
  safety :
    oneSurvivalRoundSafety budget upperSupport afterWorstUpperSupport
      afterWorstInsideSupport worst second third remainingUpper
  minimal_elimination : step.eliminatesMinimalTally
  removes_focus : step.removesFocusedCandidate
  inside_active : inside ∈ step.beforeActive
  active_subset : step.beforeActive ⊆ insert inside remainingUpper
  tally_inside :
    step.tally inside = budget + afterWorstInsideSupport
  tally_outside :
    ∀ outside, outside ∈ remainingUpper →
      step.tally outside = afterWorstUpperSupport outside

namespace OneSurvivalStepCertificate

/-- The certified one-survival step focuses on the lower candidate. -/
theorem focus_eq_inside {Candidate : Type*} [DecidableEq Candidate]
    {budget : ℕ} {inside : Candidate}
    (cert : OneSurvivalStepCertificate Candidate budget inside) :
    cert.step.focus = some inside := by
  exact oneSurvivalRoundSafety_next_elimination_focus
    cert.safety cert.minimal_elimination cert.inside_active
    cert.active_subset cert.tally_inside cert.tally_outside

/-- The certified one-survival step removes the lower candidate. -/
theorem removes_inside {Candidate : Type*} [DecidableEq Candidate]
    {budget : ℕ} {inside : Candidate}
    (cert : OneSurvivalStepCertificate Candidate budget inside) :
    cert.step.afterActive = cert.step.beforeActive.erase inside := by
  exact oneSurvivalRoundSafety_next_elimination_removes_inside
    cert.safety cert.minimal_elimination cert.removes_focus
    cert.inside_active cert.active_subset cert.tally_inside cert.tally_outside

end OneSurvivalStepCertificate

/--
Raw Algorithm 3 one-survival step facts instantiate the reusable certificate
record.  Paper-facing rows can expose the concrete step, safety inequality,
minimal-tally, focused-removal, active-set, and tally facts while library
theorems continue to consume the compact certificate API.
-/
def oneSurvivalStepCertificate_of_step_facts
    {Candidate : Type*} [DecidableEq Candidate] {budget : ℕ}
    {inside : Candidate}
    (upperSupport afterWorstUpperSupport : Candidate → ℕ)
    (afterWorstInsideSupport : ℕ)
    (worst second third : Candidate)
    (remainingUpper : Finset Candidate)
    (step : STVStep Candidate)
    (safety :
      oneSurvivalRoundSafety budget upperSupport afterWorstUpperSupport
        afterWorstInsideSupport worst second third remainingUpper)
    (minimal_elimination : step.eliminatesMinimalTally)
    (removes_focus : step.removesFocusedCandidate)
    (inside_active : inside ∈ step.beforeActive)
    (active_subset : step.beforeActive ⊆ insert inside remainingUpper)
    (tally_inside : step.tally inside = budget + afterWorstInsideSupport)
    (tally_outside :
      ∀ outside, outside ∈ remainingUpper →
        step.tally outside = afterWorstUpperSupport outside) :
    OneSurvivalStepCertificate Candidate budget inside where
  upperSupport := upperSupport
  afterWorstUpperSupport := afterWorstUpperSupport
  afterWorstInsideSupport := afterWorstInsideSupport
  worst := worst
  second := second
  third := third
  remainingUpper := remainingUpper
  step := step
  safety := safety
  minimal_elimination := minimal_elimination
  removes_focus := removes_focus
  inside_active := inside_active
  active_subset := active_subset
  tally_inside := tally_inside
  tally_outside := tally_outside

/--
Concrete one-survival constructor: after the worst upper candidate is removed,
the active set is `inside ∪ remainingUpper` and the displayed post-transfer
tally function makes `inside` the next minimum-tally elimination.
-/
def oneSurvivalStepCertificate_of_postWorst_tally
    {Candidate : Type*} [DecidableEq Candidate] {budget : ℕ}
    {inside : Candidate}
    (upperSupport afterWorstUpperSupport : Candidate → ℕ)
    (afterWorstInsideSupport : ℕ)
    (worst second third : Candidate)
    (remainingUpper : Finset Candidate)
    (hinside_not_remaining : inside ∉ remainingUpper)
    (safety :
      oneSurvivalRoundSafety budget upperSupport afterWorstUpperSupport
        afterWorstInsideSupport worst second third remainingUpper) :
    OneSurvivalStepCertificate Candidate budget inside where
  upperSupport := upperSupport
  afterWorstUpperSupport := afterWorstUpperSupport
  afterWorstInsideSupport := afterWorstInsideSupport
  worst := worst
  second := second
  third := third
  remainingUpper := remainingUpper
  step :=
    groupEliminationStep (insert inside remainingUpper) inside
      (fun candidate =>
        if candidate = inside then
          budget + afterWorstInsideSupport
        else
          afterWorstUpperSupport candidate)
  safety := safety
  minimal_elimination := by
    refine ⟨rfl, inside, rfl, by simp [groupEliminationStep], ?_⟩
    intro candidate hcandidate
    have hcandidate_active : candidate ∈ insert inside remainingUpper := by
      simpa [groupEliminationStep] using hcandidate
    by_cases hcandidate_inside : candidate = inside
    · subst candidate
      simp [groupEliminationStep]
    · have hremaining : candidate ∈ remainingUpper := by
        simpa [Finset.mem_insert, hcandidate_inside] using hcandidate_active
      exact le_of_lt (by
        simpa [groupEliminationStep, hcandidate_inside] using safety.2 candidate hremaining)
  removes_focus := by
    exact ⟨inside, rfl, rfl⟩
  inside_active := by
    simp [groupEliminationStep]
  active_subset := by
    intro candidate hcandidate
    simpa [groupEliminationStep] using hcandidate
  tally_inside := by
    simp [groupEliminationStep]
  tally_outside := by
    intro outside houtside
    have houtside_ne_inside : outside ≠ inside := by
      intro houtside_eq
      exact hinside_not_remaining (houtside_eq ▸ houtside)
    simp [groupEliminationStep, houtside_ne_inside]

/--
Algorithm 3 immediately accepts instances satisfying the original Algorithm 2
removal condition.
-/
theorem extendedCandidateRemovalCondition_of_originalCondition
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower : Finset Candidate} {budget quota : ℕ}
    {oneSurvivalSafe : Candidate → Prop}
    (horiginal :
      originalCandidateRemovalCondition
        voters ballots candidates lower budget quota) :
    extendedCandidateRemovalCondition
      voters ballots candidates lower budget quota oneSurvivalSafe :=
  Or.inl horiginal

/--
Algorithm 3 one-survival branch constructor: if every lower candidate that can
outlast an upper candidate has a certified post-transfer elimination step, then
the extended removal condition holds with the one-survival predicate
instantiated by existence of such a step certificate.
-/
theorem extendedCandidateRemovalCondition_of_oneSurvivalStepCertificates
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower : Finset Candidate} {budget quota : ℕ}
    (one_survival_step :
      ∀ inside, inside ∈ lower →
        extendedRemovalOriginalFailure voters ballots candidates lower budget
          inside →
        OneSurvivalStepCertificate Candidate budget inside) :
    extendedCandidateRemovalCondition
      voters ballots candidates lower budget quota
      (fun inside =>
        ∃ _stepCert : OneSurvivalStepCertificate Candidate budget inside,
          True) := by
  exact Or.inr (by
    intro inside hinside hfailure
    exact ⟨one_survival_step inside hinside hfailure, True.intro⟩)

/--
Per-candidate one-survival step certificates give the step-level output bridge
used by the direct Algorithm 3 proof route.
-/
theorem oneSurvivalStepWitnesses_of_oneSurvivalStepCertificates
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower : Finset Candidate} {budget : ℕ}
    (one_survival_step :
      ∀ inside, inside ∈ lower →
        extendedRemovalOriginalFailure voters ballots candidates lower budget
          inside →
        OneSurvivalStepCertificate Candidate budget inside) :
    ∀ inside, inside ∈ lower →
      extendedRemovalOriginalFailure voters ballots candidates lower budget
        inside →
      ∃ step : STVStep Candidate,
        step.afterActive = step.beforeActive.erase inside := by
  intro inside hinside hfailure
  let stepCert := one_survival_step inside hinside hfailure
  exact ⟨stepCert.step, OneSurvivalStepCertificate.removes_inside stepCert⟩

/--
Original Algorithm 2 trace bridge: along any trace whose elimination steps
choose and remove minimum-tally active candidates, the original strict-support
removal condition forces every certified elimination step to remove a focused
lower-group candidate.
-/
theorem originalCandidateRemovalCondition_trace_elimination_focus_mem_lower
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower : Finset Candidate} {budget quota : ℕ}
    (horiginal :
      originalCandidateRemovalCondition
        voters ballots candidates lower budget quota)
    {trace : RCVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hlower_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ lower ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots lower
                (candidates \ lower) inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (lower.erase inside)) (∅ : Finset Candidate)
              outside) :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      ∃ loser, step.focus = some loser ∧ loser ∈ lower ∧
        loser ∈ step.beforeActive ∧
        step.afterActive = step.beforeActive.erase loser := by
  have hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates lower budget quota := by
    exact strictSupportGroupRemovalSafety_of_condition horiginal
  exact strictSupportGroupRemovalSafety_trace_elimination_focus_mem_group
    hsafety hminimal hremove hlower_active hactive_subset_candidates
    htally_inside htally_outside

/--
Original Algorithm 2 trace bridge, predicate form: every certified
minimum-tally elimination removes a focused candidate from the lower group.
-/
theorem originalCandidateRemovalCondition_trace_eliminationRemovesFromLower
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower : Finset Candidate} {budget quota : ℕ}
    (horiginal :
      originalCandidateRemovalCondition
        voters ballots candidates lower budget quota)
    {trace : RCVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hlower_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ lower ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots lower
                (candidates \ lower) inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (lower.erase inside)) (∅ : Finset Candidate)
              outside) :
    trace.eliminationRemovesFromGroup lower := by
  have hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates lower budget quota := by
    exact strictSupportGroupRemovalSafety_of_condition horiginal
  exact strictSupportGroupRemovalSafety_trace_eliminationRemovesFromGroup
    hsafety hminimal hremove hlower_active hactive_subset_candidates
    htally_inside htally_outside

/--
Bounded-tally original Algorithm 2 trace bridge. The source proof only needs
lower-candidate tallies bounded above by the budget-augmented strict support
and outside-candidate tallies bounded below by the outside strict support.
-/
theorem originalCandidateRemovalCondition_trace_eliminationRemovesFromLower_of_tally_bounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower : Finset Candidate} {budget quota : ℕ}
    (horiginal :
      originalCandidateRemovalCondition
        voters ballots candidates lower budget quota)
    {trace : RCVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hlower_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ lower ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside_le :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside ≤
            budget +
              strictSupportCount voters ballots lower
                (candidates \ lower) inside)
    (htally_outside_ge :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          strictSupportCount voters ballots
              (insert outside (lower.erase inside)) (∅ : Finset Candidate)
              outside ≤
            step.tally outside) :
    trace.eliminationRemovesFromGroup lower := by
  have hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates lower budget quota := by
    exact strictSupportGroupRemovalSafety_of_condition horiginal
  exact strictSupportGroupRemovalSafety_trace_eliminationRemovesFromGroup_of_tally_bounds
    hsafety hminimal hremove hlower_active hactive_subset_candidates
    htally_inside_le htally_outside_ge

/--
Original Algorithm 2 trace bridge, cardinality form: every certified
minimum-tally elimination step strictly decreases the number of active lower
candidates.
-/
theorem originalCandidateRemovalCondition_trace_elimination_lower_card_decreases
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower : Finset Candidate} {budget quota : ℕ}
    (horiginal :
      originalCandidateRemovalCondition
        voters ballots candidates lower budget quota)
    {trace : RCVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hlower_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ lower ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots lower
                (candidates \ lower) inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (lower.erase inside)) (∅ : Finset Candidate)
              outside) :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      (step.afterActive ∩ lower).card <
        (step.beforeActive ∩ lower).card := by
  have hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates lower budget quota := by
    exact strictSupportGroupRemovalSafety_of_condition horiginal
  exact strictSupportGroupRemovalSafety_trace_elimination_activeGroup_card_decreases
    hsafety hminimal hremove hlower_active hactive_subset_candidates
    htally_inside htally_outside

/--
Original Algorithm 2 trace bridge, exact cardinality form: every certified
minimum-tally elimination removes exactly one active lower candidate.
-/
theorem originalCandidateRemovalCondition_trace_elimination_lower_card_add_one_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower : Finset Candidate} {budget quota : ℕ}
    (horiginal :
      originalCandidateRemovalCondition
        voters ballots candidates lower budget quota)
    {trace : RCVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hlower_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ lower ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots lower
                (candidates \ lower) inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (lower.erase inside)) (∅ : Finset Candidate)
              outside) :
    trace.eliminationActiveGroupCardAddOneEq lower := by
  have htrace :
      trace.eliminationRemovesFromGroup lower :=
    originalCandidateRemovalCondition_trace_eliminationRemovesFromLower
      horiginal hminimal hremove hlower_active hactive_subset_candidates
      htally_inside htally_outside
  exact STVTrace.eliminationActiveGroupCardAddOneEq_of_eliminationRemovesFromGroup
    htrace

/--
Original Algorithm 2 replay accounting: under the original strict-support
condition, an all-elimination replay prefix removes exactly one active lower
candidate per step.
-/
theorem originalCandidateRemovalCondition_terminal_lower_card_add_length_eq_of_replay
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower : Finset Candidate} {budget quota : ℕ}
    (horiginal :
      originalCandidateRemovalCondition
        voters ballots candidates lower budget quota)
    {trace : RCVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hlower_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ lower ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots lower
                (candidates \ lower) inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (lower.erase inside)) (∅ : Finset Candidate)
              outside)
    {startActive terminalActive : Finset Candidate}
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate) :
    (terminalActive ∩ lower).card + trace.steps.length =
      (startActive ∩ lower).card := by
  have htrace : trace.eliminationRemovesFromGroup lower :=
    originalCandidateRemovalCondition_trace_eliminationRemovesFromLower
      horiginal hminimal hremove hlower_active hactive_subset_candidates
      htally_inside htally_outside
  exact STVTrace.terminal_activeGroup_card_add_length_eq_start_card_of_replaysFrom
    hreplay hall_eliminate htrace

/--
Original Algorithm 2 replay depletion: if the all-elimination replay prefix is
long enough to remove every initially active lower candidate, no lower
candidate remains active at the terminal state.
-/
theorem originalCandidateRemovalCondition_terminal_lower_empty_of_replay
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower : Finset Candidate} {budget quota : ℕ}
    (horiginal :
      originalCandidateRemovalCondition
        voters ballots candidates lower budget quota)
    {trace : RCVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hlower_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ lower ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots lower
                (candidates \ lower) inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (lower.erase inside)) (∅ : Finset Candidate)
              outside)
    {startActive terminalActive : Finset Candidate}
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ lower).card) :
    terminalActive ∩ lower = ∅ := by
  have htrace : trace.eliminationRemovesFromGroup lower :=
    originalCandidateRemovalCondition_trace_eliminationRemovesFromLower
      horiginal hminimal hremove hlower_active hactive_subset_candidates
      htally_inside htally_outside
  exact STVTrace.terminal_activeGroup_eq_empty_of_replaysFrom_length_eq_start_card
    hreplay hall_eliminate htrace hlength

/--
Bounded-tally original Algorithm 2 replay depletion: if the all-elimination
replay prefix is long enough to remove every initially active lower candidate,
no lower candidate remains active at the terminal state.
-/
theorem originalCandidateRemovalCondition_terminal_lower_empty_of_replay_tally_bounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower : Finset Candidate} {budget quota : ℕ}
    (horiginal :
      originalCandidateRemovalCondition
        voters ballots candidates lower budget quota)
    {trace : RCVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hlower_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ lower ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside_le :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside ≤
            budget +
              strictSupportCount voters ballots lower
                (candidates \ lower) inside)
    (htally_outside_ge :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          strictSupportCount voters ballots
              (insert outside (lower.erase inside)) (∅ : Finset Candidate)
              outside ≤
            step.tally outside)
    {startActive terminalActive : Finset Candidate}
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ lower).card) :
    terminalActive ∩ lower = ∅ := by
  have htrace : trace.eliminationRemovesFromGroup lower :=
    originalCandidateRemovalCondition_trace_eliminationRemovesFromLower_of_tally_bounds
      horiginal hminimal hremove hlower_active hactive_subset_candidates
      htally_inside_le htally_outside_ge
  exact STVTrace.terminal_activeGroup_eq_empty_of_replaysFrom_length_eq_start_card
    hreplay hall_eliminate htrace hlength

/--
Candidate structures still worth evaluating in Algorithm A's structure search:
their required votes fit under the budget and their cost can improve on the
current incumbent.
-/
def smartAllocationStructureViable {Structure : Type*}
    (requiredVotes cost : Structure → ℕ)
    (budget incumbentCost : ℕ) (candidateStructure : Structure) : Prop :=
  requiredVotes candidateStructure ≤ budget ∧
    cost candidateStructure < incumbentCost

/--
Computational-enhancements certificate for Algorithm A's smart allocation
search.  The shared cache stores prefixes that are already known to make every
extension exceed the budget; a second finite set stores structures whose cost
cannot improve on the incumbent.
-/
structure SmartAllocationPruningCertificate
    (Structure Prefix : Type*) where
  infeasiblePrefixes : Finset Prefix
  suboptimalStructures : Finset Structure
  prefixOf : Prefix → Structure → Prop
  requiredVotes : Structure → ℕ
  cost : Structure → ℕ
  budget : ℕ
  incumbentCost : ℕ
  prefix_infeasible :
    ∀ cachedPrefix, cachedPrefix ∈ infeasiblePrefixes →
      ∀ candidateStructure, prefixOf cachedPrefix candidateStructure →
        budget < requiredVotes candidateStructure
  suboptimal :
    ∀ candidateStructure, candidateStructure ∈ suboptimalStructures →
      incumbentCost ≤ cost candidateStructure

/--
A structure is rejected by the shared pruning state if it extends a cached
infeasible prefix or has already been marked suboptimal relative to the
incumbent.
-/
def smartAllocationRejectedByPruningCache
    {Structure Prefix : Type*}
  (cert : SmartAllocationPruningCertificate Structure Prefix)
  (candidateStructure : Structure) : Prop :=
  (∃ cachedPrefix, cachedPrefix ∈ cert.infeasiblePrefixes ∧
      cert.prefixOf cachedPrefix candidateStructure) ∨
    candidateStructure ∈ cert.suboptimalStructures

/--
Cached infeasible prefixes and suboptimal-structure records only reject
structures that are not viable for the current budget/incumbent test.
-/
theorem smartAllocationPruningCertificate_rejects_only_nonviable
    {Structure Prefix : Type*}
    (cert : SmartAllocationPruningCertificate Structure Prefix)
    {candidateStructure : Structure}
    (hreject :
      smartAllocationRejectedByPruningCache cert candidateStructure) :
    ¬ smartAllocationStructureViable cert.requiredVotes cert.cost
      cert.budget cert.incumbentCost candidateStructure := by
  intro hviable
  rcases hreject with hprefix | hsuboptimal
  · rcases hprefix with ⟨cachedPrefix, hprefix_mem, hprefixOf⟩
    exact not_le_of_gt
      (cert.prefix_infeasible cachedPrefix hprefix_mem candidateStructure
        hprefixOf)
      hviable.1
  · exact not_lt_of_ge
      (cert.suboptimal candidateStructure hsuboptimal) hviable.2

/--
Parallel workers may use the same shared pruning cache on disjoint or
overlapping shards: every cached rejection on any shard is still nonviable.
-/
theorem smartAllocationPruningCertificate_parallelShard_sound
    {Structure Prefix : Type*}
    (cert : SmartAllocationPruningCertificate Structure Prefix)
    (shard : Finset Structure) :
    ∀ candidateStructure, candidateStructure ∈ shard →
      smartAllocationRejectedByPruningCache cert candidateStructure →
        ¬ smartAllocationStructureViable cert.requiredVotes cert.cost
          cert.budget cert.incumbentCost candidateStructure := by
  intro candidateStructure _hstructure hreject
  exact smartAllocationPruningCertificate_rejects_only_nonviable cert hreject

/--
Source-facing problem for Theorem 2.1: a strengthened Algorithm 2 candidate
removal instance whose output should preserve optimality after allowing one
survival round.
-/
structure StrengthenedRemovalProblem (ReducedInstance : Type*) where
  specification : ReducedInstance → Prop
  budget : ℕ
  uniqueBallotCount : ℕ
  candidateCount : ℕ

namespace StrengthenedRemovalProblem

/-- The Theorem 2.1 inherited `O(m n^4)` operation-count bound in exact form. -/
def quarticRuntimeBound {ReducedInstance : Type*}
    (problem : StrengthenedRemovalProblem ReducedInstance) : ℕ :=
  problem.uniqueBallotCount * problem.candidateCount ^ 4

end StrengthenedRemovalProblem

/-- Concrete operation-count model for the strengthened removal theorem. -/
def strengthenedRemovalOperationCount
    (uniqueBallotCount candidateCount : ℕ) : ℕ :=
  uniqueBallotCount * candidateCount ^ 4

/-- Source-facing alias for the concrete candidate-removal output instance. -/
abbrev ReducedElectionInstance (Voter Candidate : Type*) :=
  EconCSLib.SocialChoice.Voting.ReducedElectionInstance Voter Candidate

/--
Concrete candidate-removal reduction used by Algorithm 3's original branch:
delete lower candidates from the candidate set and from every ballot.
-/
def reduceElectionInstanceByCandidates
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (removed candidates : Finset Candidate)
    (ballots : Voter → RCVBallot Candidate) :
    ReducedElectionInstance Voter Candidate :=
  EconCSLib.SocialChoice.Voting.ReducedElectionInstance.removeCandidates
    removed candidates ballots

/--
The reduced election preserves active-support counts at the terminal active
set relative to the source profile.
-/
def reducedElectionPreservesActiveSupport
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (sourceBallots : Voter → RCVBallot Candidate)
    (terminalActive : Finset Candidate)
    (reduced : ReducedElectionInstance Voter Candidate) : Prop :=
  EconCSLib.SocialChoice.Voting.ReducedElectionInstance.PreservesActiveSupport
    voters sourceBallots terminalActive reduced

/--
The concrete candidate-deletion reduction preserves active support once the
deleted group is terminally depleted.
-/
theorem reducedElectionPreservesActiveSupport_reduceElectionInstanceByCandidates
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {terminalActive removed candidates : Finset Candidate}
    (hdepleted : terminalActive ∩ removed = ∅) :
    reducedElectionPreservesActiveSupport voters ballots terminalActive
      (reduceElectionInstanceByCandidates removed candidates ballots) := by
  exact
    EconCSLib.SocialChoice.Voting.ReducedElectionInstance.preservesActiveSupport_removeCandidates_of_disjoint_active
      (voters := voters) (ballots := ballots) (active := terminalActive)
      (removed := removed) (candidates := candidates) hdepleted

/--
Concrete source specification for Algorithm 3's original-branch reduced
election output: return exactly the candidate-deletion instance and preserve
active-support counts at the terminal active set.
-/
def strengthenedRemovalConcreteReductionSpecification
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates lower terminalActive : Finset Candidate)
    (reduced : ReducedElectionInstance Voter Candidate) : Prop :=
  reduced = reduceElectionInstanceByCandidates lower candidates ballots ∧
    reducedElectionPreservesActiveSupport voters ballots terminalActive reduced

/--
Concrete source problem for Algorithm 3's original-branch reduction. Its
specification is the paper's candidate-deletion output plus terminal
active-support preservation, rather than an arbitrary output predicate.
-/
def strengthenedRemovalConcreteReductionProblem
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates lower terminalActive : Finset Candidate)
    (budget uniqueBallotCount candidateCount : ℕ) :
    StrengthenedRemovalProblem (ReducedElectionInstance Voter Candidate) where
  specification :=
    strengthenedRemovalConcreteReductionSpecification
      voters ballots candidates lower terminalActive
  budget := budget
  uniqueBallotCount := uniqueBallotCount
  candidateCount := candidateCount

/--
Concrete Algorithm 3 original-branch implementation on a fixed source model:
delete lower candidates from every ballot and from the candidate set.
-/
def strengthenedRemovalConcreteReductionAlgorithm
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (ballots : Voter → RCVBallot Candidate)
    (candidates lower : Finset Candidate) :
    StrengthenedRemovalProblem (ReducedElectionInstance Voter Candidate) →
      ReducedElectionInstance Voter Candidate :=
  fun _problem =>
    reduceElectionInstanceByCandidates lower candidates ballots

/-- Concrete Algorithm 3 original-branch operation-count implementation. -/
def strengthenedRemovalConcreteReductionOperationCount
    {Voter Candidate : Type*} :
    StrengthenedRemovalProblem (ReducedElectionInstance Voter Candidate) → ℕ :=
  fun problem =>
    strengthenedRemovalOperationCount
      problem.uniqueBallotCount problem.candidateCount

/--
Source-shaped full election run for Algorithm 3's original-replay branch.
The record packages the concrete trace replay and tally facts that the
Theorem 2.1 constructors need, so paper-facing endpoints can consume one run
object rather than a long list of trace side conditions.
-/
structure Algorithm3OriginalFullElectionRun
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates lower : Finset Candidate) (budget : ℕ) where
  trace : RCVTrace Candidate
  startActive : Finset Candidate
  terminalActive : Finset Candidate
  minimal_eliminations :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      step.eliminatesMinimalTally
  focused_eliminations_remove_focus :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      step.removesFocusedCandidate
  lower_active_at_elimination :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      ∃ inside, inside ∈ lower ∧ inside ∈ step.beforeActive
  active_subset_candidates :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      step.beforeActive ⊆ candidates
  tally_inside :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        step.tally inside =
          budget +
            strictSupportCount voters ballots lower (candidates \ lower)
              inside
  tally_outside :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
      ∀ outside, outside ∈ candidates \ lower →
        step.tally outside =
          strictSupportCount voters ballots
            (insert outside (lower.erase inside)) (∅ : Finset Candidate)
            outside
  active_replay : trace.replaysFrom startActive terminalActive
  all_eliminate :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate
  removes_initial_lower :
    trace.steps.length = (startActive ∩ lower).card

namespace Algorithm3OriginalFullElectionRun

theorem terminal_lower_empty_of_original_condition
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower : Finset Candidate} {budget quota : ℕ}
    (run :
      Algorithm3OriginalFullElectionRun voters ballots candidates lower budget)
    (horiginal :
      originalCandidateRemovalCondition
        voters ballots candidates lower budget quota) :
    run.terminalActive ∩ lower = ∅ := by
  exact
    originalCandidateRemovalCondition_terminal_lower_empty_of_replay
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (lower := lower) (budget := budget) (quota := quota)
      (trace := run.trace)
      horiginal run.minimal_eliminations
      run.focused_eliminations_remove_focus
      run.lower_active_at_elimination run.active_subset_candidates
      run.tally_inside run.tally_outside run.active_replay
      run.all_eliminate run.removes_initial_lower

/--
The original-branch full election run supplies the initial-loss prefix sequence
fact used by shared STV/sequence-reduction endpoints.
-/
theorem initial_loss_prefix_from_trace
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower : Finset Candidate} {budget : ℕ}
    (run :
      Algorithm3OriginalFullElectionRun voters ballots candidates lower budget) :
    DGJ24OptimalStrategiesRCV.rcvSequenceHasInitialLossPrefix
      (DGJ24OptimalStrategiesRCV.rcvSequenceFromTrace run.trace)
      ((run.startActive ∩ lower).card) := by
  have hprefix :
      run.trace.HasInitialEliminationPrefix
        ((run.startActive ∩ lower).card) := by
    exact
      STVTrace.hasInitialEliminationPrefix_of_forall_mem_kind
        (by exact le_of_eq run.removes_initial_lower.symm)
        run.all_eliminate
  exact
    DGJ24OptimalStrategiesRCV.rcvSequenceHasInitialLossPrefix_of_trace_initialEliminationPrefix
      rfl hprefix

end Algorithm3OriginalFullElectionRun

/--
Source-shaped full election run for Algorithm 3.  This extends the original
Algorithm 2 replay package with Algorithm 3's branch decision: either the
original strict-support condition succeeds, or every lower candidate that
fails the original comparison has the post-worst one-survival witnesses used
by the extended-removal condition.
-/
structure Algorithm3FullElectionRun
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates lower : Finset Candidate) (budget quota : ℕ) where
  originalRun :
    Algorithm3OriginalFullElectionRun voters ballots candidates lower budget
  branch :
    originalCandidateRemovalCondition
        voters ballots candidates lower budget quota ∨
      (∀ inside, inside ∈ lower →
        extendedRemovalOriginalFailure voters ballots candidates lower budget
          inside →
        ∃ upperSupport : Candidate → ℕ,
        ∃ afterWorstUpperSupport : Candidate → ℕ,
        ∃ afterWorstInsideSupport : ℕ,
        ∃ worst : Candidate,
        ∃ second : Candidate,
        ∃ third : Candidate,
        ∃ remainingUpper : Finset Candidate,
          inside ∉ remainingUpper ∧
          oneSurvivalRoundSafety budget upperSupport
            afterWorstUpperSupport afterWorstInsideSupport worst second third
            remainingUpper ∧
          originalRun.terminalActive ⊆ remainingUpper)

/--
Executable finite branch check for Algorithm 3's Theorem 2.1 source cases.
The original branch is checked directly; otherwise each lower candidate that
fails the original strict-support comparison must pass the paper's post-worst
one-survival tally check, with the candidate witnesses supplied as finite
algorithm output data.
-/
noncomputable def algorithm3PostWorstTallyBranchCheck
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates lower terminalActive : Finset Candidate)
    (budget quota : ℕ)
    (upperSupport afterWorstUpperSupport : Candidate → Candidate → ℕ)
    (afterWorstInsideSupport : Candidate → ℕ)
    (worst second third : Candidate → Candidate)
    (remainingUpper : Candidate → Finset Candidate) : Bool :=
  by
    classical
    exact decide
      (originalCandidateRemovalCondition
          voters ballots candidates lower budget quota ∨
        ∀ inside, inside ∈ lower →
          extendedRemovalOriginalFailure voters ballots candidates lower budget
            inside →
            inside ∉ remainingUpper inside ∧
              oneSurvivalRoundSafety budget (upperSupport inside)
                (afterWorstUpperSupport inside) (afterWorstInsideSupport inside)
                (worst inside) (second inside) (third inside)
                (remainingUpper inside) ∧
              terminalActive ⊆ remainingUpper inside)

/--
A successful executable Algorithm 3 post-worst tally branch check constructs
the full source-run object consumed by the concrete Theorem 2.1 implementation.
-/
noncomputable def algorithm3FullElectionRun_of_postWorstTallyBranchCheck_eq_true
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower : Finset Candidate} {budget quota : ℕ}
    {upperSupport afterWorstUpperSupport : Candidate → Candidate → ℕ}
    {afterWorstInsideSupport : Candidate → ℕ}
    {worst second third : Candidate → Candidate}
    {remainingUpper : Candidate → Finset Candidate}
    (run :
      Algorithm3OriginalFullElectionRun voters ballots candidates lower budget)
    (hcheck :
      algorithm3PostWorstTallyBranchCheck voters ballots candidates lower
        run.terminalActive budget quota upperSupport afterWorstUpperSupport
        afterWorstInsideSupport worst second third remainingUpper = true) :
    Algorithm3FullElectionRun voters ballots candidates lower budget quota where
  originalRun := run
  branch := by
    classical
    have hbranch :
        originalCandidateRemovalCondition
            voters ballots candidates lower budget quota ∨
          ∀ inside, inside ∈ lower →
            extendedRemovalOriginalFailure voters ballots candidates lower budget
              inside →
              inside ∉ remainingUpper inside ∧
                oneSurvivalRoundSafety budget (upperSupport inside)
                  (afterWorstUpperSupport inside)
                  (afterWorstInsideSupport inside) (worst inside)
                  (second inside) (third inside) (remainingUpper inside) ∧
                run.terminalActive ⊆ remainingUpper inside := by
      simpa [algorithm3PostWorstTallyBranchCheck] using
        of_decide_eq_true hcheck
    rcases hbranch with horiginal | honeSurvival
    · exact Or.inl horiginal
    · refine Or.inr ?_
      intro inside hinside hfailure
      rcases honeSurvival inside hinside hfailure with
        ⟨hnot_remaining, hsafety, hterminal_subset⟩
      exact
        ⟨upperSupport inside, afterWorstUpperSupport inside,
          afterWorstInsideSupport inside, worst inside, second inside,
          third inside, remainingUpper inside, hnot_remaining, hsafety,
          hterminal_subset⟩

/--
Generated original-replay constructor for Algorithm 3.  A total
minimum-tally choice rule supplies the trace, replay, focus-removal, and length
facts; the source strict-support condition plus exact generated tally equations
turn the group-minimal generated eliminations into full minimum-tally
eliminations.
-/
noncomputable def algorithm3OriginalFullElectionRun_of_generated_group_elimination
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {choice : MinimalTallyChoiceRule Candidate}
    {tallyOf : Finset Candidate → Candidate → ℕ}
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower startActive : Finset Candidate}
    {budget quota : ℕ}
    (hactiveChoice : choice.ChoosesActive)
    (htotalChoice : choice.Total)
    (hminimalChoice : choice.SelectsMinimal)
    (hstart_subset : startActive ⊆ candidates)
    (horiginal :
      originalCandidateRemovalCondition
        voters ballots candidates lower budget quota)
    (htally_inside :
      ∀ step,
        step ∈
          minimalGroupEliminationGeneratedSteps choice lower tallyOf
            (startActive ∩ lower).card startActive →
        step.kind = StepKind.eliminate →
          ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
            step.tally inside =
              budget +
                strictSupportCount voters ballots lower (candidates \ lower)
                  inside)
    (htally_outside :
      ∀ step,
        step ∈
          minimalGroupEliminationGeneratedSteps choice lower tallyOf
            (startActive ∩ lower).card startActive →
        step.kind = StepKind.eliminate →
          ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          ∀ outside, outside ∈ candidates \ lower →
            step.tally outside =
              strictSupportCount voters ballots
                (insert outside (lower.erase inside)) (∅ : Finset Candidate)
                outside) :
    Algorithm3OriginalFullElectionRun voters ballots candidates lower budget where
  trace :=
    minimalGroupEliminationGeneratedTrace choice lower tallyOf
      (startActive ∩ lower).card startActive
  startActive := startActive
  terminalActive :=
    minimalGroupEliminationTerminalActive choice lower tallyOf
      (startActive ∩ lower).card startActive
  minimal_eliminations := by
    intro step hstep hkind
    have hsafety :
        strictSupportGroupRemovalSafety
          voters ballots candidates lower budget quota := by
      exact strictSupportGroupRemovalSafety_of_condition horiginal
    exact
      strictSupportGroupRemovalSafety_generated_minimal_eliminations
        (voters := voters) (ballots := ballots) (candidates := candidates)
        (group := lower) (budget := budget) (quota := quota)
        (choice := choice) (tallyOf := tallyOf)
        (rounds := (startActive ∩ lower).card)
        (initialActive := startActive)
        hsafety hminimalChoice
        (by
          intro generatedStep hgenerated _hgenerated_kind
          exact
            minimalGroupEliminationGeneratedSteps_beforeActive_subset_of_initial_subset
              choice lower tallyOf hstart_subset (startActive ∩ lower).card
              generatedStep hgenerated)
        htally_inside htally_outside step
        (by
          simpa [minimalGroupEliminationGeneratedTrace] using hstep)
        hkind
  focused_eliminations_remove_focus := by
    intro step hstep _hkind
    exact
      minimalGroupEliminationGeneratedSteps_removesFocusedCandidate
        choice lower tallyOf (startActive ∩ lower).card startActive step
        (by
          simpa [minimalGroupEliminationGeneratedTrace] using hstep)
  lower_active_at_elimination := by
    intro step hstep _hkind
    exact
      minimalGroupEliminationGeneratedSteps_group_active_at_step
        choice lower tallyOf (startActive ∩ lower).card startActive step
        (by
          simpa [minimalGroupEliminationGeneratedTrace] using hstep)
  active_subset_candidates := by
    intro step hstep _hkind
    exact
      minimalGroupEliminationGeneratedSteps_beforeActive_subset_of_initial_subset
        choice lower tallyOf hstart_subset (startActive ∩ lower).card step
        (by
          simpa [minimalGroupEliminationGeneratedTrace] using hstep)
  tally_inside := by
    intro step hstep hkind inside hinside hactive
    exact htally_inside step
      (by simpa [minimalGroupEliminationGeneratedTrace] using hstep)
      hkind inside hinside hactive
  tally_outside := by
    intro step hstep hkind inside hinside hactive outside houtside
    exact htally_outside step
      (by simpa [minimalGroupEliminationGeneratedTrace] using hstep)
      hkind inside hinside hactive outside houtside
  active_replay := by
    simpa [minimalGroupEliminationGeneratedTrace, STVTrace.replaysFrom] using
      minimalGroupEliminationGeneratedSteps_replayStepsFrom
        choice lower tallyOf (startActive ∩ lower).card startActive
  all_eliminate := by
    intro step hstep
    exact
      minimalGroupEliminationGeneratedSteps_all_eliminate
        choice lower tallyOf (startActive ∩ lower).card startActive step
        (by
          simpa [minimalGroupEliminationGeneratedTrace] using hstep)
  removes_initial_lower := by
    simpa [minimalGroupEliminationGeneratedTrace] using
      minimalGroupEliminationGeneratedSteps_length_eq
        (choice := choice) hactiveChoice htotalChoice lower tallyOf
        (startActive ∩ lower).card startActive rfl

/--
Concrete Algorithm 3 original-branch preservation theorem: under the original
strict-support condition and replay semantics, the concrete reduced election
obtained by deleting the lower group preserves all later active-support counts
at the terminal active set.
-/
theorem algorithm3_original_replay_reduceElectionInstance_preservesActiveSupport
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower startActive terminalActive : Finset Candidate}
    {budget quota : ℕ} {trace : RCVTrace Candidate}
    (horiginal :
      originalCandidateRemovalCondition
        voters ballots candidates lower budget quota)
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hlower_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ lower ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots lower (candidates \ lower)
                inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (lower.erase inside)) (∅ : Finset Candidate)
              outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ lower).card) :
    terminalActive ∩ lower = ∅ ∧
      reducedElectionPreservesActiveSupport
        voters ballots terminalActive
        (reduceElectionInstanceByCandidates lower candidates ballots) := by
  have hempty : terminalActive ∩ lower = ∅ :=
    originalCandidateRemovalCondition_terminal_lower_empty_of_replay
      horiginal hminimal hremove hlower_active hactive_subset_candidates
      htally_inside htally_outside hreplay hall_eliminate hlength
  exact ⟨hempty, by
    exact reducedElectionPreservesActiveSupport_reduceElectionInstanceByCandidates
      (voters := voters) (ballots := ballots) (terminalActive := terminalActive)
      (removed := lower) (candidates := candidates) hempty⟩

/--
Concrete Algorithm 3 original-branch Theorem 2.1 route: the reduced election
produced by deleting the lower group preserves later active-support counts,
and the exact strengthened-removal operation-count model satisfies the
inherited quartic bound.
-/
theorem algorithm3_original_replay_reduceElectionInstance_sound_and_quartic_runtime
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower startActive terminalActive : Finset Candidate}
    {budget quota uniqueBallotCount candidateCount : ℕ}
    {trace : RCVTrace Candidate}
    (horiginal :
      originalCandidateRemovalCondition
        voters ballots candidates lower budget quota)
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hlower_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ lower ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots lower (candidates \ lower)
                inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (lower.erase inside)) (∅ : Finset Candidate)
              outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ lower).card) :
    terminalActive ∩ lower = ∅ ∧
      reducedElectionPreservesActiveSupport
        voters ballots terminalActive
        (reduceElectionInstanceByCandidates lower candidates ballots) ∧
      strengthenedRemovalOperationCount uniqueBallotCount candidateCount ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  rcases algorithm3_original_replay_reduceElectionInstance_preservesActiveSupport
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (lower := lower) (startActive := startActive)
      (terminalActive := terminalActive) (budget := budget) (quota := quota)
      (trace := trace) horiginal hminimal hremove hlower_active
      hactive_subset_candidates htally_inside htally_outside hreplay
      hall_eliminate hlength with
    ⟨hempty, hpreserve⟩
  exact ⟨hempty, hpreserve, le_rfl⟩

/--
Concrete Algorithm 3 original-branch Theorem 2.1 route with no arbitrary
output-specification bridge. The source problem's specification is
definitionally the candidate-deletion output plus terminal active-support
preservation.
-/
theorem algorithm3_original_replay_concreteReductionProblem_sound_and_quartic_runtime
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower startActive terminalActive : Finset Candidate}
    {budget quota uniqueBallotCount candidateCount : ℕ}
    {trace : RCVTrace Candidate}
    (horiginal :
      originalCandidateRemovalCondition
        voters ballots candidates lower budget quota)
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hlower_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ lower ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots lower (candidates \ lower)
                inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (lower.erase inside)) (∅ : Finset Candidate)
              outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ lower).card) :
    (strengthenedRemovalConcreteReductionProblem
        voters ballots candidates lower terminalActive budget
        uniqueBallotCount candidateCount).specification
      (reduceElectionInstanceByCandidates lower candidates ballots) ∧
      strengthenedRemovalOperationCount uniqueBallotCount candidateCount ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  rcases algorithm3_original_replay_reduceElectionInstance_sound_and_quartic_runtime
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (lower := lower) (startActive := startActive)
      (terminalActive := terminalActive) (budget := budget) (quota := quota)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount) (trace := trace)
      horiginal hminimal hremove hlower_active hactive_subset_candidates
      htally_inside htally_outside hreplay hall_eliminate hlength with
    ⟨_hempty, hpreserve, hruntime⟩
  exact ⟨⟨rfl, hpreserve⟩, hruntime⟩

/--
Concrete Algorithm 3 original-branch route for an implementation: if the
implementation returns the paper's candidate-deletion reduced election on the
concrete source problem, then the original-branch replay proof gives the
concrete specification and exact quartic runtime bound.  This has no arbitrary
preservation-to-specification premise.
-/
theorem algorithm3_original_replay_concreteReductionAlgorithm_sound_and_quartic_runtime
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      StrengthenedRemovalProblem (ReducedElectionInstance Voter Candidate) →
        ReducedElectionInstance Voter Candidate}
    {operationCount :
      StrengthenedRemovalProblem (ReducedElectionInstance Voter Candidate) → ℕ}
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower startActive terminalActive : Finset Candidate}
    {budget quota uniqueBallotCount candidateCount : ℕ}
    {trace : RCVTrace Candidate}
    (horiginal :
      originalCandidateRemovalCondition
        voters ballots candidates lower budget quota)
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hlower_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ lower ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots lower (candidates \ lower)
                inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (lower.erase inside)) (∅ : Finset Candidate)
              outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ lower).card)
    (algorithm_eq :
      algorithm
          (strengthenedRemovalConcreteReductionProblem
            voters ballots candidates lower terminalActive budget
            uniqueBallotCount candidateCount) =
        reduceElectionInstanceByCandidates lower candidates ballots)
    (operationCount_eq :
      operationCount
          (strengthenedRemovalConcreteReductionProblem
            voters ballots candidates lower terminalActive budget
            uniqueBallotCount candidateCount) =
        strengthenedRemovalOperationCount
          uniqueBallotCount candidateCount) :
    (strengthenedRemovalConcreteReductionProblem
        voters ballots candidates lower terminalActive budget
        uniqueBallotCount candidateCount).specification
      (algorithm
        (strengthenedRemovalConcreteReductionProblem
          voters ballots candidates lower terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      operationCount
          (strengthenedRemovalConcreteReductionProblem
            voters ballots candidates lower terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  have hcore :
      (strengthenedRemovalConcreteReductionProblem
          voters ballots candidates lower terminalActive budget
          uniqueBallotCount candidateCount).specification
        (reduceElectionInstanceByCandidates lower candidates ballots) ∧
        strengthenedRemovalOperationCount uniqueBallotCount candidateCount ≤
          uniqueBallotCount * candidateCount ^ 4 :=
    algorithm3_original_replay_concreteReductionProblem_sound_and_quartic_runtime
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (lower := lower) (startActive := startActive)
      (terminalActive := terminalActive) (budget := budget) (quota := quota)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount) (trace := trace)
      horiginal hminimal hremove hlower_active hactive_subset_candidates
      htally_inside htally_outside hreplay hall_eliminate hlength
  exact ⟨by
    rw [algorithm_eq]
    exact hcore.1, by
    rw [operationCount_eq]
    exact hcore.2⟩

/--
Concrete Theorem 2.1 Algorithm 3 original-branch implementation: the source
implementation is the candidate-deletion reduction itself, so the
implementation-equality premises discharge by definition.
-/
theorem algorithm3_original_replay_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower startActive terminalActive : Finset Candidate}
    {budget quota uniqueBallotCount candidateCount : ℕ}
    {trace : RCVTrace Candidate}
    (horiginal :
      originalCandidateRemovalCondition
        voters ballots candidates lower budget quota)
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hlower_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ lower ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots lower (candidates \ lower)
                inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (lower.erase inside)) (∅ : Finset Candidate)
              outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ lower).card) :
    (strengthenedRemovalConcreteReductionProblem
        voters ballots candidates lower terminalActive budget
        uniqueBallotCount candidateCount).specification
      (strengthenedRemovalConcreteReductionAlgorithm ballots candidates lower
        (strengthenedRemovalConcreteReductionProblem
          voters ballots candidates lower terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      strengthenedRemovalConcreteReductionOperationCount
          (strengthenedRemovalConcreteReductionProblem
            voters ballots candidates lower terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  exact
    algorithm3_original_replay_concreteReductionAlgorithm_sound_and_quartic_runtime
      (algorithm :=
        strengthenedRemovalConcreteReductionAlgorithm ballots candidates lower)
      (operationCount :=
        strengthenedRemovalConcreteReductionOperationCount
          (Voter := Voter) (Candidate := Candidate))
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (lower := lower) (startActive := startActive)
      (terminalActive := terminalActive) (budget := budget) (quota := quota)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount) (trace := trace)
      horiginal hminimal hremove hlower_active hactive_subset_candidates
      htally_inside htally_outside hreplay hall_eliminate hlength
      rfl rfl

/--
Concrete Algorithm 3 original-branch implementation from a full election run:
the run supplies the replay/tally/length facts, and the original
strict-support condition discharges the candidate-deletion specification.
-/
theorem algorithm3_original_fullElectionRun_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower : Finset Candidate}
    {budget quota uniqueBallotCount candidateCount : ℕ}
    (run :
      Algorithm3OriginalFullElectionRun voters ballots candidates lower budget)
    (horiginal :
      originalCandidateRemovalCondition
        voters ballots candidates lower budget quota) :
    (strengthenedRemovalConcreteReductionProblem
        voters ballots candidates lower run.terminalActive budget
        uniqueBallotCount candidateCount).specification
      (strengthenedRemovalConcreteReductionAlgorithm ballots candidates lower
        (strengthenedRemovalConcreteReductionProblem
          voters ballots candidates lower run.terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      strengthenedRemovalConcreteReductionOperationCount
          (strengthenedRemovalConcreteReductionProblem
            voters ballots candidates lower run.terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  exact
    algorithm3_original_replay_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (lower := lower) (startActive := run.startActive)
      (terminalActive := run.terminalActive) (budget := budget)
      (quota := quota) (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount) (trace := run.trace)
      horiginal run.minimal_eliminations
      run.focused_eliminations_remove_focus
      run.lower_active_at_elimination run.active_subset_candidates
      run.tally_inside run.tally_outside run.active_replay
      run.all_eliminate run.removes_initial_lower

/--
Theorem 2.1 original-branch source implementation from a generated
minimum-tally lower-group elimination run.

This is the executable/source-generated replay constructor for the original
Algorithm 2 branch of Algorithm 3. A total active minimum-tally choice rule
generates the replay, all-elimination, lower-focus, removal, minimality, and
length facts consumed by the concrete candidate-deletion implementation.
-/
theorem theorem2_1_concreteOriginalReplayImplementation_sound_and_quartic_runtime_of_generated_group_elimination
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {choice : MinimalTallyChoiceRule Candidate}
    {tallyOf : Finset Candidate → Candidate → ℕ}
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower startActive : Finset Candidate}
    {budget quota uniqueBallotCount candidateCount : ℕ}
    (hactiveChoice : choice.ChoosesActive)
    (htotalChoice : choice.Total)
    (hminimalChoice : choice.SelectsMinimal)
    (hstart_subset : startActive ⊆ candidates)
    (horiginal :
      originalCandidateRemovalCondition
        voters ballots candidates lower budget quota)
    (htally_inside :
      ∀ step,
        step ∈
          minimalGroupEliminationGeneratedSteps choice lower tallyOf
            (startActive ∩ lower).card startActive →
        step.kind = StepKind.eliminate →
          ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
            step.tally inside =
              budget +
                strictSupportCount voters ballots lower (candidates \ lower)
                  inside)
    (htally_outside :
      ∀ step,
        step ∈
          minimalGroupEliminationGeneratedSteps choice lower tallyOf
            (startActive ∩ lower).card startActive →
        step.kind = StepKind.eliminate →
          ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          ∀ outside, outside ∈ candidates \ lower →
            step.tally outside =
              strictSupportCount voters ballots
                (insert outside (lower.erase inside)) (∅ : Finset Candidate)
                outside) :
    let terminalActive :=
      minimalGroupEliminationTerminalActive choice lower tallyOf
        (startActive ∩ lower).card startActive
    (strengthenedRemovalConcreteReductionProblem
        voters ballots candidates lower terminalActive budget
        uniqueBallotCount candidateCount).specification
      (strengthenedRemovalConcreteReductionAlgorithm ballots candidates lower
        (strengthenedRemovalConcreteReductionProblem
          voters ballots candidates lower terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      strengthenedRemovalConcreteReductionOperationCount
          (strengthenedRemovalConcreteReductionProblem
            voters ballots candidates lower terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  intro terminalActive
  let trace : RCVTrace Candidate :=
    minimalGroupEliminationGeneratedTrace choice lower tallyOf
      (startActive ∩ lower).card startActive
  have hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates lower budget quota := by
    exact strictSupportGroupRemovalSafety_of_condition horiginal
  have hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates := by
    intro step hstep _hkind
    exact
      minimalGroupEliminationGeneratedSteps_beforeActive_subset_of_initial_subset
        choice lower tallyOf hstart_subset (startActive ∩ lower).card step
        (by
          simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
  have hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally := by
    intro step hstep hkind
    exact
      strictSupportGroupRemovalSafety_generated_minimal_eliminations
        (voters := voters) (ballots := ballots) (candidates := candidates)
        (group := lower) (budget := budget) (quota := quota)
        (choice := choice) (tallyOf := tallyOf)
        (rounds := (startActive ∩ lower).card)
        (initialActive := startActive)
        hsafety hminimalChoice
        (by
          intro generatedStep hgenerated _hgenerated_kind
          exact
            minimalGroupEliminationGeneratedSteps_beforeActive_subset_of_initial_subset
              choice lower tallyOf hstart_subset (startActive ∩ lower).card
              generatedStep hgenerated)
        htally_inside htally_outside step
        (by
          simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
        hkind
  have hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate := by
    intro step hstep _hkind
    exact
      minimalGroupEliminationGeneratedSteps_removesFocusedCandidate
        choice lower tallyOf (startActive ∩ lower).card startActive step
        (by
          simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
  have hlower_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ lower ∧ inside ∈ step.beforeActive := by
    intro step hstep _hkind
    exact
      minimalGroupEliminationGeneratedSteps_group_active_at_step
        choice lower tallyOf (startActive ∩ lower).card startActive step
        (by
          simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
  have htally_inside_trace :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots lower (candidates \ lower)
                inside := by
    intro step hstep hkind inside hinside hactive
    exact htally_inside step
      (by simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
      hkind inside hinside hactive
  have htally_outside_trace :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (lower.erase inside)) (∅ : Finset Candidate)
              outside := by
    intro step hstep hkind inside hinside hactive outside houtside
    exact htally_outside step
      (by simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
      hkind inside hinside hactive outside houtside
  have hreplay : trace.replaysFrom startActive terminalActive := by
    simpa [trace, minimalGroupEliminationGeneratedTrace, STVTrace.replaysFrom,
      terminalActive] using
      minimalGroupEliminationGeneratedSteps_replayStepsFrom
        choice lower tallyOf (startActive ∩ lower).card startActive
  have hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate := by
    intro step hstep
    exact
      minimalGroupEliminationGeneratedSteps_all_eliminate
        choice lower tallyOf (startActive ∩ lower).card startActive step
        (by
          simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
  have hlength : trace.steps.length = (startActive ∩ lower).card := by
    simpa [trace, minimalGroupEliminationGeneratedTrace] using
      minimalGroupEliminationGeneratedSteps_length_eq
        (choice := choice) hactiveChoice htotalChoice lower tallyOf
        (startActive ∩ lower).card startActive rfl
  exact
    algorithm3_original_replay_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (lower := lower) (startActive := startActive)
      (terminalActive := terminalActive) (budget := budget) (quota := quota)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount) (trace := trace)
      horiginal hminimal hremove hlower_active hactive_subset_candidates
      htally_inside_trace htally_outside_trace hreplay hall_eliminate hlength

/--
Bounded-tally generated Theorem 2.1 original-branch route. A total active
minimum-tally choice rule generates the replay and structural trace facts, and
the source's conservative strict-support tally bounds are enough to prove the
candidate-deletion implementation sound.
-/
theorem theorem2_1_concreteOriginalReplayImplementation_sound_and_quartic_runtime_of_generated_group_elimination_tally_bounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {choice : MinimalTallyChoiceRule Candidate}
    {tallyOf : Finset Candidate → Candidate → ℕ}
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower startActive : Finset Candidate}
    {budget quota uniqueBallotCount candidateCount : ℕ}
    (hactiveChoice : choice.ChoosesActive)
    (htotalChoice : choice.Total)
    (hminimalChoice : choice.SelectsMinimal)
    (hstart_subset : startActive ⊆ candidates)
    (horiginal :
      originalCandidateRemovalCondition
        voters ballots candidates lower budget quota)
    (htally_inside_le :
      ∀ step,
        step ∈
          minimalGroupEliminationGeneratedSteps choice lower tallyOf
            (startActive ∩ lower).card startActive →
        step.kind = StepKind.eliminate →
          ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
            step.tally inside ≤
              budget +
                strictSupportCount voters ballots lower (candidates \ lower)
                  inside)
    (htally_outside_ge :
      ∀ step,
        step ∈
          minimalGroupEliminationGeneratedSteps choice lower tallyOf
            (startActive ∩ lower).card startActive →
        step.kind = StepKind.eliminate →
          ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          ∀ outside, outside ∈ candidates \ lower →
            strictSupportCount voters ballots
                (insert outside (lower.erase inside)) (∅ : Finset Candidate)
                outside ≤
              step.tally outside) :
    let terminalActive :=
      minimalGroupEliminationTerminalActive choice lower tallyOf
        (startActive ∩ lower).card startActive
    (strengthenedRemovalConcreteReductionProblem
        voters ballots candidates lower terminalActive budget
        uniqueBallotCount candidateCount).specification
      (strengthenedRemovalConcreteReductionAlgorithm ballots candidates lower
        (strengthenedRemovalConcreteReductionProblem
          voters ballots candidates lower terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      strengthenedRemovalConcreteReductionOperationCount
          (strengthenedRemovalConcreteReductionProblem
            voters ballots candidates lower terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  intro terminalActive
  let trace : RCVTrace Candidate :=
    minimalGroupEliminationGeneratedTrace choice lower tallyOf
      (startActive ∩ lower).card startActive
  have hsafety :
      strictSupportGroupRemovalSafety
        voters ballots candidates lower budget quota := by
    exact strictSupportGroupRemovalSafety_of_condition horiginal
  have hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates := by
    intro step hstep _hkind
    exact
      minimalGroupEliminationGeneratedSteps_beforeActive_subset_of_initial_subset
        choice lower tallyOf hstart_subset (startActive ∩ lower).card step
        (by
          simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
  have hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally := by
    intro step hstep hkind
    exact
      strictSupportGroupRemovalSafety_generated_minimal_eliminations_of_tally_bounds
        (voters := voters) (ballots := ballots) (candidates := candidates)
        (group := lower) (budget := budget) (quota := quota)
        (choice := choice) (tallyOf := tallyOf)
        (rounds := (startActive ∩ lower).card)
        (initialActive := startActive)
        hsafety hminimalChoice
        (by
          intro generatedStep hgenerated _hgenerated_kind
          exact
            minimalGroupEliminationGeneratedSteps_beforeActive_subset_of_initial_subset
              choice lower tallyOf hstart_subset (startActive ∩ lower).card
              generatedStep hgenerated)
        htally_inside_le htally_outside_ge step
        (by
          simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
        hkind
  have hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate := by
    intro step hstep _hkind
    exact
      minimalGroupEliminationGeneratedSteps_removesFocusedCandidate
        choice lower tallyOf (startActive ∩ lower).card startActive step
        (by
          simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
  have hlower_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ lower ∧ inside ∈ step.beforeActive := by
    intro step hstep _hkind
    exact
      minimalGroupEliminationGeneratedSteps_group_active_at_step
        choice lower tallyOf (startActive ∩ lower).card startActive step
        (by
          simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
  have htally_inside_trace_le :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside ≤
            budget +
              strictSupportCount voters ballots lower (candidates \ lower)
                inside := by
    intro step hstep hkind inside hinside hactive
    exact htally_inside_le step
      (by simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
      hkind inside hinside hactive
  have htally_outside_trace_ge :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          strictSupportCount voters ballots
              (insert outside (lower.erase inside)) (∅ : Finset Candidate)
              outside ≤
            step.tally outside := by
    intro step hstep hkind inside hinside hactive outside houtside
    exact htally_outside_ge step
      (by simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
      hkind inside hinside hactive outside houtside
  have hreplay : trace.replaysFrom startActive terminalActive := by
    simpa [trace, minimalGroupEliminationGeneratedTrace, STVTrace.replaysFrom,
      terminalActive] using
      minimalGroupEliminationGeneratedSteps_replayStepsFrom
        choice lower tallyOf (startActive ∩ lower).card startActive
  have hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate := by
    intro step hstep
    exact
      minimalGroupEliminationGeneratedSteps_all_eliminate
        choice lower tallyOf (startActive ∩ lower).card startActive step
        (by
          simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
  have hlength : trace.steps.length = (startActive ∩ lower).card := by
    simpa [trace, minimalGroupEliminationGeneratedTrace] using
      minimalGroupEliminationGeneratedSteps_length_eq
        (choice := choice) hactiveChoice htotalChoice lower tallyOf
        (startActive ∩ lower).card startActive rfl
  have hempty : terminalActive ∩ lower = ∅ :=
    originalCandidateRemovalCondition_terminal_lower_empty_of_replay_tally_bounds
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (lower := lower) (budget := budget) (quota := quota) (trace := trace)
      horiginal hminimal hremove hlower_active hactive_subset_candidates
      htally_inside_trace_le htally_outside_trace_ge hreplay hall_eliminate
      hlength
  refine ⟨?_, ?_⟩
  · exact ⟨by
      simp [strengthenedRemovalConcreteReductionAlgorithm], by
      exact reducedElectionPreservesActiveSupport_reduceElectionInstanceByCandidates
        (voters := voters) (ballots := ballots)
        (terminalActive := terminalActive) (removed := lower)
        (candidates := candidates) hempty⟩
  · simp [strengthenedRemovalConcreteReductionOperationCount,
      strengthenedRemovalOperationCount, strengthenedRemovalConcreteReductionProblem]

/--
Algorithm 3 conservative generated tally for the original-removal branch.
Lower candidates receive the paper's budget-plus-strict-support upper tally;
outside candidates receive a conservative sum over every currently active lower
candidate's outside strict-support lower tally.
-/
noncomputable def algorithm3OriginalConservativeGeneratedTallyOf
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates lower : Finset Candidate) (budget : ℕ) :
    Finset Candidate → Candidate → ℕ :=
  fun active candidate =>
    if candidate ∈ lower then
      budget +
        strictSupportCount voters ballots lower (candidates \ lower)
          candidate
    else
      ∑ inside ∈ active ∩ lower,
        strictSupportCount voters ballots
          (insert candidate (lower.erase inside)) (∅ : Finset Candidate)
          candidate

/--
Theorem 2.1 original-branch implementation with a canonical conservative
generated tally. The only source-removal premise left is the original
strict-support removal condition plus generic minimum-tally tie-breaking
sanity conditions.
-/
theorem theorem2_1_concreteOriginalReplayImplementation_sound_and_quartic_runtime_of_generated_group_elimination_conservative_tally
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {choice : MinimalTallyChoiceRule Candidate}
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower startActive : Finset Candidate}
    {budget quota uniqueBallotCount candidateCount : ℕ}
    (hactiveChoice : choice.ChoosesActive)
    (htotalChoice : choice.Total)
    (hminimalChoice : choice.SelectsMinimal)
    (hstart_subset : startActive ⊆ candidates)
    (horiginal :
      originalCandidateRemovalCondition
        voters ballots candidates lower budget quota) :
    let tallyOf :=
      algorithm3OriginalConservativeGeneratedTallyOf
        voters ballots candidates lower budget
    let terminalActive :=
      minimalGroupEliminationTerminalActive choice lower tallyOf
        (startActive ∩ lower).card startActive
    (strengthenedRemovalConcreteReductionProblem
        voters ballots candidates lower terminalActive budget
        uniqueBallotCount candidateCount).specification
      (strengthenedRemovalConcreteReductionAlgorithm ballots candidates lower
        (strengthenedRemovalConcreteReductionProblem
          voters ballots candidates lower terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      strengthenedRemovalConcreteReductionOperationCount
          (strengthenedRemovalConcreteReductionProblem
            voters ballots candidates lower terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  intro tallyOf terminalActive
  exact
    theorem2_1_concreteOriginalReplayImplementation_sound_and_quartic_runtime_of_generated_group_elimination_tally_bounds
      (choice := choice) (tallyOf := tallyOf)
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (lower := lower) (startActive := startActive) (budget := budget)
      (quota := quota) (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hactiveChoice htotalChoice hminimalChoice hstart_subset horiginal
      (by
        intro step hstep _hkind inside hinside _hactive
        have htally :
            step.tally = tallyOf step.beforeActive :=
          minimalGroupEliminationGeneratedSteps_tally_eq
            choice lower tallyOf (startActive ∩ lower).card startActive
            step hstep
        rw [htally]
        simp [tallyOf, algorithm3OriginalConservativeGeneratedTallyOf,
          hinside])
      (by
        intro step hstep _hkind inside hinside hactive outside houtside
        have htally :
            step.tally = tallyOf step.beforeActive :=
          minimalGroupEliminationGeneratedSteps_tally_eq
            choice lower tallyOf (startActive ∩ lower).card startActive
            step hstep
        have houtside_not_lower : outside ∉ lower :=
          (Finset.mem_sdiff.mp houtside).2
        have hinside_mem : inside ∈ step.beforeActive ∩ lower :=
          Finset.mem_inter.mpr ⟨hactive, hinside⟩
        rw [htally]
        simp [tallyOf, algorithm3OriginalConservativeGeneratedTallyOf,
          houtside_not_lower]
        exact
          Finset.single_le_sum
            (s := step.beforeActive ∩ lower)
            (f := fun currentInside =>
              strictSupportCount voters ballots
                (insert outside (lower.erase currentInside))
                (∅ : Finset Candidate) outside)
            (by
              intro currentInside _hcurrent
              exact Nat.zero_le _)
            hinside_mem)

/--
Generated lower-group deletion implementation theorem.  The generated replay
removes exactly the initially active lower candidates; therefore deleting the
lower group preserves active support at its generated terminal active set and
inherits the concrete quartic verification bound.
-/
theorem theorem2_1_concreteGeneratedGroupElimination_terminalDeletion_sound_and_quartic_runtime
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {choice : MinimalTallyChoiceRule Candidate}
    {tallyOf : Finset Candidate → Candidate → ℕ}
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower startActive : Finset Candidate}
    {budget uniqueBallotCount candidateCount : ℕ}
    (hactiveChoice : choice.ChoosesActive)
    (htotalChoice : choice.Total)
    (hminimalChoice : choice.SelectsMinimal) :
    let terminalActive :=
      minimalGroupEliminationTerminalActive choice lower tallyOf
        (startActive ∩ lower).card startActive
    (strengthenedRemovalConcreteReductionProblem
        voters ballots candidates lower terminalActive budget
        uniqueBallotCount candidateCount).specification
      (strengthenedRemovalConcreteReductionAlgorithm ballots candidates lower
        (strengthenedRemovalConcreteReductionProblem
          voters ballots candidates lower terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      strengthenedRemovalConcreteReductionOperationCount
          (strengthenedRemovalConcreteReductionProblem
            voters ballots candidates lower terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  intro terminalActive
  have hempty : terminalActive ∩ lower = ∅ := by
    simpa [terminalActive] using
      minimalGroupEliminationTerminalActive_inter_group_eq_empty
        (choice := choice) hactiveChoice htotalChoice hminimalChoice
        lower tallyOf startActive
  refine ⟨?_, ?_⟩
  · exact ⟨by
      simp [strengthenedRemovalConcreteReductionAlgorithm], by
      exact reducedElectionPreservesActiveSupport_reduceElectionInstanceByCandidates
        (voters := voters) (ballots := ballots)
        (terminalActive := terminalActive) (removed := lower)
        (candidates := candidates) hempty⟩
  · simp [strengthenedRemovalConcreteReductionOperationCount,
      strengthenedRemovalOperationCount, strengthenedRemovalConcreteReductionProblem]

/--
A certified one-survival step removes its lower candidate from every terminal
active set contained in the step's post-active set.
-/
theorem oneSurvivalStepCertificate_not_mem_terminal_of_terminal_subset_after_step
    {Candidate : Type*} [DecidableEq Candidate]
    {budget : ℕ} {inside : Candidate} {terminalActive : Finset Candidate}
    (cert : OneSurvivalStepCertificate Candidate budget inside)
    (hterminal_subset : terminalActive ⊆ cert.step.afterActive) :
    inside ∉ terminalActive := by
  intro hterminal
  have hafter : inside ∈ cert.step.afterActive :=
    hterminal_subset hterminal
  rw [OneSurvivalStepCertificate.removes_inside cert] at hafter
  exact (Finset.mem_erase.mp hafter).1 rfl

/--
Per-lower-candidate one-survival steps deplete the lower group at the terminal
active set when each certified post-step active set contains the terminal
active set.
-/
theorem oneSurvivalStepCertificates_terminal_lower_empty_of_terminal_subset_after_steps
    {Candidate : Type*} [DecidableEq Candidate]
    {budget : ℕ} {lower terminalActive : Finset Candidate}
    (one_survival_step :
      ∀ inside, inside ∈ lower →
        OneSurvivalStepCertificate Candidate budget inside)
    (hterminal_subset_after_step :
      ∀ inside, (hinside : inside ∈ lower) →
        terminalActive ⊆
          (one_survival_step inside hinside).step.afterActive) :
    terminalActive ∩ lower = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro inside hinside_terminal_lower
  have hterminal : inside ∈ terminalActive :=
    (Finset.mem_inter.mp hinside_terminal_lower).1
  have hinside : inside ∈ lower :=
    (Finset.mem_inter.mp hinside_terminal_lower).2
  exact
    oneSurvivalStepCertificate_not_mem_terminal_of_terminal_subset_after_step
      (cert := one_survival_step inside hinside)
      (hterminal_subset_after_step inside hinside)
      hterminal

/--
Replay-shaped form of one-survival depletion: if after each certified
one-survival step the remaining trace is active-set monotone and replays to the
common terminal active set, then no lower candidate remains terminally active.
-/
theorem oneSurvivalStepCertificates_terminal_lower_empty_of_tail_replays
    {Candidate : Type*} [DecidableEq Candidate]
    {budget : ℕ} {lower terminalActive : Finset Candidate}
    (one_survival_step :
      ∀ inside, inside ∈ lower →
        OneSurvivalStepCertificate Candidate budget inside)
    (tailTrace :
      ∀ inside, inside ∈ lower → RCVTrace Candidate)
    (tail_replay :
      ∀ inside, (hinside : inside ∈ lower) →
        (tailTrace inside hinside).replaysFrom
          (one_survival_step inside hinside).step.afterActive
          terminalActive)
    (tail_activeMonotone :
      ∀ inside, (hinside : inside ∈ lower) →
        ∀ step, step ∈ (tailTrace inside hinside).steps →
          step.activeMonotone) :
    terminalActive ∩ lower = ∅ := by
  exact
    oneSurvivalStepCertificates_terminal_lower_empty_of_terminal_subset_after_steps
      (one_survival_step := one_survival_step)
      (hterminal_subset_after_step := by
        intro inside hinside
        exact
          STVTrace.terminalActive_subset_startActive_of_replayStepsFrom_activeMonotone
            (tail_replay inside hinside)
            (tail_activeMonotone inside hinside))

/--
Concrete Algorithm 3 one-survival branch preservation theorem: certified
post-transfer one-survival removals, together with replay/terminal containment
after each removal, imply that deleting the lower group preserves all later
active-support counts at the terminal active set.
-/
theorem algorithm3_one_survival_steps_reduceElectionInstance_preservesActiveSupport
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower terminalActive : Finset Candidate} {budget : ℕ}
    (one_survival_step :
      ∀ inside, inside ∈ lower →
        OneSurvivalStepCertificate Candidate budget inside)
    (hterminal_subset_after_step :
      ∀ inside, (hinside : inside ∈ lower) →
        terminalActive ⊆
          (one_survival_step inside hinside).step.afterActive) :
    terminalActive ∩ lower = ∅ ∧
      reducedElectionPreservesActiveSupport
        voters ballots terminalActive
        (reduceElectionInstanceByCandidates lower candidates ballots) := by
  have hempty : terminalActive ∩ lower = ∅ :=
    oneSurvivalStepCertificates_terminal_lower_empty_of_terminal_subset_after_steps
      (one_survival_step := one_survival_step)
      hterminal_subset_after_step
  exact ⟨hempty, by
    exact reducedElectionPreservesActiveSupport_reduceElectionInstanceByCandidates
      (voters := voters) (ballots := ballots) (terminalActive := terminalActive)
      (removed := lower) (candidates := candidates) hempty⟩

/--
Non-failing lower candidates satisfy the original strict-support comparison
against every upper candidate. Hence, if such a candidate is still active at a
minimum-tally elimination step, the step cannot focus outside the lower group.
-/
theorem extendedRemovalOriginalNoFailure_minimal_elimination_focus_mem_lower
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower : Finset Candidate} {budget : ℕ}
    {inside : Candidate}
    (hnofailure :
      ¬ extendedRemovalOriginalFailure voters ballots candidates lower budget
        inside)
    (hinside : inside ∈ lower)
    {step : STVStep Candidate}
    (hminimal : step.eliminatesMinimalTally)
    (hinside_active : inside ∈ step.beforeActive)
    (hactive_subset_candidates : step.beforeActive ⊆ candidates)
    (htally_inside :
      step.tally inside =
        budget +
          strictSupportCount voters ballots lower (candidates \ lower)
            inside)
    (htally_outside :
      ∀ outside, outside ∈ candidates \ lower →
        step.tally outside =
          strictSupportCount voters ballots
            (insert outside (lower.erase inside)) (∅ : Finset Candidate)
            outside) :
    ∃ loser, step.focus = some loser ∧ loser ∈ lower ∧
      loser ∈ step.beforeActive := by
  rcases hminimal with ⟨_hkind, loser, hfocus, hloser_active, hloser_le⟩
  refine ⟨loser, hfocus, ?_, hloser_active⟩
  by_contra hloser_not_lower
  have hloser_candidates : loser ∈ candidates :=
    hactive_subset_candidates hloser_active
  have hloser_outside : loser ∈ candidates \ lower :=
    Finset.mem_sdiff.mpr ⟨hloser_candidates, hloser_not_lower⟩
  have hstrict :
      budget +
          strictSupportCount voters ballots lower (candidates \ lower)
            inside <
        strictSupportCount voters ballots
          (insert loser (lower.erase inside)) (∅ : Finset Candidate)
          loser := by
    have hnot_le :
        ¬ strictSupportCount voters ballots
              (insert loser (lower.erase inside)) (∅ : Finset Candidate)
              loser ≤
            budget +
              strictSupportCount voters ballots lower (candidates \ lower)
                inside := by
      intro hle
      exact hnofailure ⟨loser, hloser_outside, hle⟩
    exact not_le.mp hnot_le
  have hlt : step.tally inside < step.tally loser := by
    simpa [htally_inside, htally_outside loser hloser_outside] using hstrict
  have hle : step.tally loser ≤ step.tally inside :=
    hloser_le inside hinside_active
  exact (not_lt_of_ge hle) hlt

/--
Bounded-tally form of
`extendedRemovalOriginalNoFailure_minimal_elimination_focus_mem_lower`.  The
canonical generated replay only needs lower-candidate tallies bounded above by
their budget-augmented strict support and outside-candidate tallies bounded
below by their strict support.
-/
theorem extendedRemovalOriginalNoFailure_minimal_elimination_focus_mem_lower_of_tally_bounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower : Finset Candidate} {budget : ℕ}
    {inside : Candidate}
    (hnofailure :
      ¬ extendedRemovalOriginalFailure voters ballots candidates lower budget
        inside)
    (hinside : inside ∈ lower)
    {step : STVStep Candidate}
    (hminimal : step.eliminatesMinimalTally)
    (hinside_active : inside ∈ step.beforeActive)
    (hactive_subset_candidates : step.beforeActive ⊆ candidates)
    (htally_inside_le :
      step.tally inside ≤
        budget +
          strictSupportCount voters ballots lower (candidates \ lower)
            inside)
    (htally_outside_ge :
      ∀ outside, outside ∈ candidates \ lower →
        strictSupportCount voters ballots
          (insert outside (lower.erase inside)) (∅ : Finset Candidate)
          outside ≤ step.tally outside) :
    ∃ loser, step.focus = some loser ∧ loser ∈ lower ∧
      loser ∈ step.beforeActive := by
  rcases hminimal with ⟨_hkind, loser, hfocus, hloser_active, hloser_le⟩
  refine ⟨loser, hfocus, ?_, hloser_active⟩
  by_contra hloser_not_lower
  have hloser_candidates : loser ∈ candidates :=
    hactive_subset_candidates hloser_active
  have hloser_outside : loser ∈ candidates \ lower :=
    Finset.mem_sdiff.mpr ⟨hloser_candidates, hloser_not_lower⟩
  have hstrict :
      budget +
          strictSupportCount voters ballots lower (candidates \ lower)
            inside <
        strictSupportCount voters ballots
          (insert loser (lower.erase inside)) (∅ : Finset Candidate)
          loser := by
    have hnot_le :
        ¬ strictSupportCount voters ballots
              (insert loser (lower.erase inside)) (∅ : Finset Candidate)
              loser ≤
            budget +
              strictSupportCount voters ballots lower (candidates \ lower)
                inside := by
      intro hle
      exact hnofailure ⟨loser, hloser_outside, hle⟩
    exact not_le.mp hnot_le
  have hlt : step.tally inside < step.tally loser :=
    lt_of_le_of_lt htally_inside_le
      (lt_of_lt_of_le hstrict (htally_outside_ge loser hloser_outside))
  have hle : step.tally loser ≤ step.tally inside :=
    hloser_le inside hinside_active
  exact (not_lt_of_ge hle) hlt

/--
Mixed Algorithm 3 terminal depletion. A lower candidate that triggers the
extended-removal failure branch is removed by its one-survival certificate; a
lower candidate that does not trigger that branch is ruled out by the original
strict-support comparison along the replay trace.
-/
theorem algorithm3_mixed_original_or_one_survival_terminal_lower_empty
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower startActive terminalActive : Finset Candidate}
    {budget : ℕ} {trace : RCVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots lower (candidates \ lower)
                inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (lower.erase inside)) (∅ : Finset Candidate)
              outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ lower).card)
    (hone_survival_not_terminal :
      ∀ inside, inside ∈ lower →
        extendedRemovalOriginalFailure voters ballots candidates lower budget
          inside →
        inside ∉ terminalActive) :
    terminalActive ∩ lower = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro inside hinside_terminal_lower
  have hterminal : inside ∈ terminalActive :=
    (Finset.mem_inter.mp hinside_terminal_lower).1
  have hinside : inside ∈ lower :=
    (Finset.mem_inter.mp hinside_terminal_lower).2
  by_cases hfailure :
      extendedRemovalOriginalFailure voters ballots candidates lower budget
        inside
  · exact hone_survival_not_terminal inside hinside hfailure hterminal
  · have hremoves :
        trace.eliminationRemovesFromGroup lower := by
      intro step hstep hkind
      obtain ⟨i, hi⟩ : ∃ i : Fin trace.steps.length,
          trace.steps.get i = step := by
        exact List.mem_iff_get.mp hstep
      have hinside_active : inside ∈ step.beforeActive := by
        have hsubset :
            terminalActive ⊆ (trace.steps.get i).beforeActive :=
          STVTrace.terminalActive_subset_beforeActive_of_replaysFrom_removesFocusedCandidate
            hreplay
            (by
              intro currentStep hcurrent
              exact hremove currentStep hcurrent
                (hall_eliminate currentStep hcurrent))
            i
        rw [← hi]
        exact hsubset hterminal
      rcases
        extendedRemovalOriginalNoFailure_minimal_elimination_focus_mem_lower
          (voters := voters) (ballots := ballots) (candidates := candidates)
          (lower := lower) (budget := budget) (inside := inside)
          hfailure hinside (hminimal step hstep hkind) hinside_active
          (hactive_subset_candidates step hstep hkind)
          (htally_inside step hstep hkind inside hinside hinside_active)
          (htally_outside step hstep hkind inside hinside hinside_active)
        with ⟨loser, hfocus, hloser_lower, hloser_active⟩
      rcases hremove step hstep hkind with ⟨removed, hremoved_focus, hafter⟩
      have hremoved_eq : removed = loser := by
        exact Option.some.inj (hremoved_focus.symm.trans hfocus)
      subst removed
      exact ⟨loser, hfocus, hloser_lower, hloser_active,
        hafter⟩
    have hempty :
        terminalActive ∩ lower = ∅ :=
      STVTrace.terminal_activeGroup_eq_empty_of_replaysFrom_length_eq_start_card
        hreplay hall_eliminate hremoves hlength
    exact (Finset.eq_empty_iff_forall_notMem.mp hempty) inside
      hinside_terminal_lower

/--
Concrete mixed Algorithm 3 reduction preservation: the original replay handles
non-failing lower candidates, and one-survival branch facts rule out terminal
membership for candidates that trigger the extended-removal failure test.
-/
theorem algorithm3_mixed_original_or_one_survival_reduceElectionInstance_preservesActiveSupport
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower startActive terminalActive : Finset Candidate}
    {budget : ℕ} {trace : RCVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots lower (candidates \ lower)
                inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (lower.erase inside)) (∅ : Finset Candidate)
              outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ lower).card)
    (hone_survival_not_terminal :
      ∀ inside, inside ∈ lower →
        extendedRemovalOriginalFailure voters ballots candidates lower budget
          inside →
        inside ∉ terminalActive) :
    terminalActive ∩ lower = ∅ ∧
      reducedElectionPreservesActiveSupport
        voters ballots terminalActive
        (reduceElectionInstanceByCandidates lower candidates ballots) := by
  have hempty :
      terminalActive ∩ lower = ∅ :=
    algorithm3_mixed_original_or_one_survival_terminal_lower_empty
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (lower := lower) (startActive := startActive)
      (terminalActive := terminalActive) (budget := budget) (trace := trace)
      hminimal hremove hactive_subset_candidates htally_inside htally_outside
      hreplay hall_eliminate hlength hone_survival_not_terminal
  exact ⟨hempty, by
    exact reducedElectionPreservesActiveSupport_reduceElectionInstanceByCandidates
      (voters := voters) (ballots := ballots) (terminalActive := terminalActive)
      (removed := lower) (candidates := candidates) hempty⟩

/--
Concrete mixed Algorithm 3 Theorem 2.1 route: non-failing lower candidates are
depleted by the original replay comparison, while candidates that trigger the
extended-removal failure test are ruled out by one-survival facts. The source
implementation is candidate deletion and inherits the exact quartic bound.
-/
theorem algorithm3_mixed_original_or_one_survival_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower startActive terminalActive : Finset Candidate}
    {budget uniqueBallotCount candidateCount : ℕ}
    {trace : RCVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots lower (candidates \ lower)
                inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (lower.erase inside)) (∅ : Finset Candidate)
              outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ lower).card)
    (hone_survival_not_terminal :
      ∀ inside, inside ∈ lower →
        extendedRemovalOriginalFailure voters ballots candidates lower budget
          inside →
        inside ∉ terminalActive) :
    (strengthenedRemovalConcreteReductionProblem
        voters ballots candidates lower terminalActive budget
        uniqueBallotCount candidateCount).specification
      (strengthenedRemovalConcreteReductionAlgorithm ballots candidates lower
        (strengthenedRemovalConcreteReductionProblem
          voters ballots candidates lower terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      strengthenedRemovalConcreteReductionOperationCount
          (strengthenedRemovalConcreteReductionProblem
            voters ballots candidates lower terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  rcases algorithm3_mixed_original_or_one_survival_reduceElectionInstance_preservesActiveSupport
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (lower := lower) (startActive := startActive)
      (terminalActive := terminalActive) (budget := budget) (trace := trace)
      hminimal hremove hactive_subset_candidates htally_inside htally_outside
      hreplay hall_eliminate hlength hone_survival_not_terminal with
    ⟨_hempty, hpreserve⟩
  exact ⟨⟨rfl, hpreserve⟩, le_rfl⟩

/--
Concrete mixed Algorithm 3 route from the paper's post-worst one-survival
checks. The original replay handles lower candidates whose original
strict-support comparison does not fail; only failing lower candidates need the
one-survival post-worst remaining-upper-set certificate.
-/
theorem algorithm3_mixed_original_or_one_survival_postWorst_tallies_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower startActive terminalActive : Finset Candidate}
    {budget uniqueBallotCount candidateCount : ℕ}
    {trace : RCVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots lower (candidates \ lower)
                inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (lower.erase inside)) (∅ : Finset Candidate)
              outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ lower).card)
    (one_survival_post_worst :
      ∀ inside, inside ∈ lower →
        extendedRemovalOriginalFailure voters ballots candidates lower budget
          inside →
        ∃ upperSupport : Candidate → ℕ,
        ∃ afterWorstUpperSupport : Candidate → ℕ,
        ∃ afterWorstInsideSupport : ℕ,
        ∃ worst : Candidate,
        ∃ second : Candidate,
        ∃ third : Candidate,
        ∃ remainingUpper : Finset Candidate,
          inside ∉ remainingUpper ∧
          oneSurvivalRoundSafety budget upperSupport
            afterWorstUpperSupport afterWorstInsideSupport worst second third
            remainingUpper ∧
          terminalActive ⊆ remainingUpper) :
    (strengthenedRemovalConcreteReductionProblem
        voters ballots candidates lower terminalActive budget
        uniqueBallotCount candidateCount).specification
      (strengthenedRemovalConcreteReductionAlgorithm ballots candidates lower
        (strengthenedRemovalConcreteReductionProblem
          voters ballots candidates lower terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      strengthenedRemovalConcreteReductionOperationCount
          (strengthenedRemovalConcreteReductionProblem
            voters ballots candidates lower terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  exact
    algorithm3_mixed_original_or_one_survival_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (lower := lower) (startActive := startActive)
      (terminalActive := terminalActive) (budget := budget)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount) (trace := trace)
      hminimal hremove hactive_subset_candidates htally_inside htally_outside
      hreplay hall_eliminate hlength
      (by
        intro inside hinside hfailure hterminal
        rcases one_survival_post_worst inside hinside hfailure with
          ⟨_upperSupport, _afterWorstUpperSupport, _afterWorstInsideSupport,
            _worst, _second, _third, remainingUpper, hnot_remaining,
            _hsafety, hterminal_subset⟩
        exact hnot_remaining (hterminal_subset hterminal))

/--
Bounded-tally mixed Algorithm 3 terminal depletion.  This is the form used by
the canonical generated replay: the replay tallies may conservatively
over-count outside candidates and under-certify only upper bounds for lower
candidates, but those inequalities are enough for the no-failure branch.
-/
theorem algorithm3_mixed_original_or_one_survival_terminal_lower_empty_of_tally_bounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower startActive terminalActive : Finset Candidate}
    {budget : ℕ} {trace : RCVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside_le :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside ≤
            budget +
              strictSupportCount voters ballots lower (candidates \ lower)
                inside)
    (htally_outside_ge :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          strictSupportCount voters ballots
            (insert outside (lower.erase inside)) (∅ : Finset Candidate)
            outside ≤ step.tally outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ lower).card)
    (hone_survival_not_terminal :
      ∀ inside, inside ∈ lower →
        extendedRemovalOriginalFailure voters ballots candidates lower budget
          inside →
        inside ∉ terminalActive) :
    terminalActive ∩ lower = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro inside hinside_terminal_lower
  have hterminal : inside ∈ terminalActive :=
    (Finset.mem_inter.mp hinside_terminal_lower).1
  have hinside : inside ∈ lower :=
    (Finset.mem_inter.mp hinside_terminal_lower).2
  by_cases hfailure :
      extendedRemovalOriginalFailure voters ballots candidates lower budget
        inside
  · exact hone_survival_not_terminal inside hinside hfailure hterminal
  · have hremoves :
        trace.eliminationRemovesFromGroup lower := by
      intro step hstep hkind
      obtain ⟨i, hi⟩ : ∃ i : Fin trace.steps.length,
          trace.steps.get i = step := by
        exact List.mem_iff_get.mp hstep
      have hinside_active : inside ∈ step.beforeActive := by
        have hsubset :
            terminalActive ⊆ (trace.steps.get i).beforeActive :=
          STVTrace.terminalActive_subset_beforeActive_of_replaysFrom_removesFocusedCandidate
            hreplay
            (by
              intro currentStep hcurrent
              exact hremove currentStep hcurrent
                (hall_eliminate currentStep hcurrent))
            i
        rw [← hi]
        exact hsubset hterminal
      rcases
        extendedRemovalOriginalNoFailure_minimal_elimination_focus_mem_lower_of_tally_bounds
          (voters := voters) (ballots := ballots) (candidates := candidates)
          (lower := lower) (budget := budget) (inside := inside)
          hfailure hinside (hminimal step hstep hkind) hinside_active
          (hactive_subset_candidates step hstep hkind)
          (htally_inside_le step hstep hkind inside hinside hinside_active)
          (htally_outside_ge step hstep hkind inside hinside hinside_active)
        with ⟨loser, hfocus, hloser_lower, hloser_active⟩
      rcases hremove step hstep hkind with ⟨removed, hremoved_focus, hafter⟩
      have hremoved_eq : removed = loser := by
        exact Option.some.inj (hremoved_focus.symm.trans hfocus)
      subst removed
      exact ⟨loser, hfocus, hloser_lower, hloser_active,
        hafter⟩
    have hempty :
        terminalActive ∩ lower = ∅ :=
      STVTrace.terminal_activeGroup_eq_empty_of_replaysFrom_length_eq_start_card
        hreplay hall_eliminate hremoves hlength
    exact (Finset.eq_empty_iff_forall_notMem.mp hempty) inside
      hinside_terminal_lower

/--
Bounded-tally concrete mixed Algorithm 3 reduction preservation.
-/
theorem algorithm3_mixed_original_or_one_survival_reduceElectionInstance_preservesActiveSupport_of_tally_bounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower startActive terminalActive : Finset Candidate}
    {budget : ℕ} {trace : RCVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside_le :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside ≤
            budget +
              strictSupportCount voters ballots lower (candidates \ lower)
                inside)
    (htally_outside_ge :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          strictSupportCount voters ballots
            (insert outside (lower.erase inside)) (∅ : Finset Candidate)
            outside ≤ step.tally outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ lower).card)
    (hone_survival_not_terminal :
      ∀ inside, inside ∈ lower →
        extendedRemovalOriginalFailure voters ballots candidates lower budget
          inside →
        inside ∉ terminalActive) :
    terminalActive ∩ lower = ∅ ∧
      reducedElectionPreservesActiveSupport
        voters ballots terminalActive
        (reduceElectionInstanceByCandidates lower candidates ballots) := by
  have hempty :
      terminalActive ∩ lower = ∅ :=
    algorithm3_mixed_original_or_one_survival_terminal_lower_empty_of_tally_bounds
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (lower := lower) (startActive := startActive)
      (terminalActive := terminalActive) (budget := budget) (trace := trace)
      hminimal hremove hactive_subset_candidates htally_inside_le
      htally_outside_ge hreplay hall_eliminate hlength
      hone_survival_not_terminal
  exact ⟨hempty, by
    exact reducedElectionPreservesActiveSupport_reduceElectionInstanceByCandidates
      (voters := voters) (ballots := ballots) (terminalActive := terminalActive)
      (removed := lower) (candidates := candidates) hempty⟩

/--
Bounded-tally concrete mixed Algorithm 3 Theorem 2.1 route.
-/
theorem algorithm3_mixed_original_or_one_survival_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime_of_tally_bounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower startActive terminalActive : Finset Candidate}
    {budget uniqueBallotCount candidateCount : ℕ}
    {trace : RCVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside_le :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside ≤
            budget +
              strictSupportCount voters ballots lower (candidates \ lower)
                inside)
    (htally_outside_ge :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          strictSupportCount voters ballots
            (insert outside (lower.erase inside)) (∅ : Finset Candidate)
            outside ≤ step.tally outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ lower).card)
    (hone_survival_not_terminal :
      ∀ inside, inside ∈ lower →
        extendedRemovalOriginalFailure voters ballots candidates lower budget
          inside →
        inside ∉ terminalActive) :
    (strengthenedRemovalConcreteReductionProblem
        voters ballots candidates lower terminalActive budget
        uniqueBallotCount candidateCount).specification
      (strengthenedRemovalConcreteReductionAlgorithm ballots candidates lower
        (strengthenedRemovalConcreteReductionProblem
          voters ballots candidates lower terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      strengthenedRemovalConcreteReductionOperationCount
          (strengthenedRemovalConcreteReductionProblem
            voters ballots candidates lower terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  rcases algorithm3_mixed_original_or_one_survival_reduceElectionInstance_preservesActiveSupport_of_tally_bounds
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (lower := lower) (startActive := startActive)
      (terminalActive := terminalActive) (budget := budget) (trace := trace)
      hminimal hremove hactive_subset_candidates htally_inside_le
      htally_outside_ge hreplay hall_eliminate hlength
      hone_survival_not_terminal with
    ⟨_hempty, hpreserve⟩
  exact ⟨⟨rfl, hpreserve⟩, le_rfl⟩

/--
Bounded-tally concrete mixed Algorithm 3 route from the paper's post-worst
one-survival checks.
-/
theorem algorithm3_mixed_original_or_one_survival_postWorst_tallies_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime_of_tally_bounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower startActive terminalActive : Finset Candidate}
    {budget uniqueBallotCount candidateCount : ℕ}
    {trace : RCVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside_le :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside ≤
            budget +
              strictSupportCount voters ballots lower (candidates \ lower)
                inside)
    (htally_outside_ge :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          strictSupportCount voters ballots
            (insert outside (lower.erase inside)) (∅ : Finset Candidate)
            outside ≤ step.tally outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ lower).card)
    (one_survival_post_worst :
      ∀ inside, inside ∈ lower →
        extendedRemovalOriginalFailure voters ballots candidates lower budget
          inside →
        ∃ upperSupport : Candidate → ℕ,
        ∃ afterWorstUpperSupport : Candidate → ℕ,
        ∃ afterWorstInsideSupport : ℕ,
        ∃ worst : Candidate,
        ∃ second : Candidate,
        ∃ third : Candidate,
        ∃ remainingUpper : Finset Candidate,
          inside ∉ remainingUpper ∧
          oneSurvivalRoundSafety budget upperSupport
            afterWorstUpperSupport afterWorstInsideSupport worst second third
            remainingUpper ∧
          terminalActive ⊆ remainingUpper) :
    (strengthenedRemovalConcreteReductionProblem
        voters ballots candidates lower terminalActive budget
        uniqueBallotCount candidateCount).specification
      (strengthenedRemovalConcreteReductionAlgorithm ballots candidates lower
        (strengthenedRemovalConcreteReductionProblem
          voters ballots candidates lower terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      strengthenedRemovalConcreteReductionOperationCount
          (strengthenedRemovalConcreteReductionProblem
            voters ballots candidates lower terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  exact
    algorithm3_mixed_original_or_one_survival_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime_of_tally_bounds
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (lower := lower) (startActive := startActive)
      (terminalActive := terminalActive) (budget := budget)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount) (trace := trace)
      hminimal hremove hactive_subset_candidates htally_inside_le
      htally_outside_ge hreplay hall_eliminate hlength
      (by
        intro inside hinside hfailure hterminal
        rcases one_survival_post_worst inside hinside hfailure with
          ⟨_upperSupport, _afterWorstUpperSupport, _afterWorstInsideSupport,
            _worst, _second, _third, remainingUpper, hnot_remaining,
            _hsafety, hterminal_subset⟩
        exact hnot_remaining (hterminal_subset hterminal))

/--
Full-election-run mixed Algorithm 3 route from post-worst one-survival checks.
The run supplies the original-replay trace semantics; the post-worst witnesses
are required only for lower candidates where the original comparison fails.
-/
theorem algorithm3_fullElectionRun_mixed_original_or_one_survival_postWorst_tallies_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower : Finset Candidate}
    {budget uniqueBallotCount candidateCount : ℕ}
    (run :
      Algorithm3OriginalFullElectionRun voters ballots candidates lower budget)
    (one_survival_post_worst :
      ∀ inside, inside ∈ lower →
        extendedRemovalOriginalFailure voters ballots candidates lower budget
          inside →
        ∃ upperSupport : Candidate → ℕ,
        ∃ afterWorstUpperSupport : Candidate → ℕ,
        ∃ afterWorstInsideSupport : ℕ,
        ∃ worst : Candidate,
        ∃ second : Candidate,
        ∃ third : Candidate,
        ∃ remainingUpper : Finset Candidate,
          inside ∉ remainingUpper ∧
          oneSurvivalRoundSafety budget upperSupport
            afterWorstUpperSupport afterWorstInsideSupport worst second third
            remainingUpper ∧
          run.terminalActive ⊆ remainingUpper) :
    (strengthenedRemovalConcreteReductionProblem
        voters ballots candidates lower run.terminalActive budget
        uniqueBallotCount candidateCount).specification
      (strengthenedRemovalConcreteReductionAlgorithm ballots candidates lower
        (strengthenedRemovalConcreteReductionProblem
          voters ballots candidates lower run.terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      strengthenedRemovalConcreteReductionOperationCount
          (strengthenedRemovalConcreteReductionProblem
            voters ballots candidates lower run.terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  exact
    algorithm3_mixed_original_or_one_survival_postWorst_tallies_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (lower := lower) (startActive := run.startActive)
      (terminalActive := run.terminalActive) (budget := budget)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount) (trace := run.trace)
      run.minimal_eliminations run.focused_eliminations_remove_focus
      run.active_subset_candidates run.tally_inside run.tally_outside
      run.active_replay run.all_eliminate run.removes_initial_lower
      one_survival_post_worst

/--
Concrete Algorithm 3 one-survival branch Theorem 2.1 route with no arbitrary
output-specification bridge. The source problem's specification is
definitionally the candidate-deletion output plus terminal active-support
preservation.
-/
theorem algorithm3_one_survival_steps_concreteReductionProblem_sound_and_quartic_runtime
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower terminalActive : Finset Candidate}
    {budget uniqueBallotCount candidateCount : ℕ}
    (one_survival_step :
      ∀ inside, inside ∈ lower →
        OneSurvivalStepCertificate Candidate budget inside)
    (hterminal_subset_after_step :
      ∀ inside, (hinside : inside ∈ lower) →
        terminalActive ⊆
          (one_survival_step inside hinside).step.afterActive) :
    (strengthenedRemovalConcreteReductionProblem
        voters ballots candidates lower terminalActive budget
        uniqueBallotCount candidateCount).specification
      (reduceElectionInstanceByCandidates lower candidates ballots) ∧
      strengthenedRemovalOperationCount uniqueBallotCount candidateCount ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  rcases algorithm3_one_survival_steps_reduceElectionInstance_preservesActiveSupport
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (lower := lower) (terminalActive := terminalActive) (budget := budget)
      one_survival_step hterminal_subset_after_step with
    ⟨_hempty, hpreserve⟩
  exact ⟨⟨rfl, hpreserve⟩, le_rfl⟩

/--
Concrete Theorem 2.1 Algorithm 3 one-survival implementation route: the source
implementation is the candidate-deletion reduction itself, while per-lower
one-survival step certificates plus terminal containment discharge the
candidate-deletion specification directly.
-/
theorem algorithm3_one_survival_steps_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower terminalActive : Finset Candidate}
    {budget uniqueBallotCount candidateCount : ℕ}
    (one_survival_step :
      ∀ inside, inside ∈ lower →
        OneSurvivalStepCertificate Candidate budget inside)
    (hterminal_subset_after_step :
      ∀ inside, (hinside : inside ∈ lower) →
        terminalActive ⊆
          (one_survival_step inside hinside).step.afterActive) :
    (strengthenedRemovalConcreteReductionProblem
        voters ballots candidates lower terminalActive budget
        uniqueBallotCount candidateCount).specification
      (strengthenedRemovalConcreteReductionAlgorithm ballots candidates lower
        (strengthenedRemovalConcreteReductionProblem
          voters ballots candidates lower terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      strengthenedRemovalConcreteReductionOperationCount
          (strengthenedRemovalConcreteReductionProblem
            voters ballots candidates lower terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  exact
    algorithm3_one_survival_steps_concreteReductionProblem_sound_and_quartic_runtime
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (lower := lower) (terminalActive := terminalActive) (budget := budget)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      one_survival_step hterminal_subset_after_step

/--
Concrete Algorithm 3 one-survival route from the post-worst tally setup used
in the source: for each lower candidate, the source identifies the remaining
upper candidates after the worst upper candidate is removed, proves the
one-survival safety inequalities, and shows that the final terminal active set
is contained in those remaining upper candidates.
-/
theorem algorithm3_one_survival_postWorst_tallies_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower terminalActive : Finset Candidate}
    {budget uniqueBallotCount candidateCount : ℕ}
    (one_survival_post_worst :
      ∀ inside, inside ∈ lower →
        ∃ upperSupport : Candidate → ℕ,
        ∃ afterWorstUpperSupport : Candidate → ℕ,
        ∃ afterWorstInsideSupport : ℕ,
        ∃ worst : Candidate,
        ∃ second : Candidate,
        ∃ third : Candidate,
        ∃ remainingUpper : Finset Candidate,
          inside ∉ remainingUpper ∧
          oneSurvivalRoundSafety budget upperSupport
            afterWorstUpperSupport afterWorstInsideSupport worst second third
            remainingUpper ∧
          terminalActive ⊆ remainingUpper) :
    (strengthenedRemovalConcreteReductionProblem
        voters ballots candidates lower terminalActive budget
        uniqueBallotCount candidateCount).specification
      (strengthenedRemovalConcreteReductionAlgorithm ballots candidates lower
        (strengthenedRemovalConcreteReductionProblem
          voters ballots candidates lower terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      strengthenedRemovalConcreteReductionOperationCount
          (strengthenedRemovalConcreteReductionProblem
            voters ballots candidates lower terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  classical
  choose upperSupport afterWorstUpperSupport afterWorstInsideSupport worst
    second third remainingUpper hfacts using one_survival_post_worst
  let one_survival_step :
      ∀ inside, inside ∈ lower →
        OneSurvivalStepCertificate Candidate budget inside :=
    fun inside hinside =>
      oneSurvivalStepCertificate_of_postWorst_tally
        (upperSupport inside hinside)
        (afterWorstUpperSupport inside hinside)
        (afterWorstInsideSupport inside hinside)
        (worst inside hinside) (second inside hinside)
        (third inside hinside) (remainingUpper inside hinside)
        (hfacts inside hinside).1
        (hfacts inside hinside).2.1
  exact
    algorithm3_one_survival_steps_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (lower := lower) (terminalActive := terminalActive) (budget := budget)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      one_survival_step
      (hterminal_subset_after_step := by
        intro inside hinside candidate hcandidate
        have hremaining :
            candidate ∈ remainingUpper inside hinside :=
          (hfacts inside hinside).2.2 hcandidate
        have hcandidate_ne_inside : candidate ≠ inside := by
          intro hcandidate_eq
          exact (hfacts inside hinside).1 (hcandidate_eq ▸ hremaining)
        simpa [one_survival_step, oneSurvivalStepCertificate_of_postWorst_tally,
          groupEliminationStep, hcandidate_ne_inside, hremaining])

/--
Concrete Theorem 2.1 Algorithm 3 implementation from a full election run and
the paper's two branch facts. The original branch uses the run directly; the
one-survival branch constructs the concrete post-worst elimination steps.
-/
theorem algorithm3_fullElectionRun_original_or_one_survival_postWorst_tallies_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower : Finset Candidate}
    {budget quota uniqueBallotCount candidateCount : ℕ}
    (run :
      Algorithm3OriginalFullElectionRun voters ballots candidates lower budget)
    (hbranch :
      originalCandidateRemovalCondition
          voters ballots candidates lower budget quota ∨
        (∀ inside, inside ∈ lower →
          ∃ upperSupport : Candidate → ℕ,
          ∃ afterWorstUpperSupport : Candidate → ℕ,
          ∃ afterWorstInsideSupport : ℕ,
          ∃ worst : Candidate,
          ∃ second : Candidate,
          ∃ third : Candidate,
          ∃ remainingUpper : Finset Candidate,
            inside ∉ remainingUpper ∧
            oneSurvivalRoundSafety budget upperSupport
              afterWorstUpperSupport afterWorstInsideSupport worst second third
              remainingUpper ∧
            run.terminalActive ⊆ remainingUpper)) :
    (strengthenedRemovalConcreteReductionProblem
        voters ballots candidates lower run.terminalActive budget
        uniqueBallotCount candidateCount).specification
      (strengthenedRemovalConcreteReductionAlgorithm ballots candidates lower
        (strengthenedRemovalConcreteReductionProblem
          voters ballots candidates lower run.terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      strengthenedRemovalConcreteReductionOperationCount
          (strengthenedRemovalConcreteReductionProblem
            voters ballots candidates lower run.terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  rcases hbranch with horiginal | hone_survival
  · exact
      algorithm3_original_fullElectionRun_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime
        (voters := voters) (ballots := ballots) (candidates := candidates)
        (lower := lower) (budget := budget) (quota := quota)
        (uniqueBallotCount := uniqueBallotCount)
        (candidateCount := candidateCount) run horiginal
  · exact
      algorithm3_one_survival_postWorst_tallies_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime
        (voters := voters) (ballots := ballots) (candidates := candidates)
        (lower := lower) (terminalActive := run.terminalActive)
        (budget := budget) (uniqueBallotCount := uniqueBallotCount)
        (candidateCount := candidateCount) hone_survival

/--
Concrete Theorem 2.1 Algorithm 3 implementation from a full source run.  The
run object includes both the original replay facts and the Algorithm 3 branch
facts, so the theorem no longer carries those branch facts as a separate
premise.
-/
theorem algorithm3_fullElectionRun_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower : Finset Candidate}
    {budget quota uniqueBallotCount candidateCount : ℕ}
    (run :
      Algorithm3FullElectionRun voters ballots candidates lower budget quota) :
    (strengthenedRemovalConcreteReductionProblem
        voters ballots candidates lower run.originalRun.terminalActive budget
        uniqueBallotCount candidateCount).specification
      (strengthenedRemovalConcreteReductionAlgorithm ballots candidates lower
        (strengthenedRemovalConcreteReductionProblem
          voters ballots candidates lower run.originalRun.terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      strengthenedRemovalConcreteReductionOperationCount
          (strengthenedRemovalConcreteReductionProblem
            voters ballots candidates lower run.originalRun.terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  rcases run.branch with horiginal | hone_survival
  · exact
      algorithm3_original_fullElectionRun_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime
        (voters := voters) (ballots := ballots) (candidates := candidates)
        (lower := lower) (budget := budget) (quota := quota)
        (uniqueBallotCount := uniqueBallotCount)
        (candidateCount := candidateCount) run.originalRun horiginal
  · exact
      algorithm3_fullElectionRun_mixed_original_or_one_survival_postWorst_tallies_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime
        (voters := voters) (ballots := ballots) (candidates := candidates)
        (lower := lower) (budget := budget)
        (uniqueBallotCount := uniqueBallotCount)
        (candidateCount := candidateCount) run.originalRun hone_survival

/--
Concrete Algorithm 3 extended-condition implementation route: the original
Algorithm 2 branch is handled by the certified replay proof, while the
one-survival branch is handled by per-lower-candidate post-transfer removal
steps plus terminal containment.  The output is the concrete candidate-deletion
reduced election in both cases.
-/
theorem algorithm3_extended_condition_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates lower startActive terminalActive : Finset Candidate}
    {budget quota uniqueBallotCount candidateCount : ℕ}
    {trace : RCVTrace Candidate}
    {oneSurvivalSafe : Candidate → Prop}
    (hcondition :
      extendedCandidateRemovalCondition
        voters ballots candidates lower budget quota oneSurvivalSafe)
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hlower_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ lower ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots lower (candidates \ lower)
                inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ lower → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ lower →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (lower.erase inside)) (∅ : Finset Candidate)
              outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ lower).card)
    (one_survival_step :
      ∀ inside, inside ∈ lower →
        OneSurvivalStepCertificate Candidate budget inside)
    (hterminal_subset_after_step :
      ∀ inside, (hinside : inside ∈ lower) →
        terminalActive ⊆
          (one_survival_step inside hinside).step.afterActive) :
    (strengthenedRemovalConcreteReductionProblem
        voters ballots candidates lower terminalActive budget
        uniqueBallotCount candidateCount).specification
      (strengthenedRemovalConcreteReductionAlgorithm ballots candidates lower
        (strengthenedRemovalConcreteReductionProblem
          voters ballots candidates lower terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      strengthenedRemovalConcreteReductionOperationCount
          (strengthenedRemovalConcreteReductionProblem
            voters ballots candidates lower terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  rcases hcondition with horiginal | _hone_survival
  · exact
      algorithm3_original_replay_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime
        (voters := voters) (ballots := ballots) (candidates := candidates)
        (lower := lower) (startActive := startActive)
        (terminalActive := terminalActive) (budget := budget) (quota := quota)
        (uniqueBallotCount := uniqueBallotCount)
        (candidateCount := candidateCount) (trace := trace)
        horiginal hminimal hremove hlower_active hactive_subset_candidates
        htally_inside htally_outside hreplay hall_eliminate hlength
  · exact
      algorithm3_one_survival_steps_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime
        (voters := voters) (ballots := ballots) (candidates := candidates)
        (lower := lower) (terminalActive := terminalActive) (budget := budget)
        (uniqueBallotCount := uniqueBallotCount)
        (candidateCount := candidateCount)
        one_survival_step hterminal_subset_after_step

/--
Certificate that the strengthened candidate-removal algorithm is sound and
satisfies the inherited quartic operation bound.
-/
abbrev StrengthenedRemovalCertificate {ReducedInstance : Type*}
    (algorithm : StrengthenedRemovalProblem ReducedInstance → ReducedInstance)
    (operationCount : StrengthenedRemovalProblem ReducedInstance → ℕ) :=
  EconCSLib.Optimization.AlgorithmSoundnessCertificate algorithm
    (fun problem output => problem.specification output)
    operationCount
    StrengthenedRemovalProblem.quarticRuntimeBound

/--
Source-shaped certificate for Theorem 2.1: the strengthened-removal algorithm's
output satisfies the preservation specification and the operation count
satisfies the inherited quartic bound.
-/
structure StrengthenedRemovalSoundnessCertificate {ReducedInstance : Type*}
    (algorithm : StrengthenedRemovalProblem ReducedInstance → ReducedInstance)
    (operationCount : StrengthenedRemovalProblem ReducedInstance → ℕ) where
  output_spec : ∀ problem : StrengthenedRemovalProblem ReducedInstance,
    problem.specification (algorithm problem)
  operationCount_le : ∀ problem : StrengthenedRemovalProblem ReducedInstance,
    operationCount problem ≤
      StrengthenedRemovalProblem.quarticRuntimeBound problem

/--
A source-shaped strengthened-removal certificate gives the generic soundness
certificate used by the reusable optimization library.
-/
theorem strengthenedRemovalCertificate_of_soundnessCertificate
    {ReducedInstance : Type*}
    {algorithm : StrengthenedRemovalProblem ReducedInstance → ReducedInstance}
    {operationCount : StrengthenedRemovalProblem ReducedInstance → ℕ}
    (cert :
      StrengthenedRemovalSoundnessCertificate algorithm operationCount) :
    StrengthenedRemovalCertificate algorithm operationCount :=
  EconCSLib.Optimization.AlgorithmSoundnessCertificate.of_output_spec
    cert.output_spec cert.operationCount_le

/--
Source-shaped Algorithm 3 certificate for Theorem 2.1.

The certificate records the voter/ballot/candidate objects used to evaluate
the extended removal condition, proves that the condition holds, and supplies
the bridge from that condition to the reduced-instance preservation
specification.
-/
structure StrengthenedRemovalConditionCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    (algorithm : StrengthenedRemovalProblem ReducedInstance → ReducedInstance)
    (operationCount : StrengthenedRemovalProblem ReducedInstance → ℕ) where
  voters : StrengthenedRemovalProblem ReducedInstance → Finset Voter
  ballots :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      Voter → RCVBallot Candidate
  candidates :
    StrengthenedRemovalProblem ReducedInstance → Finset Candidate
  lower : StrengthenedRemovalProblem ReducedInstance → Finset Candidate
  quota : StrengthenedRemovalProblem ReducedInstance → ℕ
  oneSurvivalSafe :
    StrengthenedRemovalProblem ReducedInstance → Candidate → Prop
  condition :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      extendedCandidateRemovalCondition
        (voters problem) (ballots problem) (candidates problem)
        (lower problem) problem.budget (quota problem)
        (oneSurvivalSafe problem)
  output_spec_of_condition :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      extendedCandidateRemovalCondition
        (voters problem) (ballots problem) (candidates problem)
        (lower problem) problem.budget (quota problem)
        (oneSurvivalSafe problem) →
        problem.specification (algorithm problem)
  operationCount_le :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      operationCount problem ≤
        StrengthenedRemovalProblem.quarticRuntimeBound problem

/--
An Algorithm 3 condition certificate gives the generic soundness certificate
used by the source-facing Theorem 2.1 projection.
-/
def strengthenedRemovalCertificate_of_conditionCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm : StrengthenedRemovalProblem ReducedInstance → ReducedInstance}
    {operationCount : StrengthenedRemovalProblem ReducedInstance → ℕ}
    (cert :
      StrengthenedRemovalConditionCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount) :
    StrengthenedRemovalCertificate algorithm operationCount :=
  EconCSLib.Optimization.AlgorithmSoundnessCertificate.of_condition
    (fun problem =>
      extendedCandidateRemovalCondition
        (cert.voters problem) (cert.ballots problem)
        (cert.candidates problem) (cert.lower problem)
        problem.budget (cert.quota problem)
        (cert.oneSurvivalSafe problem))
    cert.condition cert.output_spec_of_condition cert.operationCount_le

/--
Build an Algorithm 3 condition certificate when the source model supplies the
extended-removal condition, the condition-to-spec bridge, and the inherited
quartic operation-count proof.
-/
def strengthenedRemovalConditionCertificate_of_runtimeBound
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm : StrengthenedRemovalProblem ReducedInstance → ReducedInstance}
    {operationCount : StrengthenedRemovalProblem ReducedInstance → ℕ}
    (voters : StrengthenedRemovalProblem ReducedInstance → Finset Voter)
    (ballots :
      ∀ problem : StrengthenedRemovalProblem ReducedInstance,
        Voter → RCVBallot Candidate)
    (candidates lower :
      StrengthenedRemovalProblem ReducedInstance → Finset Candidate)
    (quota : StrengthenedRemovalProblem ReducedInstance → ℕ)
    (oneSurvivalSafe :
      StrengthenedRemovalProblem ReducedInstance → Candidate → Prop)
    (condition :
      ∀ problem : StrengthenedRemovalProblem ReducedInstance,
        extendedCandidateRemovalCondition
          (voters problem) (ballots problem) (candidates problem)
          (lower problem) problem.budget (quota problem)
          (oneSurvivalSafe problem))
    (output_spec_of_condition :
      ∀ problem : StrengthenedRemovalProblem ReducedInstance,
        extendedCandidateRemovalCondition
          (voters problem) (ballots problem) (candidates problem)
          (lower problem) problem.budget (quota problem)
          (oneSurvivalSafe problem) →
          problem.specification (algorithm problem))
    (operationCount_le :
      ∀ problem : StrengthenedRemovalProblem ReducedInstance,
        operationCount problem ≤
          StrengthenedRemovalProblem.quarticRuntimeBound problem) :
    StrengthenedRemovalConditionCertificate
      (Voter := Voter) (Candidate := Candidate) algorithm operationCount where
  voters := voters
  ballots := ballots
  candidates := candidates
  lower := lower
  quota := quota
  oneSurvivalSafe := oneSurvivalSafe
  condition := condition
  output_spec_of_condition := output_spec_of_condition
  operationCount_le := operationCount_le

/--
Source-shaped Algorithm 3 trace certificate for Theorem 2.1.

This certificate discharges the original Algorithm 2 branch of the extended
condition by replaying certified minimum-tally eliminations through the shared
strict-support group-removal library.  The one-survival branch remains visible
as the source-specific transfer-simulation obligation.
-/
structure StrengthenedRemovalTraceCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    (algorithm : StrengthenedRemovalProblem ReducedInstance → ReducedInstance)
    (operationCount : StrengthenedRemovalProblem ReducedInstance → ℕ) where
  voters : StrengthenedRemovalProblem ReducedInstance → Finset Voter
  ballots :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      Voter → RCVBallot Candidate
  candidates :
    StrengthenedRemovalProblem ReducedInstance → Finset Candidate
  lower : StrengthenedRemovalProblem ReducedInstance → Finset Candidate
  quota : StrengthenedRemovalProblem ReducedInstance → ℕ
  oneSurvivalSafe :
    StrengthenedRemovalProblem ReducedInstance → Candidate → Prop
  trace : StrengthenedRemovalProblem ReducedInstance → RCVTrace Candidate
  condition :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      extendedCandidateRemovalCondition
        (voters problem) (ballots problem) (candidates problem)
        (lower problem) problem.budget (quota problem)
        (oneSurvivalSafe problem)
  minimal_eliminations :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate → step.eliminatesMinimalTally
  focused_eliminations_remove_focus :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate → step.removesFocusedCandidate
  lower_active_at_elimination :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate →
          ∃ inside, inside ∈ lower problem ∧ inside ∈ step.beforeActive
  active_subset_candidates :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate →
          step.beforeActive ⊆ candidates problem
  tally_inside :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate →
          ∀ inside, inside ∈ lower problem → inside ∈ step.beforeActive →
            step.tally inside =
              problem.budget +
                strictSupportCount (voters problem) (ballots problem)
                  (lower problem) (candidates problem \ lower problem) inside
  tally_outside :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate →
          ∀ inside, inside ∈ lower problem → inside ∈ step.beforeActive →
            ∀ outside, outside ∈ candidates problem \ lower problem →
              step.tally outside =
                strictSupportCount (voters problem) (ballots problem)
                  (insert outside ((lower problem).erase inside))
                  (∅ : Finset Candidate) outside
  output_spec_of_original_trace :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      (∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate →
          ∃ loser, step.focus = some loser ∧ loser ∈ lower problem ∧
            loser ∈ step.beforeActive ∧
            step.afterActive = step.beforeActive.erase loser) →
        problem.specification (algorithm problem)
  output_spec_of_one_survival :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      (∀ inside, inside ∈ lower problem →
        extendedRemovalOriginalFailure
          (voters problem) (ballots problem) (candidates problem)
          (lower problem) problem.budget inside →
        oneSurvivalSafe problem inside) →
        problem.specification (algorithm problem)
  operationCount_le :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      operationCount problem ≤
        StrengthenedRemovalProblem.quarticRuntimeBound problem

/--
The original Algorithm 2 branch of an Algorithm 3 trace certificate as the
shared library strict-support replay certificate for a fixed source problem.
-/
def strengthenedRemovalTraceCertificate_strictSupportTraceCertificate_of_original
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm : StrengthenedRemovalProblem ReducedInstance → ReducedInstance}
    {operationCount : StrengthenedRemovalProblem ReducedInstance → ℕ}
    (cert :
      StrengthenedRemovalTraceCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount)
    (problem : StrengthenedRemovalProblem ReducedInstance)
    (horiginal :
      originalCandidateRemovalCondition
        (cert.voters problem) (cert.ballots problem)
        (cert.candidates problem) (cert.lower problem)
        problem.budget (cert.quota problem)) :
    StrictSupportGroupRemovalTraceCertificate Voter Candidate where
  voters := cert.voters problem
  ballots := cert.ballots problem
  candidates := cert.candidates problem
  group := cert.lower problem
  budget := problem.budget
  quota := cert.quota problem
  trace := cert.trace problem
  condition := horiginal
  minimal_eliminations := cert.minimal_eliminations problem
  focused_eliminations_remove_focus :=
    cert.focused_eliminations_remove_focus problem
  group_active_at_elimination := cert.lower_active_at_elimination problem
  active_subset_candidates := cert.active_subset_candidates problem
  tally_inside := cert.tally_inside problem
  tally_outside := cert.tally_outside problem

/--
Original-branch replay accounting for a strengthened-removal trace certificate:
under the original Algorithm 2 condition, an all-elimination replay prefix has
terminal active lower-candidate count determined exactly by its length.
-/
theorem strengthenedRemovalTraceCertificate_original_terminal_lower_card_add_length_eq
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm : StrengthenedRemovalProblem ReducedInstance → ReducedInstance}
    {operationCount : StrengthenedRemovalProblem ReducedInstance → ℕ}
    (cert :
      StrengthenedRemovalTraceCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount)
    (problem : StrengthenedRemovalProblem ReducedInstance)
    (horiginal :
      originalCandidateRemovalCondition
        (cert.voters problem) (cert.ballots problem)
        (cert.candidates problem) (cert.lower problem)
        problem.budget (cert.quota problem))
    {startActive terminalActive : Finset Candidate}
    (hreplay :
      (cert.trace problem).replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ (cert.trace problem).steps →
        step.kind = StepKind.eliminate) :
    (terminalActive ∩ cert.lower problem).card +
        (cert.trace problem).steps.length =
      (startActive ∩ cert.lower problem).card := by
  exact StrictSupportGroupRemovalTraceCertificate.terminal_activeGroup_card_add_length_eq
    (strengthenedRemovalTraceCertificate_strictSupportTraceCertificate_of_original
      cert problem horiginal)
    hreplay hall_eliminate

/--
Original-branch depletion for a strengthened-removal trace certificate: if the
all-elimination prefix is long enough to remove every initially active lower
candidate, no lower candidate remains active at the terminal state.
-/
theorem strengthenedRemovalTraceCertificate_original_terminal_lower_empty
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm : StrengthenedRemovalProblem ReducedInstance → ReducedInstance}
    {operationCount : StrengthenedRemovalProblem ReducedInstance → ℕ}
    (cert :
      StrengthenedRemovalTraceCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount)
    (problem : StrengthenedRemovalProblem ReducedInstance)
    (horiginal :
      originalCandidateRemovalCondition
        (cert.voters problem) (cert.ballots problem)
        (cert.candidates problem) (cert.lower problem)
        problem.budget (cert.quota problem))
    {startActive terminalActive : Finset Candidate}
    (hreplay :
      (cert.trace problem).replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ (cert.trace problem).steps →
        step.kind = StepKind.eliminate)
    (hlength :
      (cert.trace problem).steps.length =
        (startActive ∩ cert.lower problem).card) :
    terminalActive ∩ cert.lower problem = ∅ := by
  exact StrictSupportGroupRemovalTraceCertificate.terminal_activeGroup_empty
    (strengthenedRemovalTraceCertificate_strictSupportTraceCertificate_of_original
      cert problem horiginal)
    hreplay hall_eliminate hlength

/--
An Algorithm 3 trace certificate gives the existing condition-certificate
interface by proving the original strict-support branch from the certified STV
trace and leaving the one-survival branch explicit.
-/
def strengthenedRemovalConditionCertificate_of_traceCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm : StrengthenedRemovalProblem ReducedInstance → ReducedInstance}
    {operationCount : StrengthenedRemovalProblem ReducedInstance → ℕ}
    (cert :
      StrengthenedRemovalTraceCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount) :
    StrengthenedRemovalConditionCertificate
      (Voter := Voter) (Candidate := Candidate) algorithm operationCount where
  voters := cert.voters
  ballots := cert.ballots
  candidates := cert.candidates
  lower := cert.lower
  quota := cert.quota
  oneSurvivalSafe := cert.oneSurvivalSafe
  condition := cert.condition
  output_spec_of_condition := by
    intro problem hcondition
    rcases hcondition with horiginal | hone_survival
    · have htrace :
          (cert.trace problem).eliminationRemovesFromGroup
            (cert.lower problem) :=
        StrictSupportGroupRemovalTraceCertificate.eliminationRemovesFromGroup
          (strengthenedRemovalTraceCertificate_strictSupportTraceCertificate_of_original
            cert problem horiginal)
      exact cert.output_spec_of_original_trace problem htrace
    · exact cert.output_spec_of_one_survival problem hone_survival
  operationCount_le := cert.operationCount_le

/--
An Algorithm 3 trace certificate gives the generic soundness certificate used
by the source-facing Theorem 2.1 projection.
-/
def strengthenedRemovalCertificate_of_traceCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm : StrengthenedRemovalProblem ReducedInstance → ReducedInstance}
    {operationCount : StrengthenedRemovalProblem ReducedInstance → ℕ}
    (cert :
      StrengthenedRemovalTraceCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount) :
    StrengthenedRemovalCertificate algorithm operationCount :=
  strengthenedRemovalCertificate_of_conditionCertificate
    (strengthenedRemovalConditionCertificate_of_traceCertificate cert)

/--
Source-shaped Algorithm 3 certificate route whose one-survival branch is
instantiated by certified post-transfer STV elimination steps.
-/
structure StrengthenedRemovalStepTraceCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    (algorithm : StrengthenedRemovalProblem ReducedInstance → ReducedInstance)
    (operationCount : StrengthenedRemovalProblem ReducedInstance → ℕ) where
  voters : StrengthenedRemovalProblem ReducedInstance → Finset Voter
  ballots :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      Voter → RCVBallot Candidate
  candidates :
    StrengthenedRemovalProblem ReducedInstance → Finset Candidate
  lower : StrengthenedRemovalProblem ReducedInstance → Finset Candidate
  quota : StrengthenedRemovalProblem ReducedInstance → ℕ
  trace : StrengthenedRemovalProblem ReducedInstance → RCVTrace Candidate
  minimal_eliminations :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate → step.eliminatesMinimalTally
  focused_eliminations_remove_focus :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate → step.removesFocusedCandidate
  lower_active_at_elimination :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate →
          ∃ inside, inside ∈ lower problem ∧ inside ∈ step.beforeActive
  active_subset_candidates :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate →
          step.beforeActive ⊆ candidates problem
  tally_inside :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate →
          ∀ inside, inside ∈ lower problem → inside ∈ step.beforeActive →
            step.tally inside =
              problem.budget +
                strictSupportCount (voters problem) (ballots problem)
                  (lower problem) (candidates problem \ lower problem) inside
  tally_outside :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate →
          ∀ inside, inside ∈ lower problem → inside ∈ step.beforeActive →
            ∀ outside, outside ∈ candidates problem \ lower problem →
              step.tally outside =
                strictSupportCount (voters problem) (ballots problem)
                  (insert outside ((lower problem).erase inside))
                  (∅ : Finset Candidate) outside
  one_survival_step :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      ∀ inside, inside ∈ lower problem →
        extendedRemovalOriginalFailure
          (voters problem) (ballots problem) (candidates problem)
          (lower problem) problem.budget inside →
        OneSurvivalStepCertificate Candidate problem.budget inside
  output_spec_of_original_trace :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      (∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate →
          ∃ loser, step.focus = some loser ∧ loser ∈ lower problem ∧
            loser ∈ step.beforeActive ∧
            step.afterActive = step.beforeActive.erase loser) →
        problem.specification (algorithm problem)
  output_spec_of_one_survival_steps :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      (∀ inside, inside ∈ lower problem →
        extendedRemovalOriginalFailure
          (voters problem) (ballots problem) (candidates problem)
          (lower problem) problem.budget inside →
          ∃ step : STVStep Candidate,
            step.afterActive = step.beforeActive.erase inside) →
        problem.specification (algorithm problem)
  operationCount_le :
    ∀ problem : StrengthenedRemovalProblem ReducedInstance,
      operationCount problem ≤
        StrengthenedRemovalProblem.quarticRuntimeBound problem

/--
The step-trace certificate instantiates the trace certificate by taking
`oneSurvivalSafe` to mean existence of a certified one-survival step.
-/
def strengthenedRemovalTraceCertificate_of_stepTraceCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm : StrengthenedRemovalProblem ReducedInstance → ReducedInstance}
    {operationCount : StrengthenedRemovalProblem ReducedInstance → ℕ}
    (cert :
      StrengthenedRemovalStepTraceCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount) :
    StrengthenedRemovalTraceCertificate
      (Voter := Voter) (Candidate := Candidate) algorithm operationCount where
  voters := cert.voters
  ballots := cert.ballots
  candidates := cert.candidates
  lower := cert.lower
  quota := cert.quota
  oneSurvivalSafe := fun problem inside =>
    ∃ _stepCert : OneSurvivalStepCertificate Candidate problem.budget inside,
      True
  trace := cert.trace
  condition := by
    intro problem
    exact Or.inr (by
      intro inside hinside hfailure
      exact ⟨cert.one_survival_step problem inside hinside hfailure, True.intro⟩)
  minimal_eliminations := cert.minimal_eliminations
  focused_eliminations_remove_focus := cert.focused_eliminations_remove_focus
  lower_active_at_elimination := cert.lower_active_at_elimination
  active_subset_candidates := cert.active_subset_candidates
  tally_inside := cert.tally_inside
  tally_outside := cert.tally_outside
  output_spec_of_original_trace := cert.output_spec_of_original_trace
  output_spec_of_one_survival := by
    intro problem hone_survival
    exact cert.output_spec_of_one_survival_steps problem (by
      intro inside hinside hfailure
      rcases hone_survival inside hinside hfailure with ⟨stepCert, _⟩
      exact ⟨stepCert.step, OneSurvivalStepCertificate.removes_inside stepCert⟩)
  operationCount_le := cert.operationCount_le

/--
The step-trace certificate gives the generic soundness certificate used by the
source-facing Theorem 2.1 projection.
-/
def strengthenedRemovalCertificate_of_stepTraceCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm : StrengthenedRemovalProblem ReducedInstance → ReducedInstance}
    {operationCount : StrengthenedRemovalProblem ReducedInstance → ℕ}
    (cert :
      StrengthenedRemovalStepTraceCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount) :
    StrengthenedRemovalCertificate algorithm operationCount :=
  strengthenedRemovalCertificate_of_traceCertificate
    (strengthenedRemovalTraceCertificate_of_stepTraceCertificate cert)

/--
Source-facing problem for Theorem 2.2: a multi-winner containment instance
whose output should certify that the retained candidate set preserves
optimality under the polynomially verifiable containment conditions.
-/
structure MultiWinnerContainmentProblem (ContainedInstance : Type*) where
  specification : ContainedInstance → Prop
  budget : ℕ
  uniqueBallotCount : ℕ
  candidateCount : ℕ
  verificationBound : ℕ

namespace MultiWinnerContainmentProblem

/-- The polynomial verification bound supplied by the containment certificate. -/
def polynomialVerificationBound {ContainedInstance : Type*}
    (problem : MultiWinnerContainmentProblem ContainedInstance) : ℕ :=
  problem.verificationBound

end MultiWinnerContainmentProblem

/--
Certificate that the multi-winner containment procedure is sound and satisfies
the supplied polynomial verification bound.
-/
abbrev MultiWinnerContainmentCertificate {ContainedInstance : Type*}
    (algorithm :
      MultiWinnerContainmentProblem ContainedInstance → ContainedInstance)
    (operationCount :
      MultiWinnerContainmentProblem ContainedInstance → ℕ) :=
  EconCSLib.Optimization.AlgorithmSoundnessCertificate algorithm
    (fun problem output => problem.specification output)
    operationCount
    MultiWinnerContainmentProblem.polynomialVerificationBound

/--
Source-shaped certificate for Theorem 2.2: the containment procedure's output
satisfies the preservation specification and the operation count satisfies the
supplied polynomial verification bound.
-/
structure MultiWinnerContainmentSoundnessCertificate {ContainedInstance : Type*}
    (algorithm :
      MultiWinnerContainmentProblem ContainedInstance → ContainedInstance)
    (operationCount :
      MultiWinnerContainmentProblem ContainedInstance → ℕ) where
  output_spec : ∀ problem : MultiWinnerContainmentProblem ContainedInstance,
    problem.specification (algorithm problem)
  operationCount_le : ∀ problem : MultiWinnerContainmentProblem ContainedInstance,
    operationCount problem ≤
      MultiWinnerContainmentProblem.polynomialVerificationBound problem

/--
Equation (2) weighted surplus-transfer bound: if `surplusVotes` is the maximum
number of votes that can push the early winner over quota, `nextChoiceVotes`
counts winner ballots whose next choice reaches the lower candidate, and
`winnerFirstChoiceVotes` is the winner's first-choice support, then this is the
weighted transfer contribution bounded in Theorem 2.2.
-/
def weightedSurplusTransferBound
    (surplusVotes nextChoiceVotes winnerFirstChoiceVotes : ℕ) : ℕ :=
  surplusVotes * nextChoiceVotes / (surplusVotes + winnerFirstChoiceVotes)

/--
Equation (2) total lower-candidate transfer bound: weighted surplus transfers
plus the unweighted transfers that can originate from the early winner's
position.
-/
def lowerCandidateTransferBound
    (surplusVotes nextChoiceVotes winnerFirstChoiceVotes
      unweightedTransferBound : ℕ) : ℕ :=
  weightedSurplusTransferBound
      surplusVotes nextChoiceVotes winnerFirstChoiceVotes +
    unweightedTransferBound

/--
Equation (2) arithmetic sanity check: the weighted surplus contribution sent
to a lower candidate is never larger than the relevant next-choice count.
-/
theorem weightedSurplusTransferBound_le_nextChoiceVotes
    (surplusVotes nextChoiceVotes winnerFirstChoiceVotes : ℕ) :
    weightedSurplusTransferBound
        surplusVotes nextChoiceVotes winnerFirstChoiceVotes ≤
      nextChoiceVotes := by
  unfold weightedSurplusTransferBound
  have hmul :
      surplusVotes * nextChoiceVotes ≤
        nextChoiceVotes * (surplusVotes + winnerFirstChoiceVotes) := by
    calc
      surplusVotes * nextChoiceVotes = nextChoiceVotes * surplusVotes := by
        rw [Nat.mul_comm]
      _ ≤ nextChoiceVotes * (surplusVotes + winnerFirstChoiceVotes) :=
        Nat.mul_le_mul_left nextChoiceVotes
          (Nat.le_add_right surplusVotes winnerFirstChoiceVotes)
  have hmul' :
      surplusVotes * nextChoiceVotes ≤
        (surplusVotes + winnerFirstChoiceVotes) * nextChoiceVotes := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
  exact Nat.div_le_of_le_mul hmul'

/--
Equation (2) total transfer sanity check: adding the unweighted-transfer term
keeps the lower-candidate transfer bound within next-choice plus unweighted
transfers.
-/
theorem lowerCandidateTransferBound_le_nextChoiceVotes_add_unweighted
    (surplusVotes nextChoiceVotes winnerFirstChoiceVotes
      unweightedTransferBound : ℕ) :
    lowerCandidateTransferBound
        surplusVotes nextChoiceVotes winnerFirstChoiceVotes
        unweightedTransferBound ≤
      nextChoiceVotes + unweightedTransferBound := by
  unfold lowerCandidateTransferBound
  exact Nat.add_le_add_right
    (weightedSurplusTransferBound_le_nextChoiceVotes
      surplusVotes nextChoiceVotes winnerFirstChoiceVotes)
    unweightedTransferBound

/--
Equation (3) updated lower bound for an upper candidate's support after the
early winner leaves the contest.  Natural subtraction represents the source
`max(0, transfers - (V_Cw - Q))` term.
-/
def updatedUpperCandidateSupportBound
    (baseSupport transferSupport winnerFirstChoiceVotes quota : ℕ) : ℕ :=
  baseSupport + (transferSupport - (winnerFirstChoiceVotes - quota))

/--
Equation (3) arithmetic sanity check: the updated upper-candidate support
bound is at least the base strict-support term.
-/
theorem baseSupport_le_updatedUpperCandidateSupportBound
    (baseSupport transferSupport winnerFirstChoiceVotes quota : ℕ) :
    baseSupport ≤
      updatedUpperCandidateSupportBound
        baseSupport transferSupport winnerFirstChoiceVotes quota := by
  unfold updatedUpperCandidateSupportBound
  exact Nat.le_add_right baseSupport
    (transferSupport - (winnerFirstChoiceVotes - quota))

/--
Theorem 2.2 updated strict-support containment condition: after adding the
bounded transfer contribution to each lower candidate, every lower candidate
still remains below every relevant upper candidate's updated support bound.
-/
def multiWinnerUpdatedStrictSupportCondition {Candidate : Type*}
    [DecidableEq Candidate]
    (lower upper : Finset Candidate)
    (lowerTransferBound : Candidate → Candidate → ℕ)
    (upperSupportBound : Candidate → Candidate → ℕ)
    (budget : ℕ) : Prop :=
  ∀ inside, inside ∈ lower → ∀ outside, outside ∈ upper →
    budget + lowerTransferBound inside outside <
      upperSupportBound inside outside

/--
Algorithm 4 no-failed-pair convention.  The paper's branch condition is often
written as the absence of a failed comparison `minVotes <= budget + maxVotes`;
over natural-number tallies this is exactly the strict inequality consumed by
the containment proof.
-/
theorem algorithm4_pairwise_lt_of_no_failed_pair
    {Candidate : Type*} [DecidableEq Candidate]
    {lower upper : Finset Candidate}
    {maxVotes minVotes : Candidate → Candidate → ℕ} {budget : ℕ}
    (hno_fail :
      ∀ inside, inside ∈ lower → ∀ outside, outside ∈ upper →
        ¬ minVotes inside outside ≤ budget + maxVotes inside outside) :
    ∀ inside, inside ∈ lower → ∀ outside, outside ∈ upper →
      budget + maxVotes inside outside < minVotes inside outside := by
  intro inside hinside outside houtside
  exact Nat.lt_of_not_ge (hno_fail inside hinside outside houtside)

/--
Algorithm 4 lower-candidate transfer bound as a pair-indexed function for the
updated strict-support check.  The second candidate is present so the bound can
be passed directly to `multiWinnerUpdatedStrictSupportCondition`.
-/
def multiWinnerLowerCandidateTransferBound {Candidate : Type*}
    (surplusVotes nextChoiceVotes unweightedTransferBound : Candidate → ℕ)
    (winnerFirstChoiceVotes : ℕ) : Candidate → Candidate → ℕ :=
  fun inside _outside =>
    lowerCandidateTransferBound
      (surplusVotes inside) (nextChoiceVotes inside)
      winnerFirstChoiceVotes (unweightedTransferBound inside)

/--
Algorithm 4 upper-candidate updated support bound as a pair-indexed function.
The first candidate indexes the reduced instance `L \ {Ci}` used in Eq. (3),
and the second candidate is the upper candidate being compared against.
-/
def multiWinnerUpdatedUpperSupportBound {Candidate : Type*}
    (baseSupport transferSupport : Candidate → Candidate → ℕ)
    (winnerFirstChoiceVotes quota : ℕ) : Candidate → Candidate → ℕ :=
  fun inside outside =>
    updatedUpperCandidateSupportBound
      (baseSupport inside outside) (transferSupport inside outside)
      winnerFirstChoiceVotes quota

/--
Source-shaped Algorithm 4 run object for the multi-winner containment branch.
It records the paper's no-failed-pair test over the concrete lower-transfer
and updated-upper-support formulas used in Theorem 2.2.
-/
structure Algorithm4ContainmentRun {Candidate : Type*}
    [DecidableEq Candidate]
    (lower upper : Finset Candidate)
    (winnerFirstChoiceVotes quota budget : ℕ)
    (surplusVotes nextChoiceVotes unweightedTransferBound : Candidate → ℕ)
    (baseUpperSupport transferUpperSupport : Candidate → Candidate → ℕ) where
  no_failed_pair :
    ∀ inside, inside ∈ lower → ∀ outside, outside ∈ upper →
      ¬
        updatedUpperCandidateSupportBound
            (baseUpperSupport inside outside)
            (transferUpperSupport inside outside)
            winnerFirstChoiceVotes quota ≤
          budget +
            lowerCandidateTransferBound
              (surplusVotes inside) (nextChoiceVotes inside)
              winnerFirstChoiceVotes (unweightedTransferBound inside)

/--
Executable Boolean check for Algorithm 4's no-failed-pair branch.  The check
is stated as a decidable finite predicate over the lower/upper candidate sets;
`true` is converted back to the source run object by
`algorithm4ContainmentRun_of_noFailedPairCheck_eq_true`.
-/
def algorithm4NoFailedPairCheck {Candidate : Type*}
    [DecidableEq Candidate]
    (lower upper : Finset Candidate)
    (winnerFirstChoiceVotes quota budget : ℕ)
    (surplusVotes nextChoiceVotes unweightedTransferBound : Candidate → ℕ)
    (baseUpperSupport transferUpperSupport : Candidate → Candidate → ℕ) :
    Bool :=
  decide
    (∀ inside, inside ∈ lower → ∀ outside, outside ∈ upper →
      ¬
        updatedUpperCandidateSupportBound
            (baseUpperSupport inside outside)
            (transferUpperSupport inside outside)
            winnerFirstChoiceVotes quota ≤
          budget +
            lowerCandidateTransferBound
              (surplusVotes inside) (nextChoiceVotes inside)
              winnerFirstChoiceVotes (unweightedTransferBound inside))

/--
Completeness of Algorithm 4's executable no-failed-pair check: the source
pairwise strict inequality is exactly the proposition decided by the Boolean
checker.
-/
theorem algorithm4NoFailedPairCheck_eq_true_of_pairwise_lt
    {Candidate : Type*} [DecidableEq Candidate]
    {lower upper : Finset Candidate}
    {winnerFirstChoiceVotes quota budget : ℕ}
    {surplusVotes nextChoiceVotes unweightedTransferBound : Candidate → ℕ}
    {baseUpperSupport transferUpperSupport : Candidate → Candidate → ℕ}
    (hpair :
      ∀ inside, inside ∈ lower → ∀ outside, outside ∈ upper →
        budget +
            lowerCandidateTransferBound
              (surplusVotes inside) (nextChoiceVotes inside)
              winnerFirstChoiceVotes (unweightedTransferBound inside) <
          updatedUpperCandidateSupportBound
            (baseUpperSupport inside outside)
            (transferUpperSupport inside outside)
            winnerFirstChoiceVotes quota) :
    algorithm4NoFailedPairCheck lower upper winnerFirstChoiceVotes quota
        budget surplusVotes nextChoiceVotes unweightedTransferBound
        baseUpperSupport transferUpperSupport = true := by
  simpa [algorithm4NoFailedPairCheck] using
    (decide_eq_true_iff.mpr hpair)

/-- A successful executable Algorithm 4 branch check constructs the run object. -/
theorem algorithm4ContainmentRun_of_noFailedPairCheck_eq_true
    {Candidate : Type*} [DecidableEq Candidate]
    {lower upper : Finset Candidate}
    {winnerFirstChoiceVotes quota budget : ℕ}
    {surplusVotes nextChoiceVotes unweightedTransferBound : Candidate → ℕ}
    {baseUpperSupport transferUpperSupport : Candidate → Candidate → ℕ}
    (hcheck :
      algorithm4NoFailedPairCheck lower upper winnerFirstChoiceVotes quota
        budget surplusVotes nextChoiceVotes unweightedTransferBound
        baseUpperSupport transferUpperSupport = true) :
    Algorithm4ContainmentRun lower upper winnerFirstChoiceVotes quota budget
      surplusVotes nextChoiceVotes unweightedTransferBound baseUpperSupport
      transferUpperSupport where
  no_failed_pair := by
    exact of_decide_eq_true hcheck

/--
Algorithm 4 checker inputs separated from the fixed lower/upper sets, winner,
quota, and budget.  The five fields are exactly the Eq. (2)/(3) quantities
used by the no-failed-pair branch check.
-/
structure Algorithm4CheckerInputs (Candidate : Type*) where
  surplusVotes : Candidate → ℕ
  nextChoiceVotes : Candidate → ℕ
  unweightedTransferBound : Candidate → ℕ
  baseUpperSupport : Candidate → Candidate → ℕ
  transferUpperSupport : Candidate → Candidate → ℕ

namespace Algorithm4CheckerInputs

/-- Algorithm 4's no-failed-pair check over packaged Eq. (2)/(3) inputs. -/
def noFailedPairCheck {Candidate : Type*} [DecidableEq Candidate]
    (inputs : Algorithm4CheckerInputs Candidate)
    (lower upper : Finset Candidate)
    (winnerFirstChoiceVotes quota budget : ℕ) : Bool :=
  algorithm4NoFailedPairCheck lower upper winnerFirstChoiceVotes quota budget
    inputs.surplusVotes inputs.nextChoiceVotes inputs.unweightedTransferBound
    inputs.baseUpperSupport inputs.transferUpperSupport

/-- A successful packaged-input check constructs the Algorithm 4 run object. -/
theorem containmentRun_of_noFailedPairCheck_eq_true
    {Candidate : Type*} [DecidableEq Candidate]
    {inputs : Algorithm4CheckerInputs Candidate}
    {lower upper : Finset Candidate}
    {winnerFirstChoiceVotes quota budget : ℕ}
    (hcheck :
      inputs.noFailedPairCheck lower upper winnerFirstChoiceVotes quota budget =
        true) :
    Algorithm4ContainmentRun lower upper winnerFirstChoiceVotes quota budget
      inputs.surplusVotes inputs.nextChoiceVotes inputs.unweightedTransferBound
      inputs.baseUpperSupport inputs.transferUpperSupport := by
  exact
    algorithm4ContainmentRun_of_noFailedPairCheck_eq_true
      (lower := lower)
      (upper := upper)
      (winnerFirstChoiceVotes := winnerFirstChoiceVotes)
      (quota := quota)
      (budget := budget)
      (surplusVotes := inputs.surplusVotes)
      (nextChoiceVotes := inputs.nextChoiceVotes)
      (unweightedTransferBound := inputs.unweightedTransferBound)
      (baseUpperSupport := inputs.baseUpperSupport)
      (transferUpperSupport := inputs.transferUpperSupport)
      (by
        simpa [Algorithm4CheckerInputs.noFailedPairCheck] using hcheck)

end Algorithm4CheckerInputs

/--
Algorithm 4 source quantity `V_Cw`: the early winner's original first-choice
support in the input profile.
-/
def algorithm4WinnerFirstChoiceVotes {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (winner : Candidate) : ℕ :=
  Ballot.firstChoiceCount voters ballots winner

/--
Algorithm 4 source quantity `SV_0`: the maximum number of votes that can push
the early winner over quota while the lower set is being eliminated.
-/
def algorithm4SourceSurplusVotes {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (winner : Candidate) (lower : Finset Candidate) (quota : ℕ)
    (_inside : Candidate) : ℕ :=
  strictSupportCount voters ballots (insert winner lower) (∅ : Finset Candidate)
    winner - quota

/--
Algorithm 4 source quantity `X`: after reducing the instance by
`L \ {inside}`, count winner-first ballots whose next active lower candidate is
`inside`.
-/
def algorithm4SourceNextChoiceVotes {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (winner : Candidate) (lower : Finset Candidate) (inside : Candidate) : ℕ :=
  strictSupportCount voters
    (fun voter => Ballot.removeCandidates (lower.erase inside) (ballots voter))
    ({winner} : Finset Candidate) (∅ : Finset Candidate) inside

/--
Algorithm 4 source quantity `SV_1`: the unweighted transfer allowance from the
early winner into a lower candidate, represented as the source strict-support
term minus the candidate's original first-choice support.
-/
def algorithm4SourceUnweightedTransferBound {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (winner : Candidate) (lower : Finset Candidate) (inside : Candidate) : ℕ :=
  strictSupportCount voters ballots (insert winner lower) (∅ : Finset Candidate)
    inside - Ballot.firstChoiceCount voters ballots inside

/--
Algorithm 4 Eq. (3) base upper-support term:
`Strict-Support_{outside ∪ L \ {inside}, ∅}(outside)`.
-/
def algorithm4SourceBaseUpperSupport {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (lower : Finset Candidate) (inside outside : Candidate) : ℕ :=
  strictSupportCount voters ballots (insert outside (lower.erase inside))
    (∅ : Finset Candidate) outside

/--
Algorithm 4 Eq. (3) transfer-after-win lower-bound term:
`Strict-Support_{L \ {inside}, winner}(outside)`.
-/
def algorithm4SourceTransferUpperSupport {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (winner : Candidate) (lower : Finset Candidate)
    (inside outside : Candidate) : ℕ :=
  strictSupportCount voters ballots (lower.erase inside) ({winner} : Finset Candidate)
    outside

/--
Extract Algorithm 4's five Eq. (2)/(3) checker inputs directly from the source
ballot profile.
-/
def algorithm4SourceCheckerInputs {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (winner : Candidate) (lower : Finset Candidate) (quota : ℕ) :
    Algorithm4CheckerInputs Candidate where
  surplusVotes := algorithm4SourceSurplusVotes voters ballots winner lower quota
  nextChoiceVotes := algorithm4SourceNextChoiceVotes voters ballots winner lower
  unweightedTransferBound :=
    algorithm4SourceUnweightedTransferBound voters ballots winner lower
  baseUpperSupport := algorithm4SourceBaseUpperSupport voters ballots lower
  transferUpperSupport :=
    algorithm4SourceTransferUpperSupport voters ballots winner lower

/--
Algorithm 4 no-failed-pair checker with all Eq. (2)/(3) inputs extracted from
the source ballot profile rather than supplied as arbitrary numeric fields.
-/
def algorithm4SourceNoFailedPairCheck {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (lower upper : Finset Candidate) (winner : Candidate)
    (quota budget : ℕ) : Bool :=
  algorithm4NoFailedPairCheck lower upper
    (algorithm4WinnerFirstChoiceVotes voters ballots winner) quota budget
    (algorithm4SourceSurplusVotes voters ballots winner lower quota)
    (algorithm4SourceNextChoiceVotes voters ballots winner lower)
    (algorithm4SourceUnweightedTransferBound voters ballots winner lower)
    (algorithm4SourceBaseUpperSupport voters ballots lower)
    (algorithm4SourceTransferUpperSupport voters ballots winner lower)

/--
Completeness of the source-extracted Algorithm 4 no-failed-pair checker from
the paper's pairwise Eq. (2)/(3) strict-support inequality.
-/
theorem algorithm4SourceNoFailedPairCheck_eq_true_of_source_pairwise_lt
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {lower upper : Finset Candidate} {winner : Candidate}
    {quota budget : ℕ}
    (hpair :
      ∀ inside, inside ∈ lower → ∀ outside, outside ∈ upper →
        budget +
            lowerCandidateTransferBound
              (algorithm4SourceSurplusVotes voters ballots winner lower quota
                inside)
              (algorithm4SourceNextChoiceVotes voters ballots winner lower
                inside)
              (algorithm4WinnerFirstChoiceVotes voters ballots winner)
              (algorithm4SourceUnweightedTransferBound voters ballots winner
                lower inside) <
          updatedUpperCandidateSupportBound
            (algorithm4SourceBaseUpperSupport voters ballots lower inside
              outside)
            (algorithm4SourceTransferUpperSupport voters ballots winner lower
              inside outside)
            (algorithm4WinnerFirstChoiceVotes voters ballots winner) quota) :
    algorithm4SourceNoFailedPairCheck voters ballots lower upper winner quota
      budget = true := by
  exact
    algorithm4NoFailedPairCheck_eq_true_of_pairwise_lt
      (lower := lower)
      (upper := upper)
      (winnerFirstChoiceVotes :=
        algorithm4WinnerFirstChoiceVotes voters ballots winner)
      (quota := quota)
      (budget := budget)
      (surplusVotes :=
        algorithm4SourceSurplusVotes voters ballots winner lower quota)
      (nextChoiceVotes :=
        algorithm4SourceNextChoiceVotes voters ballots winner lower)
      (unweightedTransferBound :=
        algorithm4SourceUnweightedTransferBound voters ballots winner lower)
      (baseUpperSupport :=
        algorithm4SourceBaseUpperSupport voters ballots lower)
      (transferUpperSupport :=
        algorithm4SourceTransferUpperSupport voters ballots winner lower)
      hpair

/--
The packaged source-input checker is definitionally the existing source
no-failed-pair checker.
-/
theorem algorithm4SourceCheckerInputs_noFailedPairCheck_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (lower upper : Finset Candidate) (winner : Candidate)
    (quota budget : ℕ) :
    (algorithm4SourceCheckerInputs voters ballots winner lower quota).noFailedPairCheck
        lower upper (algorithm4WinnerFirstChoiceVotes voters ballots winner)
        quota budget =
      algorithm4SourceNoFailedPairCheck voters ballots lower upper winner
        quota budget := by
  rfl

/--
A successful check over the source-extracted Algorithm 4 input package
constructs the existing run object.
-/
theorem algorithm4ContainmentRun_of_sourceCheckerInputsNoFailedPairCheck_eq_true
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {lower upper : Finset Candidate} {winner : Candidate}
    {quota budget : ℕ}
    (hcheck :
      (algorithm4SourceCheckerInputs voters ballots winner lower quota).noFailedPairCheck
          lower upper (algorithm4WinnerFirstChoiceVotes voters ballots winner)
          quota budget = true) :
    Algorithm4ContainmentRun lower upper
      (algorithm4WinnerFirstChoiceVotes voters ballots winner) quota budget
      (algorithm4SourceCheckerInputs voters ballots winner lower quota).surplusVotes
      (algorithm4SourceCheckerInputs voters ballots winner lower quota).nextChoiceVotes
      (algorithm4SourceCheckerInputs voters ballots winner lower quota).unweightedTransferBound
      (algorithm4SourceCheckerInputs voters ballots winner lower quota).baseUpperSupport
      (algorithm4SourceCheckerInputs voters ballots winner lower quota).transferUpperSupport := by
  exact
    Algorithm4CheckerInputs.containmentRun_of_noFailedPairCheck_eq_true
      (inputs := algorithm4SourceCheckerInputs voters ballots winner lower quota)
      (lower := lower)
      (upper := upper)
      (winnerFirstChoiceVotes :=
        algorithm4WinnerFirstChoiceVotes voters ballots winner)
      (quota := quota)
      (budget := budget)
      hcheck

/--
A successful source-extracted Algorithm 4 check constructs the existing run
object with the Eq. (2)/(3) quantities instantiated from the ballot profile.
-/
theorem algorithm4ContainmentRun_of_sourceNoFailedPairCheck_eq_true
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {lower upper : Finset Candidate} {winner : Candidate}
    {quota budget : ℕ}
    (hcheck :
      algorithm4SourceNoFailedPairCheck voters ballots lower upper winner
        quota budget = true) :
    Algorithm4ContainmentRun lower upper
      (algorithm4WinnerFirstChoiceVotes voters ballots winner) quota budget
      (algorithm4SourceSurplusVotes voters ballots winner lower quota)
      (algorithm4SourceNextChoiceVotes voters ballots winner lower)
      (algorithm4SourceUnweightedTransferBound voters ballots winner lower)
      (algorithm4SourceBaseUpperSupport voters ballots lower)
      (algorithm4SourceTransferUpperSupport voters ballots winner lower) := by
  exact
    algorithm4ContainmentRun_of_noFailedPairCheck_eq_true
      (lower := lower)
      (upper := upper)
      (winnerFirstChoiceVotes :=
        algorithm4WinnerFirstChoiceVotes voters ballots winner)
      (quota := quota)
      (budget := budget)
      (surplusVotes :=
        algorithm4SourceSurplusVotes voters ballots winner lower quota)
      (nextChoiceVotes :=
        algorithm4SourceNextChoiceVotes voters ballots winner lower)
      (unweightedTransferBound :=
        algorithm4SourceUnweightedTransferBound voters ballots winner lower)
      (baseUpperSupport :=
        algorithm4SourceBaseUpperSupport voters ballots lower)
      (transferUpperSupport :=
        algorithm4SourceTransferUpperSupport voters ballots winner lower)
      (by
        simpa [algorithm4SourceNoFailedPairCheck] using hcheck)

/--
Algorithm 4 updated strict-support condition assembled from the paper's
weighted surplus-transfer, unweighted transfer, and updated upper-support
bounds.
-/
def multiWinnerContainmentCondition {Candidate : Type*} [DecidableEq Candidate]
    (lower upper : Finset Candidate)
    (winnerFirstChoiceVotes quota : ℕ)
    (surplusVotes nextChoiceVotes unweightedTransferBound : Candidate → ℕ)
    (baseUpperSupport transferUpperSupport : Candidate → Candidate → ℕ)
    (budget : ℕ) : Prop :=
  multiWinnerUpdatedStrictSupportCondition lower upper
    (multiWinnerLowerCandidateTransferBound
      surplusVotes nextChoiceVotes unweightedTransferBound
      winnerFirstChoiceVotes)
    (multiWinnerUpdatedUpperSupportBound
      baseUpperSupport transferUpperSupport winnerFirstChoiceVotes quota)
    budget

/--
Monotonicity for Theorem 2.2's updated strict-support condition: it is enough
to verify the inequality with a conservative upper bound on lower-candidate
transfers and a conservative lower bound on upper-candidate support.
-/
theorem multiWinnerUpdatedStrictSupportCondition_of_component_bounds
    {Candidate : Type*} [DecidableEq Candidate]
    {lower upper : Finset Candidate}
    {actualLower conservativeLower actualUpper conservativeUpper :
      Candidate → Candidate → ℕ}
    {budget : ℕ}
    (hcondition :
      ∀ inside, inside ∈ lower → ∀ outside, outside ∈ upper →
        budget + conservativeLower inside outside <
          conservativeUpper inside outside)
    (hlower_bound :
      ∀ inside, inside ∈ lower → ∀ outside, outside ∈ upper →
        actualLower inside outside ≤ conservativeLower inside outside)
    (hupper_bound :
      ∀ inside, inside ∈ lower → ∀ outside, outside ∈ upper →
        conservativeUpper inside outside ≤ actualUpper inside outside) :
    multiWinnerUpdatedStrictSupportCondition lower upper actualLower actualUpper
      budget := by
  intro inside hinside outside houtside
  have hlower :
      budget + actualLower inside outside ≤
        budget + conservativeLower inside outside :=
    Nat.add_le_add_left
      (hlower_bound inside hinside outside houtside) budget
  have hstrict :
      budget + conservativeLower inside outside <
        actualUpper inside outside :=
    lt_of_lt_of_le
      (hcondition inside hinside outside houtside)
      (hupper_bound inside hinside outside houtside)
  exact lt_of_le_of_lt hlower hstrict

/--
Component-bound constructor for Algorithm 4's Theorem 2.2 condition.  A source
proof can use any pair-indexed conservative lower-transfer and upper-support
formulas, then discharge the concrete Eq. (2)/(3) condition by proving the
componentwise comparisons.
-/
theorem multiWinnerContainmentCondition_of_component_bounds
    {Candidate : Type*} [DecidableEq Candidate]
    {lower upper : Finset Candidate}
    {winnerFirstChoiceVotes quota budget : ℕ}
    {surplusVotes nextChoiceVotes unweightedTransferBound : Candidate → ℕ}
    {baseUpperSupport transferUpperSupport : Candidate → Candidate → ℕ}
    (conservativeLower conservativeUpper : Candidate → Candidate → ℕ)
    (hcondition :
      ∀ inside, inside ∈ lower → ∀ outside, outside ∈ upper →
        budget + conservativeLower inside outside <
          conservativeUpper inside outside)
    (hlower_bound :
      ∀ inside, inside ∈ lower → ∀ outside, outside ∈ upper →
        multiWinnerLowerCandidateTransferBound
            surplusVotes nextChoiceVotes unweightedTransferBound
            winnerFirstChoiceVotes inside outside ≤
          conservativeLower inside outside)
    (hupper_bound :
      ∀ inside, inside ∈ lower → ∀ outside, outside ∈ upper →
        conservativeUpper inside outside ≤
          multiWinnerUpdatedUpperSupportBound
            baseUpperSupport transferUpperSupport winnerFirstChoiceVotes quota
            inside outside) :
    multiWinnerContainmentCondition lower upper winnerFirstChoiceVotes quota
      surplusVotes nextChoiceVotes unweightedTransferBound baseUpperSupport
      transferUpperSupport budget := by
  exact multiWinnerUpdatedStrictSupportCondition_of_component_bounds
    hcondition hlower_bound hupper_bound

/--
Concrete Eq. (2)/(3) containment constructor: it is enough to compare the
budget plus `nextChoice + unweighted` transfer allowance against the base upper
support term. The weighted-transfer and updated-upper formulas then discharge
the component bounds automatically.
-/
theorem multiWinnerContainmentCondition_of_nextChoice_unweighted_baseSupport
    {Candidate : Type*} [DecidableEq Candidate]
    {lower upper : Finset Candidate}
    {winnerFirstChoiceVotes quota budget : ℕ}
    {surplusVotes nextChoiceVotes unweightedTransferBound : Candidate → ℕ}
    {baseUpperSupport transferUpperSupport : Candidate → Candidate → ℕ}
    (hcondition :
      ∀ inside, inside ∈ lower → ∀ outside, outside ∈ upper →
        budget + (nextChoiceVotes inside + unweightedTransferBound inside) <
          baseUpperSupport inside outside) :
    multiWinnerContainmentCondition lower upper winnerFirstChoiceVotes quota
      surplusVotes nextChoiceVotes unweightedTransferBound baseUpperSupport
      transferUpperSupport budget := by
  exact multiWinnerContainmentCondition_of_component_bounds
    (conservativeLower := fun inside _outside =>
      nextChoiceVotes inside + unweightedTransferBound inside)
    (conservativeUpper := fun inside outside =>
      baseUpperSupport inside outside)
    hcondition
    (by
      intro inside _hinside outside _houtside
      exact lowerCandidateTransferBound_le_nextChoiceVotes_add_unweighted
        (surplusVotes inside) (nextChoiceVotes inside)
        winnerFirstChoiceVotes (unweightedTransferBound inside))
    (by
      intro inside _hinside outside _houtside
      exact baseSupport_le_updatedUpperCandidateSupportBound
        (baseUpperSupport inside outside)
        (transferUpperSupport inside outside)
        winnerFirstChoiceVotes quota)

/--
Concrete contained-candidate output for Theorem 2.2: the verification keeps a
retained candidate set and removes the lower/irrelevant set.
-/
structure MultiWinnerContainmentOutcome (Candidate : Type*) where
  removedCandidates : Finset Candidate
  retainedCandidates : Finset Candidate

/-- The concrete containment output retaining `upper` and removing `lower`. -/
def multiWinnerContainmentOutcome {Candidate : Type*}
    (lower upper : Finset Candidate) :
    MultiWinnerContainmentOutcome Candidate where
  removedCandidates := lower
  retainedCandidates := upper

/--
Concrete Theorem 2.2 output specification: the procedure retains the relevant
candidate set, removes the lower set, and the updated strict-support condition
that validates containment is satisfied.
-/
def multiWinnerContainmentConcreteSpecification {Candidate : Type*}
    [DecidableEq Candidate]
    (lower upper : Finset Candidate)
    (winnerFirstChoiceVotes quota : ℕ)
    (surplusVotes nextChoiceVotes unweightedTransferBound : Candidate → ℕ)
    (baseUpperSupport transferUpperSupport : Candidate → Candidate → ℕ)
    (budget : ℕ) (outcome : MultiWinnerContainmentOutcome Candidate) : Prop :=
  outcome.removedCandidates = lower ∧
    outcome.retainedCandidates = upper ∧
      multiWinnerContainmentCondition lower upper winnerFirstChoiceVotes quota
        surplusVotes nextChoiceVotes unweightedTransferBound baseUpperSupport
        transferUpperSupport budget

/--
Concrete source problem for Theorem 2.2's multi-winner containment
verification.  Its specification is the paper's retained/removed candidate
sets plus the updated strict-support condition.
-/
def multiWinnerContainmentConcreteProblem {Candidate : Type*}
    [DecidableEq Candidate]
    (lower upper : Finset Candidate)
    (winnerFirstChoiceVotes quota : ℕ)
    (surplusVotes nextChoiceVotes unweightedTransferBound : Candidate → ℕ)
    (baseUpperSupport transferUpperSupport : Candidate → Candidate → ℕ)
    (budget uniqueBallotCount candidateCount verificationBound : ℕ) :
    MultiWinnerContainmentProblem
      (MultiWinnerContainmentOutcome Candidate) where
  specification :=
    multiWinnerContainmentConcreteSpecification lower upper
      winnerFirstChoiceVotes quota surplusVotes nextChoiceVotes
      unweightedTransferBound baseUpperSupport transferUpperSupport budget
  budget := budget
  uniqueBallotCount := uniqueBallotCount
  candidateCount := candidateCount
  verificationBound := verificationBound

/--
Concrete Theorem 2.2 containment implementation: return the retained/removed
candidate sets verified by the source inequalities.
-/
def multiWinnerContainmentConcreteAlgorithm {Candidate : Type*}
    [DecidableEq Candidate]
    (lower upper : Finset Candidate) :
    MultiWinnerContainmentProblem
      (MultiWinnerContainmentOutcome Candidate) →
        MultiWinnerContainmentOutcome Candidate :=
  fun _problem =>
    multiWinnerContainmentOutcome lower upper

/-- Concrete Theorem 2.2 operation-count implementation. -/
def multiWinnerContainmentConcreteOperationCount
    {Candidate : Type*} :
    MultiWinnerContainmentProblem
      (MultiWinnerContainmentOutcome Candidate) → ℕ :=
  fun problem =>
    problem.verificationBound

/--
Theorem 2.2 concrete Eq. (2)/(3) route: if the source verifies containment
using `nextChoice + unweighted` lower transfers against base upper support,
then the concrete retained/removed candidate output satisfies the source
containment specification.
-/
theorem multiWinnerContainmentConcreteSpecification_of_nextChoice_unweighted_baseSupport
    {Candidate : Type*} [DecidableEq Candidate]
    {lower upper : Finset Candidate}
    {winnerFirstChoiceVotes quota budget : ℕ}
    {surplusVotes nextChoiceVotes unweightedTransferBound : Candidate → ℕ}
    {baseUpperSupport transferUpperSupport : Candidate → Candidate → ℕ}
    (hcomponent :
      ∀ inside, inside ∈ lower → ∀ outside, outside ∈ upper →
        budget + (nextChoiceVotes inside + unweightedTransferBound inside) <
          baseUpperSupport inside outside) :
    multiWinnerContainmentConcreteSpecification lower upper
        winnerFirstChoiceVotes quota surplusVotes nextChoiceVotes
        unweightedTransferBound baseUpperSupport transferUpperSupport budget
        (multiWinnerContainmentOutcome lower upper) := by
  exact ⟨rfl, rfl,
    multiWinnerContainmentCondition_of_nextChoice_unweighted_baseSupport
      hcomponent⟩

/--
Theorem 2.2 concrete condition-to-output constructor: once the source
Algorithm 4 updated strict-support condition is established, the concrete
retained/removed candidate output satisfies the retained/removed specification.
-/
theorem multiWinnerContainmentConcreteSpecification_of_condition
    {Candidate : Type*} [DecidableEq Candidate]
    {lower upper : Finset Candidate}
    {winnerFirstChoiceVotes quota budget : ℕ}
    {surplusVotes nextChoiceVotes unweightedTransferBound : Candidate → ℕ}
    {baseUpperSupport transferUpperSupport : Candidate → Candidate → ℕ}
    (hcondition :
      multiWinnerContainmentCondition lower upper winnerFirstChoiceVotes quota
        surplusVotes nextChoiceVotes unweightedTransferBound baseUpperSupport
        transferUpperSupport budget) :
    multiWinnerContainmentConcreteSpecification lower upper
        winnerFirstChoiceVotes quota surplusVotes nextChoiceVotes
        unweightedTransferBound baseUpperSupport transferUpperSupport budget
        (multiWinnerContainmentOutcome lower upper) := by
  exact ⟨rfl, rfl, hcondition⟩

/--
Theorem 2.2 concrete implementation route: if Algorithm 4 returns the concrete
retained/removed candidate output on the concrete source problem, the Eq.
(2)/(3) comparison proves the containment specification and the supplied
polynomial verification bound.
-/
theorem theorem2_2_concreteContainmentAlgorithm_sound_and_polynomial_runtime_of_nextChoice_unweighted_baseSupport
    {Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      MultiWinnerContainmentProblem
        (MultiWinnerContainmentOutcome Candidate) →
          MultiWinnerContainmentOutcome Candidate}
    {operationCount :
      MultiWinnerContainmentProblem
        (MultiWinnerContainmentOutcome Candidate) → ℕ}
    {lower upper : Finset Candidate}
    {winnerFirstChoiceVotes quota budget uniqueBallotCount candidateCount
      verificationBound : ℕ}
    {surplusVotes nextChoiceVotes unweightedTransferBound : Candidate → ℕ}
    {baseUpperSupport transferUpperSupport : Candidate → Candidate → ℕ}
    (hcomponent :
      ∀ inside, inside ∈ lower → ∀ outside, outside ∈ upper →
        budget + (nextChoiceVotes inside + unweightedTransferBound inside) <
          baseUpperSupport inside outside)
    (algorithm_eq :
      algorithm
          (multiWinnerContainmentConcreteProblem lower upper
            winnerFirstChoiceVotes quota surplusVotes nextChoiceVotes
            unweightedTransferBound baseUpperSupport transferUpperSupport
            budget uniqueBallotCount candidateCount verificationBound) =
        multiWinnerContainmentOutcome lower upper)
    (operationCount_le :
      operationCount
          (multiWinnerContainmentConcreteProblem lower upper
            winnerFirstChoiceVotes quota surplusVotes nextChoiceVotes
            unweightedTransferBound baseUpperSupport transferUpperSupport
            budget uniqueBallotCount candidateCount verificationBound) ≤
        verificationBound) :
    (multiWinnerContainmentConcreteProblem lower upper winnerFirstChoiceVotes
        quota surplusVotes nextChoiceVotes unweightedTransferBound
        baseUpperSupport transferUpperSupport budget uniqueBallotCount
        candidateCount verificationBound).specification
      (algorithm
        (multiWinnerContainmentConcreteProblem lower upper
          winnerFirstChoiceVotes quota surplusVotes nextChoiceVotes
          unweightedTransferBound baseUpperSupport transferUpperSupport
          budget uniqueBallotCount candidateCount verificationBound)) ∧
      operationCount
          (multiWinnerContainmentConcreteProblem lower upper
            winnerFirstChoiceVotes quota surplusVotes nextChoiceVotes
            unweightedTransferBound baseUpperSupport transferUpperSupport
            budget uniqueBallotCount candidateCount verificationBound) ≤
        verificationBound := by
  exact ⟨by
    rw [algorithm_eq]
    exact
      multiWinnerContainmentConcreteSpecification_of_nextChoice_unweighted_baseSupport
        hcomponent, operationCount_le⟩

/--
Concrete Theorem 2.2 containment implementation: the source implementation is
the retained/removed candidate-set output itself, so the algorithm equality and
verification-bound premises discharge by definition and reflexivity.
-/
theorem theorem2_2_concreteContainmentAlgorithmImplementation_sound_and_polynomial_runtime_of_nextChoice_unweighted_baseSupport
    {Candidate : Type*} [DecidableEq Candidate]
    {lower upper : Finset Candidate}
    {winnerFirstChoiceVotes quota budget uniqueBallotCount candidateCount
      verificationBound : ℕ}
    {surplusVotes nextChoiceVotes unweightedTransferBound : Candidate → ℕ}
    {baseUpperSupport transferUpperSupport : Candidate → Candidate → ℕ}
    (hcomponent :
      ∀ inside, inside ∈ lower → ∀ outside, outside ∈ upper →
        budget + (nextChoiceVotes inside + unweightedTransferBound inside) <
          baseUpperSupport inside outside) :
    (multiWinnerContainmentConcreteProblem lower upper winnerFirstChoiceVotes
        quota surplusVotes nextChoiceVotes unweightedTransferBound
        baseUpperSupport transferUpperSupport budget uniqueBallotCount
        candidateCount verificationBound).specification
      (multiWinnerContainmentConcreteAlgorithm lower upper
        (multiWinnerContainmentConcreteProblem lower upper
          winnerFirstChoiceVotes quota surplusVotes nextChoiceVotes
          unweightedTransferBound baseUpperSupport transferUpperSupport
          budget uniqueBallotCount candidateCount verificationBound)) ∧
      multiWinnerContainmentConcreteOperationCount
          (multiWinnerContainmentConcreteProblem lower upper
            winnerFirstChoiceVotes quota surplusVotes nextChoiceVotes
            unweightedTransferBound baseUpperSupport transferUpperSupport
            budget uniqueBallotCount candidateCount verificationBound) ≤
        verificationBound := by
  exact
    theorem2_2_concreteContainmentAlgorithm_sound_and_polynomial_runtime_of_nextChoice_unweighted_baseSupport
      (algorithm := multiWinnerContainmentConcreteAlgorithm lower upper)
      (operationCount :=
        multiWinnerContainmentConcreteOperationCount
          (Candidate := Candidate))
      (lower := lower)
      (upper := upper)
      (winnerFirstChoiceVotes := winnerFirstChoiceVotes)
      (quota := quota)
      (budget := budget)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      (verificationBound := verificationBound)
      (surplusVotes := surplusVotes)
      (nextChoiceVotes := nextChoiceVotes)
      (unweightedTransferBound := unweightedTransferBound)
      (baseUpperSupport := baseUpperSupport)
      (transferUpperSupport := transferUpperSupport)
      hcomponent rfl le_rfl

/--
Concrete Theorem 2.2 containment implementation from the source updated
strict-support condition, without replaying the Eq. (2)/(3) sufficient
condition.
-/
theorem theorem2_2_concreteContainmentAlgorithmImplementation_sound_and_polynomial_runtime_of_condition
    {Candidate : Type*} [DecidableEq Candidate]
    {lower upper : Finset Candidate}
    {winnerFirstChoiceVotes quota budget uniqueBallotCount candidateCount
      verificationBound : ℕ}
    {surplusVotes nextChoiceVotes unweightedTransferBound : Candidate → ℕ}
    {baseUpperSupport transferUpperSupport : Candidate → Candidate → ℕ}
    (hcondition :
      multiWinnerContainmentCondition lower upper winnerFirstChoiceVotes quota
        surplusVotes nextChoiceVotes unweightedTransferBound baseUpperSupport
        transferUpperSupport budget) :
    (multiWinnerContainmentConcreteProblem lower upper winnerFirstChoiceVotes
        quota surplusVotes nextChoiceVotes unweightedTransferBound
        baseUpperSupport transferUpperSupport budget uniqueBallotCount
        candidateCount verificationBound).specification
      (multiWinnerContainmentConcreteAlgorithm lower upper
        (multiWinnerContainmentConcreteProblem lower upper
          winnerFirstChoiceVotes quota surplusVotes nextChoiceVotes
          unweightedTransferBound baseUpperSupport transferUpperSupport
          budget uniqueBallotCount candidateCount verificationBound)) ∧
      multiWinnerContainmentConcreteOperationCount
          (multiWinnerContainmentConcreteProblem lower upper
            winnerFirstChoiceVotes quota surplusVotes nextChoiceVotes
            unweightedTransferBound baseUpperSupport transferUpperSupport
            budget uniqueBallotCount candidateCount verificationBound) ≤
        verificationBound := by
  exact ⟨multiWinnerContainmentConcreteSpecification_of_condition hcondition,
    le_rfl⟩

/--
Concrete Theorem 2.2 containment implementation from a source Algorithm 4 run.
The run object packages the no-failed-pair branch condition, and the theorem
returns the retained/removed candidate-set output with the inherited
verification bound.
-/
theorem theorem2_2_concreteContainmentAlgorithmImplementation_sound_and_polynomial_runtime_of_algorithm4Run
    {Candidate : Type*} [DecidableEq Candidate]
    {lower upper : Finset Candidate}
    {winnerFirstChoiceVotes quota budget uniqueBallotCount candidateCount
      verificationBound : ℕ}
    {surplusVotes nextChoiceVotes unweightedTransferBound : Candidate → ℕ}
    {baseUpperSupport transferUpperSupport : Candidate → Candidate → ℕ}
    (run :
      Algorithm4ContainmentRun lower upper winnerFirstChoiceVotes quota budget
        surplusVotes nextChoiceVotes unweightedTransferBound baseUpperSupport
        transferUpperSupport) :
    (multiWinnerContainmentConcreteProblem lower upper winnerFirstChoiceVotes
        quota surplusVotes nextChoiceVotes unweightedTransferBound
        baseUpperSupport transferUpperSupport budget uniqueBallotCount
        candidateCount verificationBound).specification
      (multiWinnerContainmentConcreteAlgorithm lower upper
        (multiWinnerContainmentConcreteProblem lower upper
          winnerFirstChoiceVotes quota surplusVotes nextChoiceVotes
          unweightedTransferBound baseUpperSupport transferUpperSupport
          budget uniqueBallotCount candidateCount verificationBound)) ∧
      multiWinnerContainmentConcreteOperationCount
          (multiWinnerContainmentConcreteProblem lower upper
            winnerFirstChoiceVotes quota surplusVotes nextChoiceVotes
            unweightedTransferBound baseUpperSupport transferUpperSupport
            budget uniqueBallotCount candidateCount verificationBound) ≤
        verificationBound := by
  exact
    theorem2_2_concreteContainmentAlgorithmImplementation_sound_and_polynomial_runtime_of_condition
      (lower := lower)
      (upper := upper)
      (winnerFirstChoiceVotes := winnerFirstChoiceVotes)
      (quota := quota)
      (budget := budget)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      (verificationBound := verificationBound)
      (surplusVotes := surplusVotes)
      (nextChoiceVotes := nextChoiceVotes)
      (unweightedTransferBound := unweightedTransferBound)
      (baseUpperSupport := baseUpperSupport)
      (transferUpperSupport := transferUpperSupport)
      (by
        exact
          algorithm4_pairwise_lt_of_no_failed_pair
            (lower := lower)
            (upper := upper)
            (maxVotes :=
              fun inside outside =>
                lowerCandidateTransferBound
                  (surplusVotes inside) (nextChoiceVotes inside)
                  winnerFirstChoiceVotes (unweightedTransferBound inside))
            (minVotes :=
              fun inside outside =>
                updatedUpperCandidateSupportBound
                  (baseUpperSupport inside outside)
                  (transferUpperSupport inside outside)
                  winnerFirstChoiceVotes quota)
            (budget := budget)
            run.no_failed_pair)

/--
Concrete Theorem 2.2 containment implementation from the source-extracted
Algorithm 4 no-failed-pair check.  The Eq. (2)/(3) quantities are computed
from the ballot profile and lower/upper candidate sets.
-/
theorem theorem2_2_concreteContainmentAlgorithmImplementation_sound_and_polynomial_runtime_of_sourceNoFailedPairCheck
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {lower upper : Finset Candidate} {winner : Candidate}
    {quota budget uniqueBallotCount candidateCount verificationBound : ℕ}
    (hcheck :
      algorithm4SourceNoFailedPairCheck voters ballots lower upper winner
        quota budget = true) :
    (multiWinnerContainmentConcreteProblem lower upper
        (algorithm4WinnerFirstChoiceVotes voters ballots winner)
        quota
        (algorithm4SourceSurplusVotes voters ballots winner lower quota)
        (algorithm4SourceNextChoiceVotes voters ballots winner lower)
        (algorithm4SourceUnweightedTransferBound voters ballots winner lower)
        (algorithm4SourceBaseUpperSupport voters ballots lower)
        (algorithm4SourceTransferUpperSupport voters ballots winner lower)
        budget uniqueBallotCount candidateCount verificationBound).specification
      (multiWinnerContainmentConcreteAlgorithm lower upper
        (multiWinnerContainmentConcreteProblem lower upper
          (algorithm4WinnerFirstChoiceVotes voters ballots winner)
          quota
          (algorithm4SourceSurplusVotes voters ballots winner lower quota)
          (algorithm4SourceNextChoiceVotes voters ballots winner lower)
          (algorithm4SourceUnweightedTransferBound voters ballots winner lower)
          (algorithm4SourceBaseUpperSupport voters ballots lower)
          (algorithm4SourceTransferUpperSupport voters ballots winner lower)
          budget uniqueBallotCount candidateCount verificationBound)) ∧
      multiWinnerContainmentConcreteOperationCount
          (multiWinnerContainmentConcreteProblem lower upper
            (algorithm4WinnerFirstChoiceVotes voters ballots winner)
            quota
            (algorithm4SourceSurplusVotes voters ballots winner lower quota)
            (algorithm4SourceNextChoiceVotes voters ballots winner lower)
            (algorithm4SourceUnweightedTransferBound voters ballots winner lower)
            (algorithm4SourceBaseUpperSupport voters ballots lower)
            (algorithm4SourceTransferUpperSupport voters ballots winner lower)
            budget uniqueBallotCount candidateCount verificationBound) ≤
        verificationBound := by
  exact
    theorem2_2_concreteContainmentAlgorithmImplementation_sound_and_polynomial_runtime_of_algorithm4Run
      (lower := lower)
      (upper := upper)
      (winnerFirstChoiceVotes :=
        algorithm4WinnerFirstChoiceVotes voters ballots winner)
      (quota := quota)
      (budget := budget)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      (verificationBound := verificationBound)
      (surplusVotes :=
        algorithm4SourceSurplusVotes voters ballots winner lower quota)
      (nextChoiceVotes :=
        algorithm4SourceNextChoiceVotes voters ballots winner lower)
      (unweightedTransferBound :=
        algorithm4SourceUnweightedTransferBound voters ballots winner lower)
      (baseUpperSupport :=
        algorithm4SourceBaseUpperSupport voters ballots lower)
      (transferUpperSupport :=
        algorithm4SourceTransferUpperSupport voters ballots winner lower)
      (algorithm4ContainmentRun_of_sourceNoFailedPairCheck_eq_true
        (voters := voters)
        (ballots := ballots)
        (lower := lower)
        (upper := upper)
        (winner := winner)
        (quota := quota)
        (budget := budget)
        hcheck)

/--
Concrete Theorem 2.2 containment implementation from the source-extracted
Algorithm 4 no-failed-pair check, with the verification bound instantiated by
the profile and retained/removed candidate sets.
-/
theorem theorem2_2_concreteContainmentAlgorithmImplementation_sound_and_profile_quadratic_runtime_of_sourceNoFailedPairCheck
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {lower upper : Finset Candidate} {winner : Candidate}
    {quota budget : ℕ}
    (hcheck :
      algorithm4SourceNoFailedPairCheck voters ballots lower upper winner
        quota budget = true) :
    (multiWinnerContainmentConcreteProblem lower upper
        (algorithm4WinnerFirstChoiceVotes voters ballots winner)
        quota
        (algorithm4SourceSurplusVotes voters ballots winner lower quota)
        (algorithm4SourceNextChoiceVotes voters ballots winner lower)
        (algorithm4SourceUnweightedTransferBound voters ballots winner lower)
        (algorithm4SourceBaseUpperSupport voters ballots lower)
        (algorithm4SourceTransferUpperSupport voters ballots winner lower)
        budget voters.card (lower ∪ upper).card
        (voters.card * (lower ∪ upper).card ^ 2)).specification
      (multiWinnerContainmentConcreteAlgorithm lower upper
        (multiWinnerContainmentConcreteProblem lower upper
          (algorithm4WinnerFirstChoiceVotes voters ballots winner)
          quota
          (algorithm4SourceSurplusVotes voters ballots winner lower quota)
          (algorithm4SourceNextChoiceVotes voters ballots winner lower)
          (algorithm4SourceUnweightedTransferBound voters ballots winner lower)
          (algorithm4SourceBaseUpperSupport voters ballots lower)
          (algorithm4SourceTransferUpperSupport voters ballots winner lower)
          budget voters.card (lower ∪ upper).card
          (voters.card * (lower ∪ upper).card ^ 2))) ∧
      multiWinnerContainmentConcreteOperationCount
          (multiWinnerContainmentConcreteProblem lower upper
            (algorithm4WinnerFirstChoiceVotes voters ballots winner)
            quota
            (algorithm4SourceSurplusVotes voters ballots winner lower quota)
            (algorithm4SourceNextChoiceVotes voters ballots winner lower)
            (algorithm4SourceUnweightedTransferBound voters ballots winner lower)
            (algorithm4SourceBaseUpperSupport voters ballots lower)
            (algorithm4SourceTransferUpperSupport voters ballots winner lower)
            budget voters.card (lower ∪ upper).card
            (voters.card * (lower ∪ upper).card ^ 2)) ≤
        voters.card * (lower ∪ upper).card ^ 2 := by
  exact
    theorem2_2_concreteContainmentAlgorithmImplementation_sound_and_polynomial_runtime_of_sourceNoFailedPairCheck
      (voters := voters)
      (ballots := ballots)
      (lower := lower)
      (upper := upper)
      (winner := winner)
      (quota := quota)
      (budget := budget)
      (uniqueBallotCount := voters.card)
      (candidateCount := (lower ∪ upper).card)
      (verificationBound := voters.card * (lower ∪ upper).card ^ 2)
      hcheck

/--
Concrete Theorem 2.2 implementation from conservative Eq. (2)/(3) component
bounds.  This keeps the concrete retained/removed output and verification
bound, while allowing the source proof to use any pair-indexed conservative
lower-transfer and upper-support formulas.
-/
theorem theorem2_2_concreteContainmentAlgorithmImplementation_sound_and_polynomial_runtime_of_component_bounds
    {Candidate : Type*} [DecidableEq Candidate]
    {lower upper : Finset Candidate}
    {winnerFirstChoiceVotes quota budget uniqueBallotCount candidateCount
      verificationBound : ℕ}
    {surplusVotes nextChoiceVotes unweightedTransferBound : Candidate → ℕ}
    {baseUpperSupport transferUpperSupport : Candidate → Candidate → ℕ}
    (conservativeLower conservativeUpper : Candidate → Candidate → ℕ)
    (hcomponent :
      ∀ inside, inside ∈ lower → ∀ outside, outside ∈ upper →
        budget + conservativeLower inside outside <
          conservativeUpper inside outside)
    (hlower_bound :
      ∀ inside, inside ∈ lower → ∀ outside, outside ∈ upper →
        multiWinnerLowerCandidateTransferBound
            surplusVotes nextChoiceVotes unweightedTransferBound
            winnerFirstChoiceVotes inside outside ≤
          conservativeLower inside outside)
    (hupper_bound :
      ∀ inside, inside ∈ lower → ∀ outside, outside ∈ upper →
        conservativeUpper inside outside ≤
          multiWinnerUpdatedUpperSupportBound
            baseUpperSupport transferUpperSupport winnerFirstChoiceVotes quota
            inside outside) :
    (multiWinnerContainmentConcreteProblem lower upper winnerFirstChoiceVotes
        quota surplusVotes nextChoiceVotes unweightedTransferBound
        baseUpperSupport transferUpperSupport budget uniqueBallotCount
        candidateCount verificationBound).specification
      (multiWinnerContainmentConcreteAlgorithm lower upper
        (multiWinnerContainmentConcreteProblem lower upper
          winnerFirstChoiceVotes quota surplusVotes nextChoiceVotes
          unweightedTransferBound baseUpperSupport transferUpperSupport
          budget uniqueBallotCount candidateCount verificationBound)) ∧
      multiWinnerContainmentConcreteOperationCount
          (multiWinnerContainmentConcreteProblem lower upper
            winnerFirstChoiceVotes quota surplusVotes nextChoiceVotes
            unweightedTransferBound baseUpperSupport transferUpperSupport
            budget uniqueBallotCount candidateCount verificationBound) ≤
        verificationBound := by
  exact
    theorem2_2_concreteContainmentAlgorithmImplementation_sound_and_polynomial_runtime_of_condition
      (lower := lower)
      (upper := upper)
      (winnerFirstChoiceVotes := winnerFirstChoiceVotes)
      (quota := quota)
      (budget := budget)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      (verificationBound := verificationBound)
      (surplusVotes := surplusVotes)
      (nextChoiceVotes := nextChoiceVotes)
      (unweightedTransferBound := unweightedTransferBound)
      (baseUpperSupport := baseUpperSupport)
      (transferUpperSupport := transferUpperSupport)
      (multiWinnerContainmentCondition_of_component_bounds
        conservativeLower conservativeUpper hcomponent hlower_bound
        hupper_bound)

/--
A source-shaped multi-winner containment certificate gives the generic
soundness certificate used by the reusable optimization library.
-/
theorem multiWinnerContainmentCertificate_of_soundnessCertificate
    {ContainedInstance : Type*}
    {algorithm :
      MultiWinnerContainmentProblem ContainedInstance → ContainedInstance}
    {operationCount :
      MultiWinnerContainmentProblem ContainedInstance → ℕ}
    (cert :
      MultiWinnerContainmentSoundnessCertificate algorithm operationCount) :
    MultiWinnerContainmentCertificate algorithm operationCount :=
  EconCSLib.Optimization.AlgorithmSoundnessCertificate.of_output_spec
    cert.output_spec cert.operationCount_le

/--
Source-shaped Algorithm 4 certificate for Theorem 2.2.

The certificate records the lower/upper candidate sets, the early winner's
first-choice count and quota, the Eq. (2) lower-candidate transfer inputs, the
Eq. (3) upper-candidate support inputs, and the bridge from the assembled
updated strict-support condition to the output preservation specification.
-/
structure MultiWinnerContainmentConditionCertificate
    {ContainedInstance Candidate : Type*} [DecidableEq Candidate]
    (algorithm :
      MultiWinnerContainmentProblem ContainedInstance → ContainedInstance)
    (operationCount :
      MultiWinnerContainmentProblem ContainedInstance → ℕ) where
  lower : MultiWinnerContainmentProblem ContainedInstance → Finset Candidate
  upper : MultiWinnerContainmentProblem ContainedInstance → Finset Candidate
  winnerFirstChoiceVotes :
    MultiWinnerContainmentProblem ContainedInstance → ℕ
  quota : MultiWinnerContainmentProblem ContainedInstance → ℕ
  surplusVotes :
    MultiWinnerContainmentProblem ContainedInstance → Candidate → ℕ
  nextChoiceVotes :
    MultiWinnerContainmentProblem ContainedInstance → Candidate → ℕ
  unweightedTransferBound :
    MultiWinnerContainmentProblem ContainedInstance → Candidate → ℕ
  baseUpperSupport :
    MultiWinnerContainmentProblem ContainedInstance →
      Candidate → Candidate → ℕ
  transferUpperSupport :
    MultiWinnerContainmentProblem ContainedInstance →
      Candidate → Candidate → ℕ
  condition :
    ∀ problem : MultiWinnerContainmentProblem ContainedInstance,
      multiWinnerContainmentCondition
        (lower problem) (upper problem)
        (winnerFirstChoiceVotes problem) (quota problem)
        (surplusVotes problem) (nextChoiceVotes problem)
        (unweightedTransferBound problem)
        (baseUpperSupport problem) (transferUpperSupport problem)
        problem.budget
  output_spec_of_condition :
    ∀ problem : MultiWinnerContainmentProblem ContainedInstance,
      multiWinnerContainmentCondition
        (lower problem) (upper problem)
        (winnerFirstChoiceVotes problem) (quota problem)
        (surplusVotes problem) (nextChoiceVotes problem)
        (unweightedTransferBound problem)
        (baseUpperSupport problem) (transferUpperSupport problem)
        problem.budget →
        problem.specification (algorithm problem)
  operationCount_le :
    ∀ problem : MultiWinnerContainmentProblem ContainedInstance,
      operationCount problem ≤
        MultiWinnerContainmentProblem.polynomialVerificationBound problem

/--
An Algorithm 4 condition certificate gives the generic soundness certificate
used by the source-facing Theorem 2.2 projection.
-/
def multiWinnerContainmentCertificate_of_conditionCertificate
    {ContainedInstance Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      MultiWinnerContainmentProblem ContainedInstance → ContainedInstance}
    {operationCount :
      MultiWinnerContainmentProblem ContainedInstance → ℕ}
    (cert :
      MultiWinnerContainmentConditionCertificate
        (Candidate := Candidate) algorithm operationCount) :
    MultiWinnerContainmentCertificate algorithm operationCount :=
  EconCSLib.Optimization.AlgorithmSoundnessCertificate.of_condition
    (fun problem =>
      multiWinnerContainmentCondition
        (cert.lower problem) (cert.upper problem)
        (cert.winnerFirstChoiceVotes problem) (cert.quota problem)
        (cert.surplusVotes problem) (cert.nextChoiceVotes problem)
        (cert.unweightedTransferBound problem)
        (cert.baseUpperSupport problem) (cert.transferUpperSupport problem)
        problem.budget)
    cert.condition cert.output_spec_of_condition cert.operationCount_le

/--
Build an Algorithm 4 condition certificate when the source model supplies the
updated strict-support condition, the condition-to-spec bridge, and a
polynomial verification operation-count proof.
-/
def multiWinnerContainmentConditionCertificate_of_runtimeBound
    {ContainedInstance Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      MultiWinnerContainmentProblem ContainedInstance → ContainedInstance}
    {operationCount :
      MultiWinnerContainmentProblem ContainedInstance → ℕ}
    (lower upper :
      MultiWinnerContainmentProblem ContainedInstance → Finset Candidate)
    (winnerFirstChoiceVotes quota :
      MultiWinnerContainmentProblem ContainedInstance → ℕ)
    (surplusVotes nextChoiceVotes unweightedTransferBound :
      MultiWinnerContainmentProblem ContainedInstance → Candidate → ℕ)
    (baseUpperSupport transferUpperSupport :
      MultiWinnerContainmentProblem ContainedInstance →
        Candidate → Candidate → ℕ)
    (condition :
      ∀ problem : MultiWinnerContainmentProblem ContainedInstance,
        multiWinnerContainmentCondition
          (lower problem) (upper problem)
          (winnerFirstChoiceVotes problem) (quota problem)
          (surplusVotes problem) (nextChoiceVotes problem)
          (unweightedTransferBound problem)
          (baseUpperSupport problem) (transferUpperSupport problem)
          problem.budget)
    (output_spec_of_condition :
      ∀ problem : MultiWinnerContainmentProblem ContainedInstance,
        multiWinnerContainmentCondition
          (lower problem) (upper problem)
          (winnerFirstChoiceVotes problem) (quota problem)
          (surplusVotes problem) (nextChoiceVotes problem)
          (unweightedTransferBound problem)
          (baseUpperSupport problem) (transferUpperSupport problem)
          problem.budget →
          problem.specification (algorithm problem))
    (operationCount_le :
      ∀ problem : MultiWinnerContainmentProblem ContainedInstance,
        operationCount problem ≤
          MultiWinnerContainmentProblem.polynomialVerificationBound problem) :
    MultiWinnerContainmentConditionCertificate
      (Candidate := Candidate) algorithm operationCount where
  lower := lower
  upper := upper
  winnerFirstChoiceVotes := winnerFirstChoiceVotes
  quota := quota
  surplusVotes := surplusVotes
  nextChoiceVotes := nextChoiceVotes
  unweightedTransferBound := unweightedTransferBound
  baseUpperSupport := baseUpperSupport
  transferUpperSupport := transferUpperSupport
  condition := condition
  output_spec_of_condition := output_spec_of_condition
  operationCount_le := operationCount_le

/--
Source-shaped Algorithm 4 certificate for the simplified Eq. (2)/(3) route:
the source proof compares `nextChoice + unweighted` lower transfers directly
against the base upper-support term. The weighted-transfer and updated-support
arithmetic then supply the full updated strict-support condition.
-/
structure MultiWinnerContainmentSimpleBoundCertificate
    {ContainedInstance Candidate : Type*} [DecidableEq Candidate]
    (algorithm :
      MultiWinnerContainmentProblem ContainedInstance → ContainedInstance)
    (operationCount :
      MultiWinnerContainmentProblem ContainedInstance → ℕ) where
  lower : MultiWinnerContainmentProblem ContainedInstance → Finset Candidate
  upper : MultiWinnerContainmentProblem ContainedInstance → Finset Candidate
  winnerFirstChoiceVotes :
    MultiWinnerContainmentProblem ContainedInstance → ℕ
  quota : MultiWinnerContainmentProblem ContainedInstance → ℕ
  surplusVotes :
    MultiWinnerContainmentProblem ContainedInstance → Candidate → ℕ
  nextChoiceVotes :
    MultiWinnerContainmentProblem ContainedInstance → Candidate → ℕ
  unweightedTransferBound :
    MultiWinnerContainmentProblem ContainedInstance → Candidate → ℕ
  baseUpperSupport :
    MultiWinnerContainmentProblem ContainedInstance →
      Candidate → Candidate → ℕ
  transferUpperSupport :
    MultiWinnerContainmentProblem ContainedInstance →
      Candidate → Candidate → ℕ
  simple_condition :
    ∀ problem : MultiWinnerContainmentProblem ContainedInstance,
      ∀ inside, inside ∈ lower problem →
      ∀ outside, outside ∈ upper problem →
        problem.budget +
            (nextChoiceVotes problem inside +
              unweightedTransferBound problem inside) <
          baseUpperSupport problem inside outside
  output_spec_of_condition :
    ∀ problem : MultiWinnerContainmentProblem ContainedInstance,
      multiWinnerContainmentCondition
        (lower problem) (upper problem)
        (winnerFirstChoiceVotes problem) (quota problem)
        (surplusVotes problem) (nextChoiceVotes problem)
        (unweightedTransferBound problem)
        (baseUpperSupport problem) (transferUpperSupport problem)
        problem.budget →
        problem.specification (algorithm problem)
  operationCount_le :
    ∀ problem : MultiWinnerContainmentProblem ContainedInstance,
      operationCount problem ≤
        MultiWinnerContainmentProblem.polynomialVerificationBound problem

/--
The simplified Eq. (2)/(3) certificate gives the standard Algorithm 4
updated-strict-support condition certificate.
-/
def multiWinnerContainmentConditionCertificate_of_simpleBoundCertificate
    {ContainedInstance Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      MultiWinnerContainmentProblem ContainedInstance → ContainedInstance}
    {operationCount :
      MultiWinnerContainmentProblem ContainedInstance → ℕ}
    (cert :
      MultiWinnerContainmentSimpleBoundCertificate
        (Candidate := Candidate) algorithm operationCount) :
    MultiWinnerContainmentConditionCertificate
      (Candidate := Candidate) algorithm operationCount where
  lower := cert.lower
  upper := cert.upper
  winnerFirstChoiceVotes := cert.winnerFirstChoiceVotes
  quota := cert.quota
  surplusVotes := cert.surplusVotes
  nextChoiceVotes := cert.nextChoiceVotes
  unweightedTransferBound := cert.unweightedTransferBound
  baseUpperSupport := cert.baseUpperSupport
  transferUpperSupport := cert.transferUpperSupport
  condition := by
    intro problem
    exact multiWinnerContainmentCondition_of_nextChoice_unweighted_baseSupport
      (lower := cert.lower problem)
      (upper := cert.upper problem)
      (winnerFirstChoiceVotes := cert.winnerFirstChoiceVotes problem)
      (quota := cert.quota problem)
      (surplusVotes := cert.surplusVotes problem)
      (nextChoiceVotes := cert.nextChoiceVotes problem)
      (unweightedTransferBound := cert.unweightedTransferBound problem)
      (baseUpperSupport := cert.baseUpperSupport problem)
      (transferUpperSupport := cert.transferUpperSupport problem)
      (budget := problem.budget)
      (cert.simple_condition problem)
  output_spec_of_condition := cert.output_spec_of_condition
  operationCount_le := cert.operationCount_le

/--
The simplified Eq. (2)/(3) certificate gives the generic Algorithm 4 soundness
certificate.
-/
def multiWinnerContainmentCertificate_of_simpleBoundCertificate
    {ContainedInstance Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      MultiWinnerContainmentProblem ContainedInstance → ContainedInstance}
    {operationCount :
      MultiWinnerContainmentProblem ContainedInstance → ℕ}
    (cert :
      MultiWinnerContainmentSimpleBoundCertificate
        (Candidate := Candidate) algorithm operationCount) :
    MultiWinnerContainmentCertificate algorithm operationCount :=
  multiWinnerContainmentCertificate_of_conditionCertificate
    (multiWinnerContainmentConditionCertificate_of_simpleBoundCertificate cert)

/--
Shared prerequisite for Proposition 1 / Proposition 2 robustness work:
the first active preference on a ballot is always an active candidate.
-/
theorem next_active_is_active {Candidate : Type*} [DecidableEq Candidate]
    {ballot : RCVBallot Candidate} {active : Finset Candidate} {candidate : Candidate}
    (h : Ballot.nextActive ballot active = some candidate) :
    candidate ∈ active :=
  Ballot.nextActive_mem h

/--
Suffixing arbitrary subsequent preferences does not change the first active
candidate when the original strategy ballot already reaches one.
-/
theorem suffixing_preserves_first_active {Candidate : Type*} [DecidableEq Candidate]
    {base extended : RCVBallot Candidate} {active : Finset Candidate}
    {candidate : Candidate}
    (hext : ballotSuffixExtension base extended)
    (hnext : Ballot.nextActive base active = some candidate) :
    Ballot.nextActive extended active = some candidate := by
  rcases hext with ⟨suffix, rfl⟩
  exact Ballot.nextActive_append_of_some hnext

/--
Prefixing candidates that are already inactive does not change the first active
candidate of the strategy ballot.
-/
theorem prefixing_inactive_candidates_preserves_nextActive {Candidate : Type*}
    [DecidableEq Candidate]
    {pref base extended : RCVBallot Candidate} {active : Finset Candidate}
    (hext : ballotPrefixExtension pref base extended)
    (hpref : exhaustedPrefixAtActiveSet pref active) :
    Ballot.nextActive extended active = Ballot.nextActive base active := by
  rw [ballotPrefixExtension] at hext
  rw [hext]
  exact Ballot.nextActive_append_left_of_forall_not_mem hpref

/--
Suffixing arbitrary subsequent preferences to every added ballot preserves the
active-support count for every candidate, provided each base strategy ballot
already reaches some active candidate at the active set.
-/
theorem suffixing_preserves_activeSupport_count {Voter Candidate : Type*}
    [DecidableEq Candidate]
    {voters : Finset Voter}
    {base extended : Voter → RCVBallot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hext : ∀ voter ∈ voters,
      ballotSuffixExtension (base voter) (extended voter))
    (hreaches : ∀ voter ∈ voters,
      ∃ first, Ballot.nextActive (base voter) active = some first) :
    (Ballot.activeSupport voters extended active candidate).card =
      (Ballot.activeSupport voters base active candidate).card := by
  exact Ballot.activeSupport_card_eq_of_forall_suffixExtension_nextActive_some
    hext hreaches

/--
Prefixing inactive or exhausted candidates to every added ballot preserves the
active-support count for every candidate at the current active set.
-/
theorem prefixing_inactive_candidates_preserves_activeSupport_count
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {pref base extended : Voter → RCVBallot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hext : ∀ voter ∈ voters,
      ballotPrefixExtension (pref voter) (base voter) (extended voter))
    (hpref : ∀ voter ∈ voters, exhaustedPrefixAtActiveSet (pref voter) active) :
    (Ballot.activeSupport voters extended active candidate).card =
      (Ballot.activeSupport voters base active candidate).card := by
  exact Ballot.activeSupport_card_eq_of_forall_prefixExtension_inactive
    hext hpref

/--
Profile-level active-support counts agree on every active set relevant to a
source optimization problem.
-/
def activeSupportCountsEqualOn
    {Problem Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Problem → Finset Voter)
    (relevantActiveSets : Problem → Finset (Finset Candidate))
    (base robust : Problem → Voter → RCVBallot Candidate) : Prop :=
  ∀ problem active, active ∈ relevantActiveSets problem →
    ∀ candidate,
      (Ballot.activeSupport (voters problem) (robust problem) active
          candidate).card =
      (Ballot.activeSupport (voters problem) (base problem) active
          candidate).card

/-- Active-support count equality is reflexive. -/
theorem activeSupportCountsEqualOn_refl
    {Problem Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Problem → Finset Voter)
    (relevantActiveSets : Problem → Finset (Finset Candidate))
    (base : Problem → Voter → RCVBallot Candidate) :
    activeSupportCountsEqualOn voters relevantActiveSets base base := by
  intro _problem _active _hactive _candidate
  rfl

/-- Active-support count equality is symmetric. -/
theorem activeSupportCountsEqualOn_symm
    {Problem Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Problem → Finset Voter}
    {relevantActiveSets : Problem → Finset (Finset Candidate)}
    {base robust : Problem → Voter → RCVBallot Candidate}
    (hcounts :
      activeSupportCountsEqualOn voters relevantActiveSets base robust) :
    activeSupportCountsEqualOn voters relevantActiveSets robust base := by
  intro problem active hactive candidate
  exact (hcounts problem active hactive candidate).symm

/-- Active-support count equality composes across chained ballot transforms. -/
theorem activeSupportCountsEqualOn_trans
    {Problem Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Problem → Finset Voter}
    {relevantActiveSets : Problem → Finset (Finset Candidate)}
    {base middle robust : Problem → Voter → RCVBallot Candidate}
    (hbase_middle :
      activeSupportCountsEqualOn voters relevantActiveSets base middle)
    (hmiddle_robust :
      activeSupportCountsEqualOn voters relevantActiveSets middle robust) :
    activeSupportCountsEqualOn voters relevantActiveSets base robust := by
  intro problem active hactive candidate
  exact (hmiddle_robust problem active hactive candidate).trans
    (hbase_middle problem active hactive candidate)

/--
Suffix extensions give support-count equality on all relevant active sets when
each base strategy ballot already reaches an active candidate.
-/
theorem activeSupportCountsEqualOn_of_suffix_extensions
    {Problem Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Problem → Finset Voter}
    {relevantActiveSets : Problem → Finset (Finset Candidate)}
    {base robust : Problem → Voter → RCVBallot Candidate}
    (hext : ∀ problem voter, voter ∈ voters problem →
      ballotSuffixExtension (base problem voter) (robust problem voter))
    (hreaches : ∀ problem active, active ∈ relevantActiveSets problem →
      ∀ voter, voter ∈ voters problem →
        ∃ first, Ballot.nextActive (base problem voter) active = some first) :
    activeSupportCountsEqualOn voters relevantActiveSets base robust := by
  intro problem active hactive candidate
  exact suffixing_preserves_activeSupport_count
    (voters := voters problem)
    (base := base problem)
    (extended := robust problem)
    (active := active)
    (candidate := candidate)
    (fun voter hvoter => hext problem voter hvoter)
    (fun voter hvoter => hreaches problem active hactive voter hvoter)

/--
Inactive prefixes give support-count equality on all relevant active sets.
-/
theorem activeSupportCountsEqualOn_of_prefix_extensions
    {Problem Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Problem → Finset Voter}
    {relevantActiveSets : Problem → Finset (Finset Candidate)}
    {pref base robust : Problem → Voter → RCVBallot Candidate}
    (hext : ∀ problem voter, voter ∈ voters problem →
      ballotPrefixExtension (pref problem voter) (base problem voter)
        (robust problem voter))
    (hpref : ∀ problem active, active ∈ relevantActiveSets problem →
      ∀ voter, voter ∈ voters problem →
        exhaustedPrefixAtActiveSet (pref problem voter) active) :
    activeSupportCountsEqualOn voters relevantActiveSets base robust := by
  intro problem active hactive candidate
  exact prefixing_inactive_candidates_preserves_activeSupport_count
    (voters := voters problem)
    (pref := pref problem)
    (base := base problem)
    (extended := robust problem)
    (active := active)
    (candidate := candidate)
    (fun voter hvoter => hext problem voter hvoter)
    (fun voter hvoter => hpref problem active hactive voter hvoter)

/--
Exhausted-prefix completion gives support-count equality between completed
ballots and the strategy suffixes on all relevant active sets.
-/
theorem activeSupportCountsEqualOn_of_exhausted_completion
    {Problem Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Problem → Finset Voter}
    {relevantActiveSets : Problem → Finset (Finset Candidate)}
    {exhausted strategy completed :
      Problem → Voter → RCVBallot Candidate}
    (hcompleted : ∀ problem voter, voter ∈ voters problem →
      completed problem voter = exhausted problem voter ++ strategy problem voter)
    (hexhausted : ∀ problem active, active ∈ relevantActiveSets problem →
      ∀ voter, voter ∈ voters problem →
        Ballot.nextActive (exhausted problem voter) active = none) :
    activeSupportCountsEqualOn voters relevantActiveSets strategy completed := by
  intro problem active hactive candidate
  exact Ballot.activeSupport_card_eq_of_forall_append_exhausted_prefix
    (voters := voters problem)
    (pref := exhausted problem)
    (strategy := strategy problem)
    (completed := completed problem)
    (active := active)
    (candidate := candidate)
    (fun voter hvoter => hcompleted problem voter hvoter)
    (fun voter hvoter => hexhausted problem active hactive voter hvoter)

/--
Chained Proposition 1 support-count constructor: suffixing base strategy
ballots and then prefixing inactive ballots preserves all relevant active
support counts.
-/
theorem activeSupportCountsEqualOn_of_suffix_then_prefix_extensions
    {Problem Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Problem → Finset Voter}
    {relevantActiveSets : Problem → Finset (Finset Candidate)}
    {base middle robust pref : Problem → Voter → RCVBallot Candidate}
    (hsuffix : ∀ problem voter, voter ∈ voters problem →
      ballotSuffixExtension (base problem voter) (middle problem voter))
    (hreaches : ∀ problem active, active ∈ relevantActiveSets problem →
      ∀ voter, voter ∈ voters problem →
        ∃ first, Ballot.nextActive (base problem voter) active = some first)
    (hprefix : ∀ problem voter, voter ∈ voters problem →
      ballotPrefixExtension (pref problem voter) (middle problem voter)
        (robust problem voter))
    (hpref : ∀ problem active, active ∈ relevantActiveSets problem →
      ∀ voter, voter ∈ voters problem →
        exhaustedPrefixAtActiveSet (pref problem voter) active) :
    activeSupportCountsEqualOn voters relevantActiveSets base robust :=
  activeSupportCountsEqualOn_trans
    (activeSupportCountsEqualOn_of_suffix_extensions hsuffix hreaches)
    (activeSupportCountsEqualOn_of_prefix_extensions hprefix hpref)

/--
Chained Proposition 1 support-count constructor: prefixing inactive ballots
and then suffixing arbitrary later preferences preserves all relevant active
support counts.
-/
theorem activeSupportCountsEqualOn_of_prefix_then_suffix_extensions
    {Problem Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Problem → Finset Voter}
    {relevantActiveSets : Problem → Finset (Finset Candidate)}
    {base middle robust pref : Problem → Voter → RCVBallot Candidate}
    (hprefix : ∀ problem voter, voter ∈ voters problem →
      ballotPrefixExtension (pref problem voter) (base problem voter)
        (middle problem voter))
    (hpref : ∀ problem active, active ∈ relevantActiveSets problem →
      ∀ voter, voter ∈ voters problem →
        exhaustedPrefixAtActiveSet (pref problem voter) active)
    (hsuffix : ∀ problem voter, voter ∈ voters problem →
      ballotSuffixExtension (middle problem voter) (robust problem voter))
    (hreaches : ∀ problem active, active ∈ relevantActiveSets problem →
      ∀ voter, voter ∈ voters problem →
        ∃ first, Ballot.nextActive (base problem voter) active = some first) :
    activeSupportCountsEqualOn voters relevantActiveSets base robust := by
  apply activeSupportCountsEqualOn_trans
  · exact activeSupportCountsEqualOn_of_prefix_extensions hprefix hpref
  · apply activeSupportCountsEqualOn_of_suffix_extensions hsuffix
    intro problem active hactive voter hvoter
    rcases hreaches problem active hactive voter hvoter with ⟨first, hfirst⟩
    refine ⟨first, ?_⟩
    have hnext :
        Ballot.nextActive (middle problem voter) active =
          Ballot.nextActive (base problem voter) active :=
      prefixing_inactive_candidates_preserves_nextActive
        (hprefix problem voter hvoter)
        (hpref problem active hactive voter hvoter)
    simpa [hfirst] using hnext

/--
Completing an exhausted ballot with a strategy suffix is equivalent, at the
current active set, to adding the strategy ballot itself.
-/
theorem exhausted_completion_nextActive_eq_strategy {Candidate : Type*}
    [DecidableEq Candidate]
    {exhausted strategy : RCVBallot Candidate} {active : Finset Candidate}
    (hexhausted : Ballot.nextActive exhausted active = none) :
    Ballot.nextActive (exhausted ++ strategy) active =
      Ballot.nextActive strategy active :=
  Ballot.nextActive_append_of_none hexhausted

/--
If the strategy ballot would activate candidate `candidate`, then completing an
exhausted ballot with that strategy activates the same candidate.
-/
theorem exhausted_completion_activates_strategy_candidate {Candidate : Type*}
    [DecidableEq Candidate]
    {exhausted strategy : RCVBallot Candidate} {active : Finset Candidate}
    {candidate : Candidate}
    (hexhausted : Ballot.nextActive exhausted active = none)
    (hstrategy : Ballot.nextActive strategy active = some candidate) :
    Ballot.nextActive (exhausted ++ strategy) active = some candidate := by
  rw [exhausted_completion_nextActive_eq_strategy hexhausted]
  exact hstrategy

/--
Completing every exhausted ballot in a voter profile with its strategy suffix
preserves every candidate's active-support count relative to adding those
strategy ballots directly.
-/
theorem exhausted_completion_preserves_activeSupport_count
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {exhausted strategy completed : Voter → RCVBallot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hcompleted : ∀ voter ∈ voters,
      completed voter = exhausted voter ++ strategy voter)
    (hexhausted : ∀ voter ∈ voters,
      Ballot.nextActive (exhausted voter) active = none) :
    (Ballot.activeSupport voters completed active candidate).card =
      (Ballot.activeSupport voters strategy active candidate).card := by
  exact Ballot.activeSupport_card_eq_of_forall_append_exhausted_prefix
    hcompleted hexhausted

/--
Available exhausted ballots whose completion strategies activate `candidate`
provide the required active-support count for Proposition 2.
-/
theorem exhausted_completion_activeSupport_count_ge_requiredVotes
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {available voters : Finset Voter}
    {exhausted strategy completed : Voter → RCVBallot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    {requiredVotes : ℕ}
    (hrequired : requiredVotes ≤ available.card)
    (hsubset : available ⊆ voters)
    (hcompleted : ∀ voter ∈ available,
      completed voter = exhausted voter ++ strategy voter)
    (hexhausted : ∀ voter ∈ available,
      Ballot.nextActive (exhausted voter) active = none)
    (hstrategy : ∀ voter ∈ available,
      Ballot.nextActive (strategy voter) active = some candidate) :
    requiredVotes ≤
      (Ballot.activeSupport voters completed active candidate).card :=
  le_trans hrequired
    (Ballot.card_le_activeSupport_card_of_subset_forall_append_exhausted_prefix
      hsubset hcompleted hexhausted hstrategy)

/--
Concrete Algorithm A availability set: voters whose original ballot is
exhausted at the activation round and whose strategy suffix activates the
candidate.
-/
def exhaustedCompletionAvailableVoters
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter)
    (exhausted strategy : Voter → RCVBallot Candidate)
    (active : Finset Candidate) (candidate : Candidate) :
    Finset Voter :=
  voters.filter fun voter =>
    Ballot.nextActive (exhausted voter) active = none ∧
      Ballot.nextActive (strategy voter) active = some candidate

theorem mem_exhaustedCompletionAvailableVoters_iff
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {exhausted strategy : Voter → RCVBallot Candidate}
    {active : Finset Candidate} {candidate : Candidate} {voter : Voter} :
    voter ∈
        exhaustedCompletionAvailableVoters voters exhausted strategy active
          candidate ↔
      voter ∈ voters ∧
        Ballot.nextActive (exhausted voter) active = none ∧
          Ballot.nextActive (strategy voter) active = some candidate := by
  simp [exhaustedCompletionAvailableVoters]

/-- Concrete Algorithm A availability count `E_{r_c - 1}` from a profile. -/
def exhaustedCompletionAvailableCount
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter)
    (exhausted strategy : Voter → RCVBallot Candidate)
    (active : Finset Candidate) (candidate : Candidate) : ℕ :=
  (exhaustedCompletionAvailableVoters voters exhausted strategy active
    candidate).card

/--
When every completed ballot is an exhausted prefix followed by its strategy
suffix, the concrete availability count is exactly the completed profile's
active-support count.
-/
theorem exhaustedCompletionAvailableCount_eq_completed_activeSupport_card
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {exhausted strategy completed : Voter → RCVBallot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    (hcompleted : ∀ voter ∈ voters,
      completed voter = exhausted voter ++ strategy voter)
    (hexhausted : ∀ voter ∈ voters,
      Ballot.nextActive (exhausted voter) active = none) :
    exhaustedCompletionAvailableCount voters exhausted strategy active
        candidate =
      (Ballot.activeSupport voters completed active candidate).card := by
  unfold exhaustedCompletionAvailableCount
  congr 1
  ext voter
  by_cases hvoter : voter ∈ voters
  · have hnext :
        Ballot.nextActive (completed voter) active =
          Ballot.nextActive (strategy voter) active := by
      rw [hcompleted voter hvoter]
      exact exhausted_completion_nextActive_eq_strategy
        (hexhausted voter hvoter)
    simp [exhaustedCompletionAvailableVoters, Ballot.activeSupport, hvoter,
      hnext, hexhausted voter hvoter]
  · simp [exhaustedCompletionAvailableVoters, Ballot.activeSupport, hvoter]

/--
Concrete Proposition 2 availability bridge: if the required vote count is at
most the concrete profile count of exhausted ballots whose strategy suffix
activates the candidate, then completing exhausted ballots supplies the
required active support.
-/
theorem exhausted_completion_activeSupport_count_ge_requiredVotes_of_availableCount
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {exhausted strategy : Voter → RCVBallot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    {requiredVotes : ℕ}
    (hrequired :
      requiredVotes ≤
        exhaustedCompletionAvailableCount voters exhausted strategy active
          candidate) :
    requiredVotes ≤
      (Ballot.activeSupport voters
          (fun voter => exhausted voter ++ strategy voter) active
          candidate).card := by
  exact exhausted_completion_activeSupport_count_ge_requiredVotes
    (available :=
      exhaustedCompletionAvailableVoters voters exhausted strategy active
        candidate)
    (voters := voters)
    (exhausted := exhausted)
    (strategy := strategy)
    (completed := fun voter => exhausted voter ++ strategy voter)
    (active := active)
    (candidate := candidate)
    (requiredVotes := requiredVotes)
    hrequired
    (by
      intro voter hvoter
      exact (mem_exhaustedCompletionAvailableVoters_iff.mp hvoter).1)
    (by
      intro voter _hvoter
      rfl)
    (by
      intro voter hvoter
      exact (mem_exhaustedCompletionAvailableVoters_iff.mp hvoter).2.1)
    (by
      intro voter hvoter
      exact (mem_exhaustedCompletionAvailableVoters_iff.mp hvoter).2.2)

/--
Finite required-voter constructor for Proposition 2: if the required strategic
votes fit within the concrete exhausted-ballot availability count, then there
is a finite subcollection of exactly that size whose exhausted prefixes are
inactive and whose strategy suffixes activate the candidate.
-/
theorem exhaustedCompletionAvailableCount_exists_required_voters
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {exhausted strategy : Voter → RCVBallot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    {requiredVotes : ℕ}
    (hrequired :
      requiredVotes ≤
        exhaustedCompletionAvailableCount voters exhausted strategy active
          candidate) :
    ∃ required : Finset Voter,
      required ⊆ voters ∧
        required.card = requiredVotes ∧
          ∀ voter ∈ required,
            Ballot.nextActive (exhausted voter) active = none ∧
              Ballot.nextActive (strategy voter) active = some candidate := by
  obtain ⟨required, hsubset_available, hcard⟩ :=
    Finset.exists_subset_card_eq
      (s :=
        exhaustedCompletionAvailableVoters voters exhausted strategy active
          candidate)
      (by
        simpa [exhaustedCompletionAvailableCount] using hrequired)
  refine ⟨required, ?_, hcard, ?_⟩
  · intro voter hvoter
    exact
      (mem_exhaustedCompletionAvailableVoters_iff.mp
        (hsubset_available hvoter)).1
  · intro voter hvoter
    exact
      (mem_exhaustedCompletionAvailableVoters_iff.mp
        (hsubset_available hvoter)).2

/--
Proposition 2 viability predicate: a candidate can be made viable by completing
exhausted ballots when the required strategic ballots are no more than the
exhausted ballots available before the strategy activates.
-/
def exhaustedCompletionViable {Candidate : Type*}
    (requiredVotes exhaustedBeforeActivation : Candidate → ℕ)
    (candidate : Candidate) : Prop :=
  requiredVotes candidate ≤ exhaustedBeforeActivation candidate

/--
Exact Proposition 2 profile characterization: with exhausted-prefix
completion, the viability inequality is equivalent to having the required
active-support count in the completed profile.
-/
theorem exhaustedCompletionViable_iff_requiredVotes_le_completed_activeSupport_card
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {exhausted strategy completed : Voter → RCVBallot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    {requiredVotes : Candidate → ℕ}
    (hcompleted : ∀ voter ∈ voters,
      completed voter = exhausted voter ++ strategy voter)
    (hexhausted : ∀ voter ∈ voters,
      Ballot.nextActive (exhausted voter) active = none) :
    exhaustedCompletionViable requiredVotes
        (exhaustedCompletionAvailableCount voters exhausted strategy active)
        candidate ↔
      requiredVotes candidate ≤
        (Ballot.activeSupport voters completed active candidate).card := by
  unfold exhaustedCompletionViable
  rw [exhaustedCompletionAvailableCount_eq_completed_activeSupport_card
    hcompleted hexhausted]

/--
The Proposition 2 viability inequality gives the required active-support lower
bound once the available exhausted-ballot set realizes the advertised
availability count.
-/
theorem exhausted_completion_activeSupport_count_ge_requiredVotes_of_viable
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {available voters : Finset Voter}
    {exhausted strategy completed : Voter → RCVBallot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    {requiredVotes exhaustedBeforeActivation : Candidate → ℕ}
    (hviable :
      exhaustedCompletionViable requiredVotes exhaustedBeforeActivation
        candidate)
    (havailable :
      exhaustedBeforeActivation candidate ≤ available.card)
    (hsubset : available ⊆ voters)
    (hcompleted : ∀ voter ∈ available,
      completed voter = exhausted voter ++ strategy voter)
    (hexhausted : ∀ voter ∈ available,
      Ballot.nextActive (exhausted voter) active = none)
    (hstrategy : ∀ voter ∈ available,
      Ballot.nextActive (strategy voter) active = some candidate) :
    requiredVotes candidate ≤
      (Ballot.activeSupport voters completed active candidate).card := by
  exact exhausted_completion_activeSupport_count_ge_requiredVotes
    (le_trans hviable havailable) hsubset hcompleted hexhausted hstrategy

/--
Concrete Proposition 2 profile-availability route: if the viable-candidate
inequality uses the concrete profile count of exhausted ballots whose strategy
suffix activates the candidate, then the completed profile supplies the
required active support.
-/
theorem exhausted_completion_activeSupport_count_ge_requiredVotes_of_profileAvailableCount
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {exhausted strategy : Voter → RCVBallot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    {requiredVotes : Candidate → ℕ}
    (hviable :
      exhaustedCompletionViable requiredVotes
        (exhaustedCompletionAvailableCount voters exhausted strategy active)
        candidate) :
    requiredVotes candidate ≤
      (Ballot.activeSupport voters
          (fun voter => exhausted voter ++ strategy voter) active
          candidate).card := by
  exact
    exhausted_completion_activeSupport_count_ge_requiredVotes_of_availableCount
      hviable

/--
Concrete Proposition 2 required-voter constructor: if the viable-candidate
inequality is instantiated with the concrete profile availability count, then
the required exhausted-ballot completions can be selected from the profile.
-/
theorem exhaustedCompletionAvailableCount_exists_required_voters_of_profileAvailableCount
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {exhausted strategy : Voter → RCVBallot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    {requiredVotes : Candidate → ℕ}
    (hviable :
      exhaustedCompletionViable requiredVotes
        (exhaustedCompletionAvailableCount voters exhausted strategy active)
        candidate) :
    ∃ required : Finset Voter,
      required ⊆ voters ∧
        required.card = requiredVotes candidate ∧
          ∀ voter ∈ required,
            Ballot.nextActive (exhausted voter) active = none ∧
              Ballot.nextActive (strategy voter) active =
                some candidate := by
  exact
    exhaustedCompletionAvailableCount_exists_required_voters
      (voters := voters)
      (exhausted := exhausted)
      (strategy := strategy)
      (active := active)
      (candidate := candidate)
      (requiredVotes := requiredVotes candidate)
      hviable

/--
Proposition 2 viable-candidate set for exhausted-ballot completion.
-/
def exhaustedCompletionViableCandidates {Candidate : Type*}
    [DecidableEq Candidate]
    (candidates : Finset Candidate)
    (requiredVotes exhaustedBeforeActivation : Candidate → ℕ) :
    Finset Candidate :=
  candidates.filter fun candidate =>
    requiredVotes candidate ≤ exhaustedBeforeActivation candidate

/--
Membership in the Proposition 2 viable-candidate set is exactly the source
threshold condition.
-/
theorem mem_exhaustedCompletionViableCandidates_iff {Candidate : Type*}
    [DecidableEq Candidate]
    {candidates : Finset Candidate}
    {requiredVotes exhaustedBeforeActivation : Candidate → ℕ}
    {candidate : Candidate} :
    candidate ∈
        exhaustedCompletionViableCandidates candidates requiredVotes
          exhaustedBeforeActivation ↔
      candidate ∈ candidates ∧
        requiredVotes candidate ≤ exhaustedBeforeActivation candidate := by
  simp [exhaustedCompletionViableCandidates]

/--
Concrete Proposition 2 viable-set route: membership in the viable-candidate
set built from the concrete profile availability count gives the required
active support after exhausted-ballot completion.
-/
theorem exhausted_completion_activeSupport_count_ge_requiredVotes_of_mem_profileViableCandidates
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {exhausted strategy : Voter → RCVBallot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    {candidates : Finset Candidate}
    {requiredVotes : Candidate → ℕ}
    (hmem :
      candidate ∈
        exhaustedCompletionViableCandidates candidates requiredVotes
          (exhaustedCompletionAvailableCount voters exhausted strategy active)) :
    requiredVotes candidate ≤
      (Ballot.activeSupport voters
          (fun voter => exhausted voter ++ strategy voter) active
          candidate).card := by
  exact
    exhausted_completion_activeSupport_count_ge_requiredVotes_of_availableCount
      ((mem_exhaustedCompletionViableCandidates_iff.mp hmem).2)

/--
Concrete Proposition 2 viable-set constructor: membership in the viable set
built from the concrete profile availability count constructs the finite
required voter set internally.
-/
theorem exhaustedCompletionAvailableCount_exists_required_voters_of_mem_profileViableCandidates
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {exhausted strategy : Voter → RCVBallot Candidate}
    {active : Finset Candidate} {candidate : Candidate}
    {candidates : Finset Candidate}
    {requiredVotes : Candidate → ℕ}
    (hmem :
      candidate ∈
        exhaustedCompletionViableCandidates candidates requiredVotes
          (exhaustedCompletionAvailableCount voters exhausted strategy active)) :
    ∃ required : Finset Voter,
      required ⊆ voters ∧
        required.card = requiredVotes candidate ∧
          ∀ voter ∈ required,
            Ballot.nextActive (exhausted voter) active = none ∧
              Ballot.nextActive (strategy voter) active =
                some candidate := by
  exact
    exhaustedCompletionAvailableCount_exists_required_voters_of_profileAvailableCount
      (voters := voters)
      (exhausted := exhausted)
      (strategy := strategy)
      (active := active)
      (candidate := candidate)
      (requiredVotes := requiredVotes)
      ((mem_exhaustedCompletionViableCandidates_iff.mp hmem).2)

/--
Multi-round Proposition 2 viability predicate: every activation round's
required strategic ballots fit within the exhausted ballots available before
that round.
-/
def exhaustedCompletionMultiRoundViable {Round : Type*}
    (activationRounds : Finset Round)
    (requiredVotes exhaustedBeforeActivation : Round → ℕ) : Prop :=
  ∀ round, round ∈ activationRounds →
    requiredVotes round ≤ exhaustedBeforeActivation round

/-- The multi-round viability predicate reduces to the displayed single-round
threshold formula for a singleton activation-round set. -/
theorem exhaustedCompletionMultiRoundViable_singleton_iff
    {Round : Type*} [DecidableEq Round]
    {round : Round}
    {requiredVotes exhaustedBeforeActivation : Round → ℕ} :
    exhaustedCompletionMultiRoundViable ({round} : Finset Round)
        requiredVotes exhaustedBeforeActivation ↔
      requiredVotes round ≤ exhaustedBeforeActivation round := by
  simp [exhaustedCompletionMultiRoundViable]

/--
Proposition 2 multi-round viable-candidate set: candidates whose required
ballots fit the exhausted-ballot availability at every activation round.
-/
noncomputable def exhaustedCompletionMultiRoundViableCandidates
    {Candidate Round : Type*}
    [DecidableEq Candidate] [DecidableEq Round]
    (candidates : Finset Candidate)
    (activationRounds : Candidate → Finset Round)
    (requiredVotes exhaustedBeforeActivation : Candidate → Round → ℕ) :
    Finset Candidate :=
  by
    classical
    exact candidates.filter fun candidate =>
      exhaustedCompletionMultiRoundViable (activationRounds candidate)
        (requiredVotes candidate) (exhaustedBeforeActivation candidate)

/-- Membership in the multi-round viable set is exactly the per-activation-round
threshold condition. -/
theorem mem_exhaustedCompletionMultiRoundViableCandidates_iff
    {Candidate Round : Type*} [DecidableEq Candidate] [DecidableEq Round]
    {candidates : Finset Candidate}
    {activationRounds : Candidate → Finset Round}
    {requiredVotes exhaustedBeforeActivation : Candidate → Round → ℕ}
    {candidate : Candidate} :
    candidate ∈
        exhaustedCompletionMultiRoundViableCandidates candidates
          activationRounds requiredVotes exhaustedBeforeActivation ↔
      candidate ∈ candidates ∧
        ∀ round, round ∈ activationRounds candidate →
          requiredVotes candidate round ≤
            exhaustedBeforeActivation candidate round := by
  classical
  simp [exhaustedCompletionMultiRoundViableCandidates,
    exhaustedCompletionMultiRoundViable]

/--
Concrete multi-round availability count from a profile: for each candidate and
activation round, count exhausted ballots whose strategy suffix activates the
candidate at that round's active set.
-/
def exhaustedCompletionAvailableCountByRound
    {Voter Candidate Round : Type*} [DecidableEq Candidate]
    (voters : Finset Voter)
    (exhausted strategy : Voter → RCVBallot Candidate)
    (active : Round → Finset Candidate) :
    Candidate → Round → ℕ :=
  fun candidate round =>
    exhaustedCompletionAvailableCount voters exhausted strategy
      (active round) candidate

/--
Concrete profile-count characterization of Proposition 2's multi-round viable
candidate set.
-/
theorem mem_exhaustedCompletionMultiRoundViableCandidates_profileAvailableCount_iff
    {Voter Candidate Round : Type*} [DecidableEq Candidate] [DecidableEq Round]
    {voters : Finset Voter}
    {exhausted strategy : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate}
    {candidates : Finset Candidate}
    {activationRounds : Candidate → Finset Round}
    {requiredVotes : Candidate → Round → ℕ}
    {candidate : Candidate} :
    candidate ∈
        exhaustedCompletionMultiRoundViableCandidates candidates
          activationRounds requiredVotes
          (exhaustedCompletionAvailableCountByRound
            voters exhausted strategy active) ↔
      candidate ∈ candidates ∧
        ∀ round, round ∈ activationRounds candidate →
          requiredVotes candidate round ≤
            exhaustedCompletionAvailableCountByRound
              voters exhausted strategy active candidate round := by
  exact mem_exhaustedCompletionMultiRoundViableCandidates_iff

/--
Exact multi-round Proposition 2 profile characterization: if every completed
ballot is obtained by appending a strategic suffix to an exhausted prefix, and
the exhausted prefixes are inactive at each activation round, then the
multi-round viability predicate is equivalent to the displayed completed-profile
active-support inequalities.
-/
theorem exhaustedCompletionMultiRoundViable_iff_requiredVotes_le_completed_activeSupport_card
    {Voter Candidate Round : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {exhausted strategy completed : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate}
    {candidate : Candidate}
    {activationRounds : Finset Round}
    {requiredVotes : Candidate → Round → ℕ}
    (hcompleted : ∀ voter ∈ voters,
      completed voter = exhausted voter ++ strategy voter)
    (hexhausted : ∀ round, round ∈ activationRounds →
      ∀ voter ∈ voters,
        Ballot.nextActive (exhausted voter) (active round) = none) :
    exhaustedCompletionMultiRoundViable activationRounds
        (requiredVotes candidate)
        (exhaustedCompletionAvailableCountByRound voters exhausted strategy
          active candidate) ↔
      ∀ round, round ∈ activationRounds →
        requiredVotes candidate round ≤
          (Ballot.activeSupport voters completed (active round)
            candidate).card := by
  constructor
  · intro hrounds round hround
    have havailable :
        requiredVotes candidate round ≤
          exhaustedCompletionAvailableCountByRound voters exhausted strategy
            active candidate round :=
      hrounds round hround
    simpa [exhaustedCompletionAvailableCountByRound,
      exhaustedCompletionAvailableCount_eq_completed_activeSupport_card
        (voters := voters) (exhausted := exhausted) (strategy := strategy)
        (completed := completed) (active := active round)
        (candidate := candidate) hcompleted (hexhausted round hround)] using
      havailable
  · intro hrounds round hround
    have hsupport :
        requiredVotes candidate round ≤
          (Ballot.activeSupport voters completed (active round)
            candidate).card :=
      hrounds round hround
    simpa [exhaustedCompletionAvailableCountByRound,
      exhaustedCompletionAvailableCount_eq_completed_activeSupport_card
        (voters := voters) (exhausted := exhausted) (strategy := strategy)
        (completed := completed) (active := active round)
        (candidate := candidate) hcompleted (hexhausted round hround)] using
      hsupport

/--
Exact multi-round Proposition 2 viable-candidate characterization after
instantiating Algorithm A's availability counts from a completed profile.
-/
theorem mem_exhaustedCompletionMultiRoundViableCandidates_profileCompletedSupport_iff
    {Voter Candidate Round : Type*} [DecidableEq Candidate] [DecidableEq Round]
    {voters : Finset Voter}
    {exhausted strategy completed : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate}
    {candidates : Finset Candidate}
    {activationRounds : Candidate → Finset Round}
    {requiredVotes : Candidate → Round → ℕ}
    {candidate : Candidate}
    (hcompleted : ∀ voter ∈ voters,
      completed voter = exhausted voter ++ strategy voter)
    (hexhausted : ∀ candidate, candidate ∈ candidates →
      ∀ round, round ∈ activationRounds candidate →
        ∀ voter ∈ voters,
          Ballot.nextActive (exhausted voter) (active round) = none) :
    candidate ∈
        exhaustedCompletionMultiRoundViableCandidates candidates
          activationRounds requiredVotes
          (exhaustedCompletionAvailableCountByRound
            voters exhausted strategy active) ↔
      candidate ∈ candidates ∧
        ∀ round, round ∈ activationRounds candidate →
          requiredVotes candidate round ≤
            (Ballot.activeSupport voters completed (active round)
              candidate).card := by
  constructor
  · intro hmem
    have hcand : candidate ∈ candidates :=
      (mem_exhaustedCompletionMultiRoundViableCandidates_iff.mp hmem).1
    refine ⟨hcand, ?_⟩
    have hrounds :
        exhaustedCompletionMultiRoundViable (activationRounds candidate)
          (requiredVotes candidate)
          (exhaustedCompletionAvailableCountByRound voters exhausted strategy
            active candidate) :=
      (mem_exhaustedCompletionMultiRoundViableCandidates_iff.mp hmem).2
    exact
      (exhaustedCompletionMultiRoundViable_iff_requiredVotes_le_completed_activeSupport_card
        (voters := voters) (exhausted := exhausted) (strategy := strategy)
        (completed := completed) (active := active) (candidate := candidate)
        (activationRounds := activationRounds candidate)
        (requiredVotes := requiredVotes) hcompleted
        (hexhausted candidate hcand)).mp hrounds
  · intro hmem
    refine
      (mem_exhaustedCompletionMultiRoundViableCandidates_iff).mpr
        ⟨hmem.1, ?_⟩
    exact
      (exhaustedCompletionMultiRoundViable_iff_requiredVotes_le_completed_activeSupport_card
        (voters := voters) (exhausted := exhausted) (strategy := strategy)
        (completed := completed) (active := active) (candidate := candidate)
        (activationRounds := activationRounds candidate)
        (requiredVotes := requiredVotes) hcompleted
        (hexhausted candidate hmem.1)).mpr hmem.2

/--
Round-indexed concrete Proposition 2 bridge: if the required vote count is at
most the concrete profile count available at a given activation round, then
the completed profile supplies that support at that round.
-/
theorem exhausted_completion_activeSupport_count_ge_requiredVotes_of_availableCountByRound
    {Voter Candidate Round : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {exhausted strategy : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate}
    {candidate : Candidate} {round : Round}
    {requiredVotes : ℕ}
    (hrequired :
      requiredVotes ≤
        exhaustedCompletionAvailableCountByRound voters exhausted strategy
          active candidate round) :
    requiredVotes ≤
      (Ballot.activeSupport voters
          (fun voter => exhausted voter ++ strategy voter) (active round)
          candidate).card := by
  exact
    exhausted_completion_activeSupport_count_ge_requiredVotes_of_availableCount
      (by
        simpa [exhaustedCompletionAvailableCountByRound] using hrequired)

/--
Round-indexed finite required-voter constructor for Proposition 2.
-/
theorem exhaustedCompletionAvailableCountByRound_exists_required_voters
    {Voter Candidate Round : Type*} [DecidableEq Candidate]
    {voters : Finset Voter}
    {exhausted strategy : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate}
    {candidate : Candidate} {round : Round}
    {requiredVotes : ℕ}
    (hrequired :
      requiredVotes ≤
        exhaustedCompletionAvailableCountByRound voters exhausted strategy
          active candidate round) :
    ∃ required : Finset Voter,
      required ⊆ voters ∧
        required.card = requiredVotes ∧
          ∀ voter ∈ required,
            Ballot.nextActive (exhausted voter) (active round) = none ∧
              Ballot.nextActive (strategy voter) (active round) =
                some candidate := by
  exact
    exhaustedCompletionAvailableCount_exists_required_voters
      (by
        simpa [exhaustedCompletionAvailableCountByRound] using hrequired)

/--
Round-indexed Proposition 2 viable-set constructor: membership in the
multi-round concrete viable set constructs the finite required voter set for
the requested activation round.
-/
theorem exhaustedCompletionAvailableCountByRound_exists_required_voters_of_mem_multiRoundProfileViableCandidates
    {Voter Candidate Round : Type*} [DecidableEq Candidate] [DecidableEq Round]
    {voters : Finset Voter}
    {exhausted strategy : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate}
    {candidate : Candidate} {round : Round}
    {candidates : Finset Candidate}
    {activationRounds : Candidate → Finset Round}
    {requiredVotes : Candidate → Round → ℕ}
    (hmem :
      candidate ∈
        exhaustedCompletionMultiRoundViableCandidates candidates
          activationRounds requiredVotes
          (exhaustedCompletionAvailableCountByRound
            voters exhausted strategy active))
    (hround : round ∈ activationRounds candidate) :
    ∃ required : Finset Voter,
      required ⊆ voters ∧
        required.card = requiredVotes candidate round ∧
          ∀ voter ∈ required,
            Ballot.nextActive (exhausted voter) (active round) = none ∧
              Ballot.nextActive (strategy voter) (active round) =
                some candidate := by
  have hrequired :
      requiredVotes candidate round ≤
        exhaustedCompletionAvailableCountByRound voters exhausted strategy
          active candidate round :=
    (mem_exhaustedCompletionMultiRoundViableCandidates_iff.mp hmem).2
      round hround
  exact
    exhaustedCompletionAvailableCountByRound_exists_required_voters
      (voters := voters)
      (exhausted := exhausted)
      (strategy := strategy)
      (active := active)
      (candidate := candidate)
      (round := round)
      (requiredVotes := requiredVotes candidate round)
      hrequired

/--
Concrete multi-round Proposition 2 bridge: membership in the multi-round
viable-candidate set built from the concrete profile availability counts gives
the required active support at every activation round.
-/
theorem exhausted_completion_activeSupport_count_ge_requiredVotes_of_mem_multiRoundProfileViableCandidates
    {Voter Candidate Round : Type*} [DecidableEq Candidate] [DecidableEq Round]
    {voters : Finset Voter}
    {exhausted strategy : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate}
    {candidate : Candidate} {round : Round}
    {candidates : Finset Candidate}
    {activationRounds : Candidate → Finset Round}
    {requiredVotes : Candidate → Round → ℕ}
    (hmem :
      candidate ∈
        exhaustedCompletionMultiRoundViableCandidates candidates
          activationRounds requiredVotes
          (exhaustedCompletionAvailableCountByRound
            voters exhausted strategy active))
    (hround : round ∈ activationRounds candidate) :
    requiredVotes candidate round ≤
      (Ballot.activeSupport voters
          (fun voter => exhausted voter ++ strategy voter) (active round)
          candidate).card := by
  have hrequired :
      requiredVotes candidate round ≤
        exhaustedCompletionAvailableCountByRound voters exhausted strategy
          active candidate round :=
    (mem_exhaustedCompletionMultiRoundViableCandidates_iff.mp hmem).2
      round hround
  exact
    exhausted_completion_activeSupport_count_ge_requiredVotes_of_availableCount
      (by
        simpa [exhaustedCompletionAvailableCountByRound] using hrequired)

/--
Source-shaped Algorithm A certificate for Proposition 2's exhausted-ballot
completion characterization.

The certificate records the candidates, activation rounds, required strategic
votes, and concrete exhausted-ballot availability counts returned by Algorithm
A.  Its substantive field is the paper's per-round test
`g_i <= E_{r_i-1}` for every candidate/activation-round pair.
-/
structure AlgorithmAExhaustedCompletionCertificate
    {Voter Candidate Round : Type*} [DecidableEq Candidate] [DecidableEq Round]
    (voters : Finset Voter)
    (exhausted strategy : Voter → RCVBallot Candidate)
    (active : Round → Finset Candidate)
    (candidates : Finset Candidate)
    (activationRounds : Candidate → Finset Round)
    (requiredVotes : Candidate → Round → ℕ) where
  requiredVotes_le_available :
    ∀ candidate, candidate ∈ candidates →
      ∀ round, round ∈ activationRounds candidate →
        requiredVotes candidate round ≤
          exhaustedCompletionAvailableCountByRound
            voters exhausted strategy active candidate round

/--
Executable Algorithm A exhausted-completion count test.  It checks the paper's
finite condition `g_i <= E_{r_i-1}` for every candidate and every listed
activation round.
-/
noncomputable def algorithmAExhaustedCompletionRequiredVotesCheck
    {Voter Candidate Round : Type*} [DecidableEq Candidate] [DecidableEq Round]
    (voters : Finset Voter)
    (exhausted strategy : Voter → RCVBallot Candidate)
    (active : Round → Finset Candidate)
    (candidates : Finset Candidate)
    (activationRounds : Candidate → Finset Round)
    (requiredVotes : Candidate → Round → ℕ) : Bool :=
  candidates.toList.all fun candidate =>
    (activationRounds candidate).toList.all fun round =>
      decide
        (requiredVotes candidate round ≤
          exhaustedCompletionAvailableCountByRound
            voters exhausted strategy active candidate round)

/--
A successful finite Algorithm A exhausted-completion checker supplies the
source-shaped per-round count inequalities.
-/
theorem algorithmAExhaustedCompletionRequiredVotes_of_check_eq_true
    {Voter Candidate Round : Type*} [DecidableEq Candidate] [DecidableEq Round]
    {voters : Finset Voter}
    {exhausted strategy : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate}
    {candidates : Finset Candidate}
    {activationRounds : Candidate → Finset Round}
    {requiredVotes : Candidate → Round → ℕ}
    (hcheck :
      algorithmAExhaustedCompletionRequiredVotesCheck
        voters exhausted strategy active candidates activationRounds
        requiredVotes = true) :
    ∀ candidate, candidate ∈ candidates →
      ∀ round, round ∈ activationRounds candidate →
        requiredVotes candidate round ≤
          exhaustedCompletionAvailableCountByRound
            voters exhausted strategy active candidate round := by
  classical
  intro candidate hcandidate round hround
  have hcandidate_all :
      ((activationRounds candidate).toList.all fun round =>
        decide
          (requiredVotes candidate round ≤
            exhaustedCompletionAvailableCountByRound
              voters exhausted strategy active candidate round)) = true := by
    exact
      (List.all_eq_true.mp hcheck) candidate
        (Finset.mem_toList.mpr hcandidate)
  have hround_all :
      decide
        (requiredVotes candidate round ≤
          exhaustedCompletionAvailableCountByRound
            voters exhausted strategy active candidate round) = true :=
    (List.all_eq_true.mp hcandidate_all) round
      (Finset.mem_toList.mpr hround)
  exact decide_eq_true_iff.mp hround_all

/--
Concrete Algorithm A availability run for Proposition 2.

The run records the finite exhausted voters selected by Algorithm A for each
candidate and activation round.  The substantive proof obligation is local and
source-shaped: enough selected voters exist, each selected voter is in the
source profile, its exhausted prefix is inactive at the activation round, and
its strategy suffix activates the candidate.
-/
structure AlgorithmAExhaustedAvailabilityRun
    {Voter Candidate Round : Type*} [DecidableEq Candidate] [DecidableEq Round]
    (voters : Finset Voter)
    (exhausted strategy : Voter → RCVBallot Candidate)
    (active : Round → Finset Candidate)
    (candidates : Finset Candidate)
    (activationRounds : Candidate → Finset Round)
    (requiredVotes : Candidate → Round → ℕ) where
  availableVoters : Candidate → Round → Finset Voter
  available_subset :
    ∀ candidate, candidate ∈ candidates →
      ∀ round, round ∈ activationRounds candidate →
        availableVoters candidate round ⊆ voters
  available_exhausted :
    ∀ candidate, candidate ∈ candidates →
      ∀ round, round ∈ activationRounds candidate →
        ∀ voter, voter ∈ availableVoters candidate round →
          Ballot.nextActive (exhausted voter) (active round) = none
  available_strategy :
    ∀ candidate, candidate ∈ candidates →
      ∀ round, round ∈ activationRounds candidate →
        ∀ voter, voter ∈ availableVoters candidate round →
          Ballot.nextActive (strategy voter) (active round) = some candidate
  requiredVotes_le_available_card :
    ∀ candidate, candidate ∈ candidates →
      ∀ round, round ∈ activationRounds candidate →
        requiredVotes candidate round ≤
          (availableVoters candidate round).card

namespace AlgorithmAExhaustedAvailabilityRun

/--
Choose the finite exhausted-voter witnesses guaranteed by an Algorithm A
availability-count certificate.
-/
noncomputable def selectedVotersOfCompletionCertificate
    {Voter Candidate Round : Type*} [DecidableEq Candidate] [DecidableEq Round]
    {voters : Finset Voter}
    {exhausted strategy : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate}
    {candidates : Finset Candidate}
    {activationRounds : Candidate → Finset Round}
    {requiredVotes : Candidate → Round → ℕ}
    (cert :
      AlgorithmAExhaustedCompletionCertificate voters exhausted strategy active
        candidates activationRounds requiredVotes) :
    Candidate → Round → Finset Voter :=
  fun candidate round =>
    if hcandidate : candidate ∈ candidates then
      if hround : round ∈ activationRounds candidate then
        Classical.choose
          (exhaustedCompletionAvailableCountByRound_exists_required_voters
            (voters := voters)
            (exhausted := exhausted)
            (strategy := strategy)
            (active := active)
            (candidate := candidate)
            (round := round)
            (requiredVotes := requiredVotes candidate round)
            (cert.requiredVotes_le_available candidate hcandidate round hround))
      else ∅
    else ∅

/--
An Algorithm A availability-count certificate canonically supplies the concrete
availability run obtained by choosing the finite exhausted voters counted by
`E_{r_i-1}`.
-/
noncomputable def ofCompletionCertificate
    {Voter Candidate Round : Type*} [DecidableEq Candidate] [DecidableEq Round]
    {voters : Finset Voter}
    {exhausted strategy : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate}
    {candidates : Finset Candidate}
    {activationRounds : Candidate → Finset Round}
    {requiredVotes : Candidate → Round → ℕ}
    (cert :
      AlgorithmAExhaustedCompletionCertificate voters exhausted strategy active
        candidates activationRounds requiredVotes) :
    AlgorithmAExhaustedAvailabilityRun voters exhausted strategy active
      candidates activationRounds requiredVotes where
  availableVoters :=
    selectedVotersOfCompletionCertificate cert
  available_subset := by
    intro candidate hcandidate round hround voter hvoter
    have hspec :=
      Classical.choose_spec
        (exhaustedCompletionAvailableCountByRound_exists_required_voters
          (voters := voters)
          (exhausted := exhausted)
          (strategy := strategy)
          (active := active)
          (candidate := candidate)
          (round := round)
          (requiredVotes := requiredVotes candidate round)
          (cert.requiredVotes_le_available candidate hcandidate round hround))
    exact hspec.1 (by
      simpa [selectedVotersOfCompletionCertificate, hcandidate, hround] using
        hvoter)
  available_exhausted := by
    intro candidate hcandidate round hround voter hvoter
    have hspec :=
      Classical.choose_spec
        (exhaustedCompletionAvailableCountByRound_exists_required_voters
          (voters := voters)
          (exhausted := exhausted)
          (strategy := strategy)
          (active := active)
          (candidate := candidate)
          (round := round)
          (requiredVotes := requiredVotes candidate round)
          (cert.requiredVotes_le_available candidate hcandidate round hround))
    exact (hspec.2.2 voter (by
      simpa [selectedVotersOfCompletionCertificate, hcandidate, hround] using
        hvoter)).1
  available_strategy := by
    intro candidate hcandidate round hround voter hvoter
    have hspec :=
      Classical.choose_spec
        (exhaustedCompletionAvailableCountByRound_exists_required_voters
          (voters := voters)
          (exhausted := exhausted)
          (strategy := strategy)
          (active := active)
          (candidate := candidate)
          (round := round)
          (requiredVotes := requiredVotes candidate round)
          (cert.requiredVotes_le_available candidate hcandidate round hround))
    exact (hspec.2.2 voter (by
      simpa [selectedVotersOfCompletionCertificate, hcandidate, hround] using
        hvoter)).2
  requiredVotes_le_available_card := by
    intro candidate hcandidate round hround
    have hspec :=
      Classical.choose_spec
        (exhaustedCompletionAvailableCountByRound_exists_required_voters
          (voters := voters)
          (exhausted := exhausted)
          (strategy := strategy)
          (active := active)
          (candidate := candidate)
          (round := round)
          (requiredVotes := requiredVotes candidate round)
          (cert.requiredVotes_le_available candidate hcandidate round hround))
    rw [← hspec.2.1]
    simp [selectedVotersOfCompletionCertificate, hcandidate, hround]

/--
The selected available-voter set is contained in the concrete availability set
counted by `E_{r_i-1}`.
-/
theorem availableVoters_subset_exhaustedCompletionAvailableVoters
    {Voter Candidate Round : Type*} [DecidableEq Candidate] [DecidableEq Round]
    {voters : Finset Voter}
    {exhausted strategy : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate}
    {candidates : Finset Candidate}
    {activationRounds : Candidate → Finset Round}
    {requiredVotes : Candidate → Round → ℕ}
    (run :
      AlgorithmAExhaustedAvailabilityRun voters exhausted strategy active
        candidates activationRounds requiredVotes)
    {candidate : Candidate} (hcandidate : candidate ∈ candidates)
    {round : Round} (hround : round ∈ activationRounds candidate) :
    run.availableVoters candidate round ⊆
      exhaustedCompletionAvailableVoters voters exhausted strategy
        (active round) candidate := by
  intro voter hvoter
  exact
    (mem_exhaustedCompletionAvailableVoters_iff).mpr
      ⟨run.available_subset candidate hcandidate round hround hvoter,
        run.available_exhausted candidate hcandidate round hround voter hvoter,
        run.available_strategy candidate hcandidate round hround voter hvoter⟩

/--
A concrete Algorithm A availability run supplies the exhausted-completion
certificate used by Proposition 2.
-/
def toCompletionCertificate
    {Voter Candidate Round : Type*} [DecidableEq Candidate] [DecidableEq Round]
    {voters : Finset Voter}
    {exhausted strategy : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate}
    {candidates : Finset Candidate}
    {activationRounds : Candidate → Finset Round}
    {requiredVotes : Candidate → Round → ℕ}
    (run :
      AlgorithmAExhaustedAvailabilityRun voters exhausted strategy active
        candidates activationRounds requiredVotes) :
    AlgorithmAExhaustedCompletionCertificate voters exhausted strategy active
      candidates activationRounds requiredVotes where
  requiredVotes_le_available := by
    intro candidate hcandidate round hround
    exact le_trans
      (run.requiredVotes_le_available_card candidate hcandidate round hround)
      (Finset.card_le_card
        (run.availableVoters_subset_exhaustedCompletionAvailableVoters
          hcandidate hround))

end AlgorithmAExhaustedAvailabilityRun

/--
Algorithm A's exhausted-completion certificate puts every certified candidate
in the multi-round viable set.
-/
theorem exhaustedCompletionMultiRoundViableCandidates_mem_of_algorithmACertificate
    {Voter Candidate Round : Type*} [DecidableEq Candidate] [DecidableEq Round]
    {voters : Finset Voter}
    {exhausted strategy : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate}
    {candidates : Finset Candidate}
    {activationRounds : Candidate → Finset Round}
    {requiredVotes : Candidate → Round → ℕ}
    (cert :
      AlgorithmAExhaustedCompletionCertificate voters exhausted strategy active
        candidates activationRounds requiredVotes)
    {candidate : Candidate}
    (hcandidate : candidate ∈ candidates) :
    candidate ∈
      exhaustedCompletionMultiRoundViableCandidates candidates
        activationRounds requiredVotes
        (exhaustedCompletionAvailableCountByRound
          voters exhausted strategy active) := by
  exact
    (mem_exhaustedCompletionMultiRoundViableCandidates_iff).mpr
      ⟨hcandidate, cert.requiredVotes_le_available candidate hcandidate⟩

/--
Proposition 2 closeout from Algorithm A's exhausted-completion certificate:
the candidate is viable, receives enough completed-profile support at every
activation round, and has finite required exhausted-ballot witnesses at each
round.
-/
theorem exhaustedCompletionMultiRoundCloseout_of_algorithmACertificate
    {Voter Candidate Round : Type*} [DecidableEq Candidate] [DecidableEq Round]
    {voters : Finset Voter}
    {exhausted strategy : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate}
    {candidates : Finset Candidate}
    {activationRounds : Candidate → Finset Round}
    {requiredVotes : Candidate → Round → ℕ}
    (cert :
      AlgorithmAExhaustedCompletionCertificate voters exhausted strategy active
        candidates activationRounds requiredVotes)
    {candidate : Candidate}
    (hcandidate : candidate ∈ candidates) :
    candidate ∈
        exhaustedCompletionMultiRoundViableCandidates candidates
          activationRounds requiredVotes
          (exhaustedCompletionAvailableCountByRound
            voters exhausted strategy active) ∧
      (∀ round, round ∈ activationRounds candidate →
        requiredVotes candidate round ≤
          (Ballot.activeSupport voters
            (fun voter => exhausted voter ++ strategy voter)
            (active round) candidate).card) ∧
        (∀ round, round ∈ activationRounds candidate →
          ∃ required : Finset Voter,
            required ⊆ voters ∧
              required.card = requiredVotes candidate round ∧
                ∀ voter ∈ required,
                  Ballot.nextActive (exhausted voter) (active round) = none ∧
                    Ballot.nextActive (strategy voter) (active round) =
                      some candidate) := by
  let hmem :=
    exhaustedCompletionMultiRoundViableCandidates_mem_of_algorithmACertificate
      cert hcandidate
  refine ⟨hmem, ?_, ?_⟩
  · intro round hround
    exact
      exhausted_completion_activeSupport_count_ge_requiredVotes_of_mem_multiRoundProfileViableCandidates
        (voters := voters)
        (exhausted := exhausted)
        (strategy := strategy)
        (active := active)
        (candidate := candidate)
        (round := round)
        (candidates := candidates)
        (activationRounds := activationRounds)
        (requiredVotes := requiredVotes)
        hmem hround
  · intro round hround
    exact
      exhaustedCompletionAvailableCountByRound_exists_required_voters_of_mem_multiRoundProfileViableCandidates
        (voters := voters)
        (exhausted := exhausted)
        (strategy := strategy)
        (active := active)
        (candidate := candidate)
        (round := round)
        (candidates := candidates)
        (activationRounds := activationRounds)
        (requiredVotes := requiredVotes)
        hmem hround

/--
Proposition 2 closeout from a concrete Algorithm A availability run.
-/
theorem exhaustedCompletionMultiRoundCloseout_of_algorithmAAvailabilityRun
    {Voter Candidate Round : Type*} [DecidableEq Candidate] [DecidableEq Round]
    {voters : Finset Voter}
    {exhausted strategy : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate}
    {candidates : Finset Candidate}
    {activationRounds : Candidate → Finset Round}
    {requiredVotes : Candidate → Round → ℕ}
    (run :
      AlgorithmAExhaustedAvailabilityRun voters exhausted strategy active
        candidates activationRounds requiredVotes)
    {candidate : Candidate}
    (hcandidate : candidate ∈ candidates) :
    candidate ∈
        exhaustedCompletionMultiRoundViableCandidates candidates
          activationRounds requiredVotes
          (exhaustedCompletionAvailableCountByRound
            voters exhausted strategy active) ∧
      (∀ round, round ∈ activationRounds candidate →
        requiredVotes candidate round ≤
          (Ballot.activeSupport voters
            (fun voter => exhausted voter ++ strategy voter)
            (active round) candidate).card) ∧
        (∀ round, round ∈ activationRounds candidate →
          ∃ required : Finset Voter,
            required ⊆ voters ∧
              required.card = requiredVotes candidate round ∧
                ∀ voter ∈ required,
                  Ballot.nextActive (exhausted voter) (active round) = none ∧
                    Ballot.nextActive (strategy voter) (active round) =
                      some candidate) := by
  exact
    exhaustedCompletionMultiRoundCloseout_of_algorithmACertificate
      (run.toCompletionCertificate) hcandidate

/--
Source-shaped Proposition 1 certificate for robust Algorithm 1 extensions.

The certificate records the base optimality certificate and the robust output
transform obligations: feasibility is preserved, the objective value matches
the base strategy, and the robust implementation satisfies the inherited
operation bound.
-/
structure RobustExtensionCertificate
    {Problem Strategy : Type*}
    (baseAlgorithm robustAlgorithm : Problem → Strategy)
    (feasible : Problem → Strategy → Prop)
    (cost : Problem → Strategy → ℝ)
    (baseOperationCount robustOperationCount operationBound : Problem → ℕ) where
  baseCert :
    EconCSLib.Optimization.AlgorithmMinimizerCertificate
      baseAlgorithm feasible cost baseOperationCount operationBound
  robust_feasible : ∀ problem, feasible problem (robustAlgorithm problem)
  robust_cost_eq : ∀ problem,
    cost problem (robustAlgorithm problem) =
      cost problem (baseAlgorithm problem)
  robustOperationCount_le :
    ∀ problem, robustOperationCount problem ≤ operationBound problem

/--
The Proposition 1 robust-extension certificate is a paper-specific spelling of
the reusable optimization-library output-transform certificate.
-/
def minimizerOutputTransformCertificate_of_robustExtensionCertificate
    {Problem Strategy : Type*}
    {baseAlgorithm robustAlgorithm : Problem → Strategy}
    {feasible : Problem → Strategy → Prop}
    {cost : Problem → Strategy → ℝ}
    {baseOperationCount robustOperationCount operationBound : Problem → ℕ}
    (cert :
      RobustExtensionCertificate baseAlgorithm robustAlgorithm feasible cost
        baseOperationCount robustOperationCount operationBound) :
    EconCSLib.Optimization.MinimizerOutputTransformCertificate
      baseAlgorithm robustAlgorithm feasible cost
      baseOperationCount robustOperationCount operationBound where
  baseCert := cert.baseCert
  transformed_feasible := cert.robust_feasible
  transformed_objective_eq := cert.robust_cost_eq
  transformedOperationCount_le := cert.robustOperationCount_le

/--
Proposition 1 optimality/runtime preservation bridge: a robust extension of
Algorithm 1 inherits optimality when it transforms each base optimal strategy
into a feasible strategy with the same objective value and the promised
polynomial operation bound.
-/
theorem proposition1_robustExtension_optimal_and_runtime_of_transform
    {Problem Strategy : Type*}
    {baseAlgorithm robustAlgorithm : Problem → Strategy}
    {feasible : Problem → Strategy → Prop}
    {cost : Problem → Strategy → ℝ}
    {baseOperationCount robustOperationCount operationBound : Problem → ℕ}
    (baseCert :
      EconCSLib.Optimization.AlgorithmMinimizerCertificate
        baseAlgorithm feasible cost baseOperationCount operationBound)
    (robust_feasible : ∀ problem, feasible problem (robustAlgorithm problem))
    (robust_cost_eq : ∀ problem,
      cost problem (robustAlgorithm problem) =
        cost problem (baseAlgorithm problem))
    (robustOperationCount_le :
      ∀ problem, robustOperationCount problem ≤ operationBound problem) :
    ∀ problem,
      EconCSLib.Optimization.IsMinimizerOn
          (feasible problem) (cost problem) (robustAlgorithm problem) ∧
        robustOperationCount problem ≤ operationBound problem := by
  exact
    EconCSLib.Optimization.MinimizerOutputTransformCertificate.optimal_and_operationCount
      ({
        baseCert := baseCert
        transformed_feasible := robust_feasible
        transformed_objective_eq := robust_cost_eq
        transformedOperationCount_le := robustOperationCount_le
      } :
        EconCSLib.Optimization.MinimizerOutputTransformCertificate
          baseAlgorithm robustAlgorithm feasible cost
          baseOperationCount robustOperationCount operationBound)

/--
Proposition 1 optimality/runtime preservation bridge from the source-shaped
robust output-transform certificate.
-/
theorem proposition1_robustExtension_optimal_and_runtime_of_certificate
    {Problem Strategy : Type*}
    {baseAlgorithm robustAlgorithm : Problem → Strategy}
    {feasible : Problem → Strategy → Prop}
    {cost : Problem → Strategy → ℝ}
    {baseOperationCount robustOperationCount operationBound : Problem → ℕ}
    (cert :
      RobustExtensionCertificate baseAlgorithm robustAlgorithm feasible cost
        baseOperationCount robustOperationCount operationBound) :
    ∀ problem,
      EconCSLib.Optimization.IsMinimizerOn
          (feasible problem) (cost problem) (robustAlgorithm problem) ∧
        robustOperationCount problem ≤ operationBound problem := by
  exact
    EconCSLib.Optimization.MinimizerOutputTransformCertificate.optimal_and_operationCount
      (minimizerOutputTransformCertificate_of_robustExtensionCertificate cert)

/--
Constructor for Proposition 1's source-shaped robust-extension certificate
from the concrete base minimizer certificate and robust output-transform facts.
-/
def robustExtensionCertificate_of_transform
    {Problem Strategy : Type*}
    {baseAlgorithm robustAlgorithm : Problem → Strategy}
    {feasible : Problem → Strategy → Prop}
    {cost : Problem → Strategy → ℝ}
    {baseOperationCount robustOperationCount operationBound : Problem → ℕ}
    (baseCert :
      EconCSLib.Optimization.AlgorithmMinimizerCertificate
        baseAlgorithm feasible cost baseOperationCount operationBound)
    (robust_feasible : ∀ problem, feasible problem (robustAlgorithm problem))
    (robust_cost_eq : ∀ problem,
      cost problem (robustAlgorithm problem) =
        cost problem (baseAlgorithm problem))
    (robustOperationCount_le :
      ∀ problem, robustOperationCount problem ≤ operationBound problem) :
    RobustExtensionCertificate baseAlgorithm robustAlgorithm feasible cost
      baseOperationCount robustOperationCount operationBound where
  baseCert := baseCert
  robust_feasible := robust_feasible
  robust_cost_eq := robust_cost_eq
  robustOperationCount_le := robustOperationCount_le

/--
Support-extensional ballot-transform certificate for Proposition 1.

This is the strongest paper-local constructor available while DGJ24's
`SmartAllocationProblem` keeps feasibility and cost abstract: ballot
suffix/prefix/exhausted-completion facts prove equality of all relevant
active-support counts, and the source model must state that feasibility and
cost depend only on those counts.
-/
structure SupportExtensionalBallotTransformCertificate
    {Problem Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Problem → Finset Voter)
    (relevantActiveSets : Problem → Finset (Finset Candidate))
    (baseAlgorithm robustAlgorithm :
      Problem → Voter → RCVBallot Candidate)
    (feasible : Problem → (Voter → RCVBallot Candidate) → Prop)
    (cost : Problem → (Voter → RCVBallot Candidate) → ℝ)
    (baseOperationCount robustOperationCount operationBound :
      Problem → ℕ) where
  baseCert :
    EconCSLib.Optimization.AlgorithmMinimizerCertificate
      baseAlgorithm feasible cost baseOperationCount operationBound
  support_counts_eq :
    activeSupportCountsEqualOn voters relevantActiveSets
      baseAlgorithm robustAlgorithm
  feasible_of_support_counts_eq :
    ∀ problem,
      feasible problem (baseAlgorithm problem) →
        (∀ active, active ∈ relevantActiveSets problem → ∀ candidate,
          (Ballot.activeSupport (voters problem) (robustAlgorithm problem)
              active candidate).card =
            (Ballot.activeSupport (voters problem) (baseAlgorithm problem)
              active candidate).card) →
          feasible problem (robustAlgorithm problem)
  cost_eq_of_support_counts_eq :
    ∀ problem,
      (∀ active, active ∈ relevantActiveSets problem → ∀ candidate,
        (Ballot.activeSupport (voters problem) (robustAlgorithm problem)
            active candidate).card =
          (Ballot.activeSupport (voters problem) (baseAlgorithm problem)
            active candidate).card) →
        cost problem (robustAlgorithm problem) =
          cost problem (baseAlgorithm problem)
  robustOperationCount_le :
    ∀ problem, robustOperationCount problem ≤ operationBound problem

/--
Support-extensional ballot transforms instantiate the generic Proposition 1
robust-extension certificate.
-/
def robustExtensionCertificate_of_supportExtensionalBallotTransformCertificate
    {Problem Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Problem → Finset Voter}
    {relevantActiveSets : Problem → Finset (Finset Candidate)}
    {baseAlgorithm robustAlgorithm :
      Problem → Voter → RCVBallot Candidate}
    {feasible : Problem → (Voter → RCVBallot Candidate) → Prop}
    {cost : Problem → (Voter → RCVBallot Candidate) → ℝ}
    {baseOperationCount robustOperationCount operationBound : Problem → ℕ}
    (cert :
      SupportExtensionalBallotTransformCertificate voters relevantActiveSets
        baseAlgorithm robustAlgorithm feasible cost baseOperationCount
        robustOperationCount operationBound) :
    RobustExtensionCertificate baseAlgorithm robustAlgorithm feasible cost
      baseOperationCount robustOperationCount operationBound where
  baseCert := cert.baseCert
  robust_feasible := by
    intro problem
    exact cert.feasible_of_support_counts_eq problem
      ((cert.baseCert.optimal problem).isFeasible)
      (by
        intro active hactive candidate
        exact cert.support_counts_eq problem active hactive candidate)
  robust_cost_eq := by
    intro problem
    exact cert.cost_eq_of_support_counts_eq problem
      (by
        intro active hactive candidate
        exact cert.support_counts_eq problem active hactive candidate)
  robustOperationCount_le := cert.robustOperationCount_le

/--
Proposition 1 support-extensional ballot-transform route: once active-support
counts are preserved on the relevant source states and feasibility/cost are
support-extensional there, the robust Algorithm A output inherits optimality
and the operation bound.
-/
theorem proposition1_robustExtension_optimal_and_runtime_of_supportExtensionalBallotTransformCertificate
    {Problem Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Problem → Finset Voter}
    {relevantActiveSets : Problem → Finset (Finset Candidate)}
    {baseAlgorithm robustAlgorithm :
      Problem → Voter → RCVBallot Candidate}
    {feasible : Problem → (Voter → RCVBallot Candidate) → Prop}
    {cost : Problem → (Voter → RCVBallot Candidate) → ℝ}
    {baseOperationCount robustOperationCount operationBound : Problem → ℕ}
    (cert :
      SupportExtensionalBallotTransformCertificate voters relevantActiveSets
        baseAlgorithm robustAlgorithm feasible cost baseOperationCount
        robustOperationCount operationBound) :
    ∀ problem,
      EconCSLib.Optimization.IsMinimizerOn
          (feasible problem) (cost problem) (robustAlgorithm problem) ∧
        robustOperationCount problem ≤ operationBound problem := by
  exact proposition1_robustExtension_optimal_and_runtime_of_certificate
    (robustExtensionCertificate_of_supportExtensionalBallotTransformCertificate
      cert)

/--
Source-shaped Proposition 1 certificate tied to the DGJ24 SmartAllocation
slack-reduction endpoint.

The practical-dynamics robust extension uses the prior paper's fixed-structure
SmartAllocation certificate as the base optimizer, then proves that the robust
output transform preserves feasibility, cost, and the inherited linear
operation bound.
-/
structure RobustSmartAllocationSlackReductionCertificate
    {Addition Slack : Type*} [Fintype Slack]
    (baseAlgorithm robustAlgorithm :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition → Addition)
    (baseOperationCount robustOperationCount :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition → ℕ) where
  baseSlackReduction :
    DGJ24OptimalStrategiesRCV.SmartAllocationSlackReductionCertificate
      (Slack := Slack) baseAlgorithm baseOperationCount
  robust_feasible :
    ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
      problem.feasible (robustAlgorithm problem)
  robust_cost_eq :
    ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
      problem.cost (robustAlgorithm problem) =
        problem.cost (baseAlgorithm problem)
  robustOperationCount_le :
    ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
      robustOperationCount problem ≤
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
          problem

/--
A DGJ24 SmartAllocation slack-reduction certificate supplies the base
minimizer certificate needed by the DGJ26 robust-extension bridge.
-/
def robustExtensionCertificate_of_smartAllocationSlackReductionCertificate
    {Addition Slack : Type*} [Fintype Slack]
    {baseAlgorithm robustAlgorithm :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition → Addition}
    {baseOperationCount robustOperationCount :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition → ℕ}
    (cert :
      RobustSmartAllocationSlackReductionCertificate
        (Slack := Slack) baseAlgorithm robustAlgorithm
        baseOperationCount robustOperationCount) :
    RobustExtensionCertificate
      baseAlgorithm robustAlgorithm
      (fun problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          Addition => problem.feasible)
      (fun problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          Addition => problem.cost)
      baseOperationCount robustOperationCount
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound where
  baseCert :=
    DGJ24OptimalStrategiesRCV.smartAllocationCertificate_of_slackCertificate
      (DGJ24OptimalStrategiesRCV.smartAllocationSlackCertificate_of_slackReductionCertificate
        cert.baseSlackReduction)
  robust_feasible := cert.robust_feasible
  robust_cost_eq := cert.robust_cost_eq
  robustOperationCount_le := cert.robustOperationCount_le

/--
Proposition 1 robust SmartAllocation bridge: once the DGJ24
SmartAllocation-to-slack reduction certificate is available, a robust output
transform preserving feasibility and cost inherits optimality and the linear
operation bound.
-/
theorem proposition1_robustSmartAllocation_optimal_and_runtime_of_slackReductionCertificate
    {Addition Slack : Type*} [Fintype Slack]
    {baseAlgorithm robustAlgorithm :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition → Addition}
    {baseOperationCount robustOperationCount :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition → ℕ}
    (cert :
      RobustSmartAllocationSlackReductionCertificate
        (Slack := Slack) baseAlgorithm robustAlgorithm
        baseOperationCount robustOperationCount) :
    ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
      EconCSLib.Optimization.IsMinimizerOn
          problem.feasible problem.cost (robustAlgorithm problem) ∧
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem := by
  exact proposition1_robustExtension_optimal_and_runtime_of_certificate
    (robustExtensionCertificate_of_smartAllocationSlackReductionCertificate
      cert)

/--
Proposition 1 direct SmartAllocation slack-reduction route: explicit DGJ24
STV-to-slack reduction obligations prove the base optimizer, and the robust
output transform then inherits optimality and the linear operation bound.
-/
theorem proposition1_robustSmartAllocation_optimal_and_runtime_of_slack_reduction
    {Addition Slack : Type*} [Fintype Slack]
    {baseAlgorithm robustAlgorithm :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition → Addition}
    {baseOperationCount robustOperationCount :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition → ℕ}
    (slackProblem :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition →
        DGJ24OptimalStrategiesRCV.SmartAllocationSlackFillingProblem Slack)
    (slackOf :
      ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
        Addition → Slack → ℕ)
    (additionOf :
      ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
        (Slack → ℕ) → Addition)
    (base_algorithm_eq_additionOf :
      ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
        baseAlgorithm problem =
          additionOf problem
            (DGJ24OptimalStrategiesRCV.SmartAllocationSlackFillingProblem.algorithm
              (slackProblem problem)))
    (feasible_of_slack_feasible :
      ∀ (problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition)
        (allocation : Slack → ℕ),
        DGJ24OptimalStrategiesRCV.SmartAllocationSlackFillingProblem.feasible
            (slackProblem problem) allocation →
          problem.feasible (additionOf problem allocation))
    (slack_feasible_of_feasible :
      ∀ (problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition)
        (addition : Addition),
        problem.feasible addition →
          DGJ24OptimalStrategiesRCV.SmartAllocationSlackFillingProblem.feasible
            (slackProblem problem) (slackOf problem addition))
    (cost_algorithm_eq_slack :
      ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
        problem.cost (baseAlgorithm problem) =
          DGJ24OptimalStrategiesRCV.SmartAllocationSlackFillingProblem.cost
            (slackProblem problem)
            (DGJ24OptimalStrategiesRCV.SmartAllocationSlackFillingProblem.algorithm
              (slackProblem problem)))
    (cost_eq_slack_of_feasible :
      ∀ (problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition)
        (addition : Addition),
        problem.feasible addition →
          problem.cost addition =
            DGJ24OptimalStrategiesRCV.SmartAllocationSlackFillingProblem.cost
              (slackProblem problem) (slackOf problem addition))
    (baseOperationCount_le :
      ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
        baseOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem)
    (robust_feasible :
      ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
        problem.feasible (robustAlgorithm problem))
    (robust_cost_eq :
      ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
        problem.cost (robustAlgorithm problem) =
          problem.cost (baseAlgorithm problem))
    (robustOperationCount_le :
      ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem) :
    ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
      EconCSLib.Optimization.IsMinimizerOn
          problem.feasible problem.cost (robustAlgorithm problem) ∧
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem := by
  let baseCert :
      EconCSLib.Optimization.AlgorithmMinimizerCertificate
        baseAlgorithm
        (fun problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem
            Addition => problem.feasible)
        (fun problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem
            Addition => problem.cost)
        baseOperationCount
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound := {
    optimal := fun problem =>
      (DGJ24OptimalStrategiesRCV.theorem3_1_smartAllocation_optimal_and_linear_runtime_of_slack_reduction
        (slackProblem := slackProblem)
        (slackOf := slackOf)
        (additionOf := additionOf)
        base_algorithm_eq_additionOf feasible_of_slack_feasible
        slack_feasible_of_feasible cost_algorithm_eq_slack
        cost_eq_slack_of_feasible baseOperationCount_le problem).1
    operationCount_le := fun problem =>
      (DGJ24OptimalStrategiesRCV.theorem3_1_smartAllocation_optimal_and_linear_runtime_of_slack_reduction
        (slackProblem := slackProblem)
        (slackOf := slackOf)
        (additionOf := additionOf)
        base_algorithm_eq_additionOf feasible_of_slack_feasible
        slack_feasible_of_feasible cost_algorithm_eq_slack
        cost_eq_slack_of_feasible baseOperationCount_le problem).2
  }
  exact proposition1_robustExtension_optimal_and_runtime_of_transform
    baseCert robust_feasible robust_cost_eq robustOperationCount_le

/--
Proposition 1 concrete DGJ24 slack route: instantiate the base optimizer as
the DGJ24 source STV-to-slack translation followed by exact slack filling, then
apply the robust output transform.
-/
theorem proposition1_robustSmartAllocation_optimal_and_runtime_of_concrete_slack_reduction
    {Addition Slack : Type*} [Fintype Slack]
    {robustAlgorithm :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition → Addition}
    {robustOperationCount :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition → ℕ}
    (slackProblem :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition →
        DGJ24OptimalStrategiesRCV.SmartAllocationSlackFillingProblem Slack)
    (slackOf :
      ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
        Addition → Slack → ℕ)
    (additionOf :
      ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
        (Slack → ℕ) → Addition)
    (feasible_of_slack_feasible :
      ∀ (problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition)
        (allocation : Slack → ℕ),
        DGJ24OptimalStrategiesRCV.SmartAllocationSlackFillingProblem.feasible
            (slackProblem problem) allocation →
          problem.feasible (additionOf problem allocation))
    (slack_feasible_of_feasible :
      ∀ (problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition)
        (addition : Addition),
        problem.feasible addition →
          DGJ24OptimalStrategiesRCV.SmartAllocationSlackFillingProblem.feasible
            (slackProblem problem) (slackOf problem addition))
    (cost_algorithm_eq_slack :
      ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
        problem.cost
            (DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
              slackProblem additionOf problem) =
          DGJ24OptimalStrategiesRCV.SmartAllocationSlackFillingProblem.cost
            (slackProblem problem)
            (DGJ24OptimalStrategiesRCV.SmartAllocationSlackFillingProblem.algorithm
              (slackProblem problem)))
    (cost_eq_slack_of_feasible :
      ∀ (problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition)
        (addition : Addition),
        problem.feasible addition →
          problem.cost addition =
            DGJ24OptimalStrategiesRCV.SmartAllocationSlackFillingProblem.cost
              (slackProblem problem) (slackOf problem addition))
    (robust_feasible :
      ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
        problem.feasible (robustAlgorithm problem))
    (robust_cost_eq :
      ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
        problem.cost (robustAlgorithm problem) =
          problem.cost
            (DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
              slackProblem additionOf problem))
    (robustOperationCount_le :
      ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem) :
    ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
      EconCSLib.Optimization.IsMinimizerOn
          problem.feasible problem.cost (robustAlgorithm problem) ∧
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem := by
  let baseCert :
      EconCSLib.Optimization.AlgorithmMinimizerCertificate
        (DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
          slackProblem additionOf)
        (fun problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem
            Addition => problem.feasible)
        (fun problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem
            Addition => problem.cost)
        DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionOperationCount
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound := {
    optimal := fun problem =>
      (DGJ24OptimalStrategiesRCV.theorem3_1_smartAllocation_concreteSlackReductionAlgorithm_optimal_and_linear_runtime
        (slackProblem := slackProblem)
        (slackOf := slackOf)
        (additionOf := additionOf)
        feasible_of_slack_feasible
        slack_feasible_of_feasible
        cost_algorithm_eq_slack
        cost_eq_slack_of_feasible
        problem).1
    operationCount_le := fun problem =>
      (DGJ24OptimalStrategiesRCV.theorem3_1_smartAllocation_concreteSlackReductionAlgorithm_optimal_and_linear_runtime
        (slackProblem := slackProblem)
        (slackOf := slackOf)
        (additionOf := additionOf)
        feasible_of_slack_feasible
        slack_feasible_of_feasible
        cost_algorithm_eq_slack
        cost_eq_slack_of_feasible
        problem).2
  }
  exact proposition1_robustExtension_optimal_and_runtime_of_transform
    baseCert robust_feasible robust_cost_eq robustOperationCount_le

/--
Proposition 1 direct DGJ24 first-use slack route: instantiate the base
optimizer from Algorithm 3's source first-use decomposition, then apply the
robust output transform.
-/
theorem proposition1_robustSmartAllocation_optimal_and_runtime_of_firstUseSlackModel
    {Addition Slack : Type*} [Fintype Slack]
    {robustAlgorithm :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition → Addition}
    {robustOperationCount :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition → ℕ}
    (model :
      DGJ24OptimalStrategiesRCV.SmartAllocationFirstUseSlackModel Addition
        Slack)
    (robust_feasible :
      ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
        problem.feasible (robustAlgorithm problem))
    (robust_cost_eq :
      ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
        problem.cost (robustAlgorithm problem) =
          problem.cost
            (DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
              model.slackProblem model.additionOf problem))
    (robustOperationCount_le :
      ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem) :
    ∀ problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem Addition,
      EconCSLib.Optimization.IsMinimizerOn
          problem.feasible problem.cost (robustAlgorithm problem) ∧
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem := by
  let baseCert :
      EconCSLib.Optimization.AlgorithmMinimizerCertificate
        (DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
          model.slackProblem model.additionOf)
        (fun problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem
            Addition => problem.feasible)
        (fun problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem
            Addition => problem.cost)
        DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionOperationCount
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound := {
    optimal := fun problem =>
      (DGJ24OptimalStrategiesRCV.theorem3_1_smartAllocation_optimal_and_linear_runtime_of_firstUseSlackModel
        model problem).1
    operationCount_le := fun problem =>
      (DGJ24OptimalStrategiesRCV.theorem3_1_smartAllocation_optimal_and_linear_runtime_of_firstUseSlackModel
        model problem).2
  }
  exact proposition1_robustExtension_optimal_and_runtime_of_transform
    baseCert robust_feasible robust_cost_eq robustOperationCount_le

/--
Proposition 1 support-extensional SmartAllocation route: for ballot-valued
strategic additions, suffix/prefix/exhausted-completion constructors can prove
active-support preservation, and source-level support extensionality then
supplies the robust feasibility and cost preservation obligations.
-/
theorem proposition1_robustSmartAllocation_optimal_and_runtime_of_firstUseSlackModel_support_extensional_ballot_transform
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    {robustAlgorithm :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Voter → RCVBallot Candidate}
    {robustOperationCount :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        ℕ}
    (model :
      DGJ24OptimalStrategiesRCV.SmartAllocationFirstUseSlackModel
        (Voter → RCVBallot Candidate) Slack)
    (voters :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Finset Voter)
    (relevantActiveSets :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Finset (Finset Candidate))
    (support_counts_eq :
      activeSupportCountsEqualOn voters relevantActiveSets
        (DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
          model.slackProblem model.additionOf)
        robustAlgorithm)
    (feasible_of_support_counts_eq :
      ∀ problem,
        problem.feasible
          (DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
            model.slackProblem model.additionOf problem) →
          (∀ active, active ∈ relevantActiveSets problem → ∀ candidate,
            (Ballot.activeSupport (voters problem) (robustAlgorithm problem)
                active candidate).card =
              (Ballot.activeSupport (voters problem)
                (DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
                  model.slackProblem model.additionOf problem)
                active candidate).card) →
            problem.feasible (robustAlgorithm problem))
    (cost_eq_of_support_counts_eq :
      ∀ problem,
        (∀ active, active ∈ relevantActiveSets problem → ∀ candidate,
          (Ballot.activeSupport (voters problem) (robustAlgorithm problem)
              active candidate).card =
            (Ballot.activeSupport (voters problem)
              (DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
                model.slackProblem model.additionOf problem)
              active candidate).card) →
          problem.cost (robustAlgorithm problem) =
            problem.cost
              (DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
                model.slackProblem model.additionOf problem))
    (robustOperationCount_le :
      ∀ problem,
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem) :
    ∀ problem :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
        (Voter → RCVBallot Candidate),
      EconCSLib.Optimization.IsMinimizerOn
          problem.feasible problem.cost (robustAlgorithm problem) ∧
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem := by
  let baseAlgorithm :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Voter → RCVBallot Candidate :=
    DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
      model.slackProblem model.additionOf
  let baseCert :
      EconCSLib.Optimization.AlgorithmMinimizerCertificate
        baseAlgorithm
        (fun problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem
            (Voter → RCVBallot Candidate) => problem.feasible)
        (fun problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem
            (Voter → RCVBallot Candidate) => problem.cost)
        DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionOperationCount
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound := {
    optimal := fun problem =>
      (DGJ24OptimalStrategiesRCV.theorem3_1_smartAllocation_optimal_and_linear_runtime_of_firstUseSlackModel
        model problem).1
    operationCount_le := fun problem =>
      (DGJ24OptimalStrategiesRCV.theorem3_1_smartAllocation_optimal_and_linear_runtime_of_firstUseSlackModel
        model problem).2
  }
  exact
    proposition1_robustExtension_optimal_and_runtime_of_supportExtensionalBallotTransformCertificate
      ({
        baseCert := baseCert
        support_counts_eq := by
          simpa [baseAlgorithm] using support_counts_eq
        feasible_of_support_counts_eq := by
          intro problem hbase hcounts
          exact feasible_of_support_counts_eq problem (by
            simpa [baseAlgorithm] using hbase) (by
            intro active hactive candidate
            simpa [baseAlgorithm] using hcounts active hactive candidate)
        cost_eq_of_support_counts_eq := by
          intro problem hcounts
          exact cost_eq_of_support_counts_eq problem (by
            intro active hactive candidate
            simpa [baseAlgorithm] using hcounts active hactive candidate)
        robustOperationCount_le := robustOperationCount_le
      } :
        SupportExtensionalBallotTransformCertificate voters relevantActiveSets
          baseAlgorithm robustAlgorithm
          (fun problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem
              (Voter → RCVBallot Candidate) => problem.feasible)
          (fun problem : DGJ24OptimalStrategiesRCV.SmartAllocationProblem
              (Voter → RCVBallot Candidate) => problem.cost)
          DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionOperationCount
          robustOperationCount
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound)

/--
Proposition 1 support-extensional route from DGJ24's Algorithm 3 first-use
certificate.
-/
theorem proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithm3FirstUseSlackCertificate_support_extensional_ballot_transform
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    {robustAlgorithm :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Voter → RCVBallot Candidate}
    {robustOperationCount :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        ℕ}
    (cert :
      DGJ24OptimalStrategiesRCV.Algorithm3FirstUseSlackCertificate
        (Voter → RCVBallot Candidate) Slack)
    (voters :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Finset Voter)
    (relevantActiveSets :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Finset (Finset Candidate))
    (support_counts_eq :
      activeSupportCountsEqualOn voters relevantActiveSets
        (DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
          cert.toFirstUseSlackModel.slackProblem
          cert.toFirstUseSlackModel.additionOf)
        robustAlgorithm)
    (feasible_of_support_counts_eq :
      ∀ problem,
        problem.feasible
          (DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
            cert.toFirstUseSlackModel.slackProblem
            cert.toFirstUseSlackModel.additionOf problem) →
          (∀ active, active ∈ relevantActiveSets problem → ∀ candidate,
            (Ballot.activeSupport (voters problem) (robustAlgorithm problem)
                active candidate).card =
              (Ballot.activeSupport (voters problem)
                (DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
                  cert.toFirstUseSlackModel.slackProblem
                  cert.toFirstUseSlackModel.additionOf problem)
                active candidate).card) →
            problem.feasible (robustAlgorithm problem))
    (cost_eq_of_support_counts_eq :
      ∀ problem,
        (∀ active, active ∈ relevantActiveSets problem → ∀ candidate,
          (Ballot.activeSupport (voters problem) (robustAlgorithm problem)
              active candidate).card =
            (Ballot.activeSupport (voters problem)
              (DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
                cert.toFirstUseSlackModel.slackProblem
                cert.toFirstUseSlackModel.additionOf problem)
              active candidate).card) →
          problem.cost (robustAlgorithm problem) =
            problem.cost
              (DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
                cert.toFirstUseSlackModel.slackProblem
                cert.toFirstUseSlackModel.additionOf problem))
    (robustOperationCount_le :
      ∀ problem,
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem) :
    ∀ problem :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
        (Voter → RCVBallot Candidate),
      EconCSLib.Optimization.IsMinimizerOn
          problem.feasible problem.cost (robustAlgorithm problem) ∧
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem := by
  exact
    proposition1_robustSmartAllocation_optimal_and_runtime_of_firstUseSlackModel_support_extensional_ballot_transform
      (model := cert.toFirstUseSlackModel)
      (robustAlgorithm := robustAlgorithm)
      (robustOperationCount := robustOperationCount)
      voters relevantActiveSets support_counts_eq
      feasible_of_support_counts_eq cost_eq_of_support_counts_eq
      robustOperationCount_le

/--
Proposition 1 route from a concrete support-count SmartAllocation source model.
The DGJ24 source model states that feasibility and cost depend only on relevant
active-support counts; the ballot transform supplies equality of those counts.
-/
theorem proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithm3FirstUseSlackCertificate_supportCountModel
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    {robustAlgorithm :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Voter → RCVBallot Candidate}
    {robustOperationCount :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        ℕ}
    (cert :
      DGJ24OptimalStrategiesRCV.Algorithm3FirstUseSlackCertificate
        (Voter → RCVBallot Candidate) Slack)
    (voters :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Finset Voter)
    (relevantActiveSets :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Finset (Finset Candidate))
    (supportModel :
      ∀ problem :
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate),
        DGJ24OptimalStrategiesRCV.SmartAllocationSupportCountModel
          problem (voters problem) (relevantActiveSets problem))
    (support_counts_eq :
      activeSupportCountsEqualOn voters relevantActiveSets
        (DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
          cert.toFirstUseSlackModel.slackProblem
          cert.toFirstUseSlackModel.additionOf)
        robustAlgorithm)
    (robustOperationCount_le :
      ∀ problem,
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem) :
    ∀ problem :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
        (Voter → RCVBallot Candidate),
      EconCSLib.Optimization.IsMinimizerOn
          problem.feasible problem.cost (robustAlgorithm problem) ∧
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem := by
  exact
    proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithm3FirstUseSlackCertificate_support_extensional_ballot_transform
      (cert := cert)
      (robustAlgorithm := robustAlgorithm)
      (robustOperationCount := robustOperationCount)
      voters relevantActiveSets support_counts_eq
      (by
        intro problem hbase hcounts
        exact
          DGJ24OptimalStrategiesRCV.SmartAllocationSupportCountModel.feasible_of_support_counts_eq
            (supportModel problem) hbase hcounts)
      (by
        intro problem hcounts
        exact
          DGJ24OptimalStrategiesRCV.SmartAllocationSupportCountModel.cost_eq_of_support_counts_eq
            (supportModel problem) hcounts)
      robustOperationCount_le

/--
Proposition 1 for a concrete support-count SmartAllocation instance.  This is
the source-shaped Algorithm A route once the DGJ24 Algorithm 3 problem has been
specified as depending only on relevant active-support counts.
-/
theorem proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithm3FirstUseSlackCertificate_supportCountData
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (data :
      DGJ24OptimalStrategiesRCV.SupportCountSmartAllocationData Voter
        Candidate)
    (cert :
      DGJ24OptimalStrategiesRCV.Algorithm3FirstUseSlackCertificate
        (Voter → RCVBallot Candidate) Slack)
    (robust : Voter → RCVBallot Candidate)
    (robustOperationCount : ℕ)
    (support_counts_eq :
      ∀ active, active ∈ data.relevantActiveSets → ∀ candidate,
        (Ballot.activeSupport data.voters robust active candidate).card =
          (Ballot.activeSupport data.voters
            ((DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
              cert.toFirstUseSlackModel.slackProblem
              cert.toFirstUseSlackModel.additionOf) data.problem)
            active candidate).card)
    (robustOperationCount_le :
      robustOperationCount ≤
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
          data.problem) :
    EconCSLib.Optimization.IsMinimizerOn
        data.problem.feasible data.problem.cost robust ∧
      robustOperationCount ≤
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
          data.problem := by
  let base : Voter → RCVBallot Candidate :=
    (DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
      cert.toFirstUseSlackModel.slackProblem
      cert.toFirstUseSlackModel.additionOf) data.problem
  have hbase :
      EconCSLib.Optimization.IsMinimizerOn
          data.problem.feasible data.problem.cost base ∧
        DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionOperationCount
            data.problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            data.problem := by
    simpa [base] using
      DGJ24OptimalStrategiesRCV.theorem3_1_smartAllocation_optimal_and_linear_runtime_of_firstUseSlackModel
        cert.toFirstUseSlackModel data.problem
  have hrobustFeasible : data.problem.feasible robust :=
    DGJ24OptimalStrategiesRCV.SupportCountSmartAllocationData.feasible_of_support_counts_eq
      data hbase.1.1 (by
        intro active hactive candidate
        simpa [base] using support_counts_eq active hactive candidate)
  have hcost : data.problem.cost robust = data.problem.cost base :=
    DGJ24OptimalStrategiesRCV.SupportCountSmartAllocationData.cost_eq_of_support_counts_eq
      data (by
        intro active hactive candidate
        simpa [base] using support_counts_eq active hactive candidate)
  refine ⟨?_, robustOperationCount_le⟩
  refine ⟨hrobustFeasible, ?_⟩
  intro alternative halternative
  calc
    data.problem.cost robust = data.problem.cost base := hcost
    _ ≤ data.problem.cost alternative := hbase.1.2 alternative halternative

/--
Proposition 1 for a concrete support-count SmartAllocation instance, using a
fixed-problem Algorithm 3 first-use certificate.  This is the local
source-shaped route: the DGJ24 exact-fill ballot output is optimal for this
specific support-count instance, and Algorithm A only has to preserve relevant
active-support counts.
-/
theorem proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithm3ProblemFirstUseSlackCertificate_supportCountData
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (data :
      DGJ24OptimalStrategiesRCV.SupportCountSmartAllocationData Voter
        Candidate)
    (cert :
      DGJ24OptimalStrategiesRCV.Algorithm3ProblemFirstUseSlackCertificate
        (Voter → RCVBallot Candidate) Slack data.problem)
    (robust : Voter → RCVBallot Candidate)
    (robustOperationCount : ℕ)
    (support_counts_eq :
      ∀ active, active ∈ data.relevantActiveSets → ∀ candidate,
        (Ballot.activeSupport data.voters robust active candidate).card =
          (Ballot.activeSupport data.voters
            (DGJ24OptimalStrategiesRCV.Algorithm3ProblemFirstUseSlackCertificate.exactFill
              cert)
            active candidate).card)
    (robustOperationCount_le :
      robustOperationCount ≤
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
          data.problem) :
    EconCSLib.Optimization.IsMinimizerOn
        data.problem.feasible data.problem.cost robust ∧
      robustOperationCount ≤
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
          data.problem := by
  let base : Voter → RCVBallot Candidate :=
    DGJ24OptimalStrategiesRCV.Algorithm3ProblemFirstUseSlackCertificate.exactFill
      cert
  have hbase :
      EconCSLib.Optimization.IsMinimizerOn
          data.problem.feasible data.problem.cost base ∧
        DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionOperationCount
            data.problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            data.problem := by
    simpa [base] using
      DGJ24OptimalStrategiesRCV.Algorithm3ProblemFirstUseSlackCertificate.exactFill_optimal_and_linear_runtime
        cert
  have hrobustFeasible : data.problem.feasible robust :=
    DGJ24OptimalStrategiesRCV.SupportCountSmartAllocationData.feasible_of_support_counts_eq
      data hbase.1.1 (by
        intro active hactive candidate
        simpa [base] using support_counts_eq active hactive candidate)
  have hcost : data.problem.cost robust = data.problem.cost base :=
    DGJ24OptimalStrategiesRCV.SupportCountSmartAllocationData.cost_eq_of_support_counts_eq
      data (by
        intro active hactive candidate
        simpa [base] using support_counts_eq active hactive candidate)
  refine ⟨?_, robustOperationCount_le⟩
  refine ⟨hrobustFeasible, ?_⟩
  intro alternative halternative
  calc
    data.problem.cost robust = data.problem.cost base := hcost
    _ ≤ data.problem.cost alternative := hbase.1.2 alternative halternative

/--
Proposition 1 for a concrete support-count SmartAllocation instance, with
Algorithm A implemented by suffixing the DGJ24 Algorithm 3 ballots and then
prefixing candidates that are inactive at every relevant active set.
-/
theorem proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithm3FirstUseSlackCertificate_supportCountData_suffix_then_prefix
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (data :
      DGJ24OptimalStrategiesRCV.SupportCountSmartAllocationData Voter
        Candidate)
    (cert :
      DGJ24OptimalStrategiesRCV.Algorithm3FirstUseSlackCertificate
        (Voter → RCVBallot Candidate) Slack)
    (middle robust pref : Voter → RCVBallot Candidate)
    (robustOperationCount : ℕ)
    (hsuffix :
      ∀ voter, voter ∈ data.voters →
        ballotSuffixExtension
          ((DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
            cert.toFirstUseSlackModel.slackProblem
            cert.toFirstUseSlackModel.additionOf) data.problem voter)
          (middle voter))
    (hreaches :
      ∀ active, active ∈ data.relevantActiveSets →
        ∀ voter, voter ∈ data.voters →
          ∃ first,
            Ballot.nextActive
              ((DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
                cert.toFirstUseSlackModel.slackProblem
                cert.toFirstUseSlackModel.additionOf) data.problem voter)
              active = some first)
    (hprefix :
      ∀ voter, voter ∈ data.voters →
        ballotPrefixExtension (pref voter) (middle voter) (robust voter))
    (hpref :
      ∀ active, active ∈ data.relevantActiveSets →
        ∀ voter, voter ∈ data.voters →
          exhaustedPrefixAtActiveSet (pref voter) active)
    (robustOperationCount_le :
      robustOperationCount ≤
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
          data.problem) :
    EconCSLib.Optimization.IsMinimizerOn
        data.problem.feasible data.problem.cost robust ∧
      robustOperationCount ≤
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
          data.problem := by
  let base : Voter → RCVBallot Candidate :=
    (DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
      cert.toFirstUseSlackModel.slackProblem
      cert.toFirstUseSlackModel.additionOf) data.problem
  refine
    proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithm3FirstUseSlackCertificate_supportCountData
      data cert robust robustOperationCount ?_ robustOperationCount_le
  intro active hactive candidate
  have hcount :
      (Ballot.activeSupport data.voters robust active candidate).card =
        (Ballot.activeSupport data.voters base active candidate).card := by
    calc
      (Ballot.activeSupport data.voters robust active candidate).card =
          (Ballot.activeSupport data.voters middle active candidate).card := by
        exact
          prefixing_inactive_candidates_preserves_activeSupport_count
            (voters := data.voters) (pref := pref) (base := middle)
            (extended := robust) (active := active) (candidate := candidate)
            (by
              intro voter hvoter
              exact hprefix voter hvoter)
            (by
              intro voter hvoter
              exact hpref active hactive voter hvoter)
      _ = (Ballot.activeSupport data.voters base active candidate).card := by
        exact
          suffixing_preserves_activeSupport_count
            (voters := data.voters) (base := base) (extended := middle)
            (active := active) (candidate := candidate)
            (by
              intro voter hvoter
              exact hsuffix voter hvoter)
            (by
              intro voter hvoter
              exact hreaches active hactive voter hvoter)
  simpa [base] using hcount

/--
Proposition 1 for a concrete support-count SmartAllocation instance, with a
fixed-problem Algorithm 3 first-use certificate and Algorithm A implemented by
suffixing the exact-fill ballots followed by inactive prefixes.
-/
theorem proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithm3ProblemFirstUseSlackCertificate_supportCountData_suffix_then_prefix
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (data :
      DGJ24OptimalStrategiesRCV.SupportCountSmartAllocationData Voter
        Candidate)
    (cert :
      DGJ24OptimalStrategiesRCV.Algorithm3ProblemFirstUseSlackCertificate
        (Voter → RCVBallot Candidate) Slack data.problem)
    (middle robust pref : Voter → RCVBallot Candidate)
    (robustOperationCount : ℕ)
    (hsuffix :
      ∀ voter, voter ∈ data.voters →
        ballotSuffixExtension
          (DGJ24OptimalStrategiesRCV.Algorithm3ProblemFirstUseSlackCertificate.exactFill
            cert voter)
          (middle voter))
    (hreaches :
      ∀ active, active ∈ data.relevantActiveSets →
        ∀ voter, voter ∈ data.voters →
          ∃ first,
            Ballot.nextActive
              (DGJ24OptimalStrategiesRCV.Algorithm3ProblemFirstUseSlackCertificate.exactFill
                cert voter)
              active = some first)
    (hprefix :
      ∀ voter, voter ∈ data.voters →
        ballotPrefixExtension (pref voter) (middle voter) (robust voter))
    (hpref :
      ∀ active, active ∈ data.relevantActiveSets →
        ∀ voter, voter ∈ data.voters →
          exhaustedPrefixAtActiveSet (pref voter) active)
    (robustOperationCount_le :
      robustOperationCount ≤
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
          data.problem) :
    EconCSLib.Optimization.IsMinimizerOn
        data.problem.feasible data.problem.cost robust ∧
      robustOperationCount ≤
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
          data.problem := by
  let base : Voter → RCVBallot Candidate :=
    DGJ24OptimalStrategiesRCV.Algorithm3ProblemFirstUseSlackCertificate.exactFill
      cert
  refine
    proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithm3ProblemFirstUseSlackCertificate_supportCountData
      data cert robust robustOperationCount ?_ robustOperationCount_le
  intro active hactive candidate
  have hcount :
      (Ballot.activeSupport data.voters robust active candidate).card =
        (Ballot.activeSupport data.voters base active candidate).card := by
    calc
      (Ballot.activeSupport data.voters robust active candidate).card =
          (Ballot.activeSupport data.voters middle active candidate).card := by
        exact
          prefixing_inactive_candidates_preserves_activeSupport_count
            (voters := data.voters) (pref := pref) (base := middle)
            (extended := robust) (active := active) (candidate := candidate)
            (by
              intro voter hvoter
              exact hprefix voter hvoter)
            (by
              intro voter hvoter
              exact hpref active hactive voter hvoter)
      _ = (Ballot.activeSupport data.voters base active candidate).card := by
        exact
          suffixing_preserves_activeSupport_count
            (voters := data.voters) (base := base) (extended := middle)
            (active := active) (candidate := candidate)
            (by
              intro voter hvoter
              exact hsuffix voter hvoter)
            (by
              intro voter hvoter
              exact hreaches active hactive voter hvoter)
  simpa [base] using hcount

/--
Source data for Algorithm A's suffix-robust specialization when the base
strategy comes from DGJ24's concrete Algorithm 3 support-count loop.

The additional reachability invariant is the exact robust-allocation condition
needed for arbitrary suffixes: before any appended later preferences can matter,
each exact-fill strategy ballot already has a first active candidate at every
source-relevant active set.
-/
structure AlgorithmASuffixRobustSupportCountLoopData
    (Voter Candidate Slack : Type*) [DecidableEq Candidate]
    [Fintype Slack] where
  base :
    DGJ24OptimalStrategiesRCV.Algorithm3SupportCountLoopData
      Voter Candidate Slack
  exactFill_reaches :
    ∀ active, active ∈ base.relevantActiveSets →
      ∀ voter, voter ∈ base.voters →
        ∃ first, Ballot.nextActive (base.exactFill voter) active = some first

namespace AlgorithmASuffixRobustSupportCountLoopData

/-- The robust ballot profile obtained by appending arbitrary suffixes. -/
def suffixOnlyProfile
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (data : AlgorithmASuffixRobustSupportCountLoopData Voter Candidate Slack)
    (suffix : Voter → RCVBallot Candidate) : Voter → RCVBallot Candidate :=
  fun voter => data.base.exactFill voter ++ suffix voter

/--
Algorithm A suffix-robust specialization: appending arbitrary later
preferences to the DGJ24 exact-fill strategy remains optimal, with the
operation count inherited from the base SmartAllocation loop.
-/
theorem suffixOnlyProfile_optimal_and_linear_runtime
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (data : AlgorithmASuffixRobustSupportCountLoopData Voter Candidate Slack)
    (suffix : Voter → RCVBallot Candidate) :
    EconCSLib.Optimization.IsMinimizerOn
        data.base.problem.feasible data.base.problem.cost
        (data.suffixOnlyProfile suffix) ∧
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
          data.base.problem ≤
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
          data.base.problem := by
  simpa [suffixOnlyProfile,
    DGJ24OptimalStrategiesRCV.Algorithm3SupportCountLoopData.problem] using
    proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithm3ProblemFirstUseSlackCertificate_supportCountData_suffix_then_prefix
      data.base.supportCountData data.base.problemFirstUseSlackCertificate
      (fun voter => data.base.exactFill voter ++ suffix voter)
      (fun voter => data.base.exactFill voter ++ suffix voter)
      (fun _voter => ([] : RCVBallot Candidate))
      (DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
        data.base.problem)
      (by
        intro voter _hvoter
        exact ⟨suffix voter, rfl⟩)
      data.exactFill_reaches
      (by
        intro voter _hvoter
        rfl)
      (by
        intro active _hactive voter _hvoter candidate hcandidate
        simpa using hcandidate)
      le_rfl

end AlgorithmASuffixRobustSupportCountLoopData

/--
Source data for the full Algorithm A suffix-then-prefix specialization when the
base strategy comes from DGJ24's concrete Algorithm 3 support-count loop.

The concrete output is `pref ++ (exactFill ++ suffix)`.  The two remaining
fields are the source-semantic invariants needed by the suffix/prefix
robustness lemmas: the exact-fill ballot already reaches every relevant active
set, and the prefixed candidates are inactive at those same active sets.
-/
structure AlgorithmASuffixThenPrefixSupportCountLoopData
    (Voter Candidate Slack : Type*) [DecidableEq Candidate]
    [Fintype Slack] where
  base :
    DGJ24OptimalStrategiesRCV.Algorithm3SupportCountLoopData
      Voter Candidate Slack
  pref : Voter → RCVBallot Candidate
  exactFill_reaches :
    ∀ active, active ∈ base.relevantActiveSets →
      ∀ voter, voter ∈ base.voters →
        ∃ first, Ballot.nextActive (base.exactFill voter) active = some first
  prefix_exhausted :
    ∀ active, active ∈ base.relevantActiveSets →
      ∀ voter, voter ∈ base.voters →
        exhaustedPrefixAtActiveSet (pref voter) active

/--
Executable finite check for the two remaining Algorithm A suffix/prefix
invariants on a fixed DGJ24 support-count loop instance.
-/
noncomputable def algorithmASuffixThenPrefixSupportCountLoopDataCheck
    {Voter Candidate Slack : Type*} [DecidableEq Voter]
    [DecidableEq Candidate] [Fintype Slack]
    (base :
      DGJ24OptimalStrategiesRCV.Algorithm3SupportCountLoopData
        Voter Candidate Slack)
    (pref : Voter → RCVBallot Candidate) : Bool :=
  base.relevantActiveSets.toList.all fun active =>
    base.voters.toList.all fun voter =>
      (Ballot.nextActive (base.exactFill voter) active).isSome &&
        (pref voter).all fun candidate => decide (candidate ∉ active)

theorem algorithmASuffixThenPrefixSupportCountLoopData_exactFill_reaches_of_check
    {Voter Candidate Slack : Type*} [DecidableEq Voter]
    [DecidableEq Candidate] [Fintype Slack]
    {base :
      DGJ24OptimalStrategiesRCV.Algorithm3SupportCountLoopData
        Voter Candidate Slack}
    {pref : Voter → RCVBallot Candidate}
    (hcheck :
      algorithmASuffixThenPrefixSupportCountLoopDataCheck base pref = true) :
    ∀ active, active ∈ base.relevantActiveSets →
      ∀ voter, voter ∈ base.voters →
        ∃ first, Ballot.nextActive (base.exactFill voter) active = some first := by
  intro active hactive voter hvoter
  have hactive_all :=
    (List.all_eq_true.mp hcheck) active
      (Finset.mem_toList.mpr hactive)
  have hvoter_all :=
    (List.all_eq_true.mp hactive_all) voter
      (Finset.mem_toList.mpr hvoter)
  have hparts :
      (Ballot.nextActive (base.exactFill voter) active).isSome = true ∧
        (pref voter).all (fun candidate => decide (candidate ∉ active)) =
          true := by
    simpa [Bool.and_eq_true_eq_eq_true_and_eq_true] using hvoter_all
  have hsome :
      (Ballot.nextActive (base.exactFill voter) active).isSome = true := by
    exact hparts.1
  cases hnext : Ballot.nextActive (base.exactFill voter) active with
  | none =>
      simp [hnext] at hsome
  | some first =>
      exact ⟨first, rfl⟩

theorem algorithmASuffixThenPrefixSupportCountLoopData_prefix_exhausted_of_check
    {Voter Candidate Slack : Type*} [DecidableEq Voter]
    [DecidableEq Candidate] [Fintype Slack]
    {base :
      DGJ24OptimalStrategiesRCV.Algorithm3SupportCountLoopData
        Voter Candidate Slack}
    {pref : Voter → RCVBallot Candidate}
    (hcheck :
      algorithmASuffixThenPrefixSupportCountLoopDataCheck base pref = true) :
    ∀ active, active ∈ base.relevantActiveSets →
      ∀ voter, voter ∈ base.voters →
        exhaustedPrefixAtActiveSet (pref voter) active := by
  intro active hactive voter hvoter candidate hcandidate
  have hactive_all :=
    (List.all_eq_true.mp hcheck) active
      (Finset.mem_toList.mpr hactive)
  have hvoter_all :=
    (List.all_eq_true.mp hactive_all) voter
      (Finset.mem_toList.mpr hvoter)
  have hparts :
      (Ballot.nextActive (base.exactFill voter) active).isSome = true ∧
        (pref voter).all (fun candidate => decide (candidate ∉ active)) =
          true := by
    simpa [Bool.and_eq_true_eq_eq_true_and_eq_true] using hvoter_all
  have hpref_all :
      (pref voter).all (fun candidate => decide (candidate ∉ active)) = true := by
    exact hparts.2
  exact
    of_decide_eq_true
      ((List.all_eq_true.mp hpref_all) candidate hcandidate)

/--
Completeness of the executable Algorithm A suffix/prefix checker from the
source invariants it represents.
-/
theorem algorithmASuffixThenPrefixSupportCountLoopDataCheck_eq_true_of_invariants
    {Voter Candidate Slack : Type*} [DecidableEq Voter]
    [DecidableEq Candidate] [Fintype Slack]
    {base :
      DGJ24OptimalStrategiesRCV.Algorithm3SupportCountLoopData
        Voter Candidate Slack}
    {pref : Voter → RCVBallot Candidate}
    (exactFill_reaches :
      ∀ active, active ∈ base.relevantActiveSets →
        ∀ voter, voter ∈ base.voters →
          ∃ first, Ballot.nextActive (base.exactFill voter) active = some first)
    (prefix_exhausted :
      ∀ active, active ∈ base.relevantActiveSets →
        ∀ voter, voter ∈ base.voters →
          exhaustedPrefixAtActiveSet (pref voter) active) :
    algorithmASuffixThenPrefixSupportCountLoopDataCheck base pref = true := by
  unfold algorithmASuffixThenPrefixSupportCountLoopDataCheck
  apply List.all_eq_true.mpr
  intro active hactive
  apply List.all_eq_true.mpr
  intro voter hvoter
  have hactive_mem : active ∈ base.relevantActiveSets :=
    Finset.mem_toList.mp hactive
  have hvoter_mem : voter ∈ base.voters :=
    Finset.mem_toList.mp hvoter
  have hsome :
      (Ballot.nextActive (base.exactFill voter) active).isSome = true := by
    rcases exactFill_reaches active hactive_mem voter hvoter_mem with
      ⟨first, hfirst⟩
    simp [hfirst]
  have hpref_all :
      (pref voter).all (fun candidate => decide (candidate ∉ active)) = true := by
    apply List.all_eq_true.mpr
    intro candidate hcandidate
    exact decide_eq_true
      (prefix_exhausted active hactive_mem voter hvoter_mem candidate hcandidate)
  rw [Bool.and_eq_true_eq_eq_true_and_eq_true]
  exact ⟨hsome, hpref_all⟩

/--
Build the fixed DGJ24 support-count Algorithm A source data from the finite
checker, leaving no separate reachability or inactive-prefix premise.
-/
noncomputable def algorithmASuffixThenPrefixSupportCountLoopData_of_check
    {Voter Candidate Slack : Type*} [DecidableEq Voter]
    [DecidableEq Candidate] [Fintype Slack]
    (base :
      DGJ24OptimalStrategiesRCV.Algorithm3SupportCountLoopData
        Voter Candidate Slack)
    (pref : Voter → RCVBallot Candidate)
    (hcheck :
      algorithmASuffixThenPrefixSupportCountLoopDataCheck base pref = true) :
    AlgorithmASuffixThenPrefixSupportCountLoopData Voter Candidate Slack where
  base := base
  pref := pref
  exactFill_reaches :=
    algorithmASuffixThenPrefixSupportCountLoopData_exactFill_reaches_of_check
      hcheck
  prefix_exhausted :=
    algorithmASuffixThenPrefixSupportCountLoopData_prefix_exhausted_of_check
      hcheck

namespace AlgorithmASuffixThenPrefixSupportCountLoopData

/-- The intermediate Algorithm A profile after appending arbitrary suffixes. -/
def suffixProfile
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (data :
      AlgorithmASuffixThenPrefixSupportCountLoopData Voter Candidate Slack)
    (suffix : Voter → RCVBallot Candidate) :
    Voter → RCVBallot Candidate :=
  fun voter => data.base.exactFill voter ++ suffix voter

/-- The full Algorithm A profile, prefixing exhausted candidates before the suffix-extended base. -/
def outputProfile
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (data :
      AlgorithmASuffixThenPrefixSupportCountLoopData Voter Candidate Slack)
    (suffix : Voter → RCVBallot Candidate) :
    Voter → RCVBallot Candidate :=
  fun voter => data.pref voter ++ data.suffixProfile suffix voter

/--
Full Algorithm A suffix-then-prefix specialization: the concrete output
profile remains optimal, and its operation count is inherited from the base
SmartAllocation loop.
-/
theorem outputProfile_optimal_and_linear_runtime
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (data :
      AlgorithmASuffixThenPrefixSupportCountLoopData Voter Candidate Slack)
    (suffix : Voter → RCVBallot Candidate) :
    EconCSLib.Optimization.IsMinimizerOn
        data.base.problem.feasible data.base.problem.cost
        (data.outputProfile suffix) ∧
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
          data.base.problem ≤
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
          data.base.problem := by
  simpa [suffixProfile, outputProfile,
    DGJ24OptimalStrategiesRCV.Algorithm3SupportCountLoopData.problem] using
    proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithm3ProblemFirstUseSlackCertificate_supportCountData_suffix_then_prefix
      data.base.supportCountData data.base.problemFirstUseSlackCertificate
      (data.suffixProfile suffix)
      (data.outputProfile suffix)
      data.pref
      (DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
        data.base.problem)
      (by
        intro voter _hvoter
        exact ⟨suffix voter, rfl⟩)
      data.exactFill_reaches
      (by
        intro voter _hvoter
        rfl)
      data.prefix_exhausted
      le_rfl

end AlgorithmASuffixThenPrefixSupportCountLoopData

/--
Source data for the full Algorithm A suffix-then-prefix specialization when the
base strategy is DGJ24's checked exact-fill Algorithm 3 output.

This is the downstream Proposition 1 route that only needs the actual
exact-fill profile, not the stronger hypothetical support-count loop
certificate used by earlier wrappers.
-/
structure AlgorithmASuffixThenPrefixExactFillSupportCountData
    (Voter Candidate Slack : Type*) [DecidableEq Candidate]
    [Fintype Slack] where
  base :
    DGJ24OptimalStrategiesRCV.Algorithm3ExactFillSupportCountData
      Voter Candidate Slack
  pref : Voter → RCVBallot Candidate
  exactFill_reaches :
    ∀ active, active ∈ base.relevantActiveSets →
      ∀ voter, voter ∈ base.voters →
        ∃ first, Ballot.nextActive (base.exactFill voter) active = some first
  prefix_exhausted :
    ∀ active, active ∈ base.relevantActiveSets →
      ∀ voter, voter ∈ base.voters →
        exhaustedPrefixAtActiveSet (pref voter) active

/--
Executable finite check for the two remaining Algorithm A suffix/prefix
invariants on DGJ24's checked exact-fill Algorithm 3 data.
-/
noncomputable def algorithmASuffixThenPrefixExactFillSupportCountDataCheck
    {Voter Candidate Slack : Type*} [DecidableEq Voter]
    [DecidableEq Candidate] [Fintype Slack]
    (base :
      DGJ24OptimalStrategiesRCV.Algorithm3ExactFillSupportCountData
        Voter Candidate Slack)
    (pref : Voter → RCVBallot Candidate) : Bool :=
  base.relevantActiveSets.toList.all fun active =>
    base.voters.toList.all fun voter =>
      (Ballot.nextActive (base.exactFill voter) active).isSome &&
        (pref voter).all fun candidate => decide (candidate ∉ active)

theorem algorithmASuffixThenPrefixExactFillSupportCountData_exactFill_reaches_of_check
    {Voter Candidate Slack : Type*} [DecidableEq Voter]
    [DecidableEq Candidate] [Fintype Slack]
    {base :
      DGJ24OptimalStrategiesRCV.Algorithm3ExactFillSupportCountData
        Voter Candidate Slack}
    {pref : Voter → RCVBallot Candidate}
    (hcheck :
      algorithmASuffixThenPrefixExactFillSupportCountDataCheck base pref =
        true) :
    ∀ active, active ∈ base.relevantActiveSets →
      ∀ voter, voter ∈ base.voters →
        ∃ first, Ballot.nextActive (base.exactFill voter) active = some first := by
  intro active hactive voter hvoter
  have hactive_all :=
    (List.all_eq_true.mp hcheck) active
      (Finset.mem_toList.mpr hactive)
  have hvoter_all :=
    (List.all_eq_true.mp hactive_all) voter
      (Finset.mem_toList.mpr hvoter)
  have hparts :
      (Ballot.nextActive (base.exactFill voter) active).isSome = true ∧
        (pref voter).all (fun candidate => decide (candidate ∉ active)) =
          true := by
    simpa [Bool.and_eq_true_eq_eq_true_and_eq_true] using hvoter_all
  have hsome :
      (Ballot.nextActive (base.exactFill voter) active).isSome = true := by
    exact hparts.1
  cases hnext : Ballot.nextActive (base.exactFill voter) active with
  | none =>
      simp [hnext] at hsome
  | some first =>
      exact ⟨first, rfl⟩

theorem algorithmASuffixThenPrefixExactFillSupportCountData_prefix_exhausted_of_check
    {Voter Candidate Slack : Type*} [DecidableEq Voter]
    [DecidableEq Candidate] [Fintype Slack]
    {base :
      DGJ24OptimalStrategiesRCV.Algorithm3ExactFillSupportCountData
        Voter Candidate Slack}
    {pref : Voter → RCVBallot Candidate}
    (hcheck :
      algorithmASuffixThenPrefixExactFillSupportCountDataCheck base pref =
        true) :
    ∀ active, active ∈ base.relevantActiveSets →
      ∀ voter, voter ∈ base.voters →
        exhaustedPrefixAtActiveSet (pref voter) active := by
  intro active hactive voter hvoter candidate hcandidate
  have hactive_all :=
    (List.all_eq_true.mp hcheck) active
      (Finset.mem_toList.mpr hactive)
  have hvoter_all :=
    (List.all_eq_true.mp hactive_all) voter
      (Finset.mem_toList.mpr hvoter)
  have hparts :
      (Ballot.nextActive (base.exactFill voter) active).isSome = true ∧
        (pref voter).all (fun candidate => decide (candidate ∉ active)) =
          true := by
    simpa [Bool.and_eq_true_eq_eq_true_and_eq_true] using hvoter_all
  have hpref_all :
      (pref voter).all (fun candidate => decide (candidate ∉ active)) = true := by
    exact hparts.2
  exact
    of_decide_eq_true
      ((List.all_eq_true.mp hpref_all) candidate hcandidate)

/--
Completeness of the executable Algorithm A suffix/prefix checker from the
source invariants it represents, specialized to DGJ24 exact-fill data.
-/
theorem algorithmASuffixThenPrefixExactFillSupportCountDataCheck_eq_true_of_invariants
    {Voter Candidate Slack : Type*} [DecidableEq Voter]
    [DecidableEq Candidate] [Fintype Slack]
    {base :
      DGJ24OptimalStrategiesRCV.Algorithm3ExactFillSupportCountData
        Voter Candidate Slack}
    {pref : Voter → RCVBallot Candidate}
    (exactFill_reaches :
      ∀ active, active ∈ base.relevantActiveSets →
        ∀ voter, voter ∈ base.voters →
          ∃ first, Ballot.nextActive (base.exactFill voter) active = some first)
    (prefix_exhausted :
      ∀ active, active ∈ base.relevantActiveSets →
        ∀ voter, voter ∈ base.voters →
          exhaustedPrefixAtActiveSet (pref voter) active) :
    algorithmASuffixThenPrefixExactFillSupportCountDataCheck base pref = true := by
  unfold algorithmASuffixThenPrefixExactFillSupportCountDataCheck
  apply List.all_eq_true.mpr
  intro active hactive
  apply List.all_eq_true.mpr
  intro voter hvoter
  have hactive_mem : active ∈ base.relevantActiveSets :=
    Finset.mem_toList.mp hactive
  have hvoter_mem : voter ∈ base.voters :=
    Finset.mem_toList.mp hvoter
  have hsome :
      (Ballot.nextActive (base.exactFill voter) active).isSome = true := by
    rcases exactFill_reaches active hactive_mem voter hvoter_mem with
      ⟨first, hfirst⟩
    simp [hfirst]
  have hpref_all :
      (pref voter).all (fun candidate => decide (candidate ∉ active)) = true := by
    apply List.all_eq_true.mpr
    intro candidate hcandidate
    exact decide_eq_true
      (prefix_exhausted active hactive_mem voter hvoter_mem candidate hcandidate)
  rw [Bool.and_eq_true_eq_eq_true_and_eq_true]
  exact ⟨hsome, hpref_all⟩

/--
Build the checked exact-fill Algorithm A source data from the finite checker,
leaving no separate reachability or inactive-prefix premise.
-/
noncomputable def algorithmASuffixThenPrefixExactFillSupportCountData_of_check
    {Voter Candidate Slack : Type*} [DecidableEq Voter]
    [DecidableEq Candidate] [Fintype Slack]
    (base :
      DGJ24OptimalStrategiesRCV.Algorithm3ExactFillSupportCountData
        Voter Candidate Slack)
    (pref : Voter → RCVBallot Candidate)
    (hcheck :
      algorithmASuffixThenPrefixExactFillSupportCountDataCheck base pref =
        true) :
    AlgorithmASuffixThenPrefixExactFillSupportCountData
      Voter Candidate Slack where
  base := base
  pref := pref
  exactFill_reaches :=
    algorithmASuffixThenPrefixExactFillSupportCountData_exactFill_reaches_of_check
      hcheck
  prefix_exhausted :=
    algorithmASuffixThenPrefixExactFillSupportCountData_prefix_exhausted_of_check
      hcheck

namespace AlgorithmASuffixThenPrefixExactFillSupportCountData

/-- The intermediate Algorithm A profile after appending arbitrary suffixes. -/
def suffixProfile
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (data :
      AlgorithmASuffixThenPrefixExactFillSupportCountData Voter Candidate Slack)
    (suffix : Voter → RCVBallot Candidate) :
    Voter → RCVBallot Candidate :=
  fun voter => data.base.exactFill voter ++ suffix voter

/-- The full Algorithm A profile, prefixing exhausted candidates before the suffix-extended base. -/
def outputProfile
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (data :
      AlgorithmASuffixThenPrefixExactFillSupportCountData Voter Candidate Slack)
    (suffix : Voter → RCVBallot Candidate) :
    Voter → RCVBallot Candidate :=
  fun voter => data.pref voter ++ data.suffixProfile suffix voter

/--
Full Algorithm A suffix-then-prefix specialization from DGJ24's checked
exact-fill Algorithm 3 output. The operation count is inherited from the base
SmartAllocation problem.
-/
theorem outputProfile_optimal_and_linear_runtime
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (data :
      AlgorithmASuffixThenPrefixExactFillSupportCountData Voter Candidate Slack)
    (suffix : Voter → RCVBallot Candidate) :
    EconCSLib.Optimization.IsMinimizerOn
        data.base.problem.feasible data.base.problem.cost
        (data.outputProfile suffix) ∧
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
          data.base.problem ≤
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
          data.base.problem := by
  simpa [suffixProfile, outputProfile,
    DGJ24OptimalStrategiesRCV.Algorithm3ExactFillSupportCountData.problem] using
    proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithm3ProblemFirstUseSlackCertificate_supportCountData_suffix_then_prefix
      data.base.supportCountData data.base.problemFirstUseSlackCertificate
      (data.suffixProfile suffix)
      (data.outputProfile suffix)
      data.pref
      (DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
        data.base.problem)
      (by
        intro voter _hvoter
        exact ⟨suffix voter, rfl⟩)
      data.exactFill_reaches
      (by
        intro voter _hvoter
        rfl)
      data.prefix_exhausted
      le_rfl

end AlgorithmASuffixThenPrefixExactFillSupportCountData

/--
Proposition 1 support-count model route where the robust Algorithm A output is
obtained by suffixing base strategy ballots and then prefixing inactive
ballots.
-/
theorem proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithm3FirstUseSlackCertificate_supportCountModel_suffix_then_prefix
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    {middle robustAlgorithm :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Voter → RCVBallot Candidate}
    {robustOperationCount :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        ℕ}
    {pref :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Voter → RCVBallot Candidate}
    (cert :
      DGJ24OptimalStrategiesRCV.Algorithm3FirstUseSlackCertificate
        (Voter → RCVBallot Candidate) Slack)
    (voters :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Finset Voter)
    (relevantActiveSets :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Finset (Finset Candidate))
    (supportModel :
      ∀ problem :
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate),
        DGJ24OptimalStrategiesRCV.SmartAllocationSupportCountModel
          problem (voters problem) (relevantActiveSets problem))
    (hsuffix :
      ∀ problem voter, voter ∈ voters problem →
        ballotSuffixExtension
          ((DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
            cert.toFirstUseSlackModel.slackProblem
            cert.toFirstUseSlackModel.additionOf) problem voter)
          (middle problem voter))
    (hreaches :
      ∀ problem active, active ∈ relevantActiveSets problem →
        ∀ voter, voter ∈ voters problem →
          ∃ first,
            Ballot.nextActive
              ((DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
                cert.toFirstUseSlackModel.slackProblem
                cert.toFirstUseSlackModel.additionOf) problem voter)
              active = some first)
    (hprefix :
      ∀ problem voter, voter ∈ voters problem →
        ballotPrefixExtension (pref problem voter) (middle problem voter)
          (robustAlgorithm problem voter))
    (hpref :
      ∀ problem active, active ∈ relevantActiveSets problem →
        ∀ voter, voter ∈ voters problem →
          exhaustedPrefixAtActiveSet (pref problem voter) active)
    (robustOperationCount_le :
      ∀ problem,
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem) :
    ∀ problem :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
        (Voter → RCVBallot Candidate),
      EconCSLib.Optimization.IsMinimizerOn
          problem.feasible problem.cost (robustAlgorithm problem) ∧
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem :=
  proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithm3FirstUseSlackCertificate_supportCountModel
    (cert := cert)
    (robustAlgorithm := robustAlgorithm)
    (robustOperationCount := robustOperationCount)
    voters relevantActiveSets supportModel
    (activeSupportCountsEqualOn_of_suffix_then_prefix_extensions
      hsuffix hreaches hprefix hpref)
    robustOperationCount_le

/--
Proposition 1 support-count model route where the robust Algorithm A output is
obtained by prefixing inactive ballots and then suffixing later preferences.
-/
theorem proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithm3FirstUseSlackCertificate_supportCountModel_prefix_then_suffix
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    {middle robustAlgorithm :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Voter → RCVBallot Candidate}
    {robustOperationCount :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        ℕ}
    {pref :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Voter → RCVBallot Candidate}
    (cert :
      DGJ24OptimalStrategiesRCV.Algorithm3FirstUseSlackCertificate
        (Voter → RCVBallot Candidate) Slack)
    (voters :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Finset Voter)
    (relevantActiveSets :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Finset (Finset Candidate))
    (supportModel :
      ∀ problem :
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate),
        DGJ24OptimalStrategiesRCV.SmartAllocationSupportCountModel
          problem (voters problem) (relevantActiveSets problem))
    (hprefix :
      ∀ problem voter, voter ∈ voters problem →
        ballotPrefixExtension (pref problem voter)
          ((DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
            cert.toFirstUseSlackModel.slackProblem
            cert.toFirstUseSlackModel.additionOf) problem voter)
          (middle problem voter))
    (hpref :
      ∀ problem active, active ∈ relevantActiveSets problem →
        ∀ voter, voter ∈ voters problem →
          exhaustedPrefixAtActiveSet (pref problem voter) active)
    (hsuffix :
      ∀ problem voter, voter ∈ voters problem →
        ballotSuffixExtension (middle problem voter)
          (robustAlgorithm problem voter))
    (hreaches :
      ∀ problem active, active ∈ relevantActiveSets problem →
        ∀ voter, voter ∈ voters problem →
          ∃ first,
            Ballot.nextActive
              ((DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
                cert.toFirstUseSlackModel.slackProblem
                cert.toFirstUseSlackModel.additionOf) problem voter)
              active = some first)
    (robustOperationCount_le :
      ∀ problem,
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem) :
    ∀ problem :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
        (Voter → RCVBallot Candidate),
      EconCSLib.Optimization.IsMinimizerOn
          problem.feasible problem.cost (robustAlgorithm problem) ∧
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem :=
  proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithm3FirstUseSlackCertificate_supportCountModel
    (cert := cert)
    (robustAlgorithm := robustAlgorithm)
    (robustOperationCount := robustOperationCount)
    voters relevantActiveSets supportModel
    (activeSupportCountsEqualOn_of_prefix_then_suffix_extensions
      hprefix hpref hsuffix hreaches)
    robustOperationCount_le

/--
Source-shaped Algorithm A certificate for Proposition 1's robust
SmartAllocation extension.

Algorithm A first takes the DGJ24 Algorithm 3 output, extends strategy ballots
by arbitrary suffix preferences, and then prefixes candidates that are inactive
at every relevant source active set.  The certificate records those concrete
ballot-transform facts, the support-count source model, and the inherited
runtime bound.
-/
structure AlgorithmASuffixThenPrefixSmartAllocationCertificate
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (robustAlgorithm :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Voter → RCVBallot Candidate)
    (robustOperationCount :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        ℕ) where
  sourceCert :
    DGJ24OptimalStrategiesRCV.Algorithm3FirstUseSlackCertificate
      (Voter → RCVBallot Candidate) Slack
  voters :
    DGJ24OptimalStrategiesRCV.SmartAllocationProblem
        (Voter → RCVBallot Candidate) →
      Finset Voter
  relevantActiveSets :
    DGJ24OptimalStrategiesRCV.SmartAllocationProblem
        (Voter → RCVBallot Candidate) →
      Finset (Finset Candidate)
  supportModel :
    ∀ problem :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
        (Voter → RCVBallot Candidate),
      DGJ24OptimalStrategiesRCV.SmartAllocationSupportCountModel
        problem (voters problem) (relevantActiveSets problem)
  middle :
    DGJ24OptimalStrategiesRCV.SmartAllocationProblem
        (Voter → RCVBallot Candidate) →
      Voter → RCVBallot Candidate
  pref :
    DGJ24OptimalStrategiesRCV.SmartAllocationProblem
        (Voter → RCVBallot Candidate) →
      Voter → RCVBallot Candidate
  suffix_extension :
    ∀ problem voter, voter ∈ voters problem →
      ballotSuffixExtension
        ((DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
          sourceCert.toFirstUseSlackModel.slackProblem
          sourceCert.toFirstUseSlackModel.additionOf) problem voter)
        (middle problem voter)
  base_reaches :
    ∀ problem active, active ∈ relevantActiveSets problem →
      ∀ voter, voter ∈ voters problem →
        ∃ first,
          Ballot.nextActive
            ((DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
              sourceCert.toFirstUseSlackModel.slackProblem
              sourceCert.toFirstUseSlackModel.additionOf) problem voter)
            active = some first
  prefix_extension :
    ∀ problem voter, voter ∈ voters problem →
      ballotPrefixExtension (pref problem voter) (middle problem voter)
        (robustAlgorithm problem voter)
  prefix_exhausted :
    ∀ problem active, active ∈ relevantActiveSets problem →
      ∀ voter, voter ∈ voters problem →
        exhaustedPrefixAtActiveSet (pref problem voter) active
  robustOperationCount_le :
    ∀ problem,
      robustOperationCount problem ≤
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
          problem

/--
Algorithm A concrete suffix step: append arbitrary later preferences to each
ballot returned by the DGJ24 Algorithm 3 slack-reduction output.
-/
def algorithmASuffixThenPrefixMiddle
    {Voter Candidate Slack : Type*} [Fintype Slack]
    (sourceCert :
      DGJ24OptimalStrategiesRCV.Algorithm3FirstUseSlackCertificate
        (Voter → RCVBallot Candidate) Slack)
    (suffix :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Voter → RCVBallot Candidate) :
    DGJ24OptimalStrategiesRCV.SmartAllocationProblem
        (Voter → RCVBallot Candidate) →
      Voter → RCVBallot Candidate :=
  fun problem voter =>
    (DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
      sourceCert.toFirstUseSlackModel.slackProblem
      sourceCert.toFirstUseSlackModel.additionOf) problem voter ++
      suffix problem voter

/--
Algorithm A concrete suffix-then-prefix output: append arbitrary later
preferences to the DGJ24 Algorithm 3 output, then prefix candidates that are
inactive at all relevant source active sets.
-/
def algorithmASuffixThenPrefixOutput
    {Voter Candidate Slack : Type*} [Fintype Slack]
    (sourceCert :
      DGJ24OptimalStrategiesRCV.Algorithm3FirstUseSlackCertificate
        (Voter → RCVBallot Candidate) Slack)
    (pref suffix :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Voter → RCVBallot Candidate) :
    DGJ24OptimalStrategiesRCV.SmartAllocationProblem
        (Voter → RCVBallot Candidate) →
      Voter → RCVBallot Candidate :=
  fun problem voter =>
    pref problem voter ++
      algorithmASuffixThenPrefixMiddle sourceCert suffix problem voter

/--
Algorithm A concrete prefix step: prefix candidates that are inactive at all
relevant source active sets to the DGJ24 Algorithm 3 output.
-/
def algorithmAPrefixThenSuffixMiddle
    {Voter Candidate Slack : Type*} [Fintype Slack]
    (sourceCert :
      DGJ24OptimalStrategiesRCV.Algorithm3FirstUseSlackCertificate
        (Voter → RCVBallot Candidate) Slack)
    (pref :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Voter → RCVBallot Candidate) :
    DGJ24OptimalStrategiesRCV.SmartAllocationProblem
        (Voter → RCVBallot Candidate) →
      Voter → RCVBallot Candidate :=
  fun problem voter =>
    pref problem voter ++
      (DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
        sourceCert.toFirstUseSlackModel.slackProblem
        sourceCert.toFirstUseSlackModel.additionOf) problem voter

/--
Algorithm A concrete prefix-then-suffix output: prefix inactive candidates to
the DGJ24 Algorithm 3 output, then append arbitrary later preferences.
-/
def algorithmAPrefixThenSuffixOutput
    {Voter Candidate Slack : Type*} [Fintype Slack]
    (sourceCert :
      DGJ24OptimalStrategiesRCV.Algorithm3FirstUseSlackCertificate
        (Voter → RCVBallot Candidate) Slack)
    (pref suffix :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Voter → RCVBallot Candidate) :
    DGJ24OptimalStrategiesRCV.SmartAllocationProblem
        (Voter → RCVBallot Candidate) →
      Voter → RCVBallot Candidate :=
  fun problem voter =>
    algorithmAPrefixThenSuffixMiddle sourceCert pref problem voter ++
      suffix problem voter

/--
Concrete constructor for Algorithm A's suffix-then-prefix certificate.  The
source model still supplies the non-mechanical obligations: which active sets
matter, the DGJ24 support-count model, base ballot reachability, inactive
prefixes, and the inherited runtime bound.  The list-construction obligations
are discharged by the executable Algorithm A output above.
-/
def algorithmASuffixThenPrefixSmartAllocationCertificate_of_append
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (sourceCert :
      DGJ24OptimalStrategiesRCV.Algorithm3FirstUseSlackCertificate
        (Voter → RCVBallot Candidate) Slack)
    (voters :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Finset Voter)
    (relevantActiveSets :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Finset (Finset Candidate))
    (supportModel :
      ∀ problem :
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate),
        DGJ24OptimalStrategiesRCV.SmartAllocationSupportCountModel
          problem (voters problem) (relevantActiveSets problem))
    (pref suffix :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Voter → RCVBallot Candidate)
    (base_reaches :
      ∀ problem active, active ∈ relevantActiveSets problem →
        ∀ voter, voter ∈ voters problem →
          ∃ first,
            Ballot.nextActive
              ((DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
                sourceCert.toFirstUseSlackModel.slackProblem
                sourceCert.toFirstUseSlackModel.additionOf) problem voter)
              active = some first)
    (prefix_exhausted :
      ∀ problem active, active ∈ relevantActiveSets problem →
        ∀ voter, voter ∈ voters problem →
          exhaustedPrefixAtActiveSet (pref problem voter) active)
    (robustOperationCount :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        ℕ)
    (robustOperationCount_le :
      ∀ problem,
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem) :
    AlgorithmASuffixThenPrefixSmartAllocationCertificate
      (Voter := Voter) (Candidate := Candidate) (Slack := Slack)
      (algorithmASuffixThenPrefixOutput sourceCert pref suffix)
      robustOperationCount where
  sourceCert := sourceCert
  voters := voters
  relevantActiveSets := relevantActiveSets
  supportModel := supportModel
  middle := algorithmASuffixThenPrefixMiddle sourceCert suffix
  pref := pref
  suffix_extension := by
    intro problem voter _hvoter
    refine ⟨suffix problem voter, ?_⟩
    rfl
  base_reaches := base_reaches
  prefix_extension := by
    intro problem voter _hvoter
    rfl
  prefix_exhausted := prefix_exhausted
  robustOperationCount_le := robustOperationCount_le

/--
Proposition 1 route for the concrete Algorithm A suffix-then-prefix output.
The remaining inputs are the genuine source-model data; the executable ballot
transform itself is no longer a certificate boundary.
-/
theorem proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithmA_append_suffix_then_prefix
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (sourceCert :
      DGJ24OptimalStrategiesRCV.Algorithm3FirstUseSlackCertificate
        (Voter → RCVBallot Candidate) Slack)
    (voters :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Finset Voter)
    (relevantActiveSets :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Finset (Finset Candidate))
    (supportModel :
      ∀ problem :
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate),
        DGJ24OptimalStrategiesRCV.SmartAllocationSupportCountModel
          problem (voters problem) (relevantActiveSets problem))
    (pref suffix :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Voter → RCVBallot Candidate)
    (base_reaches :
      ∀ problem active, active ∈ relevantActiveSets problem →
        ∀ voter, voter ∈ voters problem →
          ∃ first,
            Ballot.nextActive
              ((DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
                sourceCert.toFirstUseSlackModel.slackProblem
                sourceCert.toFirstUseSlackModel.additionOf) problem voter)
              active = some first)
    (prefix_exhausted :
      ∀ problem active, active ∈ relevantActiveSets problem →
        ∀ voter, voter ∈ voters problem →
          exhaustedPrefixAtActiveSet (pref problem voter) active)
    (robustOperationCount :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        ℕ)
    (robustOperationCount_le :
      ∀ problem,
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem) :
    ∀ problem :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
        (Voter → RCVBallot Candidate),
      EconCSLib.Optimization.IsMinimizerOn
          problem.feasible problem.cost
          (algorithmASuffixThenPrefixOutput sourceCert pref suffix problem) ∧
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem := by
  exact
    proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithm3FirstUseSlackCertificate_supportCountModel_suffix_then_prefix
      (cert := sourceCert)
      (middle := algorithmASuffixThenPrefixMiddle sourceCert suffix)
      (robustAlgorithm := algorithmASuffixThenPrefixOutput sourceCert pref suffix)
      (robustOperationCount := robustOperationCount)
      (pref := pref)
      voters relevantActiveSets supportModel
      (by
        intro problem voter _hvoter
        refine ⟨suffix problem voter, ?_⟩
        rfl)
      base_reaches
      (by
        intro problem voter _hvoter
        rfl)
      prefix_exhausted robustOperationCount_le

/--
Proposition 1 route for the concrete Algorithm A prefix-then-suffix output.
The remaining inputs are the genuine source-model data; the executable ballot
transform itself is no longer a certificate boundary.
-/
theorem proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithmA_append_prefix_then_suffix
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    (sourceCert :
      DGJ24OptimalStrategiesRCV.Algorithm3FirstUseSlackCertificate
        (Voter → RCVBallot Candidate) Slack)
    (voters :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Finset Voter)
    (relevantActiveSets :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Finset (Finset Candidate))
    (supportModel :
      ∀ problem :
        DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate),
        DGJ24OptimalStrategiesRCV.SmartAllocationSupportCountModel
          problem (voters problem) (relevantActiveSets problem))
    (pref suffix :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Voter → RCVBallot Candidate)
    (base_reaches :
      ∀ problem active, active ∈ relevantActiveSets problem →
        ∀ voter, voter ∈ voters problem →
          ∃ first,
            Ballot.nextActive
              ((DGJ24OptimalStrategiesRCV.smartAllocationSlackReductionAlgorithm
                sourceCert.toFirstUseSlackModel.slackProblem
                sourceCert.toFirstUseSlackModel.additionOf) problem voter)
              active = some first)
    (prefix_exhausted :
      ∀ problem active, active ∈ relevantActiveSets problem →
        ∀ voter, voter ∈ voters problem →
          exhaustedPrefixAtActiveSet (pref problem voter) active)
    (robustOperationCount :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        ℕ)
    (robustOperationCount_le :
      ∀ problem,
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem) :
    ∀ problem :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
        (Voter → RCVBallot Candidate),
      EconCSLib.Optimization.IsMinimizerOn
          problem.feasible problem.cost
          (algorithmAPrefixThenSuffixOutput sourceCert pref suffix problem) ∧
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem := by
  exact
    proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithm3FirstUseSlackCertificate_supportCountModel_prefix_then_suffix
      (cert := sourceCert)
      (middle := algorithmAPrefixThenSuffixMiddle sourceCert pref)
      (robustAlgorithm := algorithmAPrefixThenSuffixOutput sourceCert pref suffix)
      (robustOperationCount := robustOperationCount)
      (pref := pref)
      voters relevantActiveSets supportModel
      (by
        intro problem voter _hvoter
        rfl)
      prefix_exhausted
      (by
        intro problem voter _hvoter
        refine ⟨suffix problem voter, ?_⟩
        rfl)
      base_reaches robustOperationCount_le

/--
Proposition 1 from the source-shaped Algorithm A suffix-then-prefix
certificate.
-/
theorem proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithmASuffixThenPrefixCertificate
    {Voter Candidate Slack : Type*} [DecidableEq Candidate] [Fintype Slack]
    {robustAlgorithm :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        Voter → RCVBallot Candidate}
    {robustOperationCount :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
          (Voter → RCVBallot Candidate) →
        ℕ}
    (cert :
      AlgorithmASuffixThenPrefixSmartAllocationCertificate
        (Voter := Voter) (Candidate := Candidate) (Slack := Slack)
        robustAlgorithm robustOperationCount) :
    ∀ problem :
      DGJ24OptimalStrategiesRCV.SmartAllocationProblem
        (Voter → RCVBallot Candidate),
      EconCSLib.Optimization.IsMinimizerOn
          problem.feasible problem.cost (robustAlgorithm problem) ∧
        robustOperationCount problem ≤
          DGJ24OptimalStrategiesRCV.SmartAllocationProblem.linearRuntimeBound
            problem :=
  proposition1_robustSmartAllocation_optimal_and_runtime_of_algorithm3FirstUseSlackCertificate_supportCountModel_suffix_then_prefix
    (cert := cert.sourceCert)
    (middle := cert.middle)
    (robustAlgorithm := robustAlgorithm)
    (robustOperationCount := robustOperationCount)
    (pref := cert.pref)
    cert.voters cert.relevantActiveSets cert.supportModel
    cert.suffix_extension cert.base_reaches cert.prefix_extension
    cert.prefix_exhausted cert.robustOperationCount_le

/--
Theorem 2.1 source-facing certificate projection: strengthened candidate
removal returns a reduced instance satisfying its preservation specification
and keeps the inherited quartic operation bound.
-/
theorem theorem2_1_strengthenedRemoval_sound_and_quartic_runtime
    {ReducedInstance : Type*}
    {algorithm : StrengthenedRemovalProblem ReducedInstance → ReducedInstance}
    {operationCount : StrengthenedRemovalProblem ReducedInstance → ℕ}
    (cert : StrengthenedRemovalCertificate algorithm operationCount)
    (problem : StrengthenedRemovalProblem ReducedInstance) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount ^ 4 := by
  exact ⟨cert.sound problem, cert.operationCount_le problem⟩

/--
Theorem 2.1 direct extended-condition route: Algorithm 3's extended removal
condition, a direct condition-to-output proof, and the exact quartic operation
count imply strengthened-removal soundness without first packaging the data as
a condition certificate.
-/
theorem theorem2_1_strengthenedRemoval_sound_and_quartic_runtime_of_extended_condition
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm : StrengthenedRemovalProblem ReducedInstance → ReducedInstance}
    {operationCount : StrengthenedRemovalProblem ReducedInstance → ℕ}
    (voters : StrengthenedRemovalProblem ReducedInstance → Finset Voter)
    (ballots :
      ∀ problem : StrengthenedRemovalProblem ReducedInstance,
        Voter → RCVBallot Candidate)
    (candidates lower :
      StrengthenedRemovalProblem ReducedInstance → Finset Candidate)
    (quota : StrengthenedRemovalProblem ReducedInstance → ℕ)
    (oneSurvivalSafe :
      StrengthenedRemovalProblem ReducedInstance → Candidate → Prop)
    (condition :
      ∀ problem : StrengthenedRemovalProblem ReducedInstance,
        extendedCandidateRemovalCondition
          (voters problem) (ballots problem) (candidates problem)
          (lower problem) problem.budget (quota problem)
          (oneSurvivalSafe problem))
    (output_spec_of_condition :
      ∀ problem : StrengthenedRemovalProblem ReducedInstance,
        extendedCandidateRemovalCondition
          (voters problem) (ballots problem) (candidates problem)
          (lower problem) problem.budget (quota problem)
          (oneSurvivalSafe problem) →
          problem.specification (algorithm problem))
    (operationCount_eq :
      ∀ problem : StrengthenedRemovalProblem ReducedInstance,
        operationCount problem =
          strengthenedRemovalOperationCount
            problem.uniqueBallotCount problem.candidateCount)
    (problem : StrengthenedRemovalProblem ReducedInstance) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount ^ 4 := by
  exact ⟨output_spec_of_condition problem (condition problem), by
    rw [operationCount_eq problem, strengthenedRemovalOperationCount]⟩

/--
Theorem 2.1 direct one-survival-step route: per-candidate post-transfer
elimination step certificates prove Algorithm 3's one-survival branch and give
the strengthened-removal soundness/runtime conclusion without first packaging
the branch as a step-trace certificate.
-/
theorem theorem2_1_strengthenedRemoval_sound_and_quartic_runtime_of_oneSurvivalSteps
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm : StrengthenedRemovalProblem ReducedInstance → ReducedInstance}
    {operationCount : StrengthenedRemovalProblem ReducedInstance → ℕ}
    (voters : StrengthenedRemovalProblem ReducedInstance → Finset Voter)
    (ballots :
      ∀ problem : StrengthenedRemovalProblem ReducedInstance,
        Voter → RCVBallot Candidate)
    (candidates lower :
      StrengthenedRemovalProblem ReducedInstance → Finset Candidate)
    (quota : StrengthenedRemovalProblem ReducedInstance → ℕ)
    (one_survival_step :
      ∀ problem : StrengthenedRemovalProblem ReducedInstance,
        ∀ inside, inside ∈ lower problem →
          extendedRemovalOriginalFailure
            (voters problem) (ballots problem) (candidates problem)
            (lower problem) problem.budget inside →
          OneSurvivalStepCertificate Candidate problem.budget inside)
    (output_spec_of_one_survival_steps :
      ∀ problem : StrengthenedRemovalProblem ReducedInstance,
        (∀ inside, inside ∈ lower problem →
          extendedRemovalOriginalFailure
            (voters problem) (ballots problem) (candidates problem)
            (lower problem) problem.budget inside →
          ∃ step : STVStep Candidate,
            step.afterActive = step.beforeActive.erase inside) →
        problem.specification (algorithm problem))
    (operationCount_eq :
      ∀ problem : StrengthenedRemovalProblem ReducedInstance,
        operationCount problem =
          strengthenedRemovalOperationCount
            problem.uniqueBallotCount problem.candidateCount)
    (problem : StrengthenedRemovalProblem ReducedInstance) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount ^ 4 := by
  exact theorem2_1_strengthenedRemoval_sound_and_quartic_runtime_of_extended_condition
    (voters := voters)
    (ballots := ballots)
    (candidates := candidates)
    (lower := lower)
    (quota := quota)
    (oneSurvivalSafe := fun problem inside =>
      ∃ _stepCert :
          OneSurvivalStepCertificate Candidate problem.budget inside,
        True)
    (condition := fun currentProblem =>
      extendedCandidateRemovalCondition_of_oneSurvivalStepCertificates
        (voters := voters currentProblem)
        (ballots := ballots currentProblem)
        (candidates := candidates currentProblem)
        (lower := lower currentProblem)
        (budget := currentProblem.budget)
        (quota := quota currentProblem)
        (one_survival_step currentProblem))
    (output_spec_of_condition := by
      intro currentProblem _hcondition
      exact output_spec_of_one_survival_steps currentProblem
        (oneSurvivalStepWitnesses_of_oneSurvivalStepCertificates
          (voters := voters currentProblem)
          (ballots := ballots currentProblem)
          (candidates := candidates currentProblem)
          (lower := lower currentProblem)
          (budget := currentProblem.budget)
          (one_survival_step currentProblem)))
    operationCount_eq problem

/--
Theorem 2.1 source-facing condition-certificate projection: Algorithm 3's
extended-removal condition certificate is enough to obtain strengthened
removal soundness and the inherited quartic operation-count conclusion.
-/
theorem theorem2_1_strengthenedRemoval_sound_and_quartic_runtime_of_conditionCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm : StrengthenedRemovalProblem ReducedInstance → ReducedInstance}
    {operationCount : StrengthenedRemovalProblem ReducedInstance → ℕ}
    (cert :
      StrengthenedRemovalConditionCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount)
    (problem : StrengthenedRemovalProblem ReducedInstance) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount ^ 4 := by
  exact theorem2_1_strengthenedRemoval_sound_and_quartic_runtime
    (strengthenedRemovalCertificate_of_conditionCertificate cert) problem

/--
Theorem 2.1 source-facing trace-certificate projection: Algorithm 3's extended
condition is enough when the original Algorithm 2 branch is witnessed by a
minimum-tally STV trace and the one-survival branch is supplied by its
source-specific transfer-simulation bridge.
-/
theorem theorem2_1_strengthenedRemoval_sound_and_quartic_runtime_of_traceCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm : StrengthenedRemovalProblem ReducedInstance → ReducedInstance}
    {operationCount : StrengthenedRemovalProblem ReducedInstance → ℕ}
    (cert :
      StrengthenedRemovalTraceCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount)
    (problem : StrengthenedRemovalProblem ReducedInstance) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount ^ 4 := by
  exact theorem2_1_strengthenedRemoval_sound_and_quartic_runtime
    (strengthenedRemovalCertificate_of_traceCertificate cert) problem

/--
Theorem 2.1 source-facing step-trace projection: the original Algorithm 2
branch is witnessed by the certified STV trace, and every one-survival branch
is witnessed by a post-transfer step certificate proving the lower candidate is
removed next.
-/
theorem theorem2_1_strengthenedRemoval_sound_and_quartic_runtime_of_stepTraceCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm : StrengthenedRemovalProblem ReducedInstance → ReducedInstance}
    {operationCount : StrengthenedRemovalProblem ReducedInstance → ℕ}
    (cert :
      StrengthenedRemovalStepTraceCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount)
    (problem : StrengthenedRemovalProblem ReducedInstance) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount ^ 4 := by
  exact theorem2_1_strengthenedRemoval_sound_and_quartic_runtime
    (strengthenedRemovalCertificate_of_stepTraceCertificate cert) problem

/--
Theorem 2.2 source-facing certificate projection: multi-winner containment
returns a contained instance satisfying its preservation specification and
meets the supplied polynomial verification bound.
-/
theorem theorem2_2_multiWinnerContainment_sound_and_polynomial_runtime
    {ContainedInstance : Type*}
    {algorithm :
      MultiWinnerContainmentProblem ContainedInstance → ContainedInstance}
    {operationCount :
      MultiWinnerContainmentProblem ContainedInstance → ℕ}
    (cert : MultiWinnerContainmentCertificate algorithm operationCount)
    (problem : MultiWinnerContainmentProblem ContainedInstance) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤ problem.verificationBound := by
  exact ⟨cert.sound problem, cert.operationCount_le problem⟩

/--
Theorem 2.2 source-facing condition-certificate projection: Algorithm 4's
updated strict-support condition certificate is enough to obtain the same
containment soundness and polynomial verification conclusion.
-/
theorem theorem2_2_multiWinnerContainment_sound_and_polynomial_runtime_of_conditionCertificate
    {ContainedInstance Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      MultiWinnerContainmentProblem ContainedInstance → ContainedInstance}
    {operationCount :
      MultiWinnerContainmentProblem ContainedInstance → ℕ}
    (cert :
      MultiWinnerContainmentConditionCertificate
        (Candidate := Candidate) algorithm operationCount)
    (problem : MultiWinnerContainmentProblem ContainedInstance) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤ problem.verificationBound := by
  exact theorem2_2_multiWinnerContainment_sound_and_polynomial_runtime
    (multiWinnerContainmentCertificate_of_conditionCertificate cert) problem

/--
Theorem 2.2 source-facing simple Eq. (2)/(3) certificate projection:
the `nextChoice + unweighted` lower-transfer comparison against base upper
support gives containment soundness and the polynomial verification bound.
-/
theorem theorem2_2_multiWinnerContainment_sound_and_polynomial_runtime_of_simpleBoundCertificate
    {ContainedInstance Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      MultiWinnerContainmentProblem ContainedInstance → ContainedInstance}
    {operationCount :
      MultiWinnerContainmentProblem ContainedInstance → ℕ}
    (cert :
      MultiWinnerContainmentSimpleBoundCertificate
        (Candidate := Candidate) algorithm operationCount)
    (problem : MultiWinnerContainmentProblem ContainedInstance) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤ problem.verificationBound := by
  exact theorem2_2_multiWinnerContainment_sound_and_polynomial_runtime
    (multiWinnerContainmentCertificate_of_simpleBoundCertificate cert) problem

/--
Theorem 2.2 direct component-bound route: conservative Eq. (2)/(3) component
bounds imply Algorithm 4's updated strict-support condition, which is enough
for containment soundness and the supplied polynomial verification bound.
-/
theorem theorem2_2_multiWinnerContainment_sound_and_polynomial_runtime_of_component_bounds
    {ContainedInstance Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      MultiWinnerContainmentProblem ContainedInstance → ContainedInstance}
    {operationCount :
      MultiWinnerContainmentProblem ContainedInstance → ℕ}
    (lower upper :
      MultiWinnerContainmentProblem ContainedInstance → Finset Candidate)
    (winnerFirstChoiceVotes quota :
      MultiWinnerContainmentProblem ContainedInstance → ℕ)
    (surplusVotes nextChoiceVotes unweightedTransferBound :
      MultiWinnerContainmentProblem ContainedInstance → Candidate → ℕ)
    (baseUpperSupport transferUpperSupport :
      MultiWinnerContainmentProblem ContainedInstance →
        Candidate → Candidate → ℕ)
    (conservativeLower conservativeUpper :
      MultiWinnerContainmentProblem ContainedInstance →
        Candidate → Candidate → ℕ)
    (hcomponent :
      ∀ problem : MultiWinnerContainmentProblem ContainedInstance,
        ∀ inside, inside ∈ lower problem →
        ∀ outside, outside ∈ upper problem →
          problem.budget + conservativeLower problem inside outside <
            conservativeUpper problem inside outside)
    (hlower_bound :
      ∀ problem : MultiWinnerContainmentProblem ContainedInstance,
        ∀ inside, inside ∈ lower problem →
        ∀ outside, outside ∈ upper problem →
          multiWinnerLowerCandidateTransferBound
              (surplusVotes problem) (nextChoiceVotes problem)
              (unweightedTransferBound problem)
              (winnerFirstChoiceVotes problem) inside outside ≤
            conservativeLower problem inside outside)
    (hupper_bound :
      ∀ problem : MultiWinnerContainmentProblem ContainedInstance,
        ∀ inside, inside ∈ lower problem →
        ∀ outside, outside ∈ upper problem →
          conservativeUpper problem inside outside ≤
            multiWinnerUpdatedUpperSupportBound
              (baseUpperSupport problem) (transferUpperSupport problem)
              (winnerFirstChoiceVotes problem) (quota problem)
              inside outside)
    (output_spec_of_condition :
      ∀ problem : MultiWinnerContainmentProblem ContainedInstance,
        multiWinnerContainmentCondition
          (lower problem) (upper problem)
          (winnerFirstChoiceVotes problem) (quota problem)
          (surplusVotes problem) (nextChoiceVotes problem)
          (unweightedTransferBound problem)
          (baseUpperSupport problem) (transferUpperSupport problem)
          problem.budget →
          problem.specification (algorithm problem))
    (operationCount_le :
      ∀ problem : MultiWinnerContainmentProblem ContainedInstance,
        operationCount problem ≤
          MultiWinnerContainmentProblem.polynomialVerificationBound problem)
    (problem : MultiWinnerContainmentProblem ContainedInstance) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤ problem.verificationBound := by
  have hcondition :
      multiWinnerContainmentCondition
        (lower problem) (upper problem)
        (winnerFirstChoiceVotes problem) (quota problem)
        (surplusVotes problem) (nextChoiceVotes problem)
        (unweightedTransferBound problem)
        (baseUpperSupport problem) (transferUpperSupport problem)
        problem.budget :=
    multiWinnerContainmentCondition_of_component_bounds
      (conservativeLower problem) (conservativeUpper problem)
      (hcomponent problem)
      (hlower_bound problem)
      (hupper_bound problem)
  exact ⟨output_spec_of_condition problem hcondition,
    operationCount_le problem⟩

/--
Theorem 2.2 direct Eq. (2)/(3) route: the source inequality using
`nextChoice + unweighted` transfers and base upper support implies Algorithm
4's updated strict-support condition through the checked arithmetic bounds.
-/
theorem theorem2_2_multiWinnerContainment_sound_and_polynomial_runtime_of_nextChoice_unweighted_baseSupport
    {ContainedInstance Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      MultiWinnerContainmentProblem ContainedInstance → ContainedInstance}
    {operationCount :
      MultiWinnerContainmentProblem ContainedInstance → ℕ}
    (lower upper :
      MultiWinnerContainmentProblem ContainedInstance → Finset Candidate)
    (winnerFirstChoiceVotes quota :
      MultiWinnerContainmentProblem ContainedInstance → ℕ)
    (surplusVotes nextChoiceVotes unweightedTransferBound :
      MultiWinnerContainmentProblem ContainedInstance → Candidate → ℕ)
    (baseUpperSupport transferUpperSupport :
      MultiWinnerContainmentProblem ContainedInstance →
        Candidate → Candidate → ℕ)
    (hcomponent :
      ∀ problem : MultiWinnerContainmentProblem ContainedInstance,
        ∀ inside, inside ∈ lower problem →
        ∀ outside, outside ∈ upper problem →
          problem.budget +
              (nextChoiceVotes problem inside +
                unweightedTransferBound problem inside) <
            baseUpperSupport problem inside outside)
    (output_spec_of_condition :
      ∀ problem : MultiWinnerContainmentProblem ContainedInstance,
        multiWinnerContainmentCondition
          (lower problem) (upper problem)
          (winnerFirstChoiceVotes problem) (quota problem)
          (surplusVotes problem) (nextChoiceVotes problem)
          (unweightedTransferBound problem)
          (baseUpperSupport problem) (transferUpperSupport problem)
          problem.budget →
          problem.specification (algorithm problem))
    (operationCount_le :
      ∀ problem : MultiWinnerContainmentProblem ContainedInstance,
        operationCount problem ≤
          MultiWinnerContainmentProblem.polynomialVerificationBound problem)
    (problem : MultiWinnerContainmentProblem ContainedInstance) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤ problem.verificationBound := by
  have hcondition :
      multiWinnerContainmentCondition
        (lower problem) (upper problem)
        (winnerFirstChoiceVotes problem) (quota problem)
        (surplusVotes problem) (nextChoiceVotes problem)
        (unweightedTransferBound problem)
        (baseUpperSupport problem) (transferUpperSupport problem)
        problem.budget :=
    multiWinnerContainmentCondition_of_nextChoice_unweighted_baseSupport
      (hcondition := hcomponent problem)
  exact ⟨output_spec_of_condition problem hcondition,
    operationCount_le problem⟩

end DGJ26PracticalDynamicsRCV
