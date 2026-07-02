import EconCSLib.Foundations.Math.FiniteSum
import EconCSLib.Foundations.Optimization.Certificate
import EconCSLib.SocialChoice.Voting

/-!
# Paper-Facing Theorems: Optimal Strategies in Ranked-Choice Voting

This file is the implementation theorem layer for the source paper. Keep
source-faithful definitions and theorem wrappers here, and expose only the
compact human-review subset in `PaperInterface.lean`.

## Main declarations

- `RCVStructure`: source-facing order-and-sequence structures.
- `reduceBallotByCandidates`: candidate-removal operation from Algorithm 4.
- `lemmaC1_reducedBallots_activeSupport_card_eq`: Lemma C.1 ballot-reduction
  support-count invariance.
- `lemmaC1_reducedBallots_activeSupport_card_eq_of_terminal_depleted`:
  terminal-depletion form of Lemma C.1.
- `strictSupportCount`: Definition C.2 strict-support count.
- `candidateGroupRemovalCondition`: Algorithm 6 candidate-group removal
  inequality.
- `RCVStructureConstraints`: nonlinear structure-region constraints.
- `rcvStructureConstraintCharacterization`: Appendix B.2-style correctness of
  a deterministic structure classifier.
- `rcvStructurePartition`: the Proposition 2.1 single-structure partition
  condition.
- `rcvStructureOutcomeAgreement`: direct STV/constraint agreement.
- `proposition2_1_existsUnique_structure_of_partition`: Proposition 2.1
  uniqueness consequence.
- `proposition2_1_existsUnique_structure_of_characterization`: Proposition
  2.1 uniqueness from a deterministic constraint characterization.
- `theoremB1_unique_finalOrder_of_structurePartition`: well-defined final
  social choice order from a structure partition.
- `theoremB1_unique_finalOrder_of_constraintCharacterization`: well-defined
  final social choice order from a deterministic constraint characterization.
- `lemmaB2_roundWinning_never_electionLoser_of_subset`: closed set-theoretic
  core of Lemma B.2.
- `proposition3_3_winCount_le_of_roundWinners_subset_electionWinners`: closed
  sequence win-count bound used by Proposition 3.3.
- `proposition3_3_feasibleSequence_count_le_sum_choose`: Proposition 3.3
  binomial enumeration of feasible win/loss sequences.
- `theorem3_1_smartAllocation_optimal_and_linear_runtime`: Theorem 3.1
  certificate interface for optimal strategic additions to a target structure.
- `SmartAllocationLowerBoundCertificate`: source-shaped lower-bound route for
  the SmartAllocation optimality proof.
- `SmartAllocationSlackFillingProblem`: componentwise slack-filling core of
  the SmartAllocation proof.
- `theorem3_1_smartAllocation_slackFilling_optimal_and_linear_runtime`:
  checked optimality/runtime theorem for exact componentwise slack filling.
- `ReducedElectionInstance` / `reduceElectionInstanceByCandidates`: concrete
  Algorithm 4 reduced-election output.
- `theorem3_2_irrelevantCandidateRemoval_sound_and_quartic_runtime`: Theorem
  3.2 candidate-reduction certificate interface.
- `IrrelevantCandidateRemovalConditionCertificate`: source-shaped Algorithm 6
  condition certificate for irrelevant-candidate removal.
- `irrelevantCandidateRemovalTraceCertificate_activeGroup_card_add_one_eq`:
  Algorithm 6 trace-certificate projection to exact active-group cardinality
  drops.
- `IrrelevantCandidateRemovalReplayCertificate`: source-shaped Appendix C.2
  replay route from group-elimination traces to terminal group depletion.
- `algorithm6_replay_terminal_depleted_and_activeSupport_preserved`:
  certificate-free Algorithm 6/Lemma C.1 replay bridge.
- `algorithm6_replay_reduceElectionInstance_sound_and_quartic_runtime`:
  certificate-free concrete Algorithm 4/6 preservation and runtime theorem.
- `proposition3_4_sequenceReduction_sound_and_quadratic_runtime`: Proposition
  3.4 sequence-reduction certificate interface.
- `predictWinsCandidates` / `predictLossesCandidates`: Algorithm 7
  strict-support filters.
- `predictWinsSupport`: Algorithm 7 ordered strict-support accumulator.
- `boundedSequenceFamily_covers_of_sequenceBoundsCover`: closed coverage
  theorem from Algorithm 7 bounds.
- `boundedSequenceFamily_subset_allSequences`: the retained family is a
  subfamily of the original sequence search space.
- `proposition3_4_boundedSequenceFamily_covers_and_quadraticRuntime_of_predictionCapacity`:
  certificate-free Proposition 3.4 route from Algorithm 7 capacity/loss-floor
  bounds to retained-family coverage and the quadratic operation-count model.
- `SequenceReductionConditionCertificate`: source-shaped Algorithm 7 coverage
  certificate.
- `SequenceReductionPredictionCertificate`: source-shaped Algorithm 7
  capacity/loss-floor certificate.
- `SequenceReductionQuotaBlockCertificate`: source-shaped Algorithm 7
  quota-block certificate deriving the win-capacity premise.
- `sequenceBoundsCover_of_quotaBlocks`: closed Algorithm 7 coverage theorem
  from disjoint quota-sized support blocks.
- `benefitsViaAction`: Definition 5.1 active-vote benefit predicate.
- `proposition5_3_individual_no_benefit_of_prefix_preservation`: ballot-prefix
  preservation bridge for Proposition 5.3.
- `proposition5_3_individual_no_benefit_of_active_gate_preservation`:
  active-gate preservation bridge for coalition edits.
- `proposition5_3_coalition_not_all_benefit_of_member_active_gate_preservation`:
  coalition bridge from one member and active gate preservation.
- `proposition5_3_coalition_not_all_benefit_of_exitRank`: finite exit-rank
  constructor for the first-exiting coalition-member bridge.
- `proposition5_3_coalition_not_all_benefit_of_roundRank`: round-rank
  constructor for the finite exit-rank bridge.
- `theorem5_4_strategy_characterization_of_shape_bridges`: Theorem 5.4
  characterization from visible shape bridge obligations.
- `theorem5_4_strategy_characterization_of_certificate`: Theorem 5.4 strategy
  shape characterization interface.
- `theorem5_4_strategy_characterization_of_cost_dominance`: Appendix E
  dominance bridge from lower-cost replacements for `other` strategies.
- `theorem5_4_strategy_characterization_of_replacement_certificate`: Appendix
  E split-replacement certificate bridge for `other` strategies.
- `AltruisticWinnerCaseACertificate`: source-shaped Case-(A) certificate for
  altruistic-to-winners strategies.
- `proposition5_3_individual_no_benefit_of_no_active_vote_increase`: closed
  logical core of Proposition 5.3.
- `proposition5_5_uncertainty_coalition_benefit_of_statewise_active_gate`:
  statewise active-gate bridge for Proposition 5.5.
- `proposition5_5_uncertainty_coalition_benefit_of_statewise_exitRank`:
  statewise exit-rank bridge for Proposition 5.5.
- `proposition5_5_uncertainty_coalition_benefit_of_statewise_roundRank`:
  statewise round-rank bridge for Proposition 5.5.
- `proposition5_5_uncertainty_coalition_benefit`: Proposition 5.5 uncertainty
  interface.
- `eliminatedEarlyByMarginLessThanAddedVotes`: Proposition 5.6 concrete
  non-selfish downside witness.
- `proposition5_6_selfish_beneficial_other_may_disadvantage`: Proposition 5.6
  robustness interface.
-/

namespace DGJ24OptimalStrategiesRCV

open EconCSLib.SocialChoice.Voting
open scoped BigOperators

/-- Source-facing alias for the ranked ballots used in the STV/RCV model. -/
abbrev RCVBallot (Candidate : Type*) := Ballot Candidate

/--
Source-facing Algorithm 4 ballot reduction: remove each candidate in `removed`
from the ballot while preserving the order of all remaining candidates.
-/
def reduceBallotByCandidates {Candidate : Type*} [DecidableEq Candidate]
    (removed : Finset Candidate) (ballot : RCVBallot Candidate) :
    RCVBallot Candidate :=
  Ballot.removeCandidates removed ballot

/--
Lemma C.1 ballot-level core: after a candidate set has been removed, the next
active candidate is exactly the next active candidate of the original ballot
with the same set absent from the active set.
-/
theorem lemmaC1_reducedBallot_nextActive_eq {Candidate : Type*}
    [DecidableEq Candidate]
    (ballot : RCVBallot Candidate) (active removed : Finset Candidate) :
    Ballot.nextActive (reduceBallotByCandidates removed ballot)
        (active \ removed) =
      Ballot.nextActive ballot (active \ removed) := by
  exact Ballot.nextActive_removeCandidates_sdiff ballot active removed

/--
Lemma C.1 vote-count core: reducing every ballot by the eliminated candidate
set preserves every remaining candidate's active-support count once the active
set is reduced by the same eliminated set.
-/
theorem lemmaC1_reducedBallots_activeSupport_card_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (active removed : Finset Candidate) (candidate : Candidate) :
    (Ballot.activeSupport voters
        (fun voter => reduceBallotByCandidates removed (ballots voter))
        (active \ removed) candidate).card =
      (Ballot.activeSupport voters ballots (active \ removed) candidate).card := by
  exact Ballot.activeSupport_card_removeCandidates_sdiff_eq

/--
Lemma C.1 terminal-depletion form: once the removed group is no longer active,
reducing every ballot by that group preserves later-round active-support counts
on the terminal active set.
-/
theorem lemmaC1_reducedBallots_activeSupport_card_eq_of_terminal_depleted
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    {terminalActive removed : Finset Candidate} (candidate : Candidate)
    (hdepleted : terminalActive ∩ removed = ∅) :
    (Ballot.activeSupport voters
        (fun voter => reduceBallotByCandidates removed (ballots voter))
        terminalActive candidate).card =
      (Ballot.activeSupport voters ballots terminalActive candidate).card := by
  exact Ballot.activeSupport_card_removeCandidates_eq_of_disjoint_active
    (voters := voters) (ballots := ballots) (active := terminalActive)
    (removed := removed) (candidate := candidate) hdepleted

/--
Definition C.2 strict-support count: voters whose first-ranked candidate lies
in `sources` and whose first active candidate among `candidate` and `blockers`
is `candidate`.
-/
def strictSupportCount {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (sources blockers : Finset Candidate) (candidate : Candidate) : ℕ :=
  Ballot.strictSupportCount voters ballots sources blockers candidate

/--
Algorithm 6 group-removal inequality condition.

The group `group` is removable when every inside candidate's strict support
plus the addition budget remains below quota, and every outside candidate's
strict support after transfers from `group \ {inside}` still dominates that
inside candidate while also staying below quota.
-/
def candidateGroupRemovalCondition {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates group : Finset Candidate) (budget quota : ℕ) : Prop :=
  strictSupportGroupRemovalCondition
    voters ballots candidates group budget quota

/--
Algorithm 6 safety conclusion split into the three inequalities used by the
proof: group candidates remain below quota, every possible last group
candidate remains below each outside candidate after transfers, and those
outside candidates remain below quota.
-/
def candidateGroupRemovalSafety {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates group : Finset Candidate) (budget quota : ℕ) : Prop :=
  strictSupportGroupRemovalSafety
    voters ballots candidates group budget quota

/--
The Algorithm 6 group-removal condition entails the separated safety
inequalities used in the Theorem 3.2 proof.
-/
theorem candidateGroupRemovalSafety_of_condition {Voter Candidate : Type*}
    [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hcondition :
      candidateGroupRemovalCondition
        voters ballots candidates group budget quota) :
    candidateGroupRemovalSafety voters ballots candidates group budget quota := by
  exact strictSupportGroupRemovalSafety_of_condition hcondition

/--
The separated Algorithm 6 safety inequalities reconstruct the compact
group-removal condition.
-/
theorem candidateGroupRemovalCondition_of_safety {Voter Candidate : Type*}
    [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      candidateGroupRemovalSafety
        voters ballots candidates group budget quota) :
    candidateGroupRemovalCondition voters ballots candidates group budget quota := by
  rcases hsafety with ⟨hbelow_quota, hdominates, houtside_quota⟩
  exact ⟨hbelow_quota, by
    intro inside hinside outside houtside
    exact ⟨hdominates inside hinside outside houtside,
      houtside_quota inside hinside outside houtside⟩⟩

/--
Executable Algorithm 6 group-removal condition.  It checks the finite
strict-support inequalities for every inside candidate and every outside
candidate.
-/
noncomputable def candidateGroupRemovalConditionCheck {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates group : Finset Candidate) (budget quota : ℕ) : Bool :=
  group.toList.all fun inside =>
    decide
        (budget + strictSupportCount voters ballots group
          (candidates \ group) inside < quota) &&
      (candidates \ group).toList.all fun outside =>
        decide
            (budget + strictSupportCount voters ballots group
              (candidates \ group) inside <
              strictSupportCount voters ballots
                (insert outside (group.erase inside)) (∅ : Finset Candidate)
                outside) &&
          decide
            (strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside < quota)

/--
A successful finite Algorithm 6 group-removal checker supplies the paper's
group-removal condition.
-/
theorem candidateGroupRemovalCondition_of_check_eq_true
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hcheck :
      candidateGroupRemovalConditionCheck voters ballots candidates group
        budget quota = true) :
    candidateGroupRemovalCondition voters ballots candidates group budget
      quota := by
  classical
  constructor
  · intro inside hinside
    have hinside_all :=
      (List.all_eq_true.mp hcheck) inside (Finset.mem_toList.mpr hinside)
    have hparts :
        decide
            (budget + strictSupportCount voters ballots group
              (candidates \ group) inside < quota) = true ∧
          ((candidates \ group).toList.all fun outside =>
            decide
                (budget + strictSupportCount voters ballots group
                  (candidates \ group) inside <
                  strictSupportCount voters ballots
                    (insert outside (group.erase inside))
                    (∅ : Finset Candidate) outside) &&
              decide
                (strictSupportCount voters ballots
                  (insert outside (group.erase inside))
                  (∅ : Finset Candidate) outside < quota)) = true := by
      simpa [candidateGroupRemovalConditionCheck,
        Bool.and_eq_true_eq_eq_true_and_eq_true] using hinside_all
    exact decide_eq_true_iff.mp hparts.1
  · intro inside hinside outside houtside
    have hinside_all :=
      (List.all_eq_true.mp hcheck) inside (Finset.mem_toList.mpr hinside)
    have hparts :
        decide
            (budget + strictSupportCount voters ballots group
              (candidates \ group) inside < quota) = true ∧
          ((candidates \ group).toList.all fun outside =>
            decide
                (budget + strictSupportCount voters ballots group
                  (candidates \ group) inside <
                  strictSupportCount voters ballots
                    (insert outside (group.erase inside))
                    (∅ : Finset Candidate) outside) &&
              decide
                (strictSupportCount voters ballots
                  (insert outside (group.erase inside))
                  (∅ : Finset Candidate) outside < quota)) = true := by
      simpa [candidateGroupRemovalConditionCheck,
        Bool.and_eq_true_eq_eq_true_and_eq_true] using hinside_all
    have houtside_all :=
      (List.all_eq_true.mp hparts.2) outside
        (Finset.mem_toList.mpr houtside)
    have houtside_parts :
        decide
            (budget + strictSupportCount voters ballots group
              (candidates \ group) inside <
              strictSupportCount voters ballots
                (insert outside (group.erase inside)) (∅ : Finset Candidate)
                outside) = true ∧
          decide
            (strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside < quota) = true := by
      simpa [Bool.and_eq_true_eq_eq_true_and_eq_true] using houtside_all
    exact ⟨decide_eq_true_iff.mp houtside_parts.1,
      decide_eq_true_iff.mp houtside_parts.2⟩

/--
Algorithm 6 safety, read as a current-round tally fact: an inside candidate's
budget-augmented strict support is still below quota.
-/
theorem candidateGroupRemovalSafety_inside_tally_lt_quota
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      candidateGroupRemovalSafety voters ballots candidates group budget quota)
    {inside : Candidate} (hinside : inside ∈ group)
    {step : STVStep Candidate}
    (htally_inside :
      step.tally inside =
        budget +
          strictSupportCount voters ballots group (candidates \ group)
            inside) :
    step.tally inside < quota := by
  simpa [htally_inside] using hsafety.1 inside hinside

/--
Algorithm 6 safety, read as a current-round tally fact: an outside candidate's
strict support after transfers from `group \ {inside}` is still below quota.
-/
theorem candidateGroupRemovalSafety_outside_tally_lt_quota
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      candidateGroupRemovalSafety voters ballots candidates group budget quota)
    {inside outside : Candidate} (hinside : inside ∈ group)
    (houtside : outside ∈ candidates \ group)
    {step : STVStep Candidate}
    (htally_outside :
      step.tally outside =
        strictSupportCount voters ballots
          (insert outside (group.erase inside)) (∅ : Finset Candidate)
          outside) :
    step.tally outside < quota := by
  simpa [htally_outside] using hsafety.2.2 inside hinside outside houtside

/--
Algorithm 6 safety prevents an outside candidate from being eliminated by a
minimum-tally elimination step when some inside candidate is still active with
the Algorithm 6 tally interpretation.
-/
theorem candidateGroupRemovalSafety_outside_not_minimal_elimination_focus
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      candidateGroupRemovalSafety voters ballots candidates group budget quota)
    {inside outside : Candidate} (hinside : inside ∈ group)
    (houtside : outside ∈ candidates \ group)
    {step : STVStep Candidate}
    (hminimal : step.eliminatesMinimalTally)
    (hinside_active : inside ∈ step.beforeActive)
    (houtside_active : outside ∈ step.beforeActive)
    (htally_inside :
      step.tally inside =
        budget +
          strictSupportCount voters ballots group (candidates \ group)
            inside)
    (htally_outside :
    step.tally outside =
        strictSupportCount voters ballots
          (insert outside (group.erase inside)) (∅ : Finset Candidate)
          outside) :
    step.focus ≠ some outside := by
  exact strictSupportGroupRemovalSafety_outside_not_minimal_elimination_focus
    hsafety hinside houtside hminimal hinside_active houtside_active
    htally_inside htally_outside

/--
Algorithm 6 safety forces a minimum-tally elimination step to eliminate from
the removable group, provided some group candidate is still active and the
step tallies agree with the Algorithm 6 strict-support quantities.
-/
theorem candidateGroupRemovalSafety_minimal_elimination_focus_mem_group
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      candidateGroupRemovalSafety voters ballots candidates group budget quota)
    {inside : Candidate} (hinside : inside ∈ group)
    {step : STVStep Candidate}
    (hminimal : step.eliminatesMinimalTally)
    (hinside_active : inside ∈ step.beforeActive)
    (hactive_subset_candidates : step.beforeActive ⊆ candidates)
    (htally_inside :
      step.tally inside =
        budget +
          strictSupportCount voters ballots group (candidates \ group)
            inside)
    (htally_outside :
      ∀ outside, outside ∈ candidates \ group →
        step.tally outside =
          strictSupportCount voters ballots
            (insert outside (group.erase inside)) (∅ : Finset Candidate)
            outside) :
    ∃ loser, step.focus = some loser ∧ loser ∈ group ∧
      loser ∈ step.beforeActive := by
  exact strictSupportGroupRemovalSafety_minimal_elimination_focus_mem_group
    hsafety hinside hminimal hinside_active hactive_subset_candidates
    htally_inside htally_outside

/-- Source-facing alias for deterministic STV/RCV traces. -/
abbrev RCVTrace (Candidate : Type*) := STVTrace Candidate

/--
Algorithm 6 trace bridge: along any trace whose elimination steps choose
minimum-tally active candidates, the safety inequalities force every
elimination step considered by the certificate to remove a focused group
candidate.
-/
theorem candidateGroupRemovalSafety_trace_elimination_focus_mem_group
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      candidateGroupRemovalSafety voters ballots candidates group budget quota)
    {trace : RCVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots group (candidates \ group)
                inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside) :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      ∃ loser, step.focus = some loser ∧ loser ∈ group ∧
        loser ∈ step.beforeActive ∧
        step.afterActive = step.beforeActive.erase loser := by
  exact strictSupportGroupRemovalSafety_trace_elimination_focus_mem_group
    hsafety hminimal hremove hgroup_active hactive_subset_candidates
    htally_inside htally_outside

/--
Algorithm 6 trace bridge, predicate form: every certified minimum-tally
elimination removes a focused candidate from the removable group.
-/
theorem candidateGroupRemovalSafety_trace_eliminationRemovesFromGroup
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      candidateGroupRemovalSafety voters ballots candidates group budget quota)
    {trace : RCVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots group (candidates \ group)
                inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside) :
    trace.eliminationRemovesFromGroup group := by
  exact strictSupportGroupRemovalSafety_trace_eliminationRemovesFromGroup
    hsafety hminimal hremove hgroup_active hactive_subset_candidates
    htally_inside htally_outside

/--
Algorithm 6 trace bridge, cardinality form: every certified minimum-tally
elimination step strictly decreases the number of active candidates in the
removable group.
-/
theorem candidateGroupRemovalSafety_trace_elimination_activeGroup_card_decreases
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      candidateGroupRemovalSafety voters ballots candidates group budget quota)
    {trace : RCVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots group (candidates \ group)
                inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside) :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      (step.afterActive ∩ group).card <
        (step.beforeActive ∩ group).card := by
  exact strictSupportGroupRemovalSafety_trace_elimination_activeGroup_card_decreases
    hsafety hminimal hremove hgroup_active hactive_subset_candidates
    htally_inside htally_outside

/--
Algorithm 6 trace bridge, exact cardinality form: every certified
minimum-tally elimination step removes exactly one active candidate from the
removable group.
-/
theorem candidateGroupRemovalSafety_trace_elimination_activeGroup_card_add_one_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group : Finset Candidate} {budget quota : ℕ}
    (hsafety :
      candidateGroupRemovalSafety voters ballots candidates group budget quota)
    {trace : RCVTrace Candidate}
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots group (candidates \ group)
                inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside) :
    ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
      (step.afterActive ∩ group).card + 1 =
        (step.beforeActive ∩ group).card := by
  exact strictSupportGroupRemovalSafety_trace_elimination_activeGroup_card_add_one_eq
    hsafety hminimal hremove hgroup_active hactive_subset_candidates
    htally_inside htally_outside

/-- Source-facing alias for final winner/loser structures. -/
abbrev RCVWinLossStructure (Candidate : Type*) := WinLossStructure Candidate

/-- Source-facing alias for an STV order-and-sequence structure. -/
abbrev RCVStructure (Candidate : Type*) := OrderSequenceStructure Candidate

/-- Source-facing alias for generated STV round-tally constraints. -/
abbrev RCVRoundTallyConstraint (Candidate : Type*) :=
  RoundTallyConstraint Candidate

/-- Source-facing alias for the win/loss sequence in an RCV structure. -/
abbrev RCVSequence := List RoundOutcome

/-- Source-facing fixed-length win/loss sequence with one label per round. -/
abbrev RCVFixedLengthSequence (rounds : ℕ) := Fin rounds → RoundOutcome

/--
Finite search space of all win/loss sequences with exactly `rounds` labels.
This is the concrete Algorithm 7 universe when the source has already bounded
the election to a fixed number of rounds.
-/
def rcvAllFixedLengthSequences (rounds : ℕ) : Finset RCVSequence :=
  (Finset.univ : Finset (RCVFixedLengthSequence rounds)).image
    (fun sequence => List.ofFn sequence)

/-- Every win/loss list of the advertised length is in the fixed-length search space. -/
theorem mem_rcvAllFixedLengthSequences_of_length_eq
    {rounds : ℕ} {sequence : RCVSequence}
    (hlength : sequence.length = rounds) :
    sequence ∈ rcvAllFixedLengthSequences rounds := by
  classical
  subst rounds
  refine Finset.mem_image.mpr
    ⟨fun i : Fin sequence.length => sequence.get i,
      Finset.mem_univ _, ?_⟩
  exact List.ofFn_get sequence

/-- Number of round-winning labels in a source-facing RCV sequence. -/
def rcvSequenceWinCount (sequence : RCVSequence) : ℕ :=
  RoundOutcome.winCount sequence

/-- Number of consecutive round-losing labels at the start of an RCV sequence. -/
def rcvSequenceInitialLossCount (sequence : RCVSequence) : ℕ :=
  RoundOutcome.initialLossCount sequence

/- The first `length` labels of an RCV sequence are losses. -/
def rcvSequenceHasInitialLossPrefix
    (sequence : RCVSequence) (length : ℕ) : Prop :=
  RoundOutcome.HasInitialLossPrefix sequence length

/--
If the first `lossPrefix.length` labels of an RCV win/loss sequence are losing
rounds, then that candidate prefix length is bounded by the sequence's
initial-loss count.
-/
theorem lossPrefix_length_le_rcvSequenceInitialLossCount_of_initialLossPrefix
    {Candidate : Type*} {sequence : RCVSequence}
    {lossPrefix : List Candidate}
    (hprefix :
      rcvSequenceHasInitialLossPrefix sequence lossPrefix.length) :
    lossPrefix.length ≤ rcvSequenceInitialLossCount sequence :=
  RoundOutcome.length_le_initialLossCount_of_hasInitialLossPrefix hprefix

/-- The win/loss sequence read from a deterministic source RCV trace. -/
def rcvSequenceFromTrace {Candidate : Type*} (trace : RCVTrace Candidate) :
    RCVSequence :=
  STVTrace.roundOutcomeSequence trace

/--
A source trace whose first `length` steps are eliminations supplies the
initial-loss prefix predicate used by Algorithm 7's sequence bounds.
-/
theorem rcvSequenceHasInitialLossPrefix_of_trace_initialEliminationPrefix
    {Candidate : Type*} {trace : RCVTrace Candidate} {sequence : RCVSequence}
    {length : ℕ}
    (hsequence : sequence = rcvSequenceFromTrace trace)
    (hprefix : trace.HasInitialEliminationPrefix length) :
    rcvSequenceHasInitialLossPrefix sequence length := by
  subst sequence
  exact
    STVTrace.hasInitialLossPrefix_roundOutcomeSequence_of_initialEliminationPrefix
      hprefix

/--
A source trace whose first steps eliminate the candidates in `lossPrefix`
supplies the initial-loss prefix predicate used by Algorithm 7's sequence
bounds.
-/
theorem rcvSequenceHasInitialLossPrefix_of_trace_initialEliminationFocusPrefix
    {Candidate : Type*} {trace : RCVTrace Candidate} {sequence : RCVSequence}
    {lossPrefix : List Candidate}
    (hsequence : sequence = rcvSequenceFromTrace trace)
    (hprefix : trace.HasInitialEliminationFocusPrefix lossPrefix) :
    rcvSequenceHasInitialLossPrefix sequence lossPrefix.length := by
  exact
    rcvSequenceHasInitialLossPrefix_of_trace_initialEliminationPrefix
      hsequence
      (STVTrace.hasInitialEliminationPrefix_of_initialEliminationFocusPrefix
        hprefix)

/--
Concrete source trace steps, checked by index, package into the focused
initial-elimination prefix used by Algorithm 7.
-/
theorem rcvTraceHasInitialEliminationFocusPrefix_of_getElem
    {Candidate : Type*} {trace : RCVTrace Candidate}
    {lossPrefix : List Candidate}
    (hlen : lossPrefix.length ≤ trace.steps.length)
    (hfocus :
      ∀ i : Fin lossPrefix.length,
        (trace.steps.get
          ⟨i.1, Nat.lt_of_lt_of_le i.2 hlen⟩).focus =
          some (lossPrefix.get i))
    (hkind :
      ∀ i : Fin lossPrefix.length,
        (trace.steps.get
          ⟨i.1, Nat.lt_of_lt_of_le i.2 hlen⟩).kind =
          StepKind.eliminate) :
    trace.HasInitialEliminationFocusPrefix lossPrefix :=
  STVTrace.hasInitialEliminationFocusPrefix_of_getElem hlen hfocus hkind

/--
Canonical profile-tally generated group-elimination trace.  This is the
paper-facing deterministic replay convention for lower groups when ordinary
active-support ballot counts and canonical minimum-tally tie-breaking are used.
-/
noncomputable def rcvCanonicalProfileGroupEliminationGeneratedTrace
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (group : Finset Candidate) (rounds : ℕ)
    (initialActive : Finset Candidate) :
    RCVTrace Candidate :=
  canonicalProfileGroupEliminationGeneratedTrace voters ballots group rounds
    initialActive

/--
Canonical profile-tally generated group-elimination traces have an
initial-elimination prefix of any length bounded by the generated run length.
-/
theorem rcvCanonicalProfileGroupEliminationGeneratedTrace_initialEliminationPrefix_of_le
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (group : Finset Candidate)
    {rounds length : ℕ} {initialActive : Finset Candidate}
    (hlength : length ≤ rounds)
    (hrounds : rounds = (initialActive ∩ group).card) :
    (rcvCanonicalProfileGroupEliminationGeneratedTrace voters ballots group
        rounds initialActive).HasInitialEliminationPrefix length := by
  exact
    STVTrace.canonicalProfileGroupEliminationGeneratedTrace_hasInitialEliminationPrefix_of_le
      voters ballots group hlength hrounds

/--
Canonical profile-tally generated group-elimination traces have the full
generated run as an initial-elimination prefix.
-/
theorem rcvCanonicalProfileGroupEliminationGeneratedTrace_initialEliminationPrefix
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (group : Finset Candidate)
    {rounds : ℕ} {initialActive : Finset Candidate}
    (hrounds : rounds = (initialActive ∩ group).card) :
    (rcvCanonicalProfileGroupEliminationGeneratedTrace voters ballots group
        rounds initialActive).HasInitialEliminationPrefix rounds :=
  rcvCanonicalProfileGroupEliminationGeneratedTrace_initialEliminationPrefix_of_le
    voters ballots group le_rfl hrounds

/--
Source-facing family of nonlinear constraints defining the ballot-space region
for each order-and-sequence structure.
-/
abbrev RCVStructureConstraints (Data Candidate : Type*) :=
  StructureConstraints Data (RCVStructure Candidate)

/--
Appendix B.2-style correctness of generated structure constraints: a
deterministic tie-broken classifier picks the unique order-and-sequence
structure whose constraints contain the voter-data point.
-/
def rcvStructureConstraintCharacterization {Data Candidate : Type*}
    (structureOf : Data → RCVStructure Candidate)
    (constraints : RCVStructureConstraints Data Candidate) : Prop :=
  StructureConstraintCharacterization structureOf constraints

/--
Appendix B.2 canonical generated constraints from a deterministic
order-and-sequence structure classifier.
-/
def rcvStructureClassifierConstraints {Data Candidate : Type*}
    (structureOf : Data → RCVStructure Candidate) :
    RCVStructureConstraints Data Candidate :=
  classifierStructureConstraints structureOf

/--
Appendix B.2 / Algorithms 1-2 structure read from a concrete deterministic
STV trace generator: the structure's final order is read by `finalOrderOf`,
and its win/loss sequence is the trace's round-outcome sequence.
-/
def rcvStructureOfTrace {Data Candidate : Type*}
    (traceOf : Data → RCVTrace Candidate)
    (finalOrderOf : Data → FinalOrder Candidate) :
    Data → RCVStructure Candidate :=
  traceStructureOf traceOf finalOrderOf

/--
Appendix B.2 / Algorithms 1-2 concrete trace-generated constraints.  These are
the structure constraints obtained by running the deterministic trace update
algorithm and reading the resulting final order and per-round win/loss labels.
-/
def rcvTraceGeneratedStructureConstraints {Data Candidate : Type*}
    (traceOf : Data → RCVTrace Candidate)
    (finalOrderOf : Data → FinalOrder Candidate) :
    RCVStructureConstraints Data Candidate :=
  traceStructureConstraints traceOf finalOrderOf

/--
Appendix B.2 / Algorithms 1-2 concrete trace generated from a proposed
order-and-sequence structure.  The source-specific tally formula is supplied as
`tallyOf`; the reusable STV layer handles the elect/eliminate step sequence and
active-set update.
-/
def rcvGeneratedTraceOfStructure {Candidate : Type*} [DecidableEq Candidate]
    (struct : RCVStructure Candidate)
    (initialActive : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) :
    RCVTrace Candidate :=
  OrderSequenceStructure.generatedTrace struct initialActive tallyOf

/-- Terminal active set of the generated trace from an RCV structure. -/
def rcvGeneratedTraceTerminalActive {Candidate : Type*} [DecidableEq Candidate]
    (struct : RCVStructure Candidate)
    (initialActive : Finset Candidate) : Finset Candidate :=
  OrderSequenceStructure.generatedTraceTerminalActive struct initialActive

/-- The generated trace from an RCV structure has the structure's win/loss
sequence up to the final-order length. -/
theorem rcvGeneratedTrace_roundOutcomeSequence {Candidate : Type*}
    [DecidableEq Candidate]
    (struct : RCVStructure Candidate)
    (initialActive : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) :
    (rcvGeneratedTraceOfStructure struct initialActive tallyOf).roundOutcomeSequence =
      struct.sequence.take struct.finalOrder.order.length := by
  exact OrderSequenceStructure.roundOutcomeSequence_generatedTrace struct
    initialActive tallyOf

/-- If the structure has one outcome label per ordered candidate, the generated
trace has exactly the structure's win/loss sequence. -/
theorem rcvGeneratedTrace_roundOutcomeSequence_of_validLength
    {Candidate : Type*} [DecidableEq Candidate]
    {struct : RCVStructure Candidate}
    {initialActive : Finset Candidate}
    {tallyOf : Finset Candidate → Candidate → ℕ}
    (hvalid : struct.validLength) :
    (rcvGeneratedTraceOfStructure struct initialActive tallyOf).roundOutcomeSequence =
      struct.sequence := by
  exact OrderSequenceStructure.roundOutcomeSequence_generatedTrace_of_validLength
    (struct := struct) (initialActive := initialActive) (tallyOf := tallyOf)
    hvalid

/-- The generated source trace has one step for each paired order/sequence
entry. -/
theorem rcvGeneratedTrace_steps_length {Candidate : Type*}
    [DecidableEq Candidate]
    (struct : RCVStructure Candidate)
    (initialActive : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) :
    (rcvGeneratedTraceOfStructure struct initialActive tallyOf).steps.length =
      min struct.finalOrder.order.length struct.sequence.length := by
  exact OrderSequenceStructure.generatedTrace_steps_length struct
    initialActive tallyOf

/-- The generated source trace replays its active-set updates. -/
theorem rcvGeneratedTrace_replaysFrom {Candidate : Type*}
    [DecidableEq Candidate]
    (struct : RCVStructure Candidate)
    (initialActive : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) :
    (rcvGeneratedTraceOfStructure struct initialActive tallyOf).replaysFrom
      initialActive (rcvGeneratedTraceTerminalActive struct initialActive) := by
  exact OrderSequenceStructure.generatedTrace_replaysFrom struct initialActive
    tallyOf

/-- The generated source trace renders win/loss labels as elect/eliminate step
kinds. -/
theorem rcvGeneratedTrace_stepKinds {Candidate : Type*}
    [DecidableEq Candidate]
    (struct : RCVStructure Candidate)
    (initialActive : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) :
    (rcvGeneratedTraceOfStructure struct initialActive tallyOf).steps.map
        STVStep.kind =
      (struct.sequence.take struct.finalOrder.order.length).map
        RoundOutcome.toStepKind := by
  exact OrderSequenceStructure.generatedTrace_stepKinds struct
    initialActive tallyOf

/--
If a generated structure is valid and its full order prefix is labeled by wins,
then every decomposed source-order prefix points to an existing generated step.
-/
theorem rcvGeneratedTrace_index_lt_of_win_prefix
    {Candidate : Type*} [DecidableEq Candidate]
    {struct : RCVStructure Candidate}
    {initialActive : Finset Candidate}
    {tallyOf : Finset Candidate → Candidate → ℕ}
    {sourceOrder pref suffix : List Candidate} {candidate : Candidate}
    (horder : struct.finalOrder.order = sourceOrder)
    (hvalid : struct.validLength)
    (hdecomp : sourceOrder = pref ++ candidate :: suffix) :
    pref.length <
      (rcvGeneratedTraceOfStructure struct initialActive tallyOf).steps.length := by
  have hpref_lt : pref.length < sourceOrder.length := by
    rw [hdecomp]
    simp
  have horder_len :
      pref.length < struct.finalOrder.order.length := by
    simpa [horder] using hpref_lt
  have hsequence_len :
      pref.length < struct.sequence.length := by
    rw [OrderSequenceStructure.validLength] at hvalid
    rw [hvalid]
    exact horder_len
  rw [rcvGeneratedTrace_steps_length]
  exact lt_min horder_len hsequence_len

/--
If a generated structure is valid and its full order prefix is labeled by wins,
then every decomposed source-order prefix is an election step in the generated
trace.
-/
theorem rcvGeneratedTrace_get_kind_eq_elect_of_win_prefix
    {Candidate : Type*} [DecidableEq Candidate]
    {struct : RCVStructure Candidate}
    {initialActive : Finset Candidate}
    {tallyOf : Finset Candidate → Candidate → ℕ}
    {sourceOrder pref suffix : List Candidate} {candidate : Candidate}
    (horder : struct.finalOrder.order = sourceOrder)
    (hvalid : struct.validLength)
    (hwin_prefix :
      struct.sequence.take sourceOrder.length =
        List.replicate sourceOrder.length RoundOutcome.win)
    (hdecomp : sourceOrder = pref ++ candidate :: suffix) :
    (((rcvGeneratedTraceOfStructure struct initialActive tallyOf).steps.get
        ⟨pref.length,
          rcvGeneratedTrace_index_lt_of_win_prefix
            (struct := struct) (initialActive := initialActive)
            (tallyOf := tallyOf) horder hvalid hdecomp⟩).kind =
      StepKind.elect) := by
  let trace := rcvGeneratedTraceOfStructure struct initialActive tallyOf
  have hpref_lt : pref.length < sourceOrder.length := by
    rw [hdecomp]
    simp
  have hpref_lt_order :
      pref.length < struct.finalOrder.order.length := by
    simpa [horder] using hpref_lt
  have hkinds :=
    congrArg (fun xs : List StepKind => xs[pref.length]?)
      (rcvGeneratedTrace_stepKinds struct initialActive tallyOf)
  have hright :
      ((struct.sequence.take struct.finalOrder.order.length).map
          RoundOutcome.toStepKind)[pref.length]? =
        some StepKind.elect := by
    have hwin_prefix' :
        struct.sequence.take struct.finalOrder.order.length =
          List.replicate struct.finalOrder.order.length RoundOutcome.win := by
      simpa [horder] using hwin_prefix
    rw [hwin_prefix']
    simp [RoundOutcome.toStepKind, hpref_lt_order]
  have hidx :
      pref.length < trace.steps.length := by
    simpa [trace] using
      rcvGeneratedTrace_index_lt_of_win_prefix
        (struct := struct) (initialActive := initialActive)
        (tallyOf := tallyOf) horder hvalid hdecomp
  have hmap_get :
      (trace.steps.map STVStep.kind)[pref.length]? =
        some StepKind.elect := by
    have hkind_eq :
        (trace.steps.map STVStep.kind)[pref.length]? =
          ((struct.sequence.take struct.finalOrder.order.length).map
            RoundOutcome.toStepKind)[pref.length]? := by
      simpa [trace, List.map_take] using hkinds
    exact hkind_eq.trans hright
  have hstep_some :
      trace.steps[pref.length]? =
        some (trace.steps.get ⟨pref.length, hidx⟩) := by
    simpa using
      (List.getElem?_eq_getElem (l := trace.steps) (i := pref.length)
        hidx)
  simpa [hstep_some] using hmap_get

/-- Every generated source trace step removes its focused candidate. -/
theorem rcvGeneratedTrace_removesFocusedCandidate {Candidate : Type*}
    [DecidableEq Candidate]
    (struct : RCVStructure Candidate)
    (initialActive : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) :
    ∀ step,
      step ∈ (rcvGeneratedTraceOfStructure struct initialActive tallyOf).steps →
        step.removesFocusedCandidate := by
  exact OrderSequenceStructure.generatedTrace_removesFocusedCandidate struct
    initialActive tallyOf

/--
Appendix B.2 / Algorithms 1-2 generated round-tally constraints for a proposed
order-and-sequence structure.
-/
def rcvGeneratedStructureRoundConstraints {Candidate : Type*}
    [DecidableEq Candidate]
    (struct : RCVStructure Candidate)
    (initialActive : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) (quota : ℕ) :
    List (RCVRoundTallyConstraint Candidate) :=
  OrderSequenceStructure.generatedConstraints struct initialActive tallyOf quota

/--
The generated Appendix B.2 round constraints recover the proposed structure's
win/loss labels up to the final-order length.
-/
theorem rcvGeneratedStructureRoundConstraints_outcomes {Candidate : Type*}
    [DecidableEq Candidate]
    (struct : RCVStructure Candidate)
    (initialActive : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) (quota : ℕ) :
    (rcvGeneratedStructureRoundConstraints struct initialActive tallyOf quota).map
        RoundTallyConstraint.outcome =
      struct.sequence.take struct.finalOrder.order.length := by
  exact OrderSequenceStructure.generatedConstraints_outcomes struct
    initialActive tallyOf quota

/--
The generated Appendix B.2 round constraints have one row for each generated
trace step.
-/
theorem rcvGeneratedStructureRoundConstraints_length {Candidate : Type*}
    [DecidableEq Candidate]
    (struct : RCVStructure Candidate)
    (initialActive : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) (quota : ℕ) :
    (rcvGeneratedStructureRoundConstraints struct initialActive tallyOf
        quota).length =
      min struct.finalOrder.order.length struct.sequence.length := by
  exact OrderSequenceStructure.generatedConstraints_length struct initialActive
    tallyOf quota

/--
The generated Appendix B.2 round constraints use the same active sets as the
generated trace steps.
-/
theorem rcvGeneratedStructureRoundConstraints_active_eq_trace_beforeActive
    {Candidate : Type*} [DecidableEq Candidate]
    (struct : RCVStructure Candidate)
    (initialActive : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) (quota : ℕ) :
    (rcvGeneratedStructureRoundConstraints struct initialActive tallyOf
        quota).map RoundTallyConstraint.active =
      (rcvGeneratedTraceOfStructure struct initialActive tallyOf).steps.map
        STVStep.beforeActive := by
  exact OrderSequenceStructure.generatedConstraints_active_eq_generatedTrace_beforeActive
    struct initialActive tallyOf quota

/--
The generated Appendix B.2 round constraints focus on the same candidates as
the generated trace steps.
-/
theorem rcvGeneratedStructureRoundConstraints_focus_eq_trace_focus
    {Candidate : Type*} [DecidableEq Candidate]
    (struct : RCVStructure Candidate)
    (initialActive : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) (quota : ℕ) :
    (rcvGeneratedStructureRoundConstraints struct initialActive tallyOf
        quota).map (fun constraint => some constraint.focus) =
      (rcvGeneratedTraceOfStructure struct initialActive tallyOf).steps.map
        STVStep.focus := by
  exact OrderSequenceStructure.generatedConstraints_focus_eq_generatedTrace_focus
    struct initialActive tallyOf quota

/--
The generated Appendix B.2 round constraints use the same tally functions as
the generated trace steps.
-/
theorem rcvGeneratedStructureRoundConstraints_tally_eq_trace_tally
    {Candidate : Type*} [DecidableEq Candidate]
    (struct : RCVStructure Candidate)
    (initialActive : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) (quota : ℕ) :
    (rcvGeneratedStructureRoundConstraints struct initialActive tallyOf
        quota).map RoundTallyConstraint.tally =
      (rcvGeneratedTraceOfStructure struct initialActive tallyOf).steps.map
        STVStep.tally := by
  exact OrderSequenceStructure.generatedConstraints_tally_eq_generatedTrace_tally
    struct initialActive tallyOf quota

/--
The generated Appendix B.2 round-constraint win/loss labels render as the
generated trace step kinds.
-/
theorem rcvGeneratedStructureRoundConstraints_kinds_eq_trace_kinds
    {Candidate : Type*} [DecidableEq Candidate]
    (struct : RCVStructure Candidate)
    (initialActive : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) (quota : ℕ) :
    (rcvGeneratedStructureRoundConstraints struct initialActive tallyOf
        quota).map (fun constraint => constraint.outcome.toStepKind) =
      (rcvGeneratedTraceOfStructure struct initialActive tallyOf).steps.map
        STVStep.kind := by
  exact OrderSequenceStructure.generatedConstraints_kinds_eq_generatedTrace_kinds
    struct initialActive tallyOf quota

/--
Held generated Appendix B.2 constraints make every generated elimination step a
minimum-tally elimination step.
-/
theorem rcvGeneratedStructureRoundConstraints_eliminatesMinimalTally_of_trace
    {Candidate : Type*} [DecidableEq Candidate]
    (struct : RCVStructure Candidate)
    (initialActive : Finset Candidate)
    (tallyOf : Finset Candidate → Candidate → ℕ) (quota : ℕ)
    (hholds :
      ∀ constraint,
        constraint ∈
          rcvGeneratedStructureRoundConstraints struct initialActive tallyOf
            quota →
        constraint.Holds)
    (i :
      Fin
        (rcvGeneratedTraceOfStructure struct initialActive
          tallyOf).steps.length)
    (heliminate :
      (((rcvGeneratedTraceOfStructure struct initialActive tallyOf).steps.get
        i).kind = StepKind.eliminate)) :
    (((rcvGeneratedTraceOfStructure struct initialActive tallyOf).steps.get
      i).eliminatesMinimalTally) := by
  exact
    OrderSequenceStructure.generatedConstraints_eliminatesMinimalTally_of_generatedTrace
      struct initialActive tallyOf quota
      (by simpa [rcvGeneratedStructureRoundConstraints] using hholds)
      i heliminate

/--
The canonical generated constraints are characterized by the deterministic
order-and-sequence classifier that generated them.
-/
theorem rcvStructureConstraintCharacterization_classifierConstraints
    {Data Candidate : Type*}
    (structureOf : Data → RCVStructure Candidate) :
    rcvStructureConstraintCharacterization structureOf
      (rcvStructureClassifierConstraints structureOf) := by
  exact structureConstraintCharacterization_classifierStructureConstraints
    structureOf

/--
Concrete trace-generated constraints are characterized by the structure read
from the deterministic trace generator.
-/
theorem rcvStructureConstraintCharacterization_traceGenerated
    {Data Candidate : Type*}
    (traceOf : Data → RCVTrace Candidate)
    (finalOrderOf : Data → FinalOrder Candidate) :
    rcvStructureConstraintCharacterization
      (rcvStructureOfTrace traceOf finalOrderOf)
      (rcvTraceGeneratedStructureConstraints traceOf finalOrderOf) := by
  exact traceStructureConstraintCharacterization traceOf finalOrderOf

/--
Proposition 2.1 partition condition: after tie-breaking, every voter-data point
satisfies the constraints of exactly one order-and-sequence structure.
-/
def rcvStructurePartition {Data Candidate : Type*}
    (constraints : RCVStructureConstraints Data Candidate) : Prop :=
  StructurePartition constraints

/--
Agreement condition between directly running the STV mechanism and reading the
final order encoded by the verified structure.
-/
def rcvStructureOutcomeAgreement {Data Candidate : Type*}
    (runSTV : Data → FinalOrder Candidate)
    (constraints : RCVStructureConstraints Data Candidate) : Prop :=
  StructureOutcomeAgreement runSTV OrderSequenceStructure.finalOrder constraints

/-- Concrete trace-generated constraints partition voter-data space. -/
theorem rcvStructurePartition_traceGenerated
    {Data Candidate : Type*}
    (traceOf : Data → RCVTrace Candidate)
    (finalOrderOf : Data → FinalOrder Candidate) :
    rcvStructurePartition
      (rcvTraceGeneratedStructureConstraints traceOf finalOrderOf) := by
  exact traceStructurePartition traceOf finalOrderOf

/--
The final-order reader agrees with the concrete trace-generated constraints.
-/
theorem rcvStructureOutcomeAgreement_traceGenerated
    {Data Candidate : Type*}
    (traceOf : Data → RCVTrace Candidate)
    (finalOrderOf : Data → FinalOrder Candidate) :
    rcvStructureOutcomeAgreement finalOrderOf
      (rcvTraceGeneratedStructureConstraints traceOf finalOrderOf) := by
  exact traceStructureOutcomeAgreement traceOf finalOrderOf

/--
Characterized generated constraints imply the Proposition 2.1 partition
condition.
-/
theorem rcvStructurePartition_of_constraintCharacterization
    {Data Candidate : Type*} {structureOf : Data → RCVStructure Candidate}
    {constraints : RCVStructureConstraints Data Candidate}
    (hcharacterization :
      rcvStructureConstraintCharacterization structureOf constraints) :
    rcvStructurePartition constraints :=
  structurePartition_of_structureConstraintCharacterization hcharacterization

/--
If direct STV agrees with the deterministic structure classifier, characterized
constraints imply direct-STV/constraint agreement.
-/
theorem rcvStructureOutcomeAgreement_of_constraintCharacterization
    {Data Candidate : Type*} {runSTV : Data → FinalOrder Candidate}
    {structureOf : Data → RCVStructure Candidate}
    {constraints : RCVStructureConstraints Data Candidate}
    (hcharacterization :
      rcvStructureConstraintCharacterization structureOf constraints)
    (hrun : ∀ data, runSTV data = (structureOf data).finalOrder) :
    rcvStructureOutcomeAgreement runSTV constraints :=
  structureOutcomeAgreement_of_structureConstraintCharacterization
    (classify := structureOf) (constraints := constraints)
    hcharacterization hrun

/--
The final order `order` is obtained by satisfying the constraints of some
order-and-sequence structure.
-/
def finalOrderRealizedByConstraints {Data Candidate : Type*}
    (constraints : RCVStructureConstraints Data Candidate)
    (data : Data) (order : FinalOrder Candidate) : Prop :=
  ∃ struct, constraints struct data ∧ order = struct.finalOrder

/--
Source-facing optimization problem for Theorem 3.1.

The feasible predicate encodes reaching a fixed target order-and-sequence
structure using at most the chosen budget. The objective is the number or cost
of added votes, represented as a real value so it can reuse the generic
`Optimization.IsMinimizerOn` API.
-/
structure SmartAllocationProblem (Addition : Type*) where
  feasible : Addition → Prop
  cost : Addition → ℝ
  budget : ℕ
  uniqueBallotCount : ℕ
  candidateCount : ℕ

namespace SmartAllocationProblem

/-- The Theorem 3.1 `O(mn)` operation-count bound in exact finite form. -/
def linearRuntimeBound {Addition : Type*}
    (problem : SmartAllocationProblem Addition) : ℕ :=
  problem.uniqueBallotCount * problem.candidateCount

end SmartAllocationProblem

/--
Finite componentwise slack-filling instance for the core of Algorithm 3.

The source proof reduces a fixed target order-and-sequence structure to
round-local nonnegative slack requirements. This structure records those
requirements and the paper's `m` and `n` size parameters; the reusable
optimization theorem proves that filling every required slack exactly minimizes
the total number of added votes in this reduced instance.
-/
structure SmartAllocationSlackFillingProblem (Slack : Type*) where
  requiredSlack : Slack → ℕ
  budget : ℕ
  uniqueBallotCount : ℕ
  candidateCount : ℕ

namespace SmartAllocationSlackFillingProblem

/-- A slack allocation is feasible when every required component is filled. -/
def feasible {Slack : Type*} (problem : SmartAllocationSlackFillingProblem Slack)
    (allocation : Slack → ℕ) : Prop :=
  EconCSLib.Optimization.componentwiseLowerBoundFeasible
    problem.requiredSlack allocation

/-- The objective is the total number of added votes across all slack components. -/
def cost {Slack : Type*} [Fintype Slack]
    (_problem : SmartAllocationSlackFillingProblem Slack)
    (allocation : Slack → ℕ) : ℝ :=
  EconCSLib.Optimization.componentwiseNatCost allocation

/-- Algorithm 3's slack-filling core fills every required component exactly. -/
def algorithm {Slack : Type*}
    (problem : SmartAllocationSlackFillingProblem Slack) : Slack → ℕ :=
  EconCSLib.Optimization.componentwiseLowerBoundFill problem.requiredSlack

/-- Exact operation-count model for the slack-filling core. -/
def operationCount {Slack : Type*}
    (problem : SmartAllocationSlackFillingProblem Slack) : ℕ :=
  problem.uniqueBallotCount * problem.candidateCount

/-- The source `m * n` linear runtime bound for the slack-filling core. -/
def linearRuntimeBound {Slack : Type*}
    (problem : SmartAllocationSlackFillingProblem Slack) : ℕ :=
  problem.uniqueBallotCount * problem.candidateCount

/--
The exact-fill slack allocation minimizes total added-vote cost among all
allocations that meet the componentwise slack requirements.
-/
theorem algorithm_optimal {Slack : Type*} [Fintype Slack]
    (problem : SmartAllocationSlackFillingProblem Slack) :
    EconCSLib.Optimization.IsMinimizerOn
      (feasible problem)
      (cost problem)
      (algorithm problem) := by
  simpa [feasible, cost, algorithm] using
    EconCSLib.Optimization.componentwiseLowerBoundFill_isMinimizerOn
      problem.requiredSlack

/-- The exact-fill slack core meets the source `m * n` operation bound. -/
theorem operationCount_le_linearRuntimeBound {Slack : Type*}
    (problem : SmartAllocationSlackFillingProblem Slack) :
    operationCount problem ≤ linearRuntimeBound problem :=
  le_rfl

end SmartAllocationSlackFillingProblem

/--
Concrete SmartAllocation implementation induced by a source STV-to-slack
reduction: solve the componentwise slack problem by exact fill, then translate
that slack allocation back to a strategic addition.
-/
def smartAllocationSlackReductionAlgorithm {Addition Slack : Type*}
    (slackProblem : SmartAllocationProblem Addition →
      SmartAllocationSlackFillingProblem Slack)
    (additionOf : ∀ problem : SmartAllocationProblem Addition,
      (Slack → ℕ) → Addition) :
    SmartAllocationProblem Addition → Addition :=
  fun problem =>
    additionOf problem
      (SmartAllocationSlackFillingProblem.algorithm (slackProblem problem))

/-- Concrete SmartAllocation operation-count implementation in the paper's `m * n` form. -/
def smartAllocationSlackReductionOperationCount {Addition : Type*} :
    SmartAllocationProblem Addition → ℕ :=
  fun problem =>
    SmartAllocationProblem.linearRuntimeBound problem

/--
Certificate that a SmartAllocation-style algorithm returns an optimal feasible
addition and meets the exact `m * n` operation bound for each problem instance.
-/
abbrev SmartAllocationCertificate {Addition : Type*}
    (algorithm : SmartAllocationProblem Addition → Addition)
    (operationCount : SmartAllocationProblem Addition → ℕ) :=
  EconCSLib.Optimization.AlgorithmMinimizerCertificate algorithm
    (fun problem addition => problem.feasible addition)
    (fun problem addition => problem.cost addition)
    operationCount
    SmartAllocationProblem.linearRuntimeBound

/--
Source-shaped slack certificate for the SmartAllocation proof: the algorithm's
output is feasible, no feasible addition has lower cost, and the operation
count satisfies the paper's linear bound.
-/
structure SmartAllocationSlackCertificate {Addition : Type*}
    (algorithm : SmartAllocationProblem Addition → Addition)
    (operationCount : SmartAllocationProblem Addition → ℕ) where
  output_feasible : ∀ problem : SmartAllocationProblem Addition,
    problem.feasible (algorithm problem)
  output_cost_le : ∀ (problem : SmartAllocationProblem Addition)
    (addition : Addition), problem.feasible addition →
    problem.cost (algorithm problem) ≤ problem.cost addition
  operationCount_le : ∀ problem : SmartAllocationProblem Addition,
    operationCount problem ≤
    SmartAllocationProblem.linearRuntimeBound problem

/--
Source-shaped no-lower-cost certificate for the SmartAllocation proof.  This
matches the Appendix C.1 argument that, once the required slacks are filled,
there is no feasible way to reach the target structure while spending less.
-/
structure SmartAllocationNoLowerCostCertificate {Addition : Type*}
    (algorithm : SmartAllocationProblem Addition → Addition)
    (operationCount : SmartAllocationProblem Addition → ℕ) where
  output_feasible : ∀ problem : SmartAllocationProblem Addition,
    problem.feasible (algorithm problem)
  no_lower_cost_feasible : ∀ problem : SmartAllocationProblem Addition,
    ¬ ∃ addition, problem.feasible addition ∧
      problem.cost addition < problem.cost (algorithm problem)
  operationCount_le : ∀ problem : SmartAllocationProblem Addition,
    operationCount problem ≤
    SmartAllocationProblem.linearRuntimeBound problem

/--
Source-shaped lower-bound certificate for the SmartAllocation proof.  The
source slack argument can be represented as a lower bound on every feasible
addition, attained by the algorithm's output, plus the claimed linear operation
bound.
-/
structure SmartAllocationLowerBoundCertificate {Addition : Type*}
    (algorithm : SmartAllocationProblem Addition → Addition)
    (operationCount : SmartAllocationProblem Addition → ℕ) where
  lowerBound : SmartAllocationProblem Addition → ℝ
  lowerBoundCertificate : ∀ problem : SmartAllocationProblem Addition,
    EconCSLib.Optimization.LowerBoundCertificate
      problem.feasible problem.cost (lowerBound problem)
  algorithm_eq_candidate : ∀ problem : SmartAllocationProblem Addition,
    (lowerBoundCertificate problem).candidate = algorithm problem
  operationCount_le : ∀ problem : SmartAllocationProblem Addition,
    operationCount problem ≤
    SmartAllocationProblem.linearRuntimeBound problem

/--
A source-shaped SmartAllocation slack certificate gives the generic minimizer
certificate used by the reusable optimization library.
-/
theorem smartAllocationCertificate_of_slackCertificate {Addition : Type*}
    {algorithm : SmartAllocationProblem Addition → Addition}
    {operationCount : SmartAllocationProblem Addition → ℕ}
    (cert : SmartAllocationSlackCertificate algorithm operationCount) :
    SmartAllocationCertificate algorithm operationCount :=
  EconCSLib.Optimization.AlgorithmMinimizerCertificate.of_output_feasible_objective_le
    cert.output_feasible cert.output_cost_le cert.operationCount_le

/--
A no-lower-cost SmartAllocation certificate gives the generic minimizer
certificate used by the reusable optimization library.
-/
theorem smartAllocationCertificate_of_noLowerCostCertificate {Addition : Type*}
    {algorithm : SmartAllocationProblem Addition → Addition}
    {operationCount : SmartAllocationProblem Addition → ℕ}
    (cert : SmartAllocationNoLowerCostCertificate algorithm operationCount) :
    SmartAllocationCertificate algorithm operationCount :=
  EconCSLib.Optimization.AlgorithmMinimizerCertificate.of_output_feasible_not_exists_objective_lt
    cert.output_feasible cert.no_lower_cost_feasible cert.operationCount_le

/--
A lower-bound SmartAllocation certificate gives the generic minimizer
certificate used by the reusable optimization library.
-/
theorem smartAllocationCertificate_of_lowerBoundCertificate {Addition : Type*}
    {algorithm : SmartAllocationProblem Addition → Addition}
    {operationCount : SmartAllocationProblem Addition → ℕ}
    (cert : SmartAllocationLowerBoundCertificate algorithm operationCount) :
    SmartAllocationCertificate algorithm operationCount :=
  EconCSLib.Optimization.AlgorithmMinimizerCertificate.of_lowerBoundCertificate
    cert.lowerBound cert.lowerBoundCertificate cert.algorithm_eq_candidate
    cert.operationCount_le

/--
The universal slack inequality used in the SmartAllocation proof can be
packaged as a lower-bound certificate whose certified value is the algorithm's
output cost.
-/
def smartAllocationLowerBoundCertificate_of_slackCertificate
    {Addition : Type*}
    {algorithm : SmartAllocationProblem Addition → Addition}
    {operationCount : SmartAllocationProblem Addition → ℕ}
    (cert : SmartAllocationSlackCertificate algorithm operationCount) :
    SmartAllocationLowerBoundCertificate algorithm operationCount where
  lowerBound problem := problem.cost (algorithm problem)
  lowerBoundCertificate := by
    intro problem
    exact {
      candidate := algorithm problem
      candidate_feasible := cert.output_feasible problem
      candidate_value := rfl
      lower_bound := by
        intro addition haddition
        exact cert.output_cost_le problem addition haddition
    }
  algorithm_eq_candidate := by
    intro _problem
    rfl
  operationCount_le := cert.operationCount_le

/--
The pairwise slack lower-bound certificate implies the no-lower-cost
certificate when a source proof is already stated in universal `≤` form.
-/
theorem smartAllocationNoLowerCostCertificate_of_slackCertificate
    {Addition : Type*}
    {algorithm : SmartAllocationProblem Addition → Addition}
    {operationCount : SmartAllocationProblem Addition → ℕ}
    (cert : SmartAllocationSlackCertificate algorithm operationCount) :
    SmartAllocationNoLowerCostCertificate algorithm operationCount where
  output_feasible := cert.output_feasible
  no_lower_cost_feasible := by
    intro problem hbetter
    rcases hbetter with ⟨addition, haddition, hlt⟩
    exact not_lt_of_ge (cert.output_cost_le problem addition haddition) hlt
  operationCount_le := cert.operationCount_le

/--
Source-shaped reduction from the full SmartAllocation instance to the checked
componentwise slack-filling core.  The fields expose the STV-specific proof
obligations: build the slack instance, translate feasible slack allocations
back to feasible additions, translate feasible additions into slack
allocations, preserve costs, and keep the advertised linear operation bound.
-/
structure SmartAllocationSlackReductionCertificate
    {Addition Slack : Type*} [Fintype Slack]
    (algorithm : SmartAllocationProblem Addition → Addition)
    (operationCount : SmartAllocationProblem Addition → ℕ) where
  slackProblem : SmartAllocationProblem Addition →
    SmartAllocationSlackFillingProblem Slack
  slackOf : ∀ problem : SmartAllocationProblem Addition, Addition → Slack → ℕ
  additionOf : ∀ problem : SmartAllocationProblem Addition, (Slack → ℕ) →
    Addition
  algorithm_eq_additionOf :
    ∀ problem : SmartAllocationProblem Addition,
      algorithm problem =
        additionOf problem
          (SmartAllocationSlackFillingProblem.algorithm (slackProblem problem))
  feasible_of_slack_feasible :
    ∀ (problem : SmartAllocationProblem Addition) (allocation : Slack → ℕ),
      SmartAllocationSlackFillingProblem.feasible (slackProblem problem)
          allocation →
        problem.feasible (additionOf problem allocation)
  slack_feasible_of_feasible :
    ∀ (problem : SmartAllocationProblem Addition) (addition : Addition),
      problem.feasible addition →
        SmartAllocationSlackFillingProblem.feasible (slackProblem problem)
          (slackOf problem addition)
  cost_algorithm_eq_slack :
    ∀ problem : SmartAllocationProblem Addition,
      problem.cost (algorithm problem) =
        SmartAllocationSlackFillingProblem.cost (slackProblem problem)
          (SmartAllocationSlackFillingProblem.algorithm (slackProblem problem))
  cost_eq_slack_of_feasible :
    ∀ (problem : SmartAllocationProblem Addition) (addition : Addition),
      problem.feasible addition →
        problem.cost addition =
          SmartAllocationSlackFillingProblem.cost (slackProblem problem)
            (slackOf problem addition)
  operationCount_le : ∀ problem : SmartAllocationProblem Addition,
    operationCount problem ≤
      SmartAllocationProblem.linearRuntimeBound problem

/--
The STV-to-slack reduction certificate discharges the source lower-bound
obligation for Theorem 3.1 once the componentwise slack-filling core is known
optimal.
-/
theorem smartAllocationSlackCertificate_of_slackReductionCertificate
    {Addition Slack : Type*} [Fintype Slack]
    {algorithm : SmartAllocationProblem Addition → Addition}
    {operationCount : SmartAllocationProblem Addition → ℕ}
    (cert :
      SmartAllocationSlackReductionCertificate
        (Slack := Slack) algorithm operationCount) :
    SmartAllocationSlackCertificate algorithm operationCount where
  output_feasible := by
    intro problem
    have hmin :=
      SmartAllocationSlackFillingProblem.algorithm_optimal
        (cert.slackProblem problem)
    rw [cert.algorithm_eq_additionOf problem]
    exact cert.feasible_of_slack_feasible problem
      (SmartAllocationSlackFillingProblem.algorithm (cert.slackProblem problem))
      hmin.isFeasible
  output_cost_le := by
    intro problem addition haddition
    have hmin :=
      SmartAllocationSlackFillingProblem.algorithm_optimal
        (cert.slackProblem problem)
    have hslack_feasible :=
      cert.slack_feasible_of_feasible problem addition haddition
    calc
      problem.cost (algorithm problem)
          = SmartAllocationSlackFillingProblem.cost (cert.slackProblem problem)
              (SmartAllocationSlackFillingProblem.algorithm
                (cert.slackProblem problem)) :=
        cert.cost_algorithm_eq_slack problem
      _ ≤ SmartAllocationSlackFillingProblem.cost (cert.slackProblem problem)
            (cert.slackOf problem addition) :=
        hmin.le hslack_feasible
      _ = problem.cost addition :=
        (cert.cost_eq_slack_of_feasible problem addition haddition).symm
  operationCount_le := cert.operationCount_le

/--
Source-facing problem for Theorem 3.2 candidate-set reduction.

The specification should state that the reduced instance removes only
irrelevant candidates who are eliminated first under every `budget`-bounded
addition and preserves the later-round dynamics for the remaining candidates.
-/
structure IrrelevantCandidateReductionProblem (ReducedInstance : Type*) where
  specification : ReducedInstance → Prop
  budget : ℕ
  uniqueBallotCount : ℕ
  candidateCount : ℕ

namespace IrrelevantCandidateReductionProblem

/-- The Theorem 3.2 `O(m n^4)` operation-count bound in exact finite form. -/
def quarticRuntimeBound {ReducedInstance : Type*}
    (problem : IrrelevantCandidateReductionProblem ReducedInstance) : ℕ :=
  problem.uniqueBallotCount * problem.candidateCount ^ 4

end IrrelevantCandidateReductionProblem

/--
Concrete Algorithm 4 reduced election instance: the candidate set and ballot
profile after removing an irrelevant group.
-/
abbrev ReducedElectionInstance (Voter Candidate : Type*) :=
  EconCSLib.SocialChoice.Voting.ReducedElectionInstance Voter Candidate

/--
Algorithm 4 concrete election reduction: remove the candidate group from the
candidate set and delete those candidates from every ballot.
-/
def reduceElectionInstanceByCandidates
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (removed candidates : Finset Candidate)
    (ballots : Voter → RCVBallot Candidate) :
    ReducedElectionInstance Voter Candidate :=
  EconCSLib.SocialChoice.Voting.ReducedElectionInstance.removeCandidates
    removed candidates ballots

/--
The reduced election preserves later-round active-support counts at a terminal
active set.
-/
def reducedElectionPreservesActiveSupport
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (sourceBallots : Voter → RCVBallot Candidate)
    (terminalActive : Finset Candidate)
    (reduced : ReducedElectionInstance Voter Candidate) : Prop :=
  EconCSLib.SocialChoice.Voting.ReducedElectionInstance.PreservesActiveSupport
    voters sourceBallots terminalActive reduced

/--
The concrete candidate-deletion reduction preserves later active support once
the deleted group is no longer active.
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
Concrete source specification for Algorithm 4's reduced election output in the
Theorem 3.2 route: the output is exactly the candidate-deletion instance and it
preserves active-support counts at the terminal active set.
-/
def irrelevantCandidateConcreteReductionSpecification
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates group terminalActive : Finset Candidate)
    (reduced : ReducedElectionInstance Voter Candidate) : Prop :=
  reduced = reduceElectionInstanceByCandidates group candidates ballots ∧
    reducedElectionPreservesActiveSupport voters ballots terminalActive reduced

/--
Concrete source problem for Algorithm 4/6 candidate reduction. Its
specification is not an arbitrary predicate: it is the paper's concrete
candidate-deletion output plus terminal active-support preservation.
-/
def irrelevantCandidateConcreteReductionProblem
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates group terminalActive : Finset Candidate)
    (budget uniqueBallotCount candidateCount : ℕ) :
    IrrelevantCandidateReductionProblem
      (ReducedElectionInstance Voter Candidate) where
  specification :=
    irrelevantCandidateConcreteReductionSpecification
      voters ballots candidates group terminalActive
  budget := budget
  uniqueBallotCount := uniqueBallotCount
  candidateCount := candidateCount

/-- Concrete operation-count model for the Algorithm 6 reduction theorem. -/
def irrelevantCandidateRemovalOperationCount
    (uniqueBallotCount candidateCount : ℕ) : ℕ :=
  uniqueBallotCount * candidateCount ^ 4

/--
Concrete Algorithm 6 / Algorithm 4 implementation on a fixed source model:
delete the certified irrelevant group from every ballot and from the candidate
set.
-/
def irrelevantCandidateConcreteReductionAlgorithm
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (ballots : Voter → RCVBallot Candidate)
    (candidates group : Finset Candidate) :
    IrrelevantCandidateReductionProblem
      (ReducedElectionInstance Voter Candidate) →
        ReducedElectionInstance Voter Candidate :=
  fun _problem =>
    reduceElectionInstanceByCandidates group candidates ballots

/-- Concrete Algorithm 6 operation-count implementation. -/
def irrelevantCandidateConcreteReductionOperationCount
    {Voter Candidate : Type*} :
    IrrelevantCandidateReductionProblem
      (ReducedElectionInstance Voter Candidate) → ℕ :=
  fun problem =>
    irrelevantCandidateRemovalOperationCount
      problem.uniqueBallotCount problem.candidateCount

/--
Certificate that irrelevant-candidate removal is sound and satisfies the
Theorem 3.2 quartic operation bound.
-/
abbrev IrrelevantCandidateRemovalCertificate {ReducedInstance : Type*}
    (algorithm :
      IrrelevantCandidateReductionProblem ReducedInstance → ReducedInstance)
    (operationCount :
      IrrelevantCandidateReductionProblem ReducedInstance → ℕ) :=
  EconCSLib.Optimization.AlgorithmSoundnessCertificate algorithm
    (fun problem output => problem.specification output)
    operationCount
    IrrelevantCandidateReductionProblem.quarticRuntimeBound

/--
Source-shaped certificate for the Theorem 3.2 irrelevant-candidate-removal
proof: the algorithm output satisfies the preservation specification and the
operation count satisfies the paper's quartic bound.
-/
structure IrrelevantCandidateRemovalSoundnessCertificate {ReducedInstance : Type*}
    (algorithm :
      IrrelevantCandidateReductionProblem ReducedInstance → ReducedInstance)
    (operationCount :
      IrrelevantCandidateReductionProblem ReducedInstance → ℕ) where
  output_spec : ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
    problem.specification (algorithm problem)
  operationCount_le :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      operationCount problem ≤
        IrrelevantCandidateReductionProblem.quarticRuntimeBound problem

/--
Source-shaped Algorithm 6 certificate for Theorem 3.2.

This narrows the remaining proof boundary to the concrete strict-support
group-removal condition: a certificate supplies the voter/ballot/candidate
objects used to evaluate Algorithm 6, proves the group-removal inequalities,
and proves that those inequalities imply the reduced instance satisfies the
problem's preservation specification.
-/
structure IrrelevantCandidateRemovalConditionCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    (algorithm :
      IrrelevantCandidateReductionProblem ReducedInstance → ReducedInstance)
    (operationCount :
      IrrelevantCandidateReductionProblem ReducedInstance → ℕ) where
  voters : IrrelevantCandidateReductionProblem ReducedInstance → Finset Voter
  ballots :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      Voter → RCVBallot Candidate
  candidates :
    IrrelevantCandidateReductionProblem ReducedInstance → Finset Candidate
  group : IrrelevantCandidateReductionProblem ReducedInstance → Finset Candidate
  quota : IrrelevantCandidateReductionProblem ReducedInstance → ℕ
  group_condition :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      candidateGroupRemovalCondition
        (voters problem) (ballots problem) (candidates problem)
        (group problem) problem.budget (quota problem)
  output_spec_of_group_safety :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      candidateGroupRemovalSafety
        (voters problem) (ballots problem) (candidates problem)
        (group problem) problem.budget (quota problem) →
        problem.specification (algorithm problem)
  operationCount_le :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      operationCount problem ≤
        IrrelevantCandidateReductionProblem.quarticRuntimeBound problem

/--
Source-shaped Algorithm 6 trace certificate for Theorem 3.2.

This refines the broad safety-to-output-spec boundary by proving, from the
Algorithm 6 safety inequalities and minimum-tally elimination semantics, that
every certified elimination step removes a candidate from the removable group.
The remaining certificate field states how that trace-level group-elimination
fact implies the concrete reduced-instance preservation specification.
-/
structure IrrelevantCandidateRemovalTraceCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    (algorithm :
      IrrelevantCandidateReductionProblem ReducedInstance → ReducedInstance)
    (operationCount :
      IrrelevantCandidateReductionProblem ReducedInstance → ℕ) where
  voters : IrrelevantCandidateReductionProblem ReducedInstance → Finset Voter
  ballots :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      Voter → RCVBallot Candidate
  candidates :
    IrrelevantCandidateReductionProblem ReducedInstance → Finset Candidate
  group : IrrelevantCandidateReductionProblem ReducedInstance → Finset Candidate
  quota : IrrelevantCandidateReductionProblem ReducedInstance → ℕ
  trace : IrrelevantCandidateReductionProblem ReducedInstance → RCVTrace Candidate
  group_condition :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      candidateGroupRemovalCondition
        (voters problem) (ballots problem) (candidates problem)
        (group problem) problem.budget (quota problem)
  minimal_eliminations :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate → step.eliminatesMinimalTally
  focused_eliminations_remove_focus :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate → step.removesFocusedCandidate
  group_active_at_elimination :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate →
          ∃ inside, inside ∈ group problem ∧ inside ∈ step.beforeActive
  active_subset_candidates :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate →
          step.beforeActive ⊆ candidates problem
  tally_inside :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate →
          ∀ inside, inside ∈ group problem → inside ∈ step.beforeActive →
            step.tally inside =
              problem.budget +
                strictSupportCount (voters problem) (ballots problem)
                  (group problem) (candidates problem \ group problem) inside
  tally_outside :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate →
          ∀ inside, inside ∈ group problem → inside ∈ step.beforeActive →
            ∀ outside, outside ∈ candidates problem \ group problem →
              step.tally outside =
                strictSupportCount (voters problem) (ballots problem)
                  (insert outside ((group problem).erase inside))
                  (∅ : Finset Candidate) outside
  output_spec_of_group_elimination_trace :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      (∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate →
          ∃ loser, step.focus = some loser ∧ loser ∈ group problem ∧
            loser ∈ step.beforeActive ∧
            step.afterActive = step.beforeActive.erase loser) →
        problem.specification (algorithm problem)
  operationCount_le :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      operationCount problem ≤
        IrrelevantCandidateReductionProblem.quarticRuntimeBound problem

/--
The Algorithm 6 trace certificate as the shared library strict-support replay
certificate for a fixed source problem.
-/
def irrelevantCandidateRemovalTraceCertificate_strictSupportTraceCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      IrrelevantCandidateReductionProblem ReducedInstance → ReducedInstance}
    {operationCount :
      IrrelevantCandidateReductionProblem ReducedInstance → ℕ}
    (cert :
      IrrelevantCandidateRemovalTraceCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount)
    (problem : IrrelevantCandidateReductionProblem ReducedInstance) :
    StrictSupportGroupRemovalTraceCertificate Voter Candidate where
  voters := cert.voters problem
  ballots := cert.ballots problem
  candidates := cert.candidates problem
  group := cert.group problem
  budget := problem.budget
  quota := cert.quota problem
  trace := cert.trace problem
  condition := cert.group_condition problem
  minimal_eliminations := cert.minimal_eliminations problem
  focused_eliminations_remove_focus :=
    cert.focused_eliminations_remove_focus problem
  group_active_at_elimination := cert.group_active_at_elimination problem
  active_subset_candidates := cert.active_subset_candidates problem
  tally_inside := cert.tally_inside problem
  tally_outside := cert.tally_outside problem

/--
Source-shaped Appendix C.2 replay certificate for Theorem 3.2.

This refines the trace-certificate boundary to the paper's consecutive
bottom-group argument: the certified prefix consists only of eliminations,
replays active sets from `startActive` to `terminalActive`, and has exactly the
length needed to exhaust the initially active removable group. The remaining
source-facing field is the Lemma C.1/reduced-instance bridge from terminal
group depletion to the concrete preservation specification.
-/
structure IrrelevantCandidateRemovalReplayCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    (algorithm :
      IrrelevantCandidateReductionProblem ReducedInstance → ReducedInstance)
    (operationCount :
      IrrelevantCandidateReductionProblem ReducedInstance → ℕ) where
  voters : IrrelevantCandidateReductionProblem ReducedInstance → Finset Voter
  ballots :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      Voter → RCVBallot Candidate
  candidates :
    IrrelevantCandidateReductionProblem ReducedInstance → Finset Candidate
  group : IrrelevantCandidateReductionProblem ReducedInstance → Finset Candidate
  quota : IrrelevantCandidateReductionProblem ReducedInstance → ℕ
  trace : IrrelevantCandidateReductionProblem ReducedInstance → RCVTrace Candidate
  startActive :
    IrrelevantCandidateReductionProblem ReducedInstance → Finset Candidate
  terminalActive :
    IrrelevantCandidateReductionProblem ReducedInstance → Finset Candidate
  group_condition :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      candidateGroupRemovalCondition
        (voters problem) (ballots problem) (candidates problem)
        (group problem) problem.budget (quota problem)
  minimal_eliminations :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate → step.eliminatesMinimalTally
  focused_eliminations_remove_focus :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate → step.removesFocusedCandidate
  group_active_at_elimination :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate →
          ∃ inside, inside ∈ group problem ∧ inside ∈ step.beforeActive
  active_subset_candidates :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate →
          step.beforeActive ⊆ candidates problem
  tally_inside :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate →
          ∀ inside, inside ∈ group problem → inside ∈ step.beforeActive →
            step.tally inside =
              problem.budget +
                strictSupportCount (voters problem) (ballots problem)
                  (group problem) (candidates problem \ group problem) inside
  tally_outside :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate →
          ∀ inside, inside ∈ group problem → inside ∈ step.beforeActive →
            ∀ outside, outside ∈ candidates problem \ group problem →
              step.tally outside =
                strictSupportCount (voters problem) (ballots problem)
                  (insert outside ((group problem).erase inside))
                  (∅ : Finset Candidate) outside
  trace_replays :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      (trace problem).replaysFrom
        (startActive problem) (terminalActive problem)
  all_steps_eliminate :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      ∀ step, step ∈ (trace problem).steps →
        step.kind = StepKind.eliminate
  trace_length_eq_initial_active_group_card :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      (trace problem).steps.length =
        (startActive problem ∩ group problem).card
  output_spec_of_terminal_group_depleted :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      terminalActive problem ∩ group problem = ∅ →
        problem.specification (algorithm problem)
  operationCount_le :
    ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
      operationCount problem ≤
        IrrelevantCandidateReductionProblem.quarticRuntimeBound problem

/--
An Algorithm 6 condition certificate gives the source-shaped soundness
certificate expected by the generic soundness projection.
-/
def irrelevantCandidateRemovalSoundnessCertificate_of_conditionCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      IrrelevantCandidateReductionProblem ReducedInstance → ReducedInstance}
    {operationCount :
      IrrelevantCandidateReductionProblem ReducedInstance → ℕ}
    (cert :
      IrrelevantCandidateRemovalConditionCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount) :
    IrrelevantCandidateRemovalSoundnessCertificate algorithm operationCount where
  output_spec := by
    intro problem
    exact cert.output_spec_of_group_safety problem
      (candidateGroupRemovalSafety_of_condition
        (cert.group_condition problem))
  operationCount_le := cert.operationCount_le

/--
An Algorithm 6 condition certificate directly gives the generic soundness
certificate used by the source-facing Theorem 3.2 projection.
-/
def irrelevantCandidateRemovalCertificate_of_conditionCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      IrrelevantCandidateReductionProblem ReducedInstance → ReducedInstance}
    {operationCount :
      IrrelevantCandidateReductionProblem ReducedInstance → ℕ}
    (cert :
      IrrelevantCandidateRemovalConditionCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount) :
    IrrelevantCandidateRemovalCertificate algorithm operationCount :=
  EconCSLib.Optimization.AlgorithmSoundnessCertificate.of_condition
    (fun problem =>
      candidateGroupRemovalSafety
        (cert.voters problem) (cert.ballots problem)
        (cert.candidates problem) (cert.group problem)
        problem.budget (cert.quota problem))
    (fun problem =>
      candidateGroupRemovalSafety_of_condition (cert.group_condition problem))
    cert.output_spec_of_group_safety cert.operationCount_le

/--
An Algorithm 6 trace certificate gives the existing condition-certificate
interface by deriving the trace-level group-elimination fact from safety.
-/
def irrelevantCandidateRemovalConditionCertificate_of_traceCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      IrrelevantCandidateReductionProblem ReducedInstance → ReducedInstance}
    {operationCount :
      IrrelevantCandidateReductionProblem ReducedInstance → ℕ}
    (cert :
      IrrelevantCandidateRemovalTraceCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount) :
    IrrelevantCandidateRemovalConditionCertificate
      (Voter := Voter) (Candidate := Candidate) algorithm operationCount where
  voters := cert.voters
  ballots := cert.ballots
  candidates := cert.candidates
  group := cert.group
  quota := cert.quota
  group_condition := cert.group_condition
  output_spec_of_group_safety := by
    intro problem hsafety
    have htrace :
        ∀ step, step ∈ (cert.trace problem).steps →
          step.kind = StepKind.eliminate →
            ∃ loser, step.focus = some loser ∧
              loser ∈ cert.group problem ∧
                loser ∈ step.beforeActive ∧
                step.afterActive = step.beforeActive.erase loser :=
      candidateGroupRemovalSafety_trace_elimination_focus_mem_group
        (voters := cert.voters problem)
        (ballots := cert.ballots problem)
        (candidates := cert.candidates problem)
        (group := cert.group problem)
        (budget := problem.budget)
        (quota := cert.quota problem)
        (trace := cert.trace problem)
        hsafety
        (cert.minimal_eliminations problem)
        (cert.focused_eliminations_remove_focus problem)
        (cert.group_active_at_elimination problem)
        (cert.active_subset_candidates problem)
        (cert.tally_inside problem)
        (cert.tally_outside problem)
    exact cert.output_spec_of_group_elimination_trace problem htrace
  operationCount_le := cert.operationCount_le

/--
An Appendix C.2 replay certificate gives the trace-certificate interface by
deriving terminal group depletion from the group-elimination trace fact.
-/
def irrelevantCandidateRemovalTraceCertificate_of_replayCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      IrrelevantCandidateReductionProblem ReducedInstance → ReducedInstance}
    {operationCount :
      IrrelevantCandidateReductionProblem ReducedInstance → ℕ}
    (cert :
      IrrelevantCandidateRemovalReplayCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount) :
    IrrelevantCandidateRemovalTraceCertificate
      (Voter := Voter) (Candidate := Candidate) algorithm operationCount where
  voters := cert.voters
  ballots := cert.ballots
  candidates := cert.candidates
  group := cert.group
  quota := cert.quota
  trace := cert.trace
  group_condition := cert.group_condition
  minimal_eliminations := cert.minimal_eliminations
  focused_eliminations_remove_focus := cert.focused_eliminations_remove_focus
  group_active_at_elimination := cert.group_active_at_elimination
  active_subset_candidates := cert.active_subset_candidates
  tally_inside := cert.tally_inside
  tally_outside := cert.tally_outside
  output_spec_of_group_elimination_trace := by
    intro problem htrace
    have htrace' :
        (cert.trace problem).eliminationRemovesFromGroup
          (cert.group problem) := htrace
    have hempty :
        cert.terminalActive problem ∩ cert.group problem = ∅ :=
      STVTrace.terminal_activeGroup_eq_empty_of_replaysFrom_length_eq_start_card
        (cert.trace_replays problem)
        (cert.all_steps_eliminate problem)
        htrace'
        (cert.trace_length_eq_initial_active_group_card problem)
    exact cert.output_spec_of_terminal_group_depleted problem hempty
  operationCount_le := cert.operationCount_le

/--
An Algorithm 6 trace certificate entails the exact cardinality form of the
removable-group elimination invariant. This is the reusable preservation-facing
fact: every certified elimination step removes exactly one active member of the
group being removed.
-/
theorem irrelevantCandidateRemovalTraceCertificate_activeGroup_card_add_one_eq
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      IrrelevantCandidateReductionProblem ReducedInstance → ReducedInstance}
    {operationCount :
      IrrelevantCandidateReductionProblem ReducedInstance → ℕ}
    (cert :
      IrrelevantCandidateRemovalTraceCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount)
    (problem : IrrelevantCandidateReductionProblem ReducedInstance) :
    (cert.trace problem).eliminationActiveGroupCardAddOneEq
      (cert.group problem) := by
  exact StrictSupportGroupRemovalTraceCertificate.eliminationActiveGroupCardAddOneEq
    (irrelevantCandidateRemovalTraceCertificate_strictSupportTraceCertificate
      cert problem)

/--
Algorithm 6 trace-certificate replay accounting: for an all-elimination prefix
whose active sets replay from `startActive` to `terminalActive`, the terminal
active removable-group count plus the number of replayed eliminations equals
the initial active removable-group count.
-/
theorem irrelevantCandidateRemovalTraceCertificate_terminal_activeGroup_card_add_length_eq
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      IrrelevantCandidateReductionProblem ReducedInstance → ReducedInstance}
    {operationCount :
      IrrelevantCandidateReductionProblem ReducedInstance → ℕ}
    (cert :
      IrrelevantCandidateRemovalTraceCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount)
    (problem : IrrelevantCandidateReductionProblem ReducedInstance)
    {startActive terminalActive : Finset Candidate}
    (hreplay :
      (cert.trace problem).replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ (cert.trace problem).steps →
        step.kind = StepKind.eliminate) :
    (terminalActive ∩ cert.group problem).card +
        (cert.trace problem).steps.length =
      (startActive ∩ cert.group problem).card := by
  exact StrictSupportGroupRemovalTraceCertificate.terminal_activeGroup_card_add_length_eq
    (irrelevantCandidateRemovalTraceCertificate_strictSupportTraceCertificate
      cert problem)
    hreplay hall_eliminate

/--
Algorithm 6 trace-certificate depletion: if an all-elimination replay prefix
has length equal to the number of initially active removable-group candidates,
then no removable-group candidate remains active at the terminal state.
-/
theorem irrelevantCandidateRemovalTraceCertificate_terminal_activeGroup_empty
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      IrrelevantCandidateReductionProblem ReducedInstance → ReducedInstance}
    {operationCount :
      IrrelevantCandidateReductionProblem ReducedInstance → ℕ}
    (cert :
      IrrelevantCandidateRemovalTraceCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount)
    (problem : IrrelevantCandidateReductionProblem ReducedInstance)
    {startActive terminalActive : Finset Candidate}
    (hreplay :
      (cert.trace problem).replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ (cert.trace problem).steps →
        step.kind = StepKind.eliminate)
    (hlength :
      (cert.trace problem).steps.length =
        (startActive ∩ cert.group problem).card) :
    terminalActive ∩ cert.group problem = ∅ := by
  exact StrictSupportGroupRemovalTraceCertificate.terminal_activeGroup_empty
    (irrelevantCandidateRemovalTraceCertificate_strictSupportTraceCertificate
      cert problem)
    hreplay hall_eliminate hlength

/--
Certificate-free Algorithm 6 replay bridge: if Algorithm 6's strict-support
condition holds and an all-elimination STV prefix replays active sets until it
has removed the initially active removable group, then that group is terminally
inactive and Lemma C.1 preserves all later-round active-support counts after
reducing ballots by the group.
-/
theorem algorithm6_replay_terminal_depleted_and_activeSupport_preserved
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group startActive terminalActive : Finset Candidate}
    {budget quota : ℕ} {trace : RCVTrace Candidate}
    (hcondition :
      candidateGroupRemovalCondition
        voters ballots candidates group budget quota)
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots group (candidates \ group)
                inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ group).card) :
    terminalActive ∩ group = ∅ ∧
      ∀ candidate : Candidate,
        (Ballot.activeSupport voters
            (fun voter => reduceBallotByCandidates group (ballots voter))
            terminalActive candidate).card =
          (Ballot.activeSupport voters ballots terminalActive candidate).card := by
  have hsafety :
      candidateGroupRemovalSafety voters ballots candidates group budget quota :=
    candidateGroupRemovalSafety_of_condition hcondition
  have htrace : trace.eliminationRemovesFromGroup group :=
    candidateGroupRemovalSafety_trace_eliminationRemovesFromGroup
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (group := group) (budget := budget) (quota := quota) (trace := trace)
      hsafety hminimal hremove hgroup_active hactive_subset_candidates
      htally_inside htally_outside
  have hempty : terminalActive ∩ group = ∅ :=
    STVTrace.terminal_activeGroup_eq_empty_of_replaysFrom_length_eq_start_card
      hreplay hall_eliminate htrace hlength
  exact ⟨hempty, by
    intro candidate
    exact lemmaC1_reducedBallots_activeSupport_card_eq_of_terminal_depleted
      voters ballots candidate hempty⟩

/--
Bounded-tally Algorithm 6 replay bridge: the strict-support quantities from
Algorithm 6 may be used as upper/lower bounds on the concrete step tallies,
rather than exact tally identities. This matches the paper proof's use of
strict support as a conservative comparison certificate.
-/
theorem algorithm6_replay_terminal_depleted_and_activeSupport_preserved_of_tally_bounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group startActive terminalActive : Finset Candidate}
    {budget quota : ℕ} {trace : RCVTrace Candidate}
    (hcondition :
      candidateGroupRemovalCondition
        voters ballots candidates group budget quota)
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside_le :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside ≤
            budget +
              strictSupportCount voters ballots group (candidates \ group)
                inside)
    (htally_outside_ge :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside ≤
            step.tally outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ group).card) :
    terminalActive ∩ group = ∅ ∧
      ∀ candidate : Candidate,
        (Ballot.activeSupport voters
            (fun voter => reduceBallotByCandidates group (ballots voter))
            terminalActive candidate).card =
          (Ballot.activeSupport voters ballots terminalActive candidate).card := by
  have hsafety :
      candidateGroupRemovalSafety voters ballots candidates group budget quota :=
    candidateGroupRemovalSafety_of_condition hcondition
  have htrace : trace.eliminationRemovesFromGroup group := by
    exact
      strictSupportGroupRemovalSafety_trace_eliminationRemovesFromGroup_of_tally_bounds
        (voters := voters) (ballots := ballots) (candidates := candidates)
        (group := group) (budget := budget) (quota := quota) (trace := trace)
        (by simpa [candidateGroupRemovalSafety] using hsafety)
        hminimal hremove hgroup_active hactive_subset_candidates
        (by
          intro step hstep hkind inside hinside hinside_active
          simpa [strictSupportCount] using
            htally_inside_le step hstep hkind inside hinside
              hinside_active)
        (by
          intro step hstep hkind inside hinside hinside_active outside
            houtside
          simpa [strictSupportCount] using
            htally_outside_ge step hstep hkind inside hinside
              hinside_active outside houtside)
  have hempty : terminalActive ∩ group = ∅ :=
    STVTrace.terminal_activeGroup_eq_empty_of_replaysFrom_length_eq_start_card
      hreplay hall_eliminate htrace hlength
  exact ⟨hempty, by
    intro candidate
    exact lemmaC1_reducedBallots_activeSupport_card_eq_of_terminal_depleted
      voters ballots candidate hempty⟩

/--
Concrete Algorithm 4/6 preservation theorem: under Algorithm 6's
strict-support condition and replay semantics, the Algorithm 4 reduced election
obtained by deleting the group preserves all later active-support counts at the
terminal active set.
-/
theorem algorithm6_replay_reduceElectionInstance_preservesActiveSupport
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group startActive terminalActive : Finset Candidate}
    {budget quota : ℕ} {trace : RCVTrace Candidate}
    (hcondition :
      candidateGroupRemovalCondition
        voters ballots candidates group budget quota)
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots group (candidates \ group)
                inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ group).card) :
    terminalActive ∩ group = ∅ ∧
      reducedElectionPreservesActiveSupport voters ballots terminalActive
        (reduceElectionInstanceByCandidates group candidates ballots) := by
  rcases algorithm6_replay_terminal_depleted_and_activeSupport_preserved
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (group := group) (startActive := startActive)
      (terminalActive := terminalActive) (budget := budget) (quota := quota)
      (trace := trace) hcondition hminimal hremove hgroup_active
      hactive_subset_candidates htally_inside htally_outside hreplay
      hall_eliminate hlength with
    ⟨hempty, hpreserve⟩
  exact ⟨hempty, by
    exact reducedElectionPreservesActiveSupport_reduceElectionInstanceByCandidates
      (voters := voters) (ballots := ballots) (terminalActive := terminalActive)
      (removed := group) (candidates := candidates) hempty⟩

/--
Bounded-tally Algorithm 4/6 preservation theorem: the same concrete
candidate-deletion reduction follows when Algorithm 6's strict-support
quantities bound, rather than exactly equal, the source trace tallies.
-/
theorem algorithm6_replay_reduceElectionInstance_preservesActiveSupport_of_tally_bounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group startActive terminalActive : Finset Candidate}
    {budget quota : ℕ} {trace : RCVTrace Candidate}
    (hcondition :
      candidateGroupRemovalCondition
        voters ballots candidates group budget quota)
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside_le :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside ≤
            budget +
              strictSupportCount voters ballots group (candidates \ group)
                inside)
    (htally_outside_ge :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside ≤
            step.tally outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ group).card) :
    terminalActive ∩ group = ∅ ∧
      reducedElectionPreservesActiveSupport voters ballots terminalActive
        (reduceElectionInstanceByCandidates group candidates ballots) := by
  rcases algorithm6_replay_terminal_depleted_and_activeSupport_preserved_of_tally_bounds
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (group := group) (startActive := startActive)
      (terminalActive := terminalActive) (budget := budget) (quota := quota)
      (trace := trace) hcondition hminimal hremove hgroup_active
      hactive_subset_candidates htally_inside_le htally_outside_ge hreplay
      hall_eliminate hlength with
    ⟨hempty, _hpreserve_counts⟩
  exact ⟨hempty, by
    exact reducedElectionPreservesActiveSupport_reduceElectionInstanceByCandidates
      (voters := voters) (ballots := ballots) (terminalActive := terminalActive)
      (removed := group) (candidates := candidates) hempty⟩

/--
Concrete Algorithm 4/6 Theorem 3.2 route: the reduced election produced by
deleting the removable group preserves later active-support counts, and the
concrete Algorithm 6 operation-count model satisfies the paper's quartic bound.
-/
theorem algorithm6_replay_reduceElectionInstance_sound_and_quartic_runtime
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group startActive terminalActive : Finset Candidate}
    {budget quota uniqueBallotCount candidateCount : ℕ}
    {trace : RCVTrace Candidate}
    (hcondition :
      candidateGroupRemovalCondition
        voters ballots candidates group budget quota)
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots group (candidates \ group)
                inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ group).card) :
    terminalActive ∩ group = ∅ ∧
      reducedElectionPreservesActiveSupport voters ballots terminalActive
        (reduceElectionInstanceByCandidates group candidates ballots) ∧
      irrelevantCandidateRemovalOperationCount uniqueBallotCount candidateCount ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  rcases algorithm6_replay_reduceElectionInstance_preservesActiveSupport
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (group := group) (startActive := startActive)
      (terminalActive := terminalActive) (budget := budget) (quota := quota)
      (trace := trace) hcondition hminimal hremove hgroup_active
      hactive_subset_candidates htally_inside htally_outside hreplay
      hall_eliminate hlength with
    ⟨hempty, hpreserve⟩
  exact ⟨hempty, hpreserve, le_rfl⟩

/--
Bounded-tally concrete Algorithm 4/6 Theorem 3.2 route.  This is the
source-facing variant to use when the Algorithm 6 replay proof supplies
conservative strict-support tally bounds rather than exact identities.
-/
theorem algorithm6_replay_reduceElectionInstance_sound_and_quartic_runtime_of_tally_bounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group startActive terminalActive : Finset Candidate}
    {budget quota uniqueBallotCount candidateCount : ℕ}
    {trace : RCVTrace Candidate}
    (hcondition :
      candidateGroupRemovalCondition
        voters ballots candidates group budget quota)
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside_le :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside ≤
            budget +
              strictSupportCount voters ballots group (candidates \ group)
                inside)
    (htally_outside_ge :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside ≤
            step.tally outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ group).card) :
    terminalActive ∩ group = ∅ ∧
      reducedElectionPreservesActiveSupport voters ballots terminalActive
        (reduceElectionInstanceByCandidates group candidates ballots) ∧
      irrelevantCandidateRemovalOperationCount uniqueBallotCount candidateCount ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  rcases algorithm6_replay_reduceElectionInstance_preservesActiveSupport_of_tally_bounds
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (group := group) (startActive := startActive)
      (terminalActive := terminalActive) (budget := budget) (quota := quota)
      (trace := trace) hcondition hminimal hremove hgroup_active
      hactive_subset_candidates htally_inside_le htally_outside_ge hreplay
      hall_eliminate hlength with
    ⟨hempty, hpreserve⟩
  exact ⟨hempty, hpreserve, le_rfl⟩

/--
Concrete Algorithm 4/6 trace-output helper: once the source trace is known to
remove candidates from the removable group, an all-elimination replay prefix
of the required length implies the concrete candidate-deletion specification
and quartic operation-count bound.
-/
theorem algorithm6_groupEliminationTrace_concreteReductionProblem_sound_and_quartic_runtime
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group startActive terminalActive : Finset Candidate}
    {budget uniqueBallotCount candidateCount : ℕ}
    {trace : RCVTrace Candidate}
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ group).card)
    (htrace : trace.eliminationRemovesFromGroup group) :
    (irrelevantCandidateConcreteReductionProblem
        voters ballots candidates group terminalActive budget
        uniqueBallotCount candidateCount).specification
      (reduceElectionInstanceByCandidates group candidates ballots) ∧
      irrelevantCandidateRemovalOperationCount uniqueBallotCount candidateCount ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  have hempty : terminalActive ∩ group = ∅ :=
    STVTrace.terminal_activeGroup_eq_empty_of_replaysFrom_length_eq_start_card
      hreplay hall_eliminate htrace hlength
  exact ⟨
    ⟨rfl,
      reducedElectionPreservesActiveSupport_reduceElectionInstanceByCandidates
        (voters := voters) (ballots := ballots)
        (terminalActive := terminalActive) (removed := group)
        (candidates := candidates) hempty⟩,
    le_rfl⟩

/--
Concrete Algorithm 6 output-specification helper: the candidate-deletion
implementation satisfies the concrete reduced-election specification whenever
the source trace removes the initially active removable group.
-/
theorem irrelevantCandidateConcreteReductionAlgorithm_output_spec_of_groupEliminationTrace
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group startActive terminalActive : Finset Candidate}
    {budget uniqueBallotCount candidateCount : ℕ}
    {trace : RCVTrace Candidate}
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ group).card)
    (htrace : trace.eliminationRemovesFromGroup group) :
    (irrelevantCandidateConcreteReductionProblem
        voters ballots candidates group terminalActive budget
        uniqueBallotCount candidateCount).specification
      (irrelevantCandidateConcreteReductionAlgorithm ballots candidates group
        (irrelevantCandidateConcreteReductionProblem
          voters ballots candidates group terminalActive budget
          uniqueBallotCount candidateCount)) := by
  rcases
      algorithm6_groupEliminationTrace_concreteReductionProblem_sound_and_quartic_runtime
        (voters := voters) (ballots := ballots) (candidates := candidates)
        (group := group) (startActive := startActive)
        (terminalActive := terminalActive) (budget := budget)
        (uniqueBallotCount := uniqueBallotCount)
        (candidateCount := candidateCount) (trace := trace)
        hreplay hall_eliminate hlength htrace with
    ⟨hspec, _hruntime⟩
  simpa [irrelevantCandidateConcreteReductionAlgorithm] using hspec

/--
Concrete Algorithm 4/6 Theorem 3.2 route with no arbitrary output
specification bridge. The source problem's specification is definitionally the
candidate-deletion output plus terminal active-support preservation.
-/
theorem algorithm6_replay_concreteReductionProblem_sound_and_quartic_runtime
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group startActive terminalActive : Finset Candidate}
    {budget quota uniqueBallotCount candidateCount : ℕ}
    {trace : RCVTrace Candidate}
    (hcondition :
      candidateGroupRemovalCondition
        voters ballots candidates group budget quota)
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots group (candidates \ group)
                inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ group).card) :
    (irrelevantCandidateConcreteReductionProblem
        voters ballots candidates group terminalActive budget
        uniqueBallotCount candidateCount).specification
      (reduceElectionInstanceByCandidates group candidates ballots) ∧
      irrelevantCandidateRemovalOperationCount uniqueBallotCount candidateCount ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  rcases algorithm6_replay_reduceElectionInstance_sound_and_quartic_runtime
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (group := group) (startActive := startActive)
      (terminalActive := terminalActive) (budget := budget) (quota := quota)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount) (trace := trace)
      hcondition hminimal hremove hgroup_active hactive_subset_candidates
      htally_inside htally_outside hreplay hall_eliminate hlength with
    ⟨_hempty, hpreserve, hruntime⟩
  exact ⟨⟨rfl, hpreserve⟩, hruntime⟩

/--
Bounded-tally concrete Algorithm 4/6 Theorem 3.2 route with no arbitrary
output-specification bridge. This source-facing variant proves the same
candidate-deletion specification from conservative Algorithm 6 tally bounds.
-/
theorem algorithm6_replay_concreteReductionProblem_sound_and_quartic_runtime_of_tally_bounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group startActive terminalActive : Finset Candidate}
    {budget quota uniqueBallotCount candidateCount : ℕ}
    {trace : RCVTrace Candidate}
    (hcondition :
      candidateGroupRemovalCondition
        voters ballots candidates group budget quota)
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside_le :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside ≤
            budget +
              strictSupportCount voters ballots group (candidates \ group)
                inside)
    (htally_outside_ge :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside ≤
            step.tally outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ group).card) :
    (irrelevantCandidateConcreteReductionProblem
        voters ballots candidates group terminalActive budget
        uniqueBallotCount candidateCount).specification
      (reduceElectionInstanceByCandidates group candidates ballots) ∧
      irrelevantCandidateRemovalOperationCount uniqueBallotCount candidateCount ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  rcases
      algorithm6_replay_reduceElectionInstance_sound_and_quartic_runtime_of_tally_bounds
        (voters := voters) (ballots := ballots) (candidates := candidates)
        (group := group) (startActive := startActive)
        (terminalActive := terminalActive) (budget := budget) (quota := quota)
        (uniqueBallotCount := uniqueBallotCount)
        (candidateCount := candidateCount) (trace := trace)
        hcondition hminimal hremove hgroup_active hactive_subset_candidates
        htally_inside_le htally_outside_ge hreplay hall_eliminate hlength with
    ⟨_hempty, hpreserve, hruntime⟩
  exact ⟨⟨rfl, hpreserve⟩, hruntime⟩

/--
An Algorithm 6 trace certificate gives the generic soundness certificate used
by the source-facing Theorem 3.2 projection.
-/
def irrelevantCandidateRemovalCertificate_of_traceCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      IrrelevantCandidateReductionProblem ReducedInstance → ReducedInstance}
    {operationCount :
      IrrelevantCandidateReductionProblem ReducedInstance → ℕ}
    (cert :
      IrrelevantCandidateRemovalTraceCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount) :
    IrrelevantCandidateRemovalCertificate algorithm operationCount :=
  irrelevantCandidateRemovalCertificate_of_conditionCertificate
    (irrelevantCandidateRemovalConditionCertificate_of_traceCertificate cert)

/--
An Appendix C.2 replay certificate gives the generic soundness certificate used
by the source-facing Theorem 3.2 projection.
-/
def irrelevantCandidateRemovalCertificate_of_replayCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      IrrelevantCandidateReductionProblem ReducedInstance → ReducedInstance}
    {operationCount :
      IrrelevantCandidateReductionProblem ReducedInstance → ℕ}
    (cert :
      IrrelevantCandidateRemovalReplayCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount) :
    IrrelevantCandidateRemovalCertificate algorithm operationCount :=
  irrelevantCandidateRemovalCertificate_of_traceCertificate
    (irrelevantCandidateRemovalTraceCertificate_of_replayCertificate cert)

/--
Build an Algorithm 6 condition certificate when the source model supplies the
group-removal condition, the condition-to-spec bridge, and an exact quartic
operation-count identity.
-/
def irrelevantCandidateRemovalConditionCertificate_of_exactRuntime
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      IrrelevantCandidateReductionProblem ReducedInstance → ReducedInstance}
    {operationCount :
      IrrelevantCandidateReductionProblem ReducedInstance → ℕ}
    (voters : IrrelevantCandidateReductionProblem ReducedInstance → Finset Voter)
    (ballots :
      ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
        Voter → RCVBallot Candidate)
    (candidates :
      IrrelevantCandidateReductionProblem ReducedInstance → Finset Candidate)
    (group : IrrelevantCandidateReductionProblem ReducedInstance → Finset Candidate)
    (quota : IrrelevantCandidateReductionProblem ReducedInstance → ℕ)
    (group_condition :
      ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
        candidateGroupRemovalCondition
          (voters problem) (ballots problem) (candidates problem)
          (group problem) problem.budget (quota problem))
    (output_spec_of_group_safety :
      ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
        candidateGroupRemovalSafety
          (voters problem) (ballots problem) (candidates problem)
          (group problem) problem.budget (quota problem) →
          problem.specification (algorithm problem))
    (operationCount_eq :
      ∀ problem : IrrelevantCandidateReductionProblem ReducedInstance,
        operationCount problem =
          IrrelevantCandidateReductionProblem.quarticRuntimeBound problem) :
    IrrelevantCandidateRemovalConditionCertificate
      (Voter := Voter) (Candidate := Candidate) algorithm operationCount where
  voters := voters
  ballots := ballots
  candidates := candidates
  group := group
  quota := quota
  group_condition := group_condition
  output_spec_of_group_safety := output_spec_of_group_safety
  operationCount_le := by
    intro problem
    rw [operationCount_eq problem]

/--
A source-shaped irrelevant-candidate-removal certificate gives the generic
soundness certificate used by the reusable optimization library.
-/
theorem irrelevantCandidateRemovalCertificate_of_soundnessCertificate
    {ReducedInstance : Type*}
    {algorithm :
      IrrelevantCandidateReductionProblem ReducedInstance → ReducedInstance}
    {operationCount :
      IrrelevantCandidateReductionProblem ReducedInstance → ℕ}
    (cert :
      IrrelevantCandidateRemovalSoundnessCertificate algorithm operationCount) :
    IrrelevantCandidateRemovalCertificate algorithm operationCount :=
  EconCSLib.Optimization.AlgorithmSoundnessCertificate.of_output_spec
    cert.output_spec cert.operationCount_le

/--
Source-facing problem for Proposition 3.4 sequence-space reduction.

The specification should state that the returned sequence family covers all
feasible sequences under `budget`-bounded additions while shortening the search
space according to the paper's win/loss bounds.
-/
structure SequenceReductionProblem (ReducedSequences : Type*) where
  specification : ReducedSequences → Prop
  budget : ℕ
  uniqueBallotCount : ℕ
  candidateCount : ℕ

namespace SequenceReductionProblem

/-- The Proposition 3.4 `O(m n^2)` operation-count bound in exact finite form. -/
def quadraticRuntimeBound {ReducedSequences : Type*}
    (problem : SequenceReductionProblem ReducedSequences) : ℕ :=
  problem.uniqueBallotCount * problem.candidateCount ^ 2

end SequenceReductionProblem

/-- Algorithm 7 output bounds: upper wins and lower initial losses. -/
structure SequenceReductionBounds where
  upperWins : ℕ
  lowerInitialLosses : ℕ

/--
Algorithm 7 bound formula: the number of possible winning rounds is bounded by
both the seat count and the total predicted win support divided by the quota,
while `lowerInitialLosses` records the loss-prefix bound computed by
Predict-Losses.
-/
def sequenceReductionBoundsFromPredictions
    (seats budget predictedWinSupport quota lowerInitialLosses : ℕ) :
    SequenceReductionBounds where
  upperWins := min seats ((budget + predictedWinSupport) / quota)
  lowerInitialLosses := lowerInitialLosses

/--
Algorithm 7 Predict-Wins candidate filter: candidates whose strict support from
the whole candidate set, plus the addition budget, can exceed quota.
-/
def predictWinsCandidates {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate) (budget quota : ℕ) : Finset Candidate :=
  candidates.filter fun candidate =>
    quota < budget +
      strictSupportCount voters ballots candidates (∅ : Finset Candidate)
        candidate

/-- Membership in the Algorithm 7 Predict-Wins filter is exactly the source inequality. -/
theorem mem_predictWinsCandidates_iff {Voter Candidate : Type*}
    [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {budget quota : ℕ}
    {candidate : Candidate} :
    candidate ∈ predictWinsCandidates voters ballots candidates budget quota ↔
      candidate ∈ candidates ∧
        quota < budget +
          strictSupportCount voters ballots candidates (∅ : Finset Candidate)
            candidate := by
  simp [predictWinsCandidates]

/--
Algorithm 7 Predict-Wins support accumulator: traverse the predicted-winner
candidates in source order, adding the strict-support count for the current
candidate while treating earlier predicted winners as blockers.
-/
def predictWinsSupport {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate) (orderedWinners : List Candidate) : ℕ :=
  Ballot.strictSupportCountWithAccumulatedBlockers
    voters ballots candidates orderedWinners

/--
Algorithm 7 Predict-Wins accumulator invariant: each counted candidate has at
least one quota unit of strict support at the blocker-prefix state where the
loop counts it.
-/
def predictWinsSupportAccumulatorQuota {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate) (quota : ℕ)
    (orderedWinners : List Candidate) : Prop :=
  Ballot.StrictSupportAccumulatorQuota voters ballots candidates ∅ quota
    orderedWinners

/--
Algorithm 7 budgeted Predict-Wins accumulator invariant: each counted
candidate reaches quota after adding the budget units assigned to that
candidate at the current blocker-prefix state.
-/
def predictWinsSupportBudgetAccumulatorQuota {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate) (assignedBudget : Candidate → ℕ)
    (quota : ℕ) (orderedWinners : List Candidate) : Prop :=
  Ballot.StrictSupportAccumulatorBudgetQuota voters ballots candidates ∅
    assignedBudget quota orderedWinners

/--
Prefix-form Predict-Wins quota condition: every listed predicted winner reaches
quota at the blocker state generated by the earlier listed winners.
-/
def predictWinsSupportAccumulatorQuotaAtPrefixes
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate) (quota : ℕ)
    (orderedWinners : List Candidate) : Prop :=
  Ballot.StrictSupportAccumulatorQuotaAtPrefixes voters ballots candidates ∅
    quota orderedWinners

/--
Prefix-form budgeted Predict-Wins quota condition: every listed predicted
winner reaches quota at the blocker state generated by the earlier listed
winners after adding the budget assigned to that candidate.
-/
def predictWinsSupportBudgetAccumulatorQuotaAtPrefixes
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate) (assignedBudget : Candidate → ℕ)
    (quota : ℕ) (orderedWinners : List Candidate) : Prop :=
  Ballot.StrictSupportAccumulatorBudgetQuotaAtPrefixes voters ballots
    candidates ∅ assignedBudget quota orderedWinners

/--
Algorithm 7 Predict-Wins ready set at a processed prefix: candidates whose
current strict support, with earlier predicted winners treated as blockers,
reaches quota after adding the candidate-specific budget allocation.
-/
def predictWinsBudgetReadyCandidatesAtPrefix
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate) (assignedBudget : Candidate → ℕ)
    (quota : ℕ) (processedWinners : List Candidate) : Finset Candidate :=
  Ballot.strictSupportBudgetReadyCandidatesAtPrefix voters ballots candidates
    ∅ assignedBudget quota processedWinners

/--
Generated-trace tally model for Predict-Wins: the focused candidate's tally is
the assigned budget for that candidate plus its strict support against the
candidates already removed from the generated active set.
-/
def predictWinsBudgetStrictSupportTallyOf
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate) (assignedBudget : Candidate → ℕ) :
    Finset Candidate → Candidate → ℕ :=
  fun active candidate =>
    assignedBudget candidate +
      strictSupportCount voters ballots candidates (candidates \ active)
        candidate

/--
Membership in the Algorithm 7 current-prefix Predict-Wins ready set is exactly
candidate membership plus the strict-support-plus-budget quota inequality.
-/
theorem mem_predictWinsBudgetReadyCandidatesAtPrefix_iff
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {assignedBudget : Candidate → ℕ}
    {quota : ℕ} {processedWinners : List Candidate}
    {candidate : Candidate} :
    candidate ∈
        predictWinsBudgetReadyCandidatesAtPrefix voters ballots candidates
          assignedBudget quota processedWinners ↔
      candidate ∈ candidates ∧
        quota ≤ assignedBudget candidate +
          strictSupportCount voters ballots candidates
            (Ballot.blockersAfterPrefix (∅ : Finset Candidate)
              processedWinners) candidate := by
  exact Ballot.mem_strictSupportBudgetReadyCandidatesAtPrefix_iff

/--
Source-inequality constructor for Predict-Wins loop selections. This packages
the two facts the concrete Algorithm 7 traversal proves for each selected
candidate into the ready-set membership premise.
-/
theorem predictWinsBudgetReadySelections_of_sourceInequalities
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {assignedBudget : Candidate → ℕ}
    {quota : ℕ} {orderedWinners : List Candidate}
    (hcandidate :
      ∀ pref candidate suffix,
        orderedWinners = pref ++ candidate :: suffix →
          candidate ∈ candidates)
    (hquota :
      ∀ pref candidate suffix,
        orderedWinners = pref ++ candidate :: suffix →
          quota ≤ assignedBudget candidate +
            strictSupportCount voters ballots candidates
              (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref)
              candidate) :
    ∀ pref candidate suffix,
      orderedWinners = pref ++ candidate :: suffix →
        candidate ∈
          predictWinsBudgetReadyCandidatesAtPrefix voters ballots candidates
            assignedBudget quota pref := by
  intro pref candidate suffix hdecomp
  exact mem_predictWinsBudgetReadyCandidatesAtPrefix_iff.2
    ⟨hcandidate pref candidate suffix hdecomp,
      hquota pref candidate suffix hdecomp⟩

/--
Predict-Wins generated-trace bridge: if the generated structure processes the
source order `pref ++ candidate :: suffix`, starts from the paper candidate set,
uses the Predict-Wins budget/strict-support tally model, and the corresponding
generated step is an election step satisfying the generated round constraints,
then `candidate` is ready at prefix `pref`.
-/
theorem predictWinsBudgetReadyCandidatesAtPrefix_of_generatedTrace_elect
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {assignedBudget : Candidate → ℕ}
    {quota : ℕ} {struct : RCVStructure Candidate}
    {initialActive : Finset Candidate}
    {pref suffix : List Candidate} {candidate : Candidate}
    (horder : struct.finalOrder.order = pref ++ candidate :: suffix)
    (horder_mem : ∀ source, source ∈ struct.finalOrder.order →
      source ∈ candidates)
    (hinitial : initialActive = candidates)
    (hholds :
      ∀ constraint,
        constraint ∈
          rcvGeneratedStructureRoundConstraints struct initialActive
            (predictWinsBudgetStrictSupportTallyOf voters ballots candidates
              assignedBudget) quota →
        constraint.Holds)
    (hidx :
      pref.length <
        (rcvGeneratedTraceOfStructure struct initialActive
          (predictWinsBudgetStrictSupportTallyOf voters ballots candidates
            assignedBudget)).steps.length)
    (helect :
      (((rcvGeneratedTraceOfStructure struct initialActive
        (predictWinsBudgetStrictSupportTallyOf voters ballots candidates
          assignedBudget)).steps.get ⟨pref.length, hidx⟩).kind =
        StepKind.elect)) :
    candidate ∈
      predictWinsBudgetReadyCandidatesAtPrefix voters ballots candidates
        assignedBudget quota pref := by
  classical
  let tallyOf :=
    predictWinsBudgetStrictSupportTallyOf voters ballots candidates assignedBudget
  let trace := rcvGeneratedTraceOfStructure struct initialActive tallyOf
  let i : Fin trace.steps.length := ⟨pref.length, by simpa [trace, tallyOf] using hidx⟩
  have hi : (i : ℕ) = pref.length := rfl
  have hcandidate_mem : candidate ∈ candidates := by
    apply horder_mem candidate
    rw [horder]
    simp
  have hpref_subset : pref.toFinset ⊆ candidates := by
    intro source hsource
    have hsource_pref : source ∈ pref := by
      simpa using hsource
    apply horder_mem source
    rw [horder]
    exact List.mem_append.mpr (Or.inl hsource_pref)
  have hblockers_eq :
      Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref =
        pref.toFinset := by
    simp
  have hsdiff :
      candidates \ (candidates \ pref.toFinset) = pref.toFinset := by
    ext source
    by_cases hsource : source ∈ pref.toFinset
    · have hsource_candidates := hpref_subset hsource
      simp [hsource, hsource_candidates]
    · simp [hsource]
  have hfocus_order :
      struct.finalOrder.order[pref.length]? = some candidate := by
    have hget : (pref ++ candidate :: suffix)[pref.length]? = some candidate := by
      simp
    simpa [horder] using hget
  have hfocus :
      ((trace.steps.get i).focus = some candidate) := by
    have hfocus_eq :=
      OrderSequenceStructure.generatedTrace_get_focus_eq_order_get?
        struct initialActive tallyOf i
    simpa [trace, rcvGeneratedTraceOfStructure, hi, hfocus_order] using
      hfocus_eq
  have hquota_step :
      candidate ∈ (trace.steps.get i).beforeActive ∧
        quota ≤ (trace.steps.get i).tally candidate := by
    have hholds' :
        ∀ constraint,
          constraint ∈
            OrderSequenceStructure.generatedConstraints struct initialActive
              tallyOf quota →
          constraint.Holds := by
      intro constraint hconstraint
      exact hholds constraint
        (by simpa [rcvGeneratedStructureRoundConstraints, tallyOf] using hconstraint)
    exact
      OrderSequenceStructure.generatedConstraints_elect_focus_quota_of_generatedTrace
        struct initialActive tallyOf quota hholds' i hfocus
        (by simpa [trace, tallyOf] using helect)
  have hbefore :
      (trace.steps.get i).beforeActive = candidates \ pref.toFinset := by
    have hbefore_eq :=
      OrderSequenceStructure.generatedTrace_get_beforeActive_eq_sdiff_take_toFinset
        struct initialActive tallyOf i
    have htake : struct.finalOrder.order.take pref.length = pref := by
      rw [horder]
      simp
    simpa [trace, rcvGeneratedTraceOfStructure, hinitial, hi, htake] using
      hbefore_eq
  have htally_eq :
      (trace.steps.get i).tally candidate =
        assignedBudget candidate +
          strictSupportCount voters ballots candidates pref.toFinset candidate := by
    have htally_trace :=
      OrderSequenceStructure.generatedTrace_tally_eq struct initialActive tallyOf i
    have htally_candidate := congrFun htally_trace candidate
    have htally_candidate' :
        (trace.steps.get i).tally candidate =
          tallyOf (trace.steps.get i).beforeActive candidate := by
      simpa [trace, rcvGeneratedTraceOfStructure] using htally_candidate
    rw [htally_candidate', hbefore]
    simp [tallyOf, predictWinsBudgetStrictSupportTallyOf, hsdiff]
  have hquota_ready :
      quota ≤ assignedBudget candidate +
        strictSupportCount voters ballots candidates
          (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref) candidate := by
    have hquota_pref :
        quota ≤ assignedBudget candidate +
          strictSupportCount voters ballots candidates pref.toFinset candidate := by
      rw [htally_eq] at hquota_step
      exact hquota_step.2
    simpa [hblockers_eq] using hquota_pref
  exact mem_predictWinsBudgetReadyCandidatesAtPrefix_iff.2
    ⟨hcandidate_mem, hquota_ready⟩

/--
List-level Predict-Wins generated-trace bridge. If a generated structure's final
order is the source winner order, starts from the paper candidate set, uses the
Predict-Wins budget/strict-support tally model, and every decomposed winner
position is an election step satisfying the generated round constraints, then
the whole source winner order satisfies the current-prefix readiness premise
used by Algorithm 7.
-/
theorem predictWinsBudgetReadySelections_of_generatedTrace_elects
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {assignedBudget : Candidate → ℕ}
    {quota : ℕ} {struct : RCVStructure Candidate}
    {initialActive : Finset Candidate}
    {sourceOrder : List Candidate}
    (horder : struct.finalOrder.order = sourceOrder)
    (horder_mem : ∀ source, source ∈ struct.finalOrder.order →
      source ∈ candidates)
    (hinitial : initialActive = candidates)
    (hholds :
      ∀ constraint,
        constraint ∈
          rcvGeneratedStructureRoundConstraints struct initialActive
            (predictWinsBudgetStrictSupportTallyOf voters ballots candidates
              assignedBudget) quota →
        constraint.Holds)
    (hidx :
      ∀ pref candidate suffix,
        sourceOrder = pref ++ candidate :: suffix →
          pref.length <
            (rcvGeneratedTraceOfStructure struct initialActive
              (predictWinsBudgetStrictSupportTallyOf voters ballots candidates
                assignedBudget)).steps.length)
    (helect :
      ∀ pref candidate suffix,
        (hdecomp : sourceOrder = pref ++ candidate :: suffix) →
          (((rcvGeneratedTraceOfStructure struct initialActive
            (predictWinsBudgetStrictSupportTallyOf voters ballots candidates
              assignedBudget)).steps.get
              ⟨pref.length, hidx pref candidate suffix hdecomp⟩).kind =
            StepKind.elect)) :
    ∀ pref candidate suffix,
      sourceOrder = pref ++ candidate :: suffix →
        candidate ∈
          predictWinsBudgetReadyCandidatesAtPrefix voters ballots candidates
            assignedBudget quota pref := by
  intro pref candidate suffix hdecomp
  exact
    predictWinsBudgetReadyCandidatesAtPrefix_of_generatedTrace_elect
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (assignedBudget := assignedBudget)
      (quota := quota)
      (struct := struct)
      (initialActive := initialActive)
      (pref := pref)
      (suffix := suffix)
      (candidate := candidate)
      (horder := by
        rw [horder]
        exact hdecomp)
      horder_mem hinitial hholds
      (hidx pref candidate suffix hdecomp)
      (helect pref candidate suffix hdecomp)

/--
Predict-Wins loop-selection constructor: if each selected winner is drawn from
the ready set computed at the prefix already processed by Algorithm 7, then
the paper's prefix-form budgeted quota premise holds.
-/
theorem predictWinsSupportBudgetAccumulatorQuotaAtPrefixes_of_mem_budgetReadyCandidatesAtPrefix
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {assignedBudget : Candidate → ℕ}
    {quota : ℕ} {orderedWinners : List Candidate}
    (hselected :
      ∀ pref candidate suffix,
        orderedWinners = pref ++ candidate :: suffix →
          candidate ∈
            predictWinsBudgetReadyCandidatesAtPrefix voters ballots candidates
              assignedBudget quota pref) :
    predictWinsSupportBudgetAccumulatorQuotaAtPrefixes voters ballots
      candidates assignedBudget quota orderedWinners := by
  exact
    Ballot.strictSupportAccumulatorBudgetQuotaAtPrefixes_of_mem_budgetReadyCandidatesAtPrefix
      (voters := voters) (ballots := ballots) (sources := candidates)
      (blockers := ∅) (assignedBudget := assignedBudget) (quota := quota)
      (candidates := orderedWinners) hselected

/--
Algorithm 7 Predict-Wins source-order loop relation: scan a source-ordered
candidate list and select only candidates that are ready at the current
processed-prefix state.
-/
abbrev PredictWinsBudgetReadySelectionLoop {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate) (assignedBudget : Candidate → ℕ)
    (quota : ℕ) :
    List Candidate → List Candidate → List Candidate → Prop :=
  Ballot.StrictSupportBudgetReadySelectionLoop voters ballots candidates
    (∅ : Finset Candidate) assignedBudget quota

/--
Concrete Predict-Wins source-order traversal: scan the source order and keep
exactly candidates that are budget-ready at their processed-prefix state.
-/
def predictWinsLoopFromSourceOrder {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate) (assignedBudget : Candidate → ℕ)
    (quota : ℕ) (sourceOrder : List Candidate) : List Candidate :=
  Ballot.strictSupportBudgetReadySelectionLoopOutput voters ballots candidates
    (∅ : Finset Candidate) assignedBudget quota [] sourceOrder

/--
The concrete Predict-Wins source-order traversal satisfies the source-order
ready-selection loop relation.
-/
theorem predictWinsLoopFromSourceOrder_spec
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate) (assignedBudget : Candidate → ℕ)
    (quota : ℕ) (sourceOrder : List Candidate) :
    PredictWinsBudgetReadySelectionLoop voters ballots candidates
      assignedBudget quota [] sourceOrder
      (predictWinsLoopFromSourceOrder voters ballots candidates
        assignedBudget quota sourceOrder) := by
  exact
    Ballot.strictSupportBudgetReadySelectionLoopOutput_spec
      voters ballots candidates (∅ : Finset Candidate) assignedBudget quota
      [] sourceOrder

/--
If the source order supplied to Predict-Wins already consists of candidates
that are ready at their processed-prefix state, the executable Predict-Wins
loop returns the source order unchanged.
-/
theorem predictWinsLoopFromSourceOrder_eq_self_of_forall_ready
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {assignedBudget : Candidate → ℕ}
    {quota : ℕ} {sourceOrder : List Candidate}
    (hready :
      ∀ pref candidate suffix,
        sourceOrder = pref ++ candidate :: suffix →
          candidate ∈
            predictWinsBudgetReadyCandidatesAtPrefix voters ballots candidates
              assignedBudget quota pref) :
    predictWinsLoopFromSourceOrder voters ballots candidates assignedBudget
      quota sourceOrder = sourceOrder := by
  exact
    Ballot.strictSupportBudgetReadySelectionLoopOutput_eq_self_of_forall_ready
      (voters := voters) (ballots := ballots) (sources := candidates)
      (blockers := ∅) (assignedBudget := assignedBudget) (quota := quota)
      (processed := []) (sourceOrder := sourceOrder)
      (by
        intro pref candidate suffix hdecomp
        simpa using hready pref candidate suffix hdecomp)

/--
A concrete Predict-Wins source-order loop supplies the prefix-form budgeted
quota condition used by Proposition 3.4.
-/
theorem predictWinsSupportBudgetAccumulatorQuotaAtPrefixes_of_budgetReadySelectionLoop
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {assignedBudget : Candidate → ℕ}
    {quota : ℕ} {sourceOrder orderedWinners : List Candidate}
    (hloop :
      PredictWinsBudgetReadySelectionLoop voters ballots candidates
        assignedBudget quota [] sourceOrder orderedWinners) :
    predictWinsSupportBudgetAccumulatorQuotaAtPrefixes voters ballots
      candidates assignedBudget quota orderedWinners := by
  exact
    Ballot.strictSupportAccumulatorBudgetQuotaAtPrefixes_of_budgetReadySelectionLoop
      (voters := voters) (ballots := ballots) (sources := candidates)
      (blockers := ∅) (assignedBudget := assignedBudget) (quota := quota)
      (sourceOrder := sourceOrder) (candidates := orderedWinners) hloop

/--
The prefix-form Predict-Wins condition constructs the recursive accumulator
invariant used by the coverage theorem.
-/
theorem predictWinsSupportAccumulatorQuota_of_atPrefixes
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {quota : ℕ}
    {orderedWinners : List Candidate}
    (hprefix :
      predictWinsSupportAccumulatorQuotaAtPrefixes voters ballots candidates
        quota orderedWinners) :
    predictWinsSupportAccumulatorQuota voters ballots candidates quota
      orderedWinners := by
  exact Ballot.strictSupportAccumulatorQuota_of_atPrefixes hprefix

/--
The prefix-form budgeted Predict-Wins condition constructs the recursive
budgeted accumulator invariant used by the coverage theorem.
-/
theorem predictWinsSupportBudgetAccumulatorQuota_of_atPrefixes
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {assignedBudget : Candidate → ℕ}
    {quota : ℕ} {orderedWinners : List Candidate}
    (hprefix :
      predictWinsSupportBudgetAccumulatorQuotaAtPrefixes voters ballots
        candidates assignedBudget quota orderedWinners) :
    predictWinsSupportBudgetAccumulatorQuota voters ballots candidates
      assignedBudget quota orderedWinners := by
  exact Ballot.strictSupportAccumulatorBudgetQuota_of_atPrefixes hprefix

/--
The Predict-Wins support accumulator carries at least one quota unit for each
ordered winner whose loop-state strict-support count reaches quota.
-/
theorem quota_mul_length_le_predictWinsSupport_of_accumulatorQuota
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {quota : ℕ}
    {orderedWinners : List Candidate}
    (hquota :
      predictWinsSupportAccumulatorQuota voters ballots candidates quota
        orderedWinners) :
    quota * orderedWinners.length ≤
      predictWinsSupport voters ballots candidates orderedWinners := by
  exact Ballot.quota_mul_length_le_strictSupportCountWithAccumulatedBlockers
    voters ballots candidates quota orderedWinners hquota

/--
The budgeted Predict-Wins support accumulator carries at least one quota unit
for each ordered winner when assigned budget units are counted together with
the loop-state strict support.
-/
theorem quota_mul_length_le_budget_sum_add_predictWinsSupport_of_budgetAccumulatorQuota
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {assignedBudget : Candidate → ℕ}
    {quota : ℕ} {orderedWinners : List Candidate}
    (hquota :
      predictWinsSupportBudgetAccumulatorQuota voters ballots candidates
        assignedBudget quota orderedWinners) :
    quota * orderedWinners.length ≤
      (orderedWinners.map assignedBudget).sum +
        predictWinsSupport voters ballots candidates orderedWinners := by
  exact
    Ballot.quota_mul_length_le_budget_sum_add_strictSupportCountWithAccumulatedBlockers
      voters ballots candidates assignedBudget quota orderedWinners hquota

/--
Algorithm 7 Predict-Losses candidate filter: candidates whose strict support
from the whole candidate set, plus the addition budget, stays below the source
first-choice threshold used for the top-`k` comparison.
-/
def predictLossesCandidates {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate) (budget firstChoiceThreshold : ℕ) :
    Finset Candidate :=
  candidates.filter fun candidate =>
    budget +
      strictSupportCount voters ballots candidates (∅ : Finset Candidate)
        candidate < firstChoiceThreshold

/-- Membership in the Algorithm 7 Predict-Losses filter is exactly the source inequality. -/
theorem mem_predictLossesCandidates_iff {Voter Candidate : Type*}
    [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {budget firstChoiceThreshold : ℕ}
    {candidate : Candidate} :
    candidate ∈
        predictLossesCandidates voters ballots candidates budget
          firstChoiceThreshold ↔
    candidate ∈ candidates ∧
        budget +
          strictSupportCount voters ballots candidates (∅ : Finset Candidate)
            candidate < firstChoiceThreshold := by
  simp [predictLossesCandidates]

/--
Predict-Losses membership bounds a candidate's first-choice count by any
upper bound on the source first-choice threshold.
-/
theorem firstChoiceCount_le_topFirstChoice_of_mem_predictLossesCandidates
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {budget firstChoiceThreshold
      topFirstChoice : ℕ} {candidate : Candidate}
    (hthreshold_le : firstChoiceThreshold ≤ topFirstChoice)
    (hmem :
      candidate ∈
        predictLossesCandidates voters ballots candidates budget
          firstChoiceThreshold) :
    Ballot.firstChoiceCount voters ballots candidate ≤ topFirstChoice := by
  rcases mem_predictLossesCandidates_iff.mp hmem with
    ⟨hcandidate, hstrict_lt_threshold⟩
  have hfirst_le_strict :
      Ballot.firstChoiceCount voters ballots candidate ≤
        strictSupportCount voters ballots candidates (∅ : Finset Candidate)
          candidate :=
    Ballot.firstChoiceCount_le_strictSupportCount_of_mem_sources
      (voters := voters) (ballots := ballots) (sources := candidates)
      (candidate := candidate) hcandidate
  have hstrict_lt :
      strictSupportCount voters ballots candidates (∅ : Finset Candidate)
          candidate < firstChoiceThreshold :=
    lt_of_le_of_lt
      (Nat.le_add_left
        (strictSupportCount voters ballots candidates (∅ : Finset Candidate)
          candidate) budget)
      hstrict_lt_threshold
  exact hfirst_le_strict.trans ((Nat.le_of_lt hstrict_lt).trans hthreshold_le)

/--
Algorithm 7 Predict-Losses source-loop prefix: the listed prefix has no
repeated candidates and every listed candidate belongs to the Predict-Losses
filter computed from the source first-choice threshold.
-/
def PredictLossesLoopPrefix {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate) (budget firstChoiceThreshold : ℕ)
    (lossPrefix : List Candidate) : Prop :=
  lossPrefix.Nodup ∧
    ∀ candidate, candidate ∈ lossPrefix →
      candidate ∈
        predictLossesCandidates voters ballots candidates budget
          firstChoiceThreshold

/--
Concrete source-order Predict-Losses loop: keep exactly the source-order
candidates satisfying the Predict-Losses strict-support test.
-/
def predictLossesLoopFromSourceOrder {Voter Candidate : Type*}
    [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate) (budget firstChoiceThreshold : ℕ)
    (sourceOrder : List Candidate) : List Candidate :=
  sourceOrder.filter fun candidate =>
    candidate ∈
      predictLossesCandidates voters ballots candidates budget
        firstChoiceThreshold

/--
The concrete source-order Predict-Losses loop returns an ordered loop prefix
whenever the source order has no repeated candidates.
-/
theorem predictLossesLoopPrefix_of_sourceOrder_filter
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {budget firstChoiceThreshold : ℕ}
    {sourceOrder : List Candidate}
    (hnodup : sourceOrder.Nodup) :
    PredictLossesLoopPrefix voters ballots candidates budget
      firstChoiceThreshold
      (predictLossesLoopFromSourceOrder voters ballots candidates budget
        firstChoiceThreshold sourceOrder) := by
  constructor
  · exact hnodup.filter _
  · intro candidate hmem
    exact of_decide_eq_true (List.mem_filter.mp hmem).2

/--
If the source order supplied to Predict-Losses already consists only of
definitely losing candidates, the executable Predict-Losses filter returns the
source order unchanged.
-/
theorem predictLossesLoopFromSourceOrder_eq_self_of_forall_mem
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {budget firstChoiceThreshold : ℕ}
    {sourceOrder : List Candidate}
    (hmem :
      ∀ candidate, candidate ∈ sourceOrder →
        candidate ∈
          predictLossesCandidates voters ballots candidates budget
            firstChoiceThreshold) :
    predictLossesLoopFromSourceOrder voters ballots candidates budget
      firstChoiceThreshold sourceOrder = sourceOrder := by
  induction sourceOrder with
  | nil =>
      simp [predictLossesLoopFromSourceOrder]
  | cons candidate rest ih =>
      have hcandidate :
          candidate ∈
            predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold := by
        exact hmem candidate (by simp)
      have hrest :
          ∀ other, other ∈ rest →
            other ∈
              predictLossesCandidates voters ballots candidates budget
                firstChoiceThreshold := by
        intro other hother
        exact hmem other (by simp [hother])
      calc
        predictLossesLoopFromSourceOrder voters ballots candidates budget
            firstChoiceThreshold (candidate :: rest)
            = candidate ::
                predictLossesLoopFromSourceOrder voters ballots candidates
                  budget firstChoiceThreshold rest := by
              simp [predictLossesLoopFromSourceOrder, hcandidate]
        _ = candidate :: rest := by
              rw [ih hrest]

/--
Length form of `predictLossesLoopFromSourceOrder_eq_self_of_forall_mem`,
matching Algorithm 7's source convention where the input order is already the
sorted definitely-losing list.
-/
theorem predictLossesLoopFromSourceOrder_length_eq_of_forall_mem
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {budget firstChoiceThreshold : ℕ}
    {sourceOrder : List Candidate}
    (hmem :
      ∀ candidate, candidate ∈ sourceOrder →
        candidate ∈
          predictLossesCandidates voters ballots candidates budget
            firstChoiceThreshold) :
    (predictLossesLoopFromSourceOrder voters ballots candidates budget
      firstChoiceThreshold sourceOrder).length = sourceOrder.length := by
  rw [predictLossesLoopFromSourceOrder_eq_self_of_forall_mem hmem]

/--
Algorithm 7 Predict-Losses transfer loop, in source form. Starting from the
top first-choice count plus an accumulated transferable total, scan the
transfer amounts in sorted order and count the initial prefix that can be
moved while staying below quota. The count is capped by the supplied transfer
list.
-/
def predictLossesTransferInitialLossBoundFrom
    (topFirstChoice quota accumulated : ℕ) : List ℕ → ℕ
  | [] => 0
  | transfer :: rest =>
      if accumulated + transfer + topFirstChoice < quota then
        Nat.succ
          (predictLossesTransferInitialLossBoundFrom topFirstChoice quota
            (accumulated + transfer) rest)
      else
        1

/--
Algorithm 7 Predict-Losses transfer-loop output from zero accumulated
transfers.
-/
def predictLossesTransferInitialLossBound
    (topFirstChoice quota : ℕ) (transfers : List ℕ) : ℕ :=
  predictLossesTransferInitialLossBoundFrom topFirstChoice quota 0 transfers

/--
The transfer-loop lower bound never exceeds the number of transfer entries
available.
-/
theorem predictLossesTransferInitialLossBoundFrom_le_length
    (topFirstChoice quota accumulated : ℕ) :
    ∀ transfers : List ℕ,
      predictLossesTransferInitialLossBoundFrom topFirstChoice quota
        accumulated transfers ≤ transfers.length := by
  intro transfers
  induction transfers generalizing accumulated with
  | nil =>
      simp [predictLossesTransferInitialLossBoundFrom]
  | cons transfer rest ih =>
      simp [predictLossesTransferInitialLossBoundFrom]
      by_cases hlt : accumulated + transfer + topFirstChoice < quota
      · simp [hlt, ih]
      · simp [hlt]

/--
The source Predict-Losses transfer-loop output is bounded by the length of the
sorted transfer list.
-/
theorem predictLossesTransferInitialLossBound_le_length
    (topFirstChoice quota : ℕ) (transfers : List ℕ) :
    predictLossesTransferInitialLossBound topFirstChoice quota transfers ≤
      transfers.length := by
  exact predictLossesTransferInitialLossBoundFrom_le_length
    topFirstChoice quota 0 transfers

/--
Transfer-loop invariant for Algorithm 7 Predict-Losses: before every index
strictly below the source lower-bound counter, the accumulated transferred
mass plus the top first-choice count remains below quota.
-/
theorem predictLossesTransferInitialLossBoundFrom_prefix_sum_lt_quota
    (topFirstChoice quota : ℕ) :
    ∀ transfers accumulated,
      accumulated + topFirstChoice < quota →
        ∀ {i : ℕ},
          i <
              predictLossesTransferInitialLossBoundFrom topFirstChoice quota
                accumulated transfers →
            accumulated + (transfers.take i).sum + topFirstChoice < quota := by
  intro transfers
  induction transfers with
  | nil =>
      intro accumulated hacc i hi
      simp [predictLossesTransferInitialLossBoundFrom] at hi
  | cons transfer rest ih =>
      intro accumulated hacc i hi
      cases i with
      | zero =>
          simpa using hacc
      | succ i =>
          by_cases hstep : accumulated + transfer + topFirstChoice < quota
          · have hi_rest :
                i <
                  predictLossesTransferInitialLossBoundFrom topFirstChoice
                    quota (accumulated + transfer) rest := by
              simpa [predictLossesTransferInitialLossBoundFrom, hstep] using hi
            have hrec :=
              ih (accumulated + transfer) hstep hi_rest
            simpa [List.take, add_assoc, add_left_comm, add_comm] using hrec
          · have hfalse : False := by
              simpa [predictLossesTransferInitialLossBoundFrom, hstep] using hi
            exact hfalse.elim

/--
Top-level form of the Predict-Losses transfer-loop invariant.
-/
theorem predictLossesTransferInitialLossBound_prefix_sum_lt_quota
    {topFirstChoice quota : ℕ} {transfers : List ℕ} {i : ℕ}
    (htop_lt : topFirstChoice < quota)
    (hi :
      i <
        predictLossesTransferInitialLossBound topFirstChoice quota
          transfers) :
    (transfers.take i).sum + topFirstChoice < quota := by
  have h :=
    predictLossesTransferInitialLossBoundFrom_prefix_sum_lt_quota
      topFirstChoice quota transfers 0 (by simpa using htop_lt)
      (by simpa [predictLossesTransferInitialLossBound] using hi)
  simpa [Nat.zero_add, add_assoc, add_left_comm, add_comm] using h

/--
If the source order is already the sorted definitely-losing list and the
transfer list is keyed to that same order, Algorithm 7's transfer-loop lower
bound is no larger than the concrete Predict-Losses loop output length.
-/
theorem predictLossesTransferInitialLossBound_le_loop_length_of_forall_mem
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {budget firstChoiceThreshold : ℕ}
    {sourceOrder : List Candidate} {topFirstChoice quota : ℕ}
    {transfers : List ℕ}
    (htransfer_length : transfers.length = sourceOrder.length)
    (hmem :
      ∀ candidate, candidate ∈ sourceOrder →
        candidate ∈
          predictLossesCandidates voters ballots candidates budget
            firstChoiceThreshold) :
    predictLossesTransferInitialLossBound topFirstChoice quota transfers ≤
      (predictLossesLoopFromSourceOrder voters ballots candidates budget
        firstChoiceThreshold sourceOrder).length := by
  calc
    predictLossesTransferInitialLossBound topFirstChoice quota transfers ≤
        transfers.length :=
      predictLossesTransferInitialLossBound_le_length topFirstChoice quota
        transfers
    _ = sourceOrder.length := htransfer_length
    _ =
        (predictLossesLoopFromSourceOrder voters ballots candidates budget
          firstChoiceThreshold sourceOrder).length := by
      symm
      exact predictLossesLoopFromSourceOrder_length_eq_of_forall_mem hmem

/--
Finite checker for the Predict-Losses source-order obligations in Proposition
3.4.  For every feasible sequence in the finite coverage set it checks that the
loss source order has no duplicates, every listed candidate belongs to the
Predict-Losses filter, the transfer list is keyed to the same order, and the
advertised lower-initial-loss count is bounded by the transfer loop.
-/
noncomputable def proposition3_4_lossSourceOrderCheckOnFinset
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate) (sourceSequences : Finset RCVSequence)
    (lossSourceOrder : RCVSequence → List Candidate)
    (lossTransfers : RCVSequence → List ℕ)
    (budget firstChoiceThreshold topFirstChoice quota lowerInitialLosses :
      ℕ) : Bool := by
  classical
  exact sourceSequences.toList.all fun sequence =>
    if feasibleSequence sequence then
      decide ((lossSourceOrder sequence).Nodup) &&
        ((lossSourceOrder sequence).all fun candidate =>
          decide
            (candidate ∈
              predictLossesCandidates voters ballots candidates budget
                firstChoiceThreshold)) &&
        decide ((lossTransfers sequence).length =
          (lossSourceOrder sequence).length) &&
        decide (lowerInitialLosses ≤
          predictLossesTransferInitialLossBound topFirstChoice quota
            (lossTransfers sequence))
    else
      true

/--
Completeness for the finite Predict-Losses source-order checker in Proposition
3.4.  Source facts over every feasible sequence in the finite coverage set are
exactly enough to make the executable checker return `true`.
-/
theorem proposition3_4_lossSourceOrderCheckOnFinset_eq_true_of_facts
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {sourceSequences : Finset RCVSequence}
    {lossSourceOrder : RCVSequence → List Candidate}
    {lossTransfers : RCVSequence → List ℕ}
    {budget firstChoiceThreshold topFirstChoice quota lowerInitialLosses :
      ℕ}
    (hnodup :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        (lossSourceOrder sequence).Nodup)
    (hmem :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        ∀ candidate, candidate ∈ lossSourceOrder sequence →
          candidate ∈
            predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold)
    (htransfer_length :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        (lossTransfers sequence).length =
          (lossSourceOrder sequence).length)
    (hlower :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        lowerInitialLosses ≤
          predictLossesTransferInitialLossBound topFirstChoice quota
            (lossTransfers sequence)) :
    proposition3_4_lossSourceOrderCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        sourceSequences lossSourceOrder lossTransfers budget
        firstChoiceThreshold topFirstChoice quota lowerInitialLosses = true := by
  classical
  apply List.all_eq_true.mpr
  intro sequence hseq
  have hsource : sequence ∈ sourceSequences := Finset.mem_toList.mp hseq
  by_cases hfeasible : feasibleSequence sequence
  · have hmem_check :
        ((lossSourceOrder sequence).all fun candidate =>
          decide
            (candidate ∈
              predictLossesCandidates voters ballots candidates budget
                firstChoiceThreshold)) = true := by
      exact List.all_eq_true.mpr (by
        intro candidate hcandidate
        exact decide_eq_true_iff.mpr
          (hmem sequence hsource hfeasible candidate hcandidate))
    simp [hfeasible, hnodup sequence hsource hfeasible, hmem_check,
      htransfer_length sequence hsource hfeasible,
      hlower sequence hsource hfeasible]
  · simp [hfeasible]

/--
A successful finite Predict-Losses source-order checker supplies all source
facts needed by the Proposition 3.4 Predict-Losses loop route.
-/
theorem proposition3_4_lossSourceOrderCheckOnFinset_facts
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {allSequences : Finset RCVSequence}
    {lossSourceOrder : RCVSequence → List Candidate}
    {lossTransfers : RCVSequence → List ℕ}
    {budget firstChoiceThreshold topFirstChoice quota lowerInitialLosses :
      ℕ}
    (hcheck :
      proposition3_4_lossSourceOrderCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        allSequences lossSourceOrder lossTransfers budget firstChoiceThreshold
        topFirstChoice quota lowerInitialLosses = true) :
    ∀ sequence, sequence ∈ allSequences → feasibleSequence sequence →
      (lossSourceOrder sequence).Nodup ∧
        (∀ candidate, candidate ∈ lossSourceOrder sequence →
          candidate ∈
            predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold) ∧
        (lossTransfers sequence).length =
          (lossSourceOrder sequence).length ∧
        lowerInitialLosses ≤
          predictLossesTransferInitialLossBound topFirstChoice quota
            (lossTransfers sequence) := by
  classical
  intro sequence hsequence hfeasible
  have hseq_all :
      (if feasibleSequence sequence then
        decide ((lossSourceOrder sequence).Nodup) &&
          ((lossSourceOrder sequence).all fun candidate =>
            decide
              (candidate ∈
                predictLossesCandidates voters ballots candidates budget
                  firstChoiceThreshold)) &&
          decide ((lossTransfers sequence).length =
            (lossSourceOrder sequence).length) &&
          decide (lowerInitialLosses ≤
            predictLossesTransferInitialLossBound topFirstChoice quota
              (lossTransfers sequence))
      else
        true) = true := by
    have hall := List.all_eq_true.mp hcheck
    simpa [proposition3_4_lossSourceOrderCheckOnFinset] using
      hall sequence (Finset.mem_toList.mpr hsequence)
  have hparts :
      (((decide ((lossSourceOrder sequence).Nodup) = true ∧
          ((lossSourceOrder sequence).all fun candidate =>
            decide
              (candidate ∈
                predictLossesCandidates voters ballots candidates budget
                  firstChoiceThreshold)) = true) ∧
          decide ((lossTransfers sequence).length =
            (lossSourceOrder sequence).length) = true) ∧
          decide (lowerInitialLosses ≤
            predictLossesTransferInitialLossBound topFirstChoice quota
              (lossTransfers sequence)) = true) := by
    simpa [hfeasible, Bool.and_eq_true_eq_eq_true_and_eq_true] using hseq_all
  refine
    ⟨decide_eq_true_iff.mp hparts.1.1.1, ?_,
      decide_eq_true_iff.mp hparts.1.2,
      decide_eq_true_iff.mp hparts.2⟩
  intro candidate hcandidate
  exact
    decide_eq_true_iff.mp
      ((List.all_eq_true.mp hparts.1.1.2) candidate hcandidate)

/--
Build a Predict-Losses loop prefix from the literal Algorithm 7 source
inequalities for each candidate in the ordered prefix.
-/
theorem predictLossesLoopPrefix_of_sourceInequalities
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {budget firstChoiceThreshold : ℕ}
    {lossPrefix : List Candidate}
    (hnodup : lossPrefix.Nodup)
    (hcandidate :
      ∀ candidate, candidate ∈ lossPrefix → candidate ∈ candidates)
    (hsupport_lt :
      ∀ candidate, candidate ∈ lossPrefix →
        budget +
          strictSupportCount voters ballots candidates (∅ : Finset Candidate)
            candidate < firstChoiceThreshold) :
    PredictLossesLoopPrefix voters ballots candidates budget
      firstChoiceThreshold lossPrefix := by
  refine ⟨hnodup, ?_⟩
  intro candidate hmem
  exact mem_predictLossesCandidates_iff.2
    ⟨hcandidate candidate hmem, hsupport_lt candidate hmem⟩

/--
Source-shaped Predict-Losses initial-prefix witness: the listed prefix is made
of Algorithm 7 Predict-Losses candidates and is long enough to justify the
claimed lower initial-loss bound for a feasible sequence.
-/
abbrev PredictLossesInitialLossPrefixCertificate
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate) (budget firstChoiceThreshold : ℕ)
    (initialLossCount : Sequence → ℕ) (lowerInitialLosses : ℕ)
    (sequence : Sequence) :=
  InitialLossPrefixCertificate
    (predictLossesCandidates voters ballots candidates budget
      firstChoiceThreshold)
    initialLossCount lowerInitialLosses sequence

/--
Build the Predict-Losses initial-loss witness from the concrete Algorithm 7
loop prefix, plus the two semantic facts that the source loop's returned prefix
is long enough for the claimed lower bound and is indeed an initial segment of
losses for the feasible sequence.
-/
def predictLossesInitialLossPrefixCertificate_of_loopPrefix
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {budget firstChoiceThreshold : ℕ}
    {initialLossCount : Sequence → ℕ} {lowerInitialLosses : ℕ}
    {sequence : Sequence} {lossPrefix : List Candidate}
    (hloop :
      PredictLossesLoopPrefix voters ballots candidates budget
        firstChoiceThreshold lossPrefix)
    (hlower : lowerInitialLosses ≤ lossPrefix.length)
    (hinitial : lossPrefix.length ≤ initialLossCount sequence) :
    PredictLossesInitialLossPrefixCertificate voters ballots candidates
      budget firstChoiceThreshold initialLossCount lowerInitialLosses
      sequence where
  lossPrefix := lossPrefix
  prefix_nodup := hloop.1
  prefix_subset_lossCandidates := hloop.2
  lower_le_prefix_length := hlower
  prefix_length_le_initialLossCount := hinitial

/--
Build the Predict-Losses initial-loss witness from the concrete Algorithm 7
loop prefix and a concrete RCV trace whose first eliminations focus on exactly
that prefix.
-/
def predictLossesInitialLossPrefixCertificate_of_loopPrefix_and_traceFocusPrefix
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {budget firstChoiceThreshold : ℕ}
    {lowerInitialLosses : ℕ}
    {sequence : RCVSequence} {trace : RCVTrace Candidate}
    {lossPrefix : List Candidate}
    (hloop :
      PredictLossesLoopPrefix voters ballots candidates budget
        firstChoiceThreshold lossPrefix)
    (hlower : lowerInitialLosses ≤ lossPrefix.length)
    (hsequence : sequence = rcvSequenceFromTrace trace)
    (hprefix : trace.HasInitialEliminationFocusPrefix lossPrefix) :
    PredictLossesInitialLossPrefixCertificate voters ballots candidates
      budget firstChoiceThreshold rcvSequenceInitialLossCount
      lowerInitialLosses sequence :=
  predictLossesInitialLossPrefixCertificate_of_loopPrefix hloop hlower
    (lossPrefix_length_le_rcvSequenceInitialLossCount_of_initialLossPrefix
      (rcvSequenceHasInitialLossPrefix_of_trace_initialEliminationFocusPrefix
        hsequence hprefix))

/--
Build the Predict-Losses initial-loss witness from the concrete Algorithm 7
loop prefix and index-wise facts about the beginning of the source trace.
-/
def predictLossesInitialLossPrefixCertificate_of_loopPrefix_and_traceGetElem
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {budget firstChoiceThreshold : ℕ}
    {lowerInitialLosses : ℕ}
    {sequence : RCVSequence} {trace : RCVTrace Candidate}
    {lossPrefix : List Candidate}
    (hloop :
      PredictLossesLoopPrefix voters ballots candidates budget
        firstChoiceThreshold lossPrefix)
    (hlower : lowerInitialLosses ≤ lossPrefix.length)
    (hsequence : sequence = rcvSequenceFromTrace trace)
    (hlen : lossPrefix.length ≤ trace.steps.length)
    (hfocus :
      ∀ i : Fin lossPrefix.length,
        (trace.steps.get
          ⟨i.1, Nat.lt_of_lt_of_le i.2 hlen⟩).focus =
          some (lossPrefix.get i))
    (hkind :
      ∀ i : Fin lossPrefix.length,
        (trace.steps.get
          ⟨i.1, Nat.lt_of_lt_of_le i.2 hlen⟩).kind =
          StepKind.eliminate) :
    PredictLossesInitialLossPrefixCertificate voters ballots candidates
      budget firstChoiceThreshold rcvSequenceInitialLossCount
      lowerInitialLosses sequence :=
  predictLossesInitialLossPrefixCertificate_of_loopPrefix_and_traceFocusPrefix
    hloop hlower hsequence
      (rcvTraceHasInitialEliminationFocusPrefix_of_getElem hlen hfocus hkind)

/--
Build the Predict-Losses initial-loss witness from the concrete Algorithm 7
loop prefix and a count-only trace fact. The witness prefix is the first
`lowerInitialLosses` candidates from the Predict-Losses loop output; the trace
only needs that many initial elimination rounds, not that it eliminates those
candidates in exactly the loop order.
-/
def predictLossesInitialLossPrefixCertificate_of_loopPrefix_take_and_traceInitialEliminationPrefix
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {budget firstChoiceThreshold : ℕ}
    {lowerInitialLosses : ℕ}
    {sequence : RCVSequence} {trace : RCVTrace Candidate}
    {lossPrefix : List Candidate}
    (hloop :
      PredictLossesLoopPrefix voters ballots candidates budget
        firstChoiceThreshold lossPrefix)
    (hlower : lowerInitialLosses ≤ lossPrefix.length)
    (hsequence : sequence = rcvSequenceFromTrace trace)
    (hprefix : trace.HasInitialEliminationPrefix lowerInitialLosses) :
    PredictLossesInitialLossPrefixCertificate voters ballots candidates
      budget firstChoiceThreshold rcvSequenceInitialLossCount
      lowerInitialLosses sequence where
  lossPrefix := lossPrefix.take lowerInitialLosses
  prefix_nodup := by
    exact hloop.1.sublist (List.take_sublist _ _)
  prefix_subset_lossCandidates := by
    intro candidate hcandidate
    exact hloop.2 candidate (List.mem_of_mem_take hcandidate)
  lower_le_prefix_length := by
    simpa [List.length_take, Nat.min_eq_left hlower]
  prefix_length_le_initialLossCount := by
    have hprefix_sequence :
        rcvSequenceHasInitialLossPrefix sequence
          (lossPrefix.take lowerInitialLosses).length := by
      simpa [List.length_take, Nat.min_eq_left hlower] using
        (rcvSequenceHasInitialLossPrefix_of_trace_initialEliminationPrefix
          hsequence hprefix)
    exact
      lossPrefix_length_le_rcvSequenceInitialLossCount_of_initialLossPrefix
        (lossPrefix := lossPrefix.take lowerInitialLosses)
        hprefix_sequence

/--
Project the lower-initial-loss inequality from a concrete Predict-Losses prefix
witness.
-/
theorem lowerInitialLosses_le_initialLossCount_of_predictLossesPrefixCertificate
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {budget firstChoiceThreshold : ℕ}
    {initialLossCount : Sequence → ℕ} {lowerInitialLosses : ℕ}
    {sequence : Sequence}
    (cert :
      PredictLossesInitialLossPrefixCertificate voters ballots candidates
        budget firstChoiceThreshold initialLossCount lowerInitialLosses
        sequence) :
    lowerInitialLosses ≤ initialLossCount sequence :=
  lowerInitialLosses_le_initialLossCount_of_initialLossPrefixCertificate cert

/--
Per-sequence Predict-Losses prefix witnesses supply the loss-floor premise used
by Algorithm 7's sequence-reduction coverage theorem.
-/
theorem loss_floor_of_predictLossesPrefixCertificates
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {budget firstChoiceThreshold : ℕ}
    {feasibleSequence : Sequence → Prop}
    {initialLossCount : Sequence → ℕ} {lowerInitialLosses : ℕ}
    (cert :
      ∀ sequence, feasibleSequence sequence →
        PredictLossesInitialLossPrefixCertificate voters ballots candidates
          budget firstChoiceThreshold initialLossCount lowerInitialLosses
          sequence) :
    ∀ sequence, feasibleSequence sequence →
      lowerInitialLosses ≤ initialLossCount sequence :=
  loss_floor_of_initialLossPrefixCertificates cert

/--
Coverage predicate for Algorithm 7: every feasible source sequence has no more
winning rounds than `upperWins` and at least `lowerInitialLosses` consecutive
initial losses.
-/
def sequenceBoundsCover {Sequence : Type*}
    (feasibleSequence : Sequence → Prop)
    (winCount initialLossCount : Sequence → ℕ)
    (bounds : SequenceReductionBounds) : Prop :=
  ∀ sequence, feasibleSequence sequence →
    winCount sequence ≤ bounds.upperWins ∧
      bounds.lowerInitialLosses ≤ initialLossCount sequence

/--
Closed Algorithm 7 arithmetic core: if every feasible sequence has at most
`seats` wins, if each win consumes one quota unit from the predicted support
capacity, and if Predict-Losses supplies an initial-loss floor, then the
resulting bounds cover every feasible sequence.
-/
theorem sequenceBoundsCover_of_predictiveCapacity
    {Sequence : Type*}
    {feasibleSequence : Sequence → Prop}
    {winCount initialLossCount : Sequence → ℕ}
    {seats budget predictedWinSupport quota lowerInitialLosses : ℕ}
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence → winCount sequence ≤ seats)
    (hcapacity :
      ∀ sequence, feasibleSequence sequence →
        quota * winCount sequence ≤ budget + predictedWinSupport)
    (hloss_floor :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ initialLossCount sequence) :
    sequenceBoundsCover feasibleSequence winCount initialLossCount
      (sequenceReductionBoundsFromPredictions
        seats budget predictedWinSupport quota lowerInitialLosses) := by
  intro sequence hfeasible
  refine ⟨?_, hloss_floor sequence hfeasible⟩
  have hdiv :
      winCount sequence ≤ (budget + predictedWinSupport) / quota := by
    exact (Nat.le_div_iff_mul_le hquota_pos).2
      (by simpa [Nat.mul_comm] using hcapacity sequence hfeasible)
  exact le_min (hseat sequence hfeasible) hdiv

/--
Algorithm 7 quota-block capacity core: if each feasible sequence's winning
rounds have pairwise-disjoint quota-sized support blocks inside the predicted
capacity pool, then the sequence satisfies the win-capacity premise used by the
quota arithmetic.
-/
theorem sequenceWinCapacity_of_quotaBlocks
    {Sequence Round SupportUnit : Type*} [DecidableEq SupportUnit]
    {feasibleSequence : Sequence → Prop}
    {winRounds : Sequence → Finset Round}
    {winCount : Sequence → ℕ}
    {capacityPool : Sequence → Finset SupportUnit}
    {quota budget predictedWinSupport : ℕ}
    (quotaBlock : Sequence → Round → Finset SupportUnit)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        winCount sequence = (winRounds sequence).card)
    (hcapacity :
      ∀ sequence, feasibleSequence sequence →
        (capacityPool sequence).card ≤ budget + predictedWinSupport)
    (hdisjoint :
      ∀ sequence, feasibleSequence sequence →
        ((winRounds sequence : Set Round).PairwiseDisjoint
          (quotaBlock sequence)))
    (hsubset :
      ∀ sequence, feasibleSequence sequence →
        ∀ round ∈ winRounds sequence,
          quotaBlock sequence round ⊆ capacityPool sequence)
    (hquota :
      ∀ sequence, feasibleSequence sequence →
        ∀ round ∈ winRounds sequence,
          quota ≤ (quotaBlock sequence round).card) :
    ∀ sequence, feasibleSequence sequence →
      quota * winCount sequence ≤ budget + predictedWinSupport := by
  intro sequence hfeasible
  rw [hwinCount_eq sequence hfeasible]
  exact le_trans
    (EconCSLib.FiniteSum.quota_mul_card_le_card_of_pairwiseDisjoint_blocks
      (winRounds sequence) (capacityPool sequence) (quotaBlock sequence)
      (hdisjoint sequence hfeasible)
      (hsubset sequence hfeasible)
      (hquota sequence hfeasible))
    (hcapacity sequence hfeasible)

/--
Algorithm 7 support-sum capacity core: if each feasible winning round is
charged at least one quota unit of counted Predict-Wins support, and the sum of
those counted supports is bounded by the budget plus Algorithm 7's predicted
support accumulator, then the sequence satisfies the win-capacity premise used
by the quota arithmetic.
-/
theorem sequenceWinCapacity_of_quotaSupportSum
    {Sequence Round : Type*}
    {feasibleSequence : Sequence → Prop}
    {winRounds : Sequence → Finset Round}
    {winCount : Sequence → ℕ}
    {supportCount : Sequence → Round → ℕ}
    {quota budget predictedWinSupport : ℕ}
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        winCount sequence = (winRounds sequence).card)
    (hsupport_sum :
      ∀ sequence, feasibleSequence sequence →
        (∑ round ∈ winRounds sequence, supportCount sequence round) ≤
          budget + predictedWinSupport)
    (hquota :
      ∀ sequence, feasibleSequence sequence →
        ∀ round ∈ winRounds sequence,
          quota ≤ supportCount sequence round) :
    ∀ sequence, feasibleSequence sequence →
      quota * winCount sequence ≤ budget + predictedWinSupport := by
  intro sequence hfeasible
  rw [hwinCount_eq sequence hfeasible]
  exact le_trans
    (EconCSLib.FiniteSum.nat_card_mul_le_sum_of_forall_le
      (winRounds sequence) (supportCount sequence)
      (hquota sequence hfeasible))
    (hsupport_sum sequence hfeasible)

/--
Algorithm 7 Predict-Wins accumulator capacity core: if the feasible sequence's
win count is represented by an ordered Predict-Wins list, every counted term
in that list reaches quota, and the loop accumulator is bounded by the
advertised predicted support, then the sequence satisfies the win-capacity
premise used by the quota arithmetic.
-/
theorem sequenceWinCapacity_of_predictWinsSupportAccumulator
    {Sequence Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {feasibleSequence : Sequence → Prop}
    {winCount : Sequence → ℕ}
    {orderedWinners : Sequence → List Candidate}
    {quota budget predictedWinSupport : ℕ}
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        winCount sequence = (orderedWinners sequence).length)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates (orderedWinners sequence) ≤
          predictedWinSupport)
    (hquota :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupportAccumulatorQuota voters ballots candidates quota
          (orderedWinners sequence)) :
    ∀ sequence, feasibleSequence sequence →
      quota * winCount sequence ≤ budget + predictedWinSupport := by
  intro sequence hfeasible
  rw [hwinCount_eq sequence hfeasible]
  exact le_trans
    (quota_mul_length_le_predictWinsSupport_of_accumulatorQuota
      (hquota sequence hfeasible))
    (le_trans (hsupport_le sequence hfeasible)
      (Nat.le_add_left predictedWinSupport budget))

/--
Algorithm 7 budgeted Predict-Wins accumulator capacity core: if each feasible
sequence's ordered winner list reaches quota after assigning budget units to
the listed winners, the total assigned budget is at most the paper budget, and
the support accumulator is bounded by the advertised predicted support, then
the sequence satisfies the win-capacity premise.
-/
theorem sequenceWinCapacity_of_budgetedPredictWinsSupportAccumulator
    {Sequence Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {feasibleSequence : Sequence → Prop}
    {winCount : Sequence → ℕ}
    {orderedWinners : Sequence → List Candidate}
    {assignedBudget : Sequence → Candidate → ℕ}
    {quota budget predictedWinSupport : ℕ}
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        winCount sequence = (orderedWinners sequence).length)
    (hassignedBudget_le :
      ∀ sequence, feasibleSequence sequence →
        ((orderedWinners sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates (orderedWinners sequence) ≤
          predictedWinSupport)
    (hquota :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupportBudgetAccumulatorQuota voters ballots candidates
          (assignedBudget sequence) quota (orderedWinners sequence)) :
    ∀ sequence, feasibleSequence sequence →
      quota * winCount sequence ≤ budget + predictedWinSupport := by
  intro sequence hfeasible
  rw [hwinCount_eq sequence hfeasible]
  exact le_trans
    (quota_mul_length_le_budget_sum_add_predictWinsSupport_of_budgetAccumulatorQuota
      (hquota sequence hfeasible))
    (Nat.add_le_add
      (hassignedBudget_le sequence hfeasible)
      (hsupport_le sequence hfeasible))

/--
Closed Algorithm 7 quota-block coverage core: disjoint quota-sized support
blocks give the win-capacity premise, and therefore the retained win/loss
bounds cover every feasible sequence.
-/
theorem sequenceBoundsCover_of_quotaBlocks
    {Sequence Round SupportUnit : Type*} [DecidableEq SupportUnit]
    {feasibleSequence : Sequence → Prop}
    {winRounds : Sequence → Finset Round}
    {winCount initialLossCount : Sequence → ℕ}
    {capacityPool : Sequence → Finset SupportUnit}
    {seats budget predictedWinSupport quota lowerInitialLosses : ℕ}
    (quotaBlock : Sequence → Round → Finset SupportUnit)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence → winCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        winCount sequence = (winRounds sequence).card)
    (hcapacity :
      ∀ sequence, feasibleSequence sequence →
        (capacityPool sequence).card ≤ budget + predictedWinSupport)
    (hdisjoint :
      ∀ sequence, feasibleSequence sequence →
        ((winRounds sequence : Set Round).PairwiseDisjoint
          (quotaBlock sequence)))
    (hsubset :
      ∀ sequence, feasibleSequence sequence →
        ∀ round ∈ winRounds sequence,
          quotaBlock sequence round ⊆ capacityPool sequence)
    (hquota :
      ∀ sequence, feasibleSequence sequence →
        ∀ round ∈ winRounds sequence,
          quota ≤ (quotaBlock sequence round).card)
    (hloss_floor :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ initialLossCount sequence) :
    sequenceBoundsCover feasibleSequence winCount initialLossCount
      (sequenceReductionBoundsFromPredictions
        seats budget predictedWinSupport quota lowerInitialLosses) := by
  exact sequenceBoundsCover_of_predictiveCapacity
    hquota_pos hseat
    (sequenceWinCapacity_of_quotaBlocks
      (quotaBlock := quotaBlock)
      hwinCount_eq hcapacity hdisjoint hsubset hquota)
    hloss_floor

/--
Closed Algorithm 7 support-sum coverage core: the counted Predict-Wins support
sum gives the win-capacity premise, and therefore the retained win/loss bounds
cover every feasible sequence.
-/
theorem sequenceBoundsCover_of_quotaSupportSum
    {Sequence Round : Type*}
    {feasibleSequence : Sequence → Prop}
    {winRounds : Sequence → Finset Round}
    {winCount initialLossCount : Sequence → ℕ}
    {supportCount : Sequence → Round → ℕ}
    {seats budget predictedWinSupport quota lowerInitialLosses : ℕ}
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence → winCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        winCount sequence = (winRounds sequence).card)
    (hsupport_sum :
      ∀ sequence, feasibleSequence sequence →
        (∑ round ∈ winRounds sequence, supportCount sequence round) ≤
          budget + predictedWinSupport)
    (hquota :
      ∀ sequence, feasibleSequence sequence →
        ∀ round ∈ winRounds sequence,
          quota ≤ supportCount sequence round)
    (hloss_floor :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ initialLossCount sequence) :
    sequenceBoundsCover feasibleSequence winCount initialLossCount
      (sequenceReductionBoundsFromPredictions
        seats budget predictedWinSupport quota lowerInitialLosses) := by
  exact sequenceBoundsCover_of_predictiveCapacity
    hquota_pos hseat
    (sequenceWinCapacity_of_quotaSupportSum
      hwinCount_eq hsupport_sum hquota)
    hloss_floor

/--
Closed Algorithm 7 Predict-Wins accumulator coverage core: the ordered
Predict-Wins support accumulator gives the win-capacity premise, and therefore
the retained win/loss bounds cover every feasible sequence.
-/
theorem sequenceBoundsCover_of_predictWinsSupportAccumulator
    {Sequence Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {feasibleSequence : Sequence → Prop}
    {winCount initialLossCount : Sequence → ℕ}
    {orderedWinners : Sequence → List Candidate}
    {seats budget predictedWinSupport quota lowerInitialLosses : ℕ}
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence → winCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        winCount sequence = (orderedWinners sequence).length)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates (orderedWinners sequence) ≤
          predictedWinSupport)
    (hquota :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupportAccumulatorQuota voters ballots candidates quota
          (orderedWinners sequence))
    (hloss_floor :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ initialLossCount sequence) :
    sequenceBoundsCover feasibleSequence winCount initialLossCount
      (sequenceReductionBoundsFromPredictions
        seats budget predictedWinSupport quota lowerInitialLosses) := by
  exact sequenceBoundsCover_of_predictiveCapacity
    hquota_pos hseat
    (sequenceWinCapacity_of_predictWinsSupportAccumulator
      hwinCount_eq hsupport_le hquota)
    hloss_floor

/--
Closed Algorithm 7 budgeted Predict-Wins accumulator coverage core: assigned
budget units plus counted strict support give the win-capacity premise, and
therefore the retained win/loss bounds cover every feasible sequence.
-/
theorem sequenceBoundsCover_of_budgetedPredictWinsSupportAccumulator
    {Sequence Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {feasibleSequence : Sequence → Prop}
    {winCount initialLossCount : Sequence → ℕ}
    {orderedWinners : Sequence → List Candidate}
    {assignedBudget : Sequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota lowerInitialLosses : ℕ}
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence → winCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        winCount sequence = (orderedWinners sequence).length)
    (hassignedBudget_le :
      ∀ sequence, feasibleSequence sequence →
        ((orderedWinners sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates (orderedWinners sequence) ≤
          predictedWinSupport)
    (hquota :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupportBudgetAccumulatorQuota voters ballots candidates
          (assignedBudget sequence) quota (orderedWinners sequence))
    (hloss_floor :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ initialLossCount sequence) :
    sequenceBoundsCover feasibleSequence winCount initialLossCount
      (sequenceReductionBoundsFromPredictions
        seats budget predictedWinSupport quota lowerInitialLosses) := by
  exact sequenceBoundsCover_of_predictiveCapacity
    hquota_pos hseat
    (sequenceWinCapacity_of_budgetedPredictWinsSupportAccumulator
      hwinCount_eq hassignedBudget_le hsupport_le hquota)
    hloss_floor

/--
Closed Algorithm 7 route with both source loops visible: budgeted Predict-Wins
gives the win-capacity premise, and Predict-Losses prefix certificates give
the lower-initial-loss premise.
-/
theorem sequenceBoundsCover_of_budgetedPredictWinsSupportAccumulator_and_predictLossesPrefixes
    {Sequence Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {feasibleSequence : Sequence → Prop}
    {winCount initialLossCount : Sequence → ℕ}
    {orderedWinners : Sequence → List Candidate}
    {assignedBudget : Sequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      lowerInitialLosses : ℕ}
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence → winCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        winCount sequence = (orderedWinners sequence).length)
    (hassignedBudget_le :
      ∀ sequence, feasibleSequence sequence →
        ((orderedWinners sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates (orderedWinners sequence) ≤
          predictedWinSupport)
    (hquota :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupportBudgetAccumulatorQuota voters ballots candidates
          (assignedBudget sequence) quota (orderedWinners sequence))
    (hloss_prefix :
      ∀ sequence, feasibleSequence sequence →
        PredictLossesInitialLossPrefixCertificate voters ballots candidates
          budget firstChoiceThreshold initialLossCount lowerInitialLosses
          sequence) :
    sequenceBoundsCover feasibleSequence winCount initialLossCount
      (sequenceReductionBoundsFromPredictions
        seats budget predictedWinSupport quota lowerInitialLosses) := by
  exact sequenceBoundsCover_of_budgetedPredictWinsSupportAccumulator
    hquota_pos hseat hwinCount_eq hassignedBudget_le hsupport_le hquota
    (loss_floor_of_predictLossesPrefixCertificates hloss_prefix)

/--
Closed Algorithm 7 route from prefix-form Predict-Wins facts: the per-prefix
budgeted quota condition constructs the recursive accumulator internally, and
Predict-Losses prefix certificates give the lower-initial-loss premise.
-/
theorem sequenceBoundsCover_of_budgetedPredictWinsAtPrefixes_and_predictLossesPrefixes
    {Sequence Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {feasibleSequence : Sequence → Prop}
    {winCount initialLossCount : Sequence → ℕ}
    {orderedWinners : Sequence → List Candidate}
    {assignedBudget : Sequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      lowerInitialLosses : ℕ}
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence → winCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        winCount sequence = (orderedWinners sequence).length)
    (hassignedBudget_le :
      ∀ sequence, feasibleSequence sequence →
        ((orderedWinners sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates (orderedWinners sequence) ≤
          predictedWinSupport)
    (hquota_prefix :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupportBudgetAccumulatorQuotaAtPrefixes voters ballots
          candidates (assignedBudget sequence) quota
          (orderedWinners sequence))
    (hloss_prefix :
      ∀ sequence, feasibleSequence sequence →
        PredictLossesInitialLossPrefixCertificate voters ballots candidates
          budget firstChoiceThreshold initialLossCount lowerInitialLosses
          sequence) :
    sequenceBoundsCover feasibleSequence winCount initialLossCount
      (sequenceReductionBoundsFromPredictions
        seats budget predictedWinSupport quota lowerInitialLosses) := by
  exact sequenceBoundsCover_of_budgetedPredictWinsSupportAccumulator_and_predictLossesPrefixes
    hquota_pos hseat hwinCount_eq hassignedBudget_le hsupport_le
    (fun sequence hfeasible =>
      predictWinsSupportBudgetAccumulatorQuota_of_atPrefixes
        (hquota_prefix sequence hfeasible))
    hloss_prefix

/--
Closed Algorithm 7 route from concrete source-loop facts: Predict-Wins
selections are checked by membership in the ready set at their processed
prefix, and Predict-Losses supplies an ordered loop prefix whose length is
semantically justified as an initial-loss lower bound.
-/
theorem sequenceBoundsCover_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes
    {Sequence Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {feasibleSequence : Sequence → Prop}
    {winCount initialLossCount : Sequence → ℕ}
    {orderedWinners lossPrefix : Sequence → List Candidate}
    {assignedBudget : Sequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      lowerInitialLosses : ℕ}
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence → winCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        winCount sequence = (orderedWinners sequence).length)
    (hassignedBudget_le :
      ∀ sequence, feasibleSequence sequence →
        ((orderedWinners sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates (orderedWinners sequence) ≤
          predictedWinSupport)
    (hselected :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          orderedWinners sequence = pref ++ candidate :: suffix →
            candidate ∈
              predictWinsBudgetReadyCandidatesAtPrefix voters ballots
                candidates (assignedBudget sequence) quota pref)
    (hloss_loop :
      ∀ sequence, feasibleSequence sequence →
        PredictLossesLoopPrefix voters ballots candidates budget
          firstChoiceThreshold (lossPrefix sequence))
    (hlower :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ (lossPrefix sequence).length)
    (hinitial :
      ∀ sequence, feasibleSequence sequence →
        (lossPrefix sequence).length ≤ initialLossCount sequence) :
    sequenceBoundsCover feasibleSequence winCount initialLossCount
      (sequenceReductionBoundsFromPredictions
        seats budget predictedWinSupport quota lowerInitialLosses) := by
  exact sequenceBoundsCover_of_budgetedPredictWinsAtPrefixes_and_predictLossesPrefixes
    hquota_pos hseat hwinCount_eq hassignedBudget_le hsupport_le
    (fun sequence hfeasible =>
      predictWinsSupportBudgetAccumulatorQuotaAtPrefixes_of_mem_budgetReadyCandidatesAtPrefix
        (hselected sequence hfeasible))
    (fun sequence hfeasible =>
      predictLossesInitialLossPrefixCertificate_of_loopPrefix
        (hloss_loop sequence hfeasible) (hlower sequence hfeasible)
        (hinitial sequence hfeasible))

/--
Concrete RCV-sequence Algorithm 7 route: the initial-loss semantic obligation
is the source-shaped statement that the first `lossPrefix.length` labels of
the win/loss sequence are losing rounds.
-/
theorem sequenceBoundsCover_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes_rcvSequence
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {feasibleSequence : RCVSequence → Prop}
    {orderedWinners lossPrefix : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      lowerInitialLosses : ℕ}
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (orderedWinners sequence).length)
    (hassignedBudget_le :
      ∀ sequence, feasibleSequence sequence →
        ((orderedWinners sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates (orderedWinners sequence) ≤
          predictedWinSupport)
    (hselected :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          orderedWinners sequence = pref ++ candidate :: suffix →
            candidate ∈
              predictWinsBudgetReadyCandidatesAtPrefix voters ballots
                candidates (assignedBudget sequence) quota pref)
    (hloss_loop :
      ∀ sequence, feasibleSequence sequence →
        PredictLossesLoopPrefix voters ballots candidates budget
          firstChoiceThreshold (lossPrefix sequence))
    (hlower :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ (lossPrefix sequence).length)
    (hinitial_prefix :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceHasInitialLossPrefix sequence
          (lossPrefix sequence).length) :
    sequenceBoundsCover feasibleSequence rcvSequenceWinCount
      rcvSequenceInitialLossCount
      (sequenceReductionBoundsFromPredictions
        seats budget predictedWinSupport quota lowerInitialLosses) := by
  exact
    sequenceBoundsCover_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes
      (winCount := rcvSequenceWinCount)
      (initialLossCount := rcvSequenceInitialLossCount)
      hquota_pos hseat hwinCount_eq hassignedBudget_le hsupport_le
      hselected hloss_loop hlower
      (fun sequence hfeasible =>
        lossPrefix_length_le_rcvSequenceInitialLossCount_of_initialLossPrefix
          (hinitial_prefix sequence hfeasible))

/--
Concrete RCV-trace Algorithm 7 route: the initial-loss semantic obligation is
checked from the deterministic trace whose first source steps are eliminations,
then replayed through the trace-derived win/loss sequence.
-/
theorem sequenceBoundsCover_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes_rcvTrace
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {feasibleSequence : RCVSequence → Prop}
    {orderedWinners lossPrefix : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      lowerInitialLosses : ℕ}
    (traceOf : RCVSequence → RCVTrace Candidate)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (orderedWinners sequence).length)
    (hassignedBudget_le :
      ∀ sequence, feasibleSequence sequence →
        ((orderedWinners sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates (orderedWinners sequence) ≤
          predictedWinSupport)
    (hselected :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          orderedWinners sequence = pref ++ candidate :: suffix →
            candidate ∈
              predictWinsBudgetReadyCandidatesAtPrefix voters ballots
                candidates (assignedBudget sequence) quota pref)
    (hloss_loop :
      ∀ sequence, feasibleSequence sequence →
        PredictLossesLoopPrefix voters ballots candidates budget
          firstChoiceThreshold (lossPrefix sequence))
    (hlower :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ (lossPrefix sequence).length)
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_prefix :
      ∀ sequence, feasibleSequence sequence →
        (traceOf sequence).HasInitialEliminationPrefix
          (lossPrefix sequence).length) :
    sequenceBoundsCover feasibleSequence rcvSequenceWinCount
      rcvSequenceInitialLossCount
      (sequenceReductionBoundsFromPredictions
        seats budget predictedWinSupport quota lowerInitialLosses) := by
  exact
    sequenceBoundsCover_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes_rcvSequence
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (feasibleSequence := feasibleSequence)
      (orderedWinners := orderedWinners)
      (lossPrefix := lossPrefix)
      (assignedBudget := assignedBudget)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (lowerInitialLosses := lowerInitialLosses)
      hquota_pos hseat hwinCount_eq hassignedBudget_le hsupport_le
      hselected hloss_loop hlower
      (fun sequence hfeasible =>
        rcvSequenceHasInitialLossPrefix_of_trace_initialEliminationPrefix
          (hsequence_eq sequence hfeasible)
          (htrace_prefix sequence hfeasible))

/--
The reduced sequence family generated by retaining only sequences satisfying
the Algorithm 7 win/loss bounds.
-/
def boundedSequenceFamily {Sequence : Type*}
    (allSequences : Finset Sequence)
    (winCount initialLossCount : Sequence → ℕ)
    (bounds : SequenceReductionBounds) : Finset Sequence :=
  allSequences.filter fun sequence =>
    winCount sequence ≤ bounds.upperWins ∧
      bounds.lowerInitialLosses ≤ initialLossCount sequence

/-- A reduced sequence family covers every feasible source sequence. -/
def sequenceFamilyCovers {Sequence : Type*}
    (feasibleSequence : Sequence → Prop)
    (family : Finset Sequence) : Prop :=
  ∀ sequence, feasibleSequence sequence → sequence ∈ family

/--
Concrete Proposition 3.4 specification: the returned sequence family covers
every feasible sequence from the source model.
-/
def sequenceReductionConcreteCoverageSpecification {Sequence : Type*}
    (feasibleSequence : Sequence → Prop) (reduced : Finset Sequence) : Prop :=
  sequenceFamilyCovers feasibleSequence reduced

/--
Concrete source problem for Algorithm 7 sequence reduction. Its specification
is exactly the coverage predicate for the source feasible-sequence family.
-/
def sequenceReductionConcreteCoverageProblem {Sequence : Type*}
    (feasibleSequence : Sequence → Prop)
    (budget uniqueBallotCount candidateCount : ℕ) :
    SequenceReductionProblem (Finset Sequence) where
  specification := sequenceReductionConcreteCoverageSpecification feasibleSequence
  budget := budget
  uniqueBallotCount := uniqueBallotCount
  candidateCount := candidateCount

/--
Exact operation-count model for Algorithm 7's strict-support sweeps and
bookkeeping loops.
-/
def sequenceReductionOperationCount
    (uniqueBallotCount candidateCount : ℕ) : ℕ :=
  uniqueBallotCount * candidateCount ^ 2

/--
Concrete Algorithm 7 implementation on a fixed source model: keep exactly the
bounded sequence family computed from the Predict-Wins/Predict-Losses bounds.
-/
def sequenceReductionConcreteCoverageAlgorithm
    {Sequence : Type*}
    (allSequences : Finset Sequence)
    (winCount initialLossCount : Sequence → ℕ)
    (seats predictedWinSupport quota lowerInitialLosses : ℕ) :
    SequenceReductionProblem (Finset Sequence) → Finset Sequence :=
  fun problem =>
    boundedSequenceFamily allSequences winCount initialLossCount
      (sequenceReductionBoundsFromPredictions
        seats problem.budget predictedWinSupport quota lowerInitialLosses)

/-- Concrete Algorithm 7 operation-count implementation. -/
def sequenceReductionConcreteCoverageOperationCount
    {Sequence : Type*} :
    SequenceReductionProblem (Finset Sequence) → ℕ :=
  fun problem =>
    sequenceReductionOperationCount
      problem.uniqueBallotCount problem.candidateCount

/-- The bounded sequence family is a subfamily of the original search space. -/
theorem boundedSequenceFamily_subset_allSequences
    {Sequence : Type*}
    {allSequences : Finset Sequence}
    {winCount initialLossCount : Sequence → ℕ}
    {bounds : SequenceReductionBounds} :
    boundedSequenceFamily allSequences winCount initialLossCount bounds ⊆
      allSequences := by
  intro sequence hsequence
  exact (Finset.mem_filter.mp hsequence).1

/--
Closed Proposition 3.4 coverage core: if Algorithm 7's bounds hold for every
feasible sequence, then the bounded sequence family covers every feasible
sequence.
-/
theorem boundedSequenceFamily_covers_of_sequenceBoundsCover
    {Sequence : Type*}
    {allSequences : Finset Sequence}
    {feasibleSequence : Sequence → Prop}
    {winCount initialLossCount : Sequence → ℕ}
    {bounds : SequenceReductionBounds}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hcover :
      sequenceBoundsCover feasibleSequence winCount initialLossCount bounds) :
    sequenceFamilyCovers feasibleSequence
      (boundedSequenceFamily allSequences winCount initialLossCount bounds) := by
  intro sequence hfeasible
  have hbounds := hcover sequence hfeasible
  simp [boundedSequenceFamily, hall sequence hfeasible, hbounds.1, hbounds.2]

/--
Concrete Proposition 3.4 coverage/runtime core: once Algorithm 7's bounds cover
every feasible sequence, the retained family covers every feasible sequence and
the exact Algorithm 7 operation-count model is bounded by `m * n^2`.
-/
theorem boundedSequenceFamily_covers_and_quadraticRuntime_of_sequenceBoundsCover
    {Sequence : Type*}
    {allSequences : Finset Sequence}
    {feasibleSequence : Sequence → Prop}
    {winCount initialLossCount : Sequence → ℕ}
    {bounds : SequenceReductionBounds}
    (uniqueBallotCount candidateCount : ℕ)
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hcover :
      sequenceBoundsCover feasibleSequence winCount initialLossCount bounds) :
    sequenceFamilyCovers feasibleSequence
        (boundedSequenceFamily allSequences winCount initialLossCount bounds) ∧
      sequenceReductionOperationCount uniqueBallotCount candidateCount ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact ⟨
    boundedSequenceFamily_covers_of_sequenceBoundsCover hall hcover,
    le_rfl⟩

/--
Concrete Proposition 3.4 route from Algorithm 7's capacity/loss-floor
premises: the retained sequence family covers every feasible sequence and the
exact Algorithm 7 operation-count model is bounded by `m * n^2`.
-/
theorem proposition3_4_boundedSequenceFamily_covers_and_quadraticRuntime_of_predictionCapacity
    {Sequence : Type*}
    {allSequences : Finset Sequence}
    {feasibleSequence : Sequence → Prop}
    {winCount initialLossCount : Sequence → ℕ}
    {seats budget predictedWinSupport quota lowerInitialLosses : ℕ}
    (uniqueBallotCount candidateCount : ℕ)
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence → winCount sequence ≤ seats)
    (hcapacity :
      ∀ sequence, feasibleSequence sequence →
        quota * winCount sequence ≤ budget + predictedWinSupport)
    (hloss_floor :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ initialLossCount sequence) :
    sequenceFamilyCovers feasibleSequence
        (boundedSequenceFamily allSequences winCount initialLossCount
          (sequenceReductionBoundsFromPredictions
            seats budget predictedWinSupport quota lowerInitialLosses)) ∧
      sequenceReductionOperationCount uniqueBallotCount candidateCount ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    boundedSequenceFamily_covers_and_quadraticRuntime_of_sequenceBoundsCover
      uniqueBallotCount candidateCount hall
      (sequenceBoundsCover_of_predictiveCapacity
        hquota_pos hseat hcapacity hloss_floor)

/--
Concrete Proposition 3.4 quota-block route: pairwise-disjoint quota-sized
support blocks give the Algorithm 7 capacity premise, so the retained sequence
family covers every feasible sequence and has the exact quadratic
operation-count model.
-/
theorem proposition3_4_boundedSequenceFamily_covers_and_quadraticRuntime_of_quotaBlocks
    {Sequence Round SupportUnit : Type*} [DecidableEq SupportUnit]
    {allSequences : Finset Sequence}
    {feasibleSequence : Sequence → Prop}
    {winRounds : Sequence → Finset Round}
    {winCount initialLossCount : Sequence → ℕ}
    {capacityPool : Sequence → Finset SupportUnit}
    {seats budget predictedWinSupport quota lowerInitialLosses : ℕ}
    (quotaBlock : Sequence → Round → Finset SupportUnit)
    (uniqueBallotCount candidateCount : ℕ)
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence → winCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        winCount sequence = (winRounds sequence).card)
    (hcapacity :
      ∀ sequence, feasibleSequence sequence →
        (capacityPool sequence).card ≤ budget + predictedWinSupport)
    (hdisjoint :
      ∀ sequence, feasibleSequence sequence →
        ((winRounds sequence : Set Round).PairwiseDisjoint
          (quotaBlock sequence)))
    (hsubset :
      ∀ sequence, feasibleSequence sequence →
        ∀ round ∈ winRounds sequence,
          quotaBlock sequence round ⊆ capacityPool sequence)
    (hquota :
      ∀ sequence, feasibleSequence sequence →
        ∀ round ∈ winRounds sequence,
          quota ≤ (quotaBlock sequence round).card)
    (hloss_floor :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ initialLossCount sequence) :
    sequenceFamilyCovers feasibleSequence
        (boundedSequenceFamily allSequences winCount initialLossCount
          (sequenceReductionBoundsFromPredictions
            seats budget predictedWinSupport quota lowerInitialLosses)) ∧
      sequenceReductionOperationCount uniqueBallotCount candidateCount ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    boundedSequenceFamily_covers_and_quadraticRuntime_of_sequenceBoundsCover
      uniqueBallotCount candidateCount hall
      (sequenceBoundsCover_of_quotaBlocks
        (quotaBlock := quotaBlock)
        hquota_pos hseat hwinCount_eq hcapacity hdisjoint hsubset hquota
        hloss_floor)

/--
Concrete Proposition 3.4 support-sum route: Algorithm 7's counted
Predict-Wins support accumulator gives the win-capacity premise directly, so
the retained sequence family covers every feasible sequence and has the exact
quadratic operation-count model.
-/
theorem proposition3_4_boundedSequenceFamily_covers_and_quadraticRuntime_of_quotaSupportSum
    {Sequence Round : Type*}
    {allSequences : Finset Sequence}
    {feasibleSequence : Sequence → Prop}
    {winRounds : Sequence → Finset Round}
    {winCount initialLossCount : Sequence → ℕ}
    {supportCount : Sequence → Round → ℕ}
    {seats budget predictedWinSupport quota lowerInitialLosses : ℕ}
    (uniqueBallotCount candidateCount : ℕ)
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence → winCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        winCount sequence = (winRounds sequence).card)
    (hsupport_sum :
      ∀ sequence, feasibleSequence sequence →
        (∑ round ∈ winRounds sequence, supportCount sequence round) ≤
          budget + predictedWinSupport)
    (hquota :
      ∀ sequence, feasibleSequence sequence →
        ∀ round ∈ winRounds sequence,
          quota ≤ supportCount sequence round)
    (hloss_floor :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ initialLossCount sequence) :
    sequenceFamilyCovers feasibleSequence
        (boundedSequenceFamily allSequences winCount initialLossCount
          (sequenceReductionBoundsFromPredictions
            seats budget predictedWinSupport quota lowerInitialLosses)) ∧
      sequenceReductionOperationCount uniqueBallotCount candidateCount ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    boundedSequenceFamily_covers_and_quadraticRuntime_of_sequenceBoundsCover
      uniqueBallotCount candidateCount hall
      (sequenceBoundsCover_of_quotaSupportSum
        hquota_pos hseat hwinCount_eq hsupport_sum hquota hloss_floor)

/--
Concrete Proposition 3.4 Predict-Wins accumulator route: the ordered
Predict-Wins support accumulator gives the win-capacity premise directly, so
the retained sequence family covers every feasible sequence and has the exact
quadratic operation-count model.
-/
theorem proposition3_4_boundedSequenceFamily_covers_and_quadraticRuntime_of_predictWinsSupportAccumulator
    {Sequence Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset Sequence}
    {feasibleSequence : Sequence → Prop}
    {winCount initialLossCount : Sequence → ℕ}
    {orderedWinners : Sequence → List Candidate}
    {seats budget predictedWinSupport quota lowerInitialLosses : ℕ}
    (uniqueBallotCount candidateCount : ℕ)
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence → winCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        winCount sequence = (orderedWinners sequence).length)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates (orderedWinners sequence) ≤
          predictedWinSupport)
    (hquota :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupportAccumulatorQuota voters ballots candidates quota
          (orderedWinners sequence))
    (hloss_floor :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ initialLossCount sequence) :
    sequenceFamilyCovers feasibleSequence
        (boundedSequenceFamily allSequences winCount initialLossCount
          (sequenceReductionBoundsFromPredictions
            seats budget predictedWinSupport quota lowerInitialLosses)) ∧
      sequenceReductionOperationCount uniqueBallotCount candidateCount ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    boundedSequenceFamily_covers_and_quadraticRuntime_of_sequenceBoundsCover
      uniqueBallotCount candidateCount hall
      (sequenceBoundsCover_of_predictWinsSupportAccumulator
        hquota_pos hseat hwinCount_eq hsupport_le hquota hloss_floor)

/--
Concrete Proposition 3.4 budgeted Predict-Wins accumulator route: the ordered
Predict-Wins support accumulator plus the assigned addition budget gives the
win-capacity premise directly, so the retained sequence family covers every
feasible sequence and has the exact quadratic operation-count model.
-/
theorem proposition3_4_boundedSequenceFamily_covers_and_quadraticRuntime_of_budgetedPredictWinsSupportAccumulator
    {Sequence Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset Sequence}
    {feasibleSequence : Sequence → Prop}
    {winCount initialLossCount : Sequence → ℕ}
    {orderedWinners : Sequence → List Candidate}
    {assignedBudget : Sequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota lowerInitialLosses : ℕ}
    (uniqueBallotCount candidateCount : ℕ)
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence → winCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        winCount sequence = (orderedWinners sequence).length)
    (hassignedBudget_le :
      ∀ sequence, feasibleSequence sequence →
        ((orderedWinners sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates (orderedWinners sequence) ≤
          predictedWinSupport)
    (hquota :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupportBudgetAccumulatorQuota voters ballots candidates
          (assignedBudget sequence) quota (orderedWinners sequence))
    (hloss_floor :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ initialLossCount sequence) :
    sequenceFamilyCovers feasibleSequence
        (boundedSequenceFamily allSequences winCount initialLossCount
          (sequenceReductionBoundsFromPredictions
            seats budget predictedWinSupport quota lowerInitialLosses)) ∧
      sequenceReductionOperationCount uniqueBallotCount candidateCount ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    boundedSequenceFamily_covers_and_quadraticRuntime_of_sequenceBoundsCover
      uniqueBallotCount candidateCount hall
      (sequenceBoundsCover_of_budgetedPredictWinsSupportAccumulator
        hquota_pos hseat hwinCount_eq hassignedBudget_le hsupport_le hquota
        hloss_floor)

/--
Concrete Proposition 3.4 route with both Algorithm 7 loops exposed:
budgeted Predict-Wins supplies the win-capacity premise and Predict-Losses
prefix certificates supply the lower-initial-loss premise.
-/
theorem proposition3_4_boundedSequenceFamily_covers_and_quadraticRuntime_of_budgetedPredictWinsSupportAccumulator_and_predictLossesPrefixes
    {Sequence Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset Sequence}
    {feasibleSequence : Sequence → Prop}
    {winCount initialLossCount : Sequence → ℕ}
    {orderedWinners : Sequence → List Candidate}
    {assignedBudget : Sequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      lowerInitialLosses : ℕ}
    (uniqueBallotCount candidateCount : ℕ)
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence → winCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        winCount sequence = (orderedWinners sequence).length)
    (hassignedBudget_le :
      ∀ sequence, feasibleSequence sequence →
        ((orderedWinners sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates (orderedWinners sequence) ≤
          predictedWinSupport)
    (hquota :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupportBudgetAccumulatorQuota voters ballots candidates
          (assignedBudget sequence) quota (orderedWinners sequence))
    (hloss_prefix :
      ∀ sequence, feasibleSequence sequence →
        PredictLossesInitialLossPrefixCertificate voters ballots candidates
          budget firstChoiceThreshold initialLossCount lowerInitialLosses
          sequence) :
    sequenceFamilyCovers feasibleSequence
        (boundedSequenceFamily allSequences winCount initialLossCount
          (sequenceReductionBoundsFromPredictions
            seats budget predictedWinSupport quota lowerInitialLosses)) ∧
      sequenceReductionOperationCount uniqueBallotCount candidateCount ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    boundedSequenceFamily_covers_and_quadraticRuntime_of_sequenceBoundsCover
      uniqueBallotCount candidateCount hall
      (sequenceBoundsCover_of_budgetedPredictWinsSupportAccumulator_and_predictLossesPrefixes
        hquota_pos hseat hwinCount_eq hassignedBudget_le hsupport_le hquota
        hloss_prefix)

/--
Concrete Proposition 3.4 route from prefix-form Algorithm 7 loop facts:
per-prefix budgeted Predict-Wins quota facts construct the accumulator
internally, while Predict-Losses prefix witnesses supply the loss floor.
-/
theorem proposition3_4_boundedSequenceFamily_covers_and_quadraticRuntime_of_budgetedPredictWinsAtPrefixes_and_predictLossesPrefixes
    {Sequence Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset Sequence}
    {feasibleSequence : Sequence → Prop}
    {winCount initialLossCount : Sequence → ℕ}
    {orderedWinners : Sequence → List Candidate}
    {assignedBudget : Sequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      lowerInitialLosses : ℕ}
    (uniqueBallotCount candidateCount : ℕ)
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence → winCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        winCount sequence = (orderedWinners sequence).length)
    (hassignedBudget_le :
      ∀ sequence, feasibleSequence sequence →
        ((orderedWinners sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates (orderedWinners sequence) ≤
          predictedWinSupport)
    (hquota_prefix :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupportBudgetAccumulatorQuotaAtPrefixes voters ballots
          candidates (assignedBudget sequence) quota
          (orderedWinners sequence))
    (hloss_prefix :
      ∀ sequence, feasibleSequence sequence →
        PredictLossesInitialLossPrefixCertificate voters ballots candidates
          budget firstChoiceThreshold initialLossCount lowerInitialLosses
          sequence) :
    sequenceFamilyCovers feasibleSequence
        (boundedSequenceFamily allSequences winCount initialLossCount
          (sequenceReductionBoundsFromPredictions
            seats budget predictedWinSupport quota lowerInitialLosses)) ∧
      sequenceReductionOperationCount uniqueBallotCount candidateCount ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    boundedSequenceFamily_covers_and_quadraticRuntime_of_sequenceBoundsCover
      uniqueBallotCount candidateCount hall
      (sequenceBoundsCover_of_budgetedPredictWinsAtPrefixes_and_predictLossesPrefixes
        hquota_pos hseat hwinCount_eq hassignedBudget_le hsupport_le
        hquota_prefix hloss_prefix)

/--
Concrete Proposition 3.4 route from source-loop facts: Predict-Wins
selections are certified by current-prefix ready-set membership, and
Predict-Losses supplies a loop prefix whose length is justified as an initial
loss lower bound.
-/
theorem proposition3_4_boundedSequenceFamily_covers_and_quadraticRuntime_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes
    {Sequence Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset Sequence}
    {feasibleSequence : Sequence → Prop}
    {winCount initialLossCount : Sequence → ℕ}
    {orderedWinners lossPrefix : Sequence → List Candidate}
    {assignedBudget : Sequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      lowerInitialLosses : ℕ}
    (uniqueBallotCount candidateCount : ℕ)
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence → winCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        winCount sequence = (orderedWinners sequence).length)
    (hassignedBudget_le :
      ∀ sequence, feasibleSequence sequence →
        ((orderedWinners sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates (orderedWinners sequence) ≤
          predictedWinSupport)
    (hselected :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          orderedWinners sequence = pref ++ candidate :: suffix →
            candidate ∈
              predictWinsBudgetReadyCandidatesAtPrefix voters ballots
                candidates (assignedBudget sequence) quota pref)
    (hloss_loop :
      ∀ sequence, feasibleSequence sequence →
        PredictLossesLoopPrefix voters ballots candidates budget
          firstChoiceThreshold (lossPrefix sequence))
    (hlower :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ (lossPrefix sequence).length)
    (hinitial :
      ∀ sequence, feasibleSequence sequence →
        (lossPrefix sequence).length ≤ initialLossCount sequence) :
    sequenceFamilyCovers feasibleSequence
        (boundedSequenceFamily allSequences winCount initialLossCount
          (sequenceReductionBoundsFromPredictions
            seats budget predictedWinSupport quota lowerInitialLosses)) ∧
      sequenceReductionOperationCount uniqueBallotCount candidateCount ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    boundedSequenceFamily_covers_and_quadraticRuntime_of_sequenceBoundsCover
      uniqueBallotCount candidateCount hall
      (sequenceBoundsCover_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes
        hquota_pos hseat hwinCount_eq hassignedBudget_le hsupport_le
        hselected hloss_loop hlower hinitial)

/--
Concrete RCV-sequence Proposition 3.4 route: Predict-Wins source-loop
ready-set facts and a losing-label prefix in the win/loss sequence prove
coverage of the retained bounded family and the exact quadratic runtime bound.
-/
theorem proposition3_4_boundedSequenceFamily_covers_and_quadraticRuntime_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes_rcvSequence
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {orderedWinners lossPrefix : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      lowerInitialLosses : ℕ}
    (uniqueBallotCount candidateCount : ℕ)
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (orderedWinners sequence).length)
    (hassignedBudget_le :
      ∀ sequence, feasibleSequence sequence →
        ((orderedWinners sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates (orderedWinners sequence) ≤
          predictedWinSupport)
    (hselected :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          orderedWinners sequence = pref ++ candidate :: suffix →
            candidate ∈
              predictWinsBudgetReadyCandidatesAtPrefix voters ballots
                candidates (assignedBudget sequence) quota pref)
    (hloss_loop :
      ∀ sequence, feasibleSequence sequence →
        PredictLossesLoopPrefix voters ballots candidates budget
          firstChoiceThreshold (lossPrefix sequence))
    (hlower :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ (lossPrefix sequence).length)
    (hinitial_prefix :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceHasInitialLossPrefix sequence
          (lossPrefix sequence).length) :
    sequenceFamilyCovers feasibleSequence
        (boundedSequenceFamily allSequences rcvSequenceWinCount
          rcvSequenceInitialLossCount
          (sequenceReductionBoundsFromPredictions
            seats budget predictedWinSupport quota lowerInitialLosses)) ∧
      sequenceReductionOperationCount uniqueBallotCount candidateCount ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    boundedSequenceFamily_covers_and_quadraticRuntime_of_sequenceBoundsCover
      uniqueBallotCount candidateCount hall
      (sequenceBoundsCover_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes_rcvSequence
        hquota_pos hseat hwinCount_eq hassignedBudget_le hsupport_le
        hselected hloss_loop hlower hinitial_prefix)

/--
Concrete RCV-trace Proposition 3.4 route: Predict-Wins source-loop ready-set
facts and a trace initial-elimination prefix prove coverage of the retained
bounded family and the exact quadratic runtime bound.
-/
theorem proposition3_4_boundedSequenceFamily_covers_and_quadraticRuntime_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes_rcvTrace
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {orderedWinners lossPrefix : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      lowerInitialLosses : ℕ}
    (traceOf : RCVSequence → RCVTrace Candidate)
    (uniqueBallotCount candidateCount : ℕ)
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (orderedWinners sequence).length)
    (hassignedBudget_le :
      ∀ sequence, feasibleSequence sequence →
        ((orderedWinners sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates (orderedWinners sequence) ≤
          predictedWinSupport)
    (hselected :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          orderedWinners sequence = pref ++ candidate :: suffix →
            candidate ∈
              predictWinsBudgetReadyCandidatesAtPrefix voters ballots
                candidates (assignedBudget sequence) quota pref)
    (hloss_loop :
      ∀ sequence, feasibleSequence sequence →
        PredictLossesLoopPrefix voters ballots candidates budget
          firstChoiceThreshold (lossPrefix sequence))
    (hlower :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ (lossPrefix sequence).length)
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_prefix :
      ∀ sequence, feasibleSequence sequence →
        (traceOf sequence).HasInitialEliminationPrefix
          (lossPrefix sequence).length) :
    sequenceFamilyCovers feasibleSequence
        (boundedSequenceFamily allSequences rcvSequenceWinCount
          rcvSequenceInitialLossCount
          (sequenceReductionBoundsFromPredictions
            seats budget predictedWinSupport quota lowerInitialLosses)) ∧
      sequenceReductionOperationCount uniqueBallotCount candidateCount ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    boundedSequenceFamily_covers_and_quadraticRuntime_of_sequenceBoundsCover
      uniqueBallotCount candidateCount hall
      (sequenceBoundsCover_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes_rcvTrace
        traceOf hquota_pos hseat hwinCount_eq hassignedBudget_le
        hsupport_le hselected hloss_loop hlower hsequence_eq htrace_prefix)

/--
Certificate that sequence-space reduction is sound and satisfies the
Proposition 3.4 quadratic operation bound.
-/
abbrev SequenceReductionCertificate {ReducedSequences : Type*}
    (algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences)
    (operationCount : SequenceReductionProblem ReducedSequences → ℕ) :=
  EconCSLib.Optimization.AlgorithmSoundnessCertificate algorithm
    (fun problem output => problem.specification output)
    operationCount
    SequenceReductionProblem.quadraticRuntimeBound

/--
Source-shaped certificate for the Proposition 3.4 sequence-reduction proof:
the reduced sequence family satisfies the coverage specification and the
operation count satisfies the paper's quadratic bound.
-/
structure SequenceReductionSoundnessCertificate {ReducedSequences : Type*}
    (algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences)
    (operationCount : SequenceReductionProblem ReducedSequences → ℕ) where
  output_spec : ∀ problem : SequenceReductionProblem ReducedSequences,
    problem.specification (algorithm problem)
  operationCount_le : ∀ problem : SequenceReductionProblem ReducedSequences,
    operationCount problem ≤
      SequenceReductionProblem.quadraticRuntimeBound problem

/--
Source-shaped Algorithm 7 certificate for Proposition 3.4.

The certificate records the finite voter/ballot data used to compute the
Predict-Wins and Predict-Losses filters, the resulting sequence bounds, and the
coverage theorem connecting those bounds to the reduced sequence-family
specification.
-/
structure SequenceReductionConditionCertificate
    {ReducedSequences Voter Candidate Sequence : Type*}
    [DecidableEq Candidate]
    (algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences)
    (operationCount : SequenceReductionProblem ReducedSequences → ℕ) where
  voters : SequenceReductionProblem ReducedSequences → Finset Voter
  ballots :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      Voter → RCVBallot Candidate
  candidates :
    SequenceReductionProblem ReducedSequences → Finset Candidate
  quota : SequenceReductionProblem ReducedSequences → ℕ
  firstChoiceThreshold : SequenceReductionProblem ReducedSequences → ℕ
  bounds : SequenceReductionProblem ReducedSequences → SequenceReductionBounds
  feasibleSequence :
    SequenceReductionProblem ReducedSequences → Sequence → Prop
  winCount : SequenceReductionProblem ReducedSequences → Sequence → ℕ
  initialLossCount : SequenceReductionProblem ReducedSequences → Sequence → ℕ
  coverage_condition :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      sequenceBoundsCover
        (feasibleSequence problem) (winCount problem)
        (initialLossCount problem) (bounds problem)
  output_spec_of_coverage :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      sequenceBoundsCover
        (feasibleSequence problem) (winCount problem)
        (initialLossCount problem) (bounds problem) →
        problem.specification (algorithm problem)
  operationCount_le :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      operationCount problem ≤
        SequenceReductionProblem.quadraticRuntimeBound problem

/--
An Algorithm 7 condition certificate gives the source-shaped soundness
certificate expected by the generic soundness projection.
-/
def sequenceReductionSoundnessCertificate_of_conditionCertificate
    {ReducedSequences Voter Candidate Sequence : Type*}
    [DecidableEq Candidate]
    {algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences}
    {operationCount : SequenceReductionProblem ReducedSequences → ℕ}
    (cert :
      SequenceReductionConditionCertificate
        (Voter := Voter) (Candidate := Candidate) (Sequence := Sequence)
        algorithm operationCount) :
    SequenceReductionSoundnessCertificate algorithm operationCount where
  output_spec := by
    intro problem
    exact cert.output_spec_of_coverage problem
      (cert.coverage_condition problem)
  operationCount_le := cert.operationCount_le

/--
An Algorithm 7 condition certificate directly gives the generic soundness
certificate used by the source-facing Proposition 3.4 projection.
-/
def sequenceReductionCertificate_of_conditionCertificate
    {ReducedSequences Voter Candidate Sequence : Type*}
    [DecidableEq Candidate]
    {algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences}
    {operationCount : SequenceReductionProblem ReducedSequences → ℕ}
    (cert :
      SequenceReductionConditionCertificate
        (Voter := Voter) (Candidate := Candidate) (Sequence := Sequence)
        algorithm operationCount) :
    SequenceReductionCertificate algorithm operationCount :=
  EconCSLib.Optimization.AlgorithmSoundnessCertificate.of_condition
    (fun problem =>
      sequenceBoundsCover
        (cert.feasibleSequence problem) (cert.winCount problem)
        (cert.initialLossCount problem) (cert.bounds problem))
    cert.coverage_condition cert.output_spec_of_coverage cert.operationCount_le

/--
Build a sequence-reduction soundness certificate when the source model supplies
the coverage proof and the algorithm's operation count is exactly the paper's
quadratic bound.
-/
def sequenceReductionSoundnessCertificate_of_exactRuntime
    {ReducedSequences : Type*}
    {algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences}
    {operationCount : SequenceReductionProblem ReducedSequences → ℕ}
    (output_spec : ∀ problem : SequenceReductionProblem ReducedSequences,
      problem.specification (algorithm problem))
    (operationCount_eq : ∀ problem : SequenceReductionProblem ReducedSequences,
      operationCount problem =
        SequenceReductionProblem.quadraticRuntimeBound problem) :
    SequenceReductionSoundnessCertificate algorithm operationCount where
  output_spec := output_spec
  operationCount_le := by
    intro problem
    rw [operationCount_eq problem]

/--
Build an Algorithm 7 condition certificate when the source model supplies the
Predict-Wins/Predict-Losses bounds, the coverage-to-spec bridge, and an exact
quadratic operation-count identity.
-/
def sequenceReductionConditionCertificate_of_exactRuntime
    {ReducedSequences Voter Candidate Sequence : Type*}
    [DecidableEq Candidate]
    {algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences}
    {operationCount : SequenceReductionProblem ReducedSequences → ℕ}
    (voters : SequenceReductionProblem ReducedSequences → Finset Voter)
    (ballots :
      ∀ problem : SequenceReductionProblem ReducedSequences,
        Voter → RCVBallot Candidate)
    (candidates :
      SequenceReductionProblem ReducedSequences → Finset Candidate)
    (quota : SequenceReductionProblem ReducedSequences → ℕ)
    (firstChoiceThreshold :
      SequenceReductionProblem ReducedSequences → ℕ)
    (bounds :
      SequenceReductionProblem ReducedSequences → SequenceReductionBounds)
    (feasibleSequence :
      SequenceReductionProblem ReducedSequences → Sequence → Prop)
    (winCount :
      SequenceReductionProblem ReducedSequences → Sequence → ℕ)
    (initialLossCount :
      SequenceReductionProblem ReducedSequences → Sequence → ℕ)
    (coverage_condition :
      ∀ problem : SequenceReductionProblem ReducedSequences,
        sequenceBoundsCover
          (feasibleSequence problem) (winCount problem)
          (initialLossCount problem) (bounds problem))
    (output_spec_of_coverage :
      ∀ problem : SequenceReductionProblem ReducedSequences,
        sequenceBoundsCover
          (feasibleSequence problem) (winCount problem)
          (initialLossCount problem) (bounds problem) →
          problem.specification (algorithm problem))
    (operationCount_eq :
      ∀ problem : SequenceReductionProblem ReducedSequences,
        operationCount problem =
          SequenceReductionProblem.quadraticRuntimeBound problem) :
    SequenceReductionConditionCertificate
      (Voter := Voter) (Candidate := Candidate) (Sequence := Sequence)
      algorithm operationCount where
  voters := voters
  ballots := ballots
  candidates := candidates
  quota := quota
  firstChoiceThreshold := firstChoiceThreshold
  bounds := bounds
  feasibleSequence := feasibleSequence
  winCount := winCount
  initialLossCount := initialLossCount
  coverage_condition := coverage_condition
  output_spec_of_coverage := output_spec_of_coverage
  operationCount_le := by
    intro problem
    rw [operationCount_eq problem]

/--
Source-shaped Algorithm 7 certificate from Predict-Wins/Predict-Losses
capacity premises.

The paper's proof derives the retained sequence bounds from an upper capacity
on winning rounds and a lower floor on initial losses. This certificate records
exactly those premises and leaves only the concrete derivation of the premises
from the Predict-Wins/Predict-Losses loops as the remaining source boundary.
-/
structure SequenceReductionPredictionCertificate
    {ReducedSequences Voter Candidate Sequence : Type*}
    [DecidableEq Candidate]
    (algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences)
    (operationCount : SequenceReductionProblem ReducedSequences → ℕ) where
  voters : SequenceReductionProblem ReducedSequences → Finset Voter
  ballots :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      Voter → RCVBallot Candidate
  candidates :
    SequenceReductionProblem ReducedSequences → Finset Candidate
  firstChoiceThreshold : SequenceReductionProblem ReducedSequences → ℕ
  seats : SequenceReductionProblem ReducedSequences → ℕ
  predictedWinSupport : SequenceReductionProblem ReducedSequences → ℕ
  quota : SequenceReductionProblem ReducedSequences → ℕ
  lowerInitialLosses : SequenceReductionProblem ReducedSequences → ℕ
  feasibleSequence :
    SequenceReductionProblem ReducedSequences → Sequence → Prop
  winCount : SequenceReductionProblem ReducedSequences → Sequence → ℕ
  initialLossCount : SequenceReductionProblem ReducedSequences → Sequence → ℕ
  quota_pos :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      0 < quota problem
  winCount_le_seats :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      ∀ sequence, feasibleSequence problem sequence →
        winCount problem sequence ≤ seats problem
  win_capacity :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      ∀ sequence, feasibleSequence problem sequence →
        quota problem * winCount problem sequence ≤
          problem.budget + predictedWinSupport problem
  loss_floor :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      ∀ sequence, feasibleSequence problem sequence →
        lowerInitialLosses problem ≤ initialLossCount problem sequence
  output_spec_of_coverage :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      sequenceBoundsCover
        (feasibleSequence problem) (winCount problem)
        (initialLossCount problem)
        (sequenceReductionBoundsFromPredictions
          (seats problem) problem.budget (predictedWinSupport problem)
          (quota problem) (lowerInitialLosses problem)) →
        problem.specification (algorithm problem)
  operationCount_le :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      operationCount problem ≤
        SequenceReductionProblem.quadraticRuntimeBound problem

/--
Source-shaped Algorithm 7 certificate whose win-capacity premise is derived
from quota-sized disjoint support blocks rather than assumed directly.

The `SupportUnit` type is intentionally abstract: an instantiation can use
voters, budget coupons, or a tagged union of both, depending on how the
paper-specific Predict-Wins proof accounts for capacity.
-/
structure SequenceReductionQuotaBlockCertificate
    {ReducedSequences Voter Candidate Sequence Round SupportUnit : Type*}
    [DecidableEq Candidate] [DecidableEq SupportUnit]
    (algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences)
    (operationCount : SequenceReductionProblem ReducedSequences → ℕ) where
  voters : SequenceReductionProblem ReducedSequences → Finset Voter
  ballots :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      Voter → RCVBallot Candidate
  candidates :
    SequenceReductionProblem ReducedSequences → Finset Candidate
  firstChoiceThreshold : SequenceReductionProblem ReducedSequences → ℕ
  seats : SequenceReductionProblem ReducedSequences → ℕ
  predictedWinSupport : SequenceReductionProblem ReducedSequences → ℕ
  quota : SequenceReductionProblem ReducedSequences → ℕ
  lowerInitialLosses : SequenceReductionProblem ReducedSequences → ℕ
  feasibleSequence :
    SequenceReductionProblem ReducedSequences → Sequence → Prop
  winCount : SequenceReductionProblem ReducedSequences → Sequence → ℕ
  initialLossCount : SequenceReductionProblem ReducedSequences → Sequence → ℕ
  winRounds :
    SequenceReductionProblem ReducedSequences → Sequence → Finset Round
  capacityPool :
    SequenceReductionProblem ReducedSequences → Sequence → Finset SupportUnit
  quotaBlock :
    SequenceReductionProblem ReducedSequences → Sequence → Round →
      Finset SupportUnit
  quota_pos :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      0 < quota problem
  winCount_le_seats :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      ∀ sequence, feasibleSequence problem sequence →
        winCount problem sequence ≤ seats problem
  winCount_eq_winRounds_card :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      ∀ sequence, feasibleSequence problem sequence →
        winCount problem sequence = (winRounds problem sequence).card
  capacityPool_card_le :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      ∀ sequence, feasibleSequence problem sequence →
        (capacityPool problem sequence).card ≤
          problem.budget + predictedWinSupport problem
  quotaBlocks_pairwiseDisjoint :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      ∀ sequence, feasibleSequence problem sequence →
        ((winRounds problem sequence : Set Round).PairwiseDisjoint
          (quotaBlock problem sequence))
  quotaBlocks_subset_capacity :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      ∀ sequence, feasibleSequence problem sequence →
        ∀ round ∈ winRounds problem sequence,
          quotaBlock problem sequence round ⊆ capacityPool problem sequence
  quotaBlocks_quota :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      ∀ sequence, feasibleSequence problem sequence →
        ∀ round ∈ winRounds problem sequence,
          quota problem ≤
            (quotaBlock problem sequence round).card
  loss_floor :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      ∀ sequence, feasibleSequence problem sequence →
        lowerInitialLosses problem ≤ initialLossCount problem sequence
  output_spec_of_coverage :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      sequenceBoundsCover
        (feasibleSequence problem) (winCount problem)
        (initialLossCount problem)
        (sequenceReductionBoundsFromPredictions
          (seats problem) problem.budget (predictedWinSupport problem)
          (quota problem) (lowerInitialLosses problem)) →
        problem.specification (algorithm problem)
  operationCount_le :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      operationCount problem ≤
        SequenceReductionProblem.quadraticRuntimeBound problem

/--
Source-shaped Algorithm 7 certificate with both concrete prediction loops
visible: the budgeted Predict-Wins accumulator supplies win capacity, and
Predict-Losses prefix witnesses supply the lower initial-loss floor.
-/
structure SequenceReductionBudgetedLoopCertificate
    {ReducedSequences Voter Candidate Sequence : Type*}
    [DecidableEq Candidate]
    (algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences)
    (operationCount : SequenceReductionProblem ReducedSequences → ℕ) where
  voters : SequenceReductionProblem ReducedSequences → Finset Voter
  ballots :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      Voter → RCVBallot Candidate
  candidates :
    SequenceReductionProblem ReducedSequences → Finset Candidate
  firstChoiceThreshold : SequenceReductionProblem ReducedSequences → ℕ
  seats : SequenceReductionProblem ReducedSequences → ℕ
  predictedWinSupport : SequenceReductionProblem ReducedSequences → ℕ
  quota : SequenceReductionProblem ReducedSequences → ℕ
  lowerInitialLosses : SequenceReductionProblem ReducedSequences → ℕ
  feasibleSequence :
    SequenceReductionProblem ReducedSequences → Sequence → Prop
  winCount : SequenceReductionProblem ReducedSequences → Sequence → ℕ
  initialLossCount : SequenceReductionProblem ReducedSequences → Sequence → ℕ
  orderedWinners :
    SequenceReductionProblem ReducedSequences → Sequence → List Candidate
  assignedBudget :
    SequenceReductionProblem ReducedSequences → Sequence → Candidate → ℕ
  quota_pos :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      0 < quota problem
  winCount_le_seats :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      ∀ sequence, feasibleSequence problem sequence →
        winCount problem sequence ≤ seats problem
  winCount_eq_orderedWinners_length :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      ∀ sequence, feasibleSequence problem sequence →
        winCount problem sequence =
          (orderedWinners problem sequence).length
  assignedBudget_sum_le :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      ∀ sequence, feasibleSequence problem sequence →
        ((orderedWinners problem sequence).map
          (assignedBudget problem sequence)).sum ≤ problem.budget
  predictedWinSupport_bound :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      ∀ sequence, feasibleSequence problem sequence →
        predictWinsSupport (voters problem) (ballots problem)
            (candidates problem) (orderedWinners problem sequence) ≤
          predictedWinSupport problem
  budgeted_accumulator_quota :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      ∀ sequence, feasibleSequence problem sequence →
        predictWinsSupportBudgetAccumulatorQuota
          (voters problem) (ballots problem) (candidates problem)
          (assignedBudget problem sequence) (quota problem)
          (orderedWinners problem sequence)
  predictLosses_prefix :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      ∀ sequence, feasibleSequence problem sequence →
        PredictLossesInitialLossPrefixCertificate
          (voters problem) (ballots problem) (candidates problem)
          problem.budget (firstChoiceThreshold problem)
          (initialLossCount problem) (lowerInitialLosses problem)
          sequence
  output_spec_of_coverage :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      sequenceBoundsCover
        (feasibleSequence problem) (winCount problem)
        (initialLossCount problem)
        (sequenceReductionBoundsFromPredictions
          (seats problem) problem.budget (predictedWinSupport problem)
          (quota problem) (lowerInitialLosses problem)) →
        problem.specification (algorithm problem)
  operationCount_le :
    ∀ problem : SequenceReductionProblem ReducedSequences,
      operationCount problem ≤
        SequenceReductionProblem.quadraticRuntimeBound problem

/--
Named constructor for Proposition 3.4's source-shaped Algorithm 7
budgeted-loop certificate from the explicit Predict-Wins, Predict-Losses,
output-specification, and runtime obligations.
-/
def sequenceReductionBudgetedLoopCertificate_of_explicit
    {ReducedSequences Voter Candidate Sequence : Type*}
    [DecidableEq Candidate]
    {algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences}
    {operationCount : SequenceReductionProblem ReducedSequences → ℕ}
    (voters : SequenceReductionProblem ReducedSequences → Finset Voter)
    (ballots :
      ∀ problem : SequenceReductionProblem ReducedSequences,
        Voter → RCVBallot Candidate)
    (candidates :
      SequenceReductionProblem ReducedSequences → Finset Candidate)
    (firstChoiceThreshold :
      SequenceReductionProblem ReducedSequences → ℕ)
    (seats predictedWinSupport quota lowerInitialLosses :
      SequenceReductionProblem ReducedSequences → ℕ)
    (feasibleSequence :
      SequenceReductionProblem ReducedSequences → Sequence → Prop)
    (winCount initialLossCount :
      SequenceReductionProblem ReducedSequences → Sequence → ℕ)
    (orderedWinners :
      SequenceReductionProblem ReducedSequences → Sequence → List Candidate)
    (assignedBudget :
      SequenceReductionProblem ReducedSequences →
        Sequence → Candidate → ℕ)
    (quota_pos :
      ∀ problem : SequenceReductionProblem ReducedSequences,
        0 < quota problem)
    (winCount_le_seats :
      ∀ problem : SequenceReductionProblem ReducedSequences,
        ∀ sequence, feasibleSequence problem sequence →
          winCount problem sequence ≤ seats problem)
    (winCount_eq_orderedWinners_length :
      ∀ problem : SequenceReductionProblem ReducedSequences,
        ∀ sequence, feasibleSequence problem sequence →
          winCount problem sequence =
            (orderedWinners problem sequence).length)
    (assignedBudget_sum_le :
      ∀ problem : SequenceReductionProblem ReducedSequences,
        ∀ sequence, feasibleSequence problem sequence →
          ((orderedWinners problem sequence).map
            (assignedBudget problem sequence)).sum ≤ problem.budget)
    (predictedWinSupport_bound :
      ∀ problem : SequenceReductionProblem ReducedSequences,
        ∀ sequence, feasibleSequence problem sequence →
          predictWinsSupport (voters problem) (ballots problem)
              (candidates problem) (orderedWinners problem sequence) ≤
            predictedWinSupport problem)
    (budgeted_accumulator_quota :
      ∀ problem : SequenceReductionProblem ReducedSequences,
        ∀ sequence, feasibleSequence problem sequence →
          predictWinsSupportBudgetAccumulatorQuota
            (voters problem) (ballots problem) (candidates problem)
            (assignedBudget problem sequence) (quota problem)
            (orderedWinners problem sequence))
    (predictLosses_prefix :
      ∀ problem : SequenceReductionProblem ReducedSequences,
        ∀ sequence, feasibleSequence problem sequence →
          PredictLossesInitialLossPrefixCertificate
            (voters problem) (ballots problem) (candidates problem)
            problem.budget (firstChoiceThreshold problem)
            (initialLossCount problem) (lowerInitialLosses problem)
            sequence)
    (output_spec_of_coverage :
      ∀ problem : SequenceReductionProblem ReducedSequences,
        sequenceBoundsCover
          (feasibleSequence problem) (winCount problem)
          (initialLossCount problem)
          (sequenceReductionBoundsFromPredictions
            (seats problem) problem.budget (predictedWinSupport problem)
            (quota problem) (lowerInitialLosses problem)) →
          problem.specification (algorithm problem))
    (operationCount_le :
      ∀ problem : SequenceReductionProblem ReducedSequences,
        operationCount problem ≤
          SequenceReductionProblem.quadraticRuntimeBound problem) :
    SequenceReductionBudgetedLoopCertificate
      (Voter := Voter) (Candidate := Candidate) (Sequence := Sequence)
      algorithm operationCount where
  voters := voters
  ballots := ballots
  candidates := candidates
  firstChoiceThreshold := firstChoiceThreshold
  seats := seats
  predictedWinSupport := predictedWinSupport
  quota := quota
  lowerInitialLosses := lowerInitialLosses
  feasibleSequence := feasibleSequence
  winCount := winCount
  initialLossCount := initialLossCount
  orderedWinners := orderedWinners
  assignedBudget := assignedBudget
  quota_pos := quota_pos
  winCount_le_seats := winCount_le_seats
  winCount_eq_orderedWinners_length := winCount_eq_orderedWinners_length
  assignedBudget_sum_le := assignedBudget_sum_le
  predictedWinSupport_bound := predictedWinSupport_bound
  budgeted_accumulator_quota := budgeted_accumulator_quota
  predictLosses_prefix := predictLosses_prefix
  output_spec_of_coverage := output_spec_of_coverage
  operationCount_le := operationCount_le

/--
Algorithm 7 capacity/loss-floor premises imply the existing coverage-condition
certificate.
-/
def sequenceReductionConditionCertificate_of_predictionCertificate
    {ReducedSequences Voter Candidate Sequence : Type*}
    [DecidableEq Candidate]
    {algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences}
    {operationCount : SequenceReductionProblem ReducedSequences → ℕ}
    (cert :
      SequenceReductionPredictionCertificate
        (Voter := Voter) (Candidate := Candidate) (Sequence := Sequence)
        algorithm operationCount) :
    SequenceReductionConditionCertificate
      (Voter := Voter) (Candidate := Candidate) (Sequence := Sequence)
      algorithm operationCount where
  voters := cert.voters
  ballots := cert.ballots
  candidates := cert.candidates
  quota := cert.quota
  firstChoiceThreshold := cert.firstChoiceThreshold
  bounds := fun problem =>
    sequenceReductionBoundsFromPredictions
      (cert.seats problem) problem.budget (cert.predictedWinSupport problem)
      (cert.quota problem) (cert.lowerInitialLosses problem)
  feasibleSequence := cert.feasibleSequence
  winCount := cert.winCount
  initialLossCount := cert.initialLossCount
  coverage_condition := by
    intro problem
    exact sequenceBoundsCover_of_predictiveCapacity
      (cert.quota_pos problem)
      (cert.winCount_le_seats problem)
      (cert.win_capacity problem)
      (cert.loss_floor problem)
  output_spec_of_coverage := cert.output_spec_of_coverage
  operationCount_le := cert.operationCount_le

/--
Quota-block Algorithm 7 certificates imply the capacity/loss-floor prediction
certificate by deriving the win-capacity premise from disjoint support blocks.
-/
def sequenceReductionPredictionCertificate_of_quotaBlockCertificate
    {ReducedSequences Voter Candidate Sequence Round SupportUnit : Type*}
    [DecidableEq Candidate] [DecidableEq SupportUnit]
    {algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences}
    {operationCount : SequenceReductionProblem ReducedSequences → ℕ}
    (cert :
      SequenceReductionQuotaBlockCertificate
        (Voter := Voter) (Candidate := Candidate) (Sequence := Sequence)
        (Round := Round) (SupportUnit := SupportUnit)
        algorithm operationCount) :
    SequenceReductionPredictionCertificate
      (Voter := Voter) (Candidate := Candidate) (Sequence := Sequence)
      algorithm operationCount where
  voters := cert.voters
  ballots := cert.ballots
  candidates := cert.candidates
  firstChoiceThreshold := cert.firstChoiceThreshold
  seats := cert.seats
  predictedWinSupport := cert.predictedWinSupport
  quota := cert.quota
  lowerInitialLosses := cert.lowerInitialLosses
  feasibleSequence := cert.feasibleSequence
  winCount := cert.winCount
  initialLossCount := cert.initialLossCount
  quota_pos := cert.quota_pos
  winCount_le_seats := cert.winCount_le_seats
  win_capacity := by
    intro problem sequence hfeasible
    exact sequenceWinCapacity_of_quotaBlocks
      (quotaBlock := cert.quotaBlock problem)
      (feasibleSequence := cert.feasibleSequence problem)
      (winRounds := cert.winRounds problem)
      (winCount := cert.winCount problem)
      (capacityPool := cert.capacityPool problem)
      (quota := cert.quota problem)
      (budget := problem.budget)
      (predictedWinSupport := cert.predictedWinSupport problem)
      (cert.winCount_eq_winRounds_card problem)
      (cert.capacityPool_card_le problem)
      (cert.quotaBlocks_pairwiseDisjoint problem)
      (cert.quotaBlocks_subset_capacity problem)
      (cert.quotaBlocks_quota problem)
      sequence hfeasible
  loss_floor := cert.loss_floor
  output_spec_of_coverage := cert.output_spec_of_coverage
  operationCount_le := cert.operationCount_le

/--
Budgeted Predict-Wins plus Predict-Losses prefix certificates imply the
capacity/loss-floor prediction certificate.
-/
def sequenceReductionPredictionCertificate_of_budgetedLoopCertificate
    {ReducedSequences Voter Candidate Sequence : Type*}
    [DecidableEq Candidate]
    {algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences}
    {operationCount : SequenceReductionProblem ReducedSequences → ℕ}
    (cert :
      SequenceReductionBudgetedLoopCertificate
        (Voter := Voter) (Candidate := Candidate) (Sequence := Sequence)
        algorithm operationCount) :
    SequenceReductionPredictionCertificate
      (Voter := Voter) (Candidate := Candidate) (Sequence := Sequence)
      algorithm operationCount where
  voters := cert.voters
  ballots := cert.ballots
  candidates := cert.candidates
  firstChoiceThreshold := cert.firstChoiceThreshold
  seats := cert.seats
  predictedWinSupport := cert.predictedWinSupport
  quota := cert.quota
  lowerInitialLosses := cert.lowerInitialLosses
  feasibleSequence := cert.feasibleSequence
  winCount := cert.winCount
  initialLossCount := cert.initialLossCount
  quota_pos := cert.quota_pos
  winCount_le_seats := cert.winCount_le_seats
  win_capacity := by
    intro problem sequence hfeasible
    exact sequenceWinCapacity_of_budgetedPredictWinsSupportAccumulator
      (voters := cert.voters problem)
      (ballots := cert.ballots problem)
      (candidates := cert.candidates problem)
      (feasibleSequence := cert.feasibleSequence problem)
      (winCount := cert.winCount problem)
      (orderedWinners := cert.orderedWinners problem)
      (assignedBudget := cert.assignedBudget problem)
      (quota := cert.quota problem)
      (budget := problem.budget)
      (predictedWinSupport := cert.predictedWinSupport problem)
      (cert.winCount_eq_orderedWinners_length problem)
      (cert.assignedBudget_sum_le problem)
      (cert.predictedWinSupport_bound problem)
      (cert.budgeted_accumulator_quota problem)
      sequence hfeasible
  loss_floor := by
    intro problem sequence hfeasible
    exact
      lowerInitialLosses_le_initialLossCount_of_predictLossesPrefixCertificate
        (cert.predictLosses_prefix problem sequence hfeasible)
  output_spec_of_coverage := cert.output_spec_of_coverage
  operationCount_le := cert.operationCount_le

/--
Quota-block Algorithm 7 certificates imply the existing coverage-condition
certificate directly.
-/
def sequenceReductionConditionCertificate_of_quotaBlockCertificate
    {ReducedSequences Voter Candidate Sequence Round SupportUnit : Type*}
    [DecidableEq Candidate] [DecidableEq SupportUnit]
    {algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences}
    {operationCount : SequenceReductionProblem ReducedSequences → ℕ}
    (cert :
      SequenceReductionQuotaBlockCertificate
        (Voter := Voter) (Candidate := Candidate) (Sequence := Sequence)
        (Round := Round) (SupportUnit := SupportUnit)
        algorithm operationCount) :
    SequenceReductionConditionCertificate
      (Voter := Voter) (Candidate := Candidate) (Sequence := Sequence)
      algorithm operationCount where
  voters := cert.voters
  ballots := cert.ballots
  candidates := cert.candidates
  quota := cert.quota
  firstChoiceThreshold := cert.firstChoiceThreshold
  bounds := fun problem =>
    sequenceReductionBoundsFromPredictions
      (cert.seats problem) problem.budget (cert.predictedWinSupport problem)
      (cert.quota problem) (cert.lowerInitialLosses problem)
  feasibleSequence := cert.feasibleSequence
  winCount := cert.winCount
  initialLossCount := cert.initialLossCount
  coverage_condition := by
    intro problem
    exact sequenceBoundsCover_of_quotaBlocks
      (quotaBlock := cert.quotaBlock problem)
      (feasibleSequence := cert.feasibleSequence problem)
      (winRounds := cert.winRounds problem)
      (winCount := cert.winCount problem)
      (initialLossCount := cert.initialLossCount problem)
      (capacityPool := cert.capacityPool problem)
      (seats := cert.seats problem)
      (budget := problem.budget)
      (predictedWinSupport := cert.predictedWinSupport problem)
      (quota := cert.quota problem)
      (lowerInitialLosses := cert.lowerInitialLosses problem)
      (cert.quota_pos problem)
      (cert.winCount_le_seats problem)
      (cert.winCount_eq_winRounds_card problem)
      (cert.capacityPool_card_le problem)
      (cert.quotaBlocks_pairwiseDisjoint problem)
      (cert.quotaBlocks_subset_capacity problem)
      (cert.quotaBlocks_quota problem)
      (cert.loss_floor problem)
  output_spec_of_coverage := cert.output_spec_of_coverage
  operationCount_le := cert.operationCount_le

/--
Budgeted-loop Algorithm 7 certificates imply the existing coverage-condition
certificate directly.
-/
def sequenceReductionConditionCertificate_of_budgetedLoopCertificate
    {ReducedSequences Voter Candidate Sequence : Type*}
    [DecidableEq Candidate]
    {algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences}
    {operationCount : SequenceReductionProblem ReducedSequences → ℕ}
    (cert :
      SequenceReductionBudgetedLoopCertificate
        (Voter := Voter) (Candidate := Candidate) (Sequence := Sequence)
        algorithm operationCount) :
    SequenceReductionConditionCertificate
      (Voter := Voter) (Candidate := Candidate) (Sequence := Sequence)
      algorithm operationCount :=
  sequenceReductionConditionCertificate_of_predictionCertificate
    (sequenceReductionPredictionCertificate_of_budgetedLoopCertificate cert)

/--
Algorithm 7 capacity/loss-floor premises give the generic soundness
certificate used by the Proposition 3.4 projection.
-/
def sequenceReductionCertificate_of_predictionCertificate
    {ReducedSequences Voter Candidate Sequence : Type*}
    [DecidableEq Candidate]
    {algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences}
    {operationCount : SequenceReductionProblem ReducedSequences → ℕ}
    (cert :
      SequenceReductionPredictionCertificate
        (Voter := Voter) (Candidate := Candidate) (Sequence := Sequence)
        algorithm operationCount) :
    SequenceReductionCertificate algorithm operationCount :=
  sequenceReductionCertificate_of_conditionCertificate
    (sequenceReductionConditionCertificate_of_predictionCertificate cert)

/--
Algorithm 7 quota-block premises give the generic soundness certificate used
by the Proposition 3.4 projection.
-/
def sequenceReductionCertificate_of_quotaBlockCertificate
    {ReducedSequences Voter Candidate Sequence Round SupportUnit : Type*}
    [DecidableEq Candidate] [DecidableEq SupportUnit]
    {algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences}
    {operationCount : SequenceReductionProblem ReducedSequences → ℕ}
    (cert :
      SequenceReductionQuotaBlockCertificate
        (Voter := Voter) (Candidate := Candidate) (Sequence := Sequence)
        (Round := Round) (SupportUnit := SupportUnit)
        algorithm operationCount) :
    SequenceReductionCertificate algorithm operationCount :=
  sequenceReductionCertificate_of_conditionCertificate
    (sequenceReductionConditionCertificate_of_quotaBlockCertificate cert)

/--
Algorithm 7 budgeted-loop premises give the generic soundness certificate used
by the Proposition 3.4 projection.
-/
def sequenceReductionCertificate_of_budgetedLoopCertificate
    {ReducedSequences Voter Candidate Sequence : Type*}
    [DecidableEq Candidate]
    {algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences}
    {operationCount : SequenceReductionProblem ReducedSequences → ℕ}
    (cert :
      SequenceReductionBudgetedLoopCertificate
        (Voter := Voter) (Candidate := Candidate) (Sequence := Sequence)
        algorithm operationCount) :
    SequenceReductionCertificate algorithm operationCount :=
  sequenceReductionCertificate_of_conditionCertificate
    (sequenceReductionConditionCertificate_of_budgetedLoopCertificate cert)

/--
A source-shaped sequence-reduction certificate gives the generic soundness
certificate used by the reusable optimization library.
-/
theorem sequenceReductionCertificate_of_soundnessCertificate
    {ReducedSequences : Type*}
    {algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences}
    {operationCount : SequenceReductionProblem ReducedSequences → ℕ}
    (cert : SequenceReductionSoundnessCertificate algorithm operationCount) :
    SequenceReductionCertificate algorithm operationCount :=
  EconCSLib.Optimization.AlgorithmSoundnessCertificate.of_output_spec
    cert.output_spec cert.operationCount_le

/--
Definition 5.1 benefit predicate: an action benefits a candidate or group when
its active-vote trajectory strictly increases in some round before exit.
-/
def benefitsViaAction {Round Score : Type*} [LT Score]
    (before after : Round → Score) (beforeExit : Round → Prop) : Prop :=
  ∃ round, beforeExit round ∧ before round < after round

/-- A coalition all benefits when every member satisfies the benefit predicate. -/
def coalitionAllBenefit {Candidate : Type*}
    (coalition : Finset Candidate) (benefits : Candidate → Prop) : Prop :=
  ∀ candidate, candidate ∈ coalition → benefits candidate

/--
Assumption 5.2-style coalition prefix preservation: every affected voter has
some coalition member whose prefix is preserved by the strategic edit.
-/
def coalitionPrefixPreservation {Voter Candidate : Type*}
    (voters : Finset Voter) (coalition : Finset Candidate)
    (before after : Voter → RCVBallot Candidate) : Prop :=
  ∀ voter ∈ voters, ∃ gate, gate ∈ coalition ∧
    Ballot.PreservesPrefixThrough gate (before voter) (after voter)

/--
Constructor for the source Assumption 5.2 convention: every affected voter has
a coalition-member gate through which the ballot prefix is preserved.
-/
theorem coalitionPrefixPreservation_of_gate_prefix
    {Voter Candidate : Type*}
    {voters : Finset Voter} {coalition : Finset Candidate}
    {before after : Voter → RCVBallot Candidate}
    (hgate : ∀ voter ∈ voters, ∃ gate, gate ∈ coalition ∧
      Ballot.PreservesPrefixThrough gate (before voter) (after voter)) :
    coalitionPrefixPreservation voters coalition before after :=
  hgate

/--
Source-shaped first-exiting coalition-member witness for Proposition 5.3: the
chosen member belongs to the coalition and, before that member exits, all
coalition gates are still active.
-/
def firstExitingCoalitionMember {Candidate Round : Type*}
    (coalition : Finset Candidate) (active : Round → Finset Candidate)
    (beforeExit : Candidate → Round → Prop) (candidate : Candidate) : Prop :=
  candidate ∈ coalition ∧
    ∀ round, beforeExit candidate round → coalition ⊆ active round

/--
Finite source constructor for the first-exiting coalition member used in
Proposition 5.3.  If a nonempty coalition has an exit-rank function and any
member whose exit rank is no later than another member's exit is before that
other member leaves, then a minimum-rank coalition member satisfies the
first-exiting-member predicate.
-/
theorem exists_firstExitingCoalitionMember_of_exitRank
    {Candidate Round : Type*}
    {coalition : Finset Candidate}
    {active : Round → Finset Candidate}
    {beforeExit : Candidate → Round → Prop}
    (hcoalition : coalition.Nonempty)
    (exitRank : Candidate → ℕ)
    (hactive_before_exitRank :
      ∀ {candidate other round}, candidate ∈ coalition → other ∈ coalition →
        exitRank candidate ≤ exitRank other →
        beforeExit candidate round → other ∈ active round) :
    ∃ candidate,
      firstExitingCoalitionMember coalition active beforeExit candidate := by
  rcases Finset.exists_min_image coalition exitRank hcoalition with
    ⟨candidate, hmember, hmin⟩
  refine ⟨candidate, hmember, ?_⟩
  intro round hbeforeExit other hother
  exact hactive_before_exitRank hmember hother (hmin other hother) hbeforeExit

/--
Round-rank constructor for the active-before-exit premise: if a candidate is
before exit only in rounds whose rank is below its exit rank, and the STV active
set contains every candidate whose exit rank is still ahead of the round rank,
then later-exiting coalition members are active before earlier exits.
-/
theorem active_before_exitRank_of_roundRank
    {Candidate Round : Type*}
    {coalition : Finset Candidate}
    {active : Round → Finset Candidate}
    {beforeExit : Candidate → Round → Prop}
    (exitRank : Candidate → ℕ) (roundRank : Round → ℕ)
    (hbeforeExit_lt :
      ∀ {candidate round}, candidate ∈ coalition →
        beforeExit candidate round → roundRank round < exitRank candidate)
    (hactive_until : ActiveUntilExitRank active roundRank exitRank) :
  ∀ {candidate other round}, candidate ∈ coalition → other ∈ coalition →
      exitRank candidate ≤ exitRank other →
      beforeExit candidate round → other ∈ active round := by
  intro candidate other round hcandidate _hother hrank hbeforeExit
  exact hactive_until (candidate := other) (round := round)
    (lt_of_lt_of_le (hbeforeExit_lt hcandidate hbeforeExit) hrank)

/--
Coalition-scoped round-rank constructor for the active-before-exit premise.
This version only requires the active-until-exit invariant on the tracked
coalition, rather than for every candidate in the ambient type.
-/
theorem active_before_exitRank_of_roundRankOn
    {Candidate Round : Type*}
    {coalition : Finset Candidate}
    {active : Round → Finset Candidate}
    {beforeExit : Candidate → Round → Prop}
    (exitRank : Candidate → ℕ) (roundRank : Round → ℕ)
    (hbeforeExit_lt :
      ∀ {candidate round}, candidate ∈ coalition →
        beforeExit candidate round → roundRank round < exitRank candidate)
    (hactive_until :
      ActiveUntilExitRankOn coalition active roundRank exitRank) :
  ∀ {candidate other round}, candidate ∈ coalition → other ∈ coalition →
      exitRank candidate ≤ exitRank other →
      beforeExit candidate round → other ∈ active round := by
  intro candidate other round hcandidate hother hrank hbeforeExit
  exact ActiveUntilExitRankOn.active_of_rank_lt_of_le
    (tracked := coalition) (active := active) (roundRank := roundRank)
    (exitRank := exitRank) hactive_until hother
    (hbeforeExit_lt hcandidate hbeforeExit) hrank

/-- Strategy categories used by Theorem 5.4. -/
inductive AdditionStrategyShape where
  | losingPrefixWinnerTerminal
  | losingOnly
  | altruisticToWinners
  | other
  deriving DecidableEq, Repr

/-- Ballot shapes allowed in Theorem 5.4 outside Case (A). -/
def losingPrefixOrLosingOnlyShape (shape : AdditionStrategyShape) : Prop :=
  shape = AdditionStrategyShape.losingPrefixWinnerTerminal ∨
    shape = AdditionStrategyShape.losingOnly

/--
Finite-shape Appendix E bridge: after ruling out altruistic-to-winners and the
catch-all `other` shape, the strategy has one of the two losing-shape forms.
-/
theorem losingPrefixOrLosingOnlyShape_of_not_altruisticToWinners_not_other
    {shape : AdditionStrategyShape}
    (hnotWinner : shape ≠ AdditionStrategyShape.altruisticToWinners)
    (hnotOther : shape ≠ AdditionStrategyShape.other) :
    losingPrefixOrLosingOnlyShape shape := by
  cases shape with
  | losingPrefixWinnerTerminal =>
      exact Or.inl rfl
  | losingOnly =>
      exact Or.inr rfl
  | altruisticToWinners =>
      exact False.elim (hnotWinner rfl)
  | other =>
      exact False.elim (hnotOther rfl)

/--
Concrete finite vote-addition strategy for Appendix E of Theorem 5.4: a finite
list of added ranked ballots together with their multiplicities.
-/
structure FiniteAdditionStrategy (Candidate : Type*) where
  entries : List (RCVBallot Candidate × ℕ)

namespace FiniteAdditionStrategy

/-- The number of added ballots represented by a finite strategy. -/
def costNat {Candidate : Type*} (strategy : FiniteAdditionStrategy Candidate) :
    ℕ :=
  (strategy.entries.map Prod.snd).sum

/-- The strategy cost as a real-valued objective. -/
def cost {Candidate : Type*} (strategy : FiniteAdditionStrategy Candidate) :
    ℝ :=
  (costNat strategy : ℝ)

/-- Weighted active-support count contributed by the finite added-ballot list. -/
def activeSupportCount {Candidate : Type*} [DecidableEq Candidate]
    (strategy : FiniteAdditionStrategy Candidate)
    (active : Finset Candidate) (candidate : Candidate) : ℕ :=
  Ballot.weightedActiveSupportCount strategy.entries active candidate

theorem costNat_append {Candidate : Type*}
    (background additions : List (RCVBallot Candidate × ℕ)) :
    costNat ({ entries := background ++ additions } :
        FiniteAdditionStrategy Candidate) =
      (background.map Prod.snd).sum + (additions.map Prod.snd).sum := by
  simp [costNat, List.map_append, List.sum_append]

theorem activeSupportCount_entries {Candidate : Type*} [DecidableEq Candidate]
    (strategy : FiniteAdditionStrategy Candidate)
    (active : Finset Candidate) (candidate : Candidate) :
    strategy.activeSupportCount active candidate =
      Ballot.weightedActiveSupportCount strategy.entries active candidate :=
  rfl

end FiniteAdditionStrategy

/--
Outcome model for finite vote-addition strategies.  It records only the
paper-facing winner set induced by each finite strategy; concrete STV
simulators or source traces can instantiate `outcome` later.
-/
structure FiniteAdditionStrategyOutcomeModel (Candidate : Type*)
    [DecidableEq Candidate] where
  targetWinners : Finset Candidate
  outcome : FiniteAdditionStrategy Candidate → RCVWinLossStructure Candidate

namespace FiniteAdditionStrategyOutcomeModel

/-- A finite strategy is feasible when its induced winner set is the target set. -/
def feasible {Candidate : Type*} [DecidableEq Candidate]
    (model : FiniteAdditionStrategyOutcomeModel Candidate)
    (strategy : FiniteAdditionStrategy Candidate) : Prop :=
  (model.outcome strategy).winners = model.targetWinners

/--
Winner-set preservation across a strategy replacement preserves feasibility in
any finite-strategy outcome model.
-/
theorem feasible_of_winners_eq {Candidate : Type*} [DecidableEq Candidate]
    (model : FiniteAdditionStrategyOutcomeModel Candidate)
    {source target : FiniteAdditionStrategy Candidate}
    (hsource : model.feasible source)
    (hwinners : (model.outcome target).winners =
      (model.outcome source).winners) :
    model.feasible target := by
  exact hwinners.trans hsource

/--
Feasibility can be recovered from one-sided target-winner preservation and the
seat-count bound.  This is the form used by Appendix E arguments where a split
replacement may change the order of round winners, but the target winner set
still appears and the rule elects no extra winners.
-/
theorem feasible_of_targetWinners_subset_outcome_of_card_le
    {Candidate : Type*} [DecidableEq Candidate]
    (model : FiniteAdditionStrategyOutcomeModel Candidate)
    {strategy : FiniteAdditionStrategy Candidate}
    (hsubset : model.targetWinners ⊆ (model.outcome strategy).winners)
    (hcard : (model.outcome strategy).winners.card ≤ model.targetWinners.card) :
    model.feasible strategy := by
  exact (Finset.eq_of_subset_of_card_le hsubset hcard).symm

end FiniteAdditionStrategyOutcomeModel

/--
Finite-strategy outcome model specialized to the paper's final-order
convention: each strategy induces a final order, and the winners are the first
`seatCount` candidates in that order.
-/
structure FiniteAdditionStrategyFinalOrderOutcomeModel (Candidate : Type*)
    [DecidableEq Candidate] where
  targetWinners : Finset Candidate
  seatCount : ℕ
  finalOrder : FiniteAdditionStrategy Candidate → FinalOrder Candidate
  targetWinners_card_eq : targetWinners.card = seatCount

namespace FiniteAdditionStrategyFinalOrderOutcomeModel

/-- Convert a final-order model into the generic winner/loser outcome model. -/
def toOutcomeModel {Candidate : Type*} [DecidableEq Candidate]
    (model : FiniteAdditionStrategyFinalOrderOutcomeModel Candidate) :
    FiniteAdditionStrategyOutcomeModel Candidate where
  targetWinners := model.targetWinners
  outcome := fun strategy =>
    WinLossStructure.ofFinalOrder (model.finalOrder strategy) model.seatCount

/-- Feasibility in the final-order model. -/
def feasible {Candidate : Type*} [DecidableEq Candidate]
    (model : FiniteAdditionStrategyFinalOrderOutcomeModel Candidate)
    (strategy : FiniteAdditionStrategy Candidate) : Prop :=
  model.toOutcomeModel.feasible strategy

@[simp] theorem toOutcomeModel_targetWinners {Candidate : Type*}
    [DecidableEq Candidate]
    (model : FiniteAdditionStrategyFinalOrderOutcomeModel Candidate) :
    model.toOutcomeModel.targetWinners = model.targetWinners := rfl

@[simp] theorem toOutcomeModel_outcome_winners {Candidate : Type*}
    [DecidableEq Candidate]
    (model : FiniteAdditionStrategyFinalOrderOutcomeModel Candidate)
    (strategy : FiniteAdditionStrategy Candidate) :
    (model.toOutcomeModel.outcome strategy).winners =
      (model.finalOrder strategy).topCandidates model.seatCount := rfl

/--
The final-order convention supplies the seat-count bound used by the generic
Appendix E target-inclusion bridge.
-/
theorem outcome_winners_card_le_targetWinners_card {Candidate : Type*}
    [DecidableEq Candidate]
    (model : FiniteAdditionStrategyFinalOrderOutcomeModel Candidate)
    (strategy : FiniteAdditionStrategy Candidate) :
    (model.toOutcomeModel.outcome strategy).winners.card ≤
      model.targetWinners.card := by
  rw [toOutcomeModel_outcome_winners, model.targetWinners_card_eq]
  exact (model.finalOrder strategy).topCandidates_card_le model.seatCount

/--
In the final-order convention, target-winner preservation alone implies
feasibility, because the outcome has at most the target number of winners.
-/
theorem feasible_of_targetWinners_subset_topCandidates
    {Candidate : Type*} [DecidableEq Candidate]
    (model : FiniteAdditionStrategyFinalOrderOutcomeModel Candidate)
    {strategy : FiniteAdditionStrategy Candidate}
    (hsubset :
      model.targetWinners ⊆
        (model.finalOrder strategy).topCandidates model.seatCount) :
    model.feasible strategy := by
  exact
    model.toOutcomeModel.feasible_of_targetWinners_subset_outcome_of_card_le
      (by simpa using hsubset)
      (outcome_winners_card_le_targetWinners_card model strategy)

end FiniteAdditionStrategyFinalOrderOutcomeModel

/--
Concrete Appendix E split replacement relation. The first constructor is the
source branch where the first winner on the original added ballot is followed
by a loser; the second constructor is the branch where it is followed by
another winner. In both branches the unchanged background additions are kept,
and the replacement uses strictly fewer added ballots for the split block.
-/
inductive AppendixESplitBallotReplacement {Candidate : Type*}
    [DecidableEq Candidate] (winners : Finset Candidate) :
    FiniteAdditionStrategy Candidate → FiniteAdditionStrategy Candidate → Prop
  | firstWinnerThenLoser
      (background : List (RCVBallot Candidate × ℕ))
      (pref suffix : RCVBallot Candidate)
      (winner loser : Candidate) (b b₁ b₂ : ℕ)
      (hwinner : winner ∈ winners) (hloser : loser ∉ winners)
      (hcost : b₁ + b₂ < b) :
      AppendixESplitBallotReplacement winners
        { entries := background ++ [(pref ++ winner :: loser :: suffix, b)] }
        { entries :=
            background ++
              [(pref ++ [winner], b₁), (pref ++ loser :: suffix, b₂)] }
  | firstWinnerThenWinner
      (background : List (RCVBallot Candidate × ℕ))
      (pref suffix : RCVBallot Candidate)
      (winner₁ winner₂ : Candidate) (b b₁ b₂ b₃ : ℕ)
      (hwinner₁ : winner₁ ∈ winners) (hwinner₂ : winner₂ ∈ winners)
      (hcost : b₁ + b₂ + b₃ < b) :
      AppendixESplitBallotReplacement winners
        { entries :=
            background ++ [(pref ++ winner₁ :: winner₂ :: suffix, b)] }
        { entries :=
            background ++
              [(pref ++ [winner₁], b₁), (pref ++ [winner₂], b₂),
                (pref ++ suffix, b₃)] }

namespace AppendixESplitBallotReplacement

theorem costNat_lt {Candidate : Type*} [DecidableEq Candidate]
    {winners : Finset Candidate}
    {source target : FiniteAdditionStrategy Candidate}
    (replacement :
      AppendixESplitBallotReplacement winners source target) :
    target.costNat < source.costNat := by
  cases replacement with
  | firstWinnerThenLoser background pref suffix winner loser b b₁ b₂
      hwinner hloser hcost =>
      simpa [FiniteAdditionStrategy.costNat, List.map_append,
        List.sum_append, Nat.add_assoc] using
        Nat.add_lt_add_left hcost (background.map Prod.snd).sum
  | firstWinnerThenWinner background pref suffix winner₁ winner₂ b b₁ b₂ b₃
      hwinner₁ hwinner₂ hcost =>
      simpa [FiniteAdditionStrategy.costNat, List.map_append,
        List.sum_append, Nat.add_assoc] using
        Nat.add_lt_add_left hcost (background.map Prod.snd).sum

theorem cost_lt {Candidate : Type*} [DecidableEq Candidate]
    {winners : Finset Candidate}
    {source target : FiniteAdditionStrategy Candidate}
    (replacement :
      AppendixESplitBallotReplacement winners source target) :
    target.cost < source.cost := by
  change ((target.costNat : ℝ) < (source.costNat : ℝ))
  exact_mod_cast costNat_lt replacement

end AppendixESplitBallotReplacement

/--
Context-preserving Appendix E split replacement.  This is the same source
split as `AppendixESplitBallotReplacement`, but it permits the split block to
appear inside a larger finite addition strategy, preserving both surrounding
blocks of added ballots.
-/
inductive AppendixEContextualSplitBallotReplacement {Candidate : Type*}
    [DecidableEq Candidate] (winners : Finset Candidate) :
    FiniteAdditionStrategy Candidate → FiniteAdditionStrategy Candidate → Prop
  | firstWinnerThenLoser
      (before after : List (RCVBallot Candidate × ℕ))
      (pref suffix : RCVBallot Candidate)
      (winner loser : Candidate) (b b₁ b₂ : ℕ)
      (hwinner : winner ∈ winners) (hloser : loser ∉ winners)
      (hcost : b₁ + b₂ < b) :
      AppendixEContextualSplitBallotReplacement winners
        { entries :=
            before ++ [(pref ++ winner :: loser :: suffix, b)] ++ after }
        { entries :=
            before ++
              [(pref ++ [winner], b₁), (pref ++ loser :: suffix, b₂)] ++
                after }
  | firstWinnerThenWinner
      (before after : List (RCVBallot Candidate × ℕ))
      (pref suffix : RCVBallot Candidate)
      (winner₁ winner₂ : Candidate) (b b₁ b₂ b₃ : ℕ)
      (hwinner₁ : winner₁ ∈ winners) (hwinner₂ : winner₂ ∈ winners)
      (hcost : b₁ + b₂ + b₃ < b) :
      AppendixEContextualSplitBallotReplacement winners
        { entries :=
            before ++ [(pref ++ winner₁ :: winner₂ :: suffix, b)] ++
              after }
        { entries :=
            before ++
              [(pref ++ [winner₁], b₁), (pref ++ [winner₂], b₂),
                (pref ++ suffix, b₃)] ++ after }

namespace AppendixEContextualSplitBallotReplacement

theorem costNat_lt {Candidate : Type*} [DecidableEq Candidate]
    {winners : Finset Candidate}
    {source target : FiniteAdditionStrategy Candidate}
    (replacement :
      AppendixEContextualSplitBallotReplacement winners source target) :
    target.costNat < source.costNat := by
  cases replacement with
  | firstWinnerThenLoser before after pref suffix winner loser b b₁ b₂
      hwinner hloser hcost =>
      have htail :
          b₁ + b₂ + (after.map Prod.snd).sum <
            b + (after.map Prod.snd).sum :=
        Nat.add_lt_add_right hcost (after.map Prod.snd).sum
      have htotal :
          (before.map Prod.snd).sum +
              (b₁ + b₂ + (after.map Prod.snd).sum) <
            (before.map Prod.snd).sum +
              (b + (after.map Prod.snd).sum) :=
        Nat.add_lt_add_left htail (before.map Prod.snd).sum
      simpa [FiniteAdditionStrategy.costNat, List.map_append,
        List.sum_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using htotal
  | firstWinnerThenWinner before after pref suffix winner₁ winner₂ b b₁ b₂ b₃
      hwinner₁ hwinner₂ hcost =>
      have htail :
          b₁ + b₂ + b₃ + (after.map Prod.snd).sum <
            b + (after.map Prod.snd).sum :=
        Nat.add_lt_add_right hcost (after.map Prod.snd).sum
      have htotal :
          (before.map Prod.snd).sum +
              (b₁ + b₂ + b₃ + (after.map Prod.snd).sum) <
            (before.map Prod.snd).sum +
              (b + (after.map Prod.snd).sum) :=
        Nat.add_lt_add_left htail (before.map Prod.snd).sum
      simpa [FiniteAdditionStrategy.costNat, List.map_append,
        List.sum_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using htotal

theorem cost_lt {Candidate : Type*} [DecidableEq Candidate]
    {winners : Finset Candidate}
    {source target : FiniteAdditionStrategy Candidate}
    (replacement :
      AppendixEContextualSplitBallotReplacement winners source target) :
    target.cost < source.cost := by
  change ((target.costNat : ℝ) < (source.costNat : ℝ))
  exact_mod_cast costNat_lt replacement

end AppendixEContextualSplitBallotReplacement

/--
The first Appendix E branch occurs in a finite strategy when some positive
added-ballot block has first winning candidate followed immediately by a loser,
possibly with other added-ballot blocks before and after it.
-/
def StrategyHasPositiveFirstWinnerThenLoserBlock {Candidate : Type*}
    (winners : Finset Candidate) (strategy : FiniteAdditionStrategy Candidate) :
    Prop :=
  ∃ before after : List (RCVBallot Candidate × ℕ),
    ∃ pref suffix : RCVBallot Candidate,
    ∃ winner loser : Candidate, ∃ b b₁ b₂ : ℕ,
      strategy.entries =
        before ++ [(pref ++ winner :: loser :: suffix, b)] ++ after ∧
      b₁ + b₂ < b ∧ winner ∈ winners ∧ loser ∉ winners

/--
The second Appendix E branch occurs in a finite strategy when some positive
added-ballot block has first winning candidate followed immediately by another
winner, possibly with other added-ballot blocks before and after it.
-/
def StrategyHasPositiveFirstWinnerThenWinnerBlock {Candidate : Type*}
    (winners : Finset Candidate) (strategy : FiniteAdditionStrategy Candidate) :
    Prop :=
  ∃ before after : List (RCVBallot Candidate × ℕ),
    ∃ pref suffix : RCVBallot Candidate,
    ∃ winner₁ winner₂ : Candidate, ∃ b b₁ b₂ b₃ : ℕ,
      strategy.entries =
        before ++ [(pref ++ winner₁ :: winner₂ :: suffix, b)] ++ after ∧
      b₁ + b₂ + b₃ < b ∧ winner₁ ∈ winners ∧ winner₂ ∈ winners

/--
Source-side structural split for catch-all `other` strategies: the first
winner on a positive added ballot has a successor, which is either a loser or
another winner.
-/
def StrategyHasPositiveAppendixESplitBlock {Candidate : Type*}
    (winners : Finset Candidate) (strategy : FiniteAdditionStrategy Candidate) :
    Prop :=
  StrategyHasPositiveFirstWinnerThenLoserBlock winners strategy ∨
    StrategyHasPositiveFirstWinnerThenWinnerBlock winners strategy

/--
Pure list/count constructor for the first Appendix E branch: a positive block
whose first winner is followed by a loser admits the contextual split target.
The source-model proof still has to show that this target is feasible.
-/
theorem exists_contextualAppendixESplitBallotReplacement_of_positiveFirstWinnerThenLoserBlock
    {Candidate : Type*} [DecidableEq Candidate] {winners : Finset Candidate}
    {strategy : FiniteAdditionStrategy Candidate}
    (hblock :
      StrategyHasPositiveFirstWinnerThenLoserBlock winners strategy) :
    ∃ alternative,
      AppendixEContextualSplitBallotReplacement winners strategy alternative := by
  rcases strategy with ⟨entries⟩
  unfold StrategyHasPositiveFirstWinnerThenLoserBlock at hblock
  rcases hblock with
    ⟨before, after, pref, suffix, winner, loser, b, b₁, b₂, hentries, hcost,
      hwinner, hloser⟩
  change entries = before ++ [(pref ++ winner :: loser :: suffix, b)] ++ after at hentries
  subst entries
  refine
    ⟨{ entries :=
        before ++ [(pref ++ [winner], b₁), (pref ++ loser :: suffix, b₂)] ++
          after }, ?_⟩
  exact
    AppendixEContextualSplitBallotReplacement.firstWinnerThenLoser
      before after pref suffix winner loser b b₁ b₂ hwinner hloser hcost

/--
Pure list/count constructor for the second Appendix E branch: a positive block
whose first winner is followed by another winner admits the contextual split
target. The source-model proof still has to show that this target is feasible.
-/
theorem exists_contextualAppendixESplitBallotReplacement_of_positiveFirstWinnerThenWinnerBlock
    {Candidate : Type*} [DecidableEq Candidate] {winners : Finset Candidate}
    {strategy : FiniteAdditionStrategy Candidate}
    (hblock :
      StrategyHasPositiveFirstWinnerThenWinnerBlock winners strategy) :
    ∃ alternative,
      AppendixEContextualSplitBallotReplacement winners strategy alternative := by
  rcases strategy with ⟨entries⟩
  unfold StrategyHasPositiveFirstWinnerThenWinnerBlock at hblock
  rcases hblock with
    ⟨before, after, pref, suffix, winner₁, winner₂, b, b₁, b₂, b₃,
      hentries, hcost,
      hwinner₁, hwinner₂⟩
  change entries =
    before ++ [(pref ++ winner₁ :: winner₂ :: suffix, b)] ++ after at hentries
  subst entries
  refine
    ⟨{ entries :=
        before ++ [(pref ++ [winner₁], b₁), (pref ++ [winner₂], b₂),
          (pref ++ suffix, b₃)] ++ after }, ?_⟩
  exact
    AppendixEContextualSplitBallotReplacement.firstWinnerThenWinner
      before after pref suffix winner₁ winner₂ b b₁ b₂ b₃ hwinner₁ hwinner₂
        hcost

/--
Pure list/count constructor for the source's Appendix E split cases. This
isolates the syntactic decomposition of finite added-ballot strategies from the
separate STV feasibility-preservation argument.
-/
theorem exists_contextualAppendixESplitBallotReplacement_of_positiveAppendixESplitBlock
    {Candidate : Type*} [DecidableEq Candidate] {winners : Finset Candidate}
    {strategy : FiniteAdditionStrategy Candidate}
    (hblock : StrategyHasPositiveAppendixESplitBlock winners strategy) :
    ∃ alternative,
      AppendixEContextualSplitBallotReplacement winners strategy alternative := by
  rcases hblock with hblock | hblock
  · exact
      exists_contextualAppendixESplitBallotReplacement_of_positiveFirstWinnerThenLoserBlock
        hblock
  · exact
      exists_contextualAppendixESplitBallotReplacement_of_positiveFirstWinnerThenWinnerBlock
        hblock

/-- Ballot shapes allowed by Theorem 5.4 when Case (A) occurs. -/
def theorem5_4_allowedShape (caseA : Prop) (shape : AdditionStrategyShape) : Prop :=
  losingPrefixOrLosingOnlyShape shape ∨
    (caseA ∧ shape = AdditionStrategyShape.altruisticToWinners)

/--
Source-shaped Case (A) occurrence for Theorem 5.4: some optimal
altruistic-to-winners strategy uses post-win surplus transfers.  The source
defines Case (A) exactly as the configuration in which a candidate is kept from
early elimination and then wins later from transfers alone, so that added votes
can transfer after that win.
-/
def theorem5_4_caseA_occurs {Strategy : Type*}
    (usesPostWinSurplus : Strategy → Prop) : Prop :=
  ∃ strategy, usesPostWinSurplus strategy

/--
Theorem 5.4 source-facing characterization predicate for optimal vote-addition
strategies.
-/
def theorem5_4_strategyCharacterization {Strategy : Type*}
    (caseA : Prop) (shape : Strategy → AdditionStrategyShape)
    (optimal : Strategy → Prop) : Prop :=
  ∀ strategy, optimal strategy → theorem5_4_allowedShape caseA (shape strategy)

/--
Appendix E-style strict cost dominance: every feasible catch-all `other`
strategy has a feasible replacement with strictly smaller cost.
-/
def otherShapeStrictCostDominance {Strategy : Type*}
    (feasible : Strategy → Prop) (cost : Strategy → ℝ)
    (shape : Strategy → AdditionStrategyShape) : Prop :=
  ∀ strategy, feasible strategy →
    shape strategy = AdditionStrategyShape.other →
      ∃ alternative, feasible alternative ∧ cost alternative < cost strategy

/--
Appendix E-style replacement certificate: each feasible catch-all `other`
strategy has a concrete feasible replacement with strictly smaller cost.
-/
structure OtherShapeReplacementCertificate {Strategy : Type*}
    (feasible : Strategy → Prop) (cost : Strategy → ℝ)
    (shape : Strategy → AdditionStrategyShape) where
  replacement : ∀ strategy, feasible strategy →
    shape strategy = AdditionStrategyShape.other → Strategy
  replacement_feasible : ∀ strategy hfeasible hshape,
    feasible (replacement strategy hfeasible hshape)
  replacement_cost_lt : ∀ strategy hfeasible hshape,
    cost (replacement strategy hfeasible hshape) < cost strategy

/--
Appendix E split-replacement certificate: the catch-all `other` strategies
split into two source cases, and each case has its own concrete feasible
strictly lower-cost replacement.
-/
structure OtherShapeSplitReplacementCertificate {Strategy : Type*}
    (feasible : Strategy → Prop) (cost : Strategy → ℝ)
    (shape : Strategy → AdditionStrategyShape) where
  leftCase : Strategy → Prop
  rightCase : Strategy → Prop
  split_other : ∀ strategy, feasible strategy →
    shape strategy = AdditionStrategyShape.other →
      leftCase strategy ∨ rightCase strategy
  leftReplacement : ∀ strategy, feasible strategy →
    shape strategy = AdditionStrategyShape.other → leftCase strategy →
      Strategy
  leftReplacement_feasible : ∀ strategy hfeasible hshape hleft,
    feasible (leftReplacement strategy hfeasible hshape hleft)
  leftReplacement_cost_lt : ∀ strategy hfeasible hshape hleft,
    cost (leftReplacement strategy hfeasible hshape hleft) < cost strategy
  rightReplacement : ∀ strategy, feasible strategy →
    shape strategy = AdditionStrategyShape.other → rightCase strategy →
      Strategy
  rightReplacement_feasible : ∀ strategy hfeasible hshape hright,
    feasible (rightReplacement strategy hfeasible hshape hright)
  rightReplacement_cost_lt : ∀ strategy hfeasible hshape hright,
    cost (rightReplacement strategy hfeasible hshape hright) < cost strategy

/--
Appendix-E-shaped split replacement certificate for Theorem 5.4.

The paper splits catch-all `other` strategies according to the first winning
candidate appearing on the added ballot: either the next relevant candidate is
a loser, so the ballot can be split before that winner, or another winner
appears next, so the ballot is split around both winners.  This record names
those two source branches directly and converts to the generic split
replacement certificate below.
-/
structure AppendixESplitReplacementCertificate {Strategy : Type*}
    (feasible : Strategy → Prop) (cost : Strategy → ℝ)
    (shape : Strategy → AdditionStrategyShape) where
  firstWinnerThenLoser : Strategy → Prop
  firstWinnerThenWinner : Strategy → Prop
  split_other : ∀ strategy, feasible strategy →
    shape strategy = AdditionStrategyShape.other →
      firstWinnerThenLoser strategy ∨ firstWinnerThenWinner strategy
  splitBeforeWinnerReplacement : ∀ strategy, feasible strategy →
    shape strategy = AdditionStrategyShape.other →
      firstWinnerThenLoser strategy → Strategy
  splitBeforeWinnerReplacement_feasible : ∀ strategy hfeasible hshape hbranch,
    feasible
      (splitBeforeWinnerReplacement strategy hfeasible hshape hbranch)
  splitBeforeWinnerReplacement_cost_lt : ∀ strategy hfeasible hshape hbranch,
    cost (splitBeforeWinnerReplacement strategy hfeasible hshape hbranch) <
      cost strategy
  splitAroundWinnersReplacement : ∀ strategy, feasible strategy →
    shape strategy = AdditionStrategyShape.other →
      firstWinnerThenWinner strategy → Strategy
  splitAroundWinnersReplacement_feasible : ∀ strategy hfeasible hshape hbranch,
    feasible
      (splitAroundWinnersReplacement strategy hfeasible hshape hbranch)
  splitAroundWinnersReplacement_cost_lt : ∀ strategy hfeasible hshape hbranch,
    cost (splitAroundWinnersReplacement strategy hfeasible hshape hbranch) <
      cost strategy

/--
A concrete replacement certificate supplies the Appendix E strict-cost
dominance witness for catch-all `other` strategies.
-/
theorem otherShapeStrictCostDominance_of_replacementCertificate
    {Strategy : Type*}
    {feasible : Strategy → Prop} {cost : Strategy → ℝ}
    {shape : Strategy → AdditionStrategyShape}
    (cert : OtherShapeReplacementCertificate feasible cost shape) :
    otherShapeStrictCostDominance feasible cost shape :=
  EconCSLib.Optimization.exists_feasible_objective_lt_of_replacement
    cert.replacement cert.replacement_feasible cert.replacement_cost_lt

/--
A split replacement certificate supplies the Appendix E strict-cost dominance
witness for catch-all `other` strategies.
-/
theorem otherShapeStrictCostDominance_of_splitReplacementCertificate
    {Strategy : Type*}
    {feasible : Strategy → Prop} {cost : Strategy → ℝ}
    {shape : Strategy → AdditionStrategyShape}
    (cert : OtherShapeSplitReplacementCertificate feasible cost shape) :
    otherShapeStrictCostDominance feasible cost shape :=
  EconCSLib.Optimization.exists_feasible_objective_lt_of_split_replacement
    (feasible := feasible)
    (bad := fun strategy => shape strategy = AdditionStrategyShape.other)
    (leftCase := cert.leftCase)
    (rightCase := cert.rightCase)
    cert.split_other
    cert.leftReplacement
    cert.leftReplacement_feasible
    cert.leftReplacement_cost_lt
    cert.rightReplacement
    cert.rightReplacement_feasible
    cert.rightReplacement_cost_lt

/--
Concrete Appendix E ballot-splitting dominance: if every feasible catch-all
`other` finite addition strategy has a feasible replacement related by the
source's explicit ballot split, then the replacement is strictly cheaper by
the proved ballot-count inequality.
-/
theorem otherShapeStrictCostDominance_of_appendixESplitBallotReplacement
    {Candidate : Type*} [DecidableEq Candidate]
    {winners : Finset Candidate}
    {feasible : FiniteAdditionStrategy Candidate → Prop}
    {shape : FiniteAdditionStrategy Candidate → AdditionStrategyShape}
    (hsplit :
      ∀ strategy, feasible strategy →
        shape strategy = AdditionStrategyShape.other →
          ∃ alternative,
            AppendixESplitBallotReplacement winners strategy alternative ∧
              feasible alternative) :
    otherShapeStrictCostDominance feasible FiniteAdditionStrategy.cost shape := by
  intro strategy hfeasible hshape
  rcases hsplit strategy hfeasible hshape with
    ⟨alternative, hreplacement, halternative⟩
  exact ⟨alternative, halternative,
    AppendixESplitBallotReplacement.cost_lt hreplacement⟩

/--
Context-preserving Appendix E ballot-splitting dominance: if every feasible
catch-all `other` finite addition strategy has a feasible contextual split
replacement, then that replacement is strictly cheaper by the proved
ballot-count inequality.
-/
theorem otherShapeStrictCostDominance_of_contextualAppendixESplitBallotReplacement
    {Candidate : Type*} [DecidableEq Candidate]
    {winners : Finset Candidate}
    {feasible : FiniteAdditionStrategy Candidate → Prop}
    {shape : FiniteAdditionStrategy Candidate → AdditionStrategyShape}
    (hsplit :
      ∀ strategy, feasible strategy →
        shape strategy = AdditionStrategyShape.other →
          ∃ alternative,
            AppendixEContextualSplitBallotReplacement winners strategy
                alternative ∧
              feasible alternative) :
    otherShapeStrictCostDominance feasible FiniteAdditionStrategy.cost shape := by
  intro strategy hfeasible hshape
  rcases hsplit strategy hfeasible hshape with
    ⟨alternative, hreplacement, halternative⟩
  exact ⟨alternative, halternative,
    AppendixEContextualSplitBallotReplacement.cost_lt hreplacement⟩

/--
Appendix E dominance from separated obligations: structural decomposition of
every feasible `other` strategy into one of the contextual split blocks, and
source-model feasibility preservation for contextual split targets.
-/
theorem otherShapeStrictCostDominance_of_positiveAppendixESplitBlock_and_contextualSplit_feasible
    {Candidate : Type*} [DecidableEq Candidate]
    {winners : Finset Candidate}
    {feasible : FiniteAdditionStrategy Candidate → Prop}
    {shape : FiniteAdditionStrategy Candidate → AdditionStrategyShape}
    (hblock :
      ∀ strategy, feasible strategy →
        shape strategy = AdditionStrategyShape.other →
          StrategyHasPositiveAppendixESplitBlock winners strategy)
    (hfeasible :
      ∀ {source target : FiniteAdditionStrategy Candidate},
        feasible source →
          AppendixEContextualSplitBallotReplacement winners source target →
            feasible target) :
    otherShapeStrictCostDominance feasible FiniteAdditionStrategy.cost shape := by
  refine
    otherShapeStrictCostDominance_of_contextualAppendixESplitBallotReplacement
      (winners := winners) ?_
  intro strategy hstrategy hshape
  rcases
    exists_contextualAppendixESplitBallotReplacement_of_positiveAppendixESplitBlock
      (hblock strategy hstrategy hshape)
    with ⟨alternative, hreplacement⟩
  exact ⟨alternative, hreplacement, hfeasible hstrategy hreplacement⟩

/--
Outcome-model form of the Appendix E feasibility-preservation obligation: it
is enough to prove that contextual split replacements preserve the winner set
of the concrete finite-strategy outcome map.
-/
theorem contextualAppendixESplitBallotReplacement_feasible_of_outcome_winners_eq
    {Candidate : Type*} [DecidableEq Candidate]
    (model : FiniteAdditionStrategyOutcomeModel Candidate)
    {source target : FiniteAdditionStrategy Candidate}
    (hsource : model.feasible source)
    (hreplacement :
      AppendixEContextualSplitBallotReplacement model.targetWinners source
        target)
    (hwinners : (model.outcome target).winners =
      (model.outcome source).winners) :
    model.feasible target := by
  exact model.feasible_of_winners_eq hsource hwinners

/--
Outcome-model Appendix E feasibility from target inclusion plus a seat-count
bound.  This packages the version of the source proof that only needs to show
the intended winners still win after the split; exact winner-set equality then
follows from the fixed number of available winner slots.
-/
theorem contextualAppendixESplitBallotReplacement_feasible_of_target_subset_card_le
    {Candidate : Type*} [DecidableEq Candidate]
    (model : FiniteAdditionStrategyOutcomeModel Candidate)
    {source target : FiniteAdditionStrategy Candidate}
    (_hsource : model.feasible source)
    (_hreplacement :
      AppendixEContextualSplitBallotReplacement model.targetWinners source
        target)
    (hsubset : model.targetWinners ⊆ (model.outcome target).winners)
    (hcard : (model.outcome target).winners.card ≤
      model.targetWinners.card) :
    model.feasible target := by
  exact
    model.feasible_of_targetWinners_subset_outcome_of_card_le hsubset hcard

/--
Theorem 5.4 dominance in a finite-strategy outcome model.  The only semantic
STV obligation is now the winner-set preservation of contextual Appendix E
splits; the list decomposition and strict cost decrease are handled in Lean.
-/
theorem otherShapeStrictCostDominance_of_positiveAppendixESplitBlock_and_outcome_winners_eq
    {Candidate : Type*} [DecidableEq Candidate]
    (model : FiniteAdditionStrategyOutcomeModel Candidate)
    {shape : FiniteAdditionStrategy Candidate → AdditionStrategyShape}
    (hblock :
      ∀ strategy, model.feasible strategy →
        shape strategy = AdditionStrategyShape.other →
          StrategyHasPositiveAppendixESplitBlock model.targetWinners strategy)
    (hwinners :
      ∀ {source target : FiniteAdditionStrategy Candidate},
        model.feasible source →
          AppendixEContextualSplitBallotReplacement model.targetWinners
            source target →
            (model.outcome target).winners =
              (model.outcome source).winners) :
    otherShapeStrictCostDominance model.feasible
      FiniteAdditionStrategy.cost shape := by
  exact
    otherShapeStrictCostDominance_of_positiveAppendixESplitBlock_and_contextualSplit_feasible
      (winners := model.targetWinners)
      (feasible := model.feasible)
      (shape := shape)
      hblock
      (by
        intro source target hsource hreplacement
        exact
          contextualAppendixESplitBallotReplacement_feasible_of_outcome_winners_eq
            model hsource hreplacement (hwinners hsource hreplacement))

/--
Theorem 5.4 dominance in a finite-strategy outcome model, using the weaker
STV obligation suggested by the source proof: after a contextual Appendix E
split, all target winners still win, and the outcome elects no more candidates
than the target set.
-/
theorem otherShapeStrictCostDominance_of_positiveAppendixESplitBlock_and_outcome_target_subset_card_le
    {Candidate : Type*} [DecidableEq Candidate]
    (model : FiniteAdditionStrategyOutcomeModel Candidate)
    {shape : FiniteAdditionStrategy Candidate → AdditionStrategyShape}
    (hblock :
      ∀ strategy, model.feasible strategy →
        shape strategy = AdditionStrategyShape.other →
          StrategyHasPositiveAppendixESplitBlock model.targetWinners strategy)
    (hsubset :
      ∀ {source target : FiniteAdditionStrategy Candidate},
        model.feasible source →
          AppendixEContextualSplitBallotReplacement model.targetWinners
            source target →
            model.targetWinners ⊆ (model.outcome target).winners)
    (hcard :
      ∀ {source target : FiniteAdditionStrategy Candidate},
        model.feasible source →
          AppendixEContextualSplitBallotReplacement model.targetWinners
            source target →
            (model.outcome target).winners.card ≤ model.targetWinners.card) :
    otherShapeStrictCostDominance model.feasible
      FiniteAdditionStrategy.cost shape := by
  exact
    otherShapeStrictCostDominance_of_positiveAppendixESplitBlock_and_contextualSplit_feasible
      (winners := model.targetWinners)
      (feasible := model.feasible)
      (shape := shape)
      hblock
      (by
        intro source target hsource hreplacement
        exact
          contextualAppendixESplitBallotReplacement_feasible_of_target_subset_card_le
            model hsource hreplacement
            (hsubset hsource hreplacement)
            (hcard hsource hreplacement))

/--
Theorem 5.4 dominance for the paper's final-order convention.  The fixed
number of winner slots supplies the card bound automatically, so the remaining
STV obligation is target-winner preservation after contextual Appendix E
splits.
-/
theorem otherShapeStrictCostDominance_of_positiveAppendixESplitBlock_and_finalOrder_target_subset
    {Candidate : Type*} [DecidableEq Candidate]
    (model : FiniteAdditionStrategyFinalOrderOutcomeModel Candidate)
    {shape : FiniteAdditionStrategy Candidate → AdditionStrategyShape}
    (hblock :
      ∀ strategy, model.feasible strategy →
        shape strategy = AdditionStrategyShape.other →
          StrategyHasPositiveAppendixESplitBlock model.targetWinners strategy)
    (hsubset :
      ∀ {source target : FiniteAdditionStrategy Candidate},
        model.feasible source →
          AppendixEContextualSplitBallotReplacement model.targetWinners
            source target →
            model.targetWinners ⊆
              (model.finalOrder target).topCandidates model.seatCount) :
    otherShapeStrictCostDominance model.feasible
      FiniteAdditionStrategy.cost shape := by
  change
    otherShapeStrictCostDominance model.toOutcomeModel.feasible
      FiniteAdditionStrategy.cost shape
  refine
    otherShapeStrictCostDominance_of_positiveAppendixESplitBlock_and_outcome_target_subset_card_le
      (model := model.toOutcomeModel)
      ?_ ?_ ?_
  · intro strategy hfeasible hshape
    exact hblock strategy hfeasible hshape
  · intro source target hsource hreplacement
    simpa using hsubset hsource hreplacement
  · intro source target _hsource _hreplacement
    exact
      FiniteAdditionStrategyFinalOrderOutcomeModel.outcome_winners_card_le_targetWinners_card
        model target

/--
Theorem 5.4 dominance for the final-order convention, with target preservation
factored through the source's Lemma B.2 round-winner/election-loser language.
-/
theorem otherShapeStrictCostDominance_of_positiveAppendixESplitBlock_and_finalOrder_roundWinners
    {Candidate : Type*} [DecidableEq Candidate]
    (model : FiniteAdditionStrategyFinalOrderOutcomeModel Candidate)
    {shape : FiniteAdditionStrategy Candidate → AdditionStrategyShape}
    (hblock :
      ∀ strategy, model.feasible strategy →
        shape strategy = AdditionStrategyShape.other →
          StrategyHasPositiveAppendixESplitBlock model.targetWinners strategy)
    (hround :
      ∀ {source target : FiniteAdditionStrategy Candidate},
        model.feasible source →
          AppendixEContextualSplitBallotReplacement model.targetWinners
            source target →
            ∃ roundWinners : Finset Candidate,
              model.targetWinners ⊆ roundWinners ∧
                roundWinners ⊆ (model.finalOrder target).order.toFinset ∧
                  Disjoint roundWinners
                    ((model.finalOrder target).order.drop
                      model.seatCount).toFinset) :
    otherShapeStrictCostDominance model.feasible
      FiniteAdditionStrategy.cost shape := by
  refine
    otherShapeStrictCostDominance_of_positiveAppendixESplitBlock_and_finalOrder_target_subset
      (model := model) hblock ?_
  intro source target hsource hreplacement
  rcases hround hsource hreplacement with
    ⟨roundWinners, htarget_round, hlisted, hnever⟩
  exact htarget_round.trans
    (FinalOrder.subset_topCandidates_of_subset_toFinset_of_disjoint_drop
      (finalOrder := model.finalOrder target) (k := model.seatCount)
      hlisted hnever)

/--
The source-named Appendix E branch certificate is a specialization of the
generic split replacement certificate.
-/
def otherShapeSplitReplacementCertificate_of_appendixE
    {Strategy : Type*}
    {feasible : Strategy → Prop} {cost : Strategy → ℝ}
    {shape : Strategy → AdditionStrategyShape}
    (cert : AppendixESplitReplacementCertificate feasible cost shape) :
    OtherShapeSplitReplacementCertificate feasible cost shape where
  leftCase := cert.firstWinnerThenLoser
  rightCase := cert.firstWinnerThenWinner
  split_other := cert.split_other
  leftReplacement := cert.splitBeforeWinnerReplacement
  leftReplacement_feasible := cert.splitBeforeWinnerReplacement_feasible
  leftReplacement_cost_lt := cert.splitBeforeWinnerReplacement_cost_lt
  rightReplacement := cert.splitAroundWinnersReplacement
  rightReplacement_feasible := cert.splitAroundWinnersReplacement_feasible
  rightReplacement_cost_lt := cert.splitAroundWinnersReplacement_cost_lt

/--
The Appendix-E-shaped branch certificate supplies strict-cost dominance for
catch-all `other` strategies.
-/
theorem otherShapeStrictCostDominance_of_appendixESplitReplacementCertificate
    {Strategy : Type*}
    {feasible : Strategy → Prop} {cost : Strategy → ℝ}
    {shape : Strategy → AdditionStrategyShape}
    (cert : AppendixESplitReplacementCertificate feasible cost shape) :
    otherShapeStrictCostDominance feasible cost shape :=
  otherShapeStrictCostDominance_of_splitReplacementCertificate
    (otherShapeSplitReplacementCertificate_of_appendixE cert)

/--
Source-shaped Case-(A) certificate: optimal altruistic-to-winners strategies
must use post-win surplus transfers, and the source model identifies any such
surplus-transfer configuration as Case (A).
-/
structure AltruisticWinnerCaseACertificate {Strategy : Type*}
    (caseA : Prop) (shape : Strategy → AdditionStrategyShape)
    (optimal : Strategy → Prop) where
  usesPostWinSurplus : Strategy → Prop
  altruisticToWinners_uses_surplus : ∀ strategy, optimal strategy →
    shape strategy = AdditionStrategyShape.altruisticToWinners →
      usesPostWinSurplus strategy
  caseA_of_uses_surplus : ∀ strategy, usesPostWinSurplus strategy → caseA

/--
Project the Case-(A) bridge needed by Theorem 5.4 from the source-shaped
surplus-transfer certificate.
-/
theorem altruisticWinner_caseA_of_certificate {Strategy : Type*}
    {caseA : Prop} {shape : Strategy → AdditionStrategyShape}
    {optimal : Strategy → Prop}
    (cert : AltruisticWinnerCaseACertificate caseA shape optimal) :
    ∀ strategy, optimal strategy →
      shape strategy = AdditionStrategyShape.altruisticToWinners → caseA := by
  intro strategy hoptimal hshape
  exact cert.caseA_of_uses_surplus strategy
    (cert.altruisticToWinners_uses_surplus strategy hoptimal hshape)

/--
Case-(A) bridge when Case (A) is represented by the existence of a
post-win-surplus strategy: any optimal altruistic-to-winners strategy witnesses
that occurrence.
-/
theorem altruisticWinner_caseA_occurs_of_usesPostWinSurplus
    {Strategy : Type*}
    {shape : Strategy → AdditionStrategyShape}
    {optimal : Strategy → Prop}
    {usesPostWinSurplus : Strategy → Prop}
    (huses : ∀ strategy, optimal strategy →
      shape strategy = AdditionStrategyShape.altruisticToWinners →
        usesPostWinSurplus strategy) :
    ∀ strategy, optimal strategy →
      shape strategy = AdditionStrategyShape.altruisticToWinners →
        theorem5_4_caseA_occurs usesPostWinSurplus := by
  intro strategy hoptimal hshape
  exact ⟨strategy, huses strategy hoptimal hshape⟩

/-- Ex-post impossibility of every coalition member benefiting in every state. -/
def exPostCoalitionAllBenefitImpossible {State Candidate : Type*}
    (coalition : Finset Candidate)
    (benefits : State → Candidate → Prop) : Prop :=
  ∀ state, ¬ coalitionAllBenefit coalition (benefits state)

/-- Ex-ante possibility that every coalition member benefits. -/
def exAnteCoalitionAllBenefitPossible {Candidate : Type*}
    (coalition : Finset Candidate) (benefits : Candidate → Prop) : Prop :=
  coalitionAllBenefit coalition benefits

/--
Existential ex-ante witness used by Proposition 5.5: at the abstract
benefit-predicate layer, there is a predicate under which every coalition
member benefits.  This is the Lean-side witness for the paper's existential
"there exist distributions" claim; concrete distributional semantics can
instantiate the predicate in a richer model.
-/
theorem exists_exAnteCoalitionAllBenefitPossible {Candidate : Type*}
    (coalition : Finset Candidate) :
    ∃ benefits : Candidate → Prop,
      exAnteCoalitionAllBenefitPossible coalition benefits := by
  exact ⟨fun candidate => candidate ∈ coalition, by
    intro candidate hcandidate
    exact hcandidate⟩

/-- A strategy is ex-post beneficial in every realized state. -/
def alwaysExPostBeneficial {State : Type*} (benefit : State → Prop) : Prop :=
  ∀ state, benefit state

/-- A strategy may be ex-post disadvantageous in some realized state. -/
def mayBeExPostDisadvantageous {State : Type*}
    (disadvantage : State → Prop) : Prop :=
  ∃ state, disadvantage state

/--
Concrete Proposition 5.6 downside witness: in some realized round, the
strategist is eliminated before the beneficiary by a margin smaller than the
votes allocated to the non-selfish strategy.
-/
def eliminatedEarlyByMarginLessThanAddedVotes {Round Margin : Type*} [LT Margin]
    (eliminatedBeforeBeneficiary : Round → Prop)
    (margin addedVotes : Round → Margin) : Prop :=
  ∃ round, eliminatedBeforeBeneficiary round ∧ margin round < addedVotes round

/--
First shared-library boundary for Proposition 2.1 / Theorem B.1 work:
a proposed structure replay exposes a monotone deterministic STV trace.
-/
theorem stv_structure_replay_active_monotone {Candidate : Type*}
    {trace : RCVTrace Candidate} {outcome : RCVWinLossStructure Candidate}
    (h : StructureReplay trace outcome) :
    trace.activeMonotone :=
  h.1

/--
Proposition 2.1 uniqueness consequence: a tie-broken structure partition gives
exactly one structure for every voter-data point.
-/
theorem proposition2_1_existsUnique_structure_of_partition {Data Candidate : Type*}
    {constraints : RCVStructureConstraints Data Candidate}
    (hpartition : rcvStructurePartition constraints) (data : Data) :
    ∃! struct : RCVStructure Candidate, constraints struct data :=
  hpartition data

/--
Proposition 2.1 uniqueness from the Appendix B.2 generated-constraint
characterization.
-/
theorem proposition2_1_existsUnique_structure_of_characterization
    {Data Candidate : Type*} {structureOf : Data → RCVStructure Candidate}
    {constraints : RCVStructureConstraints Data Candidate}
    (hcharacterization :
      rcvStructureConstraintCharacterization structureOf constraints)
    (data : Data) :
    ∃! struct : RCVStructure Candidate, constraints struct data :=
  proposition2_1_existsUnique_structure_of_partition
    (rcvStructurePartition_of_constraintCharacterization hcharacterization) data

/--
Proposition 2.1 concrete classifier-generated constraints: a deterministic
structure classifier's generated constraint family selects exactly one
order-and-sequence structure at each data point.
-/
theorem proposition2_1_existsUnique_structure_of_classifierConstraints
    {Data Candidate : Type*}
    (structureOf : Data → RCVStructure Candidate) (data : Data) :
    ∃! struct : RCVStructure Candidate,
      rcvStructureClassifierConstraints structureOf struct data :=
  proposition2_1_existsUnique_structure_of_characterization
    (rcvStructureConstraintCharacterization_classifierConstraints structureOf)
    data

/--
Any two structures whose constraints contain the same voter-data point coincide
under a tie-broken structure partition.
-/
theorem proposition2_1_structure_eq_of_partition {Data Candidate : Type*}
    {constraints : RCVStructureConstraints Data Candidate}
    (hpartition : rcvStructurePartition constraints) {data : Data}
    {struct otherStruct : RCVStructure Candidate}
    (hstruct : constraints struct data)
    (hother : constraints otherStruct data) :
    struct = otherStruct :=
  structure_eq_of_structurePartition hpartition hstruct hother

/--
The election result can be obtained by running STV or by verifying the
constraints of the realized structure.
-/
theorem proposition2_1_run_eq_structure_order_of_agreement {Data Candidate : Type*}
    {runSTV : Data → FinalOrder Candidate}
    {constraints : RCVStructureConstraints Data Candidate}
    (hagreement : rcvStructureOutcomeAgreement runSTV constraints)
    {data : Data} {struct : RCVStructure Candidate}
    (hstruct : constraints struct data) :
    runSTV data = struct.finalOrder :=
  hagreement hstruct

/--
Proposition 2.1 direct-run/constraint agreement from the generated-constraint
characterization and agreement with its deterministic classifier.
-/
theorem proposition2_1_run_eq_structure_order_of_characterization
    {Data Candidate : Type*} {runSTV : Data → FinalOrder Candidate}
    {structureOf : Data → RCVStructure Candidate}
    {constraints : RCVStructureConstraints Data Candidate}
    (hcharacterization :
      rcvStructureConstraintCharacterization structureOf constraints)
    (hrun : ∀ data, runSTV data = (structureOf data).finalOrder)
    {data : Data} {struct : RCVStructure Candidate}
    (hstruct : constraints struct data) :
    runSTV data = struct.finalOrder :=
by
  have hstruct_eq : struct = structureOf data :=
    (hcharacterization (data := data) (struct := struct)).mp hstruct
  rw [hstruct_eq]
  exact hrun data

/--
Proposition 2.1 concrete classifier-generated constraints agree with direct
`F_STV` whenever the deterministic classifier records the direct run's final
order.
-/
theorem proposition2_1_run_eq_structure_order_of_classifierConstraints
    {Data Candidate : Type*} {runSTV : Data → FinalOrder Candidate}
    (structureOf : Data → RCVStructure Candidate)
    (hrun : ∀ data, runSTV data = (structureOf data).finalOrder)
    {data : Data} {struct : RCVStructure Candidate}
    (hstruct : rcvStructureClassifierConstraints structureOf struct data) :
    runSTV data = struct.finalOrder :=
  proposition2_1_run_eq_structure_order_of_characterization
    (runSTV := runSTV)
    (structureOf := structureOf)
    (constraints := rcvStructureClassifierConstraints structureOf)
    (rcvStructureConstraintCharacterization_classifierConstraints structureOf)
    hrun hstruct

/--
Theorem B.1 well-defined-order consequence: the structure partition determines
a unique final social choice order.
-/
theorem theoremB1_unique_finalOrder_of_structurePartition {Data Candidate : Type*}
    {constraints : RCVStructureConstraints Data Candidate}
    (hpartition : rcvStructurePartition constraints) (data : Data) :
    ∃! order : FinalOrder Candidate,
      finalOrderRealizedByConstraints constraints data order := by
  rcases hpartition data with ⟨struct, hstruct, hunique⟩
  refine ⟨struct.finalOrder, ⟨struct, hstruct, rfl⟩, ?_⟩
  intro order horder
  rcases horder with ⟨otherStruct, hotherStruct, horder⟩
  have hstruct_eq : otherStruct = struct := hunique otherStruct hotherStruct
  rw [horder, hstruct_eq]

/--
Theorem B.1 well-defined-order consequence from the generated-constraint
characterization.
-/
theorem theoremB1_unique_finalOrder_of_constraintCharacterization
    {Data Candidate : Type*} {structureOf : Data → RCVStructure Candidate}
    {constraints : RCVStructureConstraints Data Candidate}
    (hcharacterization :
      rcvStructureConstraintCharacterization structureOf constraints)
    (data : Data) :
    ∃! order : FinalOrder Candidate,
      finalOrderRealizedByConstraints constraints data order :=
  theoremB1_unique_finalOrder_of_structurePartition
    (rcvStructurePartition_of_constraintCharacterization hcharacterization) data

/--
Theorem B.1 concrete classifier-generated constraints determine a unique final
social choice order for every voter-data point.
-/
theorem theoremB1_unique_finalOrder_of_classifierConstraints
    {Data Candidate : Type*}
    (structureOf : Data → RCVStructure Candidate) (data : Data) :
    ∃! order : FinalOrder Candidate,
      finalOrderRealizedByConstraints
        (rcvStructureClassifierConstraints structureOf) data order :=
  theoremB1_unique_finalOrder_of_constraintCharacterization
    (rcvStructureConstraintCharacterization_classifierConstraints structureOf)
    data

/--
Under direct-run/constraint agreement, the final order returned by `F_STV` is
the unique constraint-realized final order.
-/
theorem theoremB1_run_finalOrder_realized_by_constraints {Data Candidate : Type*}
    {runSTV : Data → FinalOrder Candidate}
    {constraints : RCVStructureConstraints Data Candidate}
    (hpartition : rcvStructurePartition constraints)
    (hagreement : rcvStructureOutcomeAgreement runSTV constraints)
    (data : Data) :
    finalOrderRealizedByConstraints constraints data (runSTV data) := by
  rcases exists_structure_of_structurePartition hpartition data with ⟨struct, hstruct⟩
  exact ⟨struct, hstruct, hagreement hstruct⟩

/--
Under the generated-constraint characterization and direct agreement with its
classifier, the final order returned by `F_STV` is realized by the verified
structure constraints.
-/
theorem theoremB1_run_finalOrder_realized_by_constraintCharacterization
    {Data Candidate : Type*} {runSTV : Data → FinalOrder Candidate}
    {structureOf : Data → RCVStructure Candidate}
    {constraints : RCVStructureConstraints Data Candidate}
    (hcharacterization :
      rcvStructureConstraintCharacterization structureOf constraints)
    (hrun : ∀ data, runSTV data = (structureOf data).finalOrder)
    (data : Data) :
    finalOrderRealizedByConstraints constraints data (runSTV data) :=
  theoremB1_run_finalOrder_realized_by_constraints
    (rcvStructurePartition_of_constraintCharacterization hcharacterization)
    (rcvStructureOutcomeAgreement_of_constraintCharacterization
      (structureOf := structureOf) (constraints := constraints)
      hcharacterization hrun)
    data

/--
Theorem B.1 concrete classifier-generated constraints realize the final order
returned by direct `F_STV` whenever the deterministic classifier records that
same final order.
-/
theorem theoremB1_run_finalOrder_realized_by_classifierConstraints
    {Data Candidate : Type*} {runSTV : Data → FinalOrder Candidate}
    (structureOf : Data → RCVStructure Candidate)
    (hrun : ∀ data, runSTV data = (structureOf data).finalOrder) :
    ∀ data,
      finalOrderRealizedByConstraints
        (rcvStructureClassifierConstraints structureOf) data (runSTV data) := by
  intro data
  exact theoremB1_run_finalOrder_realized_by_constraintCharacterization
    (runSTV := runSTV)
    (structureOf := structureOf)
    (constraints := rcvStructureClassifierConstraints structureOf)
    (rcvStructureConstraintCharacterization_classifierConstraints structureOf)
    hrun data

/--
Source-facing form of Lemma B.2's round-winner/election-loser separation: a
set of round-winning candidates is never in the election-loser set when it is
contained in the final winners.
-/
def roundWinningCandidatesNeverElectionLosers {Candidate : Type*}
    [DecidableEq Candidate] (roundWinners : Finset Candidate)
    (outcome : RCVWinLossStructure Candidate) : Prop :=
  Disjoint roundWinners outcome.losers

/--
Closed core of Lemma B.2: any certified round-winner subset of the final winner
set is disjoint from the final loser set.
-/
theorem lemmaB2_roundWinning_never_electionLoser_of_subset {Candidate : Type*}
    [DecidableEq Candidate] {roundWinners : Finset Candidate}
    {outcome : RCVWinLossStructure Candidate}
    (hsubset : roundWinners ⊆ outcome.winners) :
    roundWinningCandidatesNeverElectionLosers roundWinners outcome := by
  exact outcome.disjoint.mono_left hsubset

/--
Lemma B.2 final-order form: if the election outcome is represented by a
no-duplicate final order and the paper's first `k` candidates are the elected
winners, every certified round winner contained in that top segment is not an
election loser.
-/
theorem lemmaB2_roundWinning_never_electionLoser_of_finalOrder_topCandidates
    {Candidate : Type*} [DecidableEq Candidate]
    {roundWinners : Finset Candidate} {finalOrder : FinalOrder Candidate}
    {k : ℕ}
    (hsubset : roundWinners ⊆ finalOrder.topCandidates k) :
    roundWinningCandidatesNeverElectionLosers roundWinners
      (WinLossStructure.ofFinalOrder finalOrder k) := by
  exact lemmaB2_roundWinning_never_electionLoser_of_subset hsubset

/--
Conversely, for a complete source final order, Lemma B.2's no-election-loser
condition turns listed round winners into top-`k` election winners.
-/
theorem roundWinners_subset_topCandidates_of_neverElectionLosers_finalOrder
    {Candidate : Type*} [DecidableEq Candidate]
    {roundWinners : Finset Candidate} {finalOrder : FinalOrder Candidate}
    {k : ℕ}
    (hlisted : roundWinners ⊆ finalOrder.order.toFinset)
    (hnever :
      roundWinningCandidatesNeverElectionLosers roundWinners
        (WinLossStructure.ofFinalOrder finalOrder k)) :
    roundWinners ⊆ finalOrder.topCandidates k := by
  exact
    FinalOrder.subset_topCandidates_of_subset_toFinset_of_disjoint_drop
      (finalOrder := finalOrder) (k := k) hlisted hnever

/--
If every target winner is among the listed round winners, and Lemma B.2 shows
those round winners are not election losers, then the target set is contained
in the final-order winner set.
-/
theorem targetWinners_subset_topCandidates_of_roundWinners_neverElectionLosers
    {Candidate : Type*} [DecidableEq Candidate]
    {targetWinners roundWinners : Finset Candidate}
    {finalOrder : FinalOrder Candidate} {k : ℕ}
    (htarget_round : targetWinners ⊆ roundWinners)
    (hlisted : roundWinners ⊆ finalOrder.order.toFinset)
    (hnever :
      roundWinningCandidatesNeverElectionLosers roundWinners
        (WinLossStructure.ofFinalOrder finalOrder k)) :
    targetWinners ⊆ finalOrder.topCandidates k :=
  htarget_round.trans
    (roundWinners_subset_topCandidates_of_neverElectionLosers_finalOrder
      hlisted hnever)

/--
Source-facing Proposition 3.3 win-count boundary: the number of round-winning
positions in a feasible sequence is at most the number of election winners.
-/
def feasibleSequenceWinCountBound (sequence : RCVSequence) (k : ℕ) : Prop :=
  rcvSequenceWinCount sequence ≤ k

/--
Source-facing Proposition 3.3 family predicate: every feasible fixed-length
win/loss sequence has between one and `k` round wins.
-/
def feasibleSequenceFamilyWinBound {rounds : ℕ}
    (sequences : Finset (RCVFixedLengthSequence rounds)) (k : ℕ) : Prop :=
  ∀ sequence ∈ sequences,
    1 ≤ (RoundOutcome.winPositions sequence).card ∧
      (RoundOutcome.winPositions sequence).card ≤ k

/--
Source-facing Proposition 3.3 bridge: if every winning position in a feasible
sequence maps injectively to a final election winner, then each sequence has at
most `k` winning positions.
-/
theorem feasibleSequenceFamilyWinBound_of_roundWinner_injective
    {rounds k : ℕ} {Candidate : Type*} [DecidableEq Candidate]
    {sequences : Finset (RCVFixedLengthSequence rounds)}
    {electionWinners : Finset Candidate}
    (roundWinnerAt :
      RCVFixedLengthSequence rounds → Fin rounds → Candidate)
    (hwin_nonempty : ∀ sequence ∈ sequences,
      1 ≤ (RoundOutcome.winPositions sequence).card)
    (hwinner_mem : ∀ sequence ∈ sequences, ∀ position,
      position ∈ RoundOutcome.winPositions sequence →
        roundWinnerAt sequence position ∈ electionWinners)
    (hwinner_injective : ∀ sequence ∈ sequences,
      ∀ position ∈ RoundOutcome.winPositions sequence,
        ∀ otherPosition ∈ RoundOutcome.winPositions sequence,
          roundWinnerAt sequence position =
            roundWinnerAt sequence otherPosition →
        position = otherPosition)
    (hwinners_card : electionWinners.card ≤ k) :
    feasibleSequenceFamilyWinBound sequences k := by
  intro sequence hsequence
  refine ⟨hwin_nonempty sequence hsequence, ?_⟩
  have hpositions_card :
      (RoundOutcome.winPositions sequence).card ≤ electionWinners.card := by
    refine Finset.card_le_card_of_injOn
      (fun position => roundWinnerAt sequence position) ?_ ?_
    · intro position hposition
      exact hwinner_mem sequence hsequence position hposition
    · intro position hposition otherPosition hotherPosition heq
      exact hwinner_injective sequence hsequence
        position hposition otherPosition hotherPosition heq
  exact le_trans hpositions_card hwinners_card

/--
Final-order form of the Proposition 3.3 family bound: if every winning
position injects into the first `k` candidates of the source final order, then
every feasible sequence has between one and `k` wins.
-/
theorem feasibleSequenceFamilyWinBound_of_roundWinner_injective_finalOrder
    {rounds k : ℕ} {Candidate : Type*} [DecidableEq Candidate]
    {sequences : Finset (RCVFixedLengthSequence rounds)}
    {finalOrder : FinalOrder Candidate}
    (roundWinnerAt :
      RCVFixedLengthSequence rounds → Fin rounds → Candidate)
    (hwin_nonempty : ∀ sequence ∈ sequences,
      1 ≤ (RoundOutcome.winPositions sequence).card)
    (hwinner_mem : ∀ sequence ∈ sequences, ∀ position,
      position ∈ RoundOutcome.winPositions sequence →
        roundWinnerAt sequence position ∈ finalOrder.topCandidates k)
    (hwinner_injective : ∀ sequence ∈ sequences,
      ∀ position ∈ RoundOutcome.winPositions sequence,
        ∀ otherPosition ∈ RoundOutcome.winPositions sequence,
          roundWinnerAt sequence position =
            roundWinnerAt sequence otherPosition →
          position = otherPosition) :
    feasibleSequenceFamilyWinBound sequences k := by
  exact
    feasibleSequenceFamilyWinBound_of_roundWinner_injective
      (k := k) (electionWinners := finalOrder.topCandidates k)
      roundWinnerAt hwin_nonempty hwinner_mem hwinner_injective
      (finalOrder.topCandidates_card_le k)

/--
Closed core of Proposition 3.3: if the round-winning labels are represented by
a set of round-winning candidates contained in the election winners, and there
are at most `k` election winners, then the sequence has at most `k` wins.
-/
theorem proposition3_3_winCount_le_of_roundWinners_subset_electionWinners
    {Candidate : Type*} [DecidableEq Candidate] {sequence : RCVSequence}
    {roundWinners electionWinners : Finset Candidate} {k : ℕ}
    (hcount : rcvSequenceWinCount sequence = roundWinners.card)
    (hsubset : roundWinners ⊆ electionWinners)
    (hwinners_card : electionWinners.card ≤ k) :
    feasibleSequenceWinCountBound sequence k := by
  rw [feasibleSequenceWinCountBound, hcount]
  exact le_trans (Finset.card_le_card hsubset) hwinners_card

/--
Proposition 3.3 final-order form: if the round-winning candidates of a
sequence are contained in the first `k` positions of the source final order,
then the sequence has at most `k` wins.
-/
theorem proposition3_3_winCount_le_of_roundWinners_subset_finalOrder_topCandidates
    {Candidate : Type*} [DecidableEq Candidate] {sequence : RCVSequence}
    {roundWinners : Finset Candidate} {finalOrder : FinalOrder Candidate}
    {k : ℕ}
    (hcount : rcvSequenceWinCount sequence = roundWinners.card)
    (hsubset : roundWinners ⊆ finalOrder.topCandidates k) :
    feasibleSequenceWinCountBound sequence k := by
  exact
    proposition3_3_winCount_le_of_roundWinners_subset_electionWinners
      (sequence := sequence) (roundWinners := roundWinners)
      (electionWinners := finalOrder.topCandidates k) (k := k)
      hcount hsubset (finalOrder.topCandidates_card_le k)

/--
Proposition 3.3 binomial-counting conclusion: once feasible fixed-length
win/loss sequences have between one and `k` winning positions, they inject into
the choice of those positions.
-/
theorem proposition3_3_feasibleSequence_count_le_sum_choose {rounds k : ℕ}
    {sequences : Finset (RCVFixedLengthSequence rounds)}
    (hboundedWins : feasibleSequenceFamilyWinBound sequences k) :
    sequences.card ≤ ∑ wins ∈ Finset.Icc 1 k, rounds.choose wins :=
  RoundOutcome.card_le_sum_choose_of_winPositions_card_bounds hboundedWins

/--
Theorem 3.1 source-facing certificate projection: a SmartAllocation-style
algorithm with the certified invariant returns an optimal strategic addition
and has exact operation count at most `m * n`.
-/
theorem theorem3_1_smartAllocation_optimal_and_linear_runtime {Addition : Type*}
    {algorithm : SmartAllocationProblem Addition → Addition}
    {operationCount : SmartAllocationProblem Addition → ℕ}
    (cert : SmartAllocationCertificate algorithm operationCount)
    (problem : SmartAllocationProblem Addition) :
    EconCSLib.Optimization.IsMinimizerOn problem.feasible problem.cost
        (algorithm problem) ∧
      operationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount := by
  exact ⟨cert.optimal problem, cert.operationCount_le problem⟩

/--
Theorem 3.1 componentwise slack-filling core: after the source STV dynamics
reduce a target structure to independent nonnegative slack requirements, the
exact-fill allocation is optimal and meets the paper's `m * n` runtime bound.
-/
theorem theorem3_1_smartAllocation_slackFilling_optimal_and_linear_runtime
    {Slack : Type*} [Fintype Slack]
    (problem : SmartAllocationSlackFillingProblem Slack) :
    EconCSLib.Optimization.IsMinimizerOn
        (SmartAllocationSlackFillingProblem.feasible problem)
        (SmartAllocationSlackFillingProblem.cost problem)
        (SmartAllocationSlackFillingProblem.algorithm problem) ∧
      SmartAllocationSlackFillingProblem.operationCount problem ≤
        SmartAllocationSlackFillingProblem.linearRuntimeBound problem := by
  exact ⟨
    SmartAllocationSlackFillingProblem.algorithm_optimal problem,
    SmartAllocationSlackFillingProblem.operationCount_le_linearRuntimeBound
      problem⟩

/--
Named constructor for Theorem 3.1's source-shaped STV-to-slack reduction
certificate from the explicit feasibility, cost, algorithm-output, and runtime
obligations.
-/
def smartAllocationSlackReductionCertificate_of_explicit
    {Addition Slack : Type*} [Fintype Slack]
    {algorithm : SmartAllocationProblem Addition → Addition}
    {operationCount : SmartAllocationProblem Addition → ℕ}
    (slackProblem : SmartAllocationProblem Addition →
      SmartAllocationSlackFillingProblem Slack)
    (slackOf : ∀ problem : SmartAllocationProblem Addition, Addition → Slack → ℕ)
    (additionOf : ∀ problem : SmartAllocationProblem Addition, (Slack → ℕ) →
      Addition)
    (algorithm_eq_additionOf :
      ∀ problem : SmartAllocationProblem Addition,
        algorithm problem =
          additionOf problem
            (SmartAllocationSlackFillingProblem.algorithm
              (slackProblem problem)))
    (feasible_of_slack_feasible :
      ∀ (problem : SmartAllocationProblem Addition) (allocation : Slack → ℕ),
        SmartAllocationSlackFillingProblem.feasible (slackProblem problem)
            allocation →
          problem.feasible (additionOf problem allocation))
    (slack_feasible_of_feasible :
      ∀ (problem : SmartAllocationProblem Addition) (addition : Addition),
        problem.feasible addition →
          SmartAllocationSlackFillingProblem.feasible (slackProblem problem)
            (slackOf problem addition))
    (cost_algorithm_eq_slack :
      ∀ problem : SmartAllocationProblem Addition,
        problem.cost (algorithm problem) =
          SmartAllocationSlackFillingProblem.cost (slackProblem problem)
            (SmartAllocationSlackFillingProblem.algorithm
              (slackProblem problem)))
    (cost_eq_slack_of_feasible :
      ∀ (problem : SmartAllocationProblem Addition) (addition : Addition),
        problem.feasible addition →
          problem.cost addition =
            SmartAllocationSlackFillingProblem.cost (slackProblem problem)
              (slackOf problem addition))
    (operationCount_le : ∀ problem : SmartAllocationProblem Addition,
      operationCount problem ≤
        SmartAllocationProblem.linearRuntimeBound problem) :
    SmartAllocationSlackReductionCertificate
      (Slack := Slack) algorithm operationCount where
  slackProblem := slackProblem
  slackOf := slackOf
  additionOf := additionOf
  algorithm_eq_additionOf := algorithm_eq_additionOf
  feasible_of_slack_feasible := feasible_of_slack_feasible
  slack_feasible_of_feasible := slack_feasible_of_feasible
  cost_algorithm_eq_slack := cost_algorithm_eq_slack
  cost_eq_slack_of_feasible := cost_eq_slack_of_feasible
  operationCount_le := operationCount_le

/--
Theorem 3.1 direct STV-to-slack reduction route: if the source dynamics reduce
SmartAllocation to the checked componentwise slack-filling problem while
preserving feasibility, cost, the algorithm output, and the linear operation
bound, then the SmartAllocation output is optimal with the claimed runtime.
-/
theorem theorem3_1_smartAllocation_optimal_and_linear_runtime_of_slack_reduction
    {Addition Slack : Type*} [Fintype Slack]
    {algorithm : SmartAllocationProblem Addition → Addition}
    {operationCount : SmartAllocationProblem Addition → ℕ}
    (slackProblem : SmartAllocationProblem Addition →
      SmartAllocationSlackFillingProblem Slack)
    (slackOf : ∀ problem : SmartAllocationProblem Addition, Addition → Slack → ℕ)
    (additionOf : ∀ problem : SmartAllocationProblem Addition, (Slack → ℕ) →
      Addition)
    (algorithm_eq_additionOf :
      ∀ problem : SmartAllocationProblem Addition,
        algorithm problem =
          additionOf problem
            (SmartAllocationSlackFillingProblem.algorithm
              (slackProblem problem)))
    (feasible_of_slack_feasible :
      ∀ (problem : SmartAllocationProblem Addition) (allocation : Slack → ℕ),
        SmartAllocationSlackFillingProblem.feasible (slackProblem problem)
            allocation →
          problem.feasible (additionOf problem allocation))
    (slack_feasible_of_feasible :
      ∀ (problem : SmartAllocationProblem Addition) (addition : Addition),
        problem.feasible addition →
          SmartAllocationSlackFillingProblem.feasible (slackProblem problem)
            (slackOf problem addition))
    (cost_algorithm_eq_slack :
      ∀ problem : SmartAllocationProblem Addition,
        problem.cost (algorithm problem) =
          SmartAllocationSlackFillingProblem.cost (slackProblem problem)
            (SmartAllocationSlackFillingProblem.algorithm
              (slackProblem problem)))
    (cost_eq_slack_of_feasible :
      ∀ (problem : SmartAllocationProblem Addition) (addition : Addition),
        problem.feasible addition →
          problem.cost addition =
            SmartAllocationSlackFillingProblem.cost (slackProblem problem)
              (slackOf problem addition))
    (operationCount_le : ∀ problem : SmartAllocationProblem Addition,
      operationCount problem ≤
        SmartAllocationProblem.linearRuntimeBound problem)
    (problem : SmartAllocationProblem Addition) :
    EconCSLib.Optimization.IsMinimizerOn problem.feasible problem.cost
        (algorithm problem) ∧
      operationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount := by
  let cert :=
    smartAllocationSlackReductionCertificate_of_explicit
      (Slack := Slack) (algorithm := algorithm)
      (operationCount := operationCount) slackProblem slackOf additionOf
      algorithm_eq_additionOf feasible_of_slack_feasible
      slack_feasible_of_feasible cost_algorithm_eq_slack
      cost_eq_slack_of_feasible operationCount_le
  exact theorem3_1_smartAllocation_optimal_and_linear_runtime
    (smartAllocationCertificate_of_slackCertificate
      (smartAllocationSlackCertificate_of_slackReductionCertificate cert))
    problem

/--
Theorem 3.1 concrete slack-reduction implementation route: the SmartAllocation
algorithm is the source STV-to-slack translation followed by exact
componentwise slack filling, so no arbitrary algorithm or operation-count
equality premises remain.
-/
theorem theorem3_1_smartAllocation_concreteSlackReductionAlgorithm_optimal_and_linear_runtime
    {Addition Slack : Type*} [Fintype Slack]
    (slackProblem : SmartAllocationProblem Addition →
      SmartAllocationSlackFillingProblem Slack)
    (slackOf : ∀ problem : SmartAllocationProblem Addition, Addition → Slack → ℕ)
    (additionOf : ∀ problem : SmartAllocationProblem Addition, (Slack → ℕ) →
      Addition)
    (feasible_of_slack_feasible :
      ∀ (problem : SmartAllocationProblem Addition) (allocation : Slack → ℕ),
        SmartAllocationSlackFillingProblem.feasible (slackProblem problem)
            allocation →
          problem.feasible (additionOf problem allocation))
    (slack_feasible_of_feasible :
      ∀ (problem : SmartAllocationProblem Addition) (addition : Addition),
        problem.feasible addition →
          SmartAllocationSlackFillingProblem.feasible (slackProblem problem)
            (slackOf problem addition))
    (cost_algorithm_eq_slack :
      ∀ problem : SmartAllocationProblem Addition,
        problem.cost
            (smartAllocationSlackReductionAlgorithm slackProblem additionOf
              problem) =
          SmartAllocationSlackFillingProblem.cost (slackProblem problem)
            (SmartAllocationSlackFillingProblem.algorithm
              (slackProblem problem)))
    (cost_eq_slack_of_feasible :
      ∀ (problem : SmartAllocationProblem Addition) (addition : Addition),
        problem.feasible addition →
          problem.cost addition =
            SmartAllocationSlackFillingProblem.cost (slackProblem problem)
              (slackOf problem addition))
    (problem : SmartAllocationProblem Addition) :
    EconCSLib.Optimization.IsMinimizerOn problem.feasible problem.cost
        (smartAllocationSlackReductionAlgorithm slackProblem additionOf
          problem) ∧
      smartAllocationSlackReductionOperationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount := by
  exact
    theorem3_1_smartAllocation_optimal_and_linear_runtime_of_slack_reduction
      (algorithm :=
        smartAllocationSlackReductionAlgorithm slackProblem additionOf)
      (operationCount :=
        smartAllocationSlackReductionOperationCount (Addition := Addition))
      (slackProblem := slackProblem)
      (slackOf := slackOf)
      (additionOf := additionOf)
      (by intro problem; rfl)
      feasible_of_slack_feasible
      slack_feasible_of_feasible
      cost_algorithm_eq_slack
      cost_eq_slack_of_feasible
      (by intro problem; rfl)
      problem

/--
Theorem 3.2 source-facing certificate projection: irrelevant-candidate removal
returns a reduced election instance satisfying its preservation specification
and has exact operation count at most `m * n^4`.
-/
theorem theorem3_2_irrelevantCandidateRemoval_sound_and_quartic_runtime
    {ReducedInstance : Type*}
    {algorithm :
      IrrelevantCandidateReductionProblem ReducedInstance → ReducedInstance}
    {operationCount :
      IrrelevantCandidateReductionProblem ReducedInstance → ℕ}
    (cert : IrrelevantCandidateRemovalCertificate algorithm operationCount)
    (problem : IrrelevantCandidateReductionProblem ReducedInstance) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount ^ 4 := by
  exact ⟨cert.sound problem, cert.operationCount_le problem⟩

/--
Theorem 3.2 trace-certificate projection: if Algorithm 6's condition holds and
the certified STV trace removes a group candidate at every relevant
minimum-tally elimination step, then irrelevant-candidate removal is sound and
has the claimed quartic runtime bound.
-/
theorem theorem3_2_irrelevantCandidateRemoval_sound_and_quartic_runtime_of_traceCertificate
    {ReducedInstance Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      IrrelevantCandidateReductionProblem ReducedInstance → ReducedInstance}
    {operationCount :
      IrrelevantCandidateReductionProblem ReducedInstance → ℕ}
    (cert :
      IrrelevantCandidateRemovalTraceCertificate
        (Voter := Voter) (Candidate := Candidate) algorithm operationCount)
    (problem : IrrelevantCandidateReductionProblem ReducedInstance) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount ^ 4 := by
  exact theorem3_2_irrelevantCandidateRemoval_sound_and_quartic_runtime
    (irrelevantCandidateRemovalCertificate_of_traceCertificate cert) problem

/--
Theorem 3.2 direct Algorithm 6 replay route: if the concrete Algorithm 4
output deletes the removable group and the Algorithm 6 elimination replay
depletes that group, then the reduced election preserves later active support
and the exact quartic operation-count model satisfies the paper bound.
-/
theorem theorem3_2_irrelevantCandidateRemoval_sound_and_quartic_runtime_of_algorithm6_replay
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      IrrelevantCandidateReductionProblem
        (ReducedElectionInstance Voter Candidate) →
          ReducedElectionInstance Voter Candidate}
    {operationCount :
      IrrelevantCandidateReductionProblem
        (ReducedElectionInstance Voter Candidate) → ℕ}
    (voters :
      IrrelevantCandidateReductionProblem
        (ReducedElectionInstance Voter Candidate) → Finset Voter)
    (ballots :
      ∀ problem :
        IrrelevantCandidateReductionProblem
          (ReducedElectionInstance Voter Candidate),
        Voter → RCVBallot Candidate)
    (candidates group startActive terminalActive :
      IrrelevantCandidateReductionProblem
        (ReducedElectionInstance Voter Candidate) → Finset Candidate)
    (quota :
      IrrelevantCandidateReductionProblem
        (ReducedElectionInstance Voter Candidate) → ℕ)
    (trace :
      IrrelevantCandidateReductionProblem
        (ReducedElectionInstance Voter Candidate) → RCVTrace Candidate)
    (hcondition :
      ∀ problem :
        IrrelevantCandidateReductionProblem
          (ReducedElectionInstance Voter Candidate),
        candidateGroupRemovalCondition
          (voters problem) (ballots problem) (candidates problem)
          (group problem) problem.budget (quota problem))
    (hminimal :
      ∀ problem :
        IrrelevantCandidateReductionProblem
          (ReducedElectionInstance Voter Candidate),
        ∀ step, step ∈ (trace problem).steps →
          step.kind = StepKind.eliminate → step.eliminatesMinimalTally)
    (hremove :
      ∀ problem :
        IrrelevantCandidateReductionProblem
          (ReducedElectionInstance Voter Candidate),
        ∀ step, step ∈ (trace problem).steps →
          step.kind = StepKind.eliminate → step.removesFocusedCandidate)
    (hgroup_active :
      ∀ problem :
        IrrelevantCandidateReductionProblem
          (ReducedElectionInstance Voter Candidate),
        ∀ step, step ∈ (trace problem).steps →
          step.kind = StepKind.eliminate →
            ∃ inside, inside ∈ group problem ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ problem :
        IrrelevantCandidateReductionProblem
          (ReducedElectionInstance Voter Candidate),
        ∀ step, step ∈ (trace problem).steps →
          step.kind = StepKind.eliminate →
            step.beforeActive ⊆ candidates problem)
    (htally_inside :
      ∀ problem :
        IrrelevantCandidateReductionProblem
          (ReducedElectionInstance Voter Candidate),
        ∀ step, step ∈ (trace problem).steps →
          step.kind = StepKind.eliminate →
            ∀ inside, inside ∈ group problem → inside ∈ step.beforeActive →
              step.tally inside =
                problem.budget +
                  strictSupportCount (voters problem) (ballots problem)
                    (group problem) (candidates problem \ group problem)
                    inside)
    (htally_outside :
      ∀ problem :
        IrrelevantCandidateReductionProblem
          (ReducedElectionInstance Voter Candidate),
        ∀ step, step ∈ (trace problem).steps →
          step.kind = StepKind.eliminate →
            ∀ inside, inside ∈ group problem → inside ∈ step.beforeActive →
              ∀ outside, outside ∈ candidates problem \ group problem →
                step.tally outside =
                  strictSupportCount (voters problem) (ballots problem)
                    (insert outside ((group problem).erase inside))
                    (∅ : Finset Candidate) outside)
    (hreplay :
      ∀ problem :
        IrrelevantCandidateReductionProblem
          (ReducedElectionInstance Voter Candidate),
        (trace problem).replaysFrom
          (startActive problem) (terminalActive problem))
    (hall_eliminate :
      ∀ problem :
        IrrelevantCandidateReductionProblem
          (ReducedElectionInstance Voter Candidate),
        ∀ step, step ∈ (trace problem).steps →
          step.kind = StepKind.eliminate)
    (hlength :
      ∀ problem :
        IrrelevantCandidateReductionProblem
          (ReducedElectionInstance Voter Candidate),
        (trace problem).steps.length =
          (startActive problem ∩ group problem).card)
    (algorithm_eq :
      ∀ problem :
        IrrelevantCandidateReductionProblem
          (ReducedElectionInstance Voter Candidate),
        algorithm problem =
          reduceElectionInstanceByCandidates
            (group problem) (candidates problem) (ballots problem))
    (output_spec_of_preservation :
      ∀ problem :
        IrrelevantCandidateReductionProblem
          (ReducedElectionInstance Voter Candidate),
        terminalActive problem ∩ group problem = ∅ →
          reducedElectionPreservesActiveSupport
            (voters problem) (ballots problem) (terminalActive problem)
            (algorithm problem) →
          problem.specification (algorithm problem))
    (operationCount_eq :
      ∀ problem :
        IrrelevantCandidateReductionProblem
          (ReducedElectionInstance Voter Candidate),
        operationCount problem =
          irrelevantCandidateRemovalOperationCount
            problem.uniqueBallotCount problem.candidateCount)
    (problem :
      IrrelevantCandidateReductionProblem
        (ReducedElectionInstance Voter Candidate)) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount ^ 4 := by
  have hcore :
      terminalActive problem ∩ group problem = ∅ ∧
        reducedElectionPreservesActiveSupport
          (voters problem) (ballots problem) (terminalActive problem)
          (reduceElectionInstanceByCandidates
            (group problem) (candidates problem) (ballots problem)) ∧
        irrelevantCandidateRemovalOperationCount
            problem.uniqueBallotCount problem.candidateCount ≤
          problem.uniqueBallotCount * problem.candidateCount ^ 4 :=
    algorithm6_replay_reduceElectionInstance_sound_and_quartic_runtime
      (voters := voters problem)
      (ballots := ballots problem)
      (candidates := candidates problem)
      (group := group problem)
      (startActive := startActive problem)
      (terminalActive := terminalActive problem)
      (budget := problem.budget)
      (quota := quota problem)
      (uniqueBallotCount := problem.uniqueBallotCount)
      (candidateCount := problem.candidateCount)
      (trace := trace problem)
      (hcondition problem) (hminimal problem) (hremove problem)
      (hgroup_active problem) (hactive_subset_candidates problem)
      (htally_inside problem) (htally_outside problem)
      (hreplay problem) (hall_eliminate problem) (hlength problem)
  have hpreserve_algorithm :
      reducedElectionPreservesActiveSupport
        (voters problem) (ballots problem) (terminalActive problem)
        (algorithm problem) := by
    rw [algorithm_eq problem]
    exact hcore.2.1
  exact ⟨
    output_spec_of_preservation problem hcore.1 hpreserve_algorithm,
    by
      rw [operationCount_eq problem, irrelevantCandidateRemovalOperationCount]⟩

/--
Theorem 3.2 concrete Algorithm 4/6 route for an implementation: if the
implementation returns the paper's candidate-deletion reduced election on the
concrete source problem, then Algorithm 6's replay proof gives the concrete
specification and exact quartic runtime bound.  Unlike the generic replay
route, this theorem has no arbitrary preservation-to-specification premise.
-/
theorem theorem3_2_concreteReductionAlgorithm_sound_and_quartic_runtime_of_algorithm6_replay
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      IrrelevantCandidateReductionProblem
        (ReducedElectionInstance Voter Candidate) →
          ReducedElectionInstance Voter Candidate}
    {operationCount :
      IrrelevantCandidateReductionProblem
        (ReducedElectionInstance Voter Candidate) → ℕ}
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group startActive terminalActive : Finset Candidate}
    {budget quota uniqueBallotCount candidateCount : ℕ}
    {trace : RCVTrace Candidate}
    (hcondition :
      candidateGroupRemovalCondition
        voters ballots candidates group budget quota)
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots group (candidates \ group)
                inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ group).card)
    (algorithm_eq :
      algorithm
          (irrelevantCandidateConcreteReductionProblem
            voters ballots candidates group terminalActive budget
            uniqueBallotCount candidateCount) =
        reduceElectionInstanceByCandidates group candidates ballots)
    (operationCount_eq :
      operationCount
          (irrelevantCandidateConcreteReductionProblem
            voters ballots candidates group terminalActive budget
            uniqueBallotCount candidateCount) =
        irrelevantCandidateRemovalOperationCount
          uniqueBallotCount candidateCount) :
    (irrelevantCandidateConcreteReductionProblem
        voters ballots candidates group terminalActive budget
        uniqueBallotCount candidateCount).specification
      (algorithm
        (irrelevantCandidateConcreteReductionProblem
          voters ballots candidates group terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      operationCount
          (irrelevantCandidateConcreteReductionProblem
            voters ballots candidates group terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  have hcore :
      (irrelevantCandidateConcreteReductionProblem
          voters ballots candidates group terminalActive budget
          uniqueBallotCount candidateCount).specification
        (reduceElectionInstanceByCandidates group candidates ballots) ∧
        irrelevantCandidateRemovalOperationCount
            uniqueBallotCount candidateCount ≤
          uniqueBallotCount * candidateCount ^ 4 :=
    algorithm6_replay_concreteReductionProblem_sound_and_quartic_runtime
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (group := group) (startActive := startActive)
      (terminalActive := terminalActive) (budget := budget) (quota := quota)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount) (trace := trace)
      hcondition hminimal hremove hgroup_active hactive_subset_candidates
      htally_inside htally_outside hreplay hall_eliminate hlength
  exact ⟨by
    rw [algorithm_eq]
    exact hcore.1, by
    rw [operationCount_eq]
    exact hcore.2⟩

/--
Concrete Theorem 3.2 Algorithm 6 implementation: the source implementation is
the candidate-deletion reduction itself, so the implementation-equality
premises discharge by definition.
-/
theorem theorem3_2_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime_of_algorithm6_replay
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group startActive terminalActive : Finset Candidate}
    {budget quota uniqueBallotCount candidateCount : ℕ}
    {trace : RCVTrace Candidate}
    (hcondition :
      candidateGroupRemovalCondition
        voters ballots candidates group budget quota)
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots group (candidates \ group)
                inside)
    (htally_outside :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ group).card) :
    (irrelevantCandidateConcreteReductionProblem
        voters ballots candidates group terminalActive budget
        uniqueBallotCount candidateCount).specification
      (irrelevantCandidateConcreteReductionAlgorithm ballots candidates group
        (irrelevantCandidateConcreteReductionProblem
          voters ballots candidates group terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      irrelevantCandidateConcreteReductionOperationCount
          (irrelevantCandidateConcreteReductionProblem
            voters ballots candidates group terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  exact
    theorem3_2_concreteReductionAlgorithm_sound_and_quartic_runtime_of_algorithm6_replay
      (algorithm :=
        irrelevantCandidateConcreteReductionAlgorithm ballots candidates group)
      (operationCount :=
        irrelevantCandidateConcreteReductionOperationCount
          (Voter := Voter) (Candidate := Candidate))
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (group := group) (startActive := startActive)
      (terminalActive := terminalActive) (budget := budget) (quota := quota)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount) (trace := trace)
      hcondition hminimal hremove hgroup_active hactive_subset_candidates
      htally_inside htally_outside hreplay hall_eliminate hlength
      rfl rfl

/--
Bounded-tally concrete Theorem 3.2 Algorithm 6 implementation: the source
implementation is candidate deletion itself, and Algorithm 6's replay proof
may supply conservative strict-support tally bounds instead of exact tally
identities.
-/
theorem theorem3_2_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime_of_algorithm6_replay_tally_bounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group startActive terminalActive : Finset Candidate}
    {budget quota uniqueBallotCount candidateCount : ℕ}
    {trace : RCVTrace Candidate}
    (hcondition :
      candidateGroupRemovalCondition
        voters ballots candidates group budget quota)
    (hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally)
    (hremove :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.removesFocusedCandidate)
    (hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive)
    (hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates)
    (htally_inside_le :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside ≤
            budget +
              strictSupportCount voters ballots group (candidates \ group)
                inside)
    (htally_outside_ge :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside ≤
            step.tally outside)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate)
    (hlength : trace.steps.length = (startActive ∩ group).card) :
    (irrelevantCandidateConcreteReductionProblem
        voters ballots candidates group terminalActive budget
        uniqueBallotCount candidateCount).specification
      (irrelevantCandidateConcreteReductionAlgorithm ballots candidates group
        (irrelevantCandidateConcreteReductionProblem
          voters ballots candidates group terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      irrelevantCandidateConcreteReductionOperationCount
          (irrelevantCandidateConcreteReductionProblem
            voters ballots candidates group terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  have hcore :
      (irrelevantCandidateConcreteReductionProblem
          voters ballots candidates group terminalActive budget
          uniqueBallotCount candidateCount).specification
        (reduceElectionInstanceByCandidates group candidates ballots) ∧
        irrelevantCandidateRemovalOperationCount
            uniqueBallotCount candidateCount ≤
          uniqueBallotCount * candidateCount ^ 4 :=
    algorithm6_replay_concreteReductionProblem_sound_and_quartic_runtime_of_tally_bounds
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (group := group) (startActive := startActive)
      (terminalActive := terminalActive) (budget := budget) (quota := quota)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount) (trace := trace)
      hcondition hminimal hremove hgroup_active hactive_subset_candidates
      htally_inside_le htally_outside_ge hreplay hall_eliminate hlength
  exact ⟨by
    simpa [irrelevantCandidateConcreteReductionAlgorithm] using hcore.1, by
    simpa [irrelevantCandidateConcreteReductionOperationCount,
      irrelevantCandidateConcreteReductionProblem] using hcore.2⟩

/--
Algorithm 6 conservative generated tally. Group candidates receive the paper's
budget-plus-strict-support upper tally; outside candidates receive a
conservative sum over every currently active group candidate's outside
strict-support lower tally.
-/
noncomputable def algorithm6ConservativeGeneratedTallyOf
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates group : Finset Candidate) (budget : ℕ) :
    Finset Candidate → Candidate → ℕ :=
  fun active candidate =>
    if candidate ∈ group then
      budget +
        strictSupportCount voters ballots group (candidates \ group)
          candidate
    else
      ∑ inside ∈ active ∩ group,
        strictSupportCount voters ballots
          (insert candidate (group.erase inside)) (∅ : Finset Candidate)
          candidate

/--
Generated Theorem 3.2 Algorithm 6 route: a total active minimum-tally choice
rule generates the replay, all-elimination, group-focus, removal, minimality,
and length facts needed by the concrete candidate-deletion implementation.
The remaining source-shaped premises are the Algorithm 6 inequality condition,
the initial active-set containment, and the tally identities for generated
steps.
-/
theorem theorem3_2_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime_of_generated_group_elimination
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {choice : MinimalTallyChoiceRule Candidate}
    {tallyOf : Finset Candidate → Candidate → ℕ}
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group startActive : Finset Candidate}
    {budget quota uniqueBallotCount candidateCount : ℕ}
    (hactiveChoice : choice.ChoosesActive)
    (htotalChoice : choice.Total)
    (hminimalChoice : choice.SelectsMinimal)
    (hstart_subset : startActive ⊆ candidates)
    (hcondition :
      candidateGroupRemovalCondition
        voters ballots candidates group budget quota)
    (htally_inside :
      ∀ step,
        step ∈
          minimalGroupEliminationGeneratedSteps choice group tallyOf
            (startActive ∩ group).card startActive →
        step.kind = StepKind.eliminate →
          ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
            step.tally inside =
              budget +
                strictSupportCount voters ballots group (candidates \ group)
                  inside)
    (htally_outside :
      ∀ step,
        step ∈
          minimalGroupEliminationGeneratedSteps choice group tallyOf
            (startActive ∩ group).card startActive →
        step.kind = StepKind.eliminate →
          ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          ∀ outside, outside ∈ candidates \ group →
            step.tally outside =
              strictSupportCount voters ballots
                (insert outside (group.erase inside)) (∅ : Finset Candidate)
                outside) :
    let terminalActive :=
      minimalGroupEliminationTerminalActive choice group tallyOf
        (startActive ∩ group).card startActive
    (irrelevantCandidateConcreteReductionProblem
        voters ballots candidates group terminalActive budget
        uniqueBallotCount candidateCount).specification
      (irrelevantCandidateConcreteReductionAlgorithm ballots candidates group
        (irrelevantCandidateConcreteReductionProblem
          voters ballots candidates group terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      irrelevantCandidateConcreteReductionOperationCount
          (irrelevantCandidateConcreteReductionProblem
            voters ballots candidates group terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  intro terminalActive
  let trace : RCVTrace Candidate :=
    minimalGroupEliminationGeneratedTrace choice group tallyOf
      (startActive ∩ group).card startActive
  have hsafety :
      candidateGroupRemovalSafety voters ballots candidates group budget quota :=
    candidateGroupRemovalSafety_of_condition hcondition
  have hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates := by
    intro step hstep _hkind
    exact
      minimalGroupEliminationGeneratedSteps_beforeActive_subset_of_initial_subset
        choice group tallyOf hstart_subset (startActive ∩ group).card step
        (by
          simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
  have hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally := by
    intro step hstep hkind
    exact
      strictSupportGroupRemovalSafety_generated_minimal_eliminations
        (voters := voters) (ballots := ballots) (candidates := candidates)
        (group := group) (budget := budget) (quota := quota)
        (choice := choice) (tallyOf := tallyOf)
        (rounds := (startActive ∩ group).card)
        (initialActive := startActive)
        (by simpa [candidateGroupRemovalSafety] using hsafety)
        hminimalChoice
        (by
          intro generatedStep hgenerated hgenerated_kind
          exact
            minimalGroupEliminationGeneratedSteps_beforeActive_subset_of_initial_subset
              choice group tallyOf hstart_subset (startActive ∩ group).card
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
        choice group tallyOf (startActive ∩ group).card startActive step
        (by
          simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
  have hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive := by
    intro step hstep _hkind
    exact
      minimalGroupEliminationGeneratedSteps_group_active_at_step
        choice group tallyOf (startActive ∩ group).card startActive step
        (by
          simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
  have htally_inside_trace :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside =
            budget +
              strictSupportCount voters ballots group (candidates \ group)
                inside := by
    intro step hstep hkind inside hinside hactive
    exact htally_inside step
      (by simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
      hkind inside hinside hactive
  have htally_outside_trace :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          step.tally outside =
            strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
              outside := by
    intro step hstep hkind inside hinside hactive outside houtside
    exact htally_outside step
      (by simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
      hkind inside hinside hactive outside houtside
  have hreplay : trace.replaysFrom startActive terminalActive := by
    simpa [trace, minimalGroupEliminationGeneratedTrace, STVTrace.replaysFrom,
      terminalActive] using
      minimalGroupEliminationGeneratedSteps_replayStepsFrom
        choice group tallyOf (startActive ∩ group).card startActive
  have hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate := by
    intro step hstep
    exact
      minimalGroupEliminationGeneratedSteps_all_eliminate
        choice group tallyOf (startActive ∩ group).card startActive step
        (by
          simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
  have hlength : trace.steps.length = (startActive ∩ group).card := by
    simpa [trace, minimalGroupEliminationGeneratedTrace] using
      minimalGroupEliminationGeneratedSteps_length_eq
        (choice := choice) hactiveChoice htotalChoice group tallyOf
        (startActive ∩ group).card startActive rfl
  exact
    theorem3_2_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime_of_algorithm6_replay
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (group := group) (startActive := startActive)
      (terminalActive := terminalActive) (budget := budget) (quota := quota)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount) (trace := trace)
      hcondition hminimal hremove hgroup_active hactive_subset_candidates
      htally_inside_trace htally_outside_trace hreplay hall_eliminate hlength

/--
Bounded-tally generated Theorem 3.2 Algorithm 6 route: a total active
minimum-tally choice rule generates the replay and structural trace facts, and
the paper's conservative inside/outside strict-support tally bounds are enough
for the concrete candidate-deletion implementation.
-/
theorem theorem3_2_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime_of_generated_group_elimination_tally_bounds
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {choice : MinimalTallyChoiceRule Candidate}
    {tallyOf : Finset Candidate → Candidate → ℕ}
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group startActive : Finset Candidate}
    {budget quota uniqueBallotCount candidateCount : ℕ}
    (hactiveChoice : choice.ChoosesActive)
    (htotalChoice : choice.Total)
    (hminimalChoice : choice.SelectsMinimal)
    (hstart_subset : startActive ⊆ candidates)
    (hcondition :
      candidateGroupRemovalCondition
        voters ballots candidates group budget quota)
    (htally_inside_le :
      ∀ step,
        step ∈
          minimalGroupEliminationGeneratedSteps choice group tallyOf
            (startActive ∩ group).card startActive →
        step.kind = StepKind.eliminate →
          ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
            step.tally inside ≤
              budget +
                strictSupportCount voters ballots group (candidates \ group)
                  inside)
    (htally_outside_ge :
      ∀ step,
        step ∈
          minimalGroupEliminationGeneratedSteps choice group tallyOf
            (startActive ∩ group).card startActive →
        step.kind = StepKind.eliminate →
          ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          ∀ outside, outside ∈ candidates \ group →
            strictSupportCount voters ballots
                (insert outside (group.erase inside)) (∅ : Finset Candidate)
                outside ≤
              step.tally outside) :
    let terminalActive :=
      minimalGroupEliminationTerminalActive choice group tallyOf
        (startActive ∩ group).card startActive
    (irrelevantCandidateConcreteReductionProblem
        voters ballots candidates group terminalActive budget
        uniqueBallotCount candidateCount).specification
      (irrelevantCandidateConcreteReductionAlgorithm ballots candidates group
        (irrelevantCandidateConcreteReductionProblem
          voters ballots candidates group terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      irrelevantCandidateConcreteReductionOperationCount
          (irrelevantCandidateConcreteReductionProblem
            voters ballots candidates group terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  intro terminalActive
  let trace : RCVTrace Candidate :=
    minimalGroupEliminationGeneratedTrace choice group tallyOf
      (startActive ∩ group).card startActive
  have hsafety :
      candidateGroupRemovalSafety voters ballots candidates group budget quota :=
    candidateGroupRemovalSafety_of_condition hcondition
  have hactive_subset_candidates :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.beforeActive ⊆ candidates := by
    intro step hstep _hkind
    exact
      minimalGroupEliminationGeneratedSteps_beforeActive_subset_of_initial_subset
        choice group tallyOf hstart_subset (startActive ∩ group).card step
        (by
          simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
  have hminimal :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        step.eliminatesMinimalTally := by
    intro step hstep hkind
    exact
      strictSupportGroupRemovalSafety_generated_minimal_eliminations_of_tally_bounds
        (voters := voters) (ballots := ballots) (candidates := candidates)
        (group := group) (budget := budget) (quota := quota)
        (choice := choice) (tallyOf := tallyOf)
        (rounds := (startActive ∩ group).card)
        (initialActive := startActive)
        (by simpa [candidateGroupRemovalSafety] using hsafety)
        hminimalChoice
        (by
          intro generatedStep hgenerated _hgenerated_kind
          exact
            minimalGroupEliminationGeneratedSteps_beforeActive_subset_of_initial_subset
              choice group tallyOf hstart_subset (startActive ∩ group).card
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
        choice group tallyOf (startActive ∩ group).card startActive step
        (by
          simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
  have hgroup_active :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∃ inside, inside ∈ group ∧ inside ∈ step.beforeActive := by
    intro step hstep _hkind
    exact
      minimalGroupEliminationGeneratedSteps_group_active_at_step
        choice group tallyOf (startActive ∩ group).card startActive step
        (by
          simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
  have htally_inside_trace :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
          step.tally inside ≤
            budget +
              strictSupportCount voters ballots group (candidates \ group)
                inside := by
    intro step hstep hkind inside hinside hactive
    exact htally_inside_le step
      (by simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
      hkind inside hinside hactive
  have htally_outside_trace :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate →
        ∀ inside, inside ∈ group → inside ∈ step.beforeActive →
        ∀ outside, outside ∈ candidates \ group →
          strictSupportCount voters ballots
              (insert outside (group.erase inside)) (∅ : Finset Candidate)
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
        choice group tallyOf (startActive ∩ group).card startActive
  have hall_eliminate :
      ∀ step, step ∈ trace.steps → step.kind = StepKind.eliminate := by
    intro step hstep
    exact
      minimalGroupEliminationGeneratedSteps_all_eliminate
        choice group tallyOf (startActive ∩ group).card startActive step
        (by
          simpa [trace, minimalGroupEliminationGeneratedTrace] using hstep)
  have hlength : trace.steps.length = (startActive ∩ group).card := by
    simpa [trace, minimalGroupEliminationGeneratedTrace] using
      minimalGroupEliminationGeneratedSteps_length_eq
        (choice := choice) hactiveChoice htotalChoice group tallyOf
        (startActive ∩ group).card startActive rfl
  exact
    theorem3_2_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime_of_algorithm6_replay_tally_bounds
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (group := group) (startActive := startActive)
      (terminalActive := terminalActive) (budget := budget) (quota := quota)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount) (trace := trace)
      hcondition hminimal hremove hgroup_active hactive_subset_candidates
      htally_inside_trace htally_outside_trace hreplay hall_eliminate hlength

/--
Concrete Theorem 3.2 Algorithm 6 implementation with a canonical conservative
generated tally: the only source-removal premise left is Algorithm 6's
strict-support group-removal condition plus the generic minimum-tally
tie-breaking sanity conditions.
-/
theorem theorem3_2_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime_of_generated_group_elimination_conservative_tally
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {choice : MinimalTallyChoiceRule Candidate}
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates group startActive : Finset Candidate}
    {budget quota uniqueBallotCount candidateCount : ℕ}
    (hactiveChoice : choice.ChoosesActive)
    (htotalChoice : choice.Total)
    (hminimalChoice : choice.SelectsMinimal)
    (hstart_subset : startActive ⊆ candidates)
    (hcondition :
      candidateGroupRemovalCondition
        voters ballots candidates group budget quota) :
    let tallyOf :=
      algorithm6ConservativeGeneratedTallyOf voters ballots candidates group
        budget
    let terminalActive :=
      minimalGroupEliminationTerminalActive choice group tallyOf
        (startActive ∩ group).card startActive
    (irrelevantCandidateConcreteReductionProblem
        voters ballots candidates group terminalActive budget
        uniqueBallotCount candidateCount).specification
      (irrelevantCandidateConcreteReductionAlgorithm ballots candidates group
        (irrelevantCandidateConcreteReductionProblem
          voters ballots candidates group terminalActive budget
          uniqueBallotCount candidateCount)) ∧
      irrelevantCandidateConcreteReductionOperationCount
          (irrelevantCandidateConcreteReductionProblem
            voters ballots candidates group terminalActive budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 4 := by
  intro tallyOf terminalActive
  exact
    theorem3_2_concreteReductionAlgorithmImplementation_sound_and_quartic_runtime_of_generated_group_elimination_tally_bounds
      (choice := choice) (tallyOf := tallyOf)
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (group := group) (startActive := startActive) (budget := budget)
      (quota := quota) (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hactiveChoice htotalChoice hminimalChoice hstart_subset hcondition
      (by
        intro step hstep _hkind inside hinside _hactive
        have htally :
            step.tally = tallyOf step.beforeActive :=
          minimalGroupEliminationGeneratedSteps_tally_eq
            choice group tallyOf (startActive ∩ group).card startActive
            step hstep
        rw [htally]
        simp [tallyOf, algorithm6ConservativeGeneratedTallyOf, hinside])
      (by
        intro step hstep _hkind inside hinside hactive outside houtside
        have htally :
            step.tally = tallyOf step.beforeActive :=
          minimalGroupEliminationGeneratedSteps_tally_eq
            choice group tallyOf (startActive ∩ group).card startActive
            step hstep
        have houtside_not_group : outside ∉ group :=
          (Finset.mem_sdiff.mp houtside).2
        have hinside_mem : inside ∈ step.beforeActive ∩ group :=
          Finset.mem_inter.mpr ⟨hactive, hinside⟩
        rw [htally]
        simp [tallyOf, algorithm6ConservativeGeneratedTallyOf,
          houtside_not_group]
        exact
          Finset.single_le_sum
            (s := step.beforeActive ∩ group)
            (f := fun currentInside =>
              strictSupportCount voters ballots
                (insert outside (group.erase currentInside))
                (∅ : Finset Candidate) outside)
            (by
              intro currentInside _hcurrent
              exact Nat.zero_le _)
            hinside_mem)

/--
Proposition 3.4 source-facing certificate projection: sequence reduction
returns a covering reduced sequence family and has exact operation count at
most `m * n^2`.
-/
theorem proposition3_4_sequenceReduction_sound_and_quadratic_runtime
    {ReducedSequences : Type*}
    {algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences}
    {operationCount : SequenceReductionProblem ReducedSequences → ℕ}
    (cert : SequenceReductionCertificate algorithm operationCount)
    (problem : SequenceReductionProblem ReducedSequences) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount ^ 2 := by
  exact ⟨cert.sound problem, cert.operationCount_le problem⟩

/--
Proposition 3.4 source-facing capacity certificate projection: the
Predict-Wins/Predict-Losses capacity and loss-floor premises imply sequence
reduction soundness and the paper's quadratic operation bound.
-/
theorem proposition3_4_sequenceReduction_sound_and_quadratic_runtime_of_predictionCertificate
    {ReducedSequences Voter Candidate Sequence : Type*}
    [DecidableEq Candidate]
    {algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences}
    {operationCount : SequenceReductionProblem ReducedSequences → ℕ}
    (cert :
      SequenceReductionPredictionCertificate
        (Voter := Voter) (Candidate := Candidate) (Sequence := Sequence)
        algorithm operationCount)
    (problem : SequenceReductionProblem ReducedSequences) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount ^ 2 := by
  exact proposition3_4_sequenceReduction_sound_and_quadratic_runtime
    (sequenceReductionCertificate_of_predictionCertificate cert) problem

/--
Proposition 3.4 source-facing quota-block certificate projection: disjoint
quota-sized support blocks imply the Algorithm 7 capacity premise, which in
turn implies sequence-reduction soundness and the paper's quadratic operation
bound.
-/
theorem proposition3_4_sequenceReduction_sound_and_quadratic_runtime_of_quotaBlockCertificate
    {ReducedSequences Voter Candidate Sequence Round SupportUnit : Type*}
    [DecidableEq Candidate] [DecidableEq SupportUnit]
    {algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences}
    {operationCount : SequenceReductionProblem ReducedSequences → ℕ}
    (cert :
      SequenceReductionQuotaBlockCertificate
        (Voter := Voter) (Candidate := Candidate) (Sequence := Sequence)
        (Round := Round) (SupportUnit := SupportUnit)
        algorithm operationCount)
    (problem : SequenceReductionProblem ReducedSequences) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount ^ 2 := by
  exact proposition3_4_sequenceReduction_sound_and_quadratic_runtime
    (sequenceReductionCertificate_of_quotaBlockCertificate cert) problem

/--
Proposition 3.4 source-facing Algorithm 7 loop-certificate projection:
budgeted Predict-Wins and Predict-Losses prefix witnesses imply
sequence-reduction soundness and the paper's quadratic operation bound.
-/
theorem proposition3_4_sequenceReduction_sound_and_quadratic_runtime_of_budgetedLoopCertificate
    {ReducedSequences Voter Candidate Sequence : Type*}
    [DecidableEq Candidate]
    {algorithm : SequenceReductionProblem ReducedSequences → ReducedSequences}
    {operationCount : SequenceReductionProblem ReducedSequences → ℕ}
    (cert :
      SequenceReductionBudgetedLoopCertificate
        (Voter := Voter) (Candidate := Candidate) (Sequence := Sequence)
        algorithm operationCount)
    (problem : SequenceReductionProblem ReducedSequences) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount ^ 2 := by
  exact proposition3_4_sequenceReduction_sound_and_quadratic_runtime
    (sequenceReductionCertificate_of_budgetedLoopCertificate cert) problem

/--
Proposition 3.4 direct budgeted-accumulator route: when Algorithm 7 returns
the bounded sequence family, the budgeted Predict-Wins accumulator and
Predict-Losses floor imply the source specification and exact quadratic
operation bound without packaging the argument as a sequence-reduction
certificate.
-/
theorem proposition3_4_sequenceReduction_sound_and_quadratic_runtime_of_budgetedPredictWinsSupportAccumulator
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {algorithm :
      SequenceReductionProblem (Finset Sequence) → Finset Sequence}
    {operationCount : SequenceReductionProblem (Finset Sequence) → ℕ}
    (voters : SequenceReductionProblem (Finset Sequence) → Finset Voter)
    (ballots :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        Voter → RCVBallot Candidate)
    (candidates :
      SequenceReductionProblem (Finset Sequence) → Finset Candidate)
    (allSequences :
      SequenceReductionProblem (Finset Sequence) → Finset Sequence)
    (feasibleSequence :
      SequenceReductionProblem (Finset Sequence) → Sequence → Prop)
    (winCount initialLossCount :
      SequenceReductionProblem (Finset Sequence) → Sequence → ℕ)
    (orderedWinners :
      SequenceReductionProblem (Finset Sequence) → Sequence → List Candidate)
    (assignedBudget :
      SequenceReductionProblem (Finset Sequence) → Sequence → Candidate → ℕ)
    (seats predictedWinSupport quota lowerInitialLosses :
      SequenceReductionProblem (Finset Sequence) → ℕ)
    (hall :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          sequence ∈ allSequences problem)
    (hquota_pos :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        0 < quota problem)
    (hseat :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          winCount problem sequence ≤ seats problem)
    (hwinCount_eq :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          winCount problem sequence = (orderedWinners problem sequence).length)
    (hassignedBudget_le :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          ((orderedWinners problem sequence).map
            (assignedBudget problem sequence)).sum ≤ problem.budget)
    (hsupport_le :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          predictWinsSupport (voters problem) (ballots problem)
              (candidates problem) (orderedWinners problem sequence) ≤
            predictedWinSupport problem)
    (hquota :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          predictWinsSupportBudgetAccumulatorQuota
            (voters problem) (ballots problem) (candidates problem)
            (assignedBudget problem sequence) (quota problem)
            (orderedWinners problem sequence))
    (hloss_floor :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          lowerInitialLosses problem ≤ initialLossCount problem sequence)
    (algorithm_eq :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        algorithm problem =
          boundedSequenceFamily (allSequences problem)
            (winCount problem) (initialLossCount problem)
            (sequenceReductionBoundsFromPredictions
              (seats problem) problem.budget (predictedWinSupport problem)
              (quota problem) (lowerInitialLosses problem)))
    (output_spec_of_cover :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        sequenceFamilyCovers (feasibleSequence problem) (algorithm problem) →
          problem.specification (algorithm problem))
    (operationCount_eq :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        operationCount problem =
          sequenceReductionOperationCount
            problem.uniqueBallotCount problem.candidateCount)
    (problem : SequenceReductionProblem (Finset Sequence)) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount ^ 2 := by
  have hcore :
      sequenceFamilyCovers (feasibleSequence problem)
          (boundedSequenceFamily (allSequences problem)
            (winCount problem) (initialLossCount problem)
            (sequenceReductionBoundsFromPredictions
              (seats problem) problem.budget (predictedWinSupport problem)
              (quota problem) (lowerInitialLosses problem))) ∧
        sequenceReductionOperationCount
            problem.uniqueBallotCount problem.candidateCount ≤
          problem.uniqueBallotCount * problem.candidateCount ^ 2 :=
    proposition3_4_boundedSequenceFamily_covers_and_quadraticRuntime_of_budgetedPredictWinsSupportAccumulator
      (voters := voters problem)
      (ballots := ballots problem)
      (candidates := candidates problem)
      (allSequences := allSequences problem)
      (feasibleSequence := feasibleSequence problem)
      (winCount := winCount problem)
      (initialLossCount := initialLossCount problem)
      (orderedWinners := orderedWinners problem)
      (assignedBudget := assignedBudget problem)
      (seats := seats problem)
      (budget := problem.budget)
      (predictedWinSupport := predictedWinSupport problem)
      (quota := quota problem)
      (lowerInitialLosses := lowerInitialLosses problem)
      problem.uniqueBallotCount problem.candidateCount
      (hall problem) (hquota_pos problem) (hseat problem)
      (hwinCount_eq problem) (hassignedBudget_le problem)
      (hsupport_le problem) (hquota problem) (hloss_floor problem)
  have hcover_algorithm :
      sequenceFamilyCovers (feasibleSequence problem) (algorithm problem) := by
    rw [algorithm_eq problem]
    exact hcore.1
  exact ⟨output_spec_of_cover problem hcover_algorithm, by
    rw [operationCount_eq problem]
    exact hcore.2⟩

/--
Proposition 3.4 direct Algorithm 7 route with both prediction loops exposed:
the budgeted Predict-Wins accumulator and concrete Predict-Losses prefix
witnesses imply the bounded-family specification and exact quadratic operation
bound.
-/
theorem proposition3_4_sequenceReduction_sound_and_quadratic_runtime_of_budgetedPredictWinsSupportAccumulator_and_predictLossesPrefixes
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {algorithm :
      SequenceReductionProblem (Finset Sequence) → Finset Sequence}
    {operationCount : SequenceReductionProblem (Finset Sequence) → ℕ}
    (voters : SequenceReductionProblem (Finset Sequence) → Finset Voter)
    (ballots :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        Voter → RCVBallot Candidate)
    (candidates :
      SequenceReductionProblem (Finset Sequence) → Finset Candidate)
    (allSequences :
      SequenceReductionProblem (Finset Sequence) → Finset Sequence)
    (feasibleSequence :
      SequenceReductionProblem (Finset Sequence) → Sequence → Prop)
    (winCount initialLossCount :
      SequenceReductionProblem (Finset Sequence) → Sequence → ℕ)
    (orderedWinners :
      SequenceReductionProblem (Finset Sequence) → Sequence → List Candidate)
    (assignedBudget :
      SequenceReductionProblem (Finset Sequence) → Sequence → Candidate → ℕ)
    (seats predictedWinSupport quota firstChoiceThreshold lowerInitialLosses :
      SequenceReductionProblem (Finset Sequence) → ℕ)
    (hall :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          sequence ∈ allSequences problem)
    (hquota_pos :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        0 < quota problem)
    (hseat :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          winCount problem sequence ≤ seats problem)
    (hwinCount_eq :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          winCount problem sequence = (orderedWinners problem sequence).length)
    (hassignedBudget_le :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          ((orderedWinners problem sequence).map
            (assignedBudget problem sequence)).sum ≤ problem.budget)
    (hsupport_le :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          predictWinsSupport (voters problem) (ballots problem)
              (candidates problem) (orderedWinners problem sequence) ≤
            predictedWinSupport problem)
    (hquota :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          predictWinsSupportBudgetAccumulatorQuota
            (voters problem) (ballots problem) (candidates problem)
            (assignedBudget problem sequence) (quota problem)
            (orderedWinners problem sequence))
    (hloss_prefix :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          PredictLossesInitialLossPrefixCertificate
            (voters problem) (ballots problem) (candidates problem)
            problem.budget (firstChoiceThreshold problem)
            (initialLossCount problem) (lowerInitialLosses problem)
            sequence)
    (algorithm_eq :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        algorithm problem =
          boundedSequenceFamily (allSequences problem)
            (winCount problem) (initialLossCount problem)
            (sequenceReductionBoundsFromPredictions
              (seats problem) problem.budget (predictedWinSupport problem)
              (quota problem) (lowerInitialLosses problem)))
    (output_spec_of_cover :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        sequenceFamilyCovers (feasibleSequence problem) (algorithm problem) →
          problem.specification (algorithm problem))
    (operationCount_eq :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        operationCount problem =
          sequenceReductionOperationCount
            problem.uniqueBallotCount problem.candidateCount)
    (problem : SequenceReductionProblem (Finset Sequence)) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount ^ 2 := by
  have hcore :
      sequenceFamilyCovers (feasibleSequence problem)
          (boundedSequenceFamily (allSequences problem)
            (winCount problem) (initialLossCount problem)
            (sequenceReductionBoundsFromPredictions
              (seats problem) problem.budget (predictedWinSupport problem)
              (quota problem) (lowerInitialLosses problem))) ∧
        sequenceReductionOperationCount
            problem.uniqueBallotCount problem.candidateCount ≤
          problem.uniqueBallotCount * problem.candidateCount ^ 2 :=
    proposition3_4_boundedSequenceFamily_covers_and_quadraticRuntime_of_budgetedPredictWinsSupportAccumulator_and_predictLossesPrefixes
      (voters := voters problem)
      (ballots := ballots problem)
      (candidates := candidates problem)
      (allSequences := allSequences problem)
      (feasibleSequence := feasibleSequence problem)
      (winCount := winCount problem)
      (initialLossCount := initialLossCount problem)
      (orderedWinners := orderedWinners problem)
      (assignedBudget := assignedBudget problem)
      (seats := seats problem)
      (budget := problem.budget)
      (predictedWinSupport := predictedWinSupport problem)
      (quota := quota problem)
      (firstChoiceThreshold := firstChoiceThreshold problem)
      (lowerInitialLosses := lowerInitialLosses problem)
      problem.uniqueBallotCount problem.candidateCount
      (hall problem) (hquota_pos problem) (hseat problem)
      (hwinCount_eq problem) (hassignedBudget_le problem)
      (hsupport_le problem) (hquota problem) (hloss_prefix problem)
  have hcover_algorithm :
      sequenceFamilyCovers (feasibleSequence problem) (algorithm problem) := by
    rw [algorithm_eq problem]
    exact hcore.1
  exact ⟨output_spec_of_cover problem hcover_algorithm, by
    rw [operationCount_eq problem]
    exact hcore.2⟩

/--
Proposition 3.4 direct Algorithm 7 route from prefix-form Predict-Wins facts:
the per-prefix budgeted quota condition is converted internally to the
recursive accumulator invariant, then combined with Predict-Losses prefix
witnesses.
-/
theorem proposition3_4_sequenceReduction_sound_and_quadratic_runtime_of_budgetedPredictWinsAtPrefixes_and_predictLossesPrefixes
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {algorithm :
      SequenceReductionProblem (Finset Sequence) → Finset Sequence}
    {operationCount : SequenceReductionProblem (Finset Sequence) → ℕ}
    (voters : SequenceReductionProblem (Finset Sequence) → Finset Voter)
    (ballots :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        Voter → RCVBallot Candidate)
    (candidates :
      SequenceReductionProblem (Finset Sequence) → Finset Candidate)
    (allSequences :
      SequenceReductionProblem (Finset Sequence) → Finset Sequence)
    (feasibleSequence :
      SequenceReductionProblem (Finset Sequence) → Sequence → Prop)
    (winCount initialLossCount :
      SequenceReductionProblem (Finset Sequence) → Sequence → ℕ)
    (orderedWinners :
      SequenceReductionProblem (Finset Sequence) → Sequence → List Candidate)
    (assignedBudget :
      SequenceReductionProblem (Finset Sequence) → Sequence → Candidate → ℕ)
    (seats predictedWinSupport quota firstChoiceThreshold lowerInitialLosses :
      SequenceReductionProblem (Finset Sequence) → ℕ)
    (hall :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          sequence ∈ allSequences problem)
    (hquota_pos :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        0 < quota problem)
    (hseat :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          winCount problem sequence ≤ seats problem)
    (hwinCount_eq :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          winCount problem sequence = (orderedWinners problem sequence).length)
    (hassignedBudget_le :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          ((orderedWinners problem sequence).map
            (assignedBudget problem sequence)).sum ≤ problem.budget)
    (hsupport_le :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          predictWinsSupport (voters problem) (ballots problem)
              (candidates problem) (orderedWinners problem sequence) ≤
            predictedWinSupport problem)
    (hquota_prefix :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          predictWinsSupportBudgetAccumulatorQuotaAtPrefixes
            (voters problem) (ballots problem) (candidates problem)
            (assignedBudget problem sequence) (quota problem)
            (orderedWinners problem sequence))
    (hloss_prefix :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          PredictLossesInitialLossPrefixCertificate
            (voters problem) (ballots problem) (candidates problem)
            problem.budget (firstChoiceThreshold problem)
            (initialLossCount problem) (lowerInitialLosses problem)
            sequence)
    (algorithm_eq :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        algorithm problem =
          boundedSequenceFamily (allSequences problem)
            (winCount problem) (initialLossCount problem)
            (sequenceReductionBoundsFromPredictions
              (seats problem) problem.budget (predictedWinSupport problem)
              (quota problem) (lowerInitialLosses problem)))
    (output_spec_of_cover :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        sequenceFamilyCovers (feasibleSequence problem) (algorithm problem) →
          problem.specification (algorithm problem))
    (operationCount_eq :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        operationCount problem =
          sequenceReductionOperationCount
            problem.uniqueBallotCount problem.candidateCount)
    (problem : SequenceReductionProblem (Finset Sequence)) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount ^ 2 := by
  exact
    proposition3_4_sequenceReduction_sound_and_quadratic_runtime_of_budgetedPredictWinsSupportAccumulator_and_predictLossesPrefixes
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winCount := winCount)
      (initialLossCount := initialLossCount)
      (orderedWinners := orderedWinners)
      (assignedBudget := assignedBudget)
      (seats := seats)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (lowerInitialLosses := lowerInitialLosses)
      hall hquota_pos hseat hwinCount_eq hassignedBudget_le hsupport_le
      (fun problem sequence hfeasible =>
        predictWinsSupportBudgetAccumulatorQuota_of_atPrefixes
          (hquota_prefix problem sequence hfeasible))
      hloss_prefix algorithm_eq output_spec_of_cover operationCount_eq problem

/--
Proposition 3.4 direct Algorithm 7 route from source-loop facts: concrete
Predict-Wins selections are checked by current-prefix ready-set membership,
and concrete Predict-Losses loop prefixes are checked as initial loss
witnesses before feeding the existing sequence-reduction specification route.
-/
theorem proposition3_4_sequenceReduction_sound_and_quadratic_runtime_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {algorithm :
      SequenceReductionProblem (Finset Sequence) → Finset Sequence}
    {operationCount : SequenceReductionProblem (Finset Sequence) → ℕ}
    (voters : SequenceReductionProblem (Finset Sequence) → Finset Voter)
    (ballots :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        Voter → RCVBallot Candidate)
    (candidates :
      SequenceReductionProblem (Finset Sequence) → Finset Candidate)
    (allSequences :
      SequenceReductionProblem (Finset Sequence) → Finset Sequence)
    (feasibleSequence :
      SequenceReductionProblem (Finset Sequence) → Sequence → Prop)
    (winCount initialLossCount :
      SequenceReductionProblem (Finset Sequence) → Sequence → ℕ)
    (orderedWinners lossPrefix :
      SequenceReductionProblem (Finset Sequence) → Sequence → List Candidate)
    (assignedBudget :
      SequenceReductionProblem (Finset Sequence) → Sequence → Candidate → ℕ)
    (seats predictedWinSupport quota firstChoiceThreshold lowerInitialLosses :
      SequenceReductionProblem (Finset Sequence) → ℕ)
    (hall :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          sequence ∈ allSequences problem)
    (hquota_pos :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        0 < quota problem)
    (hseat :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          winCount problem sequence ≤ seats problem)
    (hwinCount_eq :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          winCount problem sequence = (orderedWinners problem sequence).length)
    (hassignedBudget_le :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          ((orderedWinners problem sequence).map
            (assignedBudget problem sequence)).sum ≤ problem.budget)
    (hsupport_le :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          predictWinsSupport (voters problem) (ballots problem)
              (candidates problem) (orderedWinners problem sequence) ≤
            predictedWinSupport problem)
    (hselected :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          ∀ pref candidate suffix,
            orderedWinners problem sequence = pref ++ candidate :: suffix →
              candidate ∈
                predictWinsBudgetReadyCandidatesAtPrefix
                  (voters problem) (ballots problem) (candidates problem)
                  (assignedBudget problem sequence) (quota problem) pref)
    (hloss_loop :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          PredictLossesLoopPrefix
            (voters problem) (ballots problem) (candidates problem)
            problem.budget (firstChoiceThreshold problem)
            (lossPrefix problem sequence))
    (hlower :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          lowerInitialLosses problem ≤
            (lossPrefix problem sequence).length)
    (hinitial :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        ∀ sequence, feasibleSequence problem sequence →
          (lossPrefix problem sequence).length ≤
            initialLossCount problem sequence)
    (algorithm_eq :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        algorithm problem =
          boundedSequenceFamily (allSequences problem)
            (winCount problem) (initialLossCount problem)
            (sequenceReductionBoundsFromPredictions
              (seats problem) problem.budget (predictedWinSupport problem)
              (quota problem) (lowerInitialLosses problem)))
    (output_spec_of_cover :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        sequenceFamilyCovers (feasibleSequence problem) (algorithm problem) →
          problem.specification (algorithm problem))
    (operationCount_eq :
      ∀ problem : SequenceReductionProblem (Finset Sequence),
        operationCount problem =
          sequenceReductionOperationCount
            problem.uniqueBallotCount problem.candidateCount)
    (problem : SequenceReductionProblem (Finset Sequence)) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount ^ 2 := by
  have hcore :
      sequenceFamilyCovers (feasibleSequence problem)
          (boundedSequenceFamily (allSequences problem)
            (winCount problem) (initialLossCount problem)
            (sequenceReductionBoundsFromPredictions
              (seats problem) problem.budget (predictedWinSupport problem)
              (quota problem) (lowerInitialLosses problem))) ∧
        sequenceReductionOperationCount
            problem.uniqueBallotCount problem.candidateCount ≤
          problem.uniqueBallotCount * problem.candidateCount ^ 2 :=
    proposition3_4_boundedSequenceFamily_covers_and_quadraticRuntime_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes
      (voters := voters problem)
      (ballots := ballots problem)
      (candidates := candidates problem)
      (allSequences := allSequences problem)
      (feasibleSequence := feasibleSequence problem)
      (winCount := winCount problem)
      (initialLossCount := initialLossCount problem)
      (orderedWinners := orderedWinners problem)
      (lossPrefix := lossPrefix problem)
      (assignedBudget := assignedBudget problem)
      (seats := seats problem)
      (budget := problem.budget)
      (predictedWinSupport := predictedWinSupport problem)
      (quota := quota problem)
      (firstChoiceThreshold := firstChoiceThreshold problem)
      (lowerInitialLosses := lowerInitialLosses problem)
      problem.uniqueBallotCount problem.candidateCount
      (hall problem) (hquota_pos problem) (hseat problem)
      (hwinCount_eq problem) (hassignedBudget_le problem)
      (hsupport_le problem) (hselected problem) (hloss_loop problem)
      (hlower problem) (hinitial problem)
  have hcover_algorithm :
      sequenceFamilyCovers (feasibleSequence problem) (algorithm problem) := by
    rw [algorithm_eq problem]
    exact hcore.1
  exact ⟨output_spec_of_cover problem hcover_algorithm, by
    rw [operationCount_eq problem]
    exact hcore.2⟩

/--
Proposition 3.4 direct Algorithm 7 route for concrete RCV win/loss
sequences: Predict-Wins selections are checked by current-prefix ready-set
membership, and the Predict-Losses loop prefix is checked by a concrete
initial losing-label prefix in the source sequence.
-/
theorem proposition3_4_sequenceReduction_sound_and_quadratic_runtime_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes_rcvSequence
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      SequenceReductionProblem (Finset RCVSequence) → Finset RCVSequence}
    {operationCount : SequenceReductionProblem (Finset RCVSequence) → ℕ}
    (voters : SequenceReductionProblem (Finset RCVSequence) → Finset Voter)
    (ballots :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        Voter → RCVBallot Candidate)
    (candidates :
      SequenceReductionProblem (Finset RCVSequence) → Finset Candidate)
    (allSequences :
      SequenceReductionProblem (Finset RCVSequence) → Finset RCVSequence)
    (feasibleSequence :
      SequenceReductionProblem (Finset RCVSequence) → RCVSequence → Prop)
    (orderedWinners lossPrefix :
      SequenceReductionProblem (Finset RCVSequence) →
        RCVSequence → List Candidate)
    (assignedBudget :
      SequenceReductionProblem (Finset RCVSequence) →
        RCVSequence → Candidate → ℕ)
    (seats predictedWinSupport quota firstChoiceThreshold lowerInitialLosses :
      SequenceReductionProblem (Finset RCVSequence) → ℕ)
    (hall :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        ∀ sequence, feasibleSequence problem sequence →
          sequence ∈ allSequences problem)
    (hquota_pos :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        0 < quota problem)
    (hseat :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        ∀ sequence, feasibleSequence problem sequence →
          rcvSequenceWinCount sequence ≤ seats problem)
    (hwinCount_eq :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        ∀ sequence, feasibleSequence problem sequence →
          rcvSequenceWinCount sequence =
            (orderedWinners problem sequence).length)
    (hassignedBudget_le :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        ∀ sequence, feasibleSequence problem sequence →
          ((orderedWinners problem sequence).map
            (assignedBudget problem sequence)).sum ≤ problem.budget)
    (hsupport_le :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        ∀ sequence, feasibleSequence problem sequence →
          predictWinsSupport (voters problem) (ballots problem)
              (candidates problem) (orderedWinners problem sequence) ≤
            predictedWinSupport problem)
    (hselected :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        ∀ sequence, feasibleSequence problem sequence →
          ∀ pref candidate suffix,
            orderedWinners problem sequence = pref ++ candidate :: suffix →
              candidate ∈
                predictWinsBudgetReadyCandidatesAtPrefix
                  (voters problem) (ballots problem) (candidates problem)
                  (assignedBudget problem sequence) (quota problem) pref)
    (hloss_loop :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        ∀ sequence, feasibleSequence problem sequence →
          PredictLossesLoopPrefix
            (voters problem) (ballots problem) (candidates problem)
            problem.budget (firstChoiceThreshold problem)
            (lossPrefix problem sequence))
    (hlower :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        ∀ sequence, feasibleSequence problem sequence →
          lowerInitialLosses problem ≤
            (lossPrefix problem sequence).length)
    (hinitial_prefix :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        ∀ sequence, feasibleSequence problem sequence →
          rcvSequenceHasInitialLossPrefix sequence
            (lossPrefix problem sequence).length)
    (algorithm_eq :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        algorithm problem =
          boundedSequenceFamily (allSequences problem)
            rcvSequenceWinCount rcvSequenceInitialLossCount
            (sequenceReductionBoundsFromPredictions
              (seats problem) problem.budget (predictedWinSupport problem)
              (quota problem) (lowerInitialLosses problem)))
    (output_spec_of_cover :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        sequenceFamilyCovers (feasibleSequence problem) (algorithm problem) →
          problem.specification (algorithm problem))
    (operationCount_eq :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        operationCount problem =
          sequenceReductionOperationCount
            problem.uniqueBallotCount problem.candidateCount)
    (problem : SequenceReductionProblem (Finset RCVSequence)) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount ^ 2 := by
  exact
    proposition3_4_sequenceReduction_sound_and_quadratic_runtime_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winCount := fun _problem => rcvSequenceWinCount)
      (initialLossCount := fun _problem => rcvSequenceInitialLossCount)
      (orderedWinners := orderedWinners)
      (lossPrefix := lossPrefix)
      (assignedBudget := assignedBudget)
      (seats := seats)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (lowerInitialLosses := lowerInitialLosses)
      hall hquota_pos hseat hwinCount_eq hassignedBudget_le hsupport_le
      hselected hloss_loop hlower
      (fun problem sequence hfeasible =>
        lossPrefix_length_le_rcvSequenceInitialLossCount_of_initialLossPrefix
          (hinitial_prefix problem sequence hfeasible))
      algorithm_eq output_spec_of_cover operationCount_eq problem

/--
Proposition 3.4 Algorithm 7 route for concrete RCV traces: Predict-Wins and
Predict-Losses still use the source loop facts, while the initial-loss prefix
is discharged by the trace's initial elimination steps and the sequence read
from that trace.
-/
theorem proposition3_4_sequenceReduction_sound_and_quadratic_runtime_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes_rcvTrace
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {algorithm :
      SequenceReductionProblem (Finset RCVSequence) → Finset RCVSequence}
    {operationCount : SequenceReductionProblem (Finset RCVSequence) → ℕ}
    (voters : SequenceReductionProblem (Finset RCVSequence) → Finset Voter)
    (ballots :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        Voter → RCVBallot Candidate)
    (candidates :
      SequenceReductionProblem (Finset RCVSequence) → Finset Candidate)
    (allSequences :
      SequenceReductionProblem (Finset RCVSequence) → Finset RCVSequence)
    (feasibleSequence :
      SequenceReductionProblem (Finset RCVSequence) → RCVSequence → Prop)
    (orderedWinners lossPrefix :
      SequenceReductionProblem (Finset RCVSequence) →
        RCVSequence → List Candidate)
    (assignedBudget :
      SequenceReductionProblem (Finset RCVSequence) →
        RCVSequence → Candidate → ℕ)
    (traceOf :
      SequenceReductionProblem (Finset RCVSequence) →
        RCVSequence → RCVTrace Candidate)
    (seats predictedWinSupport quota firstChoiceThreshold lowerInitialLosses :
      SequenceReductionProblem (Finset RCVSequence) → ℕ)
    (hall :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        ∀ sequence, feasibleSequence problem sequence →
          sequence ∈ allSequences problem)
    (hquota_pos :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        0 < quota problem)
    (hseat :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        ∀ sequence, feasibleSequence problem sequence →
          rcvSequenceWinCount sequence ≤ seats problem)
    (hwinCount_eq :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        ∀ sequence, feasibleSequence problem sequence →
          rcvSequenceWinCount sequence =
            (orderedWinners problem sequence).length)
    (hassignedBudget_le :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        ∀ sequence, feasibleSequence problem sequence →
          ((orderedWinners problem sequence).map
            (assignedBudget problem sequence)).sum ≤ problem.budget)
    (hsupport_le :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        ∀ sequence, feasibleSequence problem sequence →
          predictWinsSupport (voters problem) (ballots problem)
              (candidates problem) (orderedWinners problem sequence) ≤
            predictedWinSupport problem)
    (hselected :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        ∀ sequence, feasibleSequence problem sequence →
          ∀ pref candidate suffix,
            orderedWinners problem sequence = pref ++ candidate :: suffix →
              candidate ∈
                predictWinsBudgetReadyCandidatesAtPrefix
                  (voters problem) (ballots problem) (candidates problem)
                  (assignedBudget problem sequence) (quota problem) pref)
    (hloss_loop :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        ∀ sequence, feasibleSequence problem sequence →
          PredictLossesLoopPrefix
            (voters problem) (ballots problem) (candidates problem)
            problem.budget (firstChoiceThreshold problem)
            (lossPrefix problem sequence))
    (hlower :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        ∀ sequence, feasibleSequence problem sequence →
          lowerInitialLosses problem ≤
            (lossPrefix problem sequence).length)
    (hsequence_eq :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        ∀ sequence, feasibleSequence problem sequence →
          sequence = rcvSequenceFromTrace (traceOf problem sequence))
    (htrace_prefix :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        ∀ sequence, feasibleSequence problem sequence →
          (traceOf problem sequence).HasInitialEliminationPrefix
            (lossPrefix problem sequence).length)
    (algorithm_eq :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        algorithm problem =
          boundedSequenceFamily (allSequences problem)
            rcvSequenceWinCount rcvSequenceInitialLossCount
            (sequenceReductionBoundsFromPredictions
              (seats problem) problem.budget (predictedWinSupport problem)
              (quota problem) (lowerInitialLosses problem)))
    (output_spec_of_cover :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        sequenceFamilyCovers (feasibleSequence problem) (algorithm problem) →
          problem.specification (algorithm problem))
    (operationCount_eq :
      ∀ problem : SequenceReductionProblem (Finset RCVSequence),
        operationCount problem =
          sequenceReductionOperationCount
            problem.uniqueBallotCount problem.candidateCount)
    (problem : SequenceReductionProblem (Finset RCVSequence)) :
    problem.specification (algorithm problem) ∧
      operationCount problem ≤
        problem.uniqueBallotCount * problem.candidateCount ^ 2 := by
  exact
    proposition3_4_sequenceReduction_sound_and_quadratic_runtime_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes_rcvSequence
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (orderedWinners := orderedWinners)
      (lossPrefix := lossPrefix)
      (assignedBudget := assignedBudget)
      (seats := seats)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (lowerInitialLosses := lowerInitialLosses)
      hall hquota_pos hseat hwinCount_eq hassignedBudget_le hsupport_le
      hselected hloss_loop hlower
      (fun problem sequence hfeasible =>
        rcvSequenceHasInitialLossPrefix_of_trace_initialEliminationPrefix
          (hsequence_eq problem sequence hfeasible)
          (htrace_prefix problem sequence hfeasible))
      algorithm_eq output_spec_of_cover operationCount_eq problem

/--
Concrete Proposition 3.4 Algorithm 7 implementation route from source
inequalities and indexed trace-step facts. This removes the generic
implementation/specification adapter from the trace-step route: the algorithm is
the bounded-family filter itself, the specification is concrete coverage, and
the operation count is the exact Algorithm 7 model.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceInequalities_and_traceSteps
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {orderedWinners lossPrefix : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (orderedWinners sequence).length)
    (hassignedBudget_le :
      ∀ sequence, feasibleSequence sequence →
        ((orderedWinners sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (orderedWinners sequence) ≤
          predictedWinSupport)
    (hselected_candidate :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          orderedWinners sequence = pref ++ candidate :: suffix →
            candidate ∈ candidates)
    (hselected_quota :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          orderedWinners sequence = pref ++ candidate :: suffix →
            quota ≤ assignedBudget sequence candidate +
              strictSupportCount voters ballots candidates
                (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref)
                candidate)
    (hloss_nodup :
      ∀ sequence, feasibleSequence sequence →
        (lossPrefix sequence).Nodup)
    (hloss_candidate :
      ∀ sequence, feasibleSequence sequence →
        ∀ candidate, candidate ∈ lossPrefix sequence →
          candidate ∈ candidates)
    (hloss_support_lt :
      ∀ sequence, feasibleSequence sequence →
        ∀ candidate, candidate ∈ lossPrefix sequence →
          budget +
            strictSupportCount voters ballots candidates
              (∅ : Finset Candidate) candidate <
            firstChoiceThreshold)
    (hlower :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ (lossPrefix sequence).length)
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        (lossPrefix sequence).length ≤ (traceOf sequence).steps.length)
    (htrace_focus_get :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin (lossPrefix sequence).length,
          ((traceOf sequence).steps.get
            ⟨i.1, Nat.lt_of_lt_of_le i.2
              (htrace_prefix_len sequence hfeasible)⟩).focus =
            some ((lossPrefix sequence).get i))
    (htrace_kind_get :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin (lossPrefix sequence).length,
          ((traceOf sequence).steps.get
            ⟨i.1, Nat.lt_of_lt_of_le i.2
              (htrace_prefix_len sequence hfeasible)⟩).kind =
            StepKind.eliminate) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota lowerInitialLosses
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  have hcore :
      sequenceFamilyCovers feasibleSequence
          (boundedSequenceFamily allSequences rcvSequenceWinCount
            rcvSequenceInitialLossCount
            (sequenceReductionBoundsFromPredictions seats budget
              predictedWinSupport quota lowerInitialLosses)) ∧
        sequenceReductionOperationCount uniqueBallotCount candidateCount ≤
          uniqueBallotCount * candidateCount ^ 2 :=
    proposition3_4_boundedSequenceFamily_covers_and_quadraticRuntime_of_budgetReadyPredictWinsSelections_and_predictLossesLoopPrefixes_rcvTrace
      (traceOf := traceOf)
      uniqueBallotCount candidateCount hall hquota_pos hseat hwinCount_eq
      hassignedBudget_le hsupport_le
      (fun sequence hfeasible =>
        predictWinsBudgetReadySelections_of_sourceInequalities
          (hcandidate := hselected_candidate sequence hfeasible)
          (hquota := hselected_quota sequence hfeasible))
      (fun sequence hfeasible =>
        predictLossesLoopPrefix_of_sourceInequalities
          (hnodup := hloss_nodup sequence hfeasible)
          (hcandidate := hloss_candidate sequence hfeasible)
          (hsupport_lt := hloss_support_lt sequence hfeasible))
      hlower hsequence_eq
      (fun sequence hfeasible =>
        STVTrace.hasInitialEliminationPrefix_of_initialEliminationFocusPrefix
          (rcvTraceHasInitialEliminationFocusPrefix_of_getElem
            (htrace_prefix_len sequence hfeasible)
            (htrace_focus_get sequence hfeasible)
            (htrace_kind_get sequence hfeasible)))
  exact hcore

/--
Concrete Proposition 3.4 Algorithm 7 route with no arbitrary coverage-to-spec
bridge. For the concrete source problem whose specification is coverage of all
feasible sequences, the budgeted Predict-Wins accumulator and Predict-Losses
prefix witnesses prove coverage of the bounded sequence family and exact
quadratic runtime.
-/
theorem proposition3_4_concreteCoverageProblem_sound_and_quadratic_runtime_of_budgetedPredictWinsSupportAccumulator_and_predictLossesPrefixes
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset Sequence}
    {feasibleSequence : Sequence → Prop}
    {winCount initialLossCount : Sequence → ℕ}
    {orderedWinners : Sequence → List Candidate}
    {assignedBudget : Sequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence → winCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        winCount sequence = (orderedWinners sequence).length)
    (hassignedBudget_le :
      ∀ sequence, feasibleSequence sequence →
        ((orderedWinners sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (orderedWinners sequence) ≤
          predictedWinSupport)
    (hquota :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupportBudgetAccumulatorQuota voters ballots candidates
          (assignedBudget sequence) quota (orderedWinners sequence))
    (hloss_prefix :
      ∀ sequence, feasibleSequence sequence →
        PredictLossesInitialLossPrefixCertificate voters ballots candidates
          budget firstChoiceThreshold initialLossCount lowerInitialLosses
          sequence) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (boundedSequenceFamily allSequences winCount initialLossCount
        (sequenceReductionBoundsFromPredictions
          seats budget predictedWinSupport quota lowerInitialLosses)) ∧
      sequenceReductionOperationCount uniqueBallotCount candidateCount ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    proposition3_4_boundedSequenceFamily_covers_and_quadraticRuntime_of_budgetedPredictWinsSupportAccumulator_and_predictLossesPrefixes
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winCount := winCount)
      (initialLossCount := initialLossCount)
      (orderedWinners := orderedWinners)
      (assignedBudget := assignedBudget)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (lowerInitialLosses := lowerInitialLosses)
      uniqueBallotCount candidateCount hall hquota_pos hseat hwinCount_eq
      hassignedBudget_le hsupport_le hquota hloss_prefix

/--
Concrete Proposition 3.4 Algorithm 7 route for an implementation: if the
implementation returns the bounded sequence family on the concrete coverage
problem, then the budgeted Predict-Wins accumulator and Predict-Losses prefix
witnesses prove the concrete coverage specification and exact quadratic
runtime.  This removes the arbitrary coverage-to-specification premise from
the implementation-shaped theorem.
-/
theorem proposition3_4_concreteCoverageAlgorithm_sound_and_quadratic_runtime_of_budgetedPredictWinsSupportAccumulator_and_predictLossesPrefixes
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {algorithm :
      SequenceReductionProblem (Finset Sequence) → Finset Sequence}
    {operationCount : SequenceReductionProblem (Finset Sequence) → ℕ}
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset Sequence}
    {feasibleSequence : Sequence → Prop}
    {winCount initialLossCount : Sequence → ℕ}
    {orderedWinners : Sequence → List Candidate}
    {assignedBudget : Sequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence → winCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        winCount sequence = (orderedWinners sequence).length)
    (hassignedBudget_le :
      ∀ sequence, feasibleSequence sequence →
        ((orderedWinners sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (orderedWinners sequence) ≤
          predictedWinSupport)
    (hquota :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupportBudgetAccumulatorQuota voters ballots candidates
          (assignedBudget sequence) quota (orderedWinners sequence))
    (hloss_prefix :
      ∀ sequence, feasibleSequence sequence →
        PredictLossesInitialLossPrefixCertificate voters ballots candidates
          budget firstChoiceThreshold initialLossCount lowerInitialLosses
          sequence)
    (algorithm_eq :
      algorithm
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) =
        boundedSequenceFamily allSequences winCount initialLossCount
          (sequenceReductionBoundsFromPredictions
            seats budget predictedWinSupport quota lowerInitialLosses))
    (operationCount_eq :
      operationCount
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) =
        sequenceReductionOperationCount uniqueBallotCount candidateCount) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (algorithm
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      operationCount
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  have hcore :
      (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount).specification
        (boundedSequenceFamily allSequences winCount initialLossCount
          (sequenceReductionBoundsFromPredictions
            seats budget predictedWinSupport quota lowerInitialLosses)) ∧
        sequenceReductionOperationCount uniqueBallotCount candidateCount ≤
          uniqueBallotCount * candidateCount ^ 2 :=
    proposition3_4_concreteCoverageProblem_sound_and_quadratic_runtime_of_budgetedPredictWinsSupportAccumulator_and_predictLossesPrefixes
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winCount := winCount)
      (initialLossCount := initialLossCount)
      (orderedWinners := orderedWinners)
      (assignedBudget := assignedBudget)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (lowerInitialLosses := lowerInitialLosses)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwinCount_eq hassignedBudget_le hsupport_le
      hquota hloss_prefix
  exact ⟨by
    rw [algorithm_eq]
    exact hcore.1, by
    rw [operationCount_eq]
    exact hcore.2⟩

/--
Concrete Proposition 3.4 Algorithm 7 implementation: the source implementation
is the bounded-family filter itself, so the implementation-equality premises
discharge by definition.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_budgetedPredictWinsSupportAccumulator_and_predictLossesPrefixes
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset Sequence}
    {feasibleSequence : Sequence → Prop}
    {winCount initialLossCount : Sequence → ℕ}
    {orderedWinners : Sequence → List Candidate}
    {assignedBudget : Sequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence → winCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        winCount sequence = (orderedWinners sequence).length)
    (hassignedBudget_le :
      ∀ sequence, feasibleSequence sequence →
        ((orderedWinners sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (orderedWinners sequence) ≤
          predictedWinSupport)
    (hquota :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupportBudgetAccumulatorQuota voters ballots candidates
          (assignedBudget sequence) quota (orderedWinners sequence))
    (hloss_prefix :
      ∀ sequence, feasibleSequence sequence →
        PredictLossesInitialLossPrefixCertificate voters ballots candidates
          budget firstChoiceThreshold initialLossCount lowerInitialLosses
          sequence) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm
        allSequences winCount initialLossCount seats predictedWinSupport quota
        lowerInitialLosses
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    proposition3_4_concreteCoverageAlgorithm_sound_and_quadratic_runtime_of_budgetedPredictWinsSupportAccumulator_and_predictLossesPrefixes
      (algorithm :=
        sequenceReductionConcreteCoverageAlgorithm
          allSequences winCount initialLossCount seats predictedWinSupport
          quota lowerInitialLosses)
      (operationCount :=
        sequenceReductionConcreteCoverageOperationCount
          (Sequence := Sequence))
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winCount := winCount)
      (initialLossCount := initialLossCount)
      (orderedWinners := orderedWinners)
      (assignedBudget := assignedBudget)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (lowerInitialLosses := lowerInitialLosses)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwinCount_eq hassignedBudget_le hsupport_le
      hquota hloss_prefix
      rfl rfl

/--
Concrete Proposition 3.4 Algorithm 7 source-order implementation: Predict-Wins
is the executable current-prefix ready traversal, Predict-Losses is the
executable source-order filter, and indexed trace facts show that the returned
loss prefix is an initial run of eliminations. The conclusion is the concrete
coverage problem, so there is no arbitrary coverage-to-specification adapter.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceOrderLoops_and_traceSteps
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder lossSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence =
          (predictWinsLoopFromSourceOrder voters ballots candidates
            (assignedBudget sequence) quota
            (winnerSourceOrder sequence)).length)
    (hassignedBudget_le :
      ∀ sequence, feasibleSequence sequence →
        ((predictWinsLoopFromSourceOrder voters ballots candidates
            (assignedBudget sequence) quota
            (winnerSourceOrder sequence)).map
          (assignedBudget sequence)).sum ≤ budget)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (predictWinsLoopFromSourceOrder voters ballots candidates
              (assignedBudget sequence) quota
              (winnerSourceOrder sequence)) ≤
          predictedWinSupport)
    (hloss_source_nodup :
      ∀ sequence, feasibleSequence sequence →
        (lossSourceOrder sequence).Nodup)
    (hlower :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          (predictLossesLoopFromSourceOrder voters ballots candidates budget
            firstChoiceThreshold (lossSourceOrder sequence)).length)
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        (predictLossesLoopFromSourceOrder voters ballots candidates budget
            firstChoiceThreshold (lossSourceOrder sequence)).length ≤
          (traceOf sequence).steps.length)
    (htrace_focus_get :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin
          (predictLossesLoopFromSourceOrder voters ballots candidates budget
            firstChoiceThreshold (lossSourceOrder sequence)).length,
          ((traceOf sequence).steps.get
            ⟨i.1, Nat.lt_of_lt_of_le i.2
              (htrace_prefix_len sequence hfeasible)⟩).focus =
            some ((predictLossesLoopFromSourceOrder voters ballots candidates
              budget firstChoiceThreshold (lossSourceOrder sequence)).get i))
    (htrace_kind_get :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin
          (predictLossesLoopFromSourceOrder voters ballots candidates budget
            firstChoiceThreshold (lossSourceOrder sequence)).length,
          ((traceOf sequence).steps.get
            ⟨i.1, Nat.lt_of_lt_of_le i.2
              (htrace_prefix_len sequence hfeasible)⟩).kind =
            StepKind.eliminate) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota lowerInitialLosses
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_budgetedPredictWinsSupportAccumulator_and_predictLossesPrefixes
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winCount := rcvSequenceWinCount)
      (initialLossCount := rcvSequenceInitialLossCount)
      (orderedWinners := fun sequence =>
        predictWinsLoopFromSourceOrder voters ballots candidates
          (assignedBudget sequence) quota (winnerSourceOrder sequence))
      (assignedBudget := assignedBudget)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (lowerInitialLosses := lowerInitialLosses)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwinCount_eq hassignedBudget_le hsupport_le
      (fun sequence _hfeasible =>
        predictWinsSupportBudgetAccumulatorQuota_of_atPrefixes
          (predictWinsSupportBudgetAccumulatorQuotaAtPrefixes_of_budgetReadySelectionLoop
            (predictWinsLoopFromSourceOrder_spec voters ballots candidates
              (assignedBudget sequence) quota (winnerSourceOrder sequence))))
      (fun sequence hfeasible =>
        predictLossesInitialLossPrefixCertificate_of_loopPrefix_and_traceGetElem
          (hloop :=
            predictLossesLoopPrefix_of_sourceOrder_filter
              (voters := voters) (ballots := ballots)
              (candidates := candidates) (budget := budget)
              (firstChoiceThreshold := firstChoiceThreshold)
              (sourceOrder := lossSourceOrder sequence)
              (hloss_source_nodup sequence hfeasible))
          (hlower := hlower sequence hfeasible)
          (hsequence := hsequence_eq sequence hfeasible)
          (hlen := htrace_prefix_len sequence hfeasible)
          (hfocus := htrace_focus_get sequence hfeasible)
          (hkind := htrace_kind_get sequence hfeasible))

/--
Concrete Proposition 3.4 Algorithm 7 source-order implementation with the
Predict-Losses lower bound computed by the source transfer loop. The source
order is the sorted definitely-losing list `C_L`; the transfer list is keyed to
the same order.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceOrderLoops_transferBound_and_traceSteps
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder lossSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {lossTransfers : RCVSequence → List ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence =
          (predictWinsLoopFromSourceOrder voters ballots candidates
            (assignedBudget sequence) quota
            (winnerSourceOrder sequence)).length)
    (hassignedBudget_le :
      ∀ sequence, feasibleSequence sequence →
        ((predictWinsLoopFromSourceOrder voters ballots candidates
            (assignedBudget sequence) quota
            (winnerSourceOrder sequence)).map
          (assignedBudget sequence)).sum ≤ budget)
    (hsupport_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (predictWinsLoopFromSourceOrder voters ballots candidates
              (assignedBudget sequence) quota
              (winnerSourceOrder sequence)) ≤
          predictedWinSupport)
    (hloss_source_nodup :
      ∀ sequence, feasibleSequence sequence →
        (lossSourceOrder sequence).Nodup)
    (hloss_source_mem :
      ∀ sequence, feasibleSequence sequence →
        ∀ candidate, candidate ∈ lossSourceOrder sequence →
          candidate ∈
            predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold)
    (htransfer_length :
      ∀ sequence, feasibleSequence sequence →
        (lossTransfers sequence).length = (lossSourceOrder sequence).length)
    (hlower_transfer :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          predictLossesTransferInitialLossBound topFirstChoice quota
            (lossTransfers sequence))
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        (predictLossesLoopFromSourceOrder voters ballots candidates budget
            firstChoiceThreshold (lossSourceOrder sequence)).length ≤
          (traceOf sequence).steps.length)
    (htrace_focus_get :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin
          (predictLossesLoopFromSourceOrder voters ballots candidates budget
            firstChoiceThreshold (lossSourceOrder sequence)).length,
          ((traceOf sequence).steps.get
            ⟨i.1, Nat.lt_of_lt_of_le i.2
              (htrace_prefix_len sequence hfeasible)⟩).focus =
            some ((predictLossesLoopFromSourceOrder voters ballots candidates
              budget firstChoiceThreshold (lossSourceOrder sequence)).get i))
    (htrace_kind_get :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin
          (predictLossesLoopFromSourceOrder voters ballots candidates budget
            firstChoiceThreshold (lossSourceOrder sequence)).length,
          ((traceOf sequence).steps.get
            ⟨i.1, Nat.lt_of_lt_of_le i.2
              (htrace_prefix_len sequence hfeasible)⟩).kind =
            StepKind.eliminate) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota lowerInitialLosses
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceOrderLoops_and_traceSteps
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (lossSourceOrder := lossSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (lowerInitialLosses := lowerInitialLosses)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwinCount_eq hassignedBudget_le hsupport_le
      hloss_source_nodup
      (fun sequence hfeasible =>
        le_trans (hlower_transfer sequence hfeasible)
          (predictLossesTransferInitialLossBound_le_loop_length_of_forall_mem
            (voters := voters) (ballots := ballots)
            (candidates := candidates) (budget := budget)
            (firstChoiceThreshold := firstChoiceThreshold)
            (sourceOrder := lossSourceOrder sequence)
            (topFirstChoice := topFirstChoice) (quota := quota)
            (transfers := lossTransfers sequence)
            (htransfer_length sequence hfeasible)
            (hloss_source_mem sequence hfeasible)))
      hsequence_eq htrace_prefix_len htrace_focus_get htrace_kind_get

/--
Concrete Proposition 3.4 Algorithm 7 source-order implementation where the
Predict-Wins source order is already ready at each processed-prefix state. This
matches the TeX convention that the implementation scans the ordered `C_W`
list: the executable loop is only a checked rendering of that scan, so its
output facts can be rewritten to facts about the source order itself.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceOrders_ready_transferBound_and_traceSteps
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder lossSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {lossTransfers : RCVSequence → List ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwin_ready :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈
              predictWinsBudgetReadyCandidatesAtPrefix voters ballots
                candidates (assignedBudget sequence) quota pref)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hloss_source_nodup :
      ∀ sequence, feasibleSequence sequence →
        (lossSourceOrder sequence).Nodup)
    (hloss_source_mem :
      ∀ sequence, feasibleSequence sequence →
        ∀ candidate, candidate ∈ lossSourceOrder sequence →
          candidate ∈
            predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold)
    (htransfer_length :
      ∀ sequence, feasibleSequence sequence →
        (lossTransfers sequence).length = (lossSourceOrder sequence).length)
    (hlower_transfer :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          predictLossesTransferInitialLossBound topFirstChoice quota
            (lossTransfers sequence))
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        (predictLossesLoopFromSourceOrder voters ballots candidates budget
            firstChoiceThreshold (lossSourceOrder sequence)).length ≤
          (traceOf sequence).steps.length)
    (htrace_focus_get :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin
          (predictLossesLoopFromSourceOrder voters ballots candidates budget
            firstChoiceThreshold (lossSourceOrder sequence)).length,
          ((traceOf sequence).steps.get
            ⟨i.1, Nat.lt_of_lt_of_le i.2
              (htrace_prefix_len sequence hfeasible)⟩).focus =
            some ((predictLossesLoopFromSourceOrder voters ballots candidates
              budget firstChoiceThreshold (lossSourceOrder sequence)).get i))
    (htrace_kind_get :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin
          (predictLossesLoopFromSourceOrder voters ballots candidates budget
            firstChoiceThreshold (lossSourceOrder sequence)).length,
          ((traceOf sequence).steps.get
            ⟨i.1, Nat.lt_of_lt_of_le i.2
              (htrace_prefix_len sequence hfeasible)⟩).kind =
            StepKind.eliminate) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota lowerInitialLosses
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceOrderLoops_transferBound_and_traceSteps
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (lossSourceOrder := lossSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (lossTransfers := lossTransfers)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (lowerInitialLosses := lowerInitialLosses)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat
      (fun sequence hfeasible => by
        have hloop_eq :
            predictWinsLoopFromSourceOrder voters ballots candidates
                (assignedBudget sequence) quota
                (winnerSourceOrder sequence) =
              winnerSourceOrder sequence :=
          predictWinsLoopFromSourceOrder_eq_self_of_forall_ready
            (voters := voters) (ballots := ballots)
            (candidates := candidates)
            (assignedBudget := assignedBudget sequence) (quota := quota)
            (sourceOrder := winnerSourceOrder sequence)
            (hwin_ready sequence hfeasible)
        simpa [hloop_eq] using hwinCount_source_eq sequence hfeasible)
      (fun sequence hfeasible => by
        have hloop_eq :
            predictWinsLoopFromSourceOrder voters ballots candidates
                (assignedBudget sequence) quota
                (winnerSourceOrder sequence) =
              winnerSourceOrder sequence :=
          predictWinsLoopFromSourceOrder_eq_self_of_forall_ready
            (voters := voters) (ballots := ballots)
            (candidates := candidates)
            (assignedBudget := assignedBudget sequence) (quota := quota)
            (sourceOrder := winnerSourceOrder sequence)
            (hwin_ready sequence hfeasible)
        simpa [hloop_eq] using hassignedBudget_source_le sequence hfeasible)
      (fun sequence hfeasible => by
        have hloop_eq :
            predictWinsLoopFromSourceOrder voters ballots candidates
                (assignedBudget sequence) quota
                (winnerSourceOrder sequence) =
              winnerSourceOrder sequence :=
          predictWinsLoopFromSourceOrder_eq_self_of_forall_ready
            (voters := voters) (ballots := ballots)
            (candidates := candidates)
            (assignedBudget := assignedBudget sequence) (quota := quota)
            (sourceOrder := winnerSourceOrder sequence)
            (hwin_ready sequence hfeasible)
        simpa [hloop_eq] using hsupport_source_le sequence hfeasible)
      hloss_source_nodup hloss_source_mem htransfer_length hlower_transfer
      hsequence_eq htrace_prefix_len htrace_focus_get htrace_kind_get

/--
Concrete Proposition 3.4 Algorithm 7 source-order implementation with the
remaining Predict-Losses trace obligation stated as a single focused-prefix
predicate. This is the preferred source-facing bridge for the TeX Algorithm 7
loss loop.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceOrders_ready_transferBound_and_tracePrefix
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder lossSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {lossTransfers : RCVSequence → List ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwin_ready :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈
              predictWinsBudgetReadyCandidatesAtPrefix voters ballots
                candidates (assignedBudget sequence) quota pref)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hloss_source_nodup :
      ∀ sequence, feasibleSequence sequence →
        (lossSourceOrder sequence).Nodup)
    (hloss_source_mem :
      ∀ sequence, feasibleSequence sequence →
        ∀ candidate, candidate ∈ lossSourceOrder sequence →
          candidate ∈
            predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold)
    (htransfer_length :
      ∀ sequence, feasibleSequence sequence →
        (lossTransfers sequence).length = (lossSourceOrder sequence).length)
    (hlower_transfer :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          predictLossesTransferInitialLossBound topFirstChoice quota
            (lossTransfers sequence))
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_prefix :
      ∀ sequence, feasibleSequence sequence →
        (traceOf sequence).HasInitialEliminationFocusPrefix
          (predictLossesLoopFromSourceOrder voters ballots candidates budget
            firstChoiceThreshold (lossSourceOrder sequence))) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota lowerInitialLosses
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceOrders_ready_transferBound_and_traceSteps
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (lossSourceOrder := lossSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (lossTransfers := lossTransfers)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (lowerInitialLosses := lowerInitialLosses)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwin_ready hwinCount_source_eq
      hassignedBudget_source_le hsupport_source_le hloss_source_nodup
      hloss_source_mem htransfer_length hlower_transfer hsequence_eq
      (fun sequence hfeasible => (htrace_prefix sequence hfeasible).1)
      (fun sequence hfeasible i =>
        STVTrace.get_focus_eq_of_initialEliminationFocusPrefix
          (htrace_prefix sequence hfeasible) i)
      (fun sequence hfeasible i =>
        STVTrace.get_kind_eq_of_initialEliminationFocusPrefix
          (htrace_prefix sequence hfeasible) i)

/--
Concrete Proposition 3.4 Algorithm 7 source-order implementation with the
source-faithful count-only Predict-Losses trace obligation. Algorithm 7's
transfer loop computes a lower bound on the number of initial losses; the
source proof only needs the STV trace to have that many initial eliminations,
not to eliminate the whole definitely-losing list in the loop's exact order.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceOrders_ready_transferBound_and_initialEliminationCount
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder lossSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {lossTransfers : RCVSequence → List ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwin_ready :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈
              predictWinsBudgetReadyCandidatesAtPrefix voters ballots
                candidates (assignedBudget sequence) quota pref)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hloss_source_nodup :
      ∀ sequence, feasibleSequence sequence →
        (lossSourceOrder sequence).Nodup)
    (hloss_source_mem :
      ∀ sequence, feasibleSequence sequence →
        ∀ candidate, candidate ∈ lossSourceOrder sequence →
          candidate ∈
            predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold)
    (htransfer_length :
      ∀ sequence, feasibleSequence sequence →
        (lossTransfers sequence).length = (lossSourceOrder sequence).length)
    (hlower_transfer :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          predictLossesTransferInitialLossBound topFirstChoice quota
            (lossTransfers sequence))
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_initial :
      ∀ sequence, feasibleSequence sequence →
        (traceOf sequence).HasInitialEliminationPrefix lowerInitialLosses) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota lowerInitialLosses
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_budgetedPredictWinsSupportAccumulator_and_predictLossesPrefixes
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winCount := rcvSequenceWinCount)
      (initialLossCount := rcvSequenceInitialLossCount)
      (orderedWinners := winnerSourceOrder)
      (assignedBudget := assignedBudget)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (lowerInitialLosses := lowerInitialLosses)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwinCount_source_eq hassignedBudget_source_le
      hsupport_source_le
      (fun sequence hfeasible =>
        predictWinsSupportBudgetAccumulatorQuota_of_atPrefixes
          (predictWinsSupportBudgetAccumulatorQuotaAtPrefixes_of_mem_budgetReadyCandidatesAtPrefix
            (hwin_ready sequence hfeasible)))
      (fun sequence hfeasible =>
        predictLossesInitialLossPrefixCertificate_of_loopPrefix_take_and_traceInitialEliminationPrefix
          (hloop :=
            predictLossesLoopPrefix_of_sourceOrder_filter
              (voters := voters) (ballots := ballots)
              (candidates := candidates) (budget := budget)
              (firstChoiceThreshold := firstChoiceThreshold)
              (sourceOrder := lossSourceOrder sequence)
              (hloss_source_nodup sequence hfeasible))
          (hlower :=
            le_trans (hlower_transfer sequence hfeasible)
              (predictLossesTransferInitialLossBound_le_loop_length_of_forall_mem
                (voters := voters) (ballots := ballots)
                (candidates := candidates) (budget := budget)
                (firstChoiceThreshold := firstChoiceThreshold)
                (sourceOrder := lossSourceOrder sequence)
                (topFirstChoice := topFirstChoice) (quota := quota)
                (transfers := lossTransfers sequence)
                (htransfer_length sequence hfeasible)
                (hloss_source_mem sequence hfeasible)))
          (hsequence := hsequence_eq sequence hfeasible)
          (hprefix := htrace_initial sequence hfeasible))

/--
Concrete Proposition 3.4 Algorithm 7 source-order implementation where the
initial-elimination obligation is discharged by an executable/source-generated
minimal group-elimination trace.

The generated trace is parameterized by the source's loss group, initial active
set, and tally rule for each feasible sequence. This removes the abstract
`HasInitialEliminationPrefix` premise from the count-only Algorithm 7 endpoint:
the prefix follows from the generated run length and the choice rule's
active/total sanity conditions.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceOrders_ready_transferBound_and_generatedInitialEliminations
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {choice : MinimalTallyChoiceRule Candidate}
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder lossSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {lossTransfers : RCVSequence → List ℕ}
    {lossGroup initialActive : RCVSequence → Finset Candidate}
    {generatedRounds : RCVSequence → ℕ}
    {generatedTallyOf : RCVSequence → Finset Candidate → Candidate → ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    (hactiveChoice : choice.ChoosesActive)
    (htotalChoice : choice.Total)
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwin_ready :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈
              predictWinsBudgetReadyCandidatesAtPrefix voters ballots
                candidates (assignedBudget sequence) quota pref)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hloss_source_nodup :
      ∀ sequence, feasibleSequence sequence →
        (lossSourceOrder sequence).Nodup)
    (hloss_source_mem :
      ∀ sequence, feasibleSequence sequence →
        ∀ candidate, candidate ∈ lossSourceOrder sequence →
          candidate ∈
            predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold)
    (htransfer_length :
      ∀ sequence, feasibleSequence sequence →
        (lossTransfers sequence).length = (lossSourceOrder sequence).length)
    (hlower_transfer :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          predictLossesTransferInitialLossBound topFirstChoice quota
            (lossTransfers sequence))
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_generated :
      ∀ sequence, feasibleSequence sequence →
        traceOf sequence =
          minimalGroupEliminationGeneratedTrace choice (lossGroup sequence)
            (generatedTallyOf sequence) (generatedRounds sequence)
            (initialActive sequence))
    (hlower_rounds :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ generatedRounds sequence)
    (hgenerated_rounds :
      ∀ sequence, feasibleSequence sequence →
        generatedRounds sequence =
          (initialActive sequence ∩ lossGroup sequence).card) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota lowerInitialLosses
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceOrders_ready_transferBound_and_initialEliminationCount
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (lossSourceOrder := lossSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (lossTransfers := lossTransfers)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (lowerInitialLosses := lowerInitialLosses)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwin_ready hwinCount_source_eq
      hassignedBudget_source_le hsupport_source_le hloss_source_nodup
      hloss_source_mem htransfer_length hlower_transfer hsequence_eq
      (fun sequence hfeasible => by
        rw [htrace_generated sequence hfeasible]
        exact
          STVTrace.minimalGroupEliminationGeneratedTrace_hasInitialEliminationPrefix_of_le
            hactiveChoice htotalChoice (lossGroup sequence)
            (generatedTallyOf sequence) (hlower_rounds sequence hfeasible)
            (hgenerated_rounds sequence hfeasible))

/--
Concrete Proposition 3.4 Algorithm 7 source-order implementation with the
source STV run fixed to the generated minimum-tally lower-group elimination
trace. This removes the generated-trace identity and generated-round
bookkeeping premises from the more general generated-run endpoint.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceOrders_ready_transferBound_and_generatedTrace
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {choice : MinimalTallyChoiceRule Candidate}
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder lossSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {lossTransfers : RCVSequence → List ℕ}
    {lossGroup initialActive : RCVSequence → Finset Candidate}
    {generatedTallyOf : RCVSequence → Finset Candidate → Candidate → ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    (hactiveChoice : choice.ChoosesActive)
    (htotalChoice : choice.Total)
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwin_ready :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈
              predictWinsBudgetReadyCandidatesAtPrefix voters ballots
                candidates (assignedBudget sequence) quota pref)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hloss_source_nodup :
      ∀ sequence, feasibleSequence sequence →
        (lossSourceOrder sequence).Nodup)
    (hloss_source_mem :
      ∀ sequence, feasibleSequence sequence →
        ∀ candidate, candidate ∈ lossSourceOrder sequence →
          candidate ∈
            predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold)
    (htransfer_length :
      ∀ sequence, feasibleSequence sequence →
        (lossTransfers sequence).length = (lossSourceOrder sequence).length)
    (hlower_transfer :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          predictLossesTransferInitialLossBound topFirstChoice quota
            (lossTransfers sequence))
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence =
          rcvSequenceFromTrace
            (minimalGroupEliminationGeneratedTrace choice
              (lossGroup sequence) (generatedTallyOf sequence)
              ((initialActive sequence ∩ lossGroup sequence).card)
              (initialActive sequence)))
    (hlower_rounds :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          (initialActive sequence ∩ lossGroup sequence).card) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota lowerInitialLosses
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceOrders_ready_transferBound_and_generatedInitialEliminations
      (choice := choice)
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (lossSourceOrder := lossSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := fun sequence =>
        minimalGroupEliminationGeneratedTrace choice (lossGroup sequence)
          (generatedTallyOf sequence)
          ((initialActive sequence ∩ lossGroup sequence).card)
          (initialActive sequence))
      (lossTransfers := lossTransfers)
      (lossGroup := lossGroup)
      (initialActive := initialActive)
      (generatedRounds := fun sequence =>
        (initialActive sequence ∩ lossGroup sequence).card)
      (generatedTallyOf := generatedTallyOf)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (lowerInitialLosses := lowerInitialLosses)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hactiveChoice htotalChoice hall hquota_pos hseat hwin_ready
      hwinCount_source_eq hassignedBudget_source_le hsupport_source_le
      hloss_source_nodup hloss_source_mem htransfer_length hlower_transfer
      hsequence_eq
      (by
        intro sequence _hfeasible
        rfl)
      hlower_rounds
      (by
        intro sequence _hfeasible
        rfl)

/--
Concrete Proposition 3.4 Algorithm 7 source-order implementation with
index-wise trace facts for the count-only Predict-Losses prefix. This packages
the paper's natural "the first `lowerInitialLosses` rounds are eliminations"
obligation into the reusable initial-elimination prefix predicate.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceOrders_ready_transferBound_and_indexedInitialEliminations
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder lossSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {lossTransfers : RCVSequence → List ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwin_ready :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈
              predictWinsBudgetReadyCandidatesAtPrefix voters ballots
                candidates (assignedBudget sequence) quota pref)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hloss_source_nodup :
      ∀ sequence, feasibleSequence sequence →
        (lossSourceOrder sequence).Nodup)
    (hloss_source_mem :
      ∀ sequence, feasibleSequence sequence →
        ∀ candidate, candidate ∈ lossSourceOrder sequence →
          candidate ∈
            predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold)
    (htransfer_length :
      ∀ sequence, feasibleSequence sequence →
        (lossTransfers sequence).length = (lossSourceOrder sequence).length)
    (hlower_transfer :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          predictLossesTransferInitialLossBound topFirstChoice quota
            (lossTransfers sequence))
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ (traceOf sequence).steps.length)
    (htrace_kind_get :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses,
          ((traceOf sequence).steps.get
            ⟨i.1, Nat.lt_of_lt_of_le i.2
              (htrace_prefix_len sequence hfeasible)⟩).kind =
            StepKind.eliminate) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota lowerInitialLosses
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceOrders_ready_transferBound_and_initialEliminationCount
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (lossSourceOrder := lossSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (lossTransfers := lossTransfers)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (lowerInitialLosses := lowerInitialLosses)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwin_ready hwinCount_source_eq
      hassignedBudget_source_le hsupport_source_le hloss_source_nodup
      hloss_source_mem htransfer_length hlower_transfer hsequence_eq
      (fun sequence hfeasible =>
        STVTrace.hasInitialEliminationPrefix_of_getElem_kind
          (htrace_prefix_len sequence hfeasible)
          (htrace_kind_get sequence hfeasible))

/--
Concrete Proposition 3.4 Algorithm 7 source-order implementation with the
count-only Predict-Losses trace obligation discharged from an all-elimination
trace prefix. This is convenient when the source replay proves every recorded
step is an elimination and separately bounds the needed prefix length.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceOrders_ready_transferBound_and_allTraceEliminations
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder lossSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {lossTransfers : RCVSequence → List ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwin_ready :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈
              predictWinsBudgetReadyCandidatesAtPrefix voters ballots
                candidates (assignedBudget sequence) quota pref)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hloss_source_nodup :
      ∀ sequence, feasibleSequence sequence →
        (lossSourceOrder sequence).Nodup)
    (hloss_source_mem :
      ∀ sequence, feasibleSequence sequence →
        ∀ candidate, candidate ∈ lossSourceOrder sequence →
          candidate ∈
            predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold)
    (htransfer_length :
      ∀ sequence, feasibleSequence sequence →
        (lossTransfers sequence).length = (lossSourceOrder sequence).length)
    (hlower_transfer :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          predictLossesTransferInitialLossBound topFirstChoice quota
            (lossTransfers sequence))
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ (traceOf sequence).steps.length)
    (hall_trace_eliminate :
      ∀ sequence, feasibleSequence sequence →
        ∀ step, step ∈ (traceOf sequence).steps →
          step.kind = StepKind.eliminate) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota lowerInitialLosses
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceOrders_ready_transferBound_and_initialEliminationCount
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (lossSourceOrder := lossSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (lossTransfers := lossTransfers)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (lowerInitialLosses := lowerInitialLosses)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwin_ready hwinCount_source_eq
      hassignedBudget_source_le hsupport_source_le hloss_source_nodup
      hloss_source_mem htransfer_length hlower_transfer hsequence_eq
      (fun sequence hfeasible =>
        STVTrace.hasInitialEliminationPrefix_of_forall_mem_kind
          (htrace_prefix_len sequence hfeasible)
          (hall_trace_eliminate sequence hfeasible))

/--
Concrete Proposition 3.4 Algorithm 7 implementation from source inequalities,
the Predict-Losses transfer bound, and an all-elimination trace prefix. This
combines the paper's Predict-Wins candidate/quota inequalities with the
count-only Predict-Losses trace route, avoiding both a ready-set premise and a
focused candidate-order trace premise.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceInequalities_transferBound_and_allTraceEliminations
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder lossSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {lossTransfers : RCVSequence → List ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hselected_candidate :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈ candidates)
    (hselected_quota :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            quota ≤ assignedBudget sequence candidate +
              strictSupportCount voters ballots candidates
                (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref)
                candidate)
    (hloss_source_nodup :
      ∀ sequence, feasibleSequence sequence →
        (lossSourceOrder sequence).Nodup)
    (hloss_source_mem :
      ∀ sequence, feasibleSequence sequence →
        ∀ candidate, candidate ∈ lossSourceOrder sequence →
          candidate ∈
            predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold)
    (htransfer_length :
      ∀ sequence, feasibleSequence sequence →
        (lossTransfers sequence).length = (lossSourceOrder sequence).length)
    (hlower_transfer :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          predictLossesTransferInitialLossBound topFirstChoice quota
            (lossTransfers sequence))
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ (traceOf sequence).steps.length)
    (hall_trace_eliminate :
      ∀ sequence, feasibleSequence sequence →
        ∀ step, step ∈ (traceOf sequence).steps →
          step.kind = StepKind.eliminate) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota lowerInitialLosses
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceOrders_ready_transferBound_and_allTraceEliminations
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (lossSourceOrder := lossSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (lossTransfers := lossTransfers)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (lowerInitialLosses := lowerInitialLosses)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat
      (fun sequence hfeasible =>
        predictWinsBudgetReadySelections_of_sourceInequalities
          (hcandidate := hselected_candidate sequence hfeasible)
          (hquota := hselected_quota sequence hfeasible))
      hwinCount_source_eq hassignedBudget_source_le hsupport_source_le
      hloss_source_nodup hloss_source_mem htransfer_length hlower_transfer
      hsequence_eq htrace_prefix_len hall_trace_eliminate

/--
Concrete Proposition 3.4 Algorithm 7 implementation from source inequalities,
the Predict-Losses transfer bound, and prefix no-quota trace facts. This
replaces the stronger "all trace steps are eliminations" premise with the
source-shaped argument that a prefix step can only be an election or
elimination, elections require quota, and every active prefix candidate remains
below quota.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceInequalities_transferBound_and_noQuotaPrefix
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder lossSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {lossTransfers : RCVSequence → List ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hselected_candidate :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈ candidates)
    (hselected_quota :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            quota ≤ assignedBudget sequence candidate +
              strictSupportCount voters ballots candidates
                (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref)
                candidate)
    (hloss_source_nodup :
      ∀ sequence, feasibleSequence sequence →
        (lossSourceOrder sequence).Nodup)
    (hloss_source_mem :
      ∀ sequence, feasibleSequence sequence →
        ∀ candidate, candidate ∈ lossSourceOrder sequence →
          candidate ∈
            predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold)
    (htransfer_length :
      ∀ sequence, feasibleSequence sequence →
        (lossTransfers sequence).length = (lossSourceOrder sequence).length)
    (hlower_transfer :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          predictLossesTransferInitialLossBound topFirstChoice quota
            (lossTransfers sequence))
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ (traceOf sequence).steps.length)
    (htrace_kind_allowed :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses,
          ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).kind =
              StepKind.elect ∨
            ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).kind =
              StepKind.eliminate)
    (helect_quota :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses,
          ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).kind =
              StepKind.elect →
            ∃ candidate,
              candidate ∈
                ((traceOf sequence).steps.get
                  ⟨i.1, Nat.lt_of_lt_of_le i.2
                    (htrace_prefix_len sequence hfeasible)⟩).beforeActive ∧
              quota ≤
                ((traceOf sequence).steps.get
                  ⟨i.1, Nat.lt_of_lt_of_le i.2
                    (htrace_prefix_len sequence hfeasible)⟩).tally candidate)
    (hactive_lt_quota :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses,
          ∀ candidate,
            candidate ∈
              ((traceOf sequence).steps.get
                ⟨i.1, Nat.lt_of_lt_of_le i.2
                  (htrace_prefix_len sequence hfeasible)⟩).beforeActive →
            ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).tally candidate <
              quota) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota lowerInitialLosses
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceOrders_ready_transferBound_and_initialEliminationCount
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (lossSourceOrder := lossSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (lossTransfers := lossTransfers)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (lowerInitialLosses := lowerInitialLosses)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat
      (fun sequence hfeasible =>
        predictWinsBudgetReadySelections_of_sourceInequalities
          (hcandidate := hselected_candidate sequence hfeasible)
          (hquota := hselected_quota sequence hfeasible))
      hwinCount_source_eq hassignedBudget_source_le hsupport_source_le
      hloss_source_nodup hloss_source_mem htransfer_length hlower_transfer
      hsequence_eq
      (fun sequence hfeasible =>
        STVTrace.hasInitialEliminationPrefix_of_getElem_no_active_quota
          (htrace_prefix_len sequence hfeasible)
          (htrace_kind_allowed sequence hfeasible)
          (helect_quota sequence hfeasible)
          (hactive_lt_quota sequence hfeasible))

/--
Concrete Proposition 3.4 Algorithm 7 implementation from source inequalities
and the Predict-Losses transfer-loop invariant. Compared with
`..._and_noQuotaPrefix`, this theorem derives the "no quota before the counted
initial losses" premise from the source transfer counter plus a concrete tally
upper bound by the top first-choice count and previous transfers.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceInequalities_transferBound_and_transferPrefixTallies
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder lossSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {lossTransfers : RCVSequence → List ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hselected_candidate :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈ candidates)
    (hselected_quota :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            quota ≤ assignedBudget sequence candidate +
              strictSupportCount voters ballots candidates
                (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref)
                candidate)
    (hloss_source_nodup :
      ∀ sequence, feasibleSequence sequence →
        (lossSourceOrder sequence).Nodup)
    (hloss_source_mem :
      ∀ sequence, feasibleSequence sequence →
        ∀ candidate, candidate ∈ lossSourceOrder sequence →
          candidate ∈
            predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold)
    (htransfer_length :
      ∀ sequence, feasibleSequence sequence →
        (lossTransfers sequence).length = (lossSourceOrder sequence).length)
    (hlower_transfer :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          predictLossesTransferInitialLossBound topFirstChoice quota
            (lossTransfers sequence))
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ (traceOf sequence).steps.length)
    (htrace_kind_allowed :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses,
          ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).kind =
              StepKind.elect ∨
            ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).kind =
              StepKind.eliminate)
    (helect_quota :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses,
          ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).kind =
              StepKind.elect →
            ∃ candidate,
              candidate ∈
                ((traceOf sequence).steps.get
                  ⟨i.1, Nat.lt_of_lt_of_le i.2
                    (htrace_prefix_len sequence hfeasible)⟩).beforeActive ∧
              quota ≤
                ((traceOf sequence).steps.get
                  ⟨i.1, Nat.lt_of_lt_of_le i.2
                    (htrace_prefix_len sequence hfeasible)⟩).tally candidate)
    (htop_lt_quota : topFirstChoice < quota)
    (hactive_tally_le_transfer_prefix :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses,
          ∀ candidate,
            candidate ∈
              ((traceOf sequence).steps.get
                ⟨i.1, Nat.lt_of_lt_of_le i.2
                  (htrace_prefix_len sequence hfeasible)⟩).beforeActive →
            ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).tally candidate ≤
              ((lossTransfers sequence).take i.1).sum + topFirstChoice) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota lowerInitialLosses
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceInequalities_transferBound_and_noQuotaPrefix
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (lossSourceOrder := lossSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (lossTransfers := lossTransfers)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (lowerInitialLosses := lowerInitialLosses)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwinCount_source_eq
      hassignedBudget_source_le hsupport_source_le hselected_candidate
      hselected_quota hloss_source_nodup hloss_source_mem htransfer_length
      hlower_transfer hsequence_eq htrace_prefix_len htrace_kind_allowed
      helect_quota
      (fun sequence hfeasible i candidate hactive =>
        lt_of_le_of_lt
          (hactive_tally_le_transfer_prefix sequence hfeasible i candidate
            hactive)
          (predictLossesTransferInitialLossBound_prefix_sum_lt_quota
            (topFirstChoice := topFirstChoice)
            (quota := quota)
            (transfers := lossTransfers sequence)
            (i := i.1)
            htop_lt_quota
            (Nat.lt_of_lt_of_le i.2
              (hlower_transfer sequence hfeasible))))

/--
Trace-level transfer-prefix tally bound. If every candidate's first prefix
tally is at most `topFirstChoice`, and each following prefix step increases an
active candidate's tally by at most the corresponding transfer increment, then
the candidate's tally at prefix index `i` is bounded by `topFirstChoice` plus
the accumulated transfer increments before `i`.

The increment premise is deliberately stated against the previous active-set
indicator: if a candidate was not active in the previous prefix step, the
source model must bound the new active tally directly by that round's transfer
increment.
-/
theorem rcvTrace_active_tally_le_topFirstChoice_add_transfer_prefix_sum
    {Candidate : Type*} [DecidableEq Candidate]
    {trace : RCVTrace Candidate} {prefixLen topFirstChoice : ℕ}
    {transferAt : ℕ → ℕ}
    (hprefix_len : prefixLen ≤ trace.steps.length)
    (hinitial :
      ∀ hpos : 0 < prefixLen, ∀ candidate,
        candidate ∈
          (trace.steps.get
            ⟨0, Nat.lt_of_lt_of_le hpos hprefix_len⟩).beforeActive →
        (trace.steps.get
          ⟨0, Nat.lt_of_lt_of_le hpos hprefix_len⟩).tally
          candidate ≤ topFirstChoice)
    (hincrement :
      ∀ i, ∀ hnext : i + 1 < prefixLen, ∀ candidate,
          candidate ∈
            (trace.steps.get
              ⟨i + 1, Nat.lt_of_lt_of_le hnext
                hprefix_len⟩).beforeActive →
          (trace.steps.get
            ⟨i + 1, Nat.lt_of_lt_of_le hnext
              hprefix_len⟩).tally candidate ≤
            (if candidate ∈
                (trace.steps.get
                  ⟨i, Nat.lt_of_lt_of_le
                    (Nat.lt_of_succ_lt hnext) hprefix_len⟩).beforeActive then
              (trace.steps.get
                ⟨i, Nat.lt_of_lt_of_le
                  (Nat.lt_of_succ_lt hnext) hprefix_len⟩).tally
                candidate
            else
              0) + transferAt i) :
    ∀ i : Fin prefixLen,
      ∀ candidate,
        candidate ∈
          (trace.steps.get
            ⟨i.1, Nat.lt_of_lt_of_le i.2 hprefix_len⟩).beforeActive →
        (trace.steps.get
          ⟨i.1, Nat.lt_of_lt_of_le i.2 hprefix_len⟩).tally candidate ≤
          topFirstChoice + ∑ j ∈ Finset.range i.1, transferAt j := by
  intro i candidate hactive
  let value : ℕ → ℕ := fun idx =>
    if hidx : idx < prefixLen then
      if candidate ∈
          (trace.steps.get
            ⟨idx, Nat.lt_of_lt_of_le hidx hprefix_len⟩).beforeActive then
        (trace.steps.get
          ⟨idx, Nat.lt_of_lt_of_le hidx hprefix_len⟩).tally candidate
      else
        0
    else
      0
  have hzero : value 0 ≤ topFirstChoice := by
    by_cases hpos : 0 < prefixLen
    · by_cases hactive0 :
        candidate ∈
          (trace.steps.get
            ⟨0, Nat.lt_of_lt_of_le hpos hprefix_len⟩).beforeActive
      · have hactive0' : candidate ∈ trace.steps[0].beforeActive := by
          simpa using hactive0
        simpa [value, hpos, hactive0'] using hinitial hpos candidate hactive0
      · have hactive0' : candidate ∉ trace.steps[0].beforeActive := by
          simpa using hactive0
        simp [value, hpos, hactive0']
    · simp [value, hpos]
  have hstep :
      ∀ idx, idx + 1 < prefixLen →
        value (idx + 1) ≤ value idx + transferAt idx := by
    intro idx hnext
    have hidx : idx < prefixLen := Nat.lt_of_succ_lt hnext
    by_cases hactive_next :
        candidate ∈
          (trace.steps.get
            ⟨idx + 1, Nat.lt_of_lt_of_le hnext hprefix_len⟩).beforeActive
    · by_cases hactive_current :
        candidate ∈
          (trace.steps.get
            ⟨idx, Nat.lt_of_lt_of_le hidx hprefix_len⟩).beforeActive
      · have hactive_next' :
            candidate ∈ trace.steps[idx + 1].beforeActive := by
          simpa using hactive_next
        have hactive_current' :
            candidate ∈ trace.steps[idx].beforeActive := by
          simpa using hactive_current
        simpa [value, hnext, hidx, hactive_next', hactive_current'] using
          hincrement idx hnext candidate hactive_next
      · have hactive_next' :
            candidate ∈ trace.steps[idx + 1].beforeActive := by
          simpa using hactive_next
        have hactive_current' :
            candidate ∉ trace.steps[idx].beforeActive := by
          simpa using hactive_current
        simpa [value, hnext, hidx, hactive_next', hactive_current'] using
          hincrement idx hnext candidate hactive_next
    · have hactive_next' :
          candidate ∉ trace.steps[idx + 1].beforeActive := by
        simpa using hactive_next
      simp [value, hnext, hactive_next']
  have hbound :=
    EconCSLib.FiniteSum.nat_value_le_base_add_sum_range_of_step_le_of_lt
      value transferAt (base := topFirstChoice) (prefixLen := prefixLen)
      hzero hstep i.1 i.2
  have hactive' : candidate ∈ trace.steps[i.1].beforeActive := by
    simpa using hactive
  simpa [value, i.2, hactive'] using hbound

/--
Trace-level transfer-prefix tally bound from ballot support.  This is the
DGJ24-specific bridge from the shared STV support-count lemma to Algorithm 7's
transfer-prefix accounting: if each counted trace step uses a tally bounded by
active ballot support, and active-support voters split between first-choice
support for the active candidate and the already removed prefix, then the
tally is bounded by the top first-choice cap plus the accumulated transfer
budget.
-/
theorem rcvTrace_active_tally_le_topFirstChoice_add_transfer_prefix_sum_of_activeSupport_partition
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {trace : RCVTrace Candidate} {prefixLen topFirstChoice : ℕ}
    {transferAt : ℕ → ℕ}
    (hprefix_len : prefixLen ≤ trace.steps.length)
    (removedPrefix : Fin prefixLen → Finset Candidate)
    (htally_le_activeSupport :
      ∀ i : Fin prefixLen, ∀ candidate,
        candidate ∈
          (trace.steps.get
            ⟨i.1, Nat.lt_of_lt_of_le i.2 hprefix_len⟩).beforeActive →
        (trace.steps.get
          ⟨i.1, Nat.lt_of_lt_of_le i.2 hprefix_len⟩).tally candidate ≤
          (Ballot.activeSupport voters ballots
            ((trace.steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2 hprefix_len⟩).beforeActive)
            candidate).card)
    (hpartition :
      ∀ i : Fin prefixLen, ∀ candidate,
        candidate ∈
          (trace.steps.get
            ⟨i.1, Nat.lt_of_lt_of_le i.2 hprefix_len⟩).beforeActive →
        ∀ voter, voter ∈ voters →
          Ballot.nextActive (ballots voter)
              ((trace.steps.get
                ⟨i.1, Nat.lt_of_lt_of_le i.2 hprefix_len⟩).beforeActive) =
            some candidate →
          Ballot.firstChoiceIn (ballots voter) {candidate} ∨
            Ballot.firstChoiceIn (ballots voter) (removedPrefix i))
    (hfirst_le :
      ∀ i : Fin prefixLen, ∀ candidate,
        candidate ∈
          (trace.steps.get
            ⟨i.1, Nat.lt_of_lt_of_le i.2 hprefix_len⟩).beforeActive →
        Ballot.firstChoiceCount voters ballots candidate ≤ topFirstChoice)
    (htransfer_le :
      ∀ i : Fin prefixLen, ∀ candidate,
        candidate ∈
          (trace.steps.get
            ⟨i.1, Nat.lt_of_lt_of_le i.2 hprefix_len⟩).beforeActive →
        Ballot.strictSupportCount voters ballots (removedPrefix i)
            (((trace.steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2 hprefix_len⟩).beforeActive).erase
              candidate) candidate ≤
          ∑ j ∈ Finset.range i.1, transferAt j) :
    ∀ i : Fin prefixLen,
      ∀ candidate,
        candidate ∈
          (trace.steps.get
            ⟨i.1, Nat.lt_of_lt_of_le i.2 hprefix_len⟩).beforeActive →
        (trace.steps.get
          ⟨i.1, Nat.lt_of_lt_of_le i.2 hprefix_len⟩).tally candidate ≤
          topFirstChoice + ∑ j ∈ Finset.range i.1, transferAt j := by
  intro i candidate hactive
  exact
    STVStep.tally_le_base_add_transferBound_of_activeSupport_partition
      (voters := voters) (ballots := ballots) (removed := removedPrefix i)
      (step :=
        trace.steps.get
          ⟨i.1, Nat.lt_of_lt_of_le i.2 hprefix_len⟩)
      (candidate := candidate) (base := topFirstChoice)
      (transferBound := ∑ j ∈ Finset.range i.1, transferAt j)
      (htally_le_activeSupport i candidate hactive) hactive
      (hpartition i candidate hactive)
      (hfirst_le i candidate hactive)
      (htransfer_le i candidate hactive)

/--
Proposition 3.4 route whose transfer-prefix tally premise is derived from
ballot active-support accounting.  The remaining source-specific facts say
which eliminated prefix is responsible for transfers at each counted loss
round, and bound first-choice and transferred strict-support counts by the
Algorithm 7 top-first-choice and transfer-prefix budgets.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceInequalities_transferBound_and_activeSupportPartitions
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder lossSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {lossTransfers : RCVSequence → List ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    {removedPrefix : RCVSequence → Fin lowerInitialLosses → Finset Candidate}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hselected_candidate :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈ candidates)
    (hselected_quota :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            quota ≤ assignedBudget sequence candidate +
              strictSupportCount voters ballots candidates
                (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref)
                candidate)
    (hloss_source_nodup :
      ∀ sequence, feasibleSequence sequence →
        (lossSourceOrder sequence).Nodup)
    (hloss_source_mem :
      ∀ sequence, feasibleSequence sequence →
        ∀ candidate, candidate ∈ lossSourceOrder sequence →
          candidate ∈
            predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold)
    (htransfer_length :
      ∀ sequence, feasibleSequence sequence →
        (lossTransfers sequence).length = (lossSourceOrder sequence).length)
    (hlower_transfer :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          predictLossesTransferInitialLossBound topFirstChoice quota
            (lossTransfers sequence))
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ (traceOf sequence).steps.length)
    (htrace_kind_allowed :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses,
          ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).kind =
              StepKind.elect ∨
            ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).kind =
              StepKind.eliminate)
    (helect_quota :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses,
          ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).kind =
              StepKind.elect →
            ∃ candidate,
              candidate ∈
                ((traceOf sequence).steps.get
                  ⟨i.1, Nat.lt_of_lt_of_le i.2
                    (htrace_prefix_len sequence hfeasible)⟩).beforeActive ∧
              quota ≤
                ((traceOf sequence).steps.get
                  ⟨i.1, Nat.lt_of_lt_of_le i.2
                    (htrace_prefix_len sequence hfeasible)⟩).tally candidate)
    (htop_lt_quota : topFirstChoice < quota)
    (htally_le_activeSupport :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses, ∀ candidate,
          candidate ∈
            ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).beforeActive →
          ((traceOf sequence).steps.get
            ⟨i.1, Nat.lt_of_lt_of_le i.2
              (htrace_prefix_len sequence hfeasible)⟩).tally candidate ≤
            (Ballot.activeSupport voters ballots
              (((traceOf sequence).steps.get
                ⟨i.1, Nat.lt_of_lt_of_le i.2
                  (htrace_prefix_len sequence hfeasible)⟩).beforeActive)
              candidate).card)
    (hactive_partition :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses, ∀ candidate,
          candidate ∈
            ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).beforeActive →
          ∀ voter, voter ∈ voters →
            Ballot.nextActive (ballots voter)
                (((traceOf sequence).steps.get
                  ⟨i.1, Nat.lt_of_lt_of_le i.2
                    (htrace_prefix_len sequence hfeasible)⟩).beforeActive) =
              some candidate →
            Ballot.firstChoiceIn (ballots voter) {candidate} ∨
              Ballot.firstChoiceIn (ballots voter)
                (removedPrefix sequence i))
    (hfirst_le :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses, ∀ candidate,
          candidate ∈
            ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).beforeActive →
          Ballot.firstChoiceCount voters ballots candidate ≤ topFirstChoice)
    (htransfer_le :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses, ∀ candidate,
          candidate ∈
            ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).beforeActive →
          Ballot.strictSupportCount voters ballots (removedPrefix sequence i)
              ((((traceOf sequence).steps.get
                ⟨i.1, Nat.lt_of_lt_of_le i.2
                  (htrace_prefix_len sequence hfeasible)⟩).beforeActive).erase
                candidate) candidate ≤
            ((lossTransfers sequence).take i.1).sum) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota lowerInitialLosses
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceInequalities_transferBound_and_transferPrefixTallies
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (lossSourceOrder := lossSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (lossTransfers := lossTransfers)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (lowerInitialLosses := lowerInitialLosses)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwinCount_source_eq hassignedBudget_source_le
      hsupport_source_le hselected_candidate hselected_quota
      hloss_source_nodup hloss_source_mem htransfer_length hlower_transfer
      hsequence_eq htrace_prefix_len htrace_kind_allowed helect_quota
      htop_lt_quota
      (by
        intro sequence hfeasible i candidate hactive
        let transferAt : ℕ → ℕ :=
          fun j => (lossTransfers sequence).getD j 0
        have hprefix_sum :
            ((lossTransfers sequence).take i.1).sum =
              ∑ j ∈ Finset.range i.1, transferAt j := by
          simpa [transferAt] using
            EconCSLib.FiniteSum.list_sum_take_eq_sum_range_getD
              (lossTransfers sequence) i.1
        have hbound :
            ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).tally candidate ≤
              topFirstChoice + ∑ j ∈ Finset.range i.1, transferAt j :=
          rcvTrace_active_tally_le_topFirstChoice_add_transfer_prefix_sum_of_activeSupport_partition
            (voters := voters) (ballots := ballots)
            (trace := traceOf sequence) (prefixLen := lowerInitialLosses)
            (topFirstChoice := topFirstChoice) (transferAt := transferAt)
            (htrace_prefix_len sequence hfeasible)
            (removedPrefix sequence)
            (htally_le_activeSupport sequence hfeasible)
            (hactive_partition sequence hfeasible)
            (hfirst_le sequence hfeasible)
            (by
              intro k candidate hactive
              have hprefix_sum_k :
                  ((lossTransfers sequence).take k.1).sum =
                    ∑ j ∈ Finset.range k.1, transferAt j := by
                simpa [transferAt] using
                  EconCSLib.FiniteSum.list_sum_take_eq_sum_range_getD
                    (lossTransfers sequence) k.1
              rw [← hprefix_sum_k]
              exact htransfer_le sequence hfeasible k candidate hactive)
            i candidate hactive
        calc
          ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).tally candidate
              ≤ topFirstChoice + ∑ j ∈ Finset.range i.1, transferAt j :=
            hbound
          _ = topFirstChoice + ((lossTransfers sequence).take i.1).sum := by
            rw [← hprefix_sum]
          _ = ((lossTransfers sequence).take i.1).sum + topFirstChoice := by
            rw [Nat.add_comm])

/--
Proposition 3.4 active-support route specialized to the canonical profile
group-elimination trace.  The generated trace itself supplies prefix length,
all-elimination step kinds, vacuous election-step quota obligations, and exact
tally-as-active-support equalities.  The remaining source-specific work is the
ballot partition that identifies first-choice support versus transferred
removed-prefix support, and the corresponding first-choice and transfer caps.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceInequalities_transferBound_and_canonicalProfileActiveSupportPartitions
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder lossSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {lossTransfers : RCVSequence → List ℕ}
    {lossGroup initialActive : RCVSequence → Finset Candidate}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    {removedPrefix : RCVSequence → Fin lowerInitialLosses → Finset Candidate}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hselected_candidate :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈ candidates)
    (hselected_quota :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            quota ≤ assignedBudget sequence candidate +
              strictSupportCount voters ballots candidates
                (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref)
                candidate)
    (hloss_source_nodup :
      ∀ sequence, feasibleSequence sequence →
        (lossSourceOrder sequence).Nodup)
    (hloss_source_mem :
      ∀ sequence, feasibleSequence sequence →
        ∀ candidate, candidate ∈ lossSourceOrder sequence →
          candidate ∈
            predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold)
    (htransfer_length :
      ∀ sequence, feasibleSequence sequence →
        (lossTransfers sequence).length = (lossSourceOrder sequence).length)
    (hlower_transfer :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          predictLossesTransferInitialLossBound topFirstChoice quota
            (lossTransfers sequence))
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence =
          rcvSequenceFromTrace
            (canonicalProfileGroupEliminationGeneratedTrace voters ballots
              (lossGroup sequence)
              ((initialActive sequence ∩ lossGroup sequence).card)
              (initialActive sequence)))
    (hlower_rounds :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          (initialActive sequence ∩ lossGroup sequence).card)
    (htop_lt_quota : topFirstChoice < quota)
    (hactive_partition :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses,
          ∀ hidx :
            i.1 <
              (canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.length,
          ∀ candidate,
            candidate ∈
              ((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.get ⟨i.1, hidx⟩).beforeActive →
          ∀ voter, voter ∈ voters →
            Ballot.nextActive (ballots voter)
                (((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                  (lossGroup sequence)
                  ((initialActive sequence ∩ lossGroup sequence).card)
                  (initialActive sequence)).steps.get
                  ⟨i.1, hidx⟩).beforeActive) =
              some candidate →
            Ballot.firstChoiceIn (ballots voter) {candidate} ∨
              Ballot.firstChoiceIn (ballots voter)
                (removedPrefix sequence i))
    (hfirst_le :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses,
          ∀ hidx :
            i.1 <
              (canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.length,
          ∀ candidate,
            candidate ∈
              ((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.get ⟨i.1, hidx⟩).beforeActive →
          Ballot.firstChoiceCount voters ballots candidate ≤ topFirstChoice)
    (htransfer_le :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses,
          ∀ hidx :
            i.1 <
              (canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.length,
          ∀ candidate,
            candidate ∈
              ((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.get ⟨i.1, hidx⟩).beforeActive →
          strictSupportCount voters ballots (removedPrefix sequence i)
              ((((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.get
                ⟨i.1, hidx⟩).beforeActive).erase candidate) candidate ≤
            ((lossTransfers sequence).take i.1).sum) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota lowerInitialLosses
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  let traceOf : RCVSequence → RCVTrace Candidate :=
    fun sequence =>
      canonicalProfileGroupEliminationGeneratedTrace voters ballots
        (lossGroup sequence)
        ((initialActive sequence ∩ lossGroup sequence).card)
        (initialActive sequence)
  have htrace_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ (traceOf sequence).steps.length := by
    intro sequence hfeasible
    have hlen :
        (traceOf sequence).steps.length =
          (initialActive sequence ∩ lossGroup sequence).card := by
      simpa [traceOf, canonicalProfileGroupEliminationGeneratedTrace] using
        canonicalProfileGroupEliminationGeneratedSteps_length_eq
          voters ballots (lossGroup sequence)
          (initialActive := initialActive sequence) (hrounds := rfl)
    rw [hlen]
    exact hlower_rounds sequence hfeasible
  have hall_eliminate :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses,
          ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).kind =
            StepKind.eliminate := by
    intro sequence hfeasible i
    have hmem :
        (traceOf sequence).steps.get
            ⟨i.1, Nat.lt_of_lt_of_le i.2
              (htrace_prefix_len sequence hfeasible)⟩ ∈
          (traceOf sequence).steps :=
      List.get_mem (traceOf sequence).steps
        ⟨i.1, Nat.lt_of_lt_of_le i.2
          (htrace_prefix_len sequence hfeasible)⟩
    exact
      minimalGroupEliminationGeneratedSteps_all_eliminate
        (MinimalTallyChoiceRule.canonical Candidate) (lossGroup sequence)
        (profileActiveTallyOf voters ballots)
        ((initialActive sequence ∩ lossGroup sequence).card)
        (initialActive sequence)
        ((traceOf sequence).steps.get
          ⟨i.1, Nat.lt_of_lt_of_le i.2
            (htrace_prefix_len sequence hfeasible)⟩)
        (by
          simpa [traceOf, canonicalProfileGroupEliminationGeneratedTrace,
            canonicalProfileGroupEliminationGeneratedSteps] using hmem)
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceInequalities_transferBound_and_activeSupportPartitions
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (lossSourceOrder := lossSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (lossTransfers := lossTransfers)
      (removedPrefix := removedPrefix)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (lowerInitialLosses := lowerInitialLosses)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwinCount_source_eq hassignedBudget_source_le
      hsupport_source_le hselected_candidate hselected_quota
      hloss_source_nodup hloss_source_mem htransfer_length hlower_transfer
      (by
        intro sequence hfeasible
        simpa [traceOf] using hsequence_eq sequence hfeasible)
      htrace_prefix_len
      (by
        intro sequence hfeasible i
        exact Or.inr (hall_eliminate sequence hfeasible i))
      (by
        intro sequence hfeasible i helect
        have helim := hall_eliminate sequence hfeasible i
        rw [helim] at helect
        cases helect)
      htop_lt_quota
      (by
        intro sequence hfeasible i candidate hactive
        simpa [traceOf] using
          (le_of_eq
            (canonicalProfileGroupEliminationGeneratedTrace_get_tally_eq
              voters ballots (lossGroup sequence)
              ((initialActive sequence ∩ lossGroup sequence).card)
              (initialActive sequence)
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩ candidate)))
      (by
        intro sequence hfeasible i candidate hactive
        simpa [traceOf] using
          hactive_partition sequence hfeasible i
            (Nat.lt_of_lt_of_le i.2
              (htrace_prefix_len sequence hfeasible))
            candidate (by simpa [traceOf] using hactive))
      (by
        intro sequence hfeasible i candidate hactive
        simpa [traceOf] using
          hfirst_le sequence hfeasible i
            (Nat.lt_of_lt_of_le i.2
              (htrace_prefix_len sequence hfeasible))
            candidate (by simpa [traceOf] using hactive))
      (by
        intro sequence hfeasible i candidate hactive
        simpa [traceOf] using
          htransfer_le sequence hfeasible i
            (Nat.lt_of_lt_of_le i.2
              (htrace_prefix_len sequence hfeasible))
            candidate (by simpa [traceOf] using hactive))

/--
Proposition 3.4 canonical-profile route with the removed prefix fixed to the
canonical active-set difference.  If every relevant ballot starts in the
initial active set, the ballot API derives the active-support partition used by
the transfer-prefix accounting; the remaining source premises are the numeric
Algorithm 7 first-choice and transfer-prefix bounds.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceInequalities_transferBound_and_canonicalProfileInitialActiveRemovedPrefix
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder lossSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {lossTransfers : RCVSequence → List ℕ}
    {lossGroup initialActive : RCVSequence → Finset Candidate}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hselected_candidate :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈ candidates)
    (hselected_quota :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            quota ≤ assignedBudget sequence candidate +
              strictSupportCount voters ballots candidates
                (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref)
                candidate)
    (hloss_source_nodup :
      ∀ sequence, feasibleSequence sequence →
        (lossSourceOrder sequence).Nodup)
    (hloss_source_mem :
      ∀ sequence, feasibleSequence sequence →
        ∀ candidate, candidate ∈ lossSourceOrder sequence →
          candidate ∈
            predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold)
    (htransfer_length :
      ∀ sequence, feasibleSequence sequence →
        (lossTransfers sequence).length = (lossSourceOrder sequence).length)
    (hlower_transfer :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          predictLossesTransferInitialLossBound topFirstChoice quota
            (lossTransfers sequence))
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence =
          rcvSequenceFromTrace
            (canonicalProfileGroupEliminationGeneratedTrace voters ballots
              (lossGroup sequence)
              ((initialActive sequence ∩ lossGroup sequence).card)
              (initialActive sequence)))
    (hlower_rounds :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          (initialActive sequence ∩ lossGroup sequence).card)
    (hfirst_choice_initial :
      ∀ sequence, feasibleSequence sequence →
        ∀ voter, voter ∈ voters →
          Ballot.firstChoiceIn (ballots voter) (initialActive sequence))
    (htop_lt_quota : topFirstChoice < quota)
    (hfirst_le :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses,
          ∀ hidx :
            i.1 <
              (canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.length,
          ∀ candidate,
            candidate ∈
              ((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.get ⟨i.1, hidx⟩).beforeActive →
          Ballot.firstChoiceCount voters ballots candidate ≤ topFirstChoice)
    (htransfer_le :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses,
          ∀ hidx :
            i.1 <
              (canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.length,
          ∀ candidate,
            candidate ∈
              ((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.get ⟨i.1, hidx⟩).beforeActive →
          strictSupportCount voters ballots
              (initialActive sequence \
                (((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                  (lossGroup sequence)
                  ((initialActive sequence ∩ lossGroup sequence).card)
                  (initialActive sequence)).steps.get
                  ⟨i.1, hidx⟩).beforeActive))
              ((((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.get
                ⟨i.1, hidx⟩).beforeActive).erase candidate) candidate ≤
            ((lossTransfers sequence).take i.1).sum) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota lowerInitialLosses
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  classical
  let traceOf : RCVSequence → RCVTrace Candidate :=
    fun sequence =>
      canonicalProfileGroupEliminationGeneratedTrace voters ballots
        (lossGroup sequence)
        ((initialActive sequence ∩ lossGroup sequence).card)
        (initialActive sequence)
  let removedPrefix : RCVSequence → Fin lowerInitialLosses → Finset Candidate :=
    fun sequence i =>
      if hfeasible : feasibleSequence sequence then
        initialActive sequence \
          ((traceOf sequence).steps.get
            ⟨i.1, Nat.lt_of_lt_of_le i.2
              (by
                have hlen :
                    (traceOf sequence).steps.length =
                      (initialActive sequence ∩ lossGroup sequence).card := by
                  simpa [traceOf, canonicalProfileGroupEliminationGeneratedTrace] using
                    canonicalProfileGroupEliminationGeneratedSteps_length_eq
                      voters ballots (lossGroup sequence)
                      (initialActive := initialActive sequence) (hrounds := rfl)
                rw [hlen]
                exact hlower_rounds sequence hfeasible)⟩).beforeActive
      else
        ∅
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceInequalities_transferBound_and_canonicalProfileActiveSupportPartitions
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (lossSourceOrder := lossSourceOrder)
      (assignedBudget := assignedBudget)
      (lossTransfers := lossTransfers)
      (lossGroup := lossGroup)
      (initialActive := initialActive)
      (removedPrefix := removedPrefix)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (lowerInitialLosses := lowerInitialLosses)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwinCount_source_eq hassignedBudget_source_le
      hsupport_source_le hselected_candidate hselected_quota
      hloss_source_nodup hloss_source_mem htransfer_length hlower_transfer
      hsequence_eq hlower_rounds htop_lt_quota
      (by
        intro sequence hfeasible i hidx candidate hactive voter hvoter hnext
        have hpartition :=
          Ballot.firstChoiceIn_singleton_or_sdiff_of_nextActive_some
            (ballot := ballots voter)
            (initial := initialActive sequence)
            (active :=
              ((traceOf sequence).steps.get ⟨i.1, hidx⟩).beforeActive)
            (candidate := candidate)
            (hfirst_choice_initial sequence hfeasible voter hvoter)
            (by simpa [traceOf] using hnext)
        simpa [removedPrefix, hfeasible, traceOf] using hpartition)
      hfirst_le
      (by
        intro sequence hfeasible i hidx candidate hactive
        simpa [removedPrefix, hfeasible, traceOf, strictSupportCount] using
          htransfer_le sequence hfeasible i hidx candidate hactive)

/--
Proposition 3.4 canonical-profile route where the per-step first-choice cap is
derived from a global top-first-choice bound over the candidate set.  The
canonical replay keeps every pre-active candidate inside the initial active
set, so an initial-active subset proof reduces the indexed first-choice
premise to the paper's global `topFirstChoice` convention.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceInequalities_transferBound_and_canonicalProfileInitialActiveRemovedPrefix_globalFirstChoiceCap
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder lossSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {lossTransfers : RCVSequence → List ℕ}
    {lossGroup initialActive : RCVSequence → Finset Candidate}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hselected_candidate :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈ candidates)
    (hselected_quota :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            quota ≤ assignedBudget sequence candidate +
              strictSupportCount voters ballots candidates
                (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref)
                candidate)
    (hloss_source_nodup :
      ∀ sequence, feasibleSequence sequence →
        (lossSourceOrder sequence).Nodup)
    (hloss_source_mem :
      ∀ sequence, feasibleSequence sequence →
        ∀ candidate, candidate ∈ lossSourceOrder sequence →
          candidate ∈
            predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold)
    (htransfer_length :
      ∀ sequence, feasibleSequence sequence →
        (lossTransfers sequence).length = (lossSourceOrder sequence).length)
    (hlower_transfer :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          predictLossesTransferInitialLossBound topFirstChoice quota
            (lossTransfers sequence))
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence =
          rcvSequenceFromTrace
            (canonicalProfileGroupEliminationGeneratedTrace voters ballots
              (lossGroup sequence)
              ((initialActive sequence ∩ lossGroup sequence).card)
              (initialActive sequence)))
    (hlower_rounds :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          (initialActive sequence ∩ lossGroup sequence).card)
    (hinitialActive_subset_candidates :
      ∀ sequence, feasibleSequence sequence →
        initialActive sequence ⊆ candidates)
    (hfirst_choice_initial :
      ∀ sequence, feasibleSequence sequence →
        ∀ voter, voter ∈ voters →
          Ballot.firstChoiceIn (ballots voter) (initialActive sequence))
    (hglobal_first_le :
      ∀ candidate, candidate ∈ candidates →
        Ballot.firstChoiceCount voters ballots candidate ≤ topFirstChoice)
    (htop_lt_quota : topFirstChoice < quota)
    (htransfer_le :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses,
          ∀ hidx :
            i.1 <
              (canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.length,
          ∀ candidate,
            candidate ∈
              ((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.get ⟨i.1, hidx⟩).beforeActive →
          strictSupportCount voters ballots
              (initialActive sequence \
                (((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                  (lossGroup sequence)
                  ((initialActive sequence ∩ lossGroup sequence).card)
                  (initialActive sequence)).steps.get
                  ⟨i.1, hidx⟩).beforeActive))
              ((((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.get
                ⟨i.1, hidx⟩).beforeActive).erase candidate) candidate ≤
            ((lossTransfers sequence).take i.1).sum) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota lowerInitialLosses
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  refine
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceInequalities_transferBound_and_canonicalProfileInitialActiveRemovedPrefix
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (lossSourceOrder := lossSourceOrder)
      (assignedBudget := assignedBudget)
      (lossTransfers := lossTransfers)
      (lossGroup := lossGroup)
      (initialActive := initialActive)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (lowerInitialLosses := lowerInitialLosses)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwinCount_source_eq
      hassignedBudget_source_le hsupport_source_le hselected_candidate
      hselected_quota hloss_source_nodup hloss_source_mem htransfer_length
      hlower_transfer hsequence_eq hlower_rounds hfirst_choice_initial
      htop_lt_quota ?_ htransfer_le
  intro sequence hfeasible i hidx candidate hactive
  have hmem :
      (canonicalProfileGroupEliminationGeneratedTrace voters ballots
        (lossGroup sequence)
        ((initialActive sequence ∩ lossGroup sequence).card)
        (initialActive sequence)).steps.get ⟨i.1, hidx⟩ ∈
      (canonicalProfileGroupEliminationGeneratedTrace voters ballots
        (lossGroup sequence)
        ((initialActive sequence ∩ lossGroup sequence).card)
        (initialActive sequence)).steps :=
    List.get_mem
      (canonicalProfileGroupEliminationGeneratedTrace voters ballots
        (lossGroup sequence)
        ((initialActive sequence ∩ lossGroup sequence).card)
        (initialActive sequence)).steps ⟨i.1, hidx⟩
  have hcandidate_initial :
      candidate ∈ initialActive sequence :=
    minimalGroupEliminationGeneratedSteps_beforeActive_subset_initial
      (MinimalTallyChoiceRule.canonical Candidate) (lossGroup sequence)
      (profileActiveTallyOf voters ballots)
      ((initialActive sequence ∩ lossGroup sequence).card)
      (initialActive sequence)
      ((canonicalProfileGroupEliminationGeneratedTrace voters ballots
        (lossGroup sequence)
        ((initialActive sequence ∩ lossGroup sequence).card)
        (initialActive sequence)).steps.get ⟨i.1, hidx⟩)
      (by
        simpa [canonicalProfileGroupEliminationGeneratedTrace,
          canonicalProfileGroupEliminationGeneratedSteps] using hmem)
      hactive
  exact
    hglobal_first_le candidate
      ((hinitialActive_subset_candidates sequence hfeasible)
        hcandidate_initial)

/--
Finite checker for the remaining Algorithm 7 transfer-prefix source-run fact
in the canonical-profile Proposition 3.4 route.  For every feasible sequence
listed in `allSequences`, every checked initial-loss index, and every active
candidate at that generated step, the removed-prefix strict-support count is
bounded by the corresponding Predict-Losses transfer prefix.

This is an executable-shaped rendering of the source convention that
Algorithm 7's sorted transfer list accounts for all support that can have
arrived from the already removed initial-loss prefix.
-/
noncomputable def proposition3_4_canonicalProfileTransferPrefixCheck
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {feasibleSequence : Sequence → Prop} [DecidablePred feasibleSequence]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (sourceSequences : List Sequence)
    (lossTransfers : Sequence → List ℕ)
    (lossGroup initialActive : Sequence → Finset Candidate)
    (lowerInitialLosses : ℕ) : Bool :=
  sourceSequences.all fun sequence =>
    if feasibleSequence sequence then
      (List.range lowerInitialLosses).all fun idx =>
        match
          (canonicalProfileGroupEliminationGeneratedTrace voters ballots
            (lossGroup sequence)
            ((initialActive sequence ∩ lossGroup sequence).card)
            (initialActive sequence)).steps[idx]?
        with
        | none => false
        | some step =>
            decide
              (∀ candidate, candidate ∈ step.beforeActive →
                strictSupportCount voters ballots
                    (initialActive sequence \ step.beforeActive)
                    (step.beforeActive.erase candidate) candidate ≤
                  ((lossTransfers sequence).take idx).sum)
    else
      true

/--
Completeness for the canonical-profile transfer-prefix checker: if the
generated traces are long enough for the checked prefix and every checked
active candidate satisfies the source transfer-prefix bound, then the
executable finite checker succeeds.
-/
theorem proposition3_4_canonicalProfileTransferPrefixCheck_eq_true_of_facts
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {feasibleSequence : Sequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {sourceSequences : List Sequence}
    {lossTransfers : Sequence → List ℕ}
    {lossGroup initialActive : Sequence → Finset Candidate}
    {lowerInitialLosses : ℕ}
    (hprefix_len :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        lowerInitialLosses ≤
          (canonicalProfileGroupEliminationGeneratedTrace voters ballots
            (lossGroup sequence)
            ((initialActive sequence ∩ lossGroup sequence).card)
            (initialActive sequence)).steps.length)
    (hprefix_bound :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        ∀ i : Fin lowerInitialLosses,
          ∀ hidx :
            i.1 <
              (canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.length,
          ∀ candidate,
            candidate ∈
              ((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.get ⟨i.1, hidx⟩).beforeActive →
            strictSupportCount voters ballots
                (initialActive sequence \
                  (((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                    (lossGroup sequence)
                    ((initialActive sequence ∩ lossGroup sequence).card)
                    (initialActive sequence)).steps.get
                    ⟨i.1, hidx⟩).beforeActive))
                ((((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                  (lossGroup sequence)
                  ((initialActive sequence ∩ lossGroup sequence).card)
                  (initialActive sequence)).steps.get
                  ⟨i.1, hidx⟩).beforeActive).erase candidate) candidate ≤
              ((lossTransfers sequence).take i.1).sum) :
    proposition3_4_canonicalProfileTransferPrefixCheck
        (feasibleSequence := feasibleSequence) voters ballots sourceSequences
        lossTransfers lossGroup initialActive lowerInitialLosses = true := by
  classical
  apply List.all_eq_true.mpr
  intro sequence hsequence
  by_cases hfeasible : feasibleSequence sequence
  · let trace :=
      canonicalProfileGroupEliminationGeneratedTrace voters ballots
        (lossGroup sequence)
        ((initialActive sequence ∩ lossGroup sequence).card)
        (initialActive sequence)
    have hlen : lowerInitialLosses ≤ trace.steps.length := by
      simpa [trace] using hprefix_len sequence hsequence hfeasible
    have hrange_all :
        ((List.range lowerInitialLosses).all fun idx =>
          match trace.steps[idx]? with
          | none => false
          | some step =>
              decide
                (∀ candidate, candidate ∈ step.beforeActive →
                  strictSupportCount voters ballots
                      (initialActive sequence \ step.beforeActive)
                      (step.beforeActive.erase candidate) candidate ≤
                    ((lossTransfers sequence).take idx).sum)) = true := by
      apply List.all_eq_true.mpr
      intro idx hidx_range
      have hidx_lt : idx < lowerInitialLosses := by
        simpa using hidx_range
      have hidx_trace : idx < trace.steps.length :=
        Nat.lt_of_lt_of_le hidx_lt hlen
      have hsome :
          trace.steps[idx]? =
            some (trace.steps.get ⟨idx, hidx_trace⟩) := by
        simpa using
          (List.getElem?_eq_getElem (l := trace.steps) (i := idx)
            hidx_trace)
      have hdec :
          decide
            (∀ candidate,
              candidate ∈ (trace.steps.get ⟨idx, hidx_trace⟩).beforeActive →
                strictSupportCount voters ballots
                    (initialActive sequence \
                      (trace.steps.get ⟨idx, hidx_trace⟩).beforeActive)
                    ((trace.steps.get ⟨idx, hidx_trace⟩).beforeActive.erase
                      candidate) candidate ≤
                  ((lossTransfers sequence).take idx).sum) = true := by
        apply decide_eq_true_iff.mpr
        intro candidate hactive
        exact
          hprefix_bound sequence hsequence hfeasible ⟨idx, hidx_lt⟩
            (by simpa [trace] using hidx_trace) candidate
            (by simpa [trace] using hactive)
      simpa [hsome] using hdec
    simpa [proposition3_4_canonicalProfileTransferPrefixCheck, hfeasible,
      trace] using hrange_all
  · simp [hfeasible]

/--
A successful finite transfer-prefix checker supplies the transfer-prefix
premise used by the canonical-profile Proposition 3.4 proof route.
-/
theorem proposition3_4_transferPrefixCheck_eq_true_iff
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {feasibleSequence : Sequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {sourceSequences : List Sequence}
    {lossTransfers : Sequence → List ℕ}
    {lossGroup initialActive : Sequence → Finset Candidate}
    {lowerInitialLosses : ℕ}
    (hcheck :
      proposition3_4_canonicalProfileTransferPrefixCheck
        (feasibleSequence := feasibleSequence) voters ballots
        sourceSequences lossTransfers lossGroup initialActive lowerInitialLosses =
        true) :
    ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
      ∀ i : Fin lowerInitialLosses,
        ∀ hidx :
          i.1 <
            (canonicalProfileGroupEliminationGeneratedTrace voters ballots
              (lossGroup sequence)
              ((initialActive sequence ∩ lossGroup sequence).card)
              (initialActive sequence)).steps.length,
        ∀ candidate,
          candidate ∈
            ((canonicalProfileGroupEliminationGeneratedTrace voters ballots
              (lossGroup sequence)
              ((initialActive sequence ∩ lossGroup sequence).card)
              (initialActive sequence)).steps.get ⟨i.1, hidx⟩).beforeActive →
          strictSupportCount voters ballots
              (initialActive sequence \
                (((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                  (lossGroup sequence)
                  ((initialActive sequence ∩ lossGroup sequence).card)
                  (initialActive sequence)).steps.get
                  ⟨i.1, hidx⟩).beforeActive))
              ((((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.get
                ⟨i.1, hidx⟩).beforeActive).erase candidate) candidate ≤
            ((lossTransfers sequence).take i.1).sum := by
  classical
  intro sequence hsequence hfeasible i hidx candidate hactive
  let trace :=
    canonicalProfileGroupEliminationGeneratedTrace voters ballots
      (lossGroup sequence)
      ((initialActive sequence ∩ lossGroup sequence).card)
      (initialActive sequence)
  have hseq_all :
      (if feasibleSequence sequence then
        (List.range lowerInitialLosses).all fun idx =>
          match trace.steps[idx]? with
          | none => false
          | some step =>
              decide
                (∀ candidate, candidate ∈ step.beforeActive →
                  strictSupportCount voters ballots
                      (initialActive sequence \ step.beforeActive)
                      (step.beforeActive.erase candidate) candidate ≤
                    ((lossTransfers sequence).take idx).sum)
      else
        true) = true := by
    have hall := List.all_eq_true.mp hcheck
    exact hall sequence hsequence
  have hidx_all :
      (match trace.steps[i.1]? with
      | none => false
      | some step =>
          decide
            (∀ candidate, candidate ∈ step.beforeActive →
              strictSupportCount voters ballots
                  (initialActive sequence \ step.beforeActive)
                  (step.beforeActive.erase candidate) candidate ≤
                ((lossTransfers sequence).take i.1).sum)) = true := by
    have hseq_all' :
        ((List.range lowerInitialLosses).all fun idx =>
          match trace.steps[idx]? with
          | none => false
          | some step =>
              decide
                (∀ candidate, candidate ∈ step.beforeActive →
                  strictSupportCount voters ballots
                      (initialActive sequence \ step.beforeActive)
                      (step.beforeActive.erase candidate) candidate ≤
                    ((lossTransfers sequence).take idx).sum)) = true := by
      simpa [proposition3_4_canonicalProfileTransferPrefixCheck, trace,
        hfeasible] using hseq_all
    exact (List.all_eq_true.mp hseq_all') i.1 (by simp [i.2])
  have hstep_some :
      trace.steps[i.1]? =
        some (trace.steps.get ⟨i.1, hidx⟩) := by
    simpa using
      (List.getElem?_eq_getElem (l := trace.steps) (i := i.1) hidx)
  have hcandidate_all :
      (decide
        (∀ candidate, candidate ∈ (trace.steps.get ⟨i.1, hidx⟩).beforeActive →
          strictSupportCount voters ballots
              (initialActive sequence \
                (trace.steps.get ⟨i.1, hidx⟩).beforeActive)
              ((trace.steps.get ⟨i.1, hidx⟩).beforeActive.erase candidate)
              candidate ≤
            ((lossTransfers sequence).take i.1).sum)) = true := by
    simpa [hstep_some] using hidx_all
  exact (decide_eq_true_iff.mp hcandidate_all) candidate hactive

/--
Finset-backed version of the canonical-profile transfer-prefix checker.  This
is the endpoint to use when the source sequence family is already represented
by the finite `allSequences` set used by the coverage algorithm.
-/
noncomputable def proposition3_4_canonicalProfileTransferPrefixCheckOnFinset
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {feasibleSequence : Sequence → Prop} [DecidablePred feasibleSequence]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (sourceSequences : Finset Sequence)
    (lossTransfers : Sequence → List ℕ)
    (lossGroup initialActive : Sequence → Finset Candidate)
    (lowerInitialLosses : ℕ) : Bool :=
  proposition3_4_canonicalProfileTransferPrefixCheck
    (feasibleSequence := feasibleSequence) voters ballots sourceSequences.toList
    lossTransfers lossGroup initialActive lowerInitialLosses

/-- Finset-backed completeness for the canonical-profile transfer-prefix checker. -/
theorem proposition3_4_canonicalProfileTransferPrefixCheckOnFinset_eq_true_of_facts
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {feasibleSequence : Sequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {sourceSequences : Finset Sequence}
    {lossTransfers : Sequence → List ℕ}
    {lossGroup initialActive : Sequence → Finset Candidate}
    {lowerInitialLosses : ℕ}
    (hprefix_len :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        lowerInitialLosses ≤
          (canonicalProfileGroupEliminationGeneratedTrace voters ballots
            (lossGroup sequence)
            ((initialActive sequence ∩ lossGroup sequence).card)
            (initialActive sequence)).steps.length)
    (hprefix_bound :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        ∀ i : Fin lowerInitialLosses,
          ∀ hidx :
            i.1 <
              (canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.length,
          ∀ candidate,
            candidate ∈
              ((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.get ⟨i.1, hidx⟩).beforeActive →
            strictSupportCount voters ballots
                (initialActive sequence \
                  (((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                    (lossGroup sequence)
                    ((initialActive sequence ∩ lossGroup sequence).card)
                    (initialActive sequence)).steps.get
                    ⟨i.1, hidx⟩).beforeActive))
                ((((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                  (lossGroup sequence)
                  ((initialActive sequence ∩ lossGroup sequence).card)
                  (initialActive sequence)).steps.get
                  ⟨i.1, hidx⟩).beforeActive).erase candidate) candidate ≤
              ((lossTransfers sequence).take i.1).sum) :
    proposition3_4_canonicalProfileTransferPrefixCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots sourceSequences
        lossTransfers lossGroup initialActive lowerInitialLosses = true := by
  exact
    proposition3_4_canonicalProfileTransferPrefixCheck_eq_true_of_facts
      (feasibleSequence := feasibleSequence)
      (voters := voters)
      (ballots := ballots)
      (sourceSequences := sourceSequences.toList)
      (lossTransfers := lossTransfers)
      (lossGroup := lossGroup)
      (initialActive := initialActive)
      (lowerInitialLosses := lowerInitialLosses)
      (by
        intro sequence hsequence hfeasible
        exact hprefix_len sequence (Finset.mem_toList.mp hsequence) hfeasible)
      (by
        intro sequence hsequence hfeasible i hidx candidate hactive
        exact
          hprefix_bound sequence (Finset.mem_toList.mp hsequence) hfeasible
            i hidx candidate hactive)

/--
Canonical-profile transfer-prefix accounting from singleton-origin transfer
caps.  This bridges Algorithm 7's source convention, where transferable mass is
computed candidate-by-candidate, to the proof obligation that speaks about all
already removed initial-loss candidates as one source set.
-/
theorem canonicalProfile_transfer_prefix_bound_of_singleton_transfer_caps
    {Voter Candidate Sequence : Type*} [DecidableEq Voter]
    [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {lossTransfers : Sequence → List ℕ}
    {lossGroup initialActive : Sequence → Finset Candidate}
    {transferOf : Sequence → Candidate → ℕ}
    {lowerInitialLosses : ℕ}
    (hsingleton_transfer :
      ∀ sequence,
        ∀ i : Fin lowerInitialLosses,
          ∀ hidx :
            i.1 <
              (canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.length,
          ∀ candidate,
            candidate ∈
              ((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.get ⟨i.1, hidx⟩).beforeActive →
          ∀ source,
            source ∈
              initialActive sequence \
                (((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                  (lossGroup sequence)
                  ((initialActive sequence ∩ lossGroup sequence).card)
                  (initialActive sequence)).steps.get
                  ⟨i.1, hidx⟩).beforeActive) →
            strictSupportCount voters ballots {source}
                ((((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                  (lossGroup sequence)
                  ((initialActive sequence ∩ lossGroup sequence).card)
                  (initialActive sequence)).steps.get
                  ⟨i.1, hidx⟩).beforeActive).erase candidate) candidate ≤
              transferOf sequence source)
    (htransfer_sum :
      ∀ sequence,
        ∀ i : Fin lowerInitialLosses,
          ∀ hidx :
            i.1 <
              (canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.length,
          ∀ candidate,
            candidate ∈
              ((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.get ⟨i.1, hidx⟩).beforeActive →
            (∑ source ∈
                initialActive sequence \
                  (((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                    (lossGroup sequence)
                    ((initialActive sequence ∩ lossGroup sequence).card)
                    (initialActive sequence)).steps.get
                    ⟨i.1, hidx⟩).beforeActive),
                transferOf sequence source) ≤
              ((lossTransfers sequence).take i.1).sum) :
    ∀ sequence,
      ∀ i : Fin lowerInitialLosses,
        ∀ hidx :
          i.1 <
            (canonicalProfileGroupEliminationGeneratedTrace voters ballots
              (lossGroup sequence)
              ((initialActive sequence ∩ lossGroup sequence).card)
              (initialActive sequence)).steps.length,
        ∀ candidate,
          candidate ∈
            ((canonicalProfileGroupEliminationGeneratedTrace voters ballots
              (lossGroup sequence)
              ((initialActive sequence ∩ lossGroup sequence).card)
              (initialActive sequence)).steps.get ⟨i.1, hidx⟩).beforeActive →
          strictSupportCount voters ballots
              (initialActive sequence \
                (((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                  (lossGroup sequence)
                  ((initialActive sequence ∩ lossGroup sequence).card)
                  (initialActive sequence)).steps.get
                  ⟨i.1, hidx⟩).beforeActive))
              ((((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.get
                ⟨i.1, hidx⟩).beforeActive).erase candidate) candidate ≤
            ((lossTransfers sequence).take i.1).sum := by
  intro sequence i hidx candidate hactive
  let step :=
    (canonicalProfileGroupEliminationGeneratedTrace voters ballots
      (lossGroup sequence)
      ((initialActive sequence ∩ lossGroup sequence).card)
      (initialActive sequence)).steps.get ⟨i.1, hidx⟩
  let removed := initialActive sequence \ step.beforeActive
  let blockers := step.beforeActive.erase candidate
  calc
    strictSupportCount voters ballots removed blockers candidate ≤
        ∑ source ∈ removed,
          strictSupportCount voters ballots {source} blockers candidate :=
      Ballot.strictSupportCount_le_sum_singleton_sources voters ballots
        removed blockers candidate
    _ ≤ ∑ source ∈ removed, transferOf sequence source := by
      exact Finset.sum_le_sum (by
        intro source hsource
        exact
          hsingleton_transfer sequence i hidx candidate
            (by simpa [step] using hactive) source
            (by simpa [removed, step] using hsource))
    _ ≤ ((lossTransfers sequence).take i.1).sum := by
      simpa [removed, step] using
        htransfer_sum sequence i hidx candidate hactive

/--
For a generated canonical loss-order trace, the candidates removed before
indexed step `i` fit inside the first `i` source-loss-order entries whenever
the Predict-Losses transfer bound is long enough for the checked prefix.
-/
theorem canonicalProfile_removed_card_le_loss_order_prefix_card_of_transfer_bound
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {lossOrder : List Candidate} {lossTransfers : List ℕ}
    {transferOf : Candidate → ℕ}
    {topFirstChoice quota lowerInitialLosses : ℕ}
    (hloss_nodup : lossOrder.Nodup)
    (htransfers_eq : lossTransfers = lossOrder.map transferOf)
    (hlower :
      lowerInitialLosses ≤
        predictLossesTransferInitialLossBound topFirstChoice quota
          lossTransfers)
    (i : Fin lowerInitialLosses)
    (hidx :
      i.1 <
        (canonicalProfileGroupEliminationGeneratedTrace voters ballots
          lossOrder.toFinset ((candidates ∩ lossOrder.toFinset).card)
          candidates).steps.length)
    (candidate : Candidate)
    (hactive :
      candidate ∈
        ((canonicalProfileGroupEliminationGeneratedTrace voters ballots
          lossOrder.toFinset ((candidates ∩ lossOrder.toFinset).card)
          candidates).steps.get ⟨i.1, hidx⟩).beforeActive) :
    (candidates \
      (((canonicalProfileGroupEliminationGeneratedTrace voters ballots
        lossOrder.toFinset ((candidates ∩ lossOrder.toFinset).card)
        candidates).steps.get ⟨i.1, hidx⟩).beforeActive)).card ≤
      (lossOrder.take i.1).toFinset.card := by
  let trace :=
    canonicalProfileGroupEliminationGeneratedTrace voters ballots
      lossOrder.toFinset ((candidates ∩ lossOrder.toFinset).card) candidates
  let step := trace.steps.get ⟨i.1, hidx⟩
  have hbefore_subset : step.beforeActive ⊆ candidates := by
    simpa [trace, step] using
      canonicalProfileGroupEliminationGeneratedTrace_get_beforeActive_subset_initial
        voters ballots lossOrder.toFinset
        ((candidates ∩ lossOrder.toFinset).card) candidates ⟨i.1, hidx⟩
  have hcard_index : step.beforeActive.card + i.1 = candidates.card := by
    simpa [trace, step] using
      canonicalProfileGroupEliminationGeneratedTrace_get_beforeActive_card_add_index
        voters ballots lossOrder.toFinset
        ((candidates ∩ lossOrder.toFinset).card) candidates ⟨i.1, hidx⟩
  have hsdiff_card :
      (candidates \ step.beforeActive).card + step.beforeActive.card =
        candidates.card :=
    Finset.card_sdiff_add_card_eq_card hbefore_subset
  have hsdiff_card_comm :
      step.beforeActive.card + (candidates \ step.beforeActive).card =
        candidates.card := by
    simpa [Nat.add_comm] using hsdiff_card
  have hremoved_card :
      (candidates \ step.beforeActive).card = i.1 := by
    exact Nat.add_left_cancel
      (by
        calc
          step.beforeActive.card + (candidates \ step.beforeActive).card =
              candidates.card := hsdiff_card_comm
          _ = step.beforeActive.card + i.1 := hcard_index.symm)
  have horder_len : i.1 ≤ lossOrder.length := by
    have hbound_len :
        predictLossesTransferInitialLossBound topFirstChoice quota
            lossTransfers ≤
          lossTransfers.length :=
      predictLossesTransferInitialLossBound_le_length topFirstChoice quota
        lossTransfers
    have hbound_order :
        predictLossesTransferInitialLossBound topFirstChoice quota
            lossTransfers ≤
          lossOrder.length := by
      calc
        predictLossesTransferInitialLossBound topFirstChoice quota
            lossTransfers ≤
            lossTransfers.length := hbound_len
        _ = lossOrder.length := by
            rw [htransfers_eq]
            simp
    exact Nat.le_trans (Nat.le_of_lt i.2) (Nat.le_trans hlower hbound_order)
  have hprefix_card : (lossOrder.take i.1).toFinset.card = i.1 := by
    calc
      (lossOrder.take i.1).toFinset.card =
          (lossOrder.take i.1).length :=
            List.toFinset_card_of_nodup hloss_nodup.take
      _ = i.1 := by
            simp [List.length_take, horder_len]
  rw [show
      (candidates \
        (((canonicalProfileGroupEliminationGeneratedTrace voters ballots
          lossOrder.toFinset ((candidates ∩ lossOrder.toFinset).card)
          candidates).steps.get ⟨i.1, hidx⟩).beforeActive)).card =
        (candidates \ step.beforeActive).card by
        simp [trace, step]]
  rw [hremoved_card, hprefix_card]

/--
Transfer-sum bound from a source loss order whose first `i` transfer entries
dominate the removed-prefix sources.  This is the finite exchange step in
Algorithm 7: once `lossTransfers` is the transfer value of the source loss
order, the sorted prefix controls any removed set of no larger cardinality.
-/
theorem canonicalProfile_transfer_sum_bound_of_loss_source_order_prefix_dominance
    {Voter Candidate Sequence : Type*} [DecidableEq Voter]
    [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {lossSourceOrder : Sequence → List Candidate}
    {lossTransfers : Sequence → List ℕ}
    {lossGroup initialActive : Sequence → Finset Candidate}
    {transferOf : Sequence → Candidate → ℕ}
    {lowerInitialLosses : ℕ}
    (hloss_nodup : ∀ sequence, (lossSourceOrder sequence).Nodup)
    (htransfers_eq :
      ∀ sequence, lossTransfers sequence =
        (lossSourceOrder sequence).map (transferOf sequence))
    (hremoved_card_le_prefix :
      ∀ sequence,
        ∀ i : Fin lowerInitialLosses,
          ∀ hidx :
            i.1 <
              (canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.length,
          ∀ candidate,
            candidate ∈
              ((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.get ⟨i.1, hidx⟩).beforeActive →
            (initialActive sequence \
              (((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.get
                ⟨i.1, hidx⟩).beforeActive)).card ≤
              ((lossSourceOrder sequence).take i.1).toFinset.card)
    (hprefix_dominance :
      ∀ sequence,
        ∀ i : Fin lowerInitialLosses,
          ∀ hidx :
            i.1 <
              (canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.length,
          ∀ candidate,
            candidate ∈
              ((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.get ⟨i.1, hidx⟩).beforeActive →
          ∀ source,
            source ∈
              (initialActive sequence \
                (((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                  (lossGroup sequence)
                  ((initialActive sequence ∩ lossGroup sequence).card)
                  (initialActive sequence)).steps.get
                  ⟨i.1, hidx⟩).beforeActive)) \
                ((lossSourceOrder sequence).take i.1).toFinset →
          ∀ prefixSource,
            prefixSource ∈
              ((lossSourceOrder sequence).take i.1).toFinset \
                (initialActive sequence \
                  (((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                    (lossGroup sequence)
                    ((initialActive sequence ∩ lossGroup sequence).card)
                    (initialActive sequence)).steps.get
                    ⟨i.1, hidx⟩).beforeActive)) →
            transferOf sequence source ≤ transferOf sequence prefixSource) :
    ∀ sequence,
      ∀ i : Fin lowerInitialLosses,
        ∀ hidx :
          i.1 <
            (canonicalProfileGroupEliminationGeneratedTrace voters ballots
              (lossGroup sequence)
              ((initialActive sequence ∩ lossGroup sequence).card)
              (initialActive sequence)).steps.length,
        ∀ candidate,
          candidate ∈
            ((canonicalProfileGroupEliminationGeneratedTrace voters ballots
              (lossGroup sequence)
              ((initialActive sequence ∩ lossGroup sequence).card)
              (initialActive sequence)).steps.get ⟨i.1, hidx⟩).beforeActive →
          (∑ source ∈
              initialActive sequence \
                (((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                  (lossGroup sequence)
                  ((initialActive sequence ∩ lossGroup sequence).card)
                  (initialActive sequence)).steps.get
                  ⟨i.1, hidx⟩).beforeActive),
              transferOf sequence source) ≤
            ((lossTransfers sequence).take i.1).sum := by
  intro sequence i hidx candidate hactive
  let trace :=
    canonicalProfileGroupEliminationGeneratedTrace voters ballots
      (lossGroup sequence)
      ((initialActive sequence ∩ lossGroup sequence).card)
      (initialActive sequence)
  let step := trace.steps.get ⟨i.1, hidx⟩
  let removed := initialActive sequence \ step.beforeActive
  have htake_nodup : ((lossSourceOrder sequence).take i.1).Nodup := by
    simpa using (hloss_nodup sequence).take
  have hsum_prefix :
      (∑ source ∈ removed, transferOf sequence source) ≤
        (((lossSourceOrder sequence).take i.1).map
          (transferOf sequence)).sum := by
    exact
      EconCSLib.FiniteSum.nat_finset_sum_le_list_take_map_sum_of_card_le_pairwise_sdiff
        removed (lossSourceOrder sequence) (transferOf sequence) i.1
        htake_nodup
        (by
          simpa [removed, step, trace] using
            hremoved_card_le_prefix sequence i hidx candidate hactive)
        (by
          intro source hsource prefixSource hprefixSource
          exact
            hprefix_dominance sequence i hidx candidate hactive source
              (by simpa [removed, step, trace] using hsource)
              prefixSource
              (by simpa [removed, step, trace] using hprefixSource))
  have htake_sum :
      ((lossTransfers sequence).take i.1).sum =
        (((lossSourceOrder sequence).take i.1).map
          (transferOf sequence)).sum := by
    rw [htransfers_eq sequence]
    simp
  exact by
    simpa [removed, step, trace, htake_sum] using hsum_prefix

/--
A successful Finset-backed transfer-prefix checker supplies the transfer-prefix
premise used by the canonical-profile Proposition 3.4 proof route.
-/
theorem proposition3_4_transferPrefixCheckOnFinset_eq_true_iff
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {feasibleSequence : Sequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {sourceSequences : Finset Sequence}
    {lossTransfers : Sequence → List ℕ}
    {lossGroup initialActive : Sequence → Finset Candidate}
    {lowerInitialLosses : ℕ}
    (hcheck :
      proposition3_4_canonicalProfileTransferPrefixCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots
        sourceSequences lossTransfers lossGroup initialActive lowerInitialLosses =
        true) :
    ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
      ∀ i : Fin lowerInitialLosses,
        ∀ hidx :
          i.1 <
            (canonicalProfileGroupEliminationGeneratedTrace voters ballots
              (lossGroup sequence)
              ((initialActive sequence ∩ lossGroup sequence).card)
              (initialActive sequence)).steps.length,
        ∀ candidate,
          candidate ∈
            ((canonicalProfileGroupEliminationGeneratedTrace voters ballots
              (lossGroup sequence)
              ((initialActive sequence ∩ lossGroup sequence).card)
              (initialActive sequence)).steps.get ⟨i.1, hidx⟩).beforeActive →
          strictSupportCount voters ballots
              (initialActive sequence \
                (((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                  (lossGroup sequence)
                  ((initialActive sequence ∩ lossGroup sequence).card)
                  (initialActive sequence)).steps.get
                  ⟨i.1, hidx⟩).beforeActive))
              ((((canonicalProfileGroupEliminationGeneratedTrace voters ballots
                (lossGroup sequence)
                ((initialActive sequence ∩ lossGroup sequence).card)
                (initialActive sequence)).steps.get
                ⟨i.1, hidx⟩).beforeActive).erase candidate) candidate ≤
            ((lossTransfers sequence).take i.1).sum := by
  intro sequence hsequence hfeasible i hidx candidate hactive
  exact
    proposition3_4_transferPrefixCheck_eq_true_iff
      (feasibleSequence := feasibleSequence)
      (voters := voters)
      (ballots := ballots)
      (sourceSequences := sourceSequences.toList)
      (lossTransfers := lossTransfers)
      (lossGroup := lossGroup)
      (initialActive := initialActive)
      (lowerInitialLosses := lowerInitialLosses)
      (by
        simpa [proposition3_4_canonicalProfileTransferPrefixCheckOnFinset]
          using hcheck)
      sequence (Finset.mem_toList.mpr hsequence) hfeasible i hidx candidate
      hactive

/--
Concrete Proposition 3.4 Algorithm 7 implementation for the literal source
case: Predict-Wins scans one global `C_W` order, Predict-Losses scans one
global sorted `C_L` order with one transfer list `T`, and the retained
lower-initial-loss bound is exactly Algorithm 7's transfer-loop counter.
This removes the generic per-sequence lower-bound premise.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_globalSourceOrders_transferPrefixTallies
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder lossSourceOrder : List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {lossTransfers : List ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = winnerSourceOrder.length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        (winnerSourceOrder.map (assignedBudget sequence)).sum ≤ budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates winnerSourceOrder ≤
          predictedWinSupport)
    (hselected_candidate :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder = pref ++ candidate :: suffix →
            candidate ∈ candidates)
    (hselected_quota :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder = pref ++ candidate :: suffix →
            quota ≤ assignedBudget sequence candidate +
              strictSupportCount voters ballots candidates
                (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref)
                candidate)
    (hloss_source_nodup : lossSourceOrder.Nodup)
    (hloss_source_mem :
      ∀ candidate, candidate ∈ lossSourceOrder →
        candidate ∈
          predictLossesCandidates voters ballots candidates budget
            firstChoiceThreshold)
    (htransfer_length : lossTransfers.length = lossSourceOrder.length)
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        predictLossesTransferInitialLossBound topFirstChoice quota
            lossTransfers ≤
          (traceOf sequence).steps.length)
    (htrace_kind_allowed :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin
          (predictLossesTransferInitialLossBound topFirstChoice quota
            lossTransfers),
          ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).kind =
              StepKind.elect ∨
            ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).kind =
              StepKind.eliminate)
    (helect_quota :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin
          (predictLossesTransferInitialLossBound topFirstChoice quota
            lossTransfers),
          ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).kind =
              StepKind.elect →
            ∃ candidate,
              candidate ∈
                ((traceOf sequence).steps.get
                  ⟨i.1, Nat.lt_of_lt_of_le i.2
                    (htrace_prefix_len sequence hfeasible)⟩).beforeActive ∧
              quota ≤
                ((traceOf sequence).steps.get
                  ⟨i.1, Nat.lt_of_lt_of_le i.2
                    (htrace_prefix_len sequence hfeasible)⟩).tally candidate)
    (htop_lt_quota : topFirstChoice < quota)
    (hactive_tally_le_transfer_prefix :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin
          (predictLossesTransferInitialLossBound topFirstChoice quota
            lossTransfers),
          ∀ candidate,
            candidate ∈
              ((traceOf sequence).steps.get
                ⟨i.1, Nat.lt_of_lt_of_le i.2
                  (htrace_prefix_len sequence hfeasible)⟩).beforeActive →
            ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).tally candidate ≤
              (lossTransfers.take i.1).sum + topFirstChoice) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota
        (predictLossesTransferInitialLossBound topFirstChoice quota
          lossTransfers)
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceInequalities_transferBound_and_transferPrefixTallies
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := fun _ => winnerSourceOrder)
      (lossSourceOrder := fun _ => lossSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (lossTransfers := fun _ => lossTransfers)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (lowerInitialLosses :=
        predictLossesTransferInitialLossBound topFirstChoice quota
          lossTransfers)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwinCount_source_eq
      hassignedBudget_source_le hsupport_source_le hselected_candidate
      hselected_quota
      (fun _ _ => hloss_source_nodup)
      (fun _ _ => hloss_source_mem)
      (fun _ _ => htransfer_length)
      (fun _ _ => le_rfl)
      hsequence_eq htrace_prefix_len htrace_kind_allowed helect_quota
      htop_lt_quota
      (fun sequence hfeasible i candidate hactive =>
        hactive_tally_le_transfer_prefix sequence hfeasible i candidate
          hactive)

/--
Concrete Proposition 3.4 Algorithm 7 implementation from stepwise transfer
tally increments. This is the source-shaped transfer-loop invariant: the first
prefix tally is bounded by the top first-choice count, and each following
prefix step can add at most the corresponding Algorithm 7 transfer amount.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_globalSourceOrders_stepwiseTransferTallies
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder lossSourceOrder : List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {lossTransfers : List ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = winnerSourceOrder.length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        (winnerSourceOrder.map (assignedBudget sequence)).sum ≤ budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates winnerSourceOrder ≤
          predictedWinSupport)
    (hselected_candidate :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder = pref ++ candidate :: suffix →
            candidate ∈ candidates)
    (hselected_quota :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder = pref ++ candidate :: suffix →
            quota ≤ assignedBudget sequence candidate +
              strictSupportCount voters ballots candidates
                (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref)
                candidate)
    (hloss_source_nodup : lossSourceOrder.Nodup)
    (hloss_source_mem :
      ∀ candidate, candidate ∈ lossSourceOrder →
        candidate ∈
          predictLossesCandidates voters ballots candidates budget
            firstChoiceThreshold)
    (htransfer_length : lossTransfers.length = lossSourceOrder.length)
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        predictLossesTransferInitialLossBound topFirstChoice quota
            lossTransfers ≤
          (traceOf sequence).steps.length)
    (htrace_kind_allowed :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin
          (predictLossesTransferInitialLossBound topFirstChoice quota
            lossTransfers),
          ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).kind =
              StepKind.elect ∨
            ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).kind =
              StepKind.eliminate)
    (helect_quota :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin
          (predictLossesTransferInitialLossBound topFirstChoice quota
            lossTransfers),
          ((traceOf sequence).steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2
                (htrace_prefix_len sequence hfeasible)⟩).kind =
              StepKind.elect →
            ∃ candidate,
              candidate ∈
                ((traceOf sequence).steps.get
                  ⟨i.1, Nat.lt_of_lt_of_le i.2
                    (htrace_prefix_len sequence hfeasible)⟩).beforeActive ∧
              quota ≤
                ((traceOf sequence).steps.get
                  ⟨i.1, Nat.lt_of_lt_of_le i.2
                    (htrace_prefix_len sequence hfeasible)⟩).tally candidate)
    (htop_lt_quota : topFirstChoice < quota)
    (hinitial_tally_le_topFirstChoice :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ hpos :
          0 < predictLossesTransferInitialLossBound topFirstChoice quota
            lossTransfers,
        ∀ candidate,
          candidate ∈
            ((traceOf sequence).steps.get
              ⟨0, Nat.lt_of_lt_of_le hpos
                (htrace_prefix_len sequence hfeasible)⟩).beforeActive →
          ((traceOf sequence).steps.get
            ⟨0, Nat.lt_of_lt_of_le hpos
              (htrace_prefix_len sequence hfeasible)⟩).tally candidate ≤
            topFirstChoice)
    (hstep_tally_le_transfer :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ idx,
          ∀ hnext :
            idx + 1 <
              predictLossesTransferInitialLossBound topFirstChoice quota
                lossTransfers,
          ∀ candidate,
            candidate ∈
              ((traceOf sequence).steps.get
                ⟨idx + 1, Nat.lt_of_lt_of_le hnext
                  (htrace_prefix_len sequence hfeasible)⟩).beforeActive →
            ((traceOf sequence).steps.get
              ⟨idx + 1, Nat.lt_of_lt_of_le hnext
                (htrace_prefix_len sequence hfeasible)⟩).tally candidate ≤
              (if candidate ∈
                  ((traceOf sequence).steps.get
                    ⟨idx, Nat.lt_of_lt_of_le
                      (Nat.lt_of_succ_lt hnext)
                      (htrace_prefix_len sequence hfeasible)⟩).beforeActive then
                ((traceOf sequence).steps.get
                  ⟨idx, Nat.lt_of_lt_of_le
                    (Nat.lt_of_succ_lt hnext)
                    (htrace_prefix_len sequence hfeasible)⟩).tally candidate
              else
                0) + lossTransfers.getD idx 0) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota
        (predictLossesTransferInitialLossBound topFirstChoice quota
          lossTransfers)
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  refine
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_globalSourceOrders_transferPrefixTallies
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (lossSourceOrder := lossSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (lossTransfers := lossTransfers)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwinCount_source_eq hassignedBudget_source_le
      hsupport_source_le hselected_candidate hselected_quota
      hloss_source_nodup hloss_source_mem htransfer_length hsequence_eq
      htrace_prefix_len htrace_kind_allowed helect_quota htop_lt_quota ?_
  intro sequence hfeasible i candidate hactive
  have hrange :
      ((traceOf sequence).steps.get
        ⟨i.1, Nat.lt_of_lt_of_le i.2
          (htrace_prefix_len sequence hfeasible)⟩).tally candidate ≤
        topFirstChoice +
          ∑ j ∈ Finset.range i.1, lossTransfers.getD j 0 :=
    rcvTrace_active_tally_le_topFirstChoice_add_transfer_prefix_sum
      (trace := traceOf sequence)
      (prefixLen :=
        predictLossesTransferInitialLossBound topFirstChoice quota
          lossTransfers)
      (topFirstChoice := topFirstChoice)
      (transferAt := fun j => lossTransfers.getD j 0)
      (htrace_prefix_len sequence hfeasible)
      (fun hpos candidate hactive0 =>
        hinitial_tally_le_topFirstChoice sequence hfeasible hpos candidate
          hactive0)
      (fun idx hnext candidate hactive_next =>
        hstep_tally_le_transfer sequence hfeasible idx hnext candidate
          hactive_next)
      i candidate hactive
  have hprefix_sum :=
    EconCSLib.FiniteSum.list_sum_take_eq_sum_range_getD lossTransfers i.1
  have hbound :
      ((traceOf sequence).steps.get
        ⟨i.1, Nat.lt_of_lt_of_le i.2
          (htrace_prefix_len sequence hfeasible)⟩).tally candidate ≤
        topFirstChoice + (lossTransfers.take i.1).sum := by
    rw [← hprefix_sum] at hrange
    exact hrange
  calc
    ((traceOf sequence).steps.get
        ⟨i.1, Nat.lt_of_lt_of_le i.2
          (htrace_prefix_len sequence hfeasible)⟩).tally candidate
        ≤ topFirstChoice + (lossTransfers.take i.1).sum := hbound
    _ = (lossTransfers.take i.1).sum + topFirstChoice := by
      rw [Nat.add_comm]

/--
Concrete Proposition 3.4 Algorithm 7 route from generated STV replay
constraints.  The generated trace supplies the elect/eliminate classification
and the election-quota witness; the caller still supplies the source transfer
tally increments that are specific to Algorithm 7's Predict-Losses loop.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_globalSourceOrders_stepwiseTransferTallies_generatedReplay
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder lossSourceOrder : List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {structureOf : RCVSequence → RCVStructure Candidate}
    {initialActive : RCVSequence → Finset Candidate}
    {tallyOf : RCVSequence → Finset Candidate → Candidate → ℕ}
    {lossTransfers : List ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = winnerSourceOrder.length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        (winnerSourceOrder.map (assignedBudget sequence)).sum ≤ budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates winnerSourceOrder ≤
          predictedWinSupport)
    (hselected_candidate :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder = pref ++ candidate :: suffix →
            candidate ∈ candidates)
    (hselected_quota :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder = pref ++ candidate :: suffix →
            quota ≤ assignedBudget sequence candidate +
              strictSupportCount voters ballots candidates
                (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref)
                candidate)
    (hloss_source_nodup : lossSourceOrder.Nodup)
    (hloss_source_mem :
      ∀ candidate, candidate ∈ lossSourceOrder →
        candidate ∈
          predictLossesCandidates voters ballots candidates budget
            firstChoiceThreshold)
    (htransfer_length : lossTransfers.length = lossSourceOrder.length)
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_generated :
      ∀ sequence, feasibleSequence sequence →
        traceOf sequence =
          rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence))
    (hgenerated_constraints_hold :
      ∀ sequence, feasibleSequence sequence →
        ∀ constraint,
          constraint ∈
            rcvGeneratedStructureRoundConstraints (structureOf sequence)
              (initialActive sequence) (tallyOf sequence) quota →
          constraint.Holds)
    (htrace_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        predictLossesTransferInitialLossBound topFirstChoice quota
            lossTransfers ≤
          (traceOf sequence).steps.length)
    (htop_lt_quota : topFirstChoice < quota)
    (hinitial_tally_le_topFirstChoice :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ hpos :
          0 < predictLossesTransferInitialLossBound topFirstChoice quota
            lossTransfers,
        ∀ candidate,
          candidate ∈
            ((traceOf sequence).steps.get
              ⟨0, Nat.lt_of_lt_of_le hpos
                (htrace_prefix_len sequence hfeasible)⟩).beforeActive →
          ((traceOf sequence).steps.get
            ⟨0, Nat.lt_of_lt_of_le hpos
              (htrace_prefix_len sequence hfeasible)⟩).tally candidate ≤
            topFirstChoice)
    (hstep_tally_le_transfer :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ idx,
          ∀ hnext :
            idx + 1 <
              predictLossesTransferInitialLossBound topFirstChoice quota
                lossTransfers,
          ∀ candidate,
            candidate ∈
              ((traceOf sequence).steps.get
                ⟨idx + 1, Nat.lt_of_lt_of_le hnext
                  (htrace_prefix_len sequence hfeasible)⟩).beforeActive →
            ((traceOf sequence).steps.get
              ⟨idx + 1, Nat.lt_of_lt_of_le hnext
                (htrace_prefix_len sequence hfeasible)⟩).tally candidate ≤
              (if candidate ∈
                  ((traceOf sequence).steps.get
                    ⟨idx, Nat.lt_of_lt_of_le
                      (Nat.lt_of_succ_lt hnext)
                      (htrace_prefix_len sequence hfeasible)⟩).beforeActive then
                ((traceOf sequence).steps.get
                  ⟨idx, Nat.lt_of_lt_of_le
                    (Nat.lt_of_succ_lt hnext)
                    (htrace_prefix_len sequence hfeasible)⟩).tally candidate
              else
                0) + lossTransfers.getD idx 0) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota
        (predictLossesTransferInitialLossBound topFirstChoice quota
          lossTransfers)
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  refine
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_globalSourceOrders_stepwiseTransferTallies
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (lossSourceOrder := lossSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (lossTransfers := lossTransfers)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwinCount_source_eq
      hassignedBudget_source_le hsupport_source_le hselected_candidate
      hselected_quota hloss_source_nodup hloss_source_mem htransfer_length
      hsequence_eq htrace_prefix_len ?_ ?_ htop_lt_quota
      hinitial_tally_le_topFirstChoice hstep_tally_le_transfer
  · intro sequence hfeasible i
    let j :
        Fin
          (rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)).steps.length :=
      ⟨i.1, by
        simpa [htrace_generated sequence hfeasible] using
          Nat.lt_of_lt_of_le i.2 (htrace_prefix_len sequence hfeasible)⟩
    simpa [rcvGeneratedTraceOfStructure, htrace_generated sequence hfeasible]
      using
        (OrderSequenceStructure.generatedTrace_kind_elect_or_eliminate
          (structureOf sequence) (initialActive sequence) (tallyOf sequence) j)
  · intro sequence hfeasible i helect
    let j :
        Fin
          (rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)).steps.length :=
      ⟨i.1, by
        simpa [htrace_generated sequence hfeasible] using
          Nat.lt_of_lt_of_le i.2 (htrace_prefix_len sequence hfeasible)⟩
    have helect_generated :
        ((rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)).steps.get j).kind =
          StepKind.elect := by
      simpa [rcvGeneratedTraceOfStructure, htrace_generated sequence hfeasible]
        using helect
    have hholds :
        ∀ constraint,
          constraint ∈
            OrderSequenceStructure.generatedConstraints (structureOf sequence)
              (initialActive sequence) (tallyOf sequence) quota →
          constraint.Holds := by
      intro constraint hconstraint
      exact hgenerated_constraints_hold sequence hfeasible constraint
        (by simpa [rcvGeneratedStructureRoundConstraints] using hconstraint)
    simpa [rcvGeneratedTraceOfStructure, htrace_generated sequence hfeasible]
      using
        (OrderSequenceStructure.generatedConstraints_elect_quota_of_generatedTrace
          (structureOf sequence) (initialActive sequence) (tallyOf sequence)
          quota hholds j helect_generated)

/--
Concrete Proposition 3.4 Algorithm 7 route from generated STV replay data and
source transfer-prefix tally bounds.  The generated replay supplies the
elect/eliminate classification, election-quota witness, and the trace tally
formula, so callers state the transfer-loop invariant directly over the
generated active sets.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceInequalities_transferBound_and_generatedReplayTransferPrefixTallies
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder lossSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {structureOf : RCVSequence → RCVStructure Candidate}
    {initialActive : RCVSequence → Finset Candidate}
    {tallyOf : RCVSequence → Finset Candidate → Candidate → ℕ}
    {lossTransfers : RCVSequence → List ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hselected_candidate :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈ candidates)
    (hselected_quota :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            quota ≤ assignedBudget sequence candidate +
              strictSupportCount voters ballots candidates
                (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref)
                candidate)
    (hloss_source_nodup :
      ∀ sequence, feasibleSequence sequence →
        (lossSourceOrder sequence).Nodup)
    (hloss_source_mem :
      ∀ sequence, feasibleSequence sequence →
        ∀ candidate, candidate ∈ lossSourceOrder sequence →
          candidate ∈
            predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold)
    (htransfer_length :
      ∀ sequence, feasibleSequence sequence →
        (lossTransfers sequence).length = (lossSourceOrder sequence).length)
    (hlower_transfer :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          predictLossesTransferInitialLossBound topFirstChoice quota
            (lossTransfers sequence))
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_generated :
      ∀ sequence, feasibleSequence sequence →
        traceOf sequence =
          rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence))
    (hgenerated_constraints_hold :
      ∀ sequence, feasibleSequence sequence →
        ∀ constraint,
          constraint ∈
            rcvGeneratedStructureRoundConstraints (structureOf sequence)
              (initialActive sequence) (tallyOf sequence) quota →
          constraint.Holds)
    (hgenerated_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          (rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)).steps.length)
    (htop_lt_quota : topFirstChoice < quota)
    (hgenerated_active_tally_le_transfer_prefix :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses,
          ∀ candidate,
            candidate ∈
              ((rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence) (tallyOf sequence)).steps.get
                ⟨i.1, Nat.lt_of_lt_of_le i.2
                  (hgenerated_prefix_len sequence hfeasible)⟩).beforeActive →
            (tallyOf sequence
              (((rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence) (tallyOf sequence)).steps.get
                ⟨i.1, Nat.lt_of_lt_of_le i.2
                  (hgenerated_prefix_len sequence hfeasible)⟩).beforeActive))
                candidate ≤
              ((lossTransfers sequence).take i.1).sum + topFirstChoice) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota lowerInitialLosses
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  refine
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceInequalities_transferBound_and_transferPrefixTallies
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (lossSourceOrder := lossSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (lossTransfers := lossTransfers)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (lowerInitialLosses := lowerInitialLosses)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwinCount_source_eq
      hassignedBudget_source_le hsupport_source_le hselected_candidate
      hselected_quota hloss_source_nodup hloss_source_mem htransfer_length
      hlower_transfer hsequence_eq ?_ ?_ ?_ htop_lt_quota ?_
  · intro sequence hfeasible
    simpa [htrace_generated sequence hfeasible] using
      hgenerated_prefix_len sequence hfeasible
  · intro sequence hfeasible i
    let j :
        Fin
          (rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)).steps.length :=
      ⟨i.1, Nat.lt_of_lt_of_le i.2
        (hgenerated_prefix_len sequence hfeasible)⟩
    simpa [rcvGeneratedTraceOfStructure, htrace_generated sequence hfeasible]
      using
        (OrderSequenceStructure.generatedTrace_kind_elect_or_eliminate
          (structureOf sequence) (initialActive sequence) (tallyOf sequence) j)
  · intro sequence hfeasible i helect
    let j :
        Fin
          (rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)).steps.length :=
      ⟨i.1, Nat.lt_of_lt_of_le i.2
        (hgenerated_prefix_len sequence hfeasible)⟩
    have helect_generated :
        ((rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)).steps.get j).kind =
          StepKind.elect := by
      simpa [rcvGeneratedTraceOfStructure, htrace_generated sequence hfeasible]
        using helect
    have hholds :
        ∀ constraint,
          constraint ∈
            OrderSequenceStructure.generatedConstraints (structureOf sequence)
              (initialActive sequence) (tallyOf sequence) quota →
          constraint.Holds := by
      intro constraint hconstraint
      exact hgenerated_constraints_hold sequence hfeasible constraint
        (by simpa [rcvGeneratedStructureRoundConstraints] using hconstraint)
    simpa [rcvGeneratedTraceOfStructure, htrace_generated sequence hfeasible]
      using
        (OrderSequenceStructure.generatedConstraints_elect_quota_of_generatedTrace
          (structureOf sequence) (initialActive sequence) (tallyOf sequence)
          quota hholds j helect_generated)
  · intro sequence hfeasible i candidate hactive
    let j :
        Fin
          (rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)).steps.length :=
      ⟨i.1, Nat.lt_of_lt_of_le i.2
        (hgenerated_prefix_len sequence hfeasible)⟩
    have htally_eq :
        ((rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)).steps.get j).tally =
          tallyOf sequence
            (((rcvGeneratedTraceOfStructure (structureOf sequence)
              (initialActive sequence) (tallyOf sequence)).steps.get j).beforeActive) := by
      simpa [rcvGeneratedTraceOfStructure] using
        (OrderSequenceStructure.generatedTrace_tally_eq
          (structureOf sequence) (initialActive sequence) (tallyOf sequence) j)
    have hactive_generated :
        candidate ∈
          ((rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)).steps.get j).beforeActive := by
      simpa [rcvGeneratedTraceOfStructure, htrace_generated sequence hfeasible]
        using hactive
    have hbound :=
      hgenerated_active_tally_le_transfer_prefix sequence hfeasible i
        candidate hactive_generated
    have hbound' :
        ((rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)).steps.get j).tally
            candidate ≤
          ((lossTransfers sequence).take i.1).sum + topFirstChoice := by
      rw [htally_eq]
      simpa [j] using hbound
    simpa [rcvGeneratedTraceOfStructure, htrace_generated sequence hfeasible,
      j] using hbound'

/--
Concrete Proposition 3.4 generated-replay route with the generated prefix length
derived from the structure's order and win/loss label lengths.  The active-set
transfer tally premise is indexed by any proof that the generated step exists,
which keeps callers from depending on a particular `Fin` proof term.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceInequalities_transferBound_and_generatedStructureTransferPrefixTallies
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder lossSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {structureOf : RCVSequence → RCVStructure Candidate}
    {initialActive : RCVSequence → Finset Candidate}
    {tallyOf : RCVSequence → Finset Candidate → Candidate → ℕ}
    {lossTransfers : RCVSequence → List ℕ}
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hselected_candidate :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈ candidates)
    (hselected_quota :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            quota ≤ assignedBudget sequence candidate +
              strictSupportCount voters ballots candidates
                (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref)
                candidate)
    (hloss_source_nodup :
      ∀ sequence, feasibleSequence sequence →
        (lossSourceOrder sequence).Nodup)
    (hloss_source_mem :
      ∀ sequence, feasibleSequence sequence →
        ∀ candidate, candidate ∈ lossSourceOrder sequence →
          candidate ∈
            predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold)
    (htransfer_length :
      ∀ sequence, feasibleSequence sequence →
        (lossTransfers sequence).length = (lossSourceOrder sequence).length)
    (hlower_transfer :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          predictLossesTransferInitialLossBound topFirstChoice quota
            (lossTransfers sequence))
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_generated :
      ∀ sequence, feasibleSequence sequence →
        traceOf sequence =
          rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence))
    (hgenerated_constraints_hold :
      ∀ sequence, feasibleSequence sequence →
        ∀ constraint,
          constraint ∈
            rcvGeneratedStructureRoundConstraints (structureOf sequence)
              (initialActive sequence) (tallyOf sequence) quota →
          constraint.Holds)
    (hgenerated_order_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ (structureOf sequence).finalOrder.order.length)
    (hgenerated_sequence_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ (structureOf sequence).sequence.length)
    (htop_lt_quota : topFirstChoice < quota)
    (hgenerated_active_tally_le_transfer_prefix :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses,
          ∀ hidx :
            i.1 <
              (rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence) (tallyOf sequence)).steps.length,
          ∀ candidate,
            candidate ∈
              ((rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence) (tallyOf sequence)).steps.get
                ⟨i.1, hidx⟩).beforeActive →
            (tallyOf sequence
              (((rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence) (tallyOf sequence)).steps.get
                ⟨i.1, hidx⟩).beforeActive)) candidate ≤
              ((lossTransfers sequence).take i.1).sum + topFirstChoice) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota lowerInitialLosses
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  let generatedPrefixLength :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          (rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)).steps.length :=
    fun sequence hfeasible => by
      simpa [rcvGeneratedTraceOfStructure] using
        (OrderSequenceStructure.le_generatedTrace_steps_length_of_le_order_length_of_le_sequence_length
          (struct := structureOf sequence)
          (initialActive := initialActive sequence)
          (tallyOf := tallyOf sequence)
          (hgenerated_order_prefix_len sequence hfeasible)
          (hgenerated_sequence_prefix_len sequence hfeasible))
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceInequalities_transferBound_and_generatedReplayTransferPrefixTallies
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (lossSourceOrder := lossSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (structureOf := structureOf)
      (initialActive := initialActive)
      (tallyOf := tallyOf)
      (lossTransfers := lossTransfers)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (lowerInitialLosses := lowerInitialLosses)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwinCount_source_eq
      hassignedBudget_source_le hsupport_source_le hselected_candidate
      hselected_quota hloss_source_nodup hloss_source_mem htransfer_length
      hlower_transfer hsequence_eq htrace_generated hgenerated_constraints_hold
      generatedPrefixLength htop_lt_quota
      (by
        intro sequence hfeasible i candidate hactive
        exact
          hgenerated_active_tally_le_transfer_prefix sequence hfeasible i
            (Nat.lt_of_lt_of_le i.2
              (generatedPrefixLength sequence hfeasible))
            candidate hactive)

/--
Concrete Proposition 3.4 generated-replay route with Algorithm 7's
Predict-Losses source order specialized to the literal filtered candidate list
and its transfer list specialized to a candidate-keyed map. This discharges the
loss-order nodup, loss-order membership, and transfer-list length obligations
that are definitional for the source `C_L`/`T` construction.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_generatedStructureTransferPrefixTallies_predictLossesToList_mappedTransfers
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {structureOf : RCVSequence → RCVStructure Candidate}
    {initialActive : RCVSequence → Finset Candidate}
    {tallyOf : RCVSequence → Finset Candidate → Candidate → ℕ}
    (transferOf : Candidate → ℕ)
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice lowerInitialLosses uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hselected_candidate :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈ candidates)
    (hselected_quota :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            quota ≤ assignedBudget sequence candidate +
              strictSupportCount voters ballots candidates
                (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref)
                candidate)
    (hlower_transfer :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤
          predictLossesTransferInitialLossBound topFirstChoice quota
            (((predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold).toList).map transferOf))
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_generated :
      ∀ sequence, feasibleSequence sequence →
        traceOf sequence =
          rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence))
    (hgenerated_constraints_hold :
      ∀ sequence, feasibleSequence sequence →
        ∀ constraint,
          constraint ∈
            rcvGeneratedStructureRoundConstraints (structureOf sequence)
              (initialActive sequence) (tallyOf sequence) quota →
          constraint.Holds)
    (hgenerated_order_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ (structureOf sequence).finalOrder.order.length)
    (hgenerated_sequence_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        lowerInitialLosses ≤ (structureOf sequence).sequence.length)
    (htop_lt_quota : topFirstChoice < quota)
    (hgenerated_active_tally_le_transfer_prefix :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i : Fin lowerInitialLosses,
          ∀ hidx :
            i.1 <
              (rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence) (tallyOf sequence)).steps.length,
          ∀ candidate,
            candidate ∈
              ((rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence) (tallyOf sequence)).steps.get
                ⟨i.1, hidx⟩).beforeActive →
            (tallyOf sequence
              (((rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence) (tallyOf sequence)).steps.get
                ⟨i.1, hidx⟩).beforeActive)) candidate ≤
              ((((predictLossesCandidates voters ballots candidates budget
                firstChoiceThreshold).toList).map
                  transferOf).take i.1).sum +
                topFirstChoice) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota lowerInitialLosses
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_sourceInequalities_transferBound_and_generatedStructureTransferPrefixTallies
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (lossSourceOrder := fun _ =>
        (predictLossesCandidates voters ballots candidates budget
          firstChoiceThreshold).toList)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (structureOf := structureOf)
      (initialActive := initialActive)
      (tallyOf := tallyOf)
      (lossTransfers := fun sequence =>
        ((predictLossesCandidates voters ballots candidates budget
          firstChoiceThreshold).toList).map transferOf)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (lowerInitialLosses := lowerInitialLosses)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwinCount_source_eq hassignedBudget_source_le
      hsupport_source_le hselected_candidate hselected_quota
      (fun _ _ =>
        Finset.nodup_toList
          (predictLossesCandidates voters ballots candidates budget
            firstChoiceThreshold))
      (fun _ _ candidate hcandidate => by
        simpa using (Finset.mem_toList.mp hcandidate))
      (fun _ _ => by simp)
      hlower_transfer hsequence_eq htrace_generated hgenerated_constraints_hold
      hgenerated_order_prefix_len hgenerated_sequence_prefix_len htop_lt_quota
      hgenerated_active_tally_le_transfer_prefix

/--
Exact Algorithm 7 version of the preceding route: the lower initial-loss count
is the Predict-Losses transfer-loop counter computed from the literal
`C_L.toList.map transferOf` list. This is the source convention for the
returned `i_L`, so the generic lower-bound premise becomes reflexive.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_generatedStructureTransferPrefixTallies_exactPredictLossesToList_mappedTransfers
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {structureOf : RCVSequence → RCVStructure Candidate}
    {initialActive : RCVSequence → Finset Candidate}
    {tallyOf : RCVSequence → Finset Candidate → Candidate → ℕ}
    (transferOf : Candidate → ℕ)
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hselected_candidate :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈ candidates)
    (hselected_quota :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            quota ≤ assignedBudget sequence candidate +
              strictSupportCount voters ballots candidates
                (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref)
                candidate)
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_generated :
      ∀ sequence, feasibleSequence sequence →
        traceOf sequence =
          rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence))
    (hgenerated_constraints_hold :
      ∀ sequence, feasibleSequence sequence →
        ∀ constraint,
          constraint ∈
            rcvGeneratedStructureRoundConstraints (structureOf sequence)
              (initialActive sequence) (tallyOf sequence) quota →
          constraint.Holds)
    (hgenerated_order_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        predictLossesTransferInitialLossBound topFirstChoice quota
            (((predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold).toList).map transferOf) ≤
          (structureOf sequence).finalOrder.order.length)
    (hgenerated_sequence_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        predictLossesTransferInitialLossBound topFirstChoice quota
            (((predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold).toList).map transferOf) ≤
          (structureOf sequence).sequence.length)
    (htop_lt_quota : topFirstChoice < quota)
    (hgenerated_active_tally_le_transfer_prefix :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i :
          Fin
            (predictLossesTransferInitialLossBound topFirstChoice quota
              (((predictLossesCandidates voters ballots candidates budget
                firstChoiceThreshold).toList).map transferOf)),
          ∀ hidx :
            i.1 <
              (rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence) (tallyOf sequence)).steps.length,
          ∀ candidate,
            candidate ∈
              ((rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence) (tallyOf sequence)).steps.get
                ⟨i.1, hidx⟩).beforeActive →
            (tallyOf sequence
              (((rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence) (tallyOf sequence)).steps.get
                ⟨i.1, hidx⟩).beforeActive)) candidate ≤
              ((((predictLossesCandidates voters ballots candidates budget
                firstChoiceThreshold).toList).map transferOf).take i.1).sum +
                topFirstChoice) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota
        (predictLossesTransferInitialLossBound topFirstChoice quota
          (((predictLossesCandidates voters ballots candidates budget
            firstChoiceThreshold).toList).map transferOf))
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_generatedStructureTransferPrefixTallies_predictLossesToList_mappedTransfers
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (structureOf := structureOf)
      (initialActive := initialActive)
      (tallyOf := tallyOf)
      (transferOf := transferOf)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (lowerInitialLosses :=
        predictLossesTransferInitialLossBound topFirstChoice quota
          (((predictLossesCandidates voters ballots candidates budget
            firstChoiceThreshold).toList).map transferOf))
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwinCount_source_eq hassignedBudget_source_le
      hsupport_source_le hselected_candidate hselected_quota
      (fun _ _ => le_rfl) hsequence_eq htrace_generated
      hgenerated_constraints_hold hgenerated_order_prefix_len
      hgenerated_sequence_prefix_len htop_lt_quota
      hgenerated_active_tally_le_transfer_prefix

/--
Exact Algorithm 7 generated-replay route where each generated structure is
well formed: its win/loss sequence has the same length as its final order. In
that source convention, the generated sequence-prefix length premise follows
from the order-prefix length premise.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_validGeneratedStructureTransferPrefixTallies_exactPredictLossesToList_mappedTransfers
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {structureOf : RCVSequence → RCVStructure Candidate}
    {initialActive : RCVSequence → Finset Candidate}
    {tallyOf : RCVSequence → Finset Candidate → Candidate → ℕ}
    (transferOf : Candidate → ℕ)
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hselected_candidate :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈ candidates)
    (hselected_quota :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            quota ≤ assignedBudget sequence candidate +
              strictSupportCount voters ballots candidates
                (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref)
                candidate)
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_generated :
      ∀ sequence, feasibleSequence sequence →
        traceOf sequence =
          rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence))
    (hgenerated_constraints_hold :
      ∀ sequence, feasibleSequence sequence →
        ∀ constraint,
          constraint ∈
            rcvGeneratedStructureRoundConstraints (structureOf sequence)
              (initialActive sequence) (tallyOf sequence) quota →
          constraint.Holds)
    (hgenerated_valid_length :
      ∀ sequence, feasibleSequence sequence →
        (structureOf sequence).validLength)
    (hgenerated_order_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        predictLossesTransferInitialLossBound topFirstChoice quota
            (((predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold).toList).map transferOf) ≤
          (structureOf sequence).finalOrder.order.length)
    (htop_lt_quota : topFirstChoice < quota)
    (hgenerated_active_tally_le_transfer_prefix :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ i :
          Fin
            (predictLossesTransferInitialLossBound topFirstChoice quota
              (((predictLossesCandidates voters ballots candidates budget
                firstChoiceThreshold).toList).map transferOf)),
          ∀ hidx :
            i.1 <
              (rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence) (tallyOf sequence)).steps.length,
          ∀ candidate,
            candidate ∈
              ((rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence) (tallyOf sequence)).steps.get
                ⟨i.1, hidx⟩).beforeActive →
            (tallyOf sequence
              (((rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence) (tallyOf sequence)).steps.get
                ⟨i.1, hidx⟩).beforeActive)) candidate ≤
              ((((predictLossesCandidates voters ballots candidates budget
                firstChoiceThreshold).toList).map transferOf).take i.1).sum +
                topFirstChoice) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota
        (predictLossesTransferInitialLossBound topFirstChoice quota
          (((predictLossesCandidates voters ballots candidates budget
            firstChoiceThreshold).toList).map transferOf))
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_generatedStructureTransferPrefixTallies_exactPredictLossesToList_mappedTransfers
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (structureOf := structureOf)
      (initialActive := initialActive)
      (tallyOf := tallyOf)
      (transferOf := transferOf)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwinCount_source_eq hassignedBudget_source_le
      hsupport_source_le hselected_candidate hselected_quota hsequence_eq
      htrace_generated hgenerated_constraints_hold
      hgenerated_order_prefix_len
      (by
        intro sequence hfeasible
        rw [hgenerated_valid_length sequence hfeasible]
        exact hgenerated_order_prefix_len sequence hfeasible)
      htop_lt_quota hgenerated_active_tally_le_transfer_prefix

/--
Exact Algorithm 7 generated-replay route from stepwise transfer accounting.
The caller gives the source facts that the first counted prefix has every
active tally bounded by the top first-choice count and that each subsequent
counted prefix can increase an active tally by at most the next transfer-list
entry. The reusable trace summation lemma turns those stepwise facts into the
transfer-prefix tally bound used by Proposition 3.4.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_validGeneratedStructureStepwiseTransferTallies_exactPredictLossesToList_mappedTransfers
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop}
    {winnerSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {structureOf : RCVSequence → RCVStructure Candidate}
    {initialActive : RCVSequence → Finset Candidate}
    {tallyOf : RCVSequence → Finset Candidate → Candidate → ℕ}
    (transferOf : Candidate → ℕ)
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hselected_candidate :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈ candidates)
    (hselected_quota :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            quota ≤ assignedBudget sequence candidate +
              strictSupportCount voters ballots candidates
                (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref)
                candidate)
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_generated :
      ∀ sequence, feasibleSequence sequence →
        traceOf sequence =
          rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence))
    (hgenerated_constraints_hold :
      ∀ sequence, feasibleSequence sequence →
        ∀ constraint,
          constraint ∈
            rcvGeneratedStructureRoundConstraints (structureOf sequence)
              (initialActive sequence) (tallyOf sequence) quota →
          constraint.Holds)
    (hgenerated_valid_length :
      ∀ sequence, feasibleSequence sequence →
        (structureOf sequence).validLength)
    (hgenerated_order_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        predictLossesTransferInitialLossBound topFirstChoice quota
            (((predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold).toList).map transferOf) ≤
          (structureOf sequence).finalOrder.order.length)
    (htop_lt_quota : topFirstChoice < quota)
    (hinitial_tally_le_topFirstChoice :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ hpos :
          0 <
            predictLossesTransferInitialLossBound topFirstChoice quota
              (((predictLossesCandidates voters ballots candidates budget
                firstChoiceThreshold).toList).map transferOf),
        ∀ hidx :
          0 <
            (rcvGeneratedTraceOfStructure (structureOf sequence)
              (initialActive sequence) (tallyOf sequence)).steps.length,
        ∀ candidate,
          candidate ∈
            ((rcvGeneratedTraceOfStructure (structureOf sequence)
              (initialActive sequence) (tallyOf sequence)).steps.get
              ⟨0, hidx⟩).beforeActive →
          ((rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)).steps.get
            ⟨0, hidx⟩).tally candidate ≤ topFirstChoice)
    (hstep_tally_le_transfer :
      ∀ sequence, (hfeasible : feasibleSequence sequence) →
        ∀ idx,
          ∀ hnext :
            idx + 1 <
              predictLossesTransferInitialLossBound topFirstChoice quota
                (((predictLossesCandidates voters ballots candidates budget
                  firstChoiceThreshold).toList).map transferOf),
          ∀ hidx_next :
            idx + 1 <
              (rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence) (tallyOf sequence)).steps.length,
          ∀ hidx_current :
            idx <
              (rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence) (tallyOf sequence)).steps.length,
          ∀ candidate,
            candidate ∈
              ((rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence) (tallyOf sequence)).steps.get
                ⟨idx + 1, hidx_next⟩).beforeActive →
            ((rcvGeneratedTraceOfStructure (structureOf sequence)
              (initialActive sequence) (tallyOf sequence)).steps.get
              ⟨idx + 1, hidx_next⟩).tally candidate ≤
              (if candidate ∈
                  ((rcvGeneratedTraceOfStructure (structureOf sequence)
                    (initialActive sequence) (tallyOf sequence)).steps.get
                    ⟨idx, hidx_current⟩).beforeActive then
                ((rcvGeneratedTraceOfStructure (structureOf sequence)
                  (initialActive sequence) (tallyOf sequence)).steps.get
                  ⟨idx, hidx_current⟩).tally candidate
              else
                0) +
                (((predictLossesCandidates voters ballots candidates budget
                  firstChoiceThreshold).toList).map transferOf).getD idx 0) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota
        (predictLossesTransferInitialLossBound topFirstChoice quota
          (((predictLossesCandidates voters ballots candidates budget
            firstChoiceThreshold).toList).map transferOf))
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_validGeneratedStructureTransferPrefixTallies_exactPredictLossesToList_mappedTransfers
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (structureOf := structureOf)
      (initialActive := initialActive)
      (tallyOf := tallyOf)
      (transferOf := transferOf)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwinCount_source_eq hassignedBudget_source_le
      hsupport_source_le hselected_candidate hselected_quota hsequence_eq
      htrace_generated hgenerated_constraints_hold hgenerated_valid_length
      hgenerated_order_prefix_len htop_lt_quota
      (by
        intro sequence hfeasible i hidx candidate hactive
        let transfers :=
          ((predictLossesCandidates voters ballots candidates budget
            firstChoiceThreshold).toList).map transferOf
        let generated :=
          rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)
        have hprefix_len :
            predictLossesTransferInitialLossBound topFirstChoice quota
                transfers ≤ generated.steps.length := by
          have hsequence_len :
              predictLossesTransferInitialLossBound topFirstChoice quota
                  transfers ≤ (structureOf sequence).sequence.length := by
            rw [hgenerated_valid_length sequence hfeasible]
            exact hgenerated_order_prefix_len sequence hfeasible
          simpa [generated, transfers, rcvGeneratedTraceOfStructure] using
            (OrderSequenceStructure.le_generatedTrace_steps_length_of_le_order_length_of_le_sequence_length
              (struct := structureOf sequence)
              (initialActive := initialActive sequence)
              (tallyOf := tallyOf sequence)
              (hgenerated_order_prefix_len sequence hfeasible)
              hsequence_len)
        have hactive' :
            candidate ∈
              (generated.steps.get
                ⟨i.1, Nat.lt_of_lt_of_le i.2 hprefix_len⟩).beforeActive := by
          simpa [generated] using hactive
        have htrace_bound :
            (generated.steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2 hprefix_len⟩).tally candidate ≤
              topFirstChoice +
                ∑ j ∈ Finset.range i.1, transfers.getD j 0 :=
          rcvTrace_active_tally_le_topFirstChoice_add_transfer_prefix_sum
            (trace := generated)
            (prefixLen :=
              predictLossesTransferInitialLossBound topFirstChoice quota
                transfers)
            (topFirstChoice := topFirstChoice)
            (transferAt := fun j => transfers.getD j 0)
            hprefix_len
            (fun hpos candidate hactive0 =>
              hinitial_tally_le_topFirstChoice sequence hfeasible hpos
                (Nat.lt_of_lt_of_le hpos hprefix_len) candidate
                (by simpa [generated] using hactive0))
            (fun idx hnext candidate hactive_next =>
              hstep_tally_le_transfer sequence hfeasible idx hnext
                (Nat.lt_of_lt_of_le hnext hprefix_len)
                (Nat.lt_of_lt_of_le (Nat.lt_of_succ_lt hnext) hprefix_len)
                candidate
                (by simpa [generated, transfers] using hactive_next))
            i candidate hactive'
        have htally_eq :
            (generated.steps.get
              ⟨i.1, Nat.lt_of_lt_of_le i.2 hprefix_len⟩).tally =
              tallyOf sequence
                ((generated.steps.get
                  ⟨i.1, Nat.lt_of_lt_of_le i.2 hprefix_len⟩).beforeActive) := by
          simpa [generated, rcvGeneratedTraceOfStructure] using
            (OrderSequenceStructure.generatedTrace_tally_eq
              (structureOf sequence) (initialActive sequence)
              (tallyOf sequence)
              ⟨i.1, Nat.lt_of_lt_of_le i.2 hprefix_len⟩)
        have hprefix_sum :
            (transfers.take i.1).sum =
              ∑ j ∈ Finset.range i.1, transfers.getD j 0 :=
          EconCSLib.FiniteSum.list_sum_take_eq_sum_range_getD transfers i.1
        have hbound_tallyOf :
            (tallyOf sequence
              ((generated.steps.get
                ⟨i.1, Nat.lt_of_lt_of_le i.2 hprefix_len⟩).beforeActive))
                candidate ≤
              (transfers.take i.1).sum + topFirstChoice := by
          rw [← htally_eq]
          calc
            (generated.steps.get
                ⟨i.1, Nat.lt_of_lt_of_le i.2 hprefix_len⟩).tally candidate
                ≤ topFirstChoice + ∑ j ∈ Finset.range i.1,
                    transfers.getD j 0 := htrace_bound
            _ = topFirstChoice + (transfers.take i.1).sum := by
              rw [← hprefix_sum]
            _ = (transfers.take i.1).sum + topFirstChoice := by
              rw [Nat.add_comm]
        simpa [generated, transfers] using hbound_tallyOf)

/--
Finite checker for the generated-structure Algorithm 7 transfer accounting.
For every feasible source sequence in the finite coverage set, it checks that
the first counted generated round is bounded by the global top first-choice
count and that each later counted round can increase any active candidate's
tally by at most the corresponding mapped Predict-Losses transfer entry.
-/
noncomputable def proposition3_4_generatedStructureStepwiseTransferCheckOnFinset
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {feasibleSequence : Sequence → Prop} [DecidablePred feasibleSequence]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate) (sourceSequences : Finset Sequence)
    (structureOf : Sequence → RCVStructure Candidate)
    (initialActive : Sequence → Finset Candidate)
    (tallyOf : Sequence → Finset Candidate → Candidate → ℕ)
    (transferOf : Candidate → ℕ)
    (budget quota firstChoiceThreshold topFirstChoice : ℕ) : Bool := by
  classical
  let transfers :=
    ((predictLossesCandidates voters ballots candidates budget
      firstChoiceThreshold).toList).map transferOf
  let lowerBound :=
    predictLossesTransferInitialLossBound topFirstChoice quota transfers
  exact sourceSequences.toList.all fun sequence =>
    if feasibleSequence sequence then
      let trace :=
        rcvGeneratedTraceOfStructure (structureOf sequence)
          (initialActive sequence) (tallyOf sequence)
      (List.range lowerBound).all fun idx =>
        ((if idx = 0 then
            match trace.steps[idx]? with
            | none => false
            | some step =>
                decide
                  (∀ candidate, candidate ∈ step.beforeActive →
                    step.tally candidate ≤ topFirstChoice)
          else
            true) &&
          (if idx + 1 < lowerBound then
            match trace.steps[idx]?, trace.steps[idx + 1]? with
            | some current, some next =>
                decide
                  (∀ candidate, candidate ∈ next.beforeActive →
                    next.tally candidate ≤
                      (if candidate ∈ current.beforeActive then
                        current.tally candidate
                      else
                        0) + transfers.getD idx 0)
            | _, _ => false
          else
            true))
    else
      true

/--
Completeness for the generated-structure Algorithm 7 stepwise-transfer
checker.  If the generated trace has enough prefix steps, the first counted
round is below the global top-first-choice cap, and each following counted
round increases active tallies by at most the mapped transfer entry, then the
executable finite checker succeeds.
-/
theorem proposition3_4_generatedStructureStepwiseTransferCheckOnFinset_eq_true_of_facts
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {feasibleSequence : Sequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {sourceSequences : Finset Sequence}
    {structureOf : Sequence → RCVStructure Candidate}
    {initialActive : Sequence → Finset Candidate}
    {tallyOf : Sequence → Finset Candidate → Candidate → ℕ}
    {transferOf : Candidate → ℕ}
    {budget quota firstChoiceThreshold topFirstChoice : ℕ}
    (htrace_prefix_len :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        predictLossesTransferInitialLossBound topFirstChoice quota
            (((predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold).toList).map transferOf) ≤
          (rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)).steps.length)
    (hinitial_tally :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        ∀ hpos :
          0 <
            predictLossesTransferInitialLossBound topFirstChoice quota
              (((predictLossesCandidates voters ballots candidates budget
                firstChoiceThreshold).toList).map transferOf),
        ∀ hidx :
          0 <
            (rcvGeneratedTraceOfStructure (structureOf sequence)
              (initialActive sequence) (tallyOf sequence)).steps.length,
        ∀ candidate,
          candidate ∈
            ((rcvGeneratedTraceOfStructure (structureOf sequence)
              (initialActive sequence) (tallyOf sequence)).steps.get
              ⟨0, hidx⟩).beforeActive →
          ((rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)).steps.get
            ⟨0, hidx⟩).tally candidate ≤ topFirstChoice)
    (hstep_tally :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        ∀ idx,
          ∀ hnext :
            idx + 1 <
              predictLossesTransferInitialLossBound topFirstChoice quota
                (((predictLossesCandidates voters ballots candidates budget
                  firstChoiceThreshold).toList).map transferOf),
          ∀ hidx_next :
            idx + 1 <
              (rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence) (tallyOf sequence)).steps.length,
          ∀ hidx_current :
            idx <
              (rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence) (tallyOf sequence)).steps.length,
          ∀ candidate,
            candidate ∈
              ((rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence) (tallyOf sequence)).steps.get
                ⟨idx + 1, hidx_next⟩).beforeActive →
            ((rcvGeneratedTraceOfStructure (structureOf sequence)
              (initialActive sequence) (tallyOf sequence)).steps.get
              ⟨idx + 1, hidx_next⟩).tally candidate ≤
              (if candidate ∈
                  ((rcvGeneratedTraceOfStructure (structureOf sequence)
                    (initialActive sequence) (tallyOf sequence)).steps.get
                    ⟨idx, hidx_current⟩).beforeActive then
                ((rcvGeneratedTraceOfStructure (structureOf sequence)
                  (initialActive sequence) (tallyOf sequence)).steps.get
                  ⟨idx, hidx_current⟩).tally candidate
              else
                0) +
                (((predictLossesCandidates voters ballots candidates budget
                  firstChoiceThreshold).toList).map transferOf).getD idx 0) :
    proposition3_4_generatedStructureStepwiseTransferCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        sourceSequences structureOf initialActive tallyOf transferOf budget
        quota firstChoiceThreshold topFirstChoice = true := by
  classical
  apply List.all_eq_true.mpr
  intro sequence hseq
  have hmem : sequence ∈ sourceSequences := Finset.mem_toList.mp hseq
  by_cases hfeasible : feasibleSequence sequence
  · let transfers :=
      ((predictLossesCandidates voters ballots candidates budget
        firstChoiceThreshold).toList).map transferOf
    let lowerBound :=
      predictLossesTransferInitialLossBound topFirstChoice quota transfers
    let trace :=
      rcvGeneratedTraceOfStructure (structureOf sequence)
        (initialActive sequence) (tallyOf sequence)
    have hlen : lowerBound ≤ trace.steps.length := by
      simpa [lowerBound, transfers, trace] using
        htrace_prefix_len sequence hmem hfeasible
    have hrange_all :
        ((List.range lowerBound).all fun idx =>
          ((if idx = 0 then
              match trace.steps[idx]? with
              | none => false
              | some step =>
                  decide
                    (∀ candidate, candidate ∈ step.beforeActive →
                      step.tally candidate ≤ topFirstChoice)
            else
              true) &&
            (if idx + 1 < lowerBound then
              match trace.steps[idx]?, trace.steps[idx + 1]? with
              | some current, some next =>
                  decide
                    (∀ candidate, candidate ∈ next.beforeActive →
                      next.tally candidate ≤
                        (if candidate ∈ current.beforeActive then
                          current.tally candidate
                        else
                          0) + transfers.getD idx 0)
              | _, _ => false
            else
              true))) = true := by
      apply List.all_eq_true.mpr
      intro idx hidx_range
      have hidx_lt : idx < lowerBound := by
        simpa using hidx_range
      have hinitial_bool :
          (if idx = 0 then
              match trace.steps[idx]? with
              | none => false
              | some step =>
                  decide
                    (∀ candidate, candidate ∈ step.beforeActive →
                      step.tally candidate ≤ topFirstChoice)
            else
              true) = true := by
        by_cases hzero : idx = 0
        · subst idx
          have hpos : 0 < lowerBound := by
            simpa using hidx_lt
          have hidx0 : 0 < trace.steps.length :=
            Nat.lt_of_lt_of_le hpos hlen
          have hsome :
              trace.steps[0]? = some (trace.steps.get ⟨0, hidx0⟩) := by
            simpa using
              (List.getElem?_eq_getElem (l := trace.steps) (i := 0) hidx0)
          have hdec :
              decide
                (∀ candidate,
                  candidate ∈ (trace.steps.get ⟨0, hidx0⟩).beforeActive →
                    (trace.steps.get ⟨0, hidx0⟩).tally candidate ≤
                      topFirstChoice) = true := by
            apply decide_eq_true_iff.mpr
            intro candidate hactive
            exact
              hinitial_tally sequence hmem hfeasible
                (by simpa [lowerBound, transfers] using hpos)
                (by simpa [trace] using hidx0) candidate
                (by simpa [trace] using hactive)
          simp only [hsome]
          exact hdec
        · simp [hzero]
      have hstep_bool :
          (if idx + 1 < lowerBound then
              match trace.steps[idx]?, trace.steps[idx + 1]? with
              | some current, some next =>
                  decide
                    (∀ candidate, candidate ∈ next.beforeActive →
                      next.tally candidate ≤
                        (if candidate ∈ current.beforeActive then
                          current.tally candidate
                        else
                          0) + transfers.getD idx 0)
              | _, _ => false
            else
              true) = true := by
        by_cases hnext : idx + 1 < lowerBound
        · have hidx_next : idx + 1 < trace.steps.length :=
            Nat.lt_of_lt_of_le hnext hlen
          have hidx_current : idx < trace.steps.length :=
            Nat.lt_of_lt_of_le hidx_lt hlen
          have hsome_current :
              trace.steps[idx]? =
                some (trace.steps.get ⟨idx, hidx_current⟩) := by
            simpa using
              (List.getElem?_eq_getElem (l := trace.steps) (i := idx)
                hidx_current)
          have hsome_next :
              trace.steps[idx + 1]? =
                some (trace.steps.get ⟨idx + 1, hidx_next⟩) := by
            simpa using
              (List.getElem?_eq_getElem (l := trace.steps) (i := idx + 1)
                hidx_next)
          have hdec :
              decide
                (∀ candidate,
                  candidate ∈
                      (trace.steps.get ⟨idx + 1, hidx_next⟩).beforeActive →
                    (trace.steps.get ⟨idx + 1, hidx_next⟩).tally candidate ≤
                      (if candidate ∈
                          (trace.steps.get ⟨idx, hidx_current⟩).beforeActive
                        then
                          (trace.steps.get ⟨idx, hidx_current⟩).tally
                            candidate
                        else
                          0) + transfers.getD idx 0) = true := by
            apply decide_eq_true_iff.mpr
            intro candidate hactive
            exact
              hstep_tally sequence hmem hfeasible idx
                (by simpa [lowerBound, transfers] using hnext)
                (by simpa [trace] using hidx_next)
                (by simpa [trace] using hidx_current) candidate
                (by simpa [trace] using hactive)
          simp only [if_pos hnext, hsome_current, hsome_next]
          exact hdec
        · simp [hnext]
      simpa [Bool.and_eq_true_eq_eq_true_and_eq_true] using
        And.intro hinitial_bool hstep_bool
    simpa [proposition3_4_generatedStructureStepwiseTransferCheckOnFinset,
      hfeasible, trace, lowerBound, transfers] using hrange_all
  · simp [hfeasible]

/--
Profile-tally source route for the generated-structure Algorithm 7 stepwise
transfer checker.  If generated traces are long enough, all first choices are
inside the initial active set, the global first-choice cap bounds every
initially active candidate, and each focused candidate's current profile tally
is bounded by the corresponding Predict-Losses transfer entry, then the
executable transfer-accounting checker succeeds.
-/
theorem proposition3_4_generatedStructureStepwiseTransferCheckOnFinset_eq_true_of_profile_tallies
    {Voter Candidate Sequence : Type*} [DecidableEq Voter]
    [DecidableEq Candidate]
    {feasibleSequence : Sequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {sourceSequences : Finset Sequence}
    {structureOf : Sequence → RCVStructure Candidate}
    {initialActive : Sequence → Finset Candidate}
    {transferOf : Candidate → ℕ}
    {budget quota firstChoiceThreshold topFirstChoice : ℕ}
    (htrace_prefix_len :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        predictLossesTransferInitialLossBound topFirstChoice quota
            (((predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold).toList).map transferOf) ≤
          (rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence)
            (profileActiveTallyOf voters ballots)).steps.length)
    (hinitial_subset_candidates :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        initialActive sequence ⊆ candidates)
    (hfirst_initial :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        ∀ voter, voter ∈ voters →
          Ballot.firstChoiceIn (ballots voter) (initialActive sequence))
    (hglobal_first_le :
      ∀ candidate, candidate ∈ candidates →
        Ballot.firstChoiceCount voters ballots candidate ≤ topFirstChoice)
    (hfocused_transfer_cap :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        ∀ idx,
          ∀ hidx :
            idx <
              (rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence)
                (profileActiveTallyOf voters ballots)).steps.length,
          ∀ source,
            ((rcvGeneratedTraceOfStructure (structureOf sequence)
              (initialActive sequence)
              (profileActiveTallyOf voters ballots)).steps.get
              ⟨idx, hidx⟩).focus = some source →
            profileActiveTallyOf voters ballots
                (((rcvGeneratedTraceOfStructure (structureOf sequence)
                  (initialActive sequence)
                  (profileActiveTallyOf voters ballots)).steps.get
                  ⟨idx, hidx⟩).beforeActive) source ≤
              (((predictLossesCandidates voters ballots candidates budget
                firstChoiceThreshold).toList).map transferOf).getD idx 0) :
    proposition3_4_generatedStructureStepwiseTransferCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        sourceSequences structureOf initialActive
        (fun _ => profileActiveTallyOf voters ballots) transferOf budget
        quota firstChoiceThreshold topFirstChoice = true := by
  classical
  refine
    proposition3_4_generatedStructureStepwiseTransferCheckOnFinset_eq_true_of_facts
      (feasibleSequence := feasibleSequence)
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (sourceSequences := sourceSequences)
      (structureOf := structureOf)
      (initialActive := initialActive)
      (tallyOf := fun _ => profileActiveTallyOf voters ballots)
      (transferOf := transferOf)
      (budget := budget)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      htrace_prefix_len ?_ ?_
  · intro sequence hmem hfeasible hpos hidx candidate hactive
    let trace :=
      rcvGeneratedTraceOfStructure (structureOf sequence)
        (initialActive sequence) (profileActiveTallyOf voters ballots)
    have hreplay :
        trace.replaysFrom (initialActive sequence)
          (rcvGeneratedTraceTerminalActive (structureOf sequence)
            (initialActive sequence)) := by
      simpa [trace] using
        rcvGeneratedTrace_replaysFrom (structureOf sequence)
          (initialActive sequence) (profileActiveTallyOf voters ballots)
    have hbefore :
        (trace.steps.get ⟨0, by simpa [trace] using hidx⟩).beforeActive =
          initialActive sequence := by
      exact
        STVTrace.replayStepsFrom_get_zero_beforeActive_eq_startActive
          (steps := trace.steps)
          (startActive := initialActive sequence)
          (terminalActive :=
            rcvGeneratedTraceTerminalActive (structureOf sequence)
              (initialActive sequence))
          hreplay (by simpa [trace] using hidx)
    have hactive0 :
        candidate ∈
          (trace.steps.get ⟨0, by simpa [trace] using hidx⟩).beforeActive := by
      simpa [trace] using hactive
    have hactive_initial : candidate ∈ initialActive sequence := by
      rw [hbefore] at hactive0
      exact hactive0
    have hcandidate_candidates : candidate ∈ candidates :=
      hinitial_subset_candidates sequence hmem hfeasible hactive_initial
    have htally_eq :
        (trace.steps.get ⟨0, by simpa [trace] using hidx⟩).tally =
          profileActiveTallyOf voters ballots
            ((trace.steps.get ⟨0, by simpa [trace] using hidx⟩).beforeActive) := by
      simpa [trace, rcvGeneratedTraceOfStructure] using
        (OrderSequenceStructure.generatedTrace_tally_eq
          (structureOf sequence) (initialActive sequence)
          (profileActiveTallyOf voters ballots)
          ⟨0, by simpa [trace] using hidx⟩)
    have htally_initial :
        ((rcvGeneratedTraceOfStructure (structureOf sequence)
          (initialActive sequence)
          (profileActiveTallyOf voters ballots)).steps.get
          ⟨0, hidx⟩).tally candidate =
            profileActiveTallyOf voters ballots (initialActive sequence)
              candidate := by
      have h := congrFun htally_eq candidate
      rw [hbefore] at h
      simpa [trace] using h
    have hprofile_first :
        profileActiveTallyOf voters ballots (initialActive sequence)
            candidate ≤
          Ballot.firstChoiceCount voters ballots candidate :=
      profileActiveTallyOf_le_firstChoiceCount_of_forall_firstChoiceIn
        voters ballots
        (active := initialActive sequence)
        (candidate := candidate)
        (hfirst_initial sequence hmem hfeasible)
    calc
      ((rcvGeneratedTraceOfStructure (structureOf sequence)
        (initialActive sequence)
        (profileActiveTallyOf voters ballots)).steps.get
        ⟨0, hidx⟩).tally candidate
          = profileActiveTallyOf voters ballots (initialActive sequence)
              candidate := htally_initial
      _ ≤ Ballot.firstChoiceCount voters ballots candidate := hprofile_first
      _ ≤ topFirstChoice := hglobal_first_le candidate hcandidate_candidates
  · intro sequence hmem hfeasible idx hnext hidx_next hidx_current candidate
      hactive
    let trace :=
      rcvGeneratedTraceOfStructure (structureOf sequence)
        (initialActive sequence) (profileActiveTallyOf voters ballots)
    let current : STVStep Candidate :=
      trace.steps.get ⟨idx, by simpa [trace] using hidx_current⟩
    let next : STVStep Candidate :=
      trace.steps.get ⟨idx + 1, by simpa [trace] using hidx_next⟩
    have hreplay :
        trace.replaysFrom (initialActive sequence)
          (rcvGeneratedTraceTerminalActive (structureOf sequence)
            (initialActive sequence)) := by
      simpa [trace] using
        rcvGeneratedTrace_replaysFrom (structureOf sequence)
          (initialActive sequence) (profileActiveTallyOf voters ballots)
    have hnext_before :
        next.beforeActive = current.afterActive := by
      simpa [trace, current, next] using
        STVTrace.replayStepsFrom_get_succ_beforeActive_eq_afterActive
          (steps := trace.steps)
          (startActive := initialActive sequence)
          (terminalActive :=
            rcvGeneratedTraceTerminalActive (structureOf sequence)
              (initialActive sequence))
          hreplay
          (i := idx) (by simpa [trace] using hidx_next)
    have hcurrent_mem : current ∈ trace.steps := by
      simpa [current] using
        List.get_mem trace.steps ⟨idx, hidx_current⟩
    have hremove : current.removesFocusedCandidate := by
      exact
        rcvGeneratedTrace_removesFocusedCandidate (structureOf sequence)
          (initialActive sequence) (profileActiveTallyOf voters ballots)
          current (by simpa [trace] using hcurrent_mem)
    rcases hremove with ⟨source, hfocus, hafter⟩
    have hactive_next : candidate ∈ next.beforeActive := by
      simpa [trace, next] using hactive
    have hactive_erase : candidate ∈ current.beforeActive.erase source := by
      have hactive_after : candidate ∈ current.afterActive := by
        simpa [hnext_before] using hactive_next
      simpa [hafter] using hactive_after
    have hactive_current : candidate ∈ current.beforeActive :=
      Finset.mem_of_mem_erase hactive_erase
    have hcurrent_tally_eq :
        current.tally =
          profileActiveTallyOf voters ballots current.beforeActive := by
      simpa [trace, current, rcvGeneratedTraceOfStructure] using
        (OrderSequenceStructure.generatedTrace_tally_eq
          (structureOf sequence) (initialActive sequence)
          (profileActiveTallyOf voters ballots)
          ⟨idx, by simpa [trace] using hidx_current⟩)
    have hnext_tally_eq :
        next.tally =
          profileActiveTallyOf voters ballots next.beforeActive := by
      simpa [trace, next, rcvGeneratedTraceOfStructure] using
        (OrderSequenceStructure.generatedTrace_tally_eq
          (structureOf sequence) (initialActive sequence)
          (profileActiveTallyOf voters ballots)
          ⟨idx + 1, by simpa [trace] using hidx_next⟩)
    have hnext_tally_erase :
        ((rcvGeneratedTraceOfStructure (structureOf sequence)
          (initialActive sequence)
          (profileActiveTallyOf voters ballots)).steps.get
          ⟨idx + 1, hidx_next⟩).tally candidate =
            profileActiveTallyOf voters ballots
              (current.beforeActive.erase source) candidate := by
      have h := congrFun hnext_tally_eq candidate
      rw [hnext_before, hafter] at h
      simpa [trace, next] using h
    have hactive_current_trace :
        candidate ∈
          ((rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence)
            (profileActiveTallyOf voters ballots)).steps.get
            ⟨idx, hidx_current⟩).beforeActive := by
      simpa [trace, current] using hactive_current
    have hsource_cap :
        profileActiveTallyOf voters ballots current.beforeActive source ≤
          (((predictLossesCandidates voters ballots candidates budget
            firstChoiceThreshold).toList).map transferOf).getD idx 0 := by
      exact
        hfocused_transfer_cap sequence hmem hfeasible idx
          (by simpa [trace] using hidx_current) source
          (by simpa [trace, current] using hfocus)
    have herase_bound :
        profileActiveTallyOf voters ballots (current.beforeActive.erase source)
            candidate ≤
          profileActiveTallyOf voters ballots current.beforeActive candidate +
            profileActiveTallyOf voters ballots current.beforeActive source :=
      profileActiveTallyOf_erase_le_self_add_source_of_mem
        voters ballots hactive_erase
    calc
      ((rcvGeneratedTraceOfStructure (structureOf sequence)
        (initialActive sequence)
        (profileActiveTallyOf voters ballots)).steps.get
        ⟨idx + 1, hidx_next⟩).tally candidate
          = profileActiveTallyOf voters ballots
              (current.beforeActive.erase source) candidate :=
          hnext_tally_erase
      _ ≤ profileActiveTallyOf voters ballots current.beforeActive candidate +
            profileActiveTallyOf voters ballots current.beforeActive source :=
          herase_bound
      _ ≤ profileActiveTallyOf voters ballots current.beforeActive candidate +
            (((predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold).toList).map transferOf).getD idx 0 :=
          Nat.add_le_add_left hsource_cap
            (profileActiveTallyOf voters ballots current.beforeActive candidate)
      _ =
          current.tally candidate +
            (((predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold).toList).map transferOf).getD idx 0 := by
          rw [← congrFun hcurrent_tally_eq candidate]
      _ =
          (if candidate ∈
              ((rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence)
                (profileActiveTallyOf voters ballots)).steps.get
                ⟨idx, hidx_current⟩).beforeActive then
            ((rcvGeneratedTraceOfStructure (structureOf sequence)
              (initialActive sequence)
              (profileActiveTallyOf voters ballots)).steps.get
              ⟨idx, hidx_current⟩).tally candidate
          else
            0) +
            (((predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold).toList).map transferOf).getD idx 0 := by
          rw [if_pos hactive_current_trace]

theorem proposition3_4_generatedStructureStepwiseTransferCheckOnFinset_initial_tally_le_topFirstChoice
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {feasibleSequence : Sequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {sourceSequences : Finset Sequence}
    {structureOf : Sequence → RCVStructure Candidate}
    {initialActive : Sequence → Finset Candidate}
    {tallyOf : Sequence → Finset Candidate → Candidate → ℕ}
    {transferOf : Candidate → ℕ}
    {budget quota firstChoiceThreshold topFirstChoice : ℕ}
    (hcheck :
      proposition3_4_generatedStructureStepwiseTransferCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        sourceSequences structureOf initialActive tallyOf transferOf budget
        quota firstChoiceThreshold topFirstChoice = true) :
    ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
      ∀ hpos :
        0 <
          predictLossesTransferInitialLossBound topFirstChoice quota
            (((predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold).toList).map transferOf),
      ∀ hidx :
        0 <
          (rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)).steps.length,
      ∀ candidate,
        candidate ∈
          ((rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)).steps.get
            ⟨0, hidx⟩).beforeActive →
        ((rcvGeneratedTraceOfStructure (structureOf sequence)
          (initialActive sequence) (tallyOf sequence)).steps.get
          ⟨0, hidx⟩).tally candidate ≤ topFirstChoice := by
  classical
  intro sequence hsequence hfeasible hpos hidx candidate hactive
  let transfers :=
    ((predictLossesCandidates voters ballots candidates budget
      firstChoiceThreshold).toList).map transferOf
  let lowerBound :=
    predictLossesTransferInitialLossBound topFirstChoice quota transfers
  let trace :=
    rcvGeneratedTraceOfStructure (structureOf sequence)
      (initialActive sequence) (tallyOf sequence)
  have hseq_all :
      (if feasibleSequence sequence then
        let trace :=
          rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)
        (List.range lowerBound).all fun idx =>
          ((if idx = 0 then
              match trace.steps[idx]? with
              | none => false
              | some step =>
                  decide
                    (∀ candidate, candidate ∈ step.beforeActive →
                      step.tally candidate ≤ topFirstChoice)
            else
              true) &&
            (if idx + 1 < lowerBound then
              match trace.steps[idx]?, trace.steps[idx + 1]? with
              | some current, some next =>
                  decide
                    (∀ candidate, candidate ∈ next.beforeActive →
                      next.tally candidate ≤
                        (if candidate ∈ current.beforeActive then
                          current.tally candidate
                        else
                          0) + transfers.getD idx 0)
              | _, _ => false
            else
              true))
      else
        true) = true := by
    have hall := List.all_eq_true.mp hcheck
    simpa [proposition3_4_generatedStructureStepwiseTransferCheckOnFinset,
      transfers, lowerBound] using
      hall sequence (Finset.mem_toList.mpr hsequence)
  have hrange_all :
      ((List.range lowerBound).all fun idx =>
        ((if idx = 0 then
            match trace.steps[idx]? with
            | none => false
            | some step =>
                decide
                  (∀ candidate, candidate ∈ step.beforeActive →
                    step.tally candidate ≤ topFirstChoice)
          else
            true) &&
          (if idx + 1 < lowerBound then
            match trace.steps[idx]?, trace.steps[idx + 1]? with
            | some current, some next =>
                decide
                  (∀ candidate, candidate ∈ next.beforeActive →
                    next.tally candidate ≤
                      (if candidate ∈ current.beforeActive then
                        current.tally candidate
                      else
                        0) + transfers.getD idx 0)
            | _, _ => false
          else
            true))) = true := by
    simpa [hfeasible, trace, lowerBound, transfers] using hseq_all
  have hidx_all :
      ((if 0 = 0 then
          match trace.steps[0]? with
          | none => false
          | some step =>
              decide
                (∀ candidate, candidate ∈ step.beforeActive →
                  step.tally candidate ≤ topFirstChoice)
        else
          true) &&
        (if 0 + 1 < lowerBound then
          match trace.steps[0]?, trace.steps[0 + 1]? with
          | some current, some next =>
              decide
                (∀ candidate, candidate ∈ next.beforeActive →
                  next.tally candidate ≤
                    (if candidate ∈ current.beforeActive then
                      current.tally candidate
                    else
                      0) + transfers.getD 0 0)
          | _, _ => false
        else
          true)) = true := by
    have hpos_lb : 0 < lowerBound := by
      simpa [lowerBound, transfers] using hpos
    exact (List.all_eq_true.mp hrange_all) 0 (by simpa using hpos_lb)
  have hidx_parts :
      (if 0 = 0 then
          match trace.steps[0]? with
          | none => false
          | some step =>
              decide
                (∀ candidate, candidate ∈ step.beforeActive →
                  step.tally candidate ≤ topFirstChoice)
        else
          true) = true ∧
        (if 0 + 1 < lowerBound then
          match trace.steps[0]?, trace.steps[0 + 1]? with
          | some current, some next =>
              decide
                (∀ candidate, candidate ∈ next.beforeActive →
                  next.tally candidate ≤
                    (if candidate ∈ current.beforeActive then
                      current.tally candidate
                    else
                      0) + transfers.getD 0 0)
          | _, _ => false
        else
          true) = true := by
    simpa [Bool.and_eq_true_eq_eq_true_and_eq_true] using hidx_all
  have hinitial_bool :
      (if 0 = 0 then
          match trace.steps[0]? with
          | none => false
          | some step =>
              decide
                (∀ candidate, candidate ∈ step.beforeActive →
                  step.tally candidate ≤ topFirstChoice)
        else
          true) = true :=
    hidx_parts.1
  have hstep_some :
      trace.steps[0]? = some (trace.steps.get ⟨0, hidx⟩) := by
    simpa using
      (List.getElem?_eq_getElem (l := trace.steps) (i := 0) hidx)
  have hcandidate_all :
      decide
        (∀ candidate, candidate ∈ (trace.steps.get ⟨0, hidx⟩).beforeActive →
          (trace.steps.get ⟨0, hidx⟩).tally candidate ≤
            topFirstChoice) = true := by
    simpa [hstep_some] using hinitial_bool
  exact (decide_eq_true_iff.mp hcandidate_all) candidate (by simpa [trace] using hactive)

theorem proposition3_4_generatedStructureStepwiseTransferCheckOnFinset_step_tally_le_transfer
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {feasibleSequence : Sequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {sourceSequences : Finset Sequence}
    {structureOf : Sequence → RCVStructure Candidate}
    {initialActive : Sequence → Finset Candidate}
    {tallyOf : Sequence → Finset Candidate → Candidate → ℕ}
    {transferOf : Candidate → ℕ}
    {budget quota firstChoiceThreshold topFirstChoice : ℕ}
    (hcheck :
      proposition3_4_generatedStructureStepwiseTransferCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        sourceSequences structureOf initialActive tallyOf transferOf budget
        quota firstChoiceThreshold topFirstChoice = true) :
    ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
      ∀ idx,
        ∀ hnext :
          idx + 1 <
            predictLossesTransferInitialLossBound topFirstChoice quota
              (((predictLossesCandidates voters ballots candidates budget
                firstChoiceThreshold).toList).map transferOf),
        ∀ hidx_next :
          idx + 1 <
            (rcvGeneratedTraceOfStructure (structureOf sequence)
              (initialActive sequence) (tallyOf sequence)).steps.length,
        ∀ hidx_current :
          idx <
            (rcvGeneratedTraceOfStructure (structureOf sequence)
              (initialActive sequence) (tallyOf sequence)).steps.length,
        ∀ candidate,
          candidate ∈
            ((rcvGeneratedTraceOfStructure (structureOf sequence)
              (initialActive sequence) (tallyOf sequence)).steps.get
              ⟨idx + 1, hidx_next⟩).beforeActive →
          ((rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)).steps.get
            ⟨idx + 1, hidx_next⟩).tally candidate ≤
            (if candidate ∈
                ((rcvGeneratedTraceOfStructure (structureOf sequence)
                  (initialActive sequence) (tallyOf sequence)).steps.get
                  ⟨idx, hidx_current⟩).beforeActive then
              ((rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence) (tallyOf sequence)).steps.get
                ⟨idx, hidx_current⟩).tally candidate
            else
              0) +
              (((predictLossesCandidates voters ballots candidates budget
                firstChoiceThreshold).toList).map transferOf).getD idx 0 := by
  classical
  intro sequence hsequence hfeasible idx hnext hidx_next hidx_current candidate
    hactive
  let transfers :=
    ((predictLossesCandidates voters ballots candidates budget
      firstChoiceThreshold).toList).map transferOf
  let lowerBound :=
    predictLossesTransferInitialLossBound topFirstChoice quota transfers
  let trace :=
    rcvGeneratedTraceOfStructure (structureOf sequence)
      (initialActive sequence) (tallyOf sequence)
  have hseq_all :
      (if feasibleSequence sequence then
        let trace :=
          rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)
        (List.range lowerBound).all fun idx =>
          ((if idx = 0 then
              match trace.steps[idx]? with
              | none => false
              | some step =>
                  decide
                    (∀ candidate, candidate ∈ step.beforeActive →
                      step.tally candidate ≤ topFirstChoice)
            else
              true) &&
            (if idx + 1 < lowerBound then
              match trace.steps[idx]?, trace.steps[idx + 1]? with
              | some current, some next =>
                  decide
                    (∀ candidate, candidate ∈ next.beforeActive →
                      next.tally candidate ≤
                        (if candidate ∈ current.beforeActive then
                          current.tally candidate
                        else
                          0) + transfers.getD idx 0)
              | _, _ => false
            else
              true))
      else
        true) = true := by
    have hall := List.all_eq_true.mp hcheck
    simpa [proposition3_4_generatedStructureStepwiseTransferCheckOnFinset,
      transfers, lowerBound] using
      hall sequence (Finset.mem_toList.mpr hsequence)
  have hrange_all :
      ((List.range lowerBound).all fun idx =>
        ((if idx = 0 then
            match trace.steps[idx]? with
            | none => false
            | some step =>
                decide
                  (∀ candidate, candidate ∈ step.beforeActive →
                    step.tally candidate ≤ topFirstChoice)
          else
            true) &&
          (if idx + 1 < lowerBound then
            match trace.steps[idx]?, trace.steps[idx + 1]? with
            | some current, some next =>
                decide
                  (∀ candidate, candidate ∈ next.beforeActive →
                    next.tally candidate ≤
                      (if candidate ∈ current.beforeActive then
                        current.tally candidate
                      else
                        0) + transfers.getD idx 0)
            | _, _ => false
          else
            true))) = true := by
    simpa [hfeasible, trace, lowerBound, transfers] using hseq_all
  have hidx_all :
      ((if idx = 0 then
          match trace.steps[idx]? with
          | none => false
          | some step =>
              decide
                (∀ candidate, candidate ∈ step.beforeActive →
                  step.tally candidate ≤ topFirstChoice)
        else
          true) &&
        (if idx + 1 < lowerBound then
          match trace.steps[idx]?, trace.steps[idx + 1]? with
          | some current, some next =>
              decide
                (∀ candidate, candidate ∈ next.beforeActive →
                  next.tally candidate ≤
                    (if candidate ∈ current.beforeActive then
                      current.tally candidate
                    else
                      0) + transfers.getD idx 0)
          | _, _ => false
        else
          true)) = true := by
    exact
      (List.all_eq_true.mp hrange_all) idx
        (by
          have hidx_lt : idx < lowerBound :=
            Nat.lt_trans (Nat.lt_succ_self idx) hnext
          simpa [lowerBound] using hidx_lt)
  have hidx_parts :
      (if idx = 0 then
          match trace.steps[idx]? with
          | none => false
          | some step =>
              decide
                (∀ candidate, candidate ∈ step.beforeActive →
                  step.tally candidate ≤ topFirstChoice)
        else
          true) = true ∧
        (if idx + 1 < lowerBound then
          match trace.steps[idx]?, trace.steps[idx + 1]? with
          | some current, some next =>
              decide
                (∀ candidate, candidate ∈ next.beforeActive →
                  next.tally candidate ≤
                    (if candidate ∈ current.beforeActive then
                      current.tally candidate
                    else
                      0) + transfers.getD idx 0)
          | _, _ => false
        else
          true) = true := by
    simpa [Bool.and_eq_true_eq_eq_true_and_eq_true] using hidx_all
  have hstep_bool :
      (if idx + 1 < lowerBound then
          match trace.steps[idx]?, trace.steps[idx + 1]? with
          | some current, some next =>
              decide
                (∀ candidate, candidate ∈ next.beforeActive →
                  next.tally candidate ≤
                    (if candidate ∈ current.beforeActive then
                      current.tally candidate
                    else
                      0) + transfers.getD idx 0)
          | _, _ => false
        else
          true) = true :=
    hidx_parts.2
  have hcurrent_some :
      trace.steps[idx]? = some (trace.steps.get ⟨idx, hidx_current⟩) := by
    simpa using
      (List.getElem?_eq_getElem (l := trace.steps) (i := idx)
        hidx_current)
  have hnext_some :
      trace.steps[idx + 1]? =
        some (trace.steps.get ⟨idx + 1, hidx_next⟩) := by
    simpa using
      (List.getElem?_eq_getElem (l := trace.steps) (i := idx + 1)
        hidx_next)
  have hcandidate_all :
      decide
        (∀ candidate,
          candidate ∈ (trace.steps.get ⟨idx + 1, hidx_next⟩).beforeActive →
            (trace.steps.get ⟨idx + 1, hidx_next⟩).tally candidate ≤
              (if candidate ∈
                  (trace.steps.get ⟨idx, hidx_current⟩).beforeActive then
                (trace.steps.get ⟨idx, hidx_current⟩).tally candidate
              else
                0) + transfers.getD idx 0) = true := by
    have hnext_lb : idx + 1 < lowerBound := by
      simpa [lowerBound, transfers] using hnext
    simpa [hnext_lb, hcurrent_some, hnext_some] using hstep_bool
  exact (decide_eq_true_iff.mp hcandidate_all) candidate (by simpa [trace] using hactive)

/--
Finite checker for the generated-structure source-run facts used by
Proposition 3.4.  For every feasible source sequence in the finite coverage
set it checks that the generated trace has the advertised win/loss sequence,
that every generated round constraint holds, that the structure has one label
per ordered candidate, and that the Predict-Losses lower bound fits inside the
generated order.
-/
noncomputable def proposition3_4_generatedStructureSourceRunCheckOnFinset
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate) (sourceSequences : Finset RCVSequence)
    (structureOf : RCVSequence → RCVStructure Candidate)
    (initialActive : RCVSequence → Finset Candidate)
    (tallyOf : RCVSequence → Finset Candidate → Candidate → ℕ)
    (transferOf : Candidate → ℕ)
    (budget quota firstChoiceThreshold topFirstChoice : ℕ) : Bool := by
  classical
  let transfers :=
    ((predictLossesCandidates voters ballots candidates budget
      firstChoiceThreshold).toList).map transferOf
  let lowerBound :=
    predictLossesTransferInitialLossBound topFirstChoice quota transfers
  exact sourceSequences.toList.all fun sequence =>
    if feasibleSequence sequence then
      let trace :=
        rcvGeneratedTraceOfStructure (structureOf sequence)
          (initialActive sequence) (tallyOf sequence)
      (decide (sequence = rcvSequenceFromTrace trace) &&
        decide ((structureOf sequence).validLength) &&
        decide (lowerBound ≤ (structureOf sequence).finalOrder.order.length) &&
        (rcvGeneratedStructureRoundConstraints (structureOf sequence)
            (initialActive sequence) (tallyOf sequence) quota).all
          fun constraint => decide constraint.Holds)
    else
      true

/--
Completeness for the generated-structure source-run checker: the advertised
sequence identity, valid generated structure, lower-bound fit, and generated
round constraints make the executable finite checker succeed.
-/
theorem proposition3_4_generatedStructureSourceRunCheckOnFinset_eq_true_of_facts
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {sourceSequences : Finset RCVSequence}
    {structureOf : RCVSequence → RCVStructure Candidate}
    {initialActive : RCVSequence → Finset Candidate}
    {tallyOf : RCVSequence → Finset Candidate → Candidate → ℕ}
    {transferOf : Candidate → ℕ}
    {budget quota firstChoiceThreshold topFirstChoice : ℕ}
    (hsequence_eq :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        sequence =
          rcvSequenceFromTrace
            (rcvGeneratedTraceOfStructure (structureOf sequence)
              (initialActive sequence) (tallyOf sequence)))
    (hvalid :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        (structureOf sequence).validLength)
    (hlowerBound :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        predictLossesTransferInitialLossBound topFirstChoice quota
            (((predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold).toList).map transferOf) ≤
          (structureOf sequence).finalOrder.order.length)
    (hconstraints :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        ∀ constraint,
          constraint ∈
            rcvGeneratedStructureRoundConstraints (structureOf sequence)
              (initialActive sequence) (tallyOf sequence) quota →
          constraint.Holds) :
    proposition3_4_generatedStructureSourceRunCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        sourceSequences structureOf initialActive tallyOf transferOf budget
        quota firstChoiceThreshold topFirstChoice = true := by
  classical
  unfold proposition3_4_generatedStructureSourceRunCheckOnFinset
  apply List.all_eq_true.mpr
  intro sequence hseq
  have hmem : sequence ∈ sourceSequences := Finset.mem_toList.mp hseq
  by_cases hfeasible : feasibleSequence sequence
  · let transfers :=
      ((predictLossesCandidates voters ballots candidates budget
        firstChoiceThreshold).toList).map transferOf
    let lowerBound :=
      predictLossesTransferInitialLossBound topFirstChoice quota transfers
    let trace :=
      rcvGeneratedTraceOfStructure (structureOf sequence)
        (initialActive sequence) (tallyOf sequence)
    have hconstraints_all :
        (rcvGeneratedStructureRoundConstraints (structureOf sequence)
            (initialActive sequence) (tallyOf sequence) quota).all
          (fun constraint => decide constraint.Holds) = true := by
      apply List.all_eq_true.mpr
      intro constraint hconstraint
      exact decide_eq_true
        (hconstraints sequence hmem hfeasible constraint hconstraint)
    have hsequence_decide :
        decide (sequence = rcvSequenceFromTrace trace) = true := by
      exact decide_eq_true
        (by
          simpa [trace] using hsequence_eq sequence hmem hfeasible)
    have hvalid_decide :
        decide ((structureOf sequence).validLength) = true := by
      exact decide_eq_true (hvalid sequence hmem hfeasible)
    have hlower_decide :
        decide (lowerBound ≤ (structureOf sequence).finalOrder.order.length) =
          true := by
      exact decide_eq_true
        (by
          simpa [lowerBound, transfers] using
            hlowerBound sequence hmem hfeasible)
    rw [if_pos hfeasible]
    change
      ((decide (sequence = rcvSequenceFromTrace trace) &&
          decide ((structureOf sequence).validLength) &&
          decide
            (lowerBound ≤ (structureOf sequence).finalOrder.order.length) &&
          (rcvGeneratedStructureRoundConstraints (structureOf sequence)
              (initialActive sequence) (tallyOf sequence) quota).all
            (fun constraint => decide constraint.Holds)) = true)
    rw [Bool.and_eq_true_eq_eq_true_and_eq_true]
    refine ⟨?_, hconstraints_all⟩
    rw [Bool.and_eq_true_eq_eq_true_and_eq_true]
    refine ⟨?_, hlower_decide⟩
    rw [Bool.and_eq_true_eq_eq_true_and_eq_true]
    exact ⟨hsequence_decide, hvalid_decide⟩
  · simp [hfeasible]

theorem proposition3_4_generatedStructureSourceRunCheckOnFinset_sequence_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {structureOf : RCVSequence → RCVStructure Candidate}
    {initialActive : RCVSequence → Finset Candidate}
    {tallyOf : RCVSequence → Finset Candidate → Candidate → ℕ}
    {transferOf : Candidate → ℕ}
    {budget quota firstChoiceThreshold topFirstChoice : ℕ}
    (hcheck :
      proposition3_4_generatedStructureSourceRunCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        allSequences structureOf initialActive tallyOf transferOf budget quota
        firstChoiceThreshold topFirstChoice = true) :
    ∀ sequence, sequence ∈ allSequences → feasibleSequence sequence →
      sequence =
        rcvSequenceFromTrace
          (rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)) := by
  classical
  intro sequence hsequence hfeasible
  let transfers :=
    ((predictLossesCandidates voters ballots candidates budget
      firstChoiceThreshold).toList).map transferOf
  let lowerBound :=
    predictLossesTransferInitialLossBound topFirstChoice quota transfers
  let trace :=
    rcvGeneratedTraceOfStructure (structureOf sequence)
      (initialActive sequence) (tallyOf sequence)
  have hseq_all :
      (if feasibleSequence sequence then
        let trace :=
          rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)
        (decide (sequence = rcvSequenceFromTrace trace) &&
          decide ((structureOf sequence).validLength) &&
          decide (lowerBound ≤ (structureOf sequence).finalOrder.order.length) &&
          (rcvGeneratedStructureRoundConstraints (structureOf sequence)
              (initialActive sequence) (tallyOf sequence) quota).all
            fun constraint => decide constraint.Holds)
      else
        true) = true := by
    have hall := List.all_eq_true.mp hcheck
    simpa [proposition3_4_generatedStructureSourceRunCheckOnFinset,
      transfers, lowerBound] using
      hall sequence (Finset.mem_toList.mpr hsequence)
  have hparts :
      ((sequence = rcvSequenceFromTrace trace ∧
          (structureOf sequence).validLength) ∧
        lowerBound ≤ (structureOf sequence).finalOrder.order.length) ∧
        ∀ constraint,
          constraint ∈
            rcvGeneratedStructureRoundConstraints (structureOf sequence)
              (initialActive sequence) (tallyOf sequence) quota →
          constraint.Holds := by
    simpa [hfeasible, trace, Bool.and_eq_true_eq_eq_true_and_eq_true] using
      hseq_all
  exact hparts.1.1.1

theorem proposition3_4_generatedStructureSourceRunCheckOnFinset_validLength
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {structureOf : RCVSequence → RCVStructure Candidate}
    {initialActive : RCVSequence → Finset Candidate}
    {tallyOf : RCVSequence → Finset Candidate → Candidate → ℕ}
    {transferOf : Candidate → ℕ}
    {budget quota firstChoiceThreshold topFirstChoice : ℕ}
    (hcheck :
      proposition3_4_generatedStructureSourceRunCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        allSequences structureOf initialActive tallyOf transferOf budget quota
        firstChoiceThreshold topFirstChoice = true) :
    ∀ sequence, sequence ∈ allSequences → feasibleSequence sequence →
      (structureOf sequence).validLength := by
  classical
  intro sequence hsequence hfeasible
  let transfers :=
    ((predictLossesCandidates voters ballots candidates budget
      firstChoiceThreshold).toList).map transferOf
  let lowerBound :=
    predictLossesTransferInitialLossBound topFirstChoice quota transfers
  let trace :=
    rcvGeneratedTraceOfStructure (structureOf sequence)
      (initialActive sequence) (tallyOf sequence)
  have hseq_all :
      (if feasibleSequence sequence then
        let trace :=
          rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)
        (decide (sequence = rcvSequenceFromTrace trace) &&
          decide ((structureOf sequence).validLength) &&
          decide (lowerBound ≤ (structureOf sequence).finalOrder.order.length) &&
          (rcvGeneratedStructureRoundConstraints (structureOf sequence)
              (initialActive sequence) (tallyOf sequence) quota).all
            fun constraint => decide constraint.Holds)
      else
        true) = true := by
    have hall := List.all_eq_true.mp hcheck
    simpa [proposition3_4_generatedStructureSourceRunCheckOnFinset,
      transfers, lowerBound] using
      hall sequence (Finset.mem_toList.mpr hsequence)
  have hparts :
      ((sequence = rcvSequenceFromTrace trace ∧
          (structureOf sequence).validLength) ∧
        lowerBound ≤ (structureOf sequence).finalOrder.order.length) ∧
        ∀ constraint,
          constraint ∈
            rcvGeneratedStructureRoundConstraints (structureOf sequence)
              (initialActive sequence) (tallyOf sequence) quota →
          constraint.Holds := by
    simpa [hfeasible, trace, Bool.and_eq_true_eq_eq_true_and_eq_true] using
      hseq_all
  exact hparts.1.1.2

theorem proposition3_4_generatedStructureSourceRunCheckOnFinset_order_prefix_len
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {structureOf : RCVSequence → RCVStructure Candidate}
    {initialActive : RCVSequence → Finset Candidate}
    {tallyOf : RCVSequence → Finset Candidate → Candidate → ℕ}
    {transferOf : Candidate → ℕ}
    {budget quota firstChoiceThreshold topFirstChoice : ℕ}
    (hcheck :
      proposition3_4_generatedStructureSourceRunCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        allSequences structureOf initialActive tallyOf transferOf budget quota
        firstChoiceThreshold topFirstChoice = true) :
    ∀ sequence, sequence ∈ allSequences → feasibleSequence sequence →
      predictLossesTransferInitialLossBound topFirstChoice quota
          (((predictLossesCandidates voters ballots candidates budget
            firstChoiceThreshold).toList).map transferOf) ≤
        (structureOf sequence).finalOrder.order.length := by
  classical
  intro sequence hsequence hfeasible
  let transfers :=
    ((predictLossesCandidates voters ballots candidates budget
      firstChoiceThreshold).toList).map transferOf
  let lowerBound :=
    predictLossesTransferInitialLossBound topFirstChoice quota transfers
  let trace :=
    rcvGeneratedTraceOfStructure (structureOf sequence)
      (initialActive sequence) (tallyOf sequence)
  have hseq_all :
      (if feasibleSequence sequence then
        let trace :=
          rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)
        (decide (sequence = rcvSequenceFromTrace trace) &&
          decide ((structureOf sequence).validLength) &&
          decide (lowerBound ≤ (structureOf sequence).finalOrder.order.length) &&
          (rcvGeneratedStructureRoundConstraints (structureOf sequence)
              (initialActive sequence) (tallyOf sequence) quota).all
            fun constraint => decide constraint.Holds)
      else
        true) = true := by
    have hall := List.all_eq_true.mp hcheck
    simpa [proposition3_4_generatedStructureSourceRunCheckOnFinset,
      transfers, lowerBound] using
      hall sequence (Finset.mem_toList.mpr hsequence)
  have hparts :
      ((sequence = rcvSequenceFromTrace trace ∧
          (structureOf sequence).validLength) ∧
        lowerBound ≤ (structureOf sequence).finalOrder.order.length) ∧
        ∀ constraint,
          constraint ∈
            rcvGeneratedStructureRoundConstraints (structureOf sequence)
              (initialActive sequence) (tallyOf sequence) quota →
          constraint.Holds := by
    simpa [hfeasible, trace, Bool.and_eq_true_eq_eq_true_and_eq_true] using
      hseq_all
  simpa [lowerBound, transfers] using hparts.1.2

theorem proposition3_4_generatedStructureSourceRunCheckOnFinset_constraints_hold
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {structureOf : RCVSequence → RCVStructure Candidate}
    {initialActive : RCVSequence → Finset Candidate}
    {tallyOf : RCVSequence → Finset Candidate → Candidate → ℕ}
    {transferOf : Candidate → ℕ}
    {budget quota firstChoiceThreshold topFirstChoice : ℕ}
    (hcheck :
      proposition3_4_generatedStructureSourceRunCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        allSequences structureOf initialActive tallyOf transferOf budget quota
        firstChoiceThreshold topFirstChoice = true) :
    ∀ sequence, sequence ∈ allSequences → feasibleSequence sequence →
      ∀ constraint,
        constraint ∈
          rcvGeneratedStructureRoundConstraints (structureOf sequence)
            (initialActive sequence) (tallyOf sequence) quota →
        constraint.Holds := by
  classical
  intro sequence hsequence hfeasible constraint hconstraint
  let transfers :=
    ((predictLossesCandidates voters ballots candidates budget
      firstChoiceThreshold).toList).map transferOf
  let lowerBound :=
    predictLossesTransferInitialLossBound topFirstChoice quota transfers
  let trace :=
    rcvGeneratedTraceOfStructure (structureOf sequence)
      (initialActive sequence) (tallyOf sequence)
  have hseq_all :
      (if feasibleSequence sequence then
        let trace :=
          rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence)
        (decide (sequence = rcvSequenceFromTrace trace) &&
          decide ((structureOf sequence).validLength) &&
          decide (lowerBound ≤ (structureOf sequence).finalOrder.order.length) &&
          (rcvGeneratedStructureRoundConstraints (structureOf sequence)
              (initialActive sequence) (tallyOf sequence) quota).all
            fun constraint => decide constraint.Holds)
      else
        true) = true := by
    have hall := List.all_eq_true.mp hcheck
    simpa [proposition3_4_generatedStructureSourceRunCheckOnFinset,
      transfers, lowerBound] using
      hall sequence (Finset.mem_toList.mpr hsequence)
  have hparts :
      ((sequence = rcvSequenceFromTrace trace ∧
          (structureOf sequence).validLength) ∧
        lowerBound ≤ (structureOf sequence).finalOrder.order.length) ∧
        ∀ constraint,
          constraint ∈
            rcvGeneratedStructureRoundConstraints (structureOf sequence)
              (initialActive sequence) (tallyOf sequence) quota →
          constraint.Holds := by
    simpa [hfeasible, trace, Bool.and_eq_true_eq_eq_true_and_eq_true] using
      hseq_all
  exact hparts.2 constraint hconstraint

/--
Finite source-run checker for the common sequence-labeled generated-structure
case.  The structure is built from a final order and the source sequence, so
the generated trace's win/loss sequence and `validLength` facts are derivable
from the constructor.  The executable check only needs the source length
agreement, the lower-bound fit, and generated round constraints.
-/
noncomputable def proposition3_4_sequenceLabeledGeneratedStructureSourceRunCheckOnFinset
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate)
    (sourceSequences : Finset RCVSequence)
    (finalOrderOf : RCVSequence → FinalOrder Candidate)
    (initialActive : RCVSequence → Finset Candidate)
    (tallyOf : RCVSequence → Finset Candidate → Candidate → ℕ)
    (transferOf : Candidate → ℕ)
    (budget quota firstChoiceThreshold topFirstChoice : ℕ) : Bool := by
  classical
  let transfers :=
    ((predictLossesCandidates voters ballots candidates budget
      firstChoiceThreshold).toList).map transferOf
  let lowerBound :=
    predictLossesTransferInitialLossBound topFirstChoice quota transfers
  exact sourceSequences.toList.all fun sequence =>
    if feasibleSequence sequence then
      let struct :=
        OrderSequenceStructure.ofFinalOrderAndSequence
          (finalOrderOf sequence) sequence
      decide (sequence.length = (finalOrderOf sequence).order.length) &&
        decide (lowerBound ≤ sequence.length) &&
        (rcvGeneratedStructureRoundConstraints struct
            (initialActive sequence) (tallyOf sequence) quota).all
          fun constraint => decide constraint.Holds
    else
      true

/--
Completeness for the sequence-labeled generated-structure source-run checker:
the source length, lower-bound, and generated-constraint facts make the
executable finite checker succeed.
-/
theorem proposition3_4_sequenceLabeledGeneratedStructureSourceRunCheckOnFinset_eq_true_of_facts
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {sourceSequences : Finset RCVSequence}
    {finalOrderOf : RCVSequence → FinalOrder Candidate}
    {initialActive : RCVSequence → Finset Candidate}
    {tallyOf : RCVSequence → Finset Candidate → Candidate → ℕ}
    {transferOf : Candidate → ℕ}
    {budget quota firstChoiceThreshold topFirstChoice : ℕ}
    (hlength :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        sequence.length = (finalOrderOf sequence).order.length)
    (hlowerBound :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        predictLossesTransferInitialLossBound topFirstChoice quota
            (((predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold).toList).map transferOf) ≤
          sequence.length)
    (hconstraints :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        ∀ constraint,
          constraint ∈
            rcvGeneratedStructureRoundConstraints
              (OrderSequenceStructure.ofFinalOrderAndSequence
                (finalOrderOf sequence) sequence)
              (initialActive sequence) (tallyOf sequence) quota →
          constraint.Holds) :
    proposition3_4_sequenceLabeledGeneratedStructureSourceRunCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        sourceSequences finalOrderOf initialActive tallyOf transferOf budget
        quota firstChoiceThreshold topFirstChoice = true := by
  classical
  apply List.all_eq_true.mpr
  intro sequence hseq
  have hmem : sequence ∈ sourceSequences := Finset.mem_toList.mp hseq
  by_cases hfeasible : feasibleSequence sequence
  · let struct :=
      OrderSequenceStructure.ofFinalOrderAndSequence
        (finalOrderOf sequence) sequence
    have hconstraints_all :
        (rcvGeneratedStructureRoundConstraints struct
            (initialActive sequence) (tallyOf sequence) quota).all
          (fun constraint => decide constraint.Holds) = true := by
      apply List.all_eq_true.mpr
      intro constraint hconstraint
      exact decide_eq_true_iff.mpr
        (by
          simpa [struct] using
            hconstraints sequence hmem hfeasible constraint hconstraint)
    have hlowerOrder :
        predictLossesTransferInitialLossBound topFirstChoice quota
            (((predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold).toList).map transferOf) ≤
          (finalOrderOf sequence).order.length := by
      simpa [hlength sequence hmem hfeasible] using
        hlowerBound sequence hmem hfeasible
    simp [hfeasible, struct, hlength sequence hmem hfeasible, hlowerOrder,
      hconstraints_all]
  · simp [hfeasible]

theorem proposition3_4_sequenceLabeledGeneratedStructureSourceRunCheckOnFinset_facts
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {finalOrderOf : RCVSequence → FinalOrder Candidate}
    {initialActive : RCVSequence → Finset Candidate}
    {tallyOf : RCVSequence → Finset Candidate → Candidate → ℕ}
    {transferOf : Candidate → ℕ}
    {budget quota firstChoiceThreshold topFirstChoice : ℕ}
    (hcheck :
      proposition3_4_sequenceLabeledGeneratedStructureSourceRunCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        allSequences finalOrderOf initialActive tallyOf transferOf budget quota
        firstChoiceThreshold topFirstChoice = true) :
    ∀ sequence, sequence ∈ allSequences → feasibleSequence sequence →
      let struct :=
        OrderSequenceStructure.ofFinalOrderAndSequence
          (finalOrderOf sequence) sequence
      sequence =
          rcvSequenceFromTrace
            (rcvGeneratedTraceOfStructure struct
              (initialActive sequence) (tallyOf sequence)) ∧
        struct.validLength ∧
        predictLossesTransferInitialLossBound topFirstChoice quota
            (((predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold).toList).map transferOf) ≤
          struct.finalOrder.order.length ∧
        ∀ constraint,
          constraint ∈
            rcvGeneratedStructureRoundConstraints struct
              (initialActive sequence) (tallyOf sequence) quota →
          constraint.Holds := by
  classical
  intro sequence hsequence hfeasible
  let transfers :=
    ((predictLossesCandidates voters ballots candidates budget
      firstChoiceThreshold).toList).map transferOf
  let lowerBound :=
    predictLossesTransferInitialLossBound topFirstChoice quota transfers
  let struct :=
    OrderSequenceStructure.ofFinalOrderAndSequence
      (finalOrderOf sequence) sequence
  have hseq_all :
      (if feasibleSequence sequence then
        let struct :=
          OrderSequenceStructure.ofFinalOrderAndSequence
            (finalOrderOf sequence) sequence
        decide (sequence.length = (finalOrderOf sequence).order.length) &&
          decide (lowerBound ≤ sequence.length) &&
          (rcvGeneratedStructureRoundConstraints struct
              (initialActive sequence) (tallyOf sequence) quota).all
            fun constraint => decide constraint.Holds
      else
        true) = true := by
    have hall := List.all_eq_true.mp hcheck
    simpa [proposition3_4_sequenceLabeledGeneratedStructureSourceRunCheckOnFinset,
      transfers, lowerBound] using
      hall sequence (Finset.mem_toList.mpr hsequence)
  have hparts :
      ((sequence.length = (finalOrderOf sequence).order.length ∧
          lowerBound ≤ sequence.length) ∧
        ∀ constraint,
          constraint ∈
            rcvGeneratedStructureRoundConstraints struct
              (initialActive sequence) (tallyOf sequence) quota →
          constraint.Holds) := by
    simpa [hfeasible, struct, Bool.and_eq_true_eq_eq_true_and_eq_true] using
      hseq_all
  have hvalid : struct.validLength := by
    exact
      OrderSequenceStructure.ofFinalOrderAndSequence_validLength
        (finalOrder := finalOrderOf sequence)
        (sequence := sequence) hparts.1.1
  have hsequence :
      sequence =
        rcvSequenceFromTrace
          (rcvGeneratedTraceOfStructure struct
            (initialActive sequence) (tallyOf sequence)) := by
    have hround :=
      OrderSequenceStructure.roundOutcomeSequence_generatedTrace_of_validLength
        (struct := struct)
        (initialActive := initialActive sequence)
        (tallyOf := tallyOf sequence) hvalid
    simpa [rcvSequenceFromTrace, rcvGeneratedTraceOfStructure, struct] using
      hround.symm
  have hprefix :
      predictLossesTransferInitialLossBound topFirstChoice quota
          (((predictLossesCandidates voters ballots candidates budget
            firstChoiceThreshold).toList).map transferOf) ≤
        struct.finalOrder.order.length := by
    simpa [lowerBound, transfers, struct, hparts.1.1] using hparts.1.2
  exact ⟨hsequence, hvalid, hprefix, hparts.2⟩

/--
Executable check for the Algorithm 7 Predict-Wins source order: every listed
candidate must be budget-ready at the prefix made of the earlier listed
candidates.
-/
noncomputable def predictWinsBudgetReadySourceOrderCheck
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate) (assignedBudget : Candidate → ℕ)
    (quota : ℕ) : List Candidate → List Candidate → Bool
  | processed, [] => true
  | processed, candidate :: rest =>
      decide
          (candidate ∈
            predictWinsBudgetReadyCandidatesAtPrefix voters ballots
              candidates assignedBudget quota processed) &&
        predictWinsBudgetReadySourceOrderCheck voters ballots candidates
          assignedBudget quota (processed ++ [candidate]) rest

/--
A successful source-order readiness check supplies the usual decomposition
premise used by the Predict-Wins loop lemmas.
-/
theorem predictWinsBudgetReadySourceOrderCheck_selected_ready
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {assignedBudget : Candidate → ℕ}
    {quota : ℕ} :
    ∀ {processed sourceOrder : List Candidate},
      predictWinsBudgetReadySourceOrderCheck voters ballots candidates
        assignedBudget quota processed sourceOrder = true →
      ∀ pref candidate suffix,
        sourceOrder = pref ++ candidate :: suffix →
          candidate ∈
            predictWinsBudgetReadyCandidatesAtPrefix voters ballots
              candidates assignedBudget quota (processed ++ pref) := by
  intro processed sourceOrder hcheck
  induction sourceOrder generalizing processed with
  | nil =>
      intro pref candidate suffix hdecomp
      cases pref <;> simp at hdecomp
  | cons head rest ih =>
      have hparts :
          decide
              (head ∈
                predictWinsBudgetReadyCandidatesAtPrefix voters ballots
                  candidates assignedBudget quota processed) = true ∧
            predictWinsBudgetReadySourceOrderCheck voters ballots candidates
              assignedBudget quota (processed ++ [head]) rest = true := by
        simpa [predictWinsBudgetReadySourceOrderCheck,
          Bool.and_eq_true_eq_eq_true_and_eq_true] using hcheck
      intro pref candidate suffix hdecomp
      cases pref with
      | nil =>
          simp only [List.nil_append] at hdecomp
          injection hdecomp with hcandidate _hsuffix
          subst candidate
          simpa using (decide_eq_true_iff.mp hparts.1)
      | cons first pref =>
          simp only [List.cons_append] at hdecomp
          injection hdecomp with hfirst htail
          subst first
          have hready :=
            ih hparts.2 pref candidate suffix htail
          simpa [List.append_assoc] using hready

/--
Completeness for the executable Predict-Wins source-order readiness check:
if every selected source-order candidate is ready at the processed prefix, the
Boolean traversal succeeds.
-/
theorem predictWinsBudgetReadySourceOrderCheck_eq_true_of_selected_ready
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {assignedBudget : Candidate → ℕ}
    {quota : ℕ} :
    ∀ {processed sourceOrder : List Candidate},
      (∀ pref candidate suffix,
        sourceOrder = pref ++ candidate :: suffix →
          candidate ∈
            predictWinsBudgetReadyCandidatesAtPrefix voters ballots
              candidates assignedBudget quota (processed ++ pref)) →
      predictWinsBudgetReadySourceOrderCheck voters ballots candidates
        assignedBudget quota processed sourceOrder = true := by
  intro processed sourceOrder hready
  induction sourceOrder generalizing processed with
  | nil =>
      simp [predictWinsBudgetReadySourceOrderCheck]
  | cons head rest ih =>
      have hhead :
          head ∈
            predictWinsBudgetReadyCandidatesAtPrefix voters ballots
              candidates assignedBudget quota processed := by
        simpa using hready [] head rest rfl
      have htail :
          predictWinsBudgetReadySourceOrderCheck voters ballots candidates
            assignedBudget quota (processed ++ [head]) rest = true := by
        apply ih
        intro pref candidate suffix hdecomp
        have hready' :
            candidate ∈
              predictWinsBudgetReadyCandidatesAtPrefix voters ballots
                candidates assignedBudget quota
                (processed ++ (head :: pref)) := by
          apply hready (head :: pref) candidate suffix
          simp [hdecomp]
        simpa [List.append_assoc] using hready'
      simp [predictWinsBudgetReadySourceOrderCheck, hhead, htail]

/--
Finite checker for the Predict-Wins source-order obligations in Proposition
3.4.  For every feasible sequence in the finite coverage set it checks the
seat bound, the equality between wins and the source winner list length, the
assigned-budget cap, the Predict-Wins support cap, and readiness of each
source winner at its processed prefix.
-/
noncomputable def proposition3_4_sourceWinnerOrderCheckOnFinset
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate) (sourceSequences : Finset RCVSequence)
    (winnerSourceOrder : RCVSequence → List Candidate)
    (assignedBudget : RCVSequence → Candidate → ℕ)
    (seats budget predictedWinSupport quota : ℕ) : Bool := by
  classical
  exact sourceSequences.toList.all fun sequence =>
    if feasibleSequence sequence then
      decide (rcvSequenceWinCount sequence ≤ seats) &&
        decide (rcvSequenceWinCount sequence =
          (winnerSourceOrder sequence).length) &&
        decide
          (((winnerSourceOrder sequence).map
            (assignedBudget sequence)).sum ≤ budget) &&
        decide
          (predictWinsSupport voters ballots candidates
              (winnerSourceOrder sequence) ≤ predictedWinSupport) &&
        predictWinsBudgetReadySourceOrderCheck voters ballots candidates
          (assignedBudget sequence) quota [] (winnerSourceOrder sequence)
    else
      true

/--
Completeness for the finite Predict-Wins source-order checker in Proposition
3.4.  Source facts over every feasible sequence in the finite coverage set are
exactly enough to make the executable checker return `true`.
-/
theorem proposition3_4_sourceWinnerOrderCheckOnFinset_eq_true_of_facts
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {sourceSequences : Finset RCVSequence}
    {winnerSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota : ℕ}
    (hseat :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        rcvSequenceWinCount sequence =
          (winnerSourceOrder sequence).length)
    (hbudget :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤ predictedWinSupport)
    (hready :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈
              predictWinsBudgetReadyCandidatesAtPrefix voters ballots
                candidates (assignedBudget sequence) quota pref) :
    proposition3_4_sourceWinnerOrderCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        sourceSequences winnerSourceOrder assignedBudget seats budget
        predictedWinSupport quota = true := by
  classical
  apply List.all_eq_true.mpr
  intro sequence hseq
  have hmem : sequence ∈ sourceSequences := Finset.mem_toList.mp hseq
  by_cases hfeasible : feasibleSequence sequence
  · have hready_check :
        predictWinsBudgetReadySourceOrderCheck voters ballots candidates
          (assignedBudget sequence) quota []
          (winnerSourceOrder sequence) = true :=
      predictWinsBudgetReadySourceOrderCheck_eq_true_of_selected_ready
        (processed := [])
        (sourceOrder := winnerSourceOrder sequence)
        (by
          intro pref candidate suffix hdecomp
          simpa using
            hready sequence hmem hfeasible pref candidate suffix hdecomp)
    have hseat_len : (winnerSourceOrder sequence).length ≤ seats := by
      rw [← hwinCount sequence hmem hfeasible]
      exact hseat sequence hmem hfeasible
    simp [hfeasible, hseat_len, hwinCount sequence hmem hfeasible,
      hbudget sequence hmem hfeasible, hsupport sequence hmem hfeasible,
      hready_check]
  · simp [hfeasible]

/--
Completeness for the finite Predict-Wins source-order checker from generated
winner election steps. This replaces the hand-stated source candidate/quota
readiness facts with the generated STV replay convention: each selected winner
appears at its prefix index in the generated final order and that generated
step is an election satisfying the generated quota constraints under the
Predict-Wins budget/strict-support tally model.
-/
theorem proposition3_4_sourceWinnerOrderCheckOnFinset_eq_true_of_generatedTrace_elects
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {sourceSequences : Finset RCVSequence}
    {winnerSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {structureOf : RCVSequence → RCVStructure Candidate}
    {initialActive : RCVSequence → Finset Candidate}
    {seats budget predictedWinSupport quota : ℕ}
    (hseat :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        rcvSequenceWinCount sequence =
          (winnerSourceOrder sequence).length)
    (hbudget :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤ predictedWinSupport)
    (horder :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        (structureOf sequence).finalOrder.order = winnerSourceOrder sequence)
    (horder_mem :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        ∀ source, source ∈ (structureOf sequence).finalOrder.order →
          source ∈ candidates)
    (hinitial :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        initialActive sequence = candidates)
    (hholds :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        ∀ constraint,
          constraint ∈
            rcvGeneratedStructureRoundConstraints (structureOf sequence)
              (initialActive sequence)
              (predictWinsBudgetStrictSupportTallyOf voters ballots candidates
                (assignedBudget sequence)) quota →
          constraint.Holds)
    (hidx :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            pref.length <
              (rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence)
                (predictWinsBudgetStrictSupportTallyOf voters ballots
                  candidates (assignedBudget sequence))).steps.length)
    (helect :
      ∀ (sequence : RCVSequence) (hmem : sequence ∈ sourceSequences),
        (hfeasible : feasibleSequence sequence) →
        ∀ pref candidate suffix,
          (hdecomp :
            winnerSourceOrder sequence = pref ++ candidate :: suffix) →
            (((rcvGeneratedTraceOfStructure (structureOf sequence)
              (initialActive sequence)
              (predictWinsBudgetStrictSupportTallyOf voters ballots candidates
                (assignedBudget sequence))).steps.get
                ⟨pref.length,
                  hidx sequence hmem hfeasible pref candidate suffix
                    hdecomp⟩).kind = StepKind.elect)) :
    proposition3_4_sourceWinnerOrderCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        sourceSequences winnerSourceOrder assignedBudget seats budget
        predictedWinSupport quota = true := by
  classical
  exact
    proposition3_4_sourceWinnerOrderCheckOnFinset_eq_true_of_facts
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (sourceSequences := sourceSequences)
      (winnerSourceOrder := winnerSourceOrder)
      (assignedBudget := assignedBudget)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      hseat hwinCount hbudget hsupport
      (fun sequence hmem hfeasible =>
        predictWinsBudgetReadySelections_of_generatedTrace_elects
          (voters := voters)
          (ballots := ballots)
          (candidates := candidates)
          (assignedBudget := assignedBudget sequence)
          (quota := quota)
          (struct := structureOf sequence)
          (initialActive := initialActive sequence)
          (sourceOrder := winnerSourceOrder sequence)
          (horder := horder sequence hmem hfeasible)
          (horder_mem := horder_mem sequence hmem hfeasible)
          (hinitial := hinitial sequence hmem hfeasible)
          (hholds := hholds sequence hmem hfeasible)
          (hidx := hidx sequence hmem hfeasible)
          (helect := helect sequence hmem hfeasible))

theorem proposition3_4_sourceWinnerOrderCheckOnFinset_facts
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {allSequences : Finset RCVSequence}
    {winnerSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota : ℕ}
    (hcheck :
      proposition3_4_sourceWinnerOrderCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        allSequences winnerSourceOrder assignedBudget seats budget
        predictedWinSupport quota = true) :
    ∀ sequence, sequence ∈ allSequences → feasibleSequence sequence →
      rcvSequenceWinCount sequence ≤ seats ∧
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length ∧
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget ∧
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤ predictedWinSupport ∧
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈
              predictWinsBudgetReadyCandidatesAtPrefix voters ballots
                candidates (assignedBudget sequence) quota pref := by
  classical
  intro sequence hsequence hfeasible
  have hseq_all :
      (if feasibleSequence sequence then
        decide (rcvSequenceWinCount sequence ≤ seats) &&
          decide (rcvSequenceWinCount sequence =
            (winnerSourceOrder sequence).length) &&
          decide
            (((winnerSourceOrder sequence).map
              (assignedBudget sequence)).sum ≤ budget) &&
          decide
            (predictWinsSupport voters ballots candidates
                (winnerSourceOrder sequence) ≤ predictedWinSupport) &&
          predictWinsBudgetReadySourceOrderCheck voters ballots candidates
            (assignedBudget sequence) quota [] (winnerSourceOrder sequence)
      else
        true) = true := by
    have hall := List.all_eq_true.mp hcheck
    simpa [proposition3_4_sourceWinnerOrderCheckOnFinset] using
      hall sequence (Finset.mem_toList.mpr hsequence)
  have hparts :
      ((((rcvSequenceWinCount sequence ≤ seats ∧
          rcvSequenceWinCount sequence =
            (winnerSourceOrder sequence).length) ∧
          ((winnerSourceOrder sequence).map
            (assignedBudget sequence)).sum ≤ budget) ∧
          predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤ predictedWinSupport) ∧
          predictWinsBudgetReadySourceOrderCheck voters ballots candidates
            (assignedBudget sequence) quota []
            (winnerSourceOrder sequence) = true) := by
    simpa [hfeasible, Bool.and_eq_true_eq_eq_true_and_eq_true] using
      hseq_all
  refine ⟨hparts.1.1.1.1, hparts.1.1.1.2, hparts.1.1.2,
    hparts.1.2, ?_⟩
  intro pref candidate suffix hdecomp
  have hready :=
    predictWinsBudgetReadySourceOrderCheck_selected_ready
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (assignedBudget := assignedBudget sequence) (quota := quota)
      hparts.2 pref candidate suffix hdecomp
  simpa using hready

theorem proposition3_4_sourceWinnerOrderCheckOnFinset_seat
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {allSequences : Finset RCVSequence}
    {winnerSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota : ℕ}
    (hcheck :
      proposition3_4_sourceWinnerOrderCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        allSequences winnerSourceOrder assignedBudget seats budget
        predictedWinSupport quota = true) :
    ∀ sequence, sequence ∈ allSequences → feasibleSequence sequence →
      rcvSequenceWinCount sequence ≤ seats := by
  intro sequence hsequence hfeasible
  exact
    (proposition3_4_sourceWinnerOrderCheckOnFinset_facts
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (allSequences := allSequences) (winnerSourceOrder := winnerSourceOrder)
      (assignedBudget := assignedBudget) (seats := seats) (budget := budget)
      (predictedWinSupport := predictedWinSupport) (quota := quota)
      hcheck sequence hsequence hfeasible).1

theorem proposition3_4_sourceWinnerOrderCheckOnFinset_winCount_eq
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {allSequences : Finset RCVSequence}
    {winnerSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota : ℕ}
    (hcheck :
      proposition3_4_sourceWinnerOrderCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        allSequences winnerSourceOrder assignedBudget seats budget
        predictedWinSupport quota = true) :
    ∀ sequence, sequence ∈ allSequences → feasibleSequence sequence →
      rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length := by
  intro sequence hsequence hfeasible
  exact
    (proposition3_4_sourceWinnerOrderCheckOnFinset_facts
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (allSequences := allSequences) (winnerSourceOrder := winnerSourceOrder)
      (assignedBudget := assignedBudget) (seats := seats) (budget := budget)
      (predictedWinSupport := predictedWinSupport) (quota := quota)
      hcheck sequence hsequence hfeasible).2.1

theorem proposition3_4_sourceWinnerOrderCheckOnFinset_assignedBudget_le
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {allSequences : Finset RCVSequence}
    {winnerSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota : ℕ}
    (hcheck :
      proposition3_4_sourceWinnerOrderCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        allSequences winnerSourceOrder assignedBudget seats budget
        predictedWinSupport quota = true) :
    ∀ sequence, sequence ∈ allSequences → feasibleSequence sequence →
      ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
        budget := by
  intro sequence hsequence hfeasible
  exact
    (proposition3_4_sourceWinnerOrderCheckOnFinset_facts
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (allSequences := allSequences) (winnerSourceOrder := winnerSourceOrder)
      (assignedBudget := assignedBudget) (seats := seats) (budget := budget)
      (predictedWinSupport := predictedWinSupport) (quota := quota)
      hcheck sequence hsequence hfeasible).2.2.1

theorem proposition3_4_sourceWinnerOrderCheckOnFinset_support_le
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {allSequences : Finset RCVSequence}
    {winnerSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota : ℕ}
    (hcheck :
      proposition3_4_sourceWinnerOrderCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        allSequences winnerSourceOrder assignedBudget seats budget
        predictedWinSupport quota = true) :
    ∀ sequence, sequence ∈ allSequences → feasibleSequence sequence →
      predictWinsSupport voters ballots candidates (winnerSourceOrder sequence) ≤
        predictedWinSupport := by
  intro sequence hsequence hfeasible
  exact
    (proposition3_4_sourceWinnerOrderCheckOnFinset_facts
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (allSequences := allSequences) (winnerSourceOrder := winnerSourceOrder)
      (assignedBudget := assignedBudget) (seats := seats) (budget := budget)
      (predictedWinSupport := predictedWinSupport) (quota := quota)
      hcheck sequence hsequence hfeasible).2.2.2.1

theorem proposition3_4_sourceWinnerOrderCheckOnFinset_selected_candidate
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {allSequences : Finset RCVSequence}
    {winnerSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota : ℕ}
    (hcheck :
      proposition3_4_sourceWinnerOrderCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        allSequences winnerSourceOrder assignedBudget seats budget
        predictedWinSupport quota = true) :
    ∀ sequence, sequence ∈ allSequences → feasibleSequence sequence →
      ∀ pref candidate suffix,
        winnerSourceOrder sequence = pref ++ candidate :: suffix →
          candidate ∈ candidates := by
  intro sequence hsequence hfeasible pref candidate suffix hdecomp
  have hready :=
    (proposition3_4_sourceWinnerOrderCheckOnFinset_facts
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (allSequences := allSequences) (winnerSourceOrder := winnerSourceOrder)
      (assignedBudget := assignedBudget) (seats := seats) (budget := budget)
      (predictedWinSupport := predictedWinSupport) (quota := quota)
      hcheck sequence hsequence hfeasible).2.2.2.2
        pref candidate suffix hdecomp
  exact (mem_predictWinsBudgetReadyCandidatesAtPrefix_iff.mp hready).1

theorem proposition3_4_sourceWinnerOrderCheckOnFinset_selected_quota
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {allSequences : Finset RCVSequence}
    {winnerSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {seats budget predictedWinSupport quota : ℕ}
    (hcheck :
      proposition3_4_sourceWinnerOrderCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        allSequences winnerSourceOrder assignedBudget seats budget
        predictedWinSupport quota = true) :
    ∀ sequence, sequence ∈ allSequences → feasibleSequence sequence →
      ∀ pref candidate suffix,
        winnerSourceOrder sequence = pref ++ candidate :: suffix →
          quota ≤ assignedBudget sequence candidate +
            strictSupportCount voters ballots candidates
              (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref)
              candidate := by
  intro sequence hsequence hfeasible pref candidate suffix hdecomp
  have hready :=
    (proposition3_4_sourceWinnerOrderCheckOnFinset_facts
      (voters := voters) (ballots := ballots) (candidates := candidates)
      (allSequences := allSequences) (winnerSourceOrder := winnerSourceOrder)
      (assignedBudget := assignedBudget) (seats := seats) (budget := budget)
      (predictedWinSupport := predictedWinSupport) (quota := quota)
      hcheck sequence hsequence hfeasible).2.2.2.2
        pref candidate suffix hdecomp
  exact (mem_predictWinsBudgetReadyCandidatesAtPrefix_iff.mp hready).2

theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_validGeneratedStructureStepwiseTransferCheck_exactPredictLossesToList_mappedTransfers
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    {winnerSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {structureOf : RCVSequence → RCVStructure Candidate}
    {initialActive : RCVSequence → Finset Candidate}
    {tallyOf : RCVSequence → Finset Candidate → Candidate → ℕ}
    (transferOf : Candidate → ℕ)
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hselected_candidate :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈ candidates)
    (hselected_quota :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            quota ≤ assignedBudget sequence candidate +
              strictSupportCount voters ballots candidates
                (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref)
                candidate)
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_generated :
      ∀ sequence, feasibleSequence sequence →
        traceOf sequence =
          rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (tallyOf sequence))
    (hgenerated_constraints_hold :
      ∀ sequence, feasibleSequence sequence →
        ∀ constraint,
          constraint ∈
            rcvGeneratedStructureRoundConstraints (structureOf sequence)
              (initialActive sequence) (tallyOf sequence) quota →
          constraint.Holds)
    (hgenerated_valid_length :
      ∀ sequence, feasibleSequence sequence →
        (structureOf sequence).validLength)
    (hgenerated_order_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        predictLossesTransferInitialLossBound topFirstChoice quota
            (((predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold).toList).map transferOf) ≤
          (structureOf sequence).finalOrder.order.length)
    (htop_lt_quota : topFirstChoice < quota)
    (hstepwise_check :
      proposition3_4_generatedStructureStepwiseTransferCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        allSequences structureOf initialActive tallyOf transferOf budget quota
        firstChoiceThreshold topFirstChoice = true) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota
        (predictLossesTransferInitialLossBound topFirstChoice quota
          (((predictLossesCandidates voters ballots candidates budget
            firstChoiceThreshold).toList).map transferOf))
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  refine
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_validGeneratedStructureStepwiseTransferTallies_exactPredictLossesToList_mappedTransfers
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (structureOf := structureOf)
      (initialActive := initialActive)
      (tallyOf := tallyOf)
      (transferOf := transferOf)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwinCount_source_eq hassignedBudget_source_le
      hsupport_source_le hselected_candidate hselected_quota hsequence_eq
      htrace_generated hgenerated_constraints_hold hgenerated_valid_length
      hgenerated_order_prefix_len htop_lt_quota ?_ ?_
  · intro sequence hfeasible hpos hidx candidate hactive
    exact
      proposition3_4_generatedStructureStepwiseTransferCheckOnFinset_initial_tally_le_topFirstChoice
        (feasibleSequence := feasibleSequence)
        (voters := voters)
        (ballots := ballots)
        (candidates := candidates)
        (sourceSequences := allSequences)
        (structureOf := structureOf)
        (initialActive := initialActive)
        (tallyOf := tallyOf)
        (transferOf := transferOf)
        (budget := budget)
        (quota := quota)
        (firstChoiceThreshold := firstChoiceThreshold)
        (topFirstChoice := topFirstChoice)
        hstepwise_check sequence (hall sequence hfeasible) hfeasible hpos
        hidx candidate hactive
  · intro sequence hfeasible idx hnext hidx_next hidx_current candidate hactive
    exact
      proposition3_4_generatedStructureStepwiseTransferCheckOnFinset_step_tally_le_transfer
        (feasibleSequence := feasibleSequence)
        (voters := voters)
        (ballots := ballots)
        (candidates := candidates)
        (sourceSequences := allSequences)
        (structureOf := structureOf)
        (initialActive := initialActive)
        (tallyOf := tallyOf)
        (transferOf := transferOf)
        (budget := budget)
        (quota := quota)
        (firstChoiceThreshold := firstChoiceThreshold)
        (topFirstChoice := topFirstChoice)
        hstepwise_check sequence (hall sequence hfeasible) hfeasible idx
        hnext hidx_next hidx_current candidate hactive

/--
Concrete Proposition 3.4 generated-structure route with profile-derived
stepwise transfer accounting.  The generated source run still supplies the
round constraints and prefix length facts, while the transfer checker is
derived from the profile active tally, the global top-first-choice cap, and a
source-shaped cap on each focused candidate's current tally.
-/
theorem proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_validGeneratedStructureProfileTallyCaps_exactPredictLossesToList_mappedTransfers
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate}
    {allSequences : Finset RCVSequence}
    {feasibleSequence : RCVSequence → Prop} [DecidablePred feasibleSequence]
    {winnerSourceOrder : RCVSequence → List Candidate}
    {assignedBudget : RCVSequence → Candidate → ℕ}
    {traceOf : RCVSequence → RCVTrace Candidate}
    {structureOf : RCVSequence → RCVStructure Candidate}
    {initialActive : RCVSequence → Finset Candidate}
    (transferOf : Candidate → ℕ)
    {seats budget predictedWinSupport quota firstChoiceThreshold
      topFirstChoice uniqueBallotCount candidateCount : ℕ}
    (hall : ∀ sequence, feasibleSequence sequence → sequence ∈ allSequences)
    (hquota_pos : 0 < quota)
    (hseat :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence ≤ seats)
    (hwinCount_source_eq :
      ∀ sequence, feasibleSequence sequence →
        rcvSequenceWinCount sequence = (winnerSourceOrder sequence).length)
    (hassignedBudget_source_le :
      ∀ sequence, feasibleSequence sequence →
        ((winnerSourceOrder sequence).map (assignedBudget sequence)).sum ≤
          budget)
    (hsupport_source_le :
      ∀ sequence, feasibleSequence sequence →
        predictWinsSupport voters ballots candidates
            (winnerSourceOrder sequence) ≤
          predictedWinSupport)
    (hselected_candidate :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            candidate ∈ candidates)
    (hselected_quota :
      ∀ sequence, feasibleSequence sequence →
        ∀ pref candidate suffix,
          winnerSourceOrder sequence = pref ++ candidate :: suffix →
            quota ≤ assignedBudget sequence candidate +
              strictSupportCount voters ballots candidates
                (Ballot.blockersAfterPrefix (∅ : Finset Candidate) pref)
                candidate)
    (hsequence_eq :
      ∀ sequence, feasibleSequence sequence →
        sequence = rcvSequenceFromTrace (traceOf sequence))
    (htrace_generated :
      ∀ sequence, feasibleSequence sequence →
        traceOf sequence =
          rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence) (profileActiveTallyOf voters ballots))
    (hgenerated_constraints_hold :
      ∀ sequence, feasibleSequence sequence →
        ∀ constraint,
          constraint ∈
            rcvGeneratedStructureRoundConstraints (structureOf sequence)
              (initialActive sequence) (profileActiveTallyOf voters ballots)
              quota →
          constraint.Holds)
    (hgenerated_valid_length :
      ∀ sequence, feasibleSequence sequence →
        (structureOf sequence).validLength)
    (hgenerated_order_prefix_len :
      ∀ sequence, feasibleSequence sequence →
        predictLossesTransferInitialLossBound topFirstChoice quota
            (((predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold).toList).map transferOf) ≤
          (structureOf sequence).finalOrder.order.length)
    (hinitial_subset_candidates :
      ∀ sequence, sequence ∈ allSequences → feasibleSequence sequence →
        initialActive sequence ⊆ candidates)
    (hfirst_initial :
      ∀ sequence, sequence ∈ allSequences → feasibleSequence sequence →
        ∀ voter, voter ∈ voters →
          Ballot.firstChoiceIn (ballots voter) (initialActive sequence))
    (hglobal_first_le :
      ∀ candidate, candidate ∈ candidates →
        Ballot.firstChoiceCount voters ballots candidate ≤ topFirstChoice)
    (hfocused_transfer_cap :
      ∀ sequence, sequence ∈ allSequences → feasibleSequence sequence →
        ∀ idx,
          ∀ hidx :
            idx <
              (rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence)
                (profileActiveTallyOf voters ballots)).steps.length,
          ∀ source,
            ((rcvGeneratedTraceOfStructure (structureOf sequence)
              (initialActive sequence)
              (profileActiveTallyOf voters ballots)).steps.get
              ⟨idx, hidx⟩).focus = some source →
            profileActiveTallyOf voters ballots
                (((rcvGeneratedTraceOfStructure (structureOf sequence)
                  (initialActive sequence)
                  (profileActiveTallyOf voters ballots)).steps.get
                  ⟨idx, hidx⟩).beforeActive) source ≤
              (((predictLossesCandidates voters ballots candidates budget
                firstChoiceThreshold).toList).map transferOf).getD idx 0)
    (htop_lt_quota : topFirstChoice < quota) :
    (sequenceReductionConcreteCoverageProblem feasibleSequence budget
        uniqueBallotCount candidateCount).specification
      (sequenceReductionConcreteCoverageAlgorithm allSequences
        rcvSequenceWinCount rcvSequenceInitialLossCount seats
        predictedWinSupport quota
        (predictLossesTransferInitialLossBound topFirstChoice quota
          (((predictLossesCandidates voters ballots candidates budget
            firstChoiceThreshold).toList).map transferOf))
        (sequenceReductionConcreteCoverageProblem feasibleSequence budget
          uniqueBallotCount candidateCount)) ∧
      sequenceReductionConcreteCoverageOperationCount
          (Sequence := RCVSequence)
          (sequenceReductionConcreteCoverageProblem feasibleSequence budget
            uniqueBallotCount candidateCount) ≤
        uniqueBallotCount * candidateCount ^ 2 := by
  classical
  have htrace_prefix_len :
      ∀ sequence, sequence ∈ allSequences → feasibleSequence sequence →
        predictLossesTransferInitialLossBound topFirstChoice quota
            (((predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold).toList).map transferOf) ≤
          (rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence)
            (profileActiveTallyOf voters ballots)).steps.length := by
    intro sequence _hmem hfeasible
    have horder := hgenerated_order_prefix_len sequence hfeasible
    have hsequence :
        predictLossesTransferInitialLossBound topFirstChoice quota
            (((predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold).toList).map transferOf) ≤
          (structureOf sequence).sequence.length := by
      have hvalid := hgenerated_valid_length sequence hfeasible
      rw [OrderSequenceStructure.validLength] at hvalid
      rw [hvalid]
      exact horder
    simpa [rcvGeneratedTraceOfStructure] using
      (OrderSequenceStructure.le_generatedTrace_steps_length_of_le_order_length_of_le_sequence_length
        (struct := structureOf sequence)
        (initialActive := initialActive sequence)
        (tallyOf := profileActiveTallyOf voters ballots)
        horder hsequence)
  have hstepwise_check :
      proposition3_4_generatedStructureStepwiseTransferCheckOnFinset
        (feasibleSequence := feasibleSequence) voters ballots candidates
        allSequences structureOf initialActive
        (fun _ => profileActiveTallyOf voters ballots) transferOf budget
        quota firstChoiceThreshold topFirstChoice = true :=
    proposition3_4_generatedStructureStepwiseTransferCheckOnFinset_eq_true_of_profile_tallies
      (feasibleSequence := feasibleSequence)
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (sourceSequences := allSequences)
      (structureOf := structureOf)
      (initialActive := initialActive)
      (transferOf := transferOf)
      (budget := budget)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      htrace_prefix_len hinitial_subset_candidates hfirst_initial
      hglobal_first_le hfocused_transfer_cap
  exact
    proposition3_4_concreteCoverageAlgorithmImplementation_sound_and_quadratic_runtime_of_validGeneratedStructureStepwiseTransferCheck_exactPredictLossesToList_mappedTransfers
      (voters := voters)
      (ballots := ballots)
      (candidates := candidates)
      (allSequences := allSequences)
      (feasibleSequence := feasibleSequence)
      (winnerSourceOrder := winnerSourceOrder)
      (assignedBudget := assignedBudget)
      (traceOf := traceOf)
      (structureOf := structureOf)
      (initialActive := initialActive)
      (tallyOf := fun _ => profileActiveTallyOf voters ballots)
      (transferOf := transferOf)
      (seats := seats)
      (budget := budget)
      (predictedWinSupport := predictedWinSupport)
      (quota := quota)
      (firstChoiceThreshold := firstChoiceThreshold)
      (topFirstChoice := topFirstChoice)
      (uniqueBallotCount := uniqueBallotCount)
      (candidateCount := candidateCount)
      hall hquota_pos hseat hwinCount_source_eq hassignedBudget_source_le
      hsupport_source_le hselected_candidate hselected_quota hsequence_eq
      htrace_generated hgenerated_constraints_hold hgenerated_valid_length
      hgenerated_order_prefix_len htop_lt_quota hstepwise_check

/--
Generated-order bridge for Algorithm 7 focused transfer caps.  If the
structure order is exactly the Predict-Losses transfer order, then a source
bound by the focused candidate's own transfer value supplies the indexed
`getD` transfer-list bound used by the generated-profile route.
-/
theorem proposition3_4_generatedStructureFocusedTransferCap_of_order_eq_predictLossesToList_profile_tally_le_transferOf
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {feasibleSequence : Sequence → Prop}
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {sourceSequences : Finset Sequence}
    {structureOf : Sequence → RCVStructure Candidate}
    {initialActive : Sequence → Finset Candidate}
    {transferOf : Candidate → ℕ}
    {budget firstChoiceThreshold : ℕ}
    (horder_eq :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        (structureOf sequence).finalOrder.order =
          (predictLossesCandidates voters ballots candidates budget
            firstChoiceThreshold).toList)
    (hfocused_tally_le_transferOf :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        ∀ idx,
          ∀ hidx :
            idx <
              (rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence)
                (profileActiveTallyOf voters ballots)).steps.length,
          ∀ source,
            ((rcvGeneratedTraceOfStructure (structureOf sequence)
              (initialActive sequence)
              (profileActiveTallyOf voters ballots)).steps.get
              ⟨idx, hidx⟩).focus = some source →
            profileActiveTallyOf voters ballots
                (((rcvGeneratedTraceOfStructure (structureOf sequence)
                  (initialActive sequence)
                  (profileActiveTallyOf voters ballots)).steps.get
                  ⟨idx, hidx⟩).beforeActive) source ≤
              transferOf source) :
    ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
      ∀ idx,
        ∀ hidx :
          idx <
            (rcvGeneratedTraceOfStructure (structureOf sequence)
              (initialActive sequence)
              (profileActiveTallyOf voters ballots)).steps.length,
        ∀ source,
          ((rcvGeneratedTraceOfStructure (structureOf sequence)
            (initialActive sequence)
            (profileActiveTallyOf voters ballots)).steps.get
            ⟨idx, hidx⟩).focus = some source →
          profileActiveTallyOf voters ballots
              (((rcvGeneratedTraceOfStructure (structureOf sequence)
                (initialActive sequence)
                (profileActiveTallyOf voters ballots)).steps.get
                ⟨idx, hidx⟩).beforeActive) source ≤
            (((predictLossesCandidates voters ballots candidates budget
              firstChoiceThreshold).toList).map transferOf).getD idx 0 := by
  classical
  intro sequence hmem hfeasible idx hidx source hfocus
  let trace :=
    rcvGeneratedTraceOfStructure (structureOf sequence)
      (initialActive sequence) (profileActiveTallyOf voters ballots)
  let losses :=
    (predictLossesCandidates voters ballots candidates budget
      firstChoiceThreshold).toList
  have hfocus_order :
      (structureOf sequence).finalOrder.order[idx]? = some source := by
    have hfocus_eq :=
      OrderSequenceStructure.generatedTrace_get_focus_eq_order_get?
        (structureOf sequence) (initialActive sequence)
        (profileActiveTallyOf voters ballots) ⟨idx, hidx⟩
    simpa [trace] using hfocus_eq.symm.trans hfocus
  have hloss_get : losses[idx]? = some source := by
    simpa [losses, horder_eq sequence hmem hfeasible] using hfocus_order
  have hidx_losses : idx < losses.length := by
    rw [List.getElem?_eq_some_iff] at hloss_get
    rcases hloss_get with ⟨hidx_losses, _⟩
    exact hidx_losses
  have hmap_get :
      (losses.map transferOf)[idx]? = some (transferOf source) := by
    simpa [List.getElem?_map] using
      congrArg (Option.map transferOf) hloss_get
  have hgetD :
      (losses.map transferOf).getD idx 0 = transferOf source := by
    rw [List.getD_eq_getElem]
    · have hidx_map : idx < (losses.map transferOf).length := by
        simpa using hidx_losses
      have hsome :
          (losses.map transferOf)[idx]? =
            some ((losses.map transferOf)[idx]) := by
        simpa using
          (List.getElem?_eq_getElem (l := losses.map transferOf) (i := idx)
            hidx_map)
      exact Option.some.inj (hsome.symm.trans hmap_get)
    · simpa using hidx_losses
  calc
    profileActiveTallyOf voters ballots
        (((rcvGeneratedTraceOfStructure (structureOf sequence)
          (initialActive sequence)
          (profileActiveTallyOf voters ballots)).steps.get
          ⟨idx, hidx⟩).beforeActive) source
        ≤ transferOf source :=
      hfocused_tally_le_transferOf sequence hmem hfeasible idx hidx source
        hfocus
    _ =
        (((predictLossesCandidates voters ballots candidates budget
          firstChoiceThreshold).toList).map transferOf).getD idx 0 := by
      simpa [losses] using hgetD.symm

/--
Algorithm 7 profile-transfer value for a predicted losing candidate.  The
value is the profile tally when exactly the earlier Predict-Losses candidates
have been removed from the candidate set, matching the generated replay
convention for the loss order.
-/
noncomputable def predictLossesProfileTransferValue
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → RCVBallot Candidate)
    (candidates : Finset Candidate) (budget firstChoiceThreshold : ℕ)
    (source : Candidate) : ℕ :=
  let losses :=
    (predictLossesCandidates voters ballots candidates budget
      firstChoiceThreshold).toList
  profileActiveTallyOf voters ballots
    (candidates \ (losses.take (losses.idxOf source)).toFinset) source

/--
Generated-order bridge for Algorithm 7's canonical profile-transfer values.
If every generated final order is exactly the Predict-Losses order and the
generated replay starts from the paper candidate set, then the focused tally at
each generated step is exactly the candidate-keyed profile-transfer value used
by Algorithm 7.
-/
theorem proposition3_4_generatedStructureFocusedTransferCap_of_order_eq_predictLossesToList_profile_prefix_transferValue
    {Voter Candidate Sequence : Type*} [DecidableEq Candidate]
    {feasibleSequence : Sequence → Prop}
    {voters : Finset Voter} {ballots : Voter → RCVBallot Candidate}
    {candidates : Finset Candidate} {sourceSequences : Finset Sequence}
    {structureOf : Sequence → RCVStructure Candidate}
    {budget firstChoiceThreshold : ℕ}
    (horder_eq :
      ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
        (structureOf sequence).finalOrder.order =
          (predictLossesCandidates voters ballots candidates budget
            firstChoiceThreshold).toList) :
    ∀ sequence, sequence ∈ sourceSequences → feasibleSequence sequence →
      ∀ idx,
        ∀ hidx :
          idx <
            (rcvGeneratedTraceOfStructure (structureOf sequence)
              candidates (profileActiveTallyOf voters ballots)).steps.length,
        ∀ source,
          ((rcvGeneratedTraceOfStructure (structureOf sequence)
            candidates (profileActiveTallyOf voters ballots)).steps.get
            ⟨idx, hidx⟩).focus = some source →
          profileActiveTallyOf voters ballots
              (((rcvGeneratedTraceOfStructure (structureOf sequence)
                candidates (profileActiveTallyOf voters ballots)).steps.get
                ⟨idx, hidx⟩).beforeActive) source ≤
            predictLossesProfileTransferValue voters ballots candidates budget
              firstChoiceThreshold source := by
  classical
  intro sequence hmem hfeasible idx hidx source hfocus
  let trace :=
    rcvGeneratedTraceOfStructure (structureOf sequence)
      candidates (profileActiveTallyOf voters ballots)
  let losses :=
    (predictLossesCandidates voters ballots candidates budget
      firstChoiceThreshold).toList
  have hfocus_order :
      (structureOf sequence).finalOrder.order[idx]? = some source := by
    have hfocus_eq :=
      OrderSequenceStructure.generatedTrace_get_focus_eq_order_get?
        (structureOf sequence) candidates
        (profileActiveTallyOf voters ballots) ⟨idx, hidx⟩
    simpa [trace] using hfocus_eq.symm.trans hfocus
  have hloss_get : losses[idx]? = some source := by
    simpa [losses, horder_eq sequence hmem hfeasible] using hfocus_order
  have hidx_losses : idx < losses.length := by
    rw [List.getElem?_eq_some_iff] at hloss_get
    rcases hloss_get with ⟨hidx_losses, _⟩
    exact hidx_losses
  have hget : losses[idx] = source := by
    simpa [List.getElem?_eq_getElem hidx_losses] using hloss_get
  have hlosses_nodup : losses.Nodup := by
    simpa [losses] using
      (Finset.nodup_toList
        (predictLossesCandidates voters ballots candidates budget
          firstChoiceThreshold))
  have hidxOf : losses.idxOf source = idx := by
    simpa [hget] using hlosses_nodup.idxOf_getElem idx hidx_losses
  have hbefore :
      ((rcvGeneratedTraceOfStructure (structureOf sequence)
        candidates (profileActiveTallyOf voters ballots)).steps.get
        ⟨idx, hidx⟩).beforeActive =
          candidates \ (losses.take idx).toFinset := by
    have hbefore' :=
      OrderSequenceStructure.generatedTrace_get_beforeActive_eq_sdiff_take_toFinset
        (structureOf sequence) candidates
        (profileActiveTallyOf voters ballots) ⟨idx, hidx⟩
    simpa [trace, losses, horder_eq sequence hmem hfeasible] using hbefore'
  rw [hbefore]
  simp [predictLossesProfileTransferValue, losses, hidxOf]

/--
Closed Definition 5.1/Proposition 5.3 core: if an action never increases active
votes before exit, then it cannot benefit the candidate.
-/
theorem proposition5_3_individual_no_benefit_of_no_active_vote_increase
    {Round Score : Type*} [Preorder Score]
    {before after : Round → Score} {beforeExit : Round → Prop}
    (hnoIncrease : ∀ round, beforeExit round → after round ≤ before round) :
    ¬ benefitsViaAction before after beforeExit := by
  rintro ⟨round, hbeforeExit, hstrict⟩
  exact not_lt_of_ge (hnoIncrease round hbeforeExit) hstrict

/--
Closed Proposition 5.3 active-support bridge: if each strategic ballot edit
preserves the prefix through `candidate`, then while `candidate` remains active
the edit cannot increase the number of voters whose first active candidate is
`candidate`.
-/
theorem proposition5_3_individual_no_benefit_of_prefix_preservation
    {Voter Candidate Round : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {before after : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate} {candidate : Candidate}
    {beforeExit : Round → Prop}
    (hcandidate : ∀ round, beforeExit round → candidate ∈ active round)
    (hpreserve : ∀ voter ∈ voters,
      Ballot.PreservesPrefixThrough candidate (before voter) (after voter)) :
    ¬ benefitsViaAction
      (fun round => (Ballot.activeSupport voters before (active round) candidate).card)
      (fun round => (Ballot.activeSupport voters after (active round) candidate).card)
      beforeExit := by
  apply proposition5_3_individual_no_benefit_of_no_active_vote_increase
  intro round hbeforeExit
  exact Ballot.activeSupport_card_le_of_preservesPrefixThrough
    (hcandidate round hbeforeExit) hpreserve

/--
Closed Proposition 5.3 active-gate bridge: if, before a candidate exits, every
edited ballot preserves its prefix through some candidate that is still active,
then the edit cannot increase the candidate's first-active support count.
-/
theorem proposition5_3_individual_no_benefit_of_active_gate_preservation
    {Voter Candidate Round : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {before after : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate} {candidate : Candidate}
    {beforeExit : Round → Prop}
    (hgate : ∀ round, beforeExit round → ∀ voter ∈ voters,
      ∃ gate, gate ∈ active round ∧
        Ballot.PreservesPrefixThrough gate (before voter) (after voter)) :
    ¬ benefitsViaAction
      (fun round => (Ballot.activeSupport voters before (active round) candidate).card)
      (fun round => (Ballot.activeSupport voters after (active round) candidate).card)
      beforeExit := by
  apply proposition5_3_individual_no_benefit_of_no_active_vote_increase
  intro round hbeforeExit
  have hcard_eq :
      (Ballot.activeSupport voters after (active round) candidate).card =
        (Ballot.activeSupport voters before (active round) candidate).card := by
    apply Ballot.activeSupport_card_eq_of_forall_nextActive_eq
    intro voter hvoter
    exact (Ballot.nextActive_eq_of_exists_preservesPrefixThrough_active
      (hgate round hbeforeExit voter hvoter)).symm
  exact le_of_eq hcard_eq

/--
The first-exiting coalition-member model supplies the active-gate preservation
premise used by the closed Proposition 5.3 coalition bridge.
-/
theorem active_gate_preservation_of_first_exiting_coalition_member
    {Voter Candidate Round : Type*}
    {voters : Finset Voter} {coalition : Finset Candidate}
    {before after : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate} {beforeExit : Candidate → Round → Prop}
    {candidate : Candidate}
    (hfirst : firstExitingCoalitionMember coalition active beforeExit candidate)
    (hpreserve : coalitionPrefixPreservation voters coalition before after) :
    ∀ round, beforeExit candidate round → ∀ voter ∈ voters,
      ∃ gate, gate ∈ active round ∧
        Ballot.PreservesPrefixThrough gate (before voter) (after voter) := by
  intro round hbeforeExit
  exact Ballot.forall_exists_active_preservesPrefixThrough_of_subset
    (hfirst.2 round hbeforeExit) hpreserve

/--
Closed Proposition 5.3 coalition core: if at least one coalition member does
not benefit, then not all coalition members benefit.
-/
theorem proposition5_3_coalition_not_all_benefit_of_exists_nonbenefiting
    {Candidate : Type*} {coalition : Finset Candidate}
    {benefits : Candidate → Prop}
    (hnonbenefit : ∃ candidate,
      candidate ∈ coalition ∧ ¬ benefits candidate) :
    ¬ coalitionAllBenefit coalition benefits := by
  rintro hall
  rcases hnonbenefit with ⟨candidate, hmember, hnot⟩
  exact hnot (hall candidate hmember)

/--
Closed Proposition 5.3 coalition bridge: if a coalition member has
prefix-preserving strategic ballot edits, that member cannot benefit, so the
coalition cannot have every member benefit.
-/
theorem proposition5_3_coalition_not_all_benefit_of_member_active_gate_preservation
    {Voter Candidate Round : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {coalition : Finset Candidate}
    {before after : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate} {beforeExit : Candidate → Round → Prop}
    {candidate : Candidate}
    (hmember : candidate ∈ coalition)
    (hgate : ∀ round, beforeExit candidate round → ∀ voter ∈ voters,
      ∃ gate, gate ∈ active round ∧
        Ballot.PreservesPrefixThrough gate (before voter) (after voter)) :
    ¬ coalitionAllBenefit coalition
      (fun candidate =>
        benefitsViaAction
          (fun round => (Ballot.activeSupport voters before (active round) candidate).card)
          (fun round => (Ballot.activeSupport voters after (active round) candidate).card)
          (beforeExit candidate)) := by
  apply proposition5_3_coalition_not_all_benefit_of_exists_nonbenefiting
  exact ⟨candidate, hmember,
    proposition5_3_individual_no_benefit_of_active_gate_preservation hgate⟩

/--
Closed Proposition 5.3 first-exiting-member bridge: if coalition edits preserve
prefixes through coalition members and a first-exiting member is identified,
then not every coalition member can benefit.
-/
theorem proposition5_3_coalition_not_all_benefit_of_first_exiting_member
    {Voter Candidate Round : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {coalition : Finset Candidate}
    {before after : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate} {beforeExit : Candidate → Round → Prop}
    {candidate : Candidate}
    (hfirst : firstExitingCoalitionMember coalition active beforeExit candidate)
    (hpreserve : coalitionPrefixPreservation voters coalition before after) :
    ¬ coalitionAllBenefit coalition
      (fun candidate =>
        benefitsViaAction
          (fun round => (Ballot.activeSupport voters before (active round) candidate).card)
          (fun round => (Ballot.activeSupport voters after (active round) candidate).card)
          (beforeExit candidate)) := by
  exact proposition5_3_coalition_not_all_benefit_of_member_active_gate_preservation
    hfirst.1
    (active_gate_preservation_of_first_exiting_coalition_member
      hfirst hpreserve)

/--
Closed Proposition 5.3 finite-exit constructor: a nonempty coalition has a
first-exiting member whenever the source dynamics provide finite exit ranks and
all later-exiting coalition members remain active before an earlier member
exits.
-/
theorem proposition5_3_coalition_not_all_benefit_of_exitRank
    {Voter Candidate Round : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {coalition : Finset Candidate}
    {before after : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate} {beforeExit : Candidate → Round → Prop}
    (hcoalition : coalition.Nonempty)
    (exitRank : Candidate → ℕ)
    (hactive_before_exitRank :
      ∀ {candidate other round}, candidate ∈ coalition → other ∈ coalition →
        exitRank candidate ≤ exitRank other →
        beforeExit candidate round → other ∈ active round)
    (hpreserve : coalitionPrefixPreservation voters coalition before after) :
    ¬ coalitionAllBenefit coalition
      (fun candidate =>
        benefitsViaAction
          (fun round => (Ballot.activeSupport voters before (active round) candidate).card)
          (fun round => (Ballot.activeSupport voters after (active round) candidate).card)
          (beforeExit candidate)) := by
  rcases exists_firstExitingCoalitionMember_of_exitRank
      (coalition := coalition) (active := active)
      (beforeExit := beforeExit) hcoalition exitRank
      hactive_before_exitRank with
    ⟨candidate, hfirst⟩
  exact proposition5_3_coalition_not_all_benefit_of_first_exiting_member
    (voters := voters)
    (before := before)
    (after := after)
    (active := active)
    (beforeExit := beforeExit)
    hfirst hpreserve

/--
Closed Proposition 5.3 round-rank constructor: if the source dynamics provide
exit ranks, round ranks, and the standard active-until-exit-rank invariant,
then not every coalition member can benefit.
-/
theorem proposition5_3_coalition_not_all_benefit_of_roundRank
    {Voter Candidate Round : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {coalition : Finset Candidate}
    {before after : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate} {beforeExit : Candidate → Round → Prop}
    (hcoalition : coalition.Nonempty)
    (exitRank : Candidate → ℕ) (roundRank : Round → ℕ)
    (hbeforeExit_lt :
      ∀ {candidate round}, candidate ∈ coalition →
        beforeExit candidate round → roundRank round < exitRank candidate)
    (hactive_until : ActiveUntilExitRank active roundRank exitRank)
    (hpreserve : coalitionPrefixPreservation voters coalition before after) :
    ¬ coalitionAllBenefit coalition
      (fun candidate =>
        benefitsViaAction
          (fun round => (Ballot.activeSupport voters before (active round) candidate).card)
          (fun round => (Ballot.activeSupport voters after (active round) candidate).card)
          (beforeExit candidate)) := by
  exact proposition5_3_coalition_not_all_benefit_of_exitRank
    hcoalition exitRank
    (active_before_exitRank_of_roundRank exitRank roundRank
      hbeforeExit_lt hactive_until)
    hpreserve

/--
Proposition 5.3 individual route with the source "before exit" convention
spelled as active membership in the current round.
-/
theorem proposition5_3_individual_no_benefit_while_active
    {Voter Candidate Round : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {before after : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate} {candidate : Candidate}
    (hpreserve : ∀ voter ∈ voters,
      Ballot.PreservesPrefixThrough candidate (before voter) (after voter)) :
    ¬ benefitsViaAction
      (fun round => (Ballot.activeSupport voters before (active round) candidate).card)
      (fun round => (Ballot.activeSupport voters after (active round) candidate).card)
      (fun round => candidate ∈ active round) := by
  exact proposition5_3_individual_no_benefit_of_prefix_preservation
    (fun _ hactive => hactive) hpreserve

/--
Proposition 5.3 coalition route with the source "before exit" convention
spelled as active membership in the current round.
-/
theorem proposition5_3_coalition_not_all_benefit_of_roundRank_while_active
    {Voter Candidate Round : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {coalition : Finset Candidate}
    {before after : Voter → RCVBallot Candidate}
    {active : Round → Finset Candidate}
    (hcoalition : coalition.Nonempty)
    (exitRank : Candidate → ℕ) (roundRank : Round → ℕ)
    (hactive_rank_lt :
      ∀ {candidate round}, candidate ∈ coalition →
        candidate ∈ active round → roundRank round < exitRank candidate)
    (hactive_until : ActiveUntilExitRank active roundRank exitRank)
    (hpreserve : coalitionPrefixPreservation voters coalition before after) :
    ¬ coalitionAllBenefit coalition
      (fun candidate =>
        benefitsViaAction
          (fun round => (Ballot.activeSupport voters before (active round) candidate).card)
          (fun round => (Ballot.activeSupport voters after (active round) candidate).card)
          (fun round => candidate ∈ active round)) := by
  exact proposition5_3_coalition_not_all_benefit_of_roundRank
    hcoalition exitRank roundRank
    (by
      intro candidate round hcandidate hactive
      exact hactive_rank_lt hcandidate hactive)
    hactive_until hpreserve

/--
Proposition 5.3 trace-backed coalition route. Concrete STV replay facts,
focused-candidate removals, initial coalition activity, and "not focused before
exit" facts construct the active-until-exit invariant used by the
first-exiting-member argument.
-/
theorem proposition5_3_coalition_not_all_benefit_of_trace_while_active
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {coalition : Finset Candidate}
    {before after : Voter → RCVBallot Candidate}
    {trace : STVTrace Candidate}
    {startActive terminalActive : Finset Candidate}
    (hcoalition : coalition.Nonempty)
    (exitRank : Candidate → ℕ)
    (hactive_rank_lt :
      ∀ {candidate : Candidate} {round : Fin trace.steps.length},
        candidate ∈ coalition →
          candidate ∈ (trace.steps.get round).beforeActive →
            round.1 < exitRank candidate)
    (hreplay : trace.replaysFrom startActive terminalActive)
    (hremove : ∀ step, step ∈ trace.steps → step.removesFocusedCandidate)
    (hstart : coalition ⊆ startActive)
    (hnot_focus_before_exit :
      ∀ {candidate : Candidate}, candidate ∈ coalition →
        ∀ i : Fin trace.steps.length, i.1 < exitRank candidate →
          ∀ step, step ∈ trace.steps.take i.1 →
            step.focus ≠ some candidate)
    (hpreserve : coalitionPrefixPreservation voters coalition before after) :
    ¬ coalitionAllBenefit coalition
      (fun candidate =>
        benefitsViaAction
          (fun round : Fin trace.steps.length =>
            (Ballot.activeSupport voters before
              (trace.steps.get round).beforeActive candidate).card)
          (fun round : Fin trace.steps.length =>
            (Ballot.activeSupport voters after
              (trace.steps.get round).beforeActive candidate).card)
          (fun round : Fin trace.steps.length =>
            candidate ∈ (trace.steps.get round).beforeActive)) := by
  have hactive_until :
      ActiveUntilExitRankOn coalition
        (fun round : Fin trace.steps.length =>
          (trace.steps.get round).beforeActive)
        (fun round : Fin trace.steps.length => round.1)
        exitRank := by
    exact
      STVTrace.activeUntilExitRankOn_beforeActive_of_replaysFrom_not_focused_before
        (trace := trace) (startActive := startActive)
        (terminalActive := terminalActive) (tracked := coalition)
        (exitRank := exitRank) hreplay hremove hstart
        hnot_focus_before_exit
  rcases exists_firstExitingCoalitionMember_of_exitRank
      (coalition := coalition)
      (active := fun round : Fin trace.steps.length =>
        (trace.steps.get round).beforeActive)
      (beforeExit := fun candidate round =>
        candidate ∈ (trace.steps.get round).beforeActive)
      hcoalition exitRank
      (by
        intro candidate other round hcandidate hother hrank hactive
        exact
          ActiveUntilExitRankOn.active_of_rank_lt_of_le
            (tracked := coalition)
            (active := fun round : Fin trace.steps.length =>
              (trace.steps.get round).beforeActive)
            (roundRank := fun round : Fin trace.steps.length => round.1)
            (exitRank := exitRank) hactive_until hother
            (hactive_rank_lt hcandidate hactive) hrank) with
    ⟨candidate, hfirst⟩
  exact
    proposition5_3_coalition_not_all_benefit_of_first_exiting_member
      (voters := voters) (before := before) (after := after)
      hfirst hpreserve

/--
Theorem 5.4 source-facing certificate projection: an optimal-strategy shape
characterization gives the paper's allowed strategy forms.
-/
theorem theorem5_4_strategy_characterization_of_certificate {Strategy : Type*}
    {caseA : Prop} {shape : Strategy → AdditionStrategyShape}
    {optimal : Strategy → Prop}
    (cert : theorem5_4_strategyCharacterization caseA shape optimal) :
    theorem5_4_strategyCharacterization caseA shape optimal :=
  cert

/--
Theorem 5.4 source-facing bridge: optimal strategies have the allowed shapes
once non-altruistic-to-winner strategies are shown to be losing-prefix or
losing-only, and altruistic-to-winner optimality is shown to imply Case (A).
-/
theorem theorem5_4_strategy_characterization_of_shape_bridges {Strategy : Type*}
    {caseA : Prop} {shape : Strategy → AdditionStrategyShape}
    {optimal : Strategy → Prop}
    (hnonWinner : ∀ strategy, optimal strategy →
      shape strategy ≠ AdditionStrategyShape.altruisticToWinners →
      losingPrefixOrLosingOnlyShape (shape strategy))
    (hwinnerCase : ∀ strategy, optimal strategy →
      shape strategy = AdditionStrategyShape.altruisticToWinners → caseA) :
    theorem5_4_strategyCharacterization caseA shape optimal := by
  intro strategy hoptimal
  by_cases hwinner : shape strategy = AdditionStrategyShape.altruisticToWinners
  · exact Or.inr ⟨hwinnerCase strategy hoptimal hwinner, hwinner⟩
  · exact Or.inl (hnonWinner strategy hoptimal hwinner)

/--
Theorem 5.4 Appendix E dominance bridge: once Appendix E rules out the
catch-all `other` shape for optimal strategies, the finite shape vocabulary
reduces the non-altruistic-to-winners case to the two losing-shape forms.
-/
theorem theorem5_4_strategy_characterization_of_no_other_shape
    {Strategy : Type*}
    {caseA : Prop} {shape : Strategy → AdditionStrategyShape}
    {optimal : Strategy → Prop}
    (hnoOther : ∀ strategy, optimal strategy →
      shape strategy ≠ AdditionStrategyShape.other)
    (hwinnerCase : ∀ strategy, optimal strategy →
      shape strategy = AdditionStrategyShape.altruisticToWinners → caseA) :
    theorem5_4_strategyCharacterization caseA shape optimal := by
  apply theorem5_4_strategy_characterization_of_shape_bridges
  · intro strategy hoptimal hnotWinner
    exact losingPrefixOrLosingOnlyShape_of_not_altruisticToWinners_not_other
      hnotWinner (hnoOther strategy hoptimal)
  · exact hwinnerCase

/--
Appendix E dominance bridge: if optimal strategies minimize a cost objective
and every feasible `other` strategy has a feasible lower-cost replacement, then
no optimal strategy has the catch-all `other` shape.
-/
theorem theorem5_4_no_other_shape_of_strict_cost_dominance
    {Strategy : Type*}
    {feasible : Strategy → Prop} {cost : Strategy → ℝ}
    {shape : Strategy → AdditionStrategyShape}
    {optimal : Strategy → Prop}
    (hoptimal : ∀ strategy, optimal strategy →
      EconCSLib.Optimization.IsMinimizerOn feasible cost strategy)
    (hdominance : otherShapeStrictCostDominance feasible cost shape) :
    ∀ strategy, optimal strategy →
      shape strategy ≠ AdditionStrategyShape.other := by
  intro strategy hstrategy hshape
  have hmin := hoptimal strategy hstrategy
  exact EconCSLib.Optimization.IsMinimizerOn.not_of_exists_objective_lt
    (hdominance strategy hmin.isFeasible hshape) hmin

/--
Theorem 5.4 Appendix E dominance form: strict lower-cost replacements rule out
the `other` shape for optimal strategies; altruistic-to-winner optimality still
enters exactly through the Case (A) bridge.
-/
theorem theorem5_4_strategy_characterization_of_cost_dominance
    {Strategy : Type*}
    {caseA : Prop} {shape : Strategy → AdditionStrategyShape}
    {optimal feasible : Strategy → Prop} {cost : Strategy → ℝ}
    (hoptimal : ∀ strategy, optimal strategy →
      EconCSLib.Optimization.IsMinimizerOn feasible cost strategy)
    (hdominance : otherShapeStrictCostDominance feasible cost shape)
    (hwinnerCase : ∀ strategy, optimal strategy →
      shape strategy = AdditionStrategyShape.altruisticToWinners → caseA) :
    theorem5_4_strategyCharacterization caseA shape optimal := by
  exact theorem5_4_strategy_characterization_of_no_other_shape
    (theorem5_4_no_other_shape_of_strict_cost_dominance
      hoptimal hdominance)
    hwinnerCase

/--
Theorem 5.4 concrete Appendix E split-ballot form: for finite ballot-count
addition strategies, the strict-cost part of Appendix E follows from the
explicit split relation and its proved ballot-count inequality. The remaining
inputs are exactly the source-model obligations that the split replacement is
feasible and that altruistic-to-winners optimality implies Case (A).
-/
theorem theorem5_4_strategy_characterization_of_appendixE_split_ballot_replacement
    {Candidate : Type*} [DecidableEq Candidate]
    {winners : Finset Candidate} {caseA : Prop}
    {shape : FiniteAdditionStrategy Candidate → AdditionStrategyShape}
    {optimal feasible : FiniteAdditionStrategy Candidate → Prop}
    (hoptimal : ∀ strategy, optimal strategy →
      EconCSLib.Optimization.IsMinimizerOn feasible
        FiniteAdditionStrategy.cost strategy)
    (hsplit :
      ∀ strategy, feasible strategy →
        shape strategy = AdditionStrategyShape.other →
          ∃ alternative,
            AppendixESplitBallotReplacement winners strategy alternative ∧
              feasible alternative)
    (hwinnerCase : ∀ strategy, optimal strategy →
      shape strategy = AdditionStrategyShape.altruisticToWinners → caseA) :
    theorem5_4_strategyCharacterization caseA shape optimal := by
  exact theorem5_4_strategy_characterization_of_cost_dominance
    hoptimal
    (otherShapeStrictCostDominance_of_appendixESplitBallotReplacement
      (winners := winners) hsplit)
    hwinnerCase

/--
Theorem 5.4 contextual Appendix E split-ballot form: the bad ballot block may
occur anywhere inside the finite added-ballot list.  The strict-cost part still
follows from concrete ballot-count arithmetic; the source-model work is exactly
feasibility preservation of the contextual split and the Case-(A) bridge.
-/
theorem theorem5_4_strategy_characterization_of_contextual_appendixE_split_ballot_replacement
    {Candidate : Type*} [DecidableEq Candidate]
    {winners : Finset Candidate} {caseA : Prop}
    {shape : FiniteAdditionStrategy Candidate → AdditionStrategyShape}
    {optimal feasible : FiniteAdditionStrategy Candidate → Prop}
    (hoptimal : ∀ strategy, optimal strategy →
      EconCSLib.Optimization.IsMinimizerOn feasible
        FiniteAdditionStrategy.cost strategy)
    (hsplit :
      ∀ strategy, feasible strategy →
        shape strategy = AdditionStrategyShape.other →
          ∃ alternative,
            AppendixEContextualSplitBallotReplacement winners strategy
                alternative ∧
              feasible alternative)
    (hwinnerCase : ∀ strategy, optimal strategy →
      shape strategy = AdditionStrategyShape.altruisticToWinners → caseA) :
    theorem5_4_strategyCharacterization caseA shape optimal := by
  exact theorem5_4_strategy_characterization_of_cost_dominance
    hoptimal
    (otherShapeStrictCostDominance_of_contextualAppendixESplitBallotReplacement
      (winners := winners) hsplit)
    hwinnerCase

/--
Theorem 5.4 Appendix E replacement form: the paper's split-replacement
argument for catch-all `other` strategies supplies the strict-cost dominance
premise used by the shape characterization.
-/
theorem theorem5_4_strategy_characterization_of_replacement_certificate
    {Strategy : Type*}
    {caseA : Prop} {shape : Strategy → AdditionStrategyShape}
    {optimal feasible : Strategy → Prop} {cost : Strategy → ℝ}
    (hoptimal : ∀ strategy, optimal strategy →
      EconCSLib.Optimization.IsMinimizerOn feasible cost strategy)
    (cert : OtherShapeReplacementCertificate feasible cost shape)
    (hwinnerCase : ∀ strategy, optimal strategy →
      shape strategy = AdditionStrategyShape.altruisticToWinners → caseA) :
    theorem5_4_strategyCharacterization caseA shape optimal := by
  exact theorem5_4_strategy_characterization_of_cost_dominance
    hoptimal
    (otherShapeStrictCostDominance_of_replacementCertificate cert)
    hwinnerCase

/--
Theorem 5.4 replacement-and-Case-(A) certificate form: the paper's Appendix E
split-replacement argument rules out catch-all `other` strategies, while the
post-win-surplus certificate supplies the Case-(A) bridge for
altruistic-to-winners strategies.
-/
theorem theorem5_4_strategy_characterization_of_replacement_and_caseA_certificate
    {Strategy : Type*}
    {caseA : Prop} {shape : Strategy → AdditionStrategyShape}
    {optimal feasible : Strategy → Prop} {cost : Strategy → ℝ}
    (hoptimal : ∀ strategy, optimal strategy →
      EconCSLib.Optimization.IsMinimizerOn feasible cost strategy)
    (replacementCert : OtherShapeReplacementCertificate feasible cost shape)
    (caseCert : AltruisticWinnerCaseACertificate caseA shape optimal) :
    theorem5_4_strategyCharacterization caseA shape optimal := by
  exact theorem5_4_strategy_characterization_of_replacement_certificate
    hoptimal replacementCert (altruisticWinner_caseA_of_certificate caseCert)

/--
Theorem 5.4 split-replacement-and-Case-(A) certificate form: the paper's
Appendix E branch split rules out catch-all `other` strategies, while the
post-win-surplus certificate supplies the Case-(A) bridge for
altruistic-to-winners strategies.
-/
theorem theorem5_4_strategy_characterization_of_split_replacement_and_caseA_certificate
    {Strategy : Type*}
    {caseA : Prop} {shape : Strategy → AdditionStrategyShape}
    {optimal feasible : Strategy → Prop} {cost : Strategy → ℝ}
    (hoptimal : ∀ strategy, optimal strategy →
      EconCSLib.Optimization.IsMinimizerOn feasible cost strategy)
    (replacementCert :
      OtherShapeSplitReplacementCertificate feasible cost shape)
    (caseCert : AltruisticWinnerCaseACertificate caseA shape optimal) :
    theorem5_4_strategyCharacterization caseA shape optimal := by
  exact theorem5_4_strategy_characterization_of_cost_dominance
    hoptimal
    (otherShapeStrictCostDominance_of_splitReplacementCertificate
      replacementCert)
    (altruisticWinner_caseA_of_certificate caseCert)

/--
Theorem 5.4 Appendix-E-shaped certificate form: the two branch replacements
from the appendix rule out catch-all `other` strategies, while the
post-win-surplus certificate supplies the Case-(A) bridge.
-/
theorem theorem5_4_strategy_characterization_of_appendixE_and_caseA_certificate
    {Strategy : Type*}
    {caseA : Prop} {shape : Strategy → AdditionStrategyShape}
    {optimal feasible : Strategy → Prop} {cost : Strategy → ℝ}
    (hoptimal : ∀ strategy, optimal strategy →
      EconCSLib.Optimization.IsMinimizerOn feasible cost strategy)
    (replacementCert :
      AppendixESplitReplacementCertificate feasible cost shape)
    (caseCert : AltruisticWinnerCaseACertificate caseA shape optimal) :
    theorem5_4_strategyCharacterization caseA shape optimal := by
  exact theorem5_4_strategy_characterization_of_cost_dominance
    hoptimal
    (otherShapeStrictCostDominance_of_appendixESplitReplacementCertificate
      replacementCert)
    (altruisticWinner_caseA_of_certificate caseCert)

/--
Theorem 5.4 source-instantiated Case-(A) form: the Appendix E branch
replacements rule out catch-all `other` strategies, and optimal
altruistic-to-winners strategies themselves witness the source Case (A)
occurrence through post-win surplus transfers.
-/
theorem theorem5_4_strategy_characterization_of_appendixE_and_caseA_occurs
    {Strategy : Type*}
    {shape : Strategy → AdditionStrategyShape}
    {optimal feasible : Strategy → Prop} {cost : Strategy → ℝ}
    {usesPostWinSurplus : Strategy → Prop}
    (hoptimal : ∀ strategy, optimal strategy →
      EconCSLib.Optimization.IsMinimizerOn feasible cost strategy)
    (replacementCert :
      AppendixESplitReplacementCertificate feasible cost shape)
    (huses : ∀ strategy, optimal strategy →
      shape strategy = AdditionStrategyShape.altruisticToWinners →
        usesPostWinSurplus strategy) :
    theorem5_4_strategyCharacterization
      (theorem5_4_caseA_occurs usesPostWinSurplus) shape optimal := by
  exact theorem5_4_strategy_characterization_of_cost_dominance
    hoptimal
    (otherShapeStrictCostDominance_of_appendixESplitReplacementCertificate
      replacementCert)
    (altruisticWinner_caseA_occurs_of_usesPostWinSurplus huses)

/--
Proposition 5.5 source-facing uncertainty interface: under uncertainty,
coalitions can be ex-post unable to benefit all members while still having an
ex-ante all-member-benefit witness.
-/
theorem proposition5_5_uncertainty_coalition_benefit
    {State Candidate : Type*} {coalition : Finset Candidate}
    {exPostBenefits : State → Candidate → Prop}
    {exAnteBenefits : Candidate → Prop}
    (hexpost : exPostCoalitionAllBenefitImpossible coalition exPostBenefits)
    (hexante : exAnteCoalitionAllBenefitPossible coalition exAnteBenefits) :
    exPostCoalitionAllBenefitImpossible coalition exPostBenefits ∧
      exAnteCoalitionAllBenefitPossible coalition exAnteBenefits :=
  ⟨hexpost, hexante⟩

/--
Proposition 5.5 existential ex-ante form: once the ex-post no-all-benefit
statement is proved, the abstract ex-ante side can be supplied by an
existential benefit predicate.  This captures the source's existence claim
without requiring a fixed ex-ante predicate as input.
-/
theorem proposition5_5_uncertainty_coalition_benefit_exists_exAnte
    {State Candidate : Type*} {coalition : Finset Candidate}
    {exPostBenefits : State → Candidate → Prop}
    (hexpost : exPostCoalitionAllBenefitImpossible coalition exPostBenefits) :
    exPostCoalitionAllBenefitImpossible coalition exPostBenefits ∧
      ∃ exAnteBenefits : Candidate → Prop,
        exAnteCoalitionAllBenefitPossible coalition exAnteBenefits :=
  ⟨hexpost, exists_exAnteCoalitionAllBenefitPossible coalition⟩

/--
Proposition 5.5 ex-post bridge: if every realized state has a coalition member
whose before-exit rounds have active gate candidates protecting edited ballot
prefixes, then no realized state can benefit every coalition member.
-/
theorem proposition5_5_exPostCoalitionAllBenefitImpossible_of_statewise_active_gate
    {State Voter Candidate Round : Type*} [DecidableEq Candidate]
    {coalition : Finset Candidate}
    {voters : State → Finset Voter}
    {before after : State → Voter → RCVBallot Candidate}
    {active : State → Round → Finset Candidate}
    {beforeExit : State → Candidate → Round → Prop}
    (hstatewise : ∀ state, ∃ candidate,
      candidate ∈ coalition ∧
        ∀ round, beforeExit state candidate round → ∀ voter ∈ voters state,
          ∃ gate, gate ∈ active state round ∧
            Ballot.PreservesPrefixThrough gate
              (before state voter) (after state voter)) :
    exPostCoalitionAllBenefitImpossible coalition
      (fun state candidate =>
        benefitsViaAction
          (fun round =>
            (Ballot.activeSupport
              (voters state) (before state) (active state round) candidate).card)
          (fun round =>
            (Ballot.activeSupport
              (voters state) (after state) (active state round) candidate).card)
          (beforeExit state candidate)) := by
  intro state
  rcases hstatewise state with ⟨candidate, hmember, hgate⟩
  exact proposition5_3_coalition_not_all_benefit_of_member_active_gate_preservation
    (voters := voters state)
    (before := before state)
    (after := after state)
    (active := active state)
    (beforeExit := beforeExit state)
    hmember hgate

/--
Proposition 5.5 ex-post bridge from the source-shaped first-exiting-member
model in each realized state.
-/
theorem proposition5_5_exPostCoalitionAllBenefitImpossible_of_statewise_first_exiting_member
    {State Voter Candidate Round : Type*} [DecidableEq Candidate]
    {coalition : Finset Candidate}
    {voters : State → Finset Voter}
    {before after : State → Voter → RCVBallot Candidate}
    {active : State → Round → Finset Candidate}
    {beforeExit : State → Candidate → Round → Prop}
    (hstatewise : ∀ state, ∃ candidate,
      firstExitingCoalitionMember coalition (active state)
        (beforeExit state) candidate ∧
      coalitionPrefixPreservation (voters state) coalition
        (before state) (after state)) :
    exPostCoalitionAllBenefitImpossible coalition
      (fun state candidate =>
        benefitsViaAction
          (fun round =>
            (Ballot.activeSupport
              (voters state) (before state) (active state round) candidate).card)
          (fun round =>
            (Ballot.activeSupport
              (voters state) (after state) (active state round) candidate).card)
          (beforeExit state candidate)) := by
  intro state
  rcases hstatewise state with ⟨candidate, hfirst, hpreserve⟩
  exact proposition5_3_coalition_not_all_benefit_of_first_exiting_member
    (voters := voters state)
    (before := before state)
    (after := after state)
    (active := active state)
    (beforeExit := beforeExit state)
    hfirst hpreserve

/--
Proposition 5.5 ex-post bridge from statewise finite exit-rank data.  This is
the source-proof form: in each realized state, choose a coalition member whose
exit rank is minimum and apply the Proposition 5.3 prefix-preservation
argument to that first-exiting member.
-/
theorem proposition5_5_exPostCoalitionAllBenefitImpossible_of_statewise_exitRank
    {State Voter Candidate Round : Type*} [DecidableEq Candidate]
    {coalition : Finset Candidate}
    {voters : State → Finset Voter}
    {before after : State → Voter → RCVBallot Candidate}
    {active : State → Round → Finset Candidate}
    {beforeExit : State → Candidate → Round → Prop}
    (hcoalition : coalition.Nonempty)
    (exitRank : State → Candidate → ℕ)
    (hactive_before_exitRank :
      ∀ state {candidate other round},
        candidate ∈ coalition → other ∈ coalition →
        exitRank state candidate ≤ exitRank state other →
        beforeExit state candidate round → other ∈ active state round)
    (hpreserve : ∀ state,
      coalitionPrefixPreservation (voters state) coalition
        (before state) (after state)) :
    exPostCoalitionAllBenefitImpossible coalition
      (fun state candidate =>
        benefitsViaAction
          (fun round =>
            (Ballot.activeSupport
              (voters state) (before state) (active state round) candidate).card)
          (fun round =>
            (Ballot.activeSupport
              (voters state) (after state) (active state round) candidate).card)
          (beforeExit state candidate)) := by
  intro state
  rcases exists_firstExitingCoalitionMember_of_exitRank
      (coalition := coalition) (active := active state)
      (beforeExit := beforeExit state) hcoalition (exitRank state)
      (by
        intro candidate other round hcandidate hother hrank hbeforeExit
        exact hactive_before_exitRank state hcandidate hother hrank hbeforeExit) with
    ⟨candidate, hfirst⟩
  exact proposition5_3_coalition_not_all_benefit_of_first_exiting_member
    (voters := voters state)
    (before := before state)
    (after := after state)
    (active := active state)
    (beforeExit := beforeExit state)
    hfirst (hpreserve state)

/--
Proposition 5.5 ex-post bridge from statewise round-rank dynamics.  The source
dynamics only need to show that before-exit rounds occur before the candidate's
exit rank, and that the active set contains candidates whose exit rank is still
ahead of the current round rank.
-/
theorem proposition5_5_exPostCoalitionAllBenefitImpossible_of_statewise_roundRank
    {State Voter Candidate Round : Type*} [DecidableEq Candidate]
    {coalition : Finset Candidate}
    {voters : State → Finset Voter}
    {before after : State → Voter → RCVBallot Candidate}
    {active : State → Round → Finset Candidate}
    {beforeExit : State → Candidate → Round → Prop}
    (hcoalition : coalition.Nonempty)
    (exitRank : State → Candidate → ℕ)
    (roundRank : State → Round → ℕ)
    (hbeforeExit_lt :
      ∀ state {candidate round}, candidate ∈ coalition →
        beforeExit state candidate round →
          roundRank state round < exitRank state candidate)
    (hactive_until :
      ∀ state, ActiveUntilExitRank (active state) (roundRank state)
        (exitRank state))
    (hpreserve : ∀ state,
      coalitionPrefixPreservation (voters state) coalition
        (before state) (after state)) :
    exPostCoalitionAllBenefitImpossible coalition
      (fun state candidate =>
        benefitsViaAction
          (fun round =>
            (Ballot.activeSupport
              (voters state) (before state) (active state round) candidate).card)
          (fun round =>
            (Ballot.activeSupport
              (voters state) (after state) (active state round) candidate).card)
          (beforeExit state candidate)) := by
  exact proposition5_5_exPostCoalitionAllBenefitImpossible_of_statewise_exitRank
    hcoalition exitRank
    (by
      intro state candidate other round hcandidate _hother hrank hbeforeExit
      exact hactive_until state (candidate := other) (round := round)
        (lt_of_lt_of_le (hbeforeExit_lt state hcandidate hbeforeExit) hrank))
    hpreserve

/--
Proposition 5.5 source-facing uncertainty bridge: statewise active-gate
preservation gives the ex-post no-all-benefit conclusion; the ex-ante
all-benefit witness remains explicit.
-/
theorem proposition5_5_uncertainty_coalition_benefit_of_statewise_active_gate
    {State Voter Candidate Round : Type*} [DecidableEq Candidate]
    {coalition : Finset Candidate}
    {voters : State → Finset Voter}
    {before after : State → Voter → RCVBallot Candidate}
    {active : State → Round → Finset Candidate}
    {beforeExit : State → Candidate → Round → Prop}
    {exAnteBenefits : Candidate → Prop}
    (hstatewise : ∀ state, ∃ candidate,
      candidate ∈ coalition ∧
        ∀ round, beforeExit state candidate round → ∀ voter ∈ voters state,
          ∃ gate, gate ∈ active state round ∧
            Ballot.PreservesPrefixThrough gate
              (before state voter) (after state voter))
    (hexante : exAnteCoalitionAllBenefitPossible coalition exAnteBenefits) :
    exPostCoalitionAllBenefitImpossible coalition
        (fun state candidate =>
          benefitsViaAction
            (fun round =>
              (Ballot.activeSupport
                (voters state) (before state) (active state round) candidate).card)
            (fun round =>
              (Ballot.activeSupport
                (voters state) (after state) (active state round) candidate).card)
            (beforeExit state candidate)) ∧
      exAnteCoalitionAllBenefitPossible coalition exAnteBenefits := by
  exact ⟨
    proposition5_5_exPostCoalitionAllBenefitImpossible_of_statewise_active_gate
      hstatewise,
    hexante⟩

/--
Proposition 5.5 source-facing uncertainty bridge from statewise finite
exit-rank data.  The ex-post conclusion follows by choosing a minimum-rank
coalition member in each state; the ex-ante all-benefit witness remains
explicit.
-/
theorem proposition5_5_uncertainty_coalition_benefit_of_statewise_exitRank
    {State Voter Candidate Round : Type*} [DecidableEq Candidate]
    {coalition : Finset Candidate}
    {voters : State → Finset Voter}
    {before after : State → Voter → RCVBallot Candidate}
    {active : State → Round → Finset Candidate}
    {beforeExit : State → Candidate → Round → Prop}
    {exAnteBenefits : Candidate → Prop}
    (hcoalition : coalition.Nonempty)
    (exitRank : State → Candidate → ℕ)
    (hactive_before_exitRank :
      ∀ state {candidate other round},
        candidate ∈ coalition → other ∈ coalition →
        exitRank state candidate ≤ exitRank state other →
        beforeExit state candidate round → other ∈ active state round)
    (hpreserve : ∀ state,
      coalitionPrefixPreservation (voters state) coalition
        (before state) (after state))
    (hexante : exAnteCoalitionAllBenefitPossible coalition exAnteBenefits) :
    exPostCoalitionAllBenefitImpossible coalition
        (fun state candidate =>
          benefitsViaAction
            (fun round =>
              (Ballot.activeSupport
                (voters state) (before state) (active state round) candidate).card)
            (fun round =>
              (Ballot.activeSupport
                (voters state) (after state) (active state round) candidate).card)
            (beforeExit state candidate)) ∧
      exAnteCoalitionAllBenefitPossible coalition exAnteBenefits := by
  exact ⟨
    proposition5_5_exPostCoalitionAllBenefitImpossible_of_statewise_exitRank
      hcoalition exitRank hactive_before_exitRank hpreserve,
    hexante⟩

/--
Proposition 5.5 source-facing uncertainty bridge from statewise round-rank
dynamics.  This is the same finite-exit-rank conclusion with the
active-before-exit premise derived from the reusable active-until-exit-rank
invariant.
-/
theorem proposition5_5_uncertainty_coalition_benefit_of_statewise_roundRank
    {State Voter Candidate Round : Type*} [DecidableEq Candidate]
    {coalition : Finset Candidate}
    {voters : State → Finset Voter}
    {before after : State → Voter → RCVBallot Candidate}
    {active : State → Round → Finset Candidate}
    {beforeExit : State → Candidate → Round → Prop}
    {exAnteBenefits : Candidate → Prop}
    (hcoalition : coalition.Nonempty)
    (exitRank : State → Candidate → ℕ)
    (roundRank : State → Round → ℕ)
    (hbeforeExit_lt :
      ∀ state {candidate round}, candidate ∈ coalition →
        beforeExit state candidate round →
          roundRank state round < exitRank state candidate)
    (hactive_until :
      ∀ state, ActiveUntilExitRank (active state) (roundRank state)
        (exitRank state))
    (hpreserve : ∀ state,
      coalitionPrefixPreservation (voters state) coalition
        (before state) (after state))
    (hexante : exAnteCoalitionAllBenefitPossible coalition exAnteBenefits) :
    exPostCoalitionAllBenefitImpossible coalition
        (fun state candidate =>
          benefitsViaAction
            (fun round =>
              (Ballot.activeSupport
                (voters state) (before state) (active state round) candidate).card)
            (fun round =>
              (Ballot.activeSupport
                (voters state) (after state) (active state round) candidate).card)
            (beforeExit state candidate)) ∧
      exAnteCoalitionAllBenefitPossible coalition exAnteBenefits := by
  exact proposition5_5_uncertainty_coalition_benefit_of_statewise_exitRank
    hcoalition exitRank
    (by
      intro state candidate other round hcandidate _hother hrank hbeforeExit
      exact hactive_until state (candidate := other) (round := round)
        (lt_of_lt_of_le (hbeforeExit_lt state hcandidate hbeforeExit) hrank))
    hpreserve hexante

/--
Proposition 5.5 source-facing uncertainty bridge from statewise round-rank
dynamics, using only a coalition-scoped active-until-exit invariant.
-/
theorem proposition5_5_uncertainty_coalition_benefit_of_statewise_roundRankOn
    {State Voter Candidate Round : Type*} [DecidableEq Candidate]
    {coalition : Finset Candidate}
    {voters : State → Finset Voter}
    {before after : State → Voter → RCVBallot Candidate}
    {active : State → Round → Finset Candidate}
    {beforeExit : State → Candidate → Round → Prop}
    {exAnteBenefits : Candidate → Prop}
    (hcoalition : coalition.Nonempty)
    (exitRank : State → Candidate → ℕ)
    (roundRank : State → Round → ℕ)
    (hbeforeExit_lt :
      ∀ state {candidate round}, candidate ∈ coalition →
        beforeExit state candidate round →
          roundRank state round < exitRank state candidate)
    (hactive_until :
      ∀ state, ActiveUntilExitRankOn coalition (active state)
        (roundRank state) (exitRank state))
    (hpreserve : ∀ state,
      coalitionPrefixPreservation (voters state) coalition
        (before state) (after state))
    (hexante : exAnteCoalitionAllBenefitPossible coalition exAnteBenefits) :
    exPostCoalitionAllBenefitImpossible coalition
        (fun state candidate =>
          benefitsViaAction
            (fun round =>
              (Ballot.activeSupport
                (voters state) (before state) (active state round) candidate).card)
            (fun round =>
              (Ballot.activeSupport
                (voters state) (after state) (active state round) candidate).card)
            (beforeExit state candidate)) ∧
      exAnteCoalitionAllBenefitPossible coalition exAnteBenefits := by
  exact proposition5_5_uncertainty_coalition_benefit_of_statewise_exitRank
    hcoalition exitRank
    (by
      intro state candidate other round hcandidate hother hrank hbeforeExit
      exact active_before_exitRank_of_roundRankOn
        (coalition := coalition) (active := active state)
        (beforeExit := beforeExit state) (exitRank := exitRank state)
        (roundRank := roundRank state)
        (by
          intro candidate round hcandidate hbeforeExit
          exact hbeforeExit_lt state hcandidate hbeforeExit)
        (hactive_until state) hcandidate hother hrank hbeforeExit)
    hpreserve hexante

/--
Proposition 5.5 source-facing uncertainty bridge with the "before exit"
predicate instantiated as active membership in each realized state.
-/
theorem proposition5_5_uncertainty_coalition_benefit_of_statewise_roundRank_while_active
    {State Voter Candidate Round : Type*} [DecidableEq Candidate]
    {coalition : Finset Candidate}
    {voters : State → Finset Voter}
    {before after : State → Voter → RCVBallot Candidate}
    {active : State → Round → Finset Candidate}
    {exAnteBenefits : Candidate → Prop}
    (hcoalition : coalition.Nonempty)
    (exitRank : State → Candidate → ℕ)
    (roundRank : State → Round → ℕ)
    (hactive_rank_lt :
      ∀ state {candidate round}, candidate ∈ coalition →
        candidate ∈ active state round →
          roundRank state round < exitRank state candidate)
    (hactive_until :
      ∀ state, ActiveUntilExitRank (active state) (roundRank state)
        (exitRank state))
    (hpreserve : ∀ state,
      coalitionPrefixPreservation (voters state) coalition
        (before state) (after state))
    (hexante : exAnteCoalitionAllBenefitPossible coalition exAnteBenefits) :
    exPostCoalitionAllBenefitImpossible coalition
        (fun state candidate =>
          benefitsViaAction
            (fun round =>
              (Ballot.activeSupport
                (voters state) (before state) (active state round) candidate).card)
            (fun round =>
              (Ballot.activeSupport
                (voters state) (after state) (active state round) candidate).card)
            (fun round => candidate ∈ active state round)) ∧
      exAnteCoalitionAllBenefitPossible coalition exAnteBenefits := by
  exact proposition5_5_uncertainty_coalition_benefit_of_statewise_roundRank
    hcoalition exitRank roundRank
    (by
      intro state candidate round hcandidate hactive
      exact hactive_rank_lt state hcandidate hactive)
    hactive_until hpreserve hexante

/--
Proposition 5.5 source-facing uncertainty bridge with the "before exit"
predicate instantiated as active membership and with only a coalition-scoped
active-until-exit invariant.
-/
theorem proposition5_5_uncertainty_coalition_benefit_of_statewise_roundRankOn_while_active
    {State Voter Candidate Round : Type*} [DecidableEq Candidate]
    {coalition : Finset Candidate}
    {voters : State → Finset Voter}
    {before after : State → Voter → RCVBallot Candidate}
    {active : State → Round → Finset Candidate}
    {exAnteBenefits : Candidate → Prop}
    (hcoalition : coalition.Nonempty)
    (exitRank : State → Candidate → ℕ)
    (roundRank : State → Round → ℕ)
    (hactive_rank_lt :
      ∀ state {candidate round}, candidate ∈ coalition →
        candidate ∈ active state round →
          roundRank state round < exitRank state candidate)
    (hactive_until :
      ∀ state, ActiveUntilExitRankOn coalition (active state)
        (roundRank state) (exitRank state))
    (hpreserve : ∀ state,
      coalitionPrefixPreservation (voters state) coalition
        (before state) (after state))
    (hexante : exAnteCoalitionAllBenefitPossible coalition exAnteBenefits) :
    exPostCoalitionAllBenefitImpossible coalition
        (fun state candidate =>
          benefitsViaAction
            (fun round =>
              (Ballot.activeSupport
                (voters state) (before state) (active state round) candidate).card)
            (fun round =>
              (Ballot.activeSupport
                (voters state) (after state) (active state round) candidate).card)
            (fun round => candidate ∈ active state round)) ∧
      exAnteCoalitionAllBenefitPossible coalition exAnteBenefits := by
  exact proposition5_5_uncertainty_coalition_benefit_of_statewise_roundRankOn
    hcoalition exitRank roundRank
    (by
      intro state candidate round hcandidate hactive
      exact hactive_rank_lt state hcandidate hactive)
    hactive_until hpreserve hexante

/--
Proposition 5.5 trace-backed uncertainty bridge.  This specializes the
coalition-scoped active-until-exit route to concrete STV traces: replay facts,
focused-candidate removals, initial activity, and "not focused before exit"
construct the required active invariant for every realized state.
-/
theorem proposition5_5_uncertainty_coalition_benefit_of_statewise_trace_while_active
    {State Voter Candidate : Type*} [DecidableEq Candidate]
    {coalition : Finset Candidate}
    {voters : State → Finset Voter}
    {before after : State → Voter → RCVBallot Candidate}
    {trace : State → STVTrace Candidate}
    {startActive terminalActive : State → Finset Candidate}
    {exAnteBenefits : Candidate → Prop}
    (hcoalition : coalition.Nonempty)
    (exitRank : State → Candidate → ℕ)
    (hactive_rank_lt :
      ∀ state {candidate : Candidate} {round : Fin (trace state).steps.length},
        candidate ∈ coalition →
          candidate ∈ ((trace state).steps.get round).beforeActive →
            round.1 < exitRank state candidate)
    (hreplay : ∀ state,
      (trace state).replaysFrom (startActive state) (terminalActive state))
    (hremove : ∀ state step, step ∈ (trace state).steps →
      step.removesFocusedCandidate)
    (hstart : ∀ state, coalition ⊆ startActive state)
    (hnot_focus_before_exit :
      ∀ state {candidate : Candidate}, candidate ∈ coalition →
        ∀ i : Fin (trace state).steps.length, i.1 < exitRank state candidate →
          ∀ step, step ∈ (trace state).steps.take i.1 →
            step.focus ≠ some candidate)
    (hpreserve : ∀ state,
      coalitionPrefixPreservation (voters state) coalition
        (before state) (after state))
    (hexante : exAnteCoalitionAllBenefitPossible coalition exAnteBenefits) :
    exPostCoalitionAllBenefitImpossible coalition
        (fun state candidate =>
          benefitsViaAction
            (fun round : Fin (trace state).steps.length =>
              (Ballot.activeSupport
                (voters state) (before state)
                ((trace state).steps.get round).beforeActive candidate).card)
            (fun round : Fin (trace state).steps.length =>
              (Ballot.activeSupport
                (voters state) (after state)
                ((trace state).steps.get round).beforeActive candidate).card)
            (fun round : Fin (trace state).steps.length =>
              candidate ∈ ((trace state).steps.get round).beforeActive)) ∧
      exAnteCoalitionAllBenefitPossible coalition exAnteBenefits := by
  constructor
  · intro state
    have hactive_until :
        ActiveUntilExitRankOn coalition
          (fun round : Fin (trace state).steps.length =>
            ((trace state).steps.get round).beforeActive)
          (fun round : Fin (trace state).steps.length => round.1)
          (exitRank state) := by
      exact STVTrace.activeUntilExitRankOn_beforeActive_of_replaysFrom_not_focused_before
        (trace := trace state) (startActive := startActive state)
        (terminalActive := terminalActive state) (tracked := coalition)
        (exitRank := exitRank state)
        (hreplay state) (hremove state) (hstart state)
        (hnot_focus_before_exit state)
    rcases exists_firstExitingCoalitionMember_of_exitRank
        (coalition := coalition)
        (active := fun round : Fin (trace state).steps.length =>
          ((trace state).steps.get round).beforeActive)
        (beforeExit := fun candidate round =>
          candidate ∈ ((trace state).steps.get round).beforeActive)
        hcoalition (exitRank state)
        (by
          intro candidate other round hcandidate hother hrank hactive
          exact ActiveUntilExitRankOn.active_of_rank_lt_of_le
            (tracked := coalition)
            (active := fun round : Fin (trace state).steps.length =>
              ((trace state).steps.get round).beforeActive)
            (roundRank := fun round : Fin (trace state).steps.length => round.1)
            (exitRank := exitRank state) hactive_until hother
            (hactive_rank_lt state hcandidate hactive) hrank) with
      ⟨candidate, hfirst⟩
    exact proposition5_3_coalition_not_all_benefit_of_first_exiting_member
      (voters := voters state) (before := before state) (after := after state)
      hfirst (hpreserve state)
  · exact hexante

/--
Proposition 5.5 trace-backed existential form.  Concrete STV replay facts
prove the ex-post no-all-benefit conclusion, and the ex-ante side is returned
as an existential benefit predicate, matching the paper's existential
uncertainty-side claim at this abstraction level.
-/
theorem proposition5_5_uncertainty_coalition_benefit_exists_exAnte_of_statewise_trace_while_active
    {State Voter Candidate : Type*} [DecidableEq Candidate]
    {coalition : Finset Candidate}
    {voters : State → Finset Voter}
    {before after : State → Voter → RCVBallot Candidate}
    {trace : State → STVTrace Candidate}
    {startActive terminalActive : State → Finset Candidate}
    (hcoalition : coalition.Nonempty)
    (exitRank : State → Candidate → ℕ)
    (hactive_rank_lt :
      ∀ state {candidate : Candidate} {round : Fin (trace state).steps.length},
        candidate ∈ coalition →
          candidate ∈ ((trace state).steps.get round).beforeActive →
            round.1 < exitRank state candidate)
    (hreplay : ∀ state,
      (trace state).replaysFrom (startActive state) (terminalActive state))
    (hremove : ∀ state step, step ∈ (trace state).steps →
      step.removesFocusedCandidate)
    (hstart : ∀ state, coalition ⊆ startActive state)
    (hnot_focus_before_exit :
      ∀ state {candidate : Candidate}, candidate ∈ coalition →
        ∀ i : Fin (trace state).steps.length, i.1 < exitRank state candidate →
          ∀ step, step ∈ (trace state).steps.take i.1 →
            step.focus ≠ some candidate)
    (hpreserve : ∀ state,
      coalitionPrefixPreservation (voters state) coalition
        (before state) (after state)) :
    exPostCoalitionAllBenefitImpossible coalition
        (fun state candidate =>
          benefitsViaAction
            (fun round : Fin (trace state).steps.length =>
              (Ballot.activeSupport
                (voters state) (before state)
                ((trace state).steps.get round).beforeActive candidate).card)
            (fun round : Fin (trace state).steps.length =>
              (Ballot.activeSupport
                (voters state) (after state)
                ((trace state).steps.get round).beforeActive candidate).card)
            (fun round : Fin (trace state).steps.length =>
              candidate ∈ ((trace state).steps.get round).beforeActive)) ∧
      ∃ exAnteBenefits : Candidate → Prop,
        exAnteCoalitionAllBenefitPossible coalition exAnteBenefits := by
  exact proposition5_5_uncertainty_coalition_benefit_exists_exAnte
    (proposition5_5_uncertainty_coalition_benefit_of_statewise_trace_while_active
      (exAnteBenefits := fun candidate => candidate ∈ coalition)
      hcoalition exitRank hactive_rank_lt hreplay hremove hstart
      hnot_focus_before_exit hpreserve
      (by
        intro candidate hcandidate
        exact hcandidate)).1

/--
Proposition 5.6 selfish-addition bridge: if in every realized state the action
adds a new voter whose first active candidate is the target, while old voters'
first active choices are stable, then the target strictly benefits before exit.
-/
theorem proposition5_6_selfish_beneficial_of_new_first_active_support
    {State Voter Candidate Round : Type*} [DecidableEq Candidate]
    {candidate : Candidate}
    {beforeVoters afterVoters : State → Finset Voter}
    {before after : State → Voter → RCVBallot Candidate}
    {active : State → Round → Finset Candidate}
    {beforeExit : State → Round → Prop}
    (witnessRound : State → Round)
    (hbeforeExit : ∀ state, beforeExit state (witnessRound state))
    (hvoters_subset : ∀ state, beforeVoters state ⊆ afterVoters state)
    (hold_stable : ∀ state, ∀ voter ∈ beforeVoters state,
      Ballot.nextActive (after state voter) (active state (witnessRound state)) =
        Ballot.nextActive (before state voter)
          (active state (witnessRound state)))
    (hnew_first : ∀ state, ∃ voter,
      voter ∈ afterVoters state ∧ voter ∉ beforeVoters state ∧
        Ballot.nextActive (after state voter)
          (active state (witnessRound state)) = some candidate) :
    alwaysExPostBeneficial
      (fun state =>
        benefitsViaAction
          (fun round =>
            (Ballot.activeSupport
              (beforeVoters state) (before state)
              (active state round) candidate).card)
          (fun round =>
            (Ballot.activeSupport
              (afterVoters state) (after state)
              (active state round) candidate).card)
          (beforeExit state)) := by
  intro state
  refine ⟨witnessRound state, hbeforeExit state, ?_⟩
  exact Ballot.activeSupport_card_lt_of_subset_forall_nextActive_eq_exists_new
    (hvoters_subset state) (hold_stable state) (hnew_first state)

/--
Proposition 5.6 source-facing robustness interface: selfish first-place
addition is always ex-post beneficial, while a non-selfish strategy may be
ex-post disadvantageous.
-/
theorem proposition5_6_selfish_beneficial_other_may_disadvantage
    {State : Type*} {selfishBenefit otherDisadvantage : State → Prop}
    (hselfish : alwaysExPostBeneficial selfishBenefit)
    (hother : mayBeExPostDisadvantageous otherDisadvantage) :
    alwaysExPostBeneficial selfishBenefit ∧
      mayBeExPostDisadvantageous otherDisadvantage :=
  ⟨hselfish, hother⟩

/--
Proposition 5.6 concrete downside witness: a state and round where the
strategist is eliminated before the beneficiary by less than the added votes
establishes possible ex-post disadvantage.
-/
theorem mayBeExPostDisadvantageous_of_eliminatedEarly_margin
    {State Round Margin : Type*} [LT Margin]
    {eliminatedBeforeBeneficiary : State → Round → Prop}
    {margin addedVotes : State → Round → Margin}
    (state : State) (round : Round)
    (heliminated : eliminatedBeforeBeneficiary state round)
    (hmargin : margin state round < addedVotes state round) :
    mayBeExPostDisadvantageous
      (fun state =>
        eliminatedEarlyByMarginLessThanAddedVotes
          (eliminatedBeforeBeneficiary state)
          (margin state)
          (addedVotes state)) :=
  ⟨state, round, heliminated, hmargin⟩

/--
Source-shaped Proposition 5.6 certificate: selfish first-place additions
strictly increase the target's active support in every state, and one realized
state witnesses the possible downside of a non-selfish strategy.
-/
structure SelfishBenefitMarginCertificate
    {State Voter Candidate Round Margin : Type*} [DecidableEq Candidate]
    [LT Margin] (candidate : Candidate) where
  beforeVoters : State → Finset Voter
  afterVoters : State → Finset Voter
  before : State → Voter → RCVBallot Candidate
  after : State → Voter → RCVBallot Candidate
  active : State → Round → Finset Candidate
  beforeExit : State → Round → Prop
  eliminatedBeforeBeneficiary : State → Round → Prop
  margin : State → Round → Margin
  addedVotes : State → Round → Margin
  witnessRound : State → Round
  badState : State
  badRound : Round
  beforeExit_witness :
    ∀ state, beforeExit state (witnessRound state)
  voters_subset :
    ∀ state, beforeVoters state ⊆ afterVoters state
  old_voters_stable :
    ∀ state, ∀ voter ∈ beforeVoters state,
      Ballot.nextActive (after state voter) (active state (witnessRound state)) =
        Ballot.nextActive (before state voter)
          (active state (witnessRound state))
  new_first_active :
    ∀ state, ∃ voter,
      voter ∈ afterVoters state ∧ voter ∉ beforeVoters state ∧
        Ballot.nextActive (after state voter)
          (active state (witnessRound state)) = some candidate
  eliminated_witness :
    eliminatedBeforeBeneficiary badState badRound
  margin_witness :
    margin badState badRound < addedVotes badState badRound

/--
Build the Proposition 5.6 robustness certificate from the source's explicit
singleton selfish-addition pattern: old voters keep their ballots unchanged and
each state adds one new voter whose ballot is exactly `[candidate]`.
-/
def selfishBenefitMarginCertificate_of_added_singleton_selfish
    {State Voter Candidate Round Margin : Type*} [DecidableEq Candidate]
    [LT Margin] {candidate : Candidate}
    {beforeVoters afterVoters : State → Finset Voter}
    {before after : State → Voter → RCVBallot Candidate}
    {active : State → Round → Finset Candidate}
    {beforeExit : State → Round → Prop}
    {eliminatedBeforeBeneficiary : State → Round → Prop}
    {margin addedVotes : State → Round → Margin}
    (witnessRound : State → Round)
    (newVoter : State → Voter)
    (badState : State) (badRound : Round)
    (hbeforeExit : ∀ state, beforeExit state (witnessRound state))
    (hvoters_subset : ∀ state, beforeVoters state ⊆ afterVoters state)
    (hold_unchanged : ∀ state, ∀ voter ∈ beforeVoters state,
      after state voter = before state voter)
    (hnew_after : ∀ state, newVoter state ∈ afterVoters state)
    (hnew_not_before : ∀ state, newVoter state ∉ beforeVoters state)
    (hnew_ballot : ∀ state, after state (newVoter state) = [candidate])
    (hcandidate_active :
      ∀ state, candidate ∈ active state (witnessRound state))
    (heliminated : eliminatedBeforeBeneficiary badState badRound)
    (hmargin : margin badState badRound < addedVotes badState badRound) :
    SelfishBenefitMarginCertificate
      (State := State) (Voter := Voter) (Candidate := Candidate)
      (Round := Round) (Margin := Margin) candidate where
  beforeVoters := beforeVoters
  afterVoters := afterVoters
  before := before
  after := after
  active := active
  beforeExit := beforeExit
  eliminatedBeforeBeneficiary := eliminatedBeforeBeneficiary
  margin := margin
  addedVotes := addedVotes
  witnessRound := witnessRound
  badState := badState
  badRound := badRound
  beforeExit_witness := hbeforeExit
  voters_subset := hvoters_subset
  old_voters_stable := by
    intro state voter hvoter
    rw [hold_unchanged state voter hvoter]
  new_first_active := by
    intro state
    refine ⟨newVoter state, hnew_after state, hnew_not_before state, ?_⟩
    rw [hnew_ballot state]
    simpa using
      Ballot.nextActive_cons_of_mem candidate ([] : RCVBallot Candidate)
        (active state (witnessRound state))
        (hcandidate_active state)
  eliminated_witness := heliminated
  margin_witness := hmargin

/--
Proposition 5.6 source-facing robustness bridge: selfish first-place additions
strictly increase active support in every state, while the paper's early
elimination-by-small-margin configuration witnesses possible downside for a
non-selfish strategy.
-/
theorem proposition5_6_selfish_beneficial_other_may_disadvantage_of_margin
    {State Voter Candidate Round Margin : Type*} [DecidableEq Candidate]
    [LT Margin]
    {candidate : Candidate}
    {beforeVoters afterVoters : State → Finset Voter}
    {before after : State → Voter → RCVBallot Candidate}
    {active : State → Round → Finset Candidate}
    {beforeExit : State → Round → Prop}
    {eliminatedBeforeBeneficiary : State → Round → Prop}
    {margin addedVotes : State → Round → Margin}
    (witnessRound : State → Round)
    (hbeforeExit : ∀ state, beforeExit state (witnessRound state))
    (hvoters_subset : ∀ state, beforeVoters state ⊆ afterVoters state)
    (hold_stable : ∀ state, ∀ voter ∈ beforeVoters state,
      Ballot.nextActive (after state voter) (active state (witnessRound state)) =
        Ballot.nextActive (before state voter)
          (active state (witnessRound state)))
    (hnew_first : ∀ state, ∃ voter,
      voter ∈ afterVoters state ∧ voter ∉ beforeVoters state ∧
        Ballot.nextActive (after state voter)
          (active state (witnessRound state)) = some candidate)
    (badState : State) (badRound : Round)
    (heliminated : eliminatedBeforeBeneficiary badState badRound)
    (hmargin : margin badState badRound < addedVotes badState badRound) :
    alwaysExPostBeneficial
        (fun state =>
          benefitsViaAction
            (fun round =>
              (Ballot.activeSupport
                (beforeVoters state) (before state)
                (active state round) candidate).card)
            (fun round =>
              (Ballot.activeSupport
                (afterVoters state) (after state)
                (active state round) candidate).card)
            (beforeExit state)) ∧
      mayBeExPostDisadvantageous
        (fun state =>
          eliminatedEarlyByMarginLessThanAddedVotes
            (eliminatedBeforeBeneficiary state)
            (margin state)
            (addedVotes state)) :=
  proposition5_6_selfish_beneficial_other_may_disadvantage
    (proposition5_6_selfish_beneficial_of_new_first_active_support
      witnessRound hbeforeExit hvoters_subset hold_stable hnew_first)
    (mayBeExPostDisadvantageous_of_eliminatedEarly_margin
      badState badRound heliminated hmargin)

/--
Proposition 5.6 source-shaped route when selfish additions leave every old
voter's ballot unchanged.  The old-voter first-active stability premise is then
derived by rewriting the unchanged ballot.
-/
theorem proposition5_6_selfish_beneficial_other_may_disadvantage_of_old_voters_unchanged
    {State Voter Candidate Round Margin : Type*} [DecidableEq Candidate]
    [LT Margin]
    {candidate : Candidate}
    {beforeVoters afterVoters : State → Finset Voter}
    {before after : State → Voter → RCVBallot Candidate}
    {active : State → Round → Finset Candidate}
    {beforeExit : State → Round → Prop}
    {eliminatedBeforeBeneficiary : State → Round → Prop}
    {margin addedVotes : State → Round → Margin}
    (witnessRound : State → Round)
    (hbeforeExit : ∀ state, beforeExit state (witnessRound state))
    (hvoters_subset : ∀ state, beforeVoters state ⊆ afterVoters state)
    (hold_unchanged : ∀ state, ∀ voter ∈ beforeVoters state,
      after state voter = before state voter)
    (hnew_first : ∀ state, ∃ voter,
      voter ∈ afterVoters state ∧ voter ∉ beforeVoters state ∧
        Ballot.nextActive (after state voter)
          (active state (witnessRound state)) = some candidate)
    (badState : State) (badRound : Round)
    (heliminated : eliminatedBeforeBeneficiary badState badRound)
    (hmargin : margin badState badRound < addedVotes badState badRound) :
    alwaysExPostBeneficial
        (fun state =>
          benefitsViaAction
            (fun round =>
              (Ballot.activeSupport
                (beforeVoters state) (before state)
                (active state round) candidate).card)
            (fun round =>
              (Ballot.activeSupport
                (afterVoters state) (after state)
                (active state round) candidate).card)
            (beforeExit state)) ∧
      mayBeExPostDisadvantageous
        (fun state =>
          eliminatedEarlyByMarginLessThanAddedVotes
            (eliminatedBeforeBeneficiary state)
            (margin state)
            (addedVotes state)) := by
  exact
    proposition5_6_selfish_beneficial_other_may_disadvantage_of_margin
      witnessRound hbeforeExit hvoters_subset
      (by
        intro state voter hvoter
        rw [hold_unchanged state voter hvoter])
      hnew_first badState badRound heliminated hmargin

/--
Proposition 5.6 source-shaped route for explicit singleton selfish additions.
If each state adds a new voter whose ballot is exactly `[candidate]`, and the
candidate is active at the witness round, then the new first-active voter
premise follows from the ballot semantics.
-/
theorem proposition5_6_selfish_beneficial_other_may_disadvantage_of_added_singleton_selfish
    {State Voter Candidate Round Margin : Type*} [DecidableEq Candidate]
    [LT Margin]
    {candidate : Candidate}
    {beforeVoters afterVoters : State → Finset Voter}
    {before after : State → Voter → RCVBallot Candidate}
    {active : State → Round → Finset Candidate}
    {beforeExit : State → Round → Prop}
    {eliminatedBeforeBeneficiary : State → Round → Prop}
    {margin addedVotes : State → Round → Margin}
    (witnessRound : State → Round)
    (newVoter : State → Voter)
    (hbeforeExit : ∀ state, beforeExit state (witnessRound state))
    (hvoters_subset : ∀ state, beforeVoters state ⊆ afterVoters state)
    (hold_unchanged : ∀ state, ∀ voter ∈ beforeVoters state,
      after state voter = before state voter)
    (hnew_after : ∀ state, newVoter state ∈ afterVoters state)
    (hnew_not_before : ∀ state, newVoter state ∉ beforeVoters state)
    (hnew_ballot : ∀ state, after state (newVoter state) = [candidate])
    (hcandidate_active :
      ∀ state, candidate ∈ active state (witnessRound state))
    (badState : State) (badRound : Round)
    (heliminated : eliminatedBeforeBeneficiary badState badRound)
    (hmargin : margin badState badRound < addedVotes badState badRound) :
    alwaysExPostBeneficial
        (fun state =>
          benefitsViaAction
            (fun round =>
              (Ballot.activeSupport
                (beforeVoters state) (before state)
                (active state round) candidate).card)
            (fun round =>
              (Ballot.activeSupport
                (afterVoters state) (after state)
                (active state round) candidate).card)
            (beforeExit state)) ∧
      mayBeExPostDisadvantageous
        (fun state =>
          eliminatedEarlyByMarginLessThanAddedVotes
            (eliminatedBeforeBeneficiary state)
            (margin state)
            (addedVotes state)) := by
  let cert :=
    selfishBenefitMarginCertificate_of_added_singleton_selfish
      (candidate := candidate)
      (beforeVoters := beforeVoters)
      (afterVoters := afterVoters)
      (before := before)
      (after := after)
      (active := active)
      (beforeExit := beforeExit)
      (eliminatedBeforeBeneficiary := eliminatedBeforeBeneficiary)
      (margin := margin)
      (addedVotes := addedVotes)
      witnessRound newVoter badState badRound hbeforeExit
      hvoters_subset hold_unchanged hnew_after hnew_not_before
      hnew_ballot hcandidate_active heliminated hmargin
  exact
    proposition5_6_selfish_beneficial_other_may_disadvantage_of_margin
      (candidate := candidate)
      (beforeVoters := cert.beforeVoters)
      (afterVoters := cert.afterVoters)
      (before := cert.before)
      (after := cert.after)
      (active := cert.active)
      (beforeExit := cert.beforeExit)
      (eliminatedBeforeBeneficiary := cert.eliminatedBeforeBeneficiary)
      (margin := cert.margin)
      (addedVotes := cert.addedVotes)
      cert.witnessRound cert.beforeExit_witness cert.voters_subset
      cert.old_voters_stable cert.new_first_active cert.badState cert.badRound
      cert.eliminated_witness cert.margin_witness

/--
Proposition 5.6 certificate form: the source-shaped robustness witness implies
the selfish-benefit and non-selfish-downside conclusion.
-/
theorem proposition5_6_selfish_beneficial_other_may_disadvantage_of_certificate
    {State Voter Candidate Round Margin : Type*} [DecidableEq Candidate]
    [LT Margin] {candidate : Candidate}
    (cert :
      SelfishBenefitMarginCertificate
        (State := State) (Voter := Voter) (Candidate := Candidate)
        (Round := Round) (Margin := Margin) candidate) :
    alwaysExPostBeneficial
        (fun state =>
          benefitsViaAction
            (fun round =>
              (Ballot.activeSupport
                (cert.beforeVoters state) (cert.before state)
                (cert.active state round) candidate).card)
            (fun round =>
              (Ballot.activeSupport
                (cert.afterVoters state) (cert.after state)
                (cert.active state round) candidate).card)
            (cert.beforeExit state)) ∧
      mayBeExPostDisadvantageous
        (fun state =>
          eliminatedEarlyByMarginLessThanAddedVotes
            (cert.eliminatedBeforeBeneficiary state)
            (cert.margin state)
            (cert.addedVotes state)) := by
  exact proposition5_6_selfish_beneficial_other_may_disadvantage_of_margin
    (candidate := candidate)
    (beforeVoters := cert.beforeVoters)
    (afterVoters := cert.afterVoters)
    (before := cert.before)
    (after := cert.after)
    (active := cert.active)
    (beforeExit := cert.beforeExit)
    (eliminatedBeforeBeneficiary := cert.eliminatedBeforeBeneficiary)
    (margin := cert.margin)
    (addedVotes := cert.addedVotes)
    cert.witnessRound cert.beforeExit_witness cert.voters_subset
    cert.old_voters_stable cert.new_first_active cert.badState cert.badRound
    cert.eliminated_witness cert.margin_witness

end DGJ24OptimalStrategiesRCV
