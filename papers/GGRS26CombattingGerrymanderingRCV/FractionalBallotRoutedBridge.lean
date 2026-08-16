import GGRS26CombattingGerrymanderingRCV.BallotRoutedSTV
import GGRS26CombattingGerrymanderingRCV.MainTheorems

open scoped BigOperators

/-!
# Fractional Runner Bridge to Ballot-Routed STV

The library's concrete fractional runner is a particular admissible policy of
the reachable ballot-routed STV semantics.  This file proves the local policy
laws and then maps quota-first/minimum-tally runner rounds into actual source
transitions.  No trace or terminal outcome is supplied as an assumption.
-/

namespace GGRS26CombattingGerrymanderingRCV

open EconCSLib.SocialChoice.Voting

variable {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
variable {voters : Finset Voter} {ballots : Voter -> Ballot Candidate} {quota : ℝ}

/--
The library's proportional surplus update, exposed as an admissible
ballot-routed transfer policy.  The quota precondition is retained inside
`electUpdate`; this is essential because the policy laws are quantified over
all state inputs, not just runner-reachable ones.
-/
noncomputable def fractionalBallotRoutedSTVTransferPolicy
    (hquotaPos : 0 < quota) :
    BallotRoutedSTVTransferPolicy voters ballots quota where
  electUpdate active winner beforeWeight afterWeight :=
    quota ≤ ballotRoutedTally voters ballots active beforeWeight winner ∧
      afterWeight =
        fractionalSTVNextWeight voters ballots quota
          (fractionalSTVStepFromFocus voters ballots quota active beforeWeight winner)
          beforeWeight
  eliminateUpdate _active _loser beforeWeight afterWeight :=
    afterWeight = beforeWeight
  elect_exists := by
    intro active winner beforeWeight _hweight _hactive hquota
    exact ⟨fractionalSTVNextWeight voters ballots quota
      (fractionalSTVStepFromFocus voters ballots quota active beforeWeight winner)
      beforeWeight, ⟨hquota, rfl⟩⟩
  eliminate_exists := by
    intro _active _loser beforeWeight _hweight _hactive
    exact ⟨beforeWeight, rfl⟩
  elect_preserves_nonneg := by
    intro active winner beforeWeight afterWeight hweight hupdate
    rcases hupdate with ⟨hquota, rfl⟩
    apply fractionalSTVNextWeight_nonneg hweight hquotaPos
    intro focused hfocus hkind
    have hfocused : winner = focused := by
      simpa [fractionalSTVStepFromFocus] using Option.some.inj hfocus
    subst focused
    simpa using hquota
  elect_support_weight_le_before := by
    intro active winner beforeWeight afterWeight hweight hupdate voter hvoter hsupport
    rcases hupdate with ⟨hquota, rfl⟩
    have hquota' :
        quota ≤ fractionalActiveTally voters ballots beforeWeight active winner := by
      simpa [ballotRoutedTally, fractionalActiveTally] using hquota
    have htallyPos :
        0 < fractionalActiveTally voters ballots beforeWeight active winner :=
      lt_of_lt_of_le hquotaPos hquota'
    have hfactorLe :
        fractionalSurplusFactor
            (fractionalActiveTally voters ballots beforeWeight active winner) quota ≤ 1 := by
      rw [fractionalSurplusFactor]
      apply (div_le_iff₀ htallyPos).mpr
      linarith
    have hsupport' :
        voter ∈ Ballot.activeSupport voters ballots active winner := by
      simpa [ballotRoutedSupport] using hsupport
    have hkind :
        (fractionalSTVStepFromFocus voters ballots quota active beforeWeight winner).kind =
          StepKind.elect := by
      simp [fractionalSTVStepFromFocus, hquota']
    have hscaled :
        fractionalSurplusFactor
            (fractionalActiveTally voters ballots beforeWeight active winner) quota *
            beforeWeight voter ≤ beforeWeight voter := by
      simpa using
        (mul_le_mul_of_nonneg_right hfactorLe (hweight voter hvoter))
    simpa [fractionalSTVNextWeight, hkind, scaleOnSupport, hsupport'] using hscaled
  elect_unchanged_off_support := by
    intro active winner beforeWeight afterWeight _hweight hupdate voter _hvoter houtside
    rcases hupdate with ⟨hquota, rfl⟩
    have hquota' :
        quota ≤ fractionalActiveTally voters ballots beforeWeight active winner := by
      simpa [ballotRoutedTally, fractionalActiveTally] using hquota
    have houtside' :
        voter ∉ Ballot.activeSupport voters ballots active winner := by
      simpa [ballotRoutedSupport] using houtside
    have hkind :
        (fractionalSTVStepFromFocus voters ballots quota active beforeWeight winner).kind =
          StepKind.elect := by
      simp [fractionalSTVStepFromFocus, hquota']
    simp [fractionalSTVNextWeight, hkind, scaleOnSupport, houtside']
  elect_support_mass_drop_exactly_quota := by
    intro active winner beforeWeight afterWeight _hweight hupdate
    rcases hupdate with ⟨hquota, rfl⟩
    let support := ballotRoutedSupport voters ballots active winner
    let tally := fractionalActiveTally voters ballots beforeWeight active winner
    have htallyPos : 0 < tally := by
      exact lt_of_lt_of_le hquotaPos (by simpa [tally] using hquota)
    have htallyNe : tally ≠ 0 := ne_of_gt htallyPos
    have hdrop := sum_scaleOnSupport_surplusFactor_eq_sum_sub_quota
      (support := support) (voters := support) (weight := beforeWeight)
      (focusedTally := tally) (quota := quota) (by intro voter hvoter; exact hvoter)
      (by rfl) htallyNe
    have hquota' :
        quota ≤ fractionalActiveTally voters ballots beforeWeight active winner := by
      simpa [ballotRoutedTally, fractionalActiveTally] using hquota
    have hkind :
        (fractionalSTVStepFromFocus voters ballots quota active beforeWeight winner).kind =
          StepKind.elect := by
      simp [fractionalSTVStepFromFocus, hquota']
    simpa [fractionalSTVNextWeight, hkind, support, tally, ballotRoutedSupport] using hdrop
  eliminate_weight_unchanged := by
    intro _active _loser beforeWeight afterWeight _hweight hupdate voter _hvoter
    simpa [hupdate]

/-- The source's Droop quota is always strictly positive. -/
theorem stvQuota_pos (seats voters : ℕ) :
    0 < (STVQuota seats voters : ℝ) := by
  exact_mod_cast Nat.succ_pos (voters / (seats + 1))

/--
One selected quota-first/minimum-tally fractional round is an actual
ballot-routed STV transition.  The successor state is constructed from the
runner's own fractional update, not supplied by the caller.
-/
theorem exists_ballotRoutedSTVTransition_of_quotaFirstMinimumTallyChoice
    {initialCandidates : Finset Candidate} {seats : ℕ}
    {before : BallotRoutedSTVState voters initialCandidates}
    {focused : Candidate}
    (hquotaPos : 0 < quota)
    (hchoose :
      (quotaFirstMinimumTallyChoice (Candidate := Candidate) quota).choose
        before.active
        (fractionalActiveTally voters ballots before.weight before.active) =
          some focused)
    (hnotTerminal : ¬ BallotRoutedSTVTerminal seats before)
    (hroom : before.elected.card < seats) :
    ∃ after,
      BallotRoutedSTVTransition ballots quota
        (fractionalBallotRoutedSTVTransferPolicy (voters := voters)
          (ballots := ballots) hquotaPos)
        seats before after := by
  have hfocused : focused ∈ before.active :=
    (quotaFirstMinimumTallyChoice (Candidate := Candidate) quota).choose_mem hchoose
  by_cases hquota :
      quota ≤ ballotRoutedTally voters ballots before.active before.weight focused
  · let step :=
      fractionalSTVStepFromFocus voters ballots quota before.active before.weight focused
    let after : BallotRoutedSTVState voters initialCandidates := {
      active := before.active.erase focused
      elected := insert focused before.elected
      weight := fractionalSTVNextWeight voters ballots quota step before.weight
      active_subset_initial :=
        (Finset.erase_subset focused before.active).trans before.active_subset_initial
      elected_subset_initial := by
        intro candidate hcandidate
        rcases Finset.mem_insert.mp hcandidate with hcandidate | hcandidate
        · simpa [hcandidate] using before.active_subset_initial hfocused
        · exact before.elected_subset_initial hcandidate
      active_elected_disjoint := by
        rw [Finset.disjoint_left]
        intro candidate hcandidateActive hcandidateElected
        rcases Finset.mem_insert.mp hcandidateElected with hcandidate | hcandidate
        · have hne : candidate ≠ focused := (Finset.mem_erase.mp hcandidateActive).1
          exact hne hcandidate
        · exact Finset.disjoint_left.mp before.active_elected_disjoint
            (Finset.mem_erase.mp hcandidateActive).2 hcandidate
      weight_nonneg := by
        apply fractionalSTVNextWeight_nonneg before.weight_nonneg hquotaPos
        intro selected hfocus _hkind
        have hselected : focused = selected := by
          simpa [step, fractionalSTVStepFromFocus] using Option.some.inj hfocus
        subst selected
        simpa [ballotRoutedTally, fractionalActiveTally] using hquota }
    refine ⟨after, ?_⟩
    refine BallotRoutedSTVTransition.elect focused hnotTerminal hfocused hroom hquota
      (by rfl) (by rfl) ?_
    exact ⟨hquota, rfl⟩
  · have hnoQuotaExists :
        ¬ ∃ candidate, candidate ∈ before.active ∧
          quota ≤ fractionalActiveTally voters ballots before.weight before.active candidate := by
      rintro ⟨candidate, hcandidateActive, hcandidateQuota⟩
      have hfocusedQuota :
          quota ≤ fractionalActiveTally voters ballots before.weight before.active focused :=
        quotaFirstMinimumTallyChoice_quotaRespecting
          (Candidate := Candidate) quota hchoose
          ⟨candidate, hcandidateActive, hcandidateQuota⟩
      apply hquota
      simpa [ballotRoutedTally, fractionalActiveTally] using hfocusedQuota
    have hnoQuota : ∀ candidate, candidate ∈ before.active ->
        ballotRoutedTally voters ballots before.active before.weight candidate < quota := by
      intro candidate hcandidateActive
      exact lt_of_not_ge (by
        intro hcandidateQuota
        apply hnoQuotaExists
        refine ⟨candidate, hcandidateActive, ?_⟩
        simpa [ballotRoutedTally, fractionalActiveTally] using hcandidateQuota)
    have hminimum : ∀ candidate, candidate ∈ before.active ->
        ballotRoutedTally voters ballots before.active before.weight focused ≤
          ballotRoutedTally voters ballots before.active before.weight candidate := by
      intro candidate hcandidateActive
      simpa [ballotRoutedTally, fractionalActiveTally] using
        quotaFirstMinimumTallyChoice_minimum_of_no_quota hchoose hnoQuotaExists
          candidate hcandidateActive
    let after : BallotRoutedSTVState voters initialCandidates := {
      active := before.active.erase focused
      elected := before.elected
      weight := before.weight
      active_subset_initial :=
        (Finset.erase_subset focused before.active).trans before.active_subset_initial
      elected_subset_initial := before.elected_subset_initial
      active_elected_disjoint := by
        rw [Finset.disjoint_left]
        intro candidate hcandidateActive hcandidateElected
        exact Finset.disjoint_left.mp before.active_elected_disjoint
          (Finset.mem_erase.mp hcandidateActive).2 hcandidateElected
      weight_nonneg := before.weight_nonneg }
    refine ⟨after, ?_⟩
    refine BallotRoutedSTVTransition.eliminate focused hnotTerminal hfocused hnoQuota
      hminimum (by rfl) (by rfl) ?_
    rfl

end GGRS26CombattingGerrymanderingRCV
