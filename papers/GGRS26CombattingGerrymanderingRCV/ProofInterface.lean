import GGRS26CombattingGerrymanderingRCV.PaperInterface

/-!
# Proof endpoints for the paper-facing GGRS specifications

`PaperInterface` contains each source claim once as a transparent `Spec`.
This module supplies the separately compiled evidence endpoint for that
specification without adding a second human semantic-review target.
-/

namespace GGRS26CombattingGerrymanderingRCV

open EconCSLib.SocialChoice.Voting

theorem paper_lemma_c1_pav_selector_eq_unique_integer_interval
    {seats : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1) :
    paper_lemma_c1_pav_selector_eq_unique_integer_intervalSpec
      (seats := seats) hpos hle := by
  obtain ⟨seatCount, hmin⟩ :=
    exists_isMinArgmaxOn (pavSeatScore partyShare seats) seats
  have hpaper : paper_pav_min_argmax seatCount partyShare seats := by
    simpa [paper_pav_min_argmax, paper_pav_seat_score, pavSeatMinArgmax,
      pavSeatScore] using hmin
  refine ⟨seatCount, hpaper, ?_⟩
  have hinterval := paper_pav_min_argmax_seat_interval hpos hle hpaper
  have hinteger : paper_pav_integer_interval (seatCount : ℤ) partyShare seats := by
    constructor
    · exact_mod_cast hinterval.1
    · exact_mod_cast hinterval.2
  refine ⟨(seatCount : ℤ), rfl, hinteger, ?_, ?_⟩
  · intro other hother
    exact pavSeatIntegerInterval_eq_of_pavSeatInterval
      (by simpa [paper_pav_seat_interval] using hinterval) hother
  · intro otherSeatCount hother
    have hotherInterval := paper_pav_min_argmax_seat_interval hpos hle hother
    exact pavSeatIntegerInterval_eq_of_pavSeatInterval
      (by simpa [paper_pav_seat_interval] using hinterval)
      (by
        constructor
        · exact_mod_cast hotherInterval.1
        · exact_mod_cast hotherInterval.2)

theorem paper_proposition1_all_ballot_routed_surplus_transfer_outcomes_and_selected_pav
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter -> Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    {seats voters : ℕ} {partyShare : ℝ}
    (policy : BallotRoutedSTVTransferPolicy allVoters ballots
      (STVQuota seats voters : ℝ))
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartyComplete :
      paper_complete_party_ranking_ballots
        partyVoters ballots partyCandidates initialActive)
    (hotherComplete :
      paper_complete_party_ranking_ballots
        otherPartyVoters ballots otherPartyCandidates initialActive)
    (hvoters_card : voters = allVoters.card)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherPartyInitialActive : otherPartyCandidates ⊆ initialActive)
    (hinitialActiveSubset : initialActive ⊆ partyCandidates ∪ otherPartyCandidates)
    (hpartyShareCard :
      partyShare * (voters : ℝ) = (partyVoters.card : ℝ))
    (hotherShareCard :
      (1 - partyShare) * (voters : ℝ) = (otherPartyVoters.card : ℝ)) :
    paper_proposition1_all_ballot_routed_surplus_transfer_outcomes_and_selected_pavSpec
      policy hpos hle hvoters hpartyCandidates hotherPartyCandidates
      hpartyComplete hotherComplete hvoters_card hvoterPartition hvoterDisjoint
      hcandidateDisjoint hpartyInitialActive hotherPartyInitialActive
      hinitialActiveSubset hpartyShareCard hotherShareCard := by
  intro terminal hrun hterminal pavSeatCount hpav
  have hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates :=
    paper_complete_party_ranking_ballots_solid_coalition hpartyComplete
  have hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates :=
    paper_complete_party_ranking_ballots_solid_coalition hotherComplete
  simpa [paper_proposition1_ballot_routed_stv_initial_state,
    paper_seat_share_rounded] using
    (proposition1_seatSharesRounded_of_ballotRoutedSTVTerminalRun_and_pavMinArgmax
      (Voter := Voter) (Candidate := Candidate)
      (partyVoters := partyVoters) (otherPartyVoters := otherPartyVoters)
      (allVoters := allVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive)
      (initialWeight := fun _ : Voter => (1 : ℝ))
      (pavSeatCount := pavSeatCount)
      (seats := seats) (voters := voters) (partyShare := partyShare)
      (policy := policy) hpos hle hvoters hpartyCandidates hotherPartyCandidates
      hpartySolid hotherSolid hvoters_card hvoterPartition hcandidateDisjoint
      hpartyInitialActive hotherPartyInitialActive hinitialActiveSubset hpartyShareCard
      hotherShareCard
      (by
        intro voter hvoter
        rfl)
      (by
        intro voter hvoter
        positivity)
      hrun hterminal
      (by
        simpa [paper_pav_min_argmax, paper_pav_seat_score,
          pavSeatMinArgmax, pavSeatScore] using hpav))

end GGRS26CombattingGerrymanderingRCV
