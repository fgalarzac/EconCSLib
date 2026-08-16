import GGRS26CombattingGerrymanderingRCV.BallotRoutedSTVProposition1

/-!
# Human-Facing Paper Interface: Combatting Gerrymandering with Ranked Choice Voting: an Experimental Analysis of Multi-member Districts in the United States

This is the compact Lean file a human should read after formalization to check
whether the paper's definitions and named theorem statements were represented
correctly.

Rules for completing this file:

- Keep the paper's definitions/formatted objects first, in source order.
- Expose the actual paper formulas here; do not only point to generic library
  definitions or implementation witnesses.
- State named results directly, with source hypotheses visible in each theorem
  signature and proof-internal bridges discharged in `MainTheorems.lean`.
- Use short proofs that call into `MainTheorems.lean` or lower proof files.
- If implementation endpoints become broad or helper-heavy, move them to
  `ProofInterface.lean`; keep this filename as the single review surface.
- Keep exhaustive endpoint aliases and proof-seam checks in `PostPaperAudit.lean`,
  not here.

## Paper Definitions

- `paper_pav_score`: PAV/Thiele score used for the `lambda_PAV` comparison.
- `paper_pav_seat_score`: the two-party PAV objective over Republican seat
  counts.
- `paper_pav_min_argmax`: the paper's tie-broken PAV seat-count selector.
- `paper_pav_marginal_conditions`: adjacent marginal inequalities from the
  proof of Lemma C.1.
- `paper_pav_seat_interval`: Lemma C.1 interval characterization for the PAV
  party seat count.
- `paper_seat_share_rounded`: floor/ceiling target used in Proposition 1.
- `paper_source_stv_terminal_iff`: either all seats are elected or the remaining
  active candidates exactly fill the remaining seats.
- `paper_source_stv_batched_transition_iff`: the source's quota-election-batch or
  minimum-tally-elimination transition relation.
- `paper_source_d_favoring_elimination_tie_iff`: the stated cross-party tie rule,
  with within-party ties intentionally left nondeterministic.
- `paper_stv_solid_coalition_party_trace_isolation`: the STV-dynamics bridge
  justifying separate party-level analysis before party exhaustion.
- `paper_stv_quota_floors_fit`: the appendix quota-capacity step that the two
  parties' full Droop-quota floors fit into the district's seats.
- `paper_stv_solid_coalition_quota_witness_bounds`: the quota-witness
  consequence used by the STV lower-bound bridge.
- `paper_stv_solid_coalition_lower_bounds`: the proportional lower-bound
  consequence derived from the quota witness.
- `paper_stv_seat_share_bounds`: the STV floor/ceiling consequence derived from
  the cited lower-bound boundary.

## Named Results

- `paper_pav_interval_seat_share_rounded`: arithmetic bridge from the Lemma C.1
  interval to the Proposition 1 floor/ceiling target.
- `paper_pav_marginal_conditions_seat_share_rounded`: bridge from the source
  proof's adjacent PAV marginal conditions to the same floor/ceiling target.
- `paper_pav_min_argmax_seat_interval`: formalized Lemma C.1 interval statement
  from the paper's min-argmax selector.
- `paper_pav_min_argmax_seat_share_rounded`: formalized PAV component of
  Lemma C.1 / Proposition 1 from the paper's min-argmax selector.
- `paper_stv_solid_coalition_ballots_party_trace_isolation`: bridge from the
  solid-coalition ballot assumption to no cross-party active support before
  party exhaustion.
- `paper_stv_quota_floors_fit`: Appendix quota-capacity arithmetic.
- `paper_stv_solid_coalition_quota_witness_bounds_lower_bounds`: bridge from
  the quota-process witness to proportional STV lower bounds.
- `paper_stv_solid_coalition_lower_bounds_seat_share_bounds`: arithmetic bridge
  from proportional STV lower bounds to floor/ceiling bounds.
- `paper_fractional_stv_quota_first_round_refines_source_batched_algorithm`:
  every concrete generated fractional round refines one source transition.
- `paper_fractional_stv_filled_run_reaches_source_stopping_condition`: the
  generated filled-seat runner reaches one of the source stopping cases.
- `paper_ballot_routed_stv_has_terminal_execution`: the source STV procedure
  has a finite terminal execution from its unit-weight initial count.
- `paper_proposition1_all_ballot_routed_surplus_transfer_outcomes_and_selected_pav`:
  Proposition 1 uniformly over every terminal outcome of a reachable,
  ballot-routed surplus-transfer policy.
- `paper_vote_share_only_selector_refinement_and_cost`: executable direct
  vote-share computation, its rounded-output refinement, and connected
  primitive-operation certificate.
- `paper_proposition1_from_generated_filled_seat_run_fractional_stv_trace_global_weight_terminal_and_pav_min_argmax`:
  Proposition 1 from the generated, total, quota-respecting fractional STV
  filled-seat run and the PAV min-argmax input.
-/

namespace GGRS26CombattingGerrymanderingRCV

open EconCSLib.SocialChoice.Voting

/--
Paper object for the `lambda_PAV` committee-score comparison in Proposition 1.

Source status: direct PAV/Thiele score wrapper used by the Proposition 1
comparison.
-/
noncomputable def paper_pav_score {Candidate : Type*} [DecidableEq Candidate]
    (committee : Finset Candidate) (profile : List (PartyApprovalBallot Candidate)) : ℝ :=
  partyPAVScore committee profile

/--
Paper PAV objective over possible Republican seat counts:
`y_R * sum_{i=1}^{n_R} lambda_PAV(i) +
  (1 - y_R) * sum_{i=1}^{M - n_R} lambda_PAV(i)`.

Source status: direct paper formula from Lemma C.1.
-/
noncomputable def paper_pav_seat_score (partyShare : ℝ) (seats seatCount : ℕ) : ℝ :=
  partyShare * pavHarmonicSum seatCount +
    (1 - partyShare) * pavHarmonicSum (seats - seatCount)

/--
Paper selector for `n_R(y_R, lambda_PAV)`: the smallest seat count maximizing
the PAV objective among seat counts from `0` to `M`.

Source status: direct paper definition from Lemma C.1's `min arg max`.
-/
def paper_pav_min_argmax (seatCount : ℕ) (partyShare : ℝ) (seats : ℕ) : Prop :=
  seatCount ≤ seats ∧
    (∀ candidate, candidate ≤ seats →
      paper_pav_seat_score partyShare seats candidate ≤
        paper_pav_seat_score partyShare seats seatCount) ∧
    (∀ candidate, candidate ≤ seats →
      paper_pav_seat_score partyShare seats candidate =
        paper_pav_seat_score partyShare seats seatCount →
      seatCount ≤ candidate)

/-- The source's leftmost PAV seat selector, constructed over its finite domain. -/
noncomputable def paper_pav_selected_seat_count
    (partyShare : ℝ) (seats : ℕ) : ℕ :=
  pavSeatMinArgmaxChoice partyShare seats

/-- The Lemma C.1 interval over the source's integer variable. -/
def paper_pav_integer_interval
    (seatCount : ℤ) (partyShare : ℝ) (seats : ℕ) : Prop :=
  pavSeatIntegerInterval seatCount partyShare seats

/--
Paper proof inequalities from Lemma C.1 after clearing positive denominators.

For a chosen Republican seat count `n_R`, the previous chosen Republican seat
has strictly larger PAV marginal value than the next Democratic seat, and the
next Republican seat has no larger PAV marginal value than the previous
Democratic seat.

Source status: proof-local inequalities from Lemma C.1.
-/
def paper_pav_marginal_conditions (seatCount : ℕ) (partyShare : ℝ)
    (seats : ℕ) : Prop :=
  pavSeatMarginalConditions seatCount partyShare seats

/--
Paper interval characterization from Lemma C.1:
`y_R (M + 1) - 1 <= n_R < y_R (M + 1)`.

Source status: direct paper interval statement.
-/
def paper_pav_seat_interval (seatCount : ℕ) (partyShare : ℝ) (seats : ℕ) : Prop :=
  pavSeatInterval seatCount partyShare seats

/--
Paper formula target for Proposition 1: a party's seat count is one of the
floor or ceiling of party vote share times the number of seats.

Source status: direct paper formula.
-/
def paper_seat_share_rounded (seatCount : ℕ) (partyShare : ℝ) (seats : ℕ) : Prop :=
  seatShareRounded seatCount partyShare seats

/--
The Republican winner count produced by the paper's concrete fractional-STV
execution: quota-reaching candidates are selected before minimum-tally
eliminations, each elected candidate transfers its fractional surplus, and the
remaining active candidates fill the remaining seats at the source stopping
condition.

This is an operational definition, not a trace or outcome certificate supplied
by a theorem caller.
-/
noncomputable def paper_fractional_stv_republican_seat_count
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (partyCandidates : Finset Candidate) (allVoters : Finset Voter)
    (ballots : Voter → Ballot Candidate) (initialActive : Finset Candidate)
    (seats voters : ℕ) : ℕ :=
  partyFilledSeatCount partyCandidates seats
    (fractionalSTVFilledSeatRunTrace
      (quotaFirstMinimumTallyChoice
        (Candidate := Candidate) (STVQuota seats voters : ℝ))
      allVoters ballots (STVQuota seats voters : ℝ) seats initialActive.card 0
      initialActive (fun _ : Voter => (1 : ℝ))).steps
    (fractionalSTVFilledSeatRunTerminalActive
      (quotaFirstMinimumTallyChoice
        (Candidate := Candidate) (STVQuota seats voters : ℝ))
      allVoters ballots (STVQuota seats voters : ℝ) seats initialActive.card 0
      initialActive (fun _ : Voter => (1 : ℝ)))

/--
The paper's exact stopping condition: stop after all seats have elected
winners, or when the active candidates exactly fill the remaining seats.
-/
def paper_source_stv_terminal {Candidate TransferState : Type*}
    (seats : ℕ) (state : SourceSTVState Candidate TransferState) : Prop :=
  SourceSTVTerminal seats state

/--
The exact source STV transition: elect a nonempty batch whose members meet the
quota and transfer their surplus, or, when nobody meets quota, eliminate a
minimum-tally candidate and transfer those votes.
-/
def paper_source_stv_batched_transition
    {Candidate TransferState : Type*} [DecidableEq Candidate]
    (rule : SourceSTVTransferRule Candidate TransferState)
    (quota : ℝ) (seats : ℕ)
    (before after : SourceSTVState Candidate TransferState) : Prop :=
  SourceSTVBatchedTransition rule quota seats before after

/--
The source's D-favoring elimination convention. If a D candidate is removed,
every candidate tied with that minimum is also D; hence a tied non-D candidate
must be removed first. Choices within either party remain unrestricted.
-/
def paper_source_d_favoring_elimination_tie
    {Candidate TransferState : Type*} [DecidableEq Candidate]
    (favoredParty : Finset Candidate)
    (rule : SourceSTVTransferRule Candidate TransferState)
    (state : SourceSTVState Candidate TransferState) (loser : Candidate) : Prop :=
  SourceDFavoringEliminationTie favoredParty rule state loser

/--
The paper's stopping predicate is exactly its two stated terminal cases.

Source status: exact stopping definition at
`source_tex/section_methods.tex:45-58` and `:79-92`.
-/
theorem paper_source_stv_terminal_iff
    {Candidate TransferState : Type*}
    (seats : ℕ) (state : SourceSTVState Candidate TransferState) :
    paper_source_stv_terminal seats state ↔
      state.elected = seats ∨ state.active.card = seats - state.elected := by
  rfl

/--
The paper's batched STV transition is exactly the quota-election branch or the
no-quota minimum-tally elimination branch, including the corresponding
transfer relation and state update.

Source status: exact STV procedure at
`source_tex/section_methods.tex:45-58` and `:79-92`.
-/
theorem paper_source_stv_batched_transition_iff
    {Candidate TransferState : Type*} [DecidableEq Candidate]
    (rule : SourceSTVTransferRule Candidate TransferState)
    (quota : ℝ) (seats : ℕ)
    (before after : SourceSTVState Candidate TransferState) :
    paper_source_stv_batched_transition rule quota seats before after ↔
      (∃ winners : Finset Candidate,
        ¬ paper_source_stv_terminal seats before ∧
        winners.Nonempty ∧
        winners ⊆ before.active ∧
        winners.card ≤ seats - before.elected ∧
        (∀ candidate, candidate ∈ winners →
          quota ≤ rule.tally before.active before.transferState candidate) ∧
        after.active = before.active \ winners ∧
        after.elected = before.elected + winners.card ∧
        rule.electBatchTransfer before.active winners
          before.transferState after.transferState) ∨
      (∃ loser : Candidate,
        ¬ paper_source_stv_terminal seats before ∧
        loser ∈ before.active ∧
        (∀ candidate, candidate ∈ before.active →
          rule.tally before.active before.transferState candidate < quota) ∧
        (∀ candidate, candidate ∈ before.active →
          rule.tally before.active before.transferState loser ≤
            rule.tally before.active before.transferState candidate) ∧
        after.active = before.active.erase loser ∧
        after.elected = before.elected ∧
        rule.eliminateTransfer before.active loser
          before.transferState after.transferState) := by
  constructor
  · intro h
    change SourceSTVBatchedTransition rule quota seats before after at h
    cases h with
    | electBatch winners hnotTerminal hnonempty hactive hroom hquota
        hafterActive hafterElected htransfer =>
        left
        exact ⟨winners, by simpa [paper_source_stv_terminal] using hnotTerminal,
          hnonempty, hactive, hroom, hquota, hafterActive, hafterElected, htransfer⟩
    | eliminate loser hnotTerminal hactive hnoQuota hminimum
        hafterActive hafterElected htransfer =>
        right
        exact ⟨loser, by simpa [paper_source_stv_terminal] using hnotTerminal,
          hactive, hnoQuota, hminimum, hafterActive, hafterElected, htransfer⟩
  · rintro (⟨winners, hnotTerminal, hnonempty, hactive, hroom, hquota,
        hafterActive, hafterElected, htransfer⟩ |
      ⟨loser, hnotTerminal, hactive, hnoQuota, hminimum,
        hafterActive, hafterElected, htransfer⟩)
    · change SourceSTVBatchedTransition rule quota seats before after
      exact SourceSTVBatchedTransition.electBatch winners
        (by simpa [paper_source_stv_terminal] using hnotTerminal)
        hnonempty hactive hroom hquota hafterActive hafterElected htransfer
    · change SourceSTVBatchedTransition rule quota seats before after
      exact SourceSTVBatchedTransition.eliminate loser
        (by simpa [paper_source_stv_terminal] using hnotTerminal)
        hactive hnoQuota hminimum hafterActive hafterElected htransfer

/--
The paper's D-favoring tie predicate is exactly the stated cross-party
restriction, while leaving within-party tied choices unrestricted.

Source status: exact elimination tie convention at
`source_tex/section_methods.tex:45-58` and `:79-92`.
-/
theorem paper_source_d_favoring_elimination_tie_iff
    {Candidate TransferState : Type*} [DecidableEq Candidate]
    (favoredParty : Finset Candidate)
    (rule : SourceSTVTransferRule Candidate TransferState)
    (state : SourceSTVState Candidate TransferState) (loser : Candidate) :
    paper_source_d_favoring_elimination_tie favoredParty rule state loser ↔
      (loser ∈ favoredParty →
        ∀ candidate, candidate ∈ state.active →
          rule.tally state.active state.transferState candidate =
              rule.tally state.active state.transferState loser →
            candidate ∈ favoredParty) := by
  rfl

/--
Paper STV dynamics bridge: under the solid-coalition ballot condition, a
party's voters give no active support to outside-party candidates at any trace
step until all same-party candidates have been exhausted.

Source status: Proposition 1 proof line justifying separate party-level STV
analysis under solid coalitions.
-/
def paper_stv_solid_coalition_party_trace_isolation
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (partyCandidates : Finset Candidate) (trace : STVTrace Candidate) : Prop :=
  ∀ step, step ∈ trace.steps →
    (∃ same, same ∈ partyCandidates ∧ same ∈ step.beforeActive) →
      ∀ outside, outside ∉ partyCandidates →
        (Ballot.activeSupport voters ballots step.beforeActive outside).card = 0

/--
Paper STV quota-witness consequence used by the quota arithmetic bridge.

Source status: named proof bridge extracted from the Appendix Proposition 1
argument.
-/
def paper_stv_solid_coalition_quota_witness_bounds (seatCount : ℕ)
    (partyShare : ℝ) (seats voters : ℕ) : Prop :=
  stvSolidCoalitionQuotaWitnessBounds seatCount partyShare seats voters

/--
Paper STV proportional lower-bound consequence used by the final
floor/ceiling bridge.

Source status: named proof bridge extracted from the Appendix Proposition 1
argument.
-/
def paper_stv_solid_coalition_lower_bounds (seatCount : ℕ) (partyShare : ℝ)
    (seats : ℕ) :
    Prop :=
  stvSolidCoalitionLowerBounds seatCount partyShare seats

/--
Paper STV floor/ceiling consequence used by Proposition 1.

Source status: direct Proposition 1 target for the STV party seat count.
-/
def paper_stv_seat_share_bounds (seatCount : ℕ) (partyShare : ℝ) (seats : ℕ) :
    Prop :=
  stvSeatShareBounds seatCount partyShare seats

/--
Arithmetic bridge used after Lemma C.1: once the source interval
`y_R (M + 1) - 1 <= n_R < y_R (M + 1)` is available, the party seat count is
one of floor or ceiling of `y_R M`.

Source status: proof step in Lemma C.1 / Proposition 1.
-/
theorem paper_pav_interval_seat_share_rounded {seatCount seats : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hinterval : paper_pav_seat_interval seatCount partyShare seats) :
    paper_seat_share_rounded seatCount partyShare seats := by
  simpa [paper_pav_seat_interval, paper_seat_share_rounded] using
    (pavSeatInterval_seatShareRounded
      (seatCount := seatCount) (seats := seats) (partyShare := partyShare)
      hpos hle hinterval)

/--
Arithmetic bridge from the source proof's adjacent PAV marginal inequalities to
the Proposition 1 floor/ceiling target.

Source status: proof step in Lemma C.1.
-/
theorem paper_pav_marginal_conditions_seat_share_rounded {seatCount seats : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1) (hseat : seatCount ≤ seats)
    (hmarg : paper_pav_marginal_conditions seatCount partyShare seats) :
    paper_seat_share_rounded seatCount partyShare seats := by
  simpa [paper_pav_marginal_conditions, paper_seat_share_rounded] using
    (pavSeatMarginalConditions_seatShareRounded
      (seatCount := seatCount) (seats := seats) (partyShare := partyShare)
      hpos hle hseat hmarg)

/--
Lemma C.1 PAV interval statement: the paper's leftmost maximizing PAV seat
count satisfies `y_R (M + 1) - 1 <= n_R < y_R (M + 1)`.

Source status: named Lemma C.1 statement.
-/
theorem paper_pav_min_argmax_seat_interval {seatCount seats : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hmin : paper_pav_min_argmax seatCount partyShare seats) :
    paper_pav_seat_interval seatCount partyShare seats := by
  simpa [paper_pav_min_argmax, paper_pav_seat_score, paper_pav_seat_interval,
    pavSeatMinArgmax, pavSeatScore, pavSeatInterval] using
    (pavSeatMinArgmax_seatInterval
      (seatCount := seatCount) (seats := seats) (partyShare := partyShare)
      hpos hle hmin)

/--
Lemma C.1 in its full source form: the finite leftmost PAV maximizer exists
and is equal to the unique integer in the displayed half-open interval.

The paper defines `n_R` by `min arg max`.  The source-facing specification
therefore quantifies over that relational definition, rather than exposing the
implementation's `Classical.choose` witness.

Source status: named Lemma C.1 statement.
-/
abbrev paper_lemma_c1_pav_selector_eq_unique_integer_intervalSpec
    {seats : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1) : Prop :=
  ∃ seatCount : ℕ, paper_pav_min_argmax seatCount partyShare seats ∧
    ∃ ell : ℤ,
        (seatCount : ℤ) = ell ∧
          paper_pav_integer_interval ell partyShare seats ∧
            (∀ other : ℤ,
              paper_pav_integer_interval other partyShare seats → other = ell) ∧
            ∀ otherSeatCount : ℕ,
              paper_pav_min_argmax otherSeatCount partyShare seats →
                (otherSeatCount : ℤ) = ell

/--
Exact evidence theorem for the transparent Lemma C.1 specification above.
The `Spec` deliberately repeats the source-facing mathematical content rather
than referring to this theorem, so the audit can compare the two independently.
-/
theorem paper_lemma_c1_pav_selector_eq_unique_integer_interval
    {seats : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1) :
    ∃ seatCount : ℕ, paper_pav_min_argmax seatCount partyShare seats ∧
      ∃ ell : ℤ,
          (seatCount : ℤ) = ell ∧
            paper_pav_integer_interval ell partyShare seats ∧
              (∀ other : ℤ,
                paper_pav_integer_interval other partyShare seats → other = ell) ∧
              ∀ otherSeatCount : ℕ,
                paper_pav_min_argmax otherSeatCount partyShare seats →
                  (otherSeatCount : ℤ) = ell := by
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

/--
PAV component of Lemma C.1 / Proposition 1: the paper's leftmost maximizing PAV
seat count is one of floor or ceiling of `y_R M`.

Source status: named Lemma C.1 / Proposition 1 consequence.
-/
theorem paper_pav_min_argmax_seat_share_rounded {seatCount seats : ℕ}
    {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hmin : paper_pav_min_argmax seatCount partyShare seats) :
    paper_seat_share_rounded seatCount partyShare seats := by
  simpa [paper_pav_min_argmax, paper_pav_seat_score, paper_seat_share_rounded,
    pavSeatMinArgmax, pavSeatScore, seatShareRounded] using
    (pavSeatMinArgmax_seatShareRounded
      (seatCount := seatCount) (seats := seats) (partyShare := partyShare)
      hpos hle hmin)

/--
Solid-coalition STV dynamics bridge: before a party has exhausted all active
same-party candidates, its voters cannot provide active support to an
outside-party candidate.

Source status: Proposition 1 proof step justifying separate party-level STV
analysis from the solid-coalition ballot assumption.
-/
theorem paper_stv_solid_coalition_ballots_party_trace_isolation
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {partyCandidates : Finset Candidate} {trace : STVTrace Candidate}
    (hsolid : SolidCoalitionBallots voters ballots partyCandidates) :
    paper_stv_solid_coalition_party_trace_isolation
      voters ballots partyCandidates trace := by
  simpa [paper_stv_solid_coalition_party_trace_isolation,
    NoCrossPartyTransferBeforeExhaustion] using
    (stvSolidCoalitionBallots_partyTraceIsolation
      (voters := voters) (ballots := ballots)
      (partyCandidates := partyCandidates) (trace := trace) hsolid)

/--
STV quota-capacity arithmetic from the appendix proof: the two parties'
canonical full Droop-quota counts fit within the district's seat count.

Source status: Appendix Proposition 1 quota-capacity proof step.
-/
theorem paper_stv_quota_floors_fit {seats voters : ℕ} {partyShare : ℝ}
    (hshare_nonneg : 0 ≤ partyShare) (hshare_le : partyShare ≤ 1) :
    ⌊partyShare * ((voters : ℝ) / (STVQuota seats voters : ℝ))⌋₊ +
        ⌊(1 - partyShare) *
          ((voters : ℝ) / (STVQuota seats voters : ℝ))⌋₊ ≤ seats :=
  stvTwoPartyQuotaFloors_sum_le_seats hshare_nonneg hshare_le

/--
STV arithmetic bridge: the appendix quota-process witness implies the
proportional lower-bound and seat-conservation boundary.

Source status: Appendix Proposition 1 proof step.
-/
theorem paper_stv_solid_coalition_quota_witness_bounds_lower_bounds
    {seatCount seats voters : ℕ} {partyShare : ℝ}
    (hstv :
      paper_stv_solid_coalition_quota_witness_bounds seatCount partyShare seats voters) :
    paper_stv_solid_coalition_lower_bounds seatCount partyShare seats := by
  simpa [paper_stv_solid_coalition_quota_witness_bounds,
    paper_stv_solid_coalition_lower_bounds,
    stvSolidCoalitionQuotaWitnessBounds] using
    (stvSolidCoalitionLowerBounds_of_quotaLowerBounds
      (seatCount := seatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare)
      (stvSolidCoalitionQuotaLowerBounds_of_quotaWitnessBounds hstv))

/--
STV arithmetic bridge: the proportional lower-bound and seat-conservation
boundary implies the STV floor/ceiling seat-share consequence.

Source status: Appendix Proposition 1 proof step.
-/
theorem paper_stv_solid_coalition_lower_bounds_seat_share_bounds
    {seatCount seats : ℕ} {partyShare : ℝ}
    (hstv : paper_stv_solid_coalition_lower_bounds seatCount partyShare seats) :
    paper_stv_seat_share_bounds seatCount partyShare seats := by
  simpa [paper_stv_solid_coalition_lower_bounds, paper_stv_seat_share_bounds,
    stvSolidCoalitionLowerBounds] using
    (stvSeatShareBounds_of_solidCoalitionLowerBounds
      (seatCount := seatCount) (seats := seats) (partyShare := partyShare)
      hstv)

/--
Source-shaped complete ranking condition for a party block in Proposition 1.
Each voter has a valid ballot listing every initially active candidate, and
whenever any same-party candidate remains active, the voter's first active
candidate is still same-party.

Source status: explicit complete-ranking and solid-coalition ballot convention
from the Proposition 1 setup.
-/
def paper_complete_party_ranking_ballots
    {Voter Candidate : Type*} [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (partyCandidates allCandidates : Finset Candidate) : Prop :=
  ∀ voter, voter ∈ voters →
    Ballot.Valid (ballots voter) ∧
      (∀ candidate, candidate ∈ allCandidates → candidate ∈ ballots voter) ∧
        ∀ active,
          (∃ same, same ∈ partyCandidates ∧ same ∈ active) →
            ∃ same, same ∈ partyCandidates ∧
              Ballot.nextActive (ballots voter) active = some same

/--
Complete party rankings supply the operational solid-coalition predicate used
by the generated STV run theorem.

Source status: bridge from the complete-ranking paper convention to the
trace-level solid-coalition premise.
-/
theorem paper_complete_party_ranking_ballots_solid_coalition
    {Voter Candidate : Type*} [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {partyCandidates allCandidates : Finset Candidate}
    (hcomplete :
      paper_complete_party_ranking_ballots
        voters ballots partyCandidates allCandidates) :
    SolidCoalitionBallots voters ballots partyCandidates := by
  intro voter hvoter active hpartyActive
  exact (hcomplete voter hvoter).2.2 active hpartyActive

/--
Algorithm refinement for one generated fractional round. The concrete
quota-first chooser either produces a singleton source election batch or the
source's no-quota minimum-tally elimination transition. No outcome-level
premise is accepted.

Source status: exact methods-section STV transition protocol, refined by the
generated fractional implementation used elsewhere in this development.
-/
theorem paper_fractional_stv_quota_first_round_refines_source_batched_algorithm
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {voters : Finset Voter} {ballots : Voter → Ballot Candidate}
    {quota : ℝ} {seats elected : ℕ} {active : Finset Candidate}
    {weight : Voter → ℝ} {focused : Candidate}
    (hchoose :
      (quotaFirstMinimumTallyChoice (Candidate := Candidate) quota).choose
          active (fractionalActiveTally voters ballots weight active) =
        some focused)
    (hnotTerminal :
      ¬ paper_source_stv_terminal seats
        (SourceSTVState.mk active elected weight))
    (hroom : elected < seats) :
    let step :=
      fractionalSTVStepFromFocus voters ballots quota active weight focused
    paper_source_stv_batched_transition
      (fractionalSourceSTVTransferRule voters ballots quota) quota seats
      (SourceSTVState.mk active elected weight)
      (SourceSTVState.mk step.afterActive
        (if step.kind = StepKind.elect then elected + 1 else elected)
        (fractionalSTVNextWeight voters ballots quota step weight)) := by
  simpa [paper_source_stv_terminal, paper_source_stv_batched_transition] using
    (fractionalSTVStepFromQuotaFirstMinimumChoice_refines_sourceSTVBatchedTransition
      (voters := voters) (ballots := ballots) (quota := quota)
      (seats := seats) (elected := elected) (active := active)
      (weight := weight) (focused := focused) hchoose hnotTerminal hroom)

/--
Whole-run stopping refinement: with enough initial candidates, the generated
fractional filled-seat runner reaches exactly one of the two stopping cases
specified by the source algorithm.

Source status: exact methods-section stopping protocol for the concrete
generated fractional runner.
-/
theorem paper_fractional_stv_filled_run_reaches_source_stopping_condition
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (voters : Finset Voter) (ballots : Voter → Ballot Candidate)
    (quota : ℝ) (seats : ℕ) (initialActive : Finset Candidate)
    (initialWeight : Voter → ℝ)
    (hseats : seats ≤ initialActive.card) :
    let choice :=
      quotaFirstMinimumTallyChoice (Candidate := Candidate) quota
    let trace :=
      fractionalSTVFilledSeatRunTrace choice voters ballots quota seats
        initialActive.card 0 initialActive initialWeight
    let terminalActive :=
      fractionalSTVFilledSeatRunTerminalActive choice voters ballots quota seats
        initialActive.card 0 initialActive initialWeight
    paper_source_stv_terminal seats
      (SourceSTVState.mk terminalActive (electStepCount trace.steps)
        (fractionalSTVWeightAfterSteps voters ballots quota trace.steps
          initialWeight)) := by
  simpa [paper_source_stv_terminal] using
    (fractionalSTVFilledSeatRun_refines_source_stopping voters ballots quota
      seats initialActive initialWeight hseats)

/--
Proposition 1 reduction from the generated executable fractional STV simulator
using the paper-local quota-first/minimum-tally choice rule. The statement is
over the generated candidate-level run, rather than an abstract trace plus an
external trace-equality hypothesis, and does not accept hidden choice-rule
proof fields from the caller.

Source status: named Proposition 1 theorem-ledger endpoint for the theoretical STV/PAV rounded-seat claim.
-/
theorem paper_proposition1_from_generated_filled_seat_run_fractional_stv_trace_global_weight_terminal_and_pav_min_argmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    (initialWeight partyInitialWeight otherPartyInitialWeight : Voter → ℝ)
    {pavSeatCount seats voters : ℕ} {partyShare : ℝ}
    (hpos : 0 < partyShare) (hle : partyShare ≤ 1)
    (hvoters : seats * (seats + 1) ≤ voters)
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hotherPartyCandidates : seats ≤ otherPartyCandidates.card)
    (hpartySolid : SolidCoalitionBallots partyVoters ballots partyCandidates)
    (hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates)
    (hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ initialWeight voter)
    (hinitialTotalMass :
      (voters : ℝ) = ∑ voter ∈ allVoters, initialWeight voter)
    (hvoterPartition : allVoters = partyVoters ∪ otherPartyVoters)
    (hvoterDisjoint : Disjoint partyVoters otherPartyVoters)
    (hcandidateDisjoint : Disjoint partyCandidates otherPartyCandidates)
    (hpartyInitialActive : partyCandidates ⊆ initialActive)
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hinitialActiveSubset :
      initialActive ⊆ partyCandidates ∪ otherPartyCandidates)
    (hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        initialWeight voter = partyInitialWeight voter)
    (hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        initialWeight voter = otherPartyInitialWeight voter)
    (hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, partyInitialWeight voter)
    (hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, otherPartyInitialWeight voter)
    (hpav : paper_pav_min_argmax pavSeatCount partyShare seats) :
    paper_seat_share_rounded
        (partyFilledSeatCount partyCandidates seats
          (fractionalSTVFilledSeatRunTrace
            (quotaFirstMinimumTallyChoice
              (Candidate := Candidate) (STVQuota seats voters : ℝ))
            allVoters ballots
            (STVQuota seats voters : ℝ) seats initialActive.card 0
            initialActive initialWeight).steps
          (fractionalSTVFilledSeatRunTerminalActive
            (quotaFirstMinimumTallyChoice
              (Candidate := Candidate) (STVQuota seats voters : ℝ))
            allVoters ballots
            (STVQuota seats voters : ℝ) seats initialActive.card 0
            initialActive initialWeight))
        partyShare seats ∧
      paper_seat_share_rounded pavSeatCount partyShare seats := by
  simpa [paper_pav_min_argmax, paper_pav_seat_score,
    paper_seat_share_rounded, pavSeatMinArgmax, pavSeatScore,
    seatShareRounded] using
    (proposition1_seatSharesRounded_of_generatedFilledSeatRunFractionalSTVTrace_globalWeightTerminal_and_pavMinArgmax_of_total
      (Voter := Voter) (Candidate := Candidate)
      (quotaFirstMinimumTallyChoice
        (Candidate := Candidate) (STVQuota seats voters : ℝ))
      (partyVoters := partyVoters) (otherPartyVoters := otherPartyVoters)
      (allVoters := allVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive) initialWeight
      partyInitialWeight otherPartyInitialWeight
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) hpos hle hvoters
      (quotaFirstMinimumTallyChoice_total
        (Candidate := Candidate) (STVQuota seats voters : ℝ))
      (quotaFirstMinimumTallyChoice_quotaRespecting
        (Candidate := Candidate) (STVQuota seats voters : ℝ))
      hpartyCandidates hotherPartyCandidates hpartySolid hotherSolid
      hinitialWeightNonneg hinitialTotalMass hvoterPartition hvoterDisjoint
      hcandidateDisjoint hpartyInitialActive hotherInitialActive
      hinitialActiveSubset hpartyInitialWeightEq hotherInitialWeightEq
      hpartyInitialMass hotherInitialMass hpav)

/--
Proposition 1 source-specialized form with unit voter weights and complete
rankings. This instantiates the more general weighted generated-run theorem
with the paper's one-voter-one-unit convention while keeping the source's
candidate and voter partition, party-share, solid-coalition, and PAV premises
visible.

Source status: named Proposition 1 theorem-ledger endpoint specialized to unit
voter weights and complete-ranking party ballots. The source's D-favoring
tie convention is not encoded here; the checked rounded-seat conclusion uses
the proved quota-first/minimum-tally generated rule and is tie-robust.
-/
theorem paper_proposition1_from_unit_weight_complete_rankings_generated_filled_seat_run_fractional_stv_trace_terminal_and_pav_min_argmax
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    {pavSeatCount seats voters : ℕ} {partyShare : ℝ}
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
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hinitialActiveSubset :
      initialActive ⊆ partyCandidates ∪ otherPartyCandidates)
    (hpartyShareCard :
      partyShare * (voters : ℝ) = (partyVoters.card : ℝ))
    (hotherShareCard :
      (1 - partyShare) * (voters : ℝ) = (otherPartyVoters.card : ℝ))
    (hpav : paper_pav_min_argmax pavSeatCount partyShare seats) :
    paper_seat_share_rounded
        (partyFilledSeatCount partyCandidates seats
          (fractionalSTVFilledSeatRunTrace
            (quotaFirstMinimumTallyChoice
              (Candidate := Candidate) (STVQuota seats voters : ℝ))
            allVoters ballots
            (STVQuota seats voters : ℝ) seats initialActive.card 0
            initialActive (fun _ : Voter => (1 : ℝ))).steps
          (fractionalSTVFilledSeatRunTerminalActive
            (quotaFirstMinimumTallyChoice
              (Candidate := Candidate) (STVQuota seats voters : ℝ))
            allVoters ballots
            (STVQuota seats voters : ℝ) seats initialActive.card 0
            initialActive (fun _ : Voter => (1 : ℝ))))
        partyShare seats ∧
      paper_seat_share_rounded pavSeatCount partyShare seats := by
  have hpartySolid :
      SolidCoalitionBallots partyVoters ballots partyCandidates :=
    paper_complete_party_ranking_ballots_solid_coalition hpartyComplete
  have hotherSolid :
      SolidCoalitionBallots otherPartyVoters ballots otherPartyCandidates :=
    paper_complete_party_ranking_ballots_solid_coalition hotherComplete
  have hinitialWeightNonneg :
      ∀ voter, voter ∈ allVoters → 0 ≤ (fun _ : Voter => (1 : ℝ)) voter := by
    intro voter hvoter
    positivity
  have hinitialTotalMass :
      (voters : ℝ) =
        ∑ voter ∈ allVoters, (fun _ : Voter => (1 : ℝ)) voter := by
    rw [hvoters_card]
    simp
  have hpartyInitialWeightEq :
      ∀ voter, voter ∈ partyVoters →
        (fun _ : Voter => (1 : ℝ)) voter =
          (fun _ : Voter => (1 : ℝ)) voter := by
    intro voter hvoter
    rfl
  have hotherInitialWeightEq :
      ∀ voter, voter ∈ otherPartyVoters →
        (fun _ : Voter => (1 : ℝ)) voter =
          (fun _ : Voter => (1 : ℝ)) voter := by
    intro voter hvoter
    rfl
  have hpartyInitialMass :
      partyShare * (voters : ℝ) =
        ∑ voter ∈ partyVoters, (fun _ : Voter => (1 : ℝ)) voter := by
    rw [hpartyShareCard]
    simp
  have hotherInitialMass :
      (1 - partyShare) * (voters : ℝ) =
        ∑ voter ∈ otherPartyVoters, (fun _ : Voter => (1 : ℝ)) voter := by
    rw [hotherShareCard]
    simp
  simpa using
    (paper_proposition1_from_generated_filled_seat_run_fractional_stv_trace_global_weight_terminal_and_pav_min_argmax
      (Voter := Voter) (Candidate := Candidate)
      (partyVoters := partyVoters)
      (otherPartyVoters := otherPartyVoters)
      (allVoters := allVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive)
      (initialWeight := fun _ : Voter => (1 : ℝ))
      (partyInitialWeight := fun _ : Voter => (1 : ℝ))
      (otherPartyInitialWeight := fun _ : Voter => (1 : ℝ))
      (pavSeatCount := pavSeatCount) (seats := seats) (voters := voters)
      (partyShare := partyShare) hpos hle hvoters
      hpartyCandidates hotherPartyCandidates hpartySolid hotherSolid
      hinitialWeightNonneg hinitialTotalMass hvoterPartition hvoterDisjoint
      hcandidateDisjoint hpartyInitialActive hotherInitialActive
      hinitialActiveSubset hpartyInitialWeightEq hotherInitialWeightEq
      hpartyInitialMass hotherInitialMass hpav)

/--
Direct operational Proposition 1 endpoint for the paper's concrete fractional
STV procedure.  The winner count is produced by the generated ranked-ballot
runner, and the PAV count is the constructed finite leftmost argmax; neither
is accepted as a caller-supplied trace, outcome, or selector witness.

The proof is uniform over all quota-first/minimum-tally choices used by the
runner, so the source's D-favoring tie convention is not needed to establish
this rounded conclusion.  The broader source transfer-rule claim is exposed
below through a reachable ballot-routed operational model.

Source status: direct Proposition 1 endpoint for the fully executed fractional
STV rule used by the paper's simulations and the displayed PAV selector.
-/
theorem paper_proposition1_fractional_stv_complete_rankings_and_selected_pav
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {partyVoters otherPartyVoters allVoters : Finset Voter}
    {ballots : Voter → Ballot Candidate}
    {partyCandidates otherPartyCandidates : Finset Candidate}
    {initialActive : Finset Candidate}
    {seats voters : ℕ} {partyShare : ℝ}
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
    (hotherInitialActive : otherPartyCandidates ⊆ initialActive)
    (hinitialActiveSubset :
      initialActive ⊆ partyCandidates ∪ otherPartyCandidates)
    (hpartyShareCard :
      partyShare * (voters : ℝ) = (partyVoters.card : ℝ))
    (hotherShareCard :
      (1 - partyShare) * (voters : ℝ) = (otherPartyVoters.card : ℝ)) :
    paper_seat_share_rounded
        (paper_fractional_stv_republican_seat_count
          partyCandidates allVoters ballots initialActive seats voters)
        partyShare seats ∧
      paper_seat_share_rounded
        (paper_pav_selected_seat_count partyShare seats) partyShare seats := by
  simpa [paper_fractional_stv_republican_seat_count,
    paper_pav_selected_seat_count] using
    (paper_proposition1_from_unit_weight_complete_rankings_generated_filled_seat_run_fractional_stv_trace_terminal_and_pav_min_argmax
      (Voter := Voter) (Candidate := Candidate)
      (partyVoters := partyVoters) (otherPartyVoters := otherPartyVoters)
      (allVoters := allVoters) (ballots := ballots)
      (partyCandidates := partyCandidates)
      (otherPartyCandidates := otherPartyCandidates)
      (initialActive := initialActive)
      (pavSeatCount := paper_pav_selected_seat_count partyShare seats)
      (seats := seats) (voters := voters) (partyShare := partyShare)
      hpos hle hvoters hpartyCandidates hotherPartyCandidates hpartyComplete
      hotherComplete hvoters_card hvoterPartition hvoterDisjoint
      hcandidateDisjoint hpartyInitialActive hotherInitialActive
      hinitialActiveSubset hpartyShareCard hotherShareCard
      (by
        simpa [paper_pav_min_argmax, paper_pav_selected_seat_count,
          paper_pav_seat_score, pavSeatMinArgmax, pavSeatScore] using
          (pavSeatMinArgmaxChoice_spec partyShare seats)))

/--
The paper's STV transition policy cannot get stuck before its stopping
condition.  This is a construction over the actual ballot state, rather than
an externally supplied trace or an abstract outcome record.

Source status: executable existence half of the methods-section STV rule.
-/
theorem paper_ballot_routed_stv_has_terminal_execution
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    {allVoters : Finset Voter} {ballots : Voter -> Ballot Candidate}
    {partyCandidates initialActive : Finset Candidate} {seats voters : ℕ}
    (policy : BallotRoutedSTVTransferPolicy allVoters ballots
      (STVQuota seats voters : ℝ))
    (hpartyCandidates : seats ≤ partyCandidates.card)
    (hpartyInitialActive : partyCandidates ⊆ initialActive) :
    ∃ terminal,
      BallotRoutedSTVRun ballots (STVQuota seats voters : ℝ) policy seats
        (BallotRoutedSTVState.initial (voters := allVoters)
          (initialCandidates := initialActive) (fun _ : Voter => (1 : ℝ))
          (by intro voter hvoter; positivity)) terminal ∧
        BallotRoutedSTVTerminal seats terminal := by
  apply exists_ballotRoutedSTVTerminalRun (policy := policy)
    (initialWeight := fun _ : Voter => (1 : ℝ))
  exact le_trans hpartyCandidates (Finset.card_le_card hpartyInitialActive)

/--
Visible source-level description of the unit-weight initial STV state.

The operational state stores a total function on `Voter`, while the paper
specifies the ballots of its finite electorate.  Unit weight is consequently
required exactly on `allVoters`; values outside that electorate are
representation-only and are not read by the count or transfer policy.
-/
def paper_unit_weight_initial_state
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (allVoters : Finset Voter) (initialActive : Finset Candidate)
    (state : BallotRoutedSTVState allVoters initialActive) : Prop :=
  state.active = initialActive ∧
    state.elected = ∅ ∧
      ∀ voter, voter ∈ allVoters -> state.weight voter = 1

/--
The source-specified initial count for Proposition 1.  This is constructed
from the finite electorate and active roster, rather than supplied as an
outcome-domain record by a caller.
-/
def paper_proposition1_ballot_routed_stv_initial_state
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (allVoters : Finset Voter) (initialActive : Finset Candidate) :
    BallotRoutedSTVState allVoters initialActive :=
  BallotRoutedSTVState.initial (voters := allVoters)
    (initialCandidates := initialActive) (fun _ : Voter => (1 : ℝ))
    (by
      intro voter hvoter
      positivity)

/-- The internally constructed Proposition 1 initial count has unit voter weight. -/
theorem paper_proposition1_ballot_routed_stv_initial_state_unit_weight
    {Voter Candidate : Type*} [DecidableEq Voter] [DecidableEq Candidate]
    (allVoters : Finset Voter) (initialActive : Finset Candidate) :
    paper_unit_weight_initial_state allVoters initialActive
      (paper_proposition1_ballot_routed_stv_initial_state allVoters initialActive) := by
  constructor
  · rfl
  constructor
  · rfl
  intro voter hvoter
  rfl

/--
Exact-header initial-state witness for the universal terminal-outcome domain
in Proposition 1.  Together with the conditional terminal-execution bridge
below, this rules out a vacuous outcome domain while retaining the source's
finite-electorate unit-weight initial count.
-/
theorem paper_proposition1_ballot_routed_stv_initial_state_exists
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
    ∃ initialState : BallotRoutedSTVState allVoters initialActive,
      paper_unit_weight_initial_state allVoters initialActive initialState := by
  exact ⟨paper_proposition1_ballot_routed_stv_initial_state allVoters initialActive,
    paper_proposition1_ballot_routed_stv_initial_state_unit_weight
      allVoters initialActive⟩

/--
Exact-header nonvacuity receipt for the universal terminal-outcome domain in
the Proposition 1 endpoint below. This is not an additional source premise:
it uses the same finite-electorate unit-weight state and the complete
Proposition 1 header, so the audited existential has no hidden alignment.
-/
theorem paper_proposition1_ballot_routed_stv_outcome_domain_nonempty
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
    ∃ terminal,
      Relation.ReflTransGen
          (BallotRoutedSTVTransition ballots (STVQuota seats voters : ℝ)
            policy seats)
          (paper_proposition1_ballot_routed_stv_initial_state
            allVoters initialActive) terminal ∧
        BallotRoutedSTVTerminal seats terminal := by
  have hseats : seats ≤ initialActive.card :=
    le_trans hpartyCandidates (Finset.card_le_card hpartyInitialActive)
  apply exists_ballotRoutedSTVTerminalRun (policy := policy)
    (initialWeight := fun _ : Voter => (1 : ℝ))
  exact hseats

/--
Source-wide Proposition 1 endpoint for every terminal outcome of the paper's
STV procedure.  A policy updates actual ballot weights, routes each remaining
ballot to its next active candidate, removes exactly one quota on an election,
and eliminates a minimum tally only when no quota is present.  This includes
fractional transfer and random whole-vote transfer without accepting a raw
global run, party projection, or final seat count from the caller.

The run is universally quantified in the conclusion because the source rule
permits transfer and within-party tie choices.  The preceding theorem proves
that at least one such terminal run exists.

Source status: direct Proposition 1 endpoint for the source's stated class of
surplus-preserving ballot-routed STV implementations and the selected PAV
comparison.
-/
abbrev paper_proposition1_all_ballot_routed_surplus_transfer_outcomes_and_selected_pavSpec
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
      (1 - partyShare) * (voters : ℝ) = (otherPartyVoters.card : ℝ)) : Prop :=
  ∀ terminal,
    Relation.ReflTransGen
        (BallotRoutedSTVTransition ballots (STVQuota seats voters : ℝ)
          policy seats)
        (paper_proposition1_ballot_routed_stv_initial_state
          allVoters initialActive) terminal ->
      BallotRoutedSTVTerminal seats terminal ->
        ∀ pavSeatCount : ℕ,
          paper_pav_min_argmax pavSeatCount partyShare seats ->
            paper_seat_share_rounded
                (ballotRoutedPartyFinalSeats partyCandidates seats terminal)
                partyShare seats ∧
              paper_seat_share_rounded pavSeatCount partyShare seats

/--
Exact evidence theorem for the transparent Proposition 1 specification above.
The specification exposes every source-model premise, policy transition law,
and terminal-outcome conclusion without referring to this theorem.
-/
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
    ∀ terminal,
      Relation.ReflTransGen
          (BallotRoutedSTVTransition ballots (STVQuota seats voters : ℝ)
            policy seats)
          (paper_proposition1_ballot_routed_stv_initial_state
            allVoters initialActive) terminal ->
        BallotRoutedSTVTerminal seats terminal ->
          ∀ pavSeatCount : ℕ,
            paper_pav_min_argmax pavSeatCount partyShare seats ->
                paper_seat_share_rounded
                  (ballotRoutedPartyFinalSeats partyCandidates seats terminal)
                  partyShare seats ∧
                paper_seat_share_rounded pavSeatCount partyShare seats := by
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
/--
Direct-computation refinement and efficiency certificate. The evaluator's
output is exactly the floor/ceiling pair permitted by Proposition 1, and the
same returned evaluation carries a cost of five unit-cost arithmetic
operations (one multiplication, two divisions, one addition, one truncated
subtraction). This formalizes the source-supported constant-size per-query
computation, not the paper's empirical whole-map runtime.

Source status: methods-section vote-share-only computation used inside the map
search, with an explicit source-supported primitive cost model.
-/
theorem paper_vote_share_only_selector_refinement_and_cost
    {seatCount partyVotes voters seats : ℕ} {partyShare : ℝ}
    (hvoters : 0 < voters)
    (hshare : partyShare = (partyVotes : ℝ) / (voters : ℝ)) :
    (paper_seat_share_rounded seatCount partyShare seats ↔
        seatCount =
          (voteShareRoundingSelectorInstrumented
            partyVotes voters seats).1.1 ∨
        seatCount =
          (voteShareRoundingSelectorInstrumented
            partyVotes voters seats).1.2) ∧
      (voteShareRoundingSelectorInstrumented
        partyVotes voters seats).2.total = 5 := by
  simpa [paper_seat_share_rounded] using
    (voteShareRoundingSelectorInstrumented_refines_rounded_output_with_cost
      (seatCount := seatCount) hvoters hshare)

end GGRS26CombattingGerrymanderingRCV
