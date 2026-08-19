import EOS07GSP.Implementation
import EOS07GSP.PostPaperAudit
import EOS07GSP.Assumptions
import EOS07GSP.ContinuousHistory
import EOS07GSP.OrderedExPost

/-!
# Paper Interface: Internet Advertising and the Generalized Second-Price Auction

This is the compact human-review surface for Edelman, Ostrovsky, and Schwarz,
*Internet Advertising and the Generalized Second-Price Auction*.  It exposes the
paper-facing definitions and named results; implementation and audit ledgers
remain in `ProofInterface.lean` and `PostPaperAudit.lean`.
-/

namespace EOS07GSP
namespace ProofBridge

open EconCSLib.Auction
open EOS07GSP.PaperInterface

/-- Definition 4: a static GSP equilibrium is locally envy-free exactly when
each allocated bidder weakly prefers her current rank to exchanging with the
bidder one rank above.  This theorem exposes the paper's displayed inequality
directly rather than counting a proposition-valued abbreviation as proof.

Source status: direct proved unfolding of Definition 4 in the pinned NBER text. -/
theorem definition4_locally_envy_free
    {Bidder Slot : Type*} [DecidableEq Bidder]
    (E : PositionEnvironment Slot) (M : PositionMechanism Bidder Slot)
    (values bids : Bidder → ℝ) (allocatedPositions : ℕ)
    (bidderAtRank : ℕ → Bidder) (slotAtRank : ℕ → Slot) :
    sourceDefinition4LocallyEnvyFree E M values bids allocatedPositions
        bidderAtRank slotAtRank ↔
      M.IsNashEquilibrium E values bids ∧
        (∀ rank : ℕ, rank < allocatedPositions →
          (M bids).slotOf (bidderAtRank rank) = some (slotAtRank rank)) ∧
        ∀ rank : ℕ, rank + 1 < allocatedPositions →
          E.clickThroughRate (slotAtRank rank) *
              (values (bidderAtRank (rank + 1)) -
                (M bids).paymentPerClick (bidderAtRank rank)) ≤
            E.clickThroughRate (slotAtRank (rank + 1)) *
              (values (bidderAtRank (rank + 1)) -
                (M bids).paymentPerClick (bidderAtRank (rank + 1))) := by
  rfl

/-- The paper's stable-assignment vocabulary: feasibility, individual
rationality, and no profitable bidder/assigned-position rematch.  The explicit
unfolding theorem prevents the proposition-valued definition from being
mistaken for proof evidence.

Source status: direct proved unfolding of the paper's stable-assignment vocabulary. -/
theorem stable_assignment
    {Bidder Slot : Type*}
    (E : PositionEnvironment Slot) (O : PositionOutcome Bidder Slot)
    (values : Bidder → ℝ) :
    O.StableAssignment E values ↔
      O.FeasibleAssignment ∧
        O.IndividuallyRational E values ∧
          ∀ (i j : Bidder) (s : Slot),
            O.slotOf j = some s →
              E.clickThroughRate s * (values i - O.paymentPerClick j) ≤
                O.utility E values i := by
  rfl

/-- Section 2.2 first-price example: successive bid revisions are profitable. -/
abbrev first_price_running_example_profitable_revision_chain :=
  @EOS07GSP.audit_first_price_running_example_profitable_revision_chain

/-- Remark 1: truthful GSP payments weakly dominate VCG per-click payments. -/
abbrev remark1_gsp_payments_weakly_dominate_vcg :=
  @EOS07GSP.audit_remark1_truthful_gsp_payment_weakly_dominates_vcg_per_click

/-- Remark 2: VCG position mechanism is truthful. -/
abbrev remark2_vcg_truthful :=
  @EOS07GSP.audit_remark2_finite_position_vcg_truthful

/-- Remark 3: GSP is not dominant-strategy truthful. -/
abbrev remark3_gsp_not_truthful :=
  @EOS07GSP.audit_gsp_not_dominant_strategy_truthful

/-- Running example: truthful GSP bids are a Nash equilibrium. -/
abbrev running_example_truthful_gsp_nash :=
  @EOS07GSP.audit_running_example_truthful_gsp_is_nash

/-- Running example: truthful GSP revenue exceeds VCG revenue. -/
abbrev running_example_truthful_gsp_revenue_comparison :=
  @EOS07GSP.audit_running_example_truthful_gsp_revenue_gt_vcg_revenue

/-- Lemma 5: locally envy-free equilibrium gives a stable assignment. -/
theorem lemma5_locally_envy_free_stable
    {Bidder Slot : Type*} [DecidableEq Bidder]
    (E : PositionEnvironment Slot) (M : PositionMechanism Bidder Slot)
    (values bids : Bidder → ℝ)
    (hfeasible : (M bids).FeasibleAssignment)
    (hIR : (M bids).IndividuallyRational E values)
    (h : M.LocallyEnvyFreeEquilibrium E values bids) :
    (M bids).StableAssignment E values := by
  exact
    EOS07GSP.audit_lemma5_locally_envy_free_equilibrium_stable_assignment
      E M values bids hfeasible hIR h

/-- Lemma 6: stable assignment gives LEF equilibrium when bidders exceed slots. -/
theorem lemma6_tiebreak_ranked_gsp_stable_assignment_locally_envy_free
    {m n : ℕ} (hnm : n < m) {value clickThroughRate : ℕ → ℝ}
    (O : PositionOutcome (Fin m) (Fin n)) (bids : Fin m → ℝ)
    (hout : paper_ranked_gsp_tiebreak_mechanism m n bids = O)
    (hstrict : ∀ {i j : Fin m}, i.val < j.val → bids j < bids i)
    (hclick_nonneg : ∀ s : Fin n, 0 ≤ clickThroughRate s.val)
    (hstable :
      O.StableAssignment
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin m => value i.val)) :
    (paper_ranked_gsp_tiebreak_mechanism m n).LocallyEnvyFreeEquilibrium
      (paper_theorem7_ranked_environment clickThroughRate)
      (fun i : Fin m => value i.val) bids := by
  exact
    EOS07GSP.audit_lemma6_more_bidders_tiebreak_ranked_gsp_stable_assignment_locally_envy_free
      hnm O bids hout hstrict hclick_nonneg hstable

/-- Theorem 7: ranked GSP realizes the constructed `B*` next-price outcome. -/
theorem theorem7_ranked_gsp_bstar_mechanism_realizes_bstar_outcome
    {n : ℕ} {value vcgTotalPayment clickThroughRate : ℕ → ℝ}
    (hclick_pos : ∀ i, 0 < clickThroughRate i)
    (hclick_strict_mono : ∀ i, clickThroughRate (i + 1) < clickThroughRate i)
    (hrec :
      ∀ i : ℕ,
        vcgTotalPayment i =
          (clickThroughRate i - clickThroughRate (i + 1)) * value (i + 1) +
            vcgTotalPayment (i + 1))
    (hpayment_lt_value :
      ∀ i : ℕ, vcgTotalPayment i < clickThroughRate i * value i) :
    (∀ i : Fin n,
        (paper_ranked_gsp_mechanism (n + 1) n
            (fun bidder : Fin (n + 1) =>
              paper_theorem7_bstar_bid
                value vcgTotalPayment clickThroughRate bidder.val)).slotOf
            i.castSucc =
          some i) ∧
      (paper_ranked_gsp_mechanism (n + 1) n
          (fun bidder : Fin (n + 1) =>
            paper_theorem7_bstar_bid
              value vcgTotalPayment clickThroughRate bidder.val)).slotOf
          (Fin.last n) =
        none ∧
      ∀ i : Fin n,
        (paper_ranked_gsp_mechanism (n + 1) n
            (fun bidder : Fin (n + 1) =>
              paper_theorem7_bstar_bid
                value vcgTotalPayment clickThroughRate bidder.val)).paymentPerClick
            i.castSucc =
          (paper_theorem7_ranked_bstar_outcome (n := n)
            value vcgTotalPayment clickThroughRate).paymentPerClick i := by
  exact
    EOS07GSP.audit_theorem7_ranked_gsp_bstar_mechanism_realizes_bstar_outcome
      hclick_pos hclick_strict_mono hrec hpayment_lt_value

/-- Theorem 7: ranked `B*` payment identity.
Source status: formalizes the paper's recursive VCG-payment and `B*` bid
identity in the ranked finite model. -/
theorem theorem7_bstar_payment_identity
    (value vcgTotalPayment clickThroughRate : ℕ → ℝ) (i : ℕ)
    (hclick_ne : clickThroughRate i ≠ 0) :
    clickThroughRate i *
      paper_theorem7_bstar_bid value vcgTotalPayment clickThroughRate (i + 1) =
      vcgTotalPayment i := by
  exact
    EOS07GSP.audit_theorem7_bstar_payment_identity
      value vcgTotalPayment clickThroughRate i hclick_ne

/-- Theorem 7: the ranked `B*` outcome is locally envy-free.
Source status: direct row for the source subclaim that `B*` is locally
envy-free; the strict tie-broken GSP comparison row below carries the
mechanism-level equilibrium comparison. -/
theorem theorem7_bstar_locally_envy_free
    {n : ℕ} {value vcgTotalPayment clickThroughRate : ℕ → ℝ}
    (hclick_ne : ∀ r : Fin n, clickThroughRate r.val ≠ 0)
    (hclick_mono : ∀ k : ℕ, clickThroughRate (k + 1) ≤ clickThroughRate k)
    (hvalue_mono : ∀ a b : ℕ, a ≤ b → value b ≤ value a)
    (hrec :
      ∀ k : ℕ,
        vcgTotalPayment k =
          (clickThroughRate k - clickThroughRate (k + 1)) *
              value (k + 1) +
            vcgTotalPayment (k + 1)) :
    ∀ (i j : Fin n) (s : Fin n),
      (paper_theorem7_ranked_bstar_outcome
        value vcgTotalPayment clickThroughRate).slotOf j = some s →
        (paper_theorem7_ranked_environment clickThroughRate).clickThroughRate s *
            (value i.val -
              (paper_theorem7_ranked_bstar_outcome
                value vcgTotalPayment clickThroughRate).paymentPerClick j) ≤
          (paper_theorem7_ranked_bstar_outcome
            value vcgTotalPayment clickThroughRate).utility
              (paper_theorem7_ranked_environment clickThroughRate)
              (fun i : Fin n => value i.val) i := by
  exact
    EOS07GSP.audit_theorem7_slot_envy_free_of_ordered_values
      hclick_ne hclick_mono hvalue_mono hrec

/-- Theorem 7: canonical tail conclusion with no positive transfers.
Source status: direct primitive-binder statement for the source's `B*`
construction and VCG-payment comparison. -/
theorem theorem7_no_positive_transfer_conclusion
    {n : ℕ}
    (value vcgTotalPayment clickThroughRate : ℕ → ℝ)
    (hclick_nonneg : ∀ s : Fin n, 0 ≤ clickThroughRate s.val)
    (hclick_pos : ∀ s : Fin n, 0 < clickThroughRate s.val)
    (hclick_mono : ∀ k : ℕ, clickThroughRate (k + 1) ≤ clickThroughRate k)
    (hvalue_mono : ∀ a b : ℕ, a ≤ b → value b ≤ value a)
    (hvcg_rec :
      ∀ k : ℕ,
        vcgTotalPayment k =
          (clickThroughRate k - clickThroughRate (k + 1)) * value (k + 1) +
            vcgTotalPayment (k + 1))
    (hpayment_le_value :
      ∀ i : Fin n, vcgTotalPayment i.val ≤ clickThroughRate i.val * value i.val)
    (hvcg_tail_eq :
      ∀ i : Fin n,
        vcgTotalPayment i.val =
          paper_theorem7_ranked_vcg_tail_payment value clickThroughRate i.val
            (paper_theorem7_ranked_canonical_tail_remaining i))
    (hvalue_nonneg : ∀ i, 0 ≤ value i) :
    ∃ O : PositionOutcome (Fin n) (Fin n),
      paper_position_no_positive_transfers O ∧
        O.SlotEnvyFree
          (paper_theorem7_ranked_environment clickThroughRate)
          (fun i : Fin n => value i.val) ∧
        O.StableAssignment
          (paper_theorem7_ranked_environment clickThroughRate)
          (fun i : Fin n => value i.val) ∧
        (∀ i,
          O.slotOf i =
            (paper_theorem7_ranked_bstar_outcome (n := n)
              value vcgTotalPayment clickThroughRate).slotOf i) ∧
        (∀ i,
          O.paymentPerClick i =
            (paper_theorem7_ranked_bstar_outcome (n := n)
              value vcgTotalPayment clickThroughRate).paymentPerClick i) ∧
        ∀ other : PositionOutcome (Fin n) (Fin n),
          other.FeasibleAssignment →
          other.IndividuallyRational
            (paper_theorem7_ranked_environment clickThroughRate)
            (fun i : Fin n => value i.val) →
          other.SlotEnvyFree
            (paper_theorem7_ranked_environment clickThroughRate)
            (fun i : Fin n => value i.val) →
          (∀ i, O.slotOf i = other.slotOf i) →
          paper_position_no_positive_transfers other →
          O.revenue (paper_theorem7_ranked_environment clickThroughRate) ≤
            other.revenue (paper_theorem7_ranked_environment clickThroughRate) := by
  exact
    theorem7_ranked_bstar_no_positive_transfer_conclusion_from_primitives
      value vcgTotalPayment clickThroughRate hclick_nonneg hclick_pos
      hclick_mono hvalue_mono hvcg_rec hpayment_le_value hvcg_tail_eq
      hvalue_nonneg

/-- Theorem 7: strict source ordering derives sorted GSP comparison slots.
Source status: direct primitive-binder statement for the source's tie-broken
ranking and GSP/VCG comparison. -/
theorem theorem7_strict_tiebreak_gsp_comparison_conclusion
    {n : ℕ}
    (value vcgTotalPayment clickThroughRate : ℕ → ℝ)
    (hclick_nonneg : ∀ s : Fin n, 0 ≤ clickThroughRate s.val)
    (hclick_pos : ∀ s : Fin n, 0 < clickThroughRate s.val)
    (hclick_mono : ∀ k : ℕ, clickThroughRate (k + 1) ≤ clickThroughRate k)
    (hvalue_mono : ∀ a b : ℕ, a ≤ b → value b ≤ value a)
    (hvcg_rec :
      ∀ k : ℕ,
        vcgTotalPayment k =
          (clickThroughRate k - clickThroughRate (k + 1)) * value (k + 1) +
            vcgTotalPayment (k + 1))
    (hpayment_le_value :
      ∀ i : Fin n, vcgTotalPayment i.val ≤ clickThroughRate i.val * value i.val)
    (hvcg_tail_eq :
      ∀ i : Fin n,
        vcgTotalPayment i.val =
          paper_theorem7_ranked_vcg_tail_payment value clickThroughRate i.val
            (paper_theorem7_ranked_canonical_tail_remaining i))
    (hvalue_nonneg : ∀ i, 0 ≤ value i)
    (hvalue_strict : ∀ k : ℕ, k + 1 < n → value (k + 1) < value k)
    (hclick_strict :
      ∀ k : ℕ, k + 1 < n → clickThroughRate (k + 1) < clickThroughRate k) :
    ∃ O : PositionOutcome (Fin n) (Fin n),
      paper_position_no_positive_transfers O ∧
        O.SlotEnvyFree
          (paper_theorem7_ranked_environment clickThroughRate)
          (fun i : Fin n => value i.val) ∧
        O.StableAssignment
          (paper_theorem7_ranked_environment clickThroughRate)
          (fun i : Fin n => value i.val) ∧
        (∀ i,
          O.slotOf i =
            (paper_theorem7_ranked_bstar_outcome (n := n)
              value vcgTotalPayment clickThroughRate).slotOf i) ∧
        (∀ i,
          O.paymentPerClick i =
            (paper_theorem7_ranked_bstar_outcome (n := n)
              value vcgTotalPayment clickThroughRate).paymentPerClick i) ∧
        ∀ bids : Fin n → ℝ,
          (paper_ranked_gsp_tiebreak_mechanism n n).LocallyEnvyFreeEquilibrium
            (paper_theorem7_ranked_environment clickThroughRate)
            (fun i : Fin n => value i.val) bids →
          (∀ i, 0 ≤ bids i) →
            O.revenue (paper_theorem7_ranked_environment clickThroughRate) ≤
              (paper_ranked_gsp_tiebreak_mechanism n n bids).revenue
                (paper_theorem7_ranked_environment clickThroughRate) := by
  exact
    EOS07GSP.PaperInterface.theorem7_ranked_bstar_strict_tiebreak_gsp_comparison_from_primitives
      value vcgTotalPayment clickThroughRate hclick_nonneg hclick_pos
      hclick_mono hvalue_mono hvcg_rec hpayment_le_value hvcg_tail_eq
      hvalue_nonneg hvalue_strict hclick_strict

/-- Theorem 8: the displayed dropout-price formula equals the finite `B*` threshold.
Source status: algebraic bridge from the paper's `q` formula to finite `B*`
continuation prices. -/
abbrev theorem8_dropout_formula_eq_bstar_threshold :=
  @EOS07GSP.PaperInterface.theorem8_ranked_dropout_formula_eq_bstar_threshold

/-- Theorem 8 Step 2: waiting below `q` is strictly better. -/
theorem theorem8_q_step2_waiting_before_q_review
    {clickThroughRate lastDropout value : ℕ → ℝ}
    {state : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hclock_lt :
      state.clockPrice <
        paper_theorem8_generalized_english_ranked_dropout_price
          clickThroughRate lastDropout value rank) :
    clickThroughRate (rank + 1) * (value (rank + 1) - lastDropout rank) <
      clickThroughRate rank * (value (rank + 1) - state.clockPrice) := by
  exact
    EOS07GSP.PaperInterface.theorem8_source_step2_waiting_before_q_strictly_better
      hclick_pos hclock_lt

/-- Theorem 8 Step 1: dropping above `q` is strictly better. -/
theorem theorem8_q_step1_dropping_after_q_review
    {clickThroughRate lastDropout value : ℕ → ℝ}
    {state : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hthreshold_lt :
      paper_theorem8_generalized_english_ranked_dropout_price
          clickThroughRate lastDropout value rank <
        state.clockPrice) :
    clickThroughRate rank * (value (rank + 1) - state.clockPrice) <
      clickThroughRate (rank + 1) * (value (rank + 1) - lastDropout rank) := by
  exact
    EOS07GSP.PaperInterface.theorem8_source_step1_dropping_after_q_strictly_better
      hclick_pos hthreshold_lt

/-- Theorem 8: `q` lies in the weak source interval. -/
abbrev theorem8_q_mem_interval_review :=
  @EOS07GSP.PaperInterface.theorem8_source_q_mem_interval

/-- Theorem 8: `q` lies in the strict source interval. -/
abbrev theorem8_q_strict_mem_interval_review :=
  @EOS07GSP.PaperInterface.theorem8_source_q_strict_mem_interval

/-- Theorem 8: `q` is continuous in value. -/
theorem theorem8_q_continuous_value_review
    (clickThroughRate lastDropout value : ℕ → ℝ) (rank : ℕ) :
    Continuous
      (fun bidderValue : ℝ =>
        paper_theorem8_generalized_english_ranked_dropout_price
          clickThroughRate lastDropout
          (Function.update value (rank + 1) bidderValue)
          rank) := by
  exact
    EOS07GSP.PaperInterface.theorem8_source_q_continuous_value
      clickThroughRate lastDropout value rank

/-- Theorem 8: continuous one-step best responses agree with the formula on support.
Source status: the Step 1/Step 2 payoff comparison implied by the source's
ex-post PBE proof identifies the displayed dropout formula on the support. -/
theorem theorem8_continuous_source_local_best_response_support_unique_review
    (clickThroughRate : ℕ → ℝ) (boundary : ℕ → ℝ → ℝ)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank) :
    let namedStrategy := theorem8ContinuousSourceStrategy clickThroughRate
    namedStrategy.ContinuousInValuation ∧
      Theorem8ContinuousSourceOneStepBestResponse namedStrategy clickThroughRate ∧
        ∀ strategy : Theorem8ContinuousSourceStrategy,
          strategy.ContinuousInValuation →
            Theorem8ContinuousSourceOneStepBestResponse
              strategy clickThroughRate →
              strategy.SupportEq namedStrategy boundary := by
  exact
    EOS07GSP.audit_theorem8_continuous_source_local_best_response_support_unique
      clickThroughRate boundary hclick_pos

/-- Theorem 8: full-history continuous local best responses agree with the
displayed formula on source support.
Source status: closes the source strategy-domain shape `p_i(k,h,s_i)` for the
local payoff theorem; the legal-history PBE endpoint below supplies the
arbitrary-continuation and Bayes-consistency layer. -/
abbrev theorem8_continuous_full_history_local_best_response_support_unique_review :=
  @EOS07GSP.PaperInterface.theorem8_continuous_history_local_best_response_support_unique

/-- Theorem 8: belief-explicit full-history strategy, arbitrary-continuation
ex-post optimality, and operational uniqueness.

Source status: legal-history ex-post PBE, the source-intended refinement.  The
continuous value law and full-history survival events induce an actual Bayes-
consistent conditional belief system.  Sequential rationality compares every
full history-dependent continuation plan for every realized ordered opponent
profile and therefore under every supported posterior.  Every other legal-
history ex-post PBE has the same clock-clamped dropout action at every feasible
history. -/
theorem theorem8_continuous_full_history_bayes_ex_post_review
    {Bidder : Type*} (law : Theorem8ContinuousValueLaw)
    (clickThroughRate : ℕ → ℝ)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank)
    (hclick_strict : ∀ rank,
      clickThroughRate (rank + 1) < clickThroughRate rank) :
    Theorem8LegalHistoryExPostPBE Bidder law clickThroughRate
        (theorem8NamedContinuationPlan clickThroughRate) ∧
      ∀ plan : Theorem8ContinuationPlan,
        Theorem8LegalHistoryExPostPBE Bidder law clickThroughRate plan →
          ∀ rank history ownValue,
            theorem8SourcePriceHistoryLastDropout history ≤ ownValue →
              max (theorem8SourcePriceHistoryLastDropout history)
                  (plan rank history ownValue) =
                paper_theorem8_generalized_english_indifference_price
                  (clickThroughRate rank) (clickThroughRate (rank + 1))
                  (theorem8SourcePriceHistoryLastDropout history)
                  ownValue := by
  exact theorem8_legal_history_ex_post_pbe_exists_unique
    Bidder law clickThroughRate hclick_pos hclick_strict

/-- The literal displayed threshold is not a legal future clock price for all
types at all histories; below-clock thresholds must be read operationally as
immediate dropout. -/
abbrev theorem8_named_history_strategy_not_globally_clock_legal_review :=
  @EOS07GSP.PaperInterface.theorem8_named_history_strategy_not_globally_clock_legal

/-- Theorem 8: reduced continuous local PBE is unique on source support.
Source status: auxiliary payoff-local form; the compact source endpoint below
uses the source theorem's ex-post payoff-game semantics. -/
theorem theorem8_continuous_source_local_pbe_support_unique_review
    (clickThroughRate : ℕ → ℝ) (boundary : ℕ → ℝ → ℝ)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank) :
    let namedStrategy := theorem8ContinuousSourceStrategy clickThroughRate
    Theorem8ContinuousSourceLocalPBE clickThroughRate namedStrategy ∧
      ∀ strategy : Theorem8ContinuousSourceStrategy,
        Theorem8ContinuousSourceLocalPBE clickThroughRate strategy →
          strategy.SupportEq namedStrategy boundary := by
  exact
    EOS07GSP.audit_theorem8_continuous_source_local_pbe_support_unique
      clickThroughRate boundary hclick_pos

/-- Theorem 8: continuous generalized-English payoff-PBE is unique on nonnegative support.
Source status: ex-post payoff-level source game; PBE unfolds to the paper's
drop/continue payoff comparison plus continuity. -/
abbrev theorem8_continuous_generalized_english_payoff_game_support_unique_review :=
  @EOS07GSP.PaperInterface.theorem8_continuous_generalized_english_payoff_game_support_unique

/-- Theorem 8: source-event conclusion from strict ranked source values. -/
abbrev theorem8_price_sorted_finite_schedule_source_event_strict_values_conclusion :=
  @EOS07GSP.PaperInterface.theorem8_price_sorted_finite_schedule_source_event_strict_values_boundary_threshold_event_ordered_displayed_conclusion

/-- Theorem 8: source-event conclusion with the paper's dropout-price formula.
Source status: finite strict-values source-event specialization of the
continuous dropout-price formula. -/
abbrev theorem8_source_event_strict_values_payment_formula :=
  @EOS07GSP.PaperInterface.theorem8_price_sorted_finite_schedule_source_event_strict_values_payment_formula

/-- Theorem 8: unique source-event PBE with dropout-price formula and VCG payoff.
Source status: finite strict-values source-event specialization with formula
and VCG conclusion. -/
abbrev theorem8_source_event_strict_values_unique_pbe_formula_conclusion :=
  @EOS07GSP.PaperInterface.theorem8_price_sorted_finite_schedule_source_event_strict_values_unique_pbe_formula_conclusion

/-- Theorem 8: price-sorted finite source-event trace gives the full VCG state-game conclusion.
Source status: finite strict-values source-event specialization retaining the source-event trace, exact dropout history, unique PBE, VCG outcome equality, and rankwise slot/payment/utility equalities. -/
abbrev theorem8_source_event_strict_values_trace_full_vcg_conclusion :=
  @EOS07GSP.PaperInterface.theorem8_price_sorted_finite_schedule_source_event_strict_values_threshold_event_trace_full_vcg_conclusion

/-- Theorem 8: continuous formula is profile-unique in the finite source checker.
Source status: auxiliary finite source-sequential specialization of the
continuous formula. -/
theorem theorem8_continuous_source_profile_unique_source_sequential_pbe
    (model : theorem8StrictOrderedValueCertificate)
    (initialState : PaperTheorem8GeneralizedEnglishAuctionState ℕ) :
    let localModel :=
      paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
        (theorem8StrictOrderedLocalOptimalityCertificateOfStrictValues model)
    let continuation :=
      fun k =>
        theorem7BStarBid localModel.value
          (fun j =>
            paper_theorem7_ranked_vcg_tail_payment
              localModel.value localModel.clickThroughRate j
              localModel.remaining)
          localModel.clickThroughRate (k + 2)
    let namedStrategy :=
      theorem8ContinuousSourceStrategy localModel.clickThroughRate
    namedStrategy.ContinuousInValuation ∧
      (sourceSequentialGame localModel initialState).PerfectBayesianEquilibrium
        (namedStrategy.inducedActionStrategy continuation localModel.value) ∧
      ∀ otherStrategy : Theorem8ContinuousSourceStrategy,
        (sourceSequentialGame localModel initialState).PerfectBayesianEquilibrium
          (otherStrategy.inducedActionStrategy continuation localModel.value) →
        otherStrategy.ProfileEq namedStrategy continuation localModel.value := by
  exact
    EOS07GSP.audit_theorem8_continuous_source_strategy_profile_unique_source_sequential_pbe_of_strict_values
      model initialState

/-- Theorem 8: source-event unique PBE stated via the induced continuous action rule.
Source status: finite source-event specialization of the continuous formula's
induced action rule. -/
abbrev theorem8_source_event_strict_values_unique_pbe_continuous_action_formula :=
  @EOS07GSP.audit_theorem8_price_sorted_finite_schedule_source_event_strict_values_unique_pbe_continuous_action_formula_conclusion

/-- Theorem 8: source-event PBE continuous strategies agree on the finite profile.
Source status: finite source-event profile uniqueness for continuous
dropout-price strategies. -/
abbrev theorem8_source_event_strict_values_continuous_profile_unique_source_extensive_pbe :=
  @EOS07GSP.audit_theorem8_price_sorted_finite_schedule_source_event_strict_values_continuous_profile_unique_source_extensive_pbe_conclusion

/-- Theorem 8: payoff-PBE continuous strategies give the finite VCG source-event outcome.
Source status: continuous payoff-PBE semantics with nonnegative support,
specialized to the strict finite source event and the paper's dropout formula. -/
abbrev theorem8_source_event_strict_values_payoff_pbe_nonnegative_support_conclusion :=
  @EOS07GSP.PaperInterface.theorem8_price_sorted_finite_schedule_source_event_strict_values_payoff_pbe_nonnegative_support_conclusion

/-- Theorem 8: continuous payoff-game PBE gives the strict source-event VCG outcome.
Source status: top-down ex-post payoff-game statement linked to the finite
source-event VCG route. -/
abbrev theorem8_continuous_generalized_english_payoff_game_strict_values_source_event_conclusion_review :=
  @EOS07GSP.PaperInterface.theorem8_continuous_generalized_english_payoff_game_strict_values_source_event_conclusion

end ProofBridge
end EOS07GSP
