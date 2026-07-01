import EOS07GSP.ProofInterface
import EOS07GSP.PostPaperAudit
import EOS07GSP.Assumptions

/-!
# Paper Interface: Internet Advertising and the Generalized Second-Price Auction

This is the compact human-review surface for Edelman, Ostrovsky, and Schwarz,
*Internet Advertising and the Generalized Second-Price Auction*.  It exposes the
paper-facing definitions and named results; implementation and audit ledgers
remain in `ProofInterface.lean` and `PostPaperAudit.lean`.
-/

namespace EOS07GSP
namespace PaperInterface

open EconCSLib.Auction

/-- Definition 4: locally envy-free outcome predicate. -/
abbrev definition4_locally_envy_free := @locallyEnvyFree

/-- Stable-assignment predicate used by the paper's stable-assignment bridge. -/
abbrev stable_assignment := @stableAssignment

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
abbrev lemma5_locally_envy_free_stable :=
  @EOS07GSP.audit_lemma5_locally_envy_free_equilibrium_stable_assignment

/-- Lemma 6: stable assignment gives LEF equilibrium when bidders exceed slots. -/
abbrev lemma6_tiebreak_ranked_gsp_stable_assignment_locally_envy_free :=
  @EOS07GSP.audit_lemma6_more_bidders_tiebreak_ranked_gsp_stable_assignment_locally_envy_free

/-- Theorem 7: ranked GSP realizes the constructed `B*` next-price outcome. -/
abbrev theorem7_ranked_gsp_bstar_mechanism_realizes_bstar_outcome :=
  @EOS07GSP.audit_theorem7_ranked_gsp_bstar_mechanism_realizes_bstar_outcome

/-- Theorem 7: ranked `B*` payment identity.
Source status: formalizes the paper's recursive VCG-payment and `B*` bid
identity in the ranked finite model. -/
abbrev theorem7_bstar_payment_identity :=
  @EOS07GSP.audit_theorem7_bstar_payment_identity

/-- Theorem 7: the ranked `B*` outcome is locally envy-free.
Source status: direct row for the source subclaim that `B*` is locally
envy-free; the strict tie-broken GSP comparison row below carries the
mechanism-level equilibrium comparison. -/
abbrev theorem7_bstar_locally_envy_free :=
  @EOS07GSP.audit_theorem7_slot_envy_free_of_ordered_values

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
abbrev theorem7_strict_tiebreak_gsp_comparison_conclusion :=
  @EOS07GSP.PaperInterface.theorem7_ranked_bstar_strict_tiebreak_gsp_comparison_from_primitives

/-- Theorem 8: the displayed dropout-price formula equals the finite `B*` threshold.
Source status: algebraic bridge from the paper's `q` formula to finite `B*`
continuation prices. -/
abbrev theorem8_dropout_formula_eq_bstar_threshold :=
  @EOS07GSP.PaperInterface.theorem8_ranked_dropout_formula_eq_bstar_threshold

/-- Theorem 8 Step 2: waiting below `q` is strictly better. -/
abbrev theorem8_q_step2_waiting_before_q_review :=
  @EOS07GSP.PaperInterface.theorem8_source_step2_waiting_before_q_strictly_better

/-- Theorem 8 Step 1: dropping above `q` is strictly better. -/
abbrev theorem8_q_step1_dropping_after_q_review :=
  @EOS07GSP.PaperInterface.theorem8_source_step1_dropping_after_q_strictly_better

/-- Theorem 8: `q` lies in the weak source interval. -/
abbrev theorem8_q_mem_interval_review :=
  @EOS07GSP.PaperInterface.theorem8_source_q_mem_interval

/-- Theorem 8: `q` lies in the strict source interval. -/
abbrev theorem8_q_strict_mem_interval_review :=
  @EOS07GSP.PaperInterface.theorem8_source_q_strict_mem_interval

/-- Theorem 8: `q` is continuous in value. -/
abbrev theorem8_q_continuous_value_review :=
  @EOS07GSP.PaperInterface.theorem8_source_q_continuous_value

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

/-- Theorem 8: strict source values imply the ex-post local best-response condition. -/
abbrev theorem8_strict_values_ex_post_local_deviation :=
  @EOS07GSP.PaperInterface.theorem8_strict_values_named_strategy_ex_post_local_deviation

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

/-- Theorem 8: price-sorted belief-explicit source event has the VCG outcome.
Source status: finite strict-values source-event specialization; the
price-sorted schedule, generated history, terminality proof, belief witness,
and rankwise VCG payoff conclusion are constructed internally. -/
abbrev theorem8_belief_source_extensive_unique_pbe_vcg_conclusion :=
  @EOS07GSP.PaperInterface.theorem8_strict_values_price_sorted_belief_source_event_boundary_threshold_event_ordered_displayed_paper_conclusion

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

/-- Theorem 8: bundled payoff-game main conclusion for strict ranked source values.
Source status: named continuous payoff-PBE, support uniqueness, and finite source-event VCG outcome in one top-level endpoint. -/
abbrev theorem8_continuous_generalized_english_payoff_game_strict_values_main_conclusion_review :=
  @EOS07GSP.PaperInterface.theorem8_continuous_generalized_english_payoff_game_strict_values_main_conclusion

end PaperInterface
end EOS07GSP
