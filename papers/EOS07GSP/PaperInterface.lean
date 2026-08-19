import EOS07GSP.ProofBridge

namespace EOS07GSP

namespace PaperInterface

open EconCSLib.Auction
noncomputable section

/-- Source-facing semantic target for `definition4_locally_envy_free`. -/
def definition4_locally_envy_freeSpec
    {Bidder Slot : Type*} [DecidableEq Bidder]
    (E : PositionEnvironment Slot) (M : PositionMechanism Bidder Slot)
    (values bids : Bidder → ℝ) (allocatedPositions : ℕ)
    (bidderAtRank : ℕ → Bidder) (slotAtRank : ℕ → Slot) : Prop :=
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
              (M bids).paymentPerClick (bidderAtRank (rank + 1)))

/-- Source-facing semantic target for `stable_assignment`. -/
def stable_assignmentSpec
    {Bidder Slot : Type*}
    (E : PositionEnvironment Slot) (O : PositionOutcome Bidder Slot)
    (values : Bidder → ℝ) : Prop :=
  O.StableAssignment E values ↔
    O.FeasibleAssignment ∧
      O.IndividuallyRational E values ∧
        ∀ (i j : Bidder) (s : Slot),
          O.slotOf j = some s →
            E.clickThroughRate s * (values i - O.paymentPerClick j) ≤
              O.utility E values i

/-- Source-facing semantic target for `first_price_running_example_profitable_revision_chain`. -/
def first_price_running_example_profitable_revision_chainSpec : Prop :=
  (200 * (10 - (203 / 100 : ℝ)) <
    200 * (10 - (202 / 100 : ℝ))) ∧
  (100 * (4 - (201 / 100 : ℝ)) <
    200 * (4 - (203 / 100 : ℝ))) ∧
  (100 * (10 - (202 / 100 : ℝ)) <
    200 * (10 - (204 / 100 : ℝ)))

/-- Source-facing semantic target for `remark1_gsp_payments_weakly_dominate_vcg`. -/
def remark1_gsp_payments_weakly_dominate_vcgSpec
    {value clickThroughRate : ℕ → ℝ}
    (hvalue_nonneg : ∀ i, 0 ≤ value i)
    (hvalue_mono : ∀ i, value (i + 1) ≤ value i)
    (hclick_nonneg : ∀ i, 0 ≤ clickThroughRate i)
    {rank remaining : ℕ}
    (hclick_pos : 0 < clickThroughRate rank) : Prop :=
  paper_theorem7_ranked_vcg_tail_payment
      value clickThroughRate rank remaining / clickThroughRate rank ≤
    value (rank + 1)

/-- Source-facing semantic target for `remark2_vcg_truthful`. -/
def remark2_vcg_truthfulSpec
    {Bidder Slot : Type*} [Fintype Bidder] [DecidableEq Bidder]
    [Fintype Slot] [DecidableEq Slot]
    {E : PositionEnvironment Slot}
    (hclick_pos : ∀ s, 0 < E.clickThroughRate s) : Prop :=
  PositionMechanism.TruthfulDominantStrategy E
    (PositionMechanism.positionVCGMechanism
      (Bidder := Bidder) (Slot := Slot) E)

/-- Source-facing semantic target for `remark3_gsp_not_truthful`. -/
def remark3_gsp_not_truthfulSpec : Prop :=
  ¬ PositionMechanism.TruthfulDominantStrategy
    gspCounterexampleEnvironment gsp3TwoSlotMechanism

/-- Source-facing semantic target for `running_example_truthful_gsp_nash`. -/
def running_example_truthful_gsp_nashSpec : Prop :=
  PositionMechanism.IsNashEquilibrium
    paper_eos_running_example_environment
    gsp3TwoSlotMechanism
    paper_eos_running_example_values3
    paper_eos_running_example_values3

/-- Source-facing semantic target for `running_example_truthful_gsp_revenue_comparison`. -/
def running_example_truthful_gsp_revenue_comparisonSpec : Prop :=
  paper_eos_running_example_clickThroughRate 0 *
        paper_eos_running_example_value 1 +
      paper_eos_running_example_clickThroughRate 1 *
        paper_eos_running_example_value 2 >
    paper_theorem7_ranked_vcg_tail_payment
        paper_eos_running_example_value
        paper_eos_running_example_clickThroughRate 0 2 +
      paper_theorem7_ranked_vcg_tail_payment
        paper_eos_running_example_value
        paper_eos_running_example_clickThroughRate 1 1

/-- Source-facing semantic target for `lemma5_locally_envy_free_stable`. -/
def lemma5_locally_envy_free_stableSpec
    {Bidder Slot : Type*} [DecidableEq Bidder]
    (E : PositionEnvironment Slot) (M : PositionMechanism Bidder Slot)
    (values bids : Bidder → ℝ)
    (hfeasible : (M bids).FeasibleAssignment)
    (hIR : (M bids).IndividuallyRational E values)
    (h : M.LocallyEnvyFreeEquilibrium E values bids) : Prop :=
  (M bids).StableAssignment E values

/-- Source-facing semantic target for `lemma6_tiebreak_ranked_gsp_stable_assignment_locally_envy_free`. -/
def lemma6_tiebreak_ranked_gsp_stable_assignment_locally_envy_freeSpec
    {m n : ℕ} (hnm : n < m) {value clickThroughRate : ℕ → ℝ}
    (O : PositionOutcome (Fin m) (Fin n)) (bids : Fin m → ℝ)
    (hout : paper_ranked_gsp_tiebreak_mechanism m n bids = O)
    (hstrict : ∀ {i j : Fin m}, i.val < j.val → bids j < bids i)
    (hclick_nonneg : ∀ s : Fin n, 0 ≤ clickThroughRate s.val)
    (hstable :
      O.StableAssignment
        (paper_theorem7_ranked_environment clickThroughRate)
        (fun i : Fin m => value i.val)) : Prop :=
  (paper_ranked_gsp_tiebreak_mechanism m n).LocallyEnvyFreeEquilibrium
    (paper_theorem7_ranked_environment clickThroughRate)
    (fun i : Fin m => value i.val) bids

/-- Source-facing semantic target for `theorem7_ranked_gsp_bstar_mechanism_realizes_bstar_outcome`. -/
def theorem7_ranked_gsp_bstar_mechanism_realizes_bstar_outcomeSpec
    {n : ℕ} {value vcgTotalPayment clickThroughRate : ℕ → ℝ}
    (hclick_pos : ∀ i, 0 < clickThroughRate i)
    (hclick_strict_mono : ∀ i, clickThroughRate (i + 1) < clickThroughRate i)
    (hrec :
      ∀ i : ℕ,
        vcgTotalPayment i =
          (clickThroughRate i - clickThroughRate (i + 1)) * value (i + 1) +
            vcgTotalPayment (i + 1))
    (hpayment_lt_value :
      ∀ i : ℕ, vcgTotalPayment i < clickThroughRate i * value i) : Prop :=
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
          value vcgTotalPayment clickThroughRate).paymentPerClick i

/-- Source-facing semantic target for `theorem7_bstar_payment_identity`. -/
def theorem7_bstar_payment_identitySpec
    (value vcgTotalPayment clickThroughRate : ℕ → ℝ) (i : ℕ)
    (hclick_ne : clickThroughRate i ≠ 0) : Prop :=
  clickThroughRate i *
    paper_theorem7_bstar_bid value vcgTotalPayment clickThroughRate (i + 1) =
    vcgTotalPayment i

/-- Source-facing semantic target for `theorem7_bstar_locally_envy_free`. -/
def theorem7_bstar_locally_envy_freeSpec
    {n : ℕ} {value vcgTotalPayment clickThroughRate : ℕ → ℝ}
    (hclick_ne : ∀ r : Fin n, clickThroughRate r.val ≠ 0)
    (hclick_mono : ∀ k : ℕ, clickThroughRate (k + 1) ≤ clickThroughRate k)
    (hvalue_mono : ∀ a b : ℕ, a ≤ b → value b ≤ value a)
    (hrec :
      ∀ k : ℕ,
        vcgTotalPayment k =
          (clickThroughRate k - clickThroughRate (k + 1)) *
              value (k + 1) +
            vcgTotalPayment (k + 1)) : Prop :=
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
            (fun i : Fin n => value i.val) i

/-- Source-facing semantic target for `theorem7_no_positive_transfer_conclusion`. -/
def theorem7_no_positive_transfer_conclusionSpec
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
    (hvalue_nonneg : ∀ i, 0 ≤ value i) : Prop :=
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
          other.revenue (paper_theorem7_ranked_environment clickThroughRate)

/-- Source-facing semantic target for `theorem7_strict_tiebreak_gsp_comparison_conclusion`. -/
def theorem7_strict_tiebreak_gsp_comparison_conclusionSpec
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
      ∀ k : ℕ, k + 1 < n → clickThroughRate (k + 1) < clickThroughRate k) : Prop :=
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
              (paper_theorem7_ranked_environment clickThroughRate)

/-- Source-facing semantic target for `theorem8_dropout_formula_eq_bstar_threshold`. -/
def theorem8_dropout_formula_eq_bstar_thresholdSpec
    (value clickThroughRate : ℕ → ℝ) (remaining rank : ℕ)
    (hclick_pos : ∀ i, 0 < clickThroughRate i) : Prop :=
  theorem8RankedGeneralizedEnglishDropoutPrice
      clickThroughRate
      (fun k =>
        theorem7BStarBid value
          (fun j =>
            paper_theorem7_ranked_vcg_tail_payment
              value clickThroughRate j remaining)
          clickThroughRate (k + 2))
      value rank =
    theorem8BStarThresholdBid value clickThroughRate (remaining + 1)
      (rank + 1)

/-- Source-facing semantic target for `theorem8_q_step2_waiting_before_q_review`. -/
def theorem8_q_step2_waiting_before_q_reviewSpec
    {clickThroughRate lastDropout value : ℕ → ℝ}
    {state : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hclock_lt :
      state.clockPrice <
        paper_theorem8_generalized_english_ranked_dropout_price
          clickThroughRate lastDropout value rank) : Prop :=
  clickThroughRate (rank + 1) * (value (rank + 1) - lastDropout rank) <
    clickThroughRate rank * (value (rank + 1) - state.clockPrice)

/-- Source-facing semantic target for `theorem8_q_step1_dropping_after_q_review`. -/
def theorem8_q_step1_dropping_after_q_reviewSpec
    {clickThroughRate lastDropout value : ℕ → ℝ}
    {state : PaperTheorem8GeneralizedEnglishAuctionState ℕ}
    {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hthreshold_lt :
      paper_theorem8_generalized_english_ranked_dropout_price
          clickThroughRate lastDropout value rank <
        state.clockPrice) : Prop :=
  clickThroughRate rank * (value (rank + 1) - state.clockPrice) <
    clickThroughRate (rank + 1) * (value (rank + 1) - lastDropout rank)

/-- Source-facing semantic target for `theorem8_q_mem_interval_review`. -/
def theorem8_q_mem_interval_reviewSpec
    {clickThroughRate lastDropout value : ℕ → ℝ} {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hcurrent_nonneg : 0 ≤ clickThroughRate (rank + 1))
    (hcurrent_le : clickThroughRate (rank + 1) ≤ clickThroughRate rank)
    (hlastDropout_le : lastDropout rank ≤ value (rank + 1)) : Prop :=
  lastDropout rank ≤
      paper_theorem8_generalized_english_ranked_dropout_price
        clickThroughRate lastDropout value rank ∧
    paper_theorem8_generalized_english_ranked_dropout_price
        clickThroughRate lastDropout value rank ≤ value (rank + 1)

/-- Source-facing semantic target for `theorem8_q_strict_mem_interval_review`. -/
def theorem8_q_strict_mem_interval_reviewSpec
    {clickThroughRate lastDropout value : ℕ → ℝ} {rank : ℕ}
    (hclick_pos : 0 < clickThroughRate rank)
    (hcurrent_pos : 0 < clickThroughRate (rank + 1))
    (hcurrent_lt : clickThroughRate (rank + 1) < clickThroughRate rank)
    (hlastDropout_lt : lastDropout rank < value (rank + 1)) : Prop :=
  lastDropout rank <
      paper_theorem8_generalized_english_ranked_dropout_price
        clickThroughRate lastDropout value rank ∧
    paper_theorem8_generalized_english_ranked_dropout_price
        clickThroughRate lastDropout value rank < value (rank + 1)

/-- Source-facing semantic target for `theorem8_q_continuous_value_review`. -/
def theorem8_q_continuous_value_reviewSpec
    (clickThroughRate lastDropout value : ℕ → ℝ) (rank : ℕ) : Prop :=
  Continuous
    (fun bidderValue : ℝ =>
      paper_theorem8_generalized_english_ranked_dropout_price
        clickThroughRate lastDropout
        (Function.update value (rank + 1) bidderValue)
        rank)

def theorem8_continuous_source_local_best_response_support_unique_reviewSpec
    (clickThroughRate : ℕ → ℝ) (boundary : ℕ → ℝ → ℝ)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank) : Prop :=
  let namedStrategy := theorem8ContinuousSourceStrategy clickThroughRate
  namedStrategy.ContinuousInValuation ∧
    Theorem8ContinuousSourceOneStepBestResponse namedStrategy clickThroughRate ∧
      ∀ strategy : Theorem8ContinuousSourceStrategy,
        strategy.ContinuousInValuation →
          Theorem8ContinuousSourceOneStepBestResponse
            strategy clickThroughRate →
            strategy.SupportEq namedStrategy boundary

/-- Source-facing semantic target for `theorem8_strict_values_ex_post_local_deviation`. -/
def theorem8_strict_values_ex_post_local_deviationSpec
    (model : theorem8StrictOrderedValueCertificate) : Prop :=
  let localModel :=
    paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
      (theorem8StrictOrderedLocalOptimalityCertificateOfStrictValues model)
  paper_theorem8_bstar_ranked_threshold_local_deviation_sequential_rationality_statement
    localModel.clickThroughRate localModel.value localModel.remaining
    (paper_theorem8_bstar_ranked_threshold_strategy
      localModel.value localModel.clickThroughRate localModel.remaining)

/-- Source-facing semantic target for `theorem8_continuous_generalized_english_payoff_game_strict_values_main_conclusion_review`. -/
def theorem8_continuous_generalized_english_payoff_game_strict_values_main_conclusion_reviewSpec
    (model : theorem8StrictOrderedValueCertificate) (n : ℕ) : Prop :=
  let game :=
    Theorem8ContinuousGeneralizedEnglishPayoffGame.ofStrictValues model
  let scheduledRanks :=
    paper_theorem8_bstar_ranked_threshold_price_sorted_fin_schedule
      (theorem8StrictOrderedLocalOptimalityCertificateOfStrictValues model) n
  let rankSchedule :=
    paper_theorem8_bstar_ranked_threshold_fin_schedule_ranks scheduledRanks
  let localModel :=
    paper_theorem8_bstar_ranked_threshold_strict_ordered_local_deviation_exact_schedule_model
      (theorem8StrictOrderedLocalOptimalityCertificateOfStrictValues model)
  let activeRanks := rankSchedule.toFinset
  let initialState :=
    paper_theorem8_bstar_ranked_threshold_finite_active_exact_record_cold_start_state
      localModel activeRanks
  let finalState :=
    paper_theorem8_bstar_ranked_threshold_exact_drop_schedule_final_state
      localModel initialState rankSchedule
  let G :=
    paper_theorem8_bstar_ranked_threshold_terminal_record_source_extensive_dynamic_game_of_states
      localModel initialState finalState
  let continuation :=
    fun k =>
      theorem7BStarBid localModel.value
        (fun j =>
          paper_theorem7_ranked_vcg_tail_payment
            localModel.value localModel.clickThroughRate j
            localModel.remaining)
        localModel.clickThroughRate (k + 2)
  let namedContinuousStrategy :=
    theorem8ContinuousSourceStrategy localModel.clickThroughRate
  game.PerfectBayesianEquilibrium namedContinuousStrategy ∧
    (∀ strategy : Theorem8ContinuousSourceStrategy,
      game.PerfectBayesianEquilibrium strategy →
        strategy.SupportEq namedContinuousStrategy
          Theorem8ContinuousGeneralizedEnglishPayoffGame.nonnegativeSupport) ∧
      ∀ strategy : Theorem8ContinuousSourceStrategy,
        game.PerfectBayesianEquilibrium strategy →
          G.PerfectBayesianEquilibrium
              (strategy.inducedActionStrategy continuation localModel.value) ∧
            G.outcomeOf
                (strategy.inducedActionStrategy continuation localModel.value) =
              G.vcgOutcome ∧
              strategy.ProfileEq
                namedContinuousStrategy continuation localModel.value

end

end PaperInterface
end EOS07GSP
