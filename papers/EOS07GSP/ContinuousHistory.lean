import EOS07GSP.Implementation

/-!
# EOS07 Theorem 8: full price-history strategy layer

The source writes a continuous strategy as `p_i(k, h, s_i)`, where `h` is the
entire list of earlier dropout prices.  The older continuous layer in
`ProofInterface.lean` retained only the most recent dropout price.  This file
closes that strategy-shape mismatch for the already-proved local payoff
argument: strategies may depend on the whole history, while the named EOS
formula is proved to depend only on the most recent dropout price and to be the
unique continuous local best response on source support at every history.

This is deliberately not called a perfect Bayesian equilibrium theorem.  The
separate remaining theorem must still derive the local best-response condition
from a continuous-type, belief-consistent extensive-form PBE.
-/

namespace EOS07GSP
namespace PaperInterface

noncomputable section

universe u

variable {Bidder : Type u}

/-- A source history is stored newest dropout price first, matching
`h = (b_{k+1}, ..., b_K)` in the paper. -/
abbrev Theorem8SourcePriceHistory := List ℝ

/-- The price paid if the bidder drops next: `b_{k+1}`, or zero at the empty
history, exactly as in the source convention. -/
def theorem8SourcePriceHistoryLastDropout
    (history : Theorem8SourcePriceHistory) : ℝ :=
  history.head?.getD 0

@[simp]
theorem theorem8_source_price_history_last_dropout_nil :
    theorem8SourcePriceHistoryLastDropout [] = 0 := by
  rfl

@[simp]
theorem theorem8_source_price_history_last_dropout_cons
    (price : ℝ) (history : Theorem8SourcePriceHistory) :
    theorem8SourcePriceHistoryLastDropout (price :: history) = price := by
  rfl

/-- The source strategy-profile shape `p_i(k,h,s_i)`.  The bidder coordinate is
kept explicit because Theorem 8 allows bidder-asymmetric beliefs and strategy
profiles even though its displayed equilibrium formula is bidder independent. -/
structure Theorem8ContinuousHistoryStrategy (Bidder : Type*) where
  dropoutPrice : Bidder → ℕ → Theorem8SourcePriceHistory → ℝ → ℝ

namespace Theorem8ContinuousHistoryStrategy

/-- The source's continuity restriction, holding rank and full history fixed. -/
def ContinuousInValuation
    (strategy : Theorem8ContinuousHistoryStrategy Bidder) : Prop :=
  ∀ bidder rank history,
    Continuous
      (fun bidderValue => strategy.dropoutPrice bidder rank history bidderValue)

/-- Equality on every nonnegative/source-supported value at every full price
history. -/
def SupportEq
    (strategy other : Theorem8ContinuousHistoryStrategy Bidder)
    (boundary : ℕ → Theorem8SourcePriceHistory → ℝ) : Prop :=
  ∀ bidder rank history bidderValue,
    boundary rank history ≤ bidderValue →
      strategy.dropoutPrice bidder rank history bidderValue =
        other.dropoutPrice bidder rank history bidderValue

end Theorem8ContinuousHistoryStrategy

/-- The history-shaped EOS strategy.  The theorem's displayed formula uses the
full history only through its most recent dropout price. -/
def theorem8ContinuousHistoryStrategy
    (Bidder : Type*) (clickThroughRate : ℕ → ℝ) :
    Theorem8ContinuousHistoryStrategy Bidder where
  dropoutPrice := fun _bidder rank history bidderValue =>
    theorem8ContinuousSourceDropoutPrice clickThroughRate rank
      (theorem8SourcePriceHistoryLastDropout history) bidderValue

/-- The named history strategy is definitionally the displayed source formula. -/
theorem theorem8_continuous_history_strategy_dropout_eq_formula
    (clickThroughRate : ℕ → ℝ) (bidder : Bidder) (rank : ℕ)
    (history : Theorem8SourcePriceHistory) (bidderValue : ℝ) :
    (theorem8ContinuousHistoryStrategy Bidder clickThroughRate).dropoutPrice
        bidder rank history bidderValue =
      theorem8ContinuousSourceDropoutPrice clickThroughRate rank
        (theorem8SourcePriceHistoryLastDropout history) bidderValue := by
  rfl

/-- The displayed formula is independent of older entries once the most recent
dropout price is fixed. -/
theorem theorem8_continuous_history_strategy_tail_irrelevant
    (clickThroughRate : ℕ → ℝ) (bidder : Bidder) (rank : ℕ)
    (history history' : Theorem8SourcePriceHistory) (bidderValue : ℝ)
    (hlast : theorem8SourcePriceHistoryLastDropout history =
      theorem8SourcePriceHistoryLastDropout history') :
    (theorem8ContinuousHistoryStrategy Bidder clickThroughRate).dropoutPrice
        bidder rank history bidderValue =
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate).dropoutPrice
        bidder rank history' bidderValue := by
  simp [theorem8ContinuousHistoryStrategy, hlast]

/-- The full-history named strategy is continuous in the bidder's value. -/
theorem theorem8_continuous_history_strategy_continuous_in_value
    (clickThroughRate : ℕ → ℝ) :
    (theorem8ContinuousHistoryStrategy Bidder
      clickThroughRate).ContinuousInValuation := by
  intro bidder rank history
  exact theorem8_continuous_source_dropout_price_continuous_in_value
    clickThroughRate rank (theorem8SourcePriceHistoryLastDropout history)

/-- Full-history version of the paper's local drop/continue payoff condition. -/
def Theorem8ContinuousHistoryOneStepBestResponse
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (clickThroughRate : ℕ → ℝ) : Prop :=
  ∀ bidder rank history bidderValue clockPrice,
    (strategy.dropoutPrice bidder rank history bidderValue ≤ clockPrice →
      clickThroughRate rank * (bidderValue - clockPrice) ≤
        clickThroughRate (rank + 1) *
          (bidderValue - theorem8SourcePriceHistoryLastDropout history)) ∧
      (¬ strategy.dropoutPrice bidder rank history bidderValue ≤ clockPrice →
        clickThroughRate (rank + 1) *
            (bidderValue - theorem8SourcePriceHistoryLastDropout history) ≤
          clickThroughRate rank * (bidderValue - clockPrice))

/-- The named history-shaped formula satisfies the local payoff condition at
every full history. -/
theorem theorem8_continuous_history_named_strategy_one_step_best_response
    (clickThroughRate : ℕ → ℝ)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank) :
    Theorem8ContinuousHistoryOneStepBestResponse
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate)
      clickThroughRate := by
  intro bidder rank history bidderValue clockPrice
  simpa [theorem8ContinuousHistoryStrategy] using
    theorem8_continuous_source_named_strategy_one_step_best_response
      clickThroughRate hclick_pos rank
        (theorem8SourcePriceHistoryLastDropout history)
        bidderValue clockPrice

/-- Collapse one selected full history to the older `(rank,last-price,value)`
strategy shape, using the named formula everywhere else.  This lets the
existing Step 1/Step 2 algebra be reused without assuming that an arbitrary
strategy ignores older history. -/
def Theorem8ContinuousHistoryStrategy.atHistory
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (clickThroughRate : ℕ → ℝ) (targetBidder : Bidder) (targetRank : ℕ)
    (targetHistory : Theorem8SourcePriceHistory) :
    Theorem8ContinuousSourceStrategy where
  dropoutPrice := fun rank lastDropout bidderValue =>
    if rank = targetRank ∧
        lastDropout = theorem8SourcePriceHistoryLastDropout targetHistory then
      strategy.dropoutPrice targetBidder targetRank targetHistory bidderValue
    else
      theorem8ContinuousSourceDropoutPrice
        clickThroughRate rank lastDropout bidderValue

/-- Continuity of a full-history strategy transfers to each selected-history
collapse. -/
theorem theorem8_continuous_history_atHistory_continuous
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (clickThroughRate : ℕ → ℝ) (targetBidder : Bidder) (targetRank : ℕ)
    (targetHistory : Theorem8SourcePriceHistory)
    (hcont : strategy.ContinuousInValuation) :
    (strategy.atHistory clickThroughRate targetBidder targetRank
      targetHistory).ContinuousInValuation := by
  intro rank lastDropout
  by_cases htarget : rank = targetRank ∧
      lastDropout = theorem8SourcePriceHistoryLastDropout targetHistory
  · simpa [Theorem8ContinuousHistoryStrategy.atHistory, htarget] using
      hcont targetBidder targetRank targetHistory
  · simpa [Theorem8ContinuousHistoryStrategy.atHistory, htarget] using
      theorem8_continuous_source_dropout_price_continuous_in_value
        clickThroughRate rank lastDropout

/-- The full-history local payoff condition transfers to each selected-history
collapse; off the selected history the collapse uses the already-proved named
formula. -/
theorem theorem8_continuous_history_atHistory_one_step_best_response
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (clickThroughRate : ℕ → ℝ) (targetBidder : Bidder) (targetRank : ℕ)
    (targetHistory : Theorem8SourcePriceHistory)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank)
    (hbest : Theorem8ContinuousHistoryOneStepBestResponse
      strategy clickThroughRate) :
    Theorem8ContinuousSourceOneStepBestResponse
      (strategy.atHistory clickThroughRate targetBidder targetRank targetHistory)
      clickThroughRate := by
  intro rank lastDropout bidderValue clockPrice
  by_cases htarget : rank = targetRank ∧
      lastDropout = theorem8SourcePriceHistoryLastDropout targetHistory
  · rcases htarget with ⟨rfl, rfl⟩
    simpa [Theorem8ContinuousHistoryStrategy.atHistory] using
      hbest targetBidder rank targetHistory bidderValue clockPrice
  · simpa [Theorem8ContinuousHistoryStrategy.atHistory, htarget] using
      theorem8_continuous_source_named_strategy_one_step_best_response
        clickThroughRate hclick_pos rank lastDropout bidderValue clockPrice

/-- Full-history local uniqueness: every continuous strategy satisfying the
source drop/continue payoff condition agrees with the displayed formula on the
source support at every history. -/
theorem theorem8_continuous_history_support_eq_formula_of_one_step_best_response
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (clickThroughRate : ℕ → ℝ)
    (boundary : ℕ → Theorem8SourcePriceHistory → ℝ)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank)
    (hcont : strategy.ContinuousInValuation)
    (hbest : Theorem8ContinuousHistoryOneStepBestResponse
      strategy clickThroughRate) :
    strategy.SupportEq
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate) boundary := by
  intro bidder rank history bidderValue hsupport
  let collapsed := strategy.atHistory clickThroughRate bidder rank history
  have hcollapsed_cont : collapsed.ContinuousInValuation := by
    exact theorem8_continuous_history_atHistory_continuous
      strategy clickThroughRate bidder rank history hcont
  have hcollapsed_best :
      Theorem8ContinuousSourceOneStepBestResponse
        collapsed clickThroughRate := by
    exact theorem8_continuous_history_atHistory_one_step_best_response
      strategy clickThroughRate bidder rank history hclick_pos hbest
  let collapsedBoundary : ℕ → ℝ → ℝ := fun _ _ => boundary rank history
  have heq :=
    theorem8_continuous_source_support_eq_formula_of_one_step_best_response
      collapsed clickThroughRate collapsedBoundary hclick_pos
      hcollapsed_cont hcollapsed_best rank
      (theorem8SourcePriceHistoryLastDropout history) bidderValue hsupport
  simpa [collapsed, collapsedBoundary,
    Theorem8ContinuousHistoryStrategy.atHistory,
    theorem8ContinuousHistoryStrategy,
    theorem8ContinuousSourceStrategy] using heq

/-- Bundled full-history local theorem.  It closes the source strategy-domain
shape while keeping the still-open Bayesian extensive-form bridge explicit. -/
theorem theorem8_continuous_history_local_best_response_support_unique
    (clickThroughRate : ℕ → ℝ)
    (boundary : ℕ → Theorem8SourcePriceHistory → ℝ)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank) :
    let namedStrategy :=
      theorem8ContinuousHistoryStrategy Bidder clickThroughRate
    namedStrategy.ContinuousInValuation ∧
      Theorem8ContinuousHistoryOneStepBestResponse
        namedStrategy clickThroughRate ∧
      ∀ strategy : Theorem8ContinuousHistoryStrategy Bidder,
        strategy.ContinuousInValuation →
          Theorem8ContinuousHistoryOneStepBestResponse
            strategy clickThroughRate →
          strategy.SupportEq namedStrategy boundary := by
  dsimp
  exact
    ⟨theorem8_continuous_history_strategy_continuous_in_value clickThroughRate,
      theorem8_continuous_history_named_strategy_one_step_best_response
        clickThroughRate hclick_pos,
      fun strategy hcont hbest =>
        theorem8_continuous_history_support_eq_formula_of_one_step_best_response
          strategy clickThroughRate boundary hclick_pos hcont hbest⟩

end

end PaperInterface
end EOS07GSP
