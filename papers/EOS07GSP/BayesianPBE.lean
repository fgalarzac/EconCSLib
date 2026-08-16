import EOS07GSP.ContinuousHistory
import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# EOS07 Theorem 8: continuous type laws and history-conditioned beliefs

This file starts the explicit Bayesian layer omitted by the older payoff-local
checker.  It models the source's continuous value distribution by a probability
measure with a continuous, everywhere-positive density on `(0,∞)`.  It also
defines the event that a bidder has survived every public dropout in a full
price history, and gives the Bayes posterior obtained by conditioning the type
law on that event.

The belief construction is deliberately independent of equilibrium labels:
`BayesConsistent` below is an actual conditional-measure equality at every
positive-probability history event.  Zero-probability histories retain an
arbitrary probability belief, as standard PBE consistency permits.  A later
section adds continuation utilities and sequential rationality; no theorem in
this file identifies those notions with the payoff-local predicate.
-/

namespace EOS07GSP
namespace PaperInterface

noncomputable section

open MeasureTheory ProbabilityTheory Set

universe u

variable {Bidder : Type u}

/-! ## The source continuous type law -/

/-- The value law assumed in EOS Theorem 8.  `measure_eq_withDensity` makes the
relationship between the probability measure and the displayed density
mathematical data rather than an informal label. -/
structure Theorem8ContinuousValueLaw where
  density : ℝ → ℝ
  measure : Measure ℝ
  density_continuous : Continuous density
  density_nonnegative : ∀ value, 0 ≤ density value
  density_zero_of_neg : ∀ value, value < 0 → density value = 0
  density_pos_of_pos : ∀ value, 0 < value → 0 < density value
  measure_eq_withDensity :
    measure = volume.withDensity (fun value => ENNReal.ofReal (density value))
  measure_isProbability : IsProbabilityMeasure measure

instance (law : Theorem8ContinuousValueLaw) :
    IsProbabilityMeasure law.measure :=
  law.measure_isProbability

/-- Every nonempty positive-value interval has positive probability under the
source density assumption.  This is the reusable full-support fact used by the
positive-probability deviations in the paper's Step 1 and Step 2 arguments. -/
theorem Theorem8ContinuousValueLaw.measure_Ioc_pos
    (law : Theorem8ContinuousValueLaw) {lower upper : ℝ}
    (hlower_nonneg : 0 ≤ lower) (hlower_lt_upper : lower < upper) :
    0 < law.measure (Ioc lower upper) := by
  rw [law.measure_eq_withDensity, withDensity_apply _ measurableSet_Ioc]
  have hinter : IntervalIntegrable law.density volume lower upper :=
    law.density_continuous.intervalIntegrable lower upper
  have hinter_pos : 0 < ∫ value in lower..upper, law.density value := by
    exact intervalIntegral.intervalIntegral_pos_of_pos_on hinter
      (fun value hvalue =>
        law.density_pos_of_pos value (lt_of_le_of_lt hlower_nonneg hvalue.1))
      hlower_lt_upper
  have hintegrableOn : IntegrableOn law.density (Ioc lower upper) volume := by
    rw [← uIoc_of_le hlower_lt_upper.le]
    exact (intervalIntegrable_iff.mp hinter)
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Ioc lower upper)] law.density :=
    Filter.Eventually.of_forall (fun value => law.density_nonnegative value)
  rw [← ofReal_integral_eq_lintegral_ofReal hintegrableOn hnonneg]
  apply ENNReal.ofReal_pos.mpr
  rwa [← intervalIntegral.integral_of_le hlower_lt_upper.le]

/-- In particular, every nonnegative survival cutoff has nonzero upper-tail
probability. -/
theorem Theorem8ContinuousValueLaw.measure_Ici_ne_zero
    (law : Theorem8ContinuousValueLaw) {lower : ℝ}
    (hlower_nonneg : 0 ≤ lower) :
    law.measure (Ici lower) ≠ 0 := by
  have hinterval : 0 < law.measure (Ioc lower (lower + 1)) :=
    law.measure_Ioc_pos hlower_nonneg (by linarith)
  have hsub : Ioc lower (lower + 1) ⊆ Ici lower := fun _ h => h.1.le
  exact ne_of_gt (hinterval.trans_le (measure_mono hsub))

/-- The ordinary conditional value law above a nonnegative survival cutoff. -/
def Theorem8ContinuousValueLaw.survivalPosterior
    (law : Theorem8ContinuousValueLaw) (lower : ℝ) : Measure ℝ :=
  law.measure[| Ici lower]

instance Theorem8ContinuousValueLaw.survivalPosterior_isProbability
    (law : Theorem8ContinuousValueLaw) (lower : ℝ) [Fact (0 ≤ lower)] :
    IsProbabilityMeasure (law.survivalPosterior lower) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure
  exact law.measure_Ici_ne_zero (Fact.out : 0 ≤ lower)

/-! ## Full public-history survival events -/

/-- `SurvivesHistory strategy bidder value rank history` says that the bidder
did not drop at any of the public prices in `history`.  Histories are newest
first.  At the newest recorded price the preceding decision node had index
`rank + 1` and the older tail as its then-current history. -/
def Theorem8SurvivesHistory
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (bidder : Bidder) (value : ℝ) :
    Theorem8SourcePriceHistory → ℕ → Prop
  | [], _rank => True
  | price :: olderHistory, rank =>
      Theorem8SurvivesHistory strategy bidder value olderHistory (rank + 1) ∧
        price ≤ strategy.dropoutPrice bidder (rank + 1) olderHistory value

@[simp]
theorem theorem8_survives_history_nil
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (bidder : Bidder) (value : ℝ) (rank : ℕ) :
    Theorem8SurvivesHistory strategy bidder value [] rank := by
  simp only [Theorem8SurvivesHistory]

@[simp]
theorem theorem8_survives_history_cons
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (bidder : Bidder) (value price : ℝ) (rank : ℕ)
    (olderHistory : Theorem8SourcePriceHistory) :
    Theorem8SurvivesHistory strategy bidder value
        (price :: olderHistory) rank ↔
      Theorem8SurvivesHistory strategy bidder value olderHistory (rank + 1) ∧
        price ≤ strategy.dropoutPrice bidder (rank + 1) olderHistory value := by
  rfl

/-- The source-supported type event at a public history. -/
def theorem8HistorySurvivalSet
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (bidder : Bidder) (rank : ℕ)
    (history : Theorem8SourcePriceHistory) : Set ℝ :=
  {value | 0 ≤ value ∧
    Theorem8SurvivesHistory strategy bidder value history rank}

/-- Continuity in own value makes every finite-history survival event Borel
measurable, so ordinary conditional probability is available without a hidden
measurability certificate. -/
theorem theorem8_history_survival_set_measurable
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (hcontinuous : strategy.ContinuousInValuation)
    (bidder : Bidder) (rank : ℕ)
    (history : Theorem8SourcePriceHistory) :
    MeasurableSet (theorem8HistorySurvivalSet strategy bidder rank history) := by
  unfold theorem8HistorySurvivalSet
  apply measurableSet_Ici.inter
  induction history generalizing rank with
  | nil =>
      simpa only [theorem8_survives_history_nil, setOf_true] using
        (MeasurableSet.univ : MeasurableSet (Set.univ : Set ℝ))
  | cons price olderHistory ih =>
      simp only [theorem8_survives_history_cons]
      exact (ih (rank + 1)).inter
        (measurableSet_le measurable_const
          (hcontinuous bidder (rank + 1) olderHistory).measurable)

/-! ## Belief systems and Bayes consistency -/

/-- A marginal belief for each still-active bidder, public rank, and public
price history.  The probability-measure field prevents a zero measure from
being passed off as an off-path belief. -/
structure Theorem8HistoryBeliefSystem (Bidder : Type u) where
  posterior : Bidder → ℕ → Theorem8SourcePriceHistory → Measure ℝ
  posterior_isProbability :
    ∀ bidder rank history,
      IsProbabilityMeasure (posterior bidder rank history)

/-- Bayes consistency at every history whose survival event has positive prior
probability.  The posterior is the source type law conditioned on the complete
strategy-generated survival event, not merely on the last dropout price. -/
def Theorem8HistoryBeliefSystem.BayesConsistent
    (belief : Theorem8HistoryBeliefSystem Bidder)
    (law : Theorem8ContinuousValueLaw)
    (strategy : Theorem8ContinuousHistoryStrategy Bidder) : Prop :=
  ∀ bidder rank history,
    law.measure (theorem8HistorySurvivalSet strategy bidder rank history) ≠ 0 →
      belief.posterior bidder rank history =
        law.measure[| theorem8HistorySurvivalSet strategy bidder rank history]

/-- Canonical Bayesian beliefs for a continuous strategy.  At a null history
event the prior is used as a total off-path probability belief; positive-mass
history events use ordinary conditional probability. -/
def theorem8CanonicalHistoryBeliefSystem
    (law : Theorem8ContinuousValueLaw)
    (strategy : Theorem8ContinuousHistoryStrategy Bidder) :
    Theorem8HistoryBeliefSystem Bidder where
  posterior := fun bidder rank history =>
    if law.measure
        (theorem8HistorySurvivalSet strategy bidder rank history) = 0 then
      law.measure
    else
      law.measure[| theorem8HistorySurvivalSet strategy bidder rank history]
  posterior_isProbability := by
    intro bidder rank history
    split
    · exact law.measure_isProbability
    · apply ProbabilityTheory.cond_isProbabilityMeasure
      assumption

/-- The canonical history belief system satisfies the explicit Bayes rule. -/
theorem theorem8_canonical_history_belief_bayes_consistent
    (law : Theorem8ContinuousValueLaw)
    (strategy : Theorem8ContinuousHistoryStrategy Bidder) :
    (theorem8CanonicalHistoryBeliefSystem law strategy).BayesConsistent
      law strategy := by
  intro bidder rank history hpositive
  simp [theorem8CanonicalHistoryBeliefSystem, hpositive]

/-! ## Legal current-clock actions and the source's implicit history domain -/

namespace Theorem8ContinuousHistoryStrategy

/-- A dropout-price strategy never names a price earlier than the current
clock.  This is the basic feasibility requirement for a future stopping
action. -/
def ClockLegal (strategy : Theorem8ContinuousHistoryStrategy Bidder) : Prop :=
  ∀ bidder rank history value,
    theorem8SourcePriceHistoryLastDropout history ≤
      strategy.dropoutPrice bidder rank history value

/-- The weaker, source-reachable legality condition: the bidder's value is at
least the last dropout price.  This is the domain actually used in the source
appendix through its `s >= s_min >= b_(k+1)` invariant. -/
def ClockLegalOnFeasibleHistory
    (strategy : Theorem8ContinuousHistoryStrategy Bidder) : Prop :=
  ∀ bidder rank history value,
    theorem8SourcePriceHistoryLastDropout history ≤ value →
      theorem8SourcePriceHistoryLastDropout history ≤
        strategy.dropoutPrice bidder rank history value

end Theorem8ContinuousHistoryStrategy

/-- The displayed EOS formula is a legal future dropout price throughout the
source-reachable domain. -/
theorem theorem8_named_history_strategy_clock_legal_on_feasible_history
    (clickThroughRate : ℕ → ℝ)
    (hclick_pos : ∀ rank, 0 < clickThroughRate rank)
    (hclick_mono : ∀ rank,
      clickThroughRate (rank + 1) ≤ clickThroughRate rank) :
    Theorem8ContinuousHistoryStrategy.ClockLegalOnFeasibleHistory
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate) := by
  intro bidder rank history value hfeasible
  exact
    paper_theorem8_generalized_english_indifference_price_lastDropout_le
      (hclick_pos rank) (hclick_mono rank) hfeasible

/-- Below the current clock, the displayed formula names a price strictly in
the past under the source's strict click-rate condition. -/
theorem theorem8_named_history_strategy_dropout_lt_current_clock_of_value_lt
    (clickThroughRate : ℕ → ℝ) (bidder : Bidder) (rank : ℕ)
    (history : Theorem8SourcePriceHistory) (value : ℝ)
    (hclick_pos : 0 < clickThroughRate rank)
    (hclick_strict : clickThroughRate (rank + 1) < clickThroughRate rank)
    (hvalue_lt : value < theorem8SourcePriceHistoryLastDropout history) :
    (theorem8ContinuousHistoryStrategy Bidder clickThroughRate).dropoutPrice
        bidder rank history value <
      theorem8SourcePriceHistoryLastDropout history := by
  let lastDropout := theorem8SourcePriceHistoryLastDropout history
  have hstrict :=
    paper_theorem8_generalized_english_indifference_price_strict_mono_value
      (alphaAbove := clickThroughRate rank)
      (alphaCurrent := clickThroughRate (rank + 1))
      (lastDropout := lastDropout)
      hclick_pos hclick_strict hvalue_lt
  have hself :
      paper_theorem8_generalized_english_indifference_price
          (clickThroughRate rank) (clickThroughRate (rank + 1))
          lastDropout lastDropout = lastDropout := by
    unfold paper_theorem8_generalized_english_indifference_price
    ring
  simpa [theorem8ContinuousHistoryStrategy,
    theorem8ContinuousSourceDropoutPrice,
    theorem8GeneralizedEnglishDropoutPrice, lastDropout, hself] using hstrict

/-- Consequently, the literal all-type/all-history displayed formula is not a
globally legal stopping strategy.  The theorem needs the feasible-survival
domain made explicit (or an immediate-drop-at-current-clock convention). -/
theorem theorem8_named_history_strategy_not_globally_clock_legal
    (clickThroughRate : ℕ → ℝ) (bidder : Bidder) (rank : ℕ)
    (hclick_pos : 0 < clickThroughRate rank)
    (hclick_strict : clickThroughRate (rank + 1) < clickThroughRate rank) :
    ¬ Theorem8ContinuousHistoryStrategy.ClockLegal
      (theorem8ContinuousHistoryStrategy Bidder clickThroughRate) := by
  intro hlegal
  have hpast :=
    theorem8_named_history_strategy_dropout_lt_current_clock_of_value_lt
      clickThroughRate bidder rank [1] 0 hclick_pos hclick_strict (by norm_num)
  have hfuture := hlegal bidder rank [1] 0
  norm_num [theorem8SourcePriceHistoryLastDropout] at hpast hfuture
  linarith

/-! ## The finite generalized-English continuation game -/

section FiniteGame

variable [Fintype Bidder] [DecidableEq Bidder]

/-- Operational stopping price.  A threshold in the past means immediate
dropout at the stopped current clock, matching footnote 18's rule that the
clock is stopped while additional bidders are allowed to drop. -/
def theorem8EffectiveDropoutPrice
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (bidder : Bidder) (rank : ℕ)
    (history : Theorem8SourcePriceHistory) : ℝ :=
  max (theorem8SourcePriceHistoryLastDropout history)
    (strategy.dropoutPrice bidder rank history (values bidder))

/-- The next stopped-clock price among a nonempty active set. -/
def theorem8MinimumDropoutPrice
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (remaining : Finset Bidder)
    (hremaining : remaining.Nonempty) (rank : ℕ)
    (history : Theorem8SourcePriceHistory) : ℝ :=
  (remaining.image fun bidder =>
    theorem8EffectiveDropoutPrice strategy values bidder rank history).min'
      (Finset.image_nonempty.mpr hremaining)

/-- Bidders who request dropout at the next stopped-clock price.  One of this
finite nonempty set is selected uniformly, after which the survivors may again
drop at the same stopped price. -/
def theorem8FirstDropperSet
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (remaining : Finset Bidder)
    (hremaining : remaining.Nonempty) (rank : ℕ)
    (history : Theorem8SourcePriceHistory) : Finset Bidder :=
  remaining.filter fun bidder =>
    theorem8EffectiveDropoutPrice strategy values bidder rank history =
      theorem8MinimumDropoutPrice strategy values remaining hremaining rank history

theorem theorem8_first_dropper_set_nonempty
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (remaining : Finset Bidder)
    (hremaining : remaining.Nonempty) (rank : ℕ)
    (history : Theorem8SourcePriceHistory) :
    (theorem8FirstDropperSet strategy values remaining hremaining rank history).Nonempty := by
  let prices := remaining.image fun bidder =>
    theorem8EffectiveDropoutPrice strategy values bidder rank history
  have hprices : prices.Nonempty := Finset.image_nonempty.mpr hremaining
  have hmin_mem : prices.min' hprices ∈ prices := Finset.min'_mem prices hprices
  rcases Finset.mem_image.mp hmin_mem with ⟨bidder, hbidder, hprice⟩
  refine ⟨bidder, Finset.mem_filter.mpr ⟨hbidder, ?_⟩⟩
  simpa [theorem8MinimumDropoutPrice, prices] using hprice

/-- Expected realized payoff over the source's uniform random tie-breaking,
for a fixed profile of bidder values.  `rank` is the zero-based higher slot in
the current comparison, so a bidder dropping now receives slot `rank+1`; when
`rank=0`, a surviving bidder receives the top slot after the next dropout.

The recursion recomputes thresholds after each selected dropout and prepends
the stopped price to the full history.  It therefore implements the sequential
same-price tie rule from source footnote 18 rather than imposing a one-shot
tie ordering. -/
def theorem8RealizedContinuationUtility
    (clickThroughRate : ℕ → ℝ)
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (values : Bidder → ℝ) (focal : Bidder) :
    ℕ → Finset Bidder → Theorem8SourcePriceHistory → ℝ
  | 0, remaining, history =>
      if hremaining : remaining.Nonempty then
        let nextPrice := theorem8MinimumDropoutPrice
          strategy values remaining hremaining 0 history
        let firstDroppers := theorem8FirstDropperSet
          strategy values remaining hremaining 0 history
        (∑ dropper ∈ firstDroppers,
          if dropper = focal then
            clickThroughRate 1 *
              (values focal - theorem8SourcePriceHistoryLastDropout history)
          else
            clickThroughRate 0 * (values focal - nextPrice)) /
          (firstDroppers.card : ℝ)
      else 0
  | rank + 1, remaining, history =>
      if hremaining : remaining.Nonempty then
        let nextPrice := theorem8MinimumDropoutPrice
          strategy values remaining hremaining (rank + 1) history
        let firstDroppers := theorem8FirstDropperSet
          strategy values remaining hremaining (rank + 1) history
        (∑ dropper ∈ firstDroppers,
          if dropper = focal then
            clickThroughRate (rank + 2) *
              (values focal - theorem8SourcePriceHistoryLastDropout history)
          else
            theorem8RealizedContinuationUtility clickThroughRate strategy
              values focal rank (remaining.erase dropper)
              (nextPrice :: history)) /
          (firstDroppers.card : ℝ)
      else 0

/-- Replace one bidder's entire continuation plan while leaving every other
bidder's strategy unchanged.  Sequential rationality below quantifies over
these full continuation deviations, not merely over the current threshold. -/
def Theorem8ContinuousHistoryStrategy.replaceBidder
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (focal : Bidder)
    (deviation : ℕ → Theorem8SourcePriceHistory → ℝ → ℝ) :
    Theorem8ContinuousHistoryStrategy Bidder where
  dropoutPrice := fun bidder rank history value =>
    if bidder = focal then deviation rank history value
    else strategy.dropoutPrice bidder rank history value

@[simp]
theorem theorem8_replace_bidder_self
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (focal : Bidder)
    (deviation : ℕ → Theorem8SourcePriceHistory → ℝ → ℝ)
    (rank : ℕ) (history : Theorem8SourcePriceHistory) (value : ℝ) :
    (strategy.replaceBidder focal deviation).dropoutPrice
      focal rank history value = deviation rank history value := by
  simp [Theorem8ContinuousHistoryStrategy.replaceBidder]

@[simp]
theorem theorem8_replace_bidder_other
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (focal other : Bidder) (hother : other ≠ focal)
    (deviation : ℕ → Theorem8SourcePriceHistory → ℝ → ℝ)
    (rank : ℕ) (history : Theorem8SourcePriceHistory) (value : ℝ) :
    (strategy.replaceBidder focal deviation).dropoutPrice
      other rank history value =
        strategy.dropoutPrice other rank history value := by
  simp [Theorem8ContinuousHistoryStrategy.replaceBidder, hother]

/-! ## Joint beliefs, arbitrary-continuation rationality, and PBE -/

/-- The focal bidder's coordinate is fixed at the known own value; every other
coordinate uses the public-history posterior. -/
def theorem8ProfileMarginal
    (belief : Theorem8HistoryBeliefSystem Bidder)
    (focal : Bidder) (ownValue : ℝ) (rank : ℕ)
    (history : Theorem8SourcePriceHistory) (bidder : Bidder) : Measure ℝ :=
  if bidder = focal then Measure.dirac ownValue
  else belief.posterior bidder rank history

instance theorem8ProfileMarginal_isProbability
    (belief : Theorem8HistoryBeliefSystem Bidder)
    (focal : Bidder) (ownValue : ℝ) (rank : ℕ)
    (history : Theorem8SourcePriceHistory) (bidder : Bidder) :
    IsProbabilityMeasure
      (theorem8ProfileMarginal belief focal ownValue rank history bidder) := by
  unfold theorem8ProfileMarginal
  split
  · infer_instance
  · exact belief.posterior_isProbability bidder rank history

/-- The source independent-private-values posterior profile.  Conditional on
the public survival event, the remaining bidders' type restrictions are
coordinatewise, so the product of the Bayes marginals is the joint posterior. -/
def theorem8JointHistoryBelief
    (belief : Theorem8HistoryBeliefSystem Bidder)
    (focal : Bidder) (ownValue : ℝ) (rank : ℕ)
    (history : Theorem8SourcePriceHistory) : Measure (Bidder → ℝ) :=
  Measure.pi
    (theorem8ProfileMarginal belief focal ownValue rank history)

instance theorem8JointHistoryBelief_isProbability
    (belief : Theorem8HistoryBeliefSystem Bidder)
    (focal : Bidder) (ownValue : ℝ) (rank : ℕ)
    (history : Theorem8SourcePriceHistory) :
    IsProbabilityMeasure
      (theorem8JointHistoryBelief belief focal ownValue rank history) := by
  unfold theorem8JointHistoryBelief
  infer_instance

/-- Expected continuation utility in the actual finite generalized-English
game, under the product posterior at the current full public history. -/
def theorem8ExpectedContinuationUtility
    (clickThroughRate : ℕ → ℝ)
    (belief : Theorem8HistoryBeliefSystem Bidder)
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (focal : Bidder) (ownValue : ℝ) (rank : ℕ)
    (remaining : Finset Bidder)
    (history : Theorem8SourcePriceHistory) : ℝ :=
  ∫ values,
    theorem8RealizedContinuationUtility clickThroughRate strategy
      values focal rank remaining history
    ∂theorem8JointHistoryBelief belief focal ownValue rank history

/-- Integrability of the continuation payoff at one information set.  This is
kept explicit because the source permits unbounded value distributions and
does not assume a finite first moment for arbitrary loss-making deviations. -/
def Theorem8ContinuationUtilityIntegrable
    (clickThroughRate : ℕ → ℝ)
    (belief : Theorem8HistoryBeliefSystem Bidder)
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (focal : Bidder) (ownValue : ℝ) (rank : ℕ)
    (remaining : Finset Bidder)
    (history : Theorem8SourcePriceHistory) : Prop :=
  Integrable
    (fun values =>
      theorem8RealizedContinuationUtility clickThroughRate strategy
        values focal rank remaining history)
    (theorem8JointHistoryBelief belief focal ownValue rank history)

/-- Sequential rationality against arbitrary full continuation plans.  The
comparison is made at every feasible information set for every active bidder;
the deviating function changes that bidder's thresholds at all current and
future histories.  Only deviations with a well-defined finite expectation are
listed, while the equilibrium continuation itself is required integrable. -/
def Theorem8HistorySequentiallyRational
    (clickThroughRate : ℕ → ℝ)
    (belief : Theorem8HistoryBeliefSystem Bidder)
    (strategy : Theorem8ContinuousHistoryStrategy Bidder) : Prop :=
  ∀ focal rank history ownValue remaining,
    focal ∈ remaining →
    remaining.card = rank + 2 →
    0 ≤ ownValue →
    Theorem8SurvivesHistory strategy focal ownValue history rank →
    theorem8SourcePriceHistoryLastDropout history ≤ ownValue →
    Theorem8ContinuationUtilityIntegrable clickThroughRate belief strategy
      focal ownValue rank remaining history ∧
      ∀ deviation : ℕ → Theorem8SourcePriceHistory → ℝ → ℝ,
        Theorem8ContinuationUtilityIntegrable clickThroughRate belief
            (strategy.replaceBidder focal deviation)
            focal ownValue rank remaining history →
          theorem8ExpectedContinuationUtility clickThroughRate belief
              (strategy.replaceBidder focal deviation)
              focal ownValue rank remaining history ≤
            theorem8ExpectedContinuationUtility clickThroughRate belief
              strategy focal ownValue rank remaining history

/-- Explicit perfect Bayesian equilibrium for the finite generalized-English
game: a continuous and clock-feasible strategy profile, a probability belief
system satisfying Bayes' rule at every positive-mass full-history event, and
sequential rationality against arbitrary continuation deviations. -/
def Theorem8HistoryPerfectBayesianEquilibrium
    (law : Theorem8ContinuousValueLaw)
    (clickThroughRate : ℕ → ℝ)
    (strategy : Theorem8ContinuousHistoryStrategy Bidder) : Prop :=
  strategy.ContinuousInValuation ∧
    strategy.ClockLegalOnFeasibleHistory ∧
      ∃ belief : Theorem8HistoryBeliefSystem Bidder,
        belief.BayesConsistent law strategy ∧
          Theorem8HistorySequentiallyRational
            clickThroughRate belief strategy

/-- Belief consistency is constructively available for every continuous
strategy.  The remaining mathematical content of PBE is therefore the actual
continuation-utility sequential-rationality theorem. -/
theorem theorem8_history_pbe_of_canonical_belief_and_sequential_rationality
    (law : Theorem8ContinuousValueLaw)
    (clickThroughRate : ℕ → ℝ)
    (strategy : Theorem8ContinuousHistoryStrategy Bidder)
    (hcontinuous : strategy.ContinuousInValuation)
    (hlegal : strategy.ClockLegalOnFeasibleHistory)
    (hrational : Theorem8HistorySequentiallyRational clickThroughRate
      (theorem8CanonicalHistoryBeliefSystem law strategy) strategy) :
    Theorem8HistoryPerfectBayesianEquilibrium
      law clickThroughRate strategy := by
  exact ⟨hcontinuous, hlegal,
    theorem8CanonicalHistoryBeliefSystem law strategy,
    theorem8_canonical_history_belief_bayes_consistent law strategy,
    hrational⟩

/-! ## Last-stage arbitrary-deviation theorem -/

/-- Realized continuation utility when two bidders remain.  A lower threshold
drops first into the lower slot; a higher threshold wins the top slot at the
other bidder's price; equality is averaged by the source random tie rule. -/
def theorem8TwoBidderRealizedUtility
    (alphaAbove alphaCurrent lastDropout ownValue
      ownPrice otherPrice : ℝ) : ℝ :=
  if ownPrice < otherPrice then
    alphaCurrent * (ownValue - lastDropout)
  else if otherPrice < ownPrice then
    alphaAbove * (ownValue - otherPrice)
  else
    (alphaCurrent * (ownValue - lastDropout) +
      alphaAbove * (ownValue - otherPrice)) / 2

/-- Every two-bidder stopping choice yields at most the better of dropping now
and winning at the opponent's price. -/
theorem theorem8_two_bidder_realized_utility_le_max
    (alphaAbove alphaCurrent lastDropout ownValue ownPrice otherPrice : ℝ) :
    theorem8TwoBidderRealizedUtility alphaAbove alphaCurrent lastDropout
        ownValue ownPrice otherPrice ≤
      max
        (alphaCurrent * (ownValue - lastDropout))
        (alphaAbove * (ownValue - otherPrice)) := by
  unfold theorem8TwoBidderRealizedUtility
  split
  · exact le_max_left _ _
  · split
    · exact le_max_right _ _
    · have hdrop := le_max_left
        (alphaCurrent * (ownValue - lastDropout))
        (alphaAbove * (ownValue - otherPrice))
      have hwin := le_max_right
        (alphaCurrent * (ownValue - lastDropout))
        (alphaAbove * (ownValue - otherPrice))
      linarith

/-- At the final comparison, the EOS indifference price is a best response to
every realized opponent stopping price, including a tie.  This is a genuine
arbitrary-deviation result, not the payoff-local predicate by definition. -/
theorem theorem8_two_bidder_named_price_best_response
    {alphaAbove alphaCurrent lastDropout ownValue otherPrice
      deviationPrice : ℝ}
    (halphaAbove_pos : 0 < alphaAbove) :
    theorem8TwoBidderRealizedUtility alphaAbove alphaCurrent lastDropout
        ownValue deviationPrice otherPrice ≤
      theorem8TwoBidderRealizedUtility alphaAbove alphaCurrent lastDropout
        ownValue
        (paper_theorem8_generalized_english_indifference_price
          alphaAbove alphaCurrent lastDropout ownValue)
        otherPrice := by
  let q := paper_theorem8_generalized_english_indifference_price
    alphaAbove alphaCurrent lastDropout ownValue
  let dropPayoff := alphaCurrent * (ownValue - lastDropout)
  let winPayoff := alphaAbove * (ownValue - otherPrice)
  have hindiff : alphaAbove * (ownValue - q) = dropPayoff := by
    simpa [q, dropPayoff] using
      paper_theorem8_generalized_english_indifference_price_eq
        (alphaCurrent := alphaCurrent) (lastDropout := lastDropout)
        (value := ownValue) (ne_of_gt halphaAbove_pos)
  have hdeviation := theorem8_two_bidder_realized_utility_le_max
    alphaAbove alphaCurrent lastDropout ownValue deviationPrice otherPrice
  rcases lt_trichotomy q otherPrice with hq_lt | hq_eq | hother_lt
  · have hwin_lt : winPayoff < dropPayoff := by
      dsimp [winPayoff]
      rw [← hindiff]
      nlinarith
    have hnamed :
        theorem8TwoBidderRealizedUtility alphaAbove alphaCurrent lastDropout
          ownValue q otherPrice = dropPayoff := by
      simp [theorem8TwoBidderRealizedUtility, hq_lt, dropPayoff]
    calc
      theorem8TwoBidderRealizedUtility alphaAbove alphaCurrent lastDropout
          ownValue deviationPrice otherPrice ≤ max dropPayoff winPayoff :=
        hdeviation
      _ = dropPayoff := max_eq_left hwin_lt.le
      _ = theorem8TwoBidderRealizedUtility alphaAbove alphaCurrent lastDropout
          ownValue q otherPrice := hnamed.symm
  · have hpay_eq : winPayoff = dropPayoff := by
      simpa [winPayoff, hq_eq] using hindiff
    have hpay_raw :
        alphaAbove * (ownValue - otherPrice) =
          alphaCurrent * (ownValue - lastDropout) := by
      simpa [winPayoff, dropPayoff] using hpay_eq
    have hnamed :
        theorem8TwoBidderRealizedUtility alphaAbove alphaCurrent lastDropout
          ownValue q otherPrice = dropPayoff := by
      simp [theorem8TwoBidderRealizedUtility, hq_eq, dropPayoff, hpay_raw]
    calc
      theorem8TwoBidderRealizedUtility alphaAbove alphaCurrent lastDropout
          ownValue deviationPrice otherPrice ≤ max dropPayoff winPayoff :=
        hdeviation
      _ = dropPayoff := by rw [hpay_eq, max_self]
      _ = theorem8TwoBidderRealizedUtility alphaAbove alphaCurrent lastDropout
          ownValue q otherPrice := hnamed.symm
  · have hdrop_lt : dropPayoff < winPayoff := by
      dsimp [winPayoff]
      rw [← hindiff]
      nlinarith
    have hnamed :
        theorem8TwoBidderRealizedUtility alphaAbove alphaCurrent lastDropout
          ownValue q otherPrice = winPayoff := by
      simp [theorem8TwoBidderRealizedUtility, hother_lt, hother_lt.not_gt,
        winPayoff]
    calc
      theorem8TwoBidderRealizedUtility alphaAbove alphaCurrent lastDropout
          ownValue deviationPrice otherPrice ≤ max dropPayoff winPayoff :=
        hdeviation
      _ = winPayoff := max_eq_right hdrop_lt.le
      _ = theorem8TwoBidderRealizedUtility alphaAbove alphaCurrent lastDropout
          ownValue q otherPrice := hnamed.symm

end FiniteGame

end

end PaperInterface
end EOS07GSP
