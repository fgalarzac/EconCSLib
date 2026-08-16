import GGSG19TopThree.ProofInterface

/-!
# Paper Assumptions: GGSG19 Top Three

This file records source theorem conditions used by the compact paper-facing
review surface. The assumptions are not proof certificates: they are the
strict-separation, finite-support, randomized-mechanism, and Mallows-domain
conditions appearing in the source statements.
-/

namespace GGSG19TopThree

open EconCSLib.SocialChoice.Ranking
open EconCSLib.Probability

/-- Proposition 3's K-approval pairwise row uses the ternary score-gap domain. -/
-- audit-premise: hle : pDown ≤ pUp
-- audit-premise: hscore : ∀ signal, hiScore signal - loScore signal = 1 ∨ hiScore signal - loScore signal = 0 ∨ hiScore signal - loScore signal = -1
-- audit-premise: hpUp : EconCSLib.pmfProb law (fun signal => hiScore signal - loScore signal = 1) = pUp
-- audit-premise: hpDown : EconCSLib.pmfProb law (fun signal => hiScore signal - loScore signal = -1) = pDown
-- audit-premise: hpZero : EconCSLib.pmfProb law (fun signal => hiScore signal - loScore signal = 0) = pZero
abbrev assumption_pairwise_approval_ternary_gap_domain
    {Signal : Type*} [Fintype Signal] [DecidableEq Signal]
    (law : PMF Signal) (hiScore loScore : Signal → ℝ)
    (pUp pDown pZero : ℝ) : Prop :=
  pDown ≤ pUp ∧
    (∀ signal,
      hiScore signal - loScore signal = 1 ∨
        hiScore signal - loScore signal = 0 ∨
          hiScore signal - loScore signal = -1) ∧
    EconCSLib.pmfProb law
        (fun signal => hiScore signal - loScore signal = 1) =
      pUp ∧
    EconCSLib.pmfProb law
        (fun signal => hiScore signal - loScore signal = -1) =
      pDown ∧
    EconCSLib.pmfProb law
        (fun signal => hiScore signal - loScore signal = 0) =
      pZero

/-- Randomized scoring and randomized K-approval mechanisms use probability weights. -/
-- audit-premise: hweight : ∀ rule, 0 ≤ weight rule
-- audit-premise: hsum : (∑ rule : Rule, weight rule) = 1
abbrev assumption_randomized_mechanism_probability_weights
    {Rule : Type*} [Fintype Rule] (weight : Rule → ℝ) : Prop :=
  (∀ rule, 0 ≤ weight rule) ∧
    (∑ rule : Rule, weight rule) = 1

/-- The positive-parameter Mallows corollary uses a nontrivial winner and `0 < q < 1`. -/
-- audit-premise: hDomain : 0 < W.val ∧ 0 < q ∧ q < 1
abbrev assumption_mallows_nontrivial_winner_and_parameter_domain
    {n : ℕ} (q : ℝ) (W : Candidate n) : Prop :=
  0 < W.val ∧ 0 < q ∧ q < 1

/-- The repeated-insertion algorithm uses the source's closed Mallows domain. -/
-- audit-premise: hDomain : 0 ≤ q ∧ q ≤ 1
abbrev assumption_mallows_repeated_insertion_parameter_domain (q : ℝ) : Prop :=
  0 ≤ q ∧ q ≤ 1

/-- Randomized Mallows K-approval families range over nontrivial proper cutoffs. -/
-- audit-premise: hK_pos : ∀ rule, 0 < K rule
-- audit-premise: hK_lt : ∀ rule, K rule < n + 2
abbrev assumption_nontrivial_k_approval_cutoffs
    {n : ℕ} {Rule : Type*} [Fintype Rule] (K : Rule → ℕ) : Prop :=
  (∀ rule, 0 < K rule) ∧
    (∀ rule, K rule < n + 2)

end GGSG19TopThree
