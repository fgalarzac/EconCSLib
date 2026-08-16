import KR21Monoculture.SignedWelfareSource

namespace KR21Monoculture
namespace Model

/-!
# Pure-equilibrium and social-optimum layer for the signed-welfare observation

The KR21 model has two labeled firms and two available strategies.  This module
makes the game-theoretic content of the signed-welfare observation explicit:
`labeledFirmRandomOrderExpectedPayoff` is the payoff of one labeled firm after
uniformly randomizing which firm moves first; `PureNashEquilibrium` ranges only
over the four pure profiles; and `finitePureSocialWelfareOptimum` is the maximum
of the welfare of those four profiles.  Nothing here makes a mixed-equilibrium
claim.
-/

/-- The expected payoff of the labeled firm using `self` against a labeled
opponent using `other`, when the two arrival orders are equally likely.  This is
definitionally the established model payoff. -/
noncomputable def labeledFirmRandomOrderExpectedPayoff {n : ℕ} (M : Model n)
    (self other : Strategy) : ℝ :=
  payoffAgainst M self other

/-- The game-facing name is exactly the established payoff construction. -/
theorem labeledFirmRandomOrderExpectedPayoff_eq_payoffAgainst {n : ℕ}
    (M : Model n) (self other : Strategy) :
    labeledFirmRandomOrderExpectedPayoff M self other = payoffAgainst M self other :=
  rfl

/-- A pure Nash equilibrium of the source's finite two-firm game.  Each labeled
firm has no profitable unilateral switch between the human and algorithmic
ranking strategies. -/
noncomputable def PureNashEquilibrium {n : ℕ} (M : Model n)
    (first second : Strategy) : Prop :=
  (∀ deviation : Strategy,
    labeledFirmRandomOrderExpectedPayoff M deviation second ≤
      labeledFirmRandomOrderExpectedPayoff M first second) ∧
  (∀ deviation : Strategy,
    labeledFirmRandomOrderExpectedPayoff M deviation first ≤
      labeledFirmRandomOrderExpectedPayoff M second first)

/-- A specified pure profile is the unique pure Nash equilibrium. -/
noncomputable def UniquePureNashEquilibrium {n : ℕ} (M : Model n)
    (first second : Strategy) : Prop :=
  PureNashEquilibrium M first second ∧
    ∀ otherFirst otherSecond,
      PureNashEquilibrium M otherFirst otherSecond →
        otherFirst = first ∧ otherSecond = second

/-- The all-algorithm profile is a pure Nash equilibrium under the model's
strict-dominance certificate. -/
theorem algorithm_algorithm_pureNashEquilibrium_of_algorithmStrictlyDominant
    {n : ℕ} (M : Model n) (hdominant : AlgorithmStrictlyDominant M) :
    PureNashEquilibrium M Strategy.algorithm Strategy.algorithm := by
  rcases (algorithmStrictlyDominant_iff_payoffAgainst M).1 hdominant with
    ⟨hAgainstAlgorithm, hAgainstHuman⟩
  constructor
  · intro deviation
    cases deviation with
    | algorithm => exact le_rfl
    | human =>
      simpa [labeledFirmRandomOrderExpectedPayoff] using le_of_lt hAgainstAlgorithm
  · intro deviation
    cases deviation with
    | algorithm => exact le_rfl
    | human =>
      simpa [labeledFirmRandomOrderExpectedPayoff] using le_of_lt hAgainstAlgorithm

/-- Strict algorithmic dominance makes the all-algorithm profile the unique
pure Nash equilibrium.  The proof checks all four pure profiles, so it does not
silently identify the two labeled firms or assert anything about mixed play. -/
theorem algorithm_algorithm_uniquePureNashEquilibrium_of_algorithmStrictlyDominant
    {n : ℕ} (M : Model n) (hdominant : AlgorithmStrictlyDominant M) :
    UniquePureNashEquilibrium M Strategy.algorithm Strategy.algorithm := by
  rcases (algorithmStrictlyDominant_iff_payoffAgainst M).1 hdominant with
    ⟨hAgainstAlgorithm, hAgainstHuman⟩
  refine ⟨algorithm_algorithm_pureNashEquilibrium_of_algorithmStrictlyDominant
    M hdominant, ?_⟩
  intro otherFirst otherSecond hne
  rcases hne with ⟨hfirst, hsecond⟩
  cases otherFirst <;> cases otherSecond
  · exact ⟨rfl, rfl⟩
  · exfalso
    exact (not_le_of_gt hAgainstAlgorithm)
      (by simpa [labeledFirmRandomOrderExpectedPayoff] using hsecond Strategy.algorithm)
  · exfalso
    exact (not_le_of_gt hAgainstAlgorithm)
      (by simpa [labeledFirmRandomOrderExpectedPayoff] using hfirst Strategy.algorithm)
  · exfalso
    exact (not_le_of_gt hAgainstHuman)
      (by simpa [labeledFirmRandomOrderExpectedPayoff] using hfirst Strategy.algorithm)

/-- Social welfare at one of the source game's four labeled pure profiles. -/
noncomputable def pureProfileSocialWelfare {n : ℕ} (M : Model n)
    (first second : Strategy) : ℝ :=
  welfareRandomOrder M first second

/-- The finite pure-profile social optimum: the maximum welfare of `AA`, `AH`,
`HA`, and `HH`.  The profile need not be unique, and this definition does not
claim that `HH` itself attains the maximum. -/
noncomputable def finitePureSocialWelfareOptimum {n : ℕ} (M : Model n) : ℝ :=
  max
    (max (pureProfileSocialWelfare M Strategy.algorithm Strategy.algorithm)
      (pureProfileSocialWelfare M Strategy.algorithm Strategy.human))
    (max (pureProfileSocialWelfare M Strategy.human Strategy.algorithm)
      (pureProfileSocialWelfare M Strategy.human Strategy.human))

/-- Every pure profile's social welfare is bounded by the explicit finite
maximum. -/
theorem pureProfileSocialWelfare_le_finitePureSocialWelfareOptimum {n : ℕ}
    (M : Model n) (first second : Strategy) :
    pureProfileSocialWelfare M first second ≤ finitePureSocialWelfareOptimum M := by
  cases first <;> cases second <;>
    simp only [pureProfileSocialWelfare, finitePureSocialWelfareOptimum]
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- A positive all-human welfare witness entails a positive finite pure social
optimum, without claiming that all-human is the maximizing profile. -/
theorem finitePureSocialWelfareOptimum_pos_of_human_human_pos {n : ℕ}
    (M : Model n)
    (hpositive : 0 < welfareRandomOrder M Strategy.human Strategy.human) :
    0 < finitePureSocialWelfareOptimum M := by
  calc
    0 < pureProfileSocialWelfare M Strategy.human Strategy.human := by
      simpa [pureProfileSocialWelfare] using hpositive
    _ ≤ finitePureSocialWelfareOptimum M :=
      pureProfileSocialWelfare_le_finitePureSocialWelfareOptimum
        M Strategy.human Strategy.human

/-- The signed-welfare conclusion at the pure-game level: monocultural `AA` is
the unique pure equilibrium, has negative welfare, and the finite pure social
optimum has positive welfare. -/
noncomputable def HasSignedWelfareUniquePureEquilibrium {n : ℕ} (M : Model n) : Prop :=
  UniquePureNashEquilibrium M Strategy.algorithm Strategy.algorithm ∧
    welfareRandomOrder M Strategy.algorithm Strategy.algorithm < 0 ∧
      0 < finitePureSocialWelfareOptimum M

/-- The existing KR21 paradox certificate, together with the two signed welfare
witnesses, yields the source-facing pure-game signed-welfare conclusion. -/
theorem hasSignedWelfareUniquePureEquilibrium_of_paradox_negativeAA_positiveHH
    {n : ℕ} (M : Model n) (hparadox : HasKR21MonocultureParadox M)
    (hnegativeAA : welfareRandomOrder M Strategy.algorithm Strategy.algorithm < 0)
    (hpositiveHH : 0 < welfareRandomOrder M Strategy.human Strategy.human) :
    HasSignedWelfareUniquePureEquilibrium M := by
  refine ⟨algorithm_algorithm_uniquePureNashEquilibrium_of_algorithmStrictlyDominant
    M hparadox.1, hnegativeAA,
    finitePureSocialWelfareOptimum_pos_of_human_human_pos M hpositiveHH⟩

end Model

/-- Source-model signed-welfare construction with the game-theoretic conclusion
made explicit.  It reuses the established fixed-center Mallows translation
construction; `AA` is the unique pure Nash equilibrium, and the positive social
quantity is the maximum over all four pure profiles.  No mixed-equilibrium claim
is made. -/
theorem fixedCenterMallows_exists_signedWelfare_uniquePureEquilibrium
    {n : ℕ} (center : Ranking n) (value : ValueProfile n)
    (hvalue : StrictlyOrderedBy center value) (hn : 0 < n)
    (thetaH : ℝ) (hthetaH : 0 < thetaH) :
    ∃ thetaA, thetaH < thetaA ∧ ∃ shift,
      let M := (fixedCenterMallowsPointFamily center value).modelAt thetaA thetaH
      Model.HasSignedWelfareUniquePureEquilibrium (M.translateValues shift) := by
  rcases fixedCenterMallows_exists_unbounded_relative_welfare_loss
      center value hvalue hn thetaH hthetaH 1 zero_lt_one with
    ⟨thetaA, hthetaA, shift, hparadox, hnegativeAA, hpositiveHH, _⟩
  exact ⟨thetaA, hthetaA, shift,
    Model.hasSignedWelfareUniquePureEquilibrium_of_paradox_negativeAA_positiveHH
      _ hparadox hnegativeAA hpositiveHH⟩

end KR21Monoculture
