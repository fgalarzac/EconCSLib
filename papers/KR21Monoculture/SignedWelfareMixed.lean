import KR21Monoculture.SignedWelfareEquilibrium

namespace KR21Monoculture
namespace Model

/-!
# Finite mixed-equilibrium layer for the signed-welfare observation

This file makes the previously omitted mixed-strategy qualifier explicit for
the source's two-firm, two-action game.  A `MixedStrategy` is an individual
probability distribution on the two strategies, and a mixed profile uses the
product of the two individual distributions.  Thus these definitions concern
ordinary independent mixed Nash equilibria; they do not assert anything about
correlated play or a different extensive-form game.
-/

/-- An individual mixed strategy on the source game's two actions.  Both atom
weights are carried explicitly, together with nonnegativity and total mass. -/
structure MixedStrategy where
  algorithmWeight : ℝ
  humanWeight : ℝ
  algorithmWeight_nonneg : 0 ≤ algorithmWeight
  humanWeight_nonneg : 0 ≤ humanWeight
  weights_sum_one : algorithmWeight + humanWeight = 1

/-- The pure algorithmic strategy, viewed as a mixed strategy. -/
def mixedAlgorithm : MixedStrategy where
  algorithmWeight := 1
  humanWeight := 0
  algorithmWeight_nonneg := by norm_num
  humanWeight_nonneg := by norm_num
  weights_sum_one := by norm_num

/-- The pure human strategy, viewed as a mixed strategy. -/
def mixedHuman : MixedStrategy where
  algorithmWeight := 0
  humanWeight := 1
  algorithmWeight_nonneg := by norm_num
  humanWeight_nonneg := by norm_num
  weights_sum_one := by norm_num

/-- Embed either pure action into the explicit two-action mixed-strategy
simplex. -/
def pureMixedStrategy : Strategy → MixedStrategy
  | Strategy.algorithm => mixedAlgorithm
  | Strategy.human => mixedHuman

/-- Equality of two explicit two-action mixed strategies follows from equality
of their two atom weights. -/
theorem MixedStrategy.ext {left right : MixedStrategy}
    (halgorithm : left.algorithmWeight = right.algorithmWeight)
    (hhuman : left.humanWeight = right.humanWeight) :
    left = right := by
  cases left
  cases right
  simp_all

@[simp] theorem mixedAlgorithm_algorithmWeight :
    mixedAlgorithm.algorithmWeight = 1 := rfl

@[simp] theorem mixedAlgorithm_humanWeight :
    mixedAlgorithm.humanWeight = 0 := rfl

@[simp] theorem mixedHuman_algorithmWeight :
    mixedHuman.algorithmWeight = 0 := rfl

@[simp] theorem mixedHuman_humanWeight :
    mixedHuman.humanWeight = 1 := rfl

/-- A mixed strategy with zero human mass is exactly the pure algorithmic
strategy. -/
theorem mixedStrategy_eq_mixedAlgorithm_of_humanWeight_eq_zero
    (strategy : MixedStrategy) (hhuman : strategy.humanWeight = 0) :
    strategy = mixedAlgorithm := by
  apply MixedStrategy.ext
  · rw [show strategy.algorithmWeight = 1 by linarith [strategy.weights_sum_one]]
    rfl
  · simpa [hhuman]

/-- The payoff from a pure action against an independently mixed opponent. -/
noncomputable def purePayoffAgainstMixed {n : ℕ} (M : Model n)
    (self : Strategy) (other : MixedStrategy) : ℝ :=
  other.algorithmWeight * labeledFirmRandomOrderExpectedPayoff M self Strategy.algorithm +
    other.humanWeight * labeledFirmRandomOrderExpectedPayoff M self Strategy.human

/-- The expected payoff from independently mixing one's own two actions against
an independently mixed opponent. -/
noncomputable def mixedExpectedPayoff {n : ℕ} (M : Model n)
    (self other : MixedStrategy) : ℝ :=
  self.algorithmWeight * purePayoffAgainstMixed M Strategy.algorithm other +
    self.humanWeight * purePayoffAgainstMixed M Strategy.human other

/-- A mixed Nash equilibrium of the finite two-firm game.  The second clause
uses the reversed payoff orientation, just as `PureNashEquilibrium` does. -/
noncomputable def MixedNashEquilibrium {n : ℕ} (M : Model n)
    (first second : MixedStrategy) : Prop :=
  (∀ deviation : MixedStrategy,
    mixedExpectedPayoff M deviation second ≤ mixedExpectedPayoff M first second) ∧
  (∀ deviation : MixedStrategy,
    mixedExpectedPayoff M deviation first ≤ mixedExpectedPayoff M second first)

/-- A specified independently mixed profile is the unique mixed Nash
equilibrium. -/
noncomputable def UniqueMixedNashEquilibrium {n : ℕ} (M : Model n)
    (first second : MixedStrategy) : Prop :=
  MixedNashEquilibrium M first second ∧
    ∀ otherFirst otherSecond,
      MixedNashEquilibrium M otherFirst otherSecond →
        otherFirst = first ∧ otherSecond = second

/-- Strict dominance against both pure opponent actions extends to a strict
advantage against every explicitly mixed opponent. -/
theorem algorithm_strictlyBeats_human_against_mixed
    {n : ℕ} (M : Model n) (hdominant : AlgorithmStrictlyDominant M)
    (other : MixedStrategy) :
    purePayoffAgainstMixed M Strategy.human other <
      purePayoffAgainstMixed M Strategy.algorithm other := by
  rcases (algorithmStrictlyDominant_iff_payoffAgainst M).1 hdominant with
    ⟨hAgainstAlgorithm, hAgainstHuman⟩
  have hAlgorithmGap :
      0 < labeledFirmRandomOrderExpectedPayoff M Strategy.algorithm Strategy.algorithm -
        labeledFirmRandomOrderExpectedPayoff M Strategy.human Strategy.algorithm := by
    simpa [labeledFirmRandomOrderExpectedPayoff] using sub_pos.mpr hAgainstAlgorithm
  have hHumanGap :
      0 < labeledFirmRandomOrderExpectedPayoff M Strategy.algorithm Strategy.human -
        labeledFirmRandomOrderExpectedPayoff M Strategy.human Strategy.human := by
    simpa [labeledFirmRandomOrderExpectedPayoff] using sub_pos.mpr hAgainstHuman
  have hHumanTermNonneg :
      0 ≤ other.humanWeight *
        (labeledFirmRandomOrderExpectedPayoff M Strategy.algorithm Strategy.human -
          labeledFirmRandomOrderExpectedPayoff M Strategy.human Strategy.human) :=
    mul_nonneg other.humanWeight_nonneg (le_of_lt hHumanGap)
  have hPositiveCombination :
      0 < other.algorithmWeight *
        (labeledFirmRandomOrderExpectedPayoff M Strategy.algorithm Strategy.algorithm -
          labeledFirmRandomOrderExpectedPayoff M Strategy.human Strategy.algorithm) +
        other.humanWeight *
          (labeledFirmRandomOrderExpectedPayoff M Strategy.algorithm Strategy.human -
            labeledFirmRandomOrderExpectedPayoff M Strategy.human Strategy.human) := by
    by_cases halgorithm : 0 < other.algorithmWeight
    · exact add_pos_of_pos_of_nonneg
        (mul_pos halgorithm hAlgorithmGap) hHumanTermNonneg
    · have halgorithm_zero : other.algorithmWeight = 0 := by
        exact le_antisymm (le_of_not_gt halgorithm) other.algorithmWeight_nonneg
      have hhuman : 0 < other.humanWeight := by
        have hsum := other.weights_sum_one
        rw [halgorithm_zero] at hsum
        linarith [hsum]
      rw [halgorithm_zero]
      simpa using mul_pos hhuman hHumanGap
  apply sub_pos.mp
  unfold purePayoffAgainstMixed
  ring_nf
  convert hPositiveCombination using 1
  ring

/-- Against any mixed opponent, no independently mixed own strategy beats the
pure algorithmic action under strict algorithmic dominance. -/
theorem mixedExpectedPayoff_le_mixedAlgorithm_against_mixed
    {n : ℕ} (M : Model n) (hdominant : AlgorithmStrictlyDominant M)
    (self other : MixedStrategy) :
    mixedExpectedPayoff M self other ≤ mixedExpectedPayoff M mixedAlgorithm other := by
  have hstrict := algorithm_strictlyBeats_human_against_mixed M hdominant other
  have hgap : 0 ≤ purePayoffAgainstMixed M Strategy.algorithm other -
      purePayoffAgainstMixed M Strategy.human other :=
    le_of_lt (sub_pos.mpr hstrict)
  have hnonneg : 0 ≤ self.humanWeight *
      (purePayoffAgainstMixed M Strategy.algorithm other -
        purePayoffAgainstMixed M Strategy.human other) :=
    mul_nonneg self.humanWeight_nonneg hgap
  apply sub_nonneg.mp
  change 0 ≤ mixedExpectedPayoff M mixedAlgorithm other -
    mixedExpectedPayoff M self other
  rw [show mixedExpectedPayoff M mixedAlgorithm other -
      mixedExpectedPayoff M self other =
        self.humanWeight *
          (purePayoffAgainstMixed M Strategy.algorithm other -
            purePayoffAgainstMixed M Strategy.human other) by
        unfold mixedExpectedPayoff mixedAlgorithm
        rw [show self.algorithmWeight = 1 - self.humanWeight by
          linarith [self.weights_sum_one]]
        ring]
  exact hnonneg

/-- Any mixed strategy assigning positive mass to the human action is strictly
worse than pure algorithm against any mixed opponent under strict dominance. -/
theorem mixedExpectedPayoff_mixedAlgorithm_gt_of_humanWeight_pos
    {n : ℕ} (M : Model n) (hdominant : AlgorithmStrictlyDominant M)
    (self other : MixedStrategy) (hhuman : 0 < self.humanWeight) :
    mixedExpectedPayoff M self other < mixedExpectedPayoff M mixedAlgorithm other := by
  have hstrict := algorithm_strictlyBeats_human_against_mixed M hdominant other
  have hgap : 0 < purePayoffAgainstMixed M Strategy.algorithm other -
      purePayoffAgainstMixed M Strategy.human other :=
    sub_pos.mpr hstrict
  apply sub_pos.mp
  change 0 < mixedExpectedPayoff M mixedAlgorithm other -
    mixedExpectedPayoff M self other
  rw [show mixedExpectedPayoff M mixedAlgorithm other -
      mixedExpectedPayoff M self other =
        self.humanWeight *
          (purePayoffAgainstMixed M Strategy.algorithm other -
            purePayoffAgainstMixed M Strategy.human other) by
        unfold mixedExpectedPayoff mixedAlgorithm
        rw [show self.algorithmWeight = 1 - self.humanWeight by
          linarith [self.weights_sum_one]]
        ring]
  exact mul_pos hhuman hgap

/-- The all-algorithm independently mixed profile is a mixed Nash equilibrium
under strict algorithmic dominance. -/
theorem mixedAlgorithm_mixedAlgorithm_mixedNashEquilibrium_of_algorithmStrictlyDominant
    {n : ℕ} (M : Model n) (hdominant : AlgorithmStrictlyDominant M) :
    MixedNashEquilibrium M mixedAlgorithm mixedAlgorithm := by
  constructor <;> intro deviation
  · exact mixedExpectedPayoff_le_mixedAlgorithm_against_mixed
      M hdominant deviation mixedAlgorithm
  · exact mixedExpectedPayoff_le_mixedAlgorithm_against_mixed
      M hdominant deviation mixedAlgorithm

/-- Strict dominance forces a mixed-equilibrium player's human atom to have
zero probability. -/
theorem humanWeight_eq_zero_of_mixedNashEquilibrium
    {n : ℕ} (M : Model n) (hdominant : AlgorithmStrictlyDominant M)
    {first second : MixedStrategy}
    (hne : MixedNashEquilibrium M first second) :
    first.humanWeight = 0 := by
  by_contra hnonzero
  have hpositive : 0 < first.humanWeight :=
    lt_of_le_of_ne first.humanWeight_nonneg (Ne.symm hnonzero)
  have hstrict := mixedExpectedPayoff_mixedAlgorithm_gt_of_humanWeight_pos
    M hdominant first second hpositive
  exact (not_le_of_gt hstrict) (hne.1 mixedAlgorithm)

/-- Strict dominance gives the full, not merely pure, unique mixed Nash
equilibrium conclusion for the independent finite two-action model. -/
theorem mixedAlgorithm_mixedAlgorithm_uniqueMixedNashEquilibrium_of_algorithmStrictlyDominant
    {n : ℕ} (M : Model n) (hdominant : AlgorithmStrictlyDominant M) :
    UniqueMixedNashEquilibrium M mixedAlgorithm mixedAlgorithm := by
  refine ⟨mixedAlgorithm_mixedAlgorithm_mixedNashEquilibrium_of_algorithmStrictlyDominant
    M hdominant, ?_⟩
  intro otherFirst otherSecond hne
  have hfirst : otherFirst.humanWeight = 0 :=
    humanWeight_eq_zero_of_mixedNashEquilibrium M hdominant hne
  have hsecond : otherSecond.humanWeight = 0 := by
    have hswapped : MixedNashEquilibrium M otherSecond otherFirst :=
      ⟨hne.2, hne.1⟩
    exact humanWeight_eq_zero_of_mixedNashEquilibrium M hdominant hswapped
  exact ⟨mixedStrategy_eq_mixedAlgorithm_of_humanWeight_eq_zero otherFirst hfirst,
    mixedStrategy_eq_mixedAlgorithm_of_humanWeight_eq_zero otherSecond hsecond⟩

/-- Social welfare after independent finite mixing of the two labeled firms.
Every coefficient is visibly one of the four product atom masses. -/
noncomputable def mixedProfileSocialWelfare {n : ℕ} (M : Model n)
    (first second : MixedStrategy) : ℝ :=
  first.algorithmWeight * second.algorithmWeight *
      pureProfileSocialWelfare M Strategy.algorithm Strategy.algorithm +
    first.algorithmWeight * second.humanWeight *
      pureProfileSocialWelfare M Strategy.algorithm Strategy.human +
    first.humanWeight * second.algorithmWeight *
      pureProfileSocialWelfare M Strategy.human Strategy.algorithm +
    first.humanWeight * second.humanWeight *
      pureProfileSocialWelfare M Strategy.human Strategy.human

/-- The four product atom masses of an independently mixed profile sum to one. -/
theorem mixedProfileSocialWelfare_weights_sum_one
    (first second : MixedStrategy) :
    first.algorithmWeight * second.algorithmWeight +
      first.algorithmWeight * second.humanWeight +
      first.humanWeight * second.algorithmWeight +
      first.humanWeight * second.humanWeight = 1 := by
  calc
    first.algorithmWeight * second.algorithmWeight +
        first.algorithmWeight * second.humanWeight +
        first.humanWeight * second.algorithmWeight +
        first.humanWeight * second.humanWeight =
      (first.algorithmWeight + first.humanWeight) *
        (second.algorithmWeight + second.humanWeight) := by ring
    _ = 1 := by rw [first.weights_sum_one, second.weights_sum_one]; norm_num

/-- Each independently mixed social-welfare profile is a convex combination of
the four pure profile welfares, hence is bounded by their explicit finite
maximum. -/
theorem mixedProfileSocialWelfare_le_finitePureSocialWelfareOptimum
    {n : ℕ} (M : Model n) (first second : MixedStrategy) :
    mixedProfileSocialWelfare M first second ≤ finitePureSocialWelfareOptimum M := by
  have hAA := pureProfileSocialWelfare_le_finitePureSocialWelfareOptimum
    M Strategy.algorithm Strategy.algorithm
  have hAH := pureProfileSocialWelfare_le_finitePureSocialWelfareOptimum
    M Strategy.algorithm Strategy.human
  have hHA := pureProfileSocialWelfare_le_finitePureSocialWelfareOptimum
    M Strategy.human Strategy.algorithm
  have hHH := pureProfileSocialWelfare_le_finitePureSocialWelfareOptimum
    M Strategy.human Strategy.human
  have hAAweight : 0 ≤ first.algorithmWeight * second.algorithmWeight :=
    mul_nonneg first.algorithmWeight_nonneg second.algorithmWeight_nonneg
  have hAHweight : 0 ≤ first.algorithmWeight * second.humanWeight :=
    mul_nonneg first.algorithmWeight_nonneg second.humanWeight_nonneg
  have hHAweight : 0 ≤ first.humanWeight * second.algorithmWeight :=
    mul_nonneg first.humanWeight_nonneg second.algorithmWeight_nonneg
  have hHHweight : 0 ≤ first.humanWeight * second.humanWeight :=
    mul_nonneg first.humanWeight_nonneg second.humanWeight_nonneg
  calc
    mixedProfileSocialWelfare M first second ≤
        first.algorithmWeight * second.algorithmWeight * finitePureSocialWelfareOptimum M +
          first.algorithmWeight * second.humanWeight * finitePureSocialWelfareOptimum M +
          first.humanWeight * second.algorithmWeight * finitePureSocialWelfareOptimum M +
          first.humanWeight * second.humanWeight * finitePureSocialWelfareOptimum M := by
      unfold mixedProfileSocialWelfare
      gcongr
    _ = (first.algorithmWeight * second.algorithmWeight +
          first.algorithmWeight * second.humanWeight +
          first.humanWeight * second.algorithmWeight +
          first.humanWeight * second.humanWeight) * finitePureSocialWelfareOptimum M := by
      ring
    _ = finitePureSocialWelfareOptimum M := by
      rw [mixedProfileSocialWelfare_weights_sum_one]
      ring

/-- The finite mixed-profile welfare maximum is exactly the already explicit
maximum over the four pure profiles: independent mixing cannot exceed it, and
each pure profile is itself an allowed mixed profile. -/
noncomputable def finiteMixedSocialWelfareOptimum {n : ℕ} (M : Model n) : ℝ :=
  finitePureSocialWelfareOptimum M

/-- The direct maximum bridge from every independently mixed profile to the
finite pure-profile maximum. -/
theorem mixedProfileSocialWelfare_le_finiteMixedSocialWelfareOptimum
    {n : ℕ} (M : Model n) (first second : MixedStrategy) :
    mixedProfileSocialWelfare M first second ≤ finiteMixedSocialWelfareOptimum M := by
  simpa [finiteMixedSocialWelfareOptimum] using
    mixedProfileSocialWelfare_le_finitePureSocialWelfareOptimum M first second

/-- Pure profiles embed literally in the independent mixed-welfare formula. -/
theorem mixedProfileSocialWelfare_pureMixedStrategy
    {n : ℕ} (M : Model n) (first second : Strategy) :
    mixedProfileSocialWelfare M (pureMixedStrategy first) (pureMixedStrategy second) =
      pureProfileSocialWelfare M first second := by
  cases first <;> cases second <;>
    simp [mixedProfileSocialWelfare, pureMixedStrategy, mixedAlgorithm, mixedHuman]

/-- The finite four-profile maximum is attained by one of the source game's
pure profiles. -/
theorem exists_pureProfileSocialWelfare_eq_finitePureSocialWelfareOptimum
    {n : ℕ} (M : Model n) :
    ∃ first second : Strategy,
      pureProfileSocialWelfare M first second = finitePureSocialWelfareOptimum M := by
  let aa := pureProfileSocialWelfare M Strategy.algorithm Strategy.algorithm
  let ah := pureProfileSocialWelfare M Strategy.algorithm Strategy.human
  let ha := pureProfileSocialWelfare M Strategy.human Strategy.algorithm
  let hh := pureProfileSocialWelfare M Strategy.human Strategy.human
  change ∃ first second : Strategy,
    pureProfileSocialWelfare M first second = max (max aa ah) (max ha hh)
  by_cases hleft : max aa ah ≤ max ha hh
  · by_cases hright : ha ≤ hh
    · refine ⟨Strategy.human, Strategy.human, ?_⟩
      simp only [aa, ah, ha, hh] at hleft hright ⊢
      rw [max_eq_right hleft, max_eq_right hright]
    · refine ⟨Strategy.human, Strategy.algorithm, ?_⟩
      simp only [aa, ah, ha, hh] at hleft hright ⊢
      rw [max_eq_right hleft, max_eq_left (le_of_not_ge hright)]
  · have hrightleft : max ha hh ≤ max aa ah := le_of_not_ge hleft
    by_cases hleftinner : aa ≤ ah
    · refine ⟨Strategy.algorithm, Strategy.human, ?_⟩
      simp only [aa, ah, ha, hh] at hrightleft hleftinner ⊢
      rw [max_eq_left hrightleft, max_eq_right hleftinner]
    · refine ⟨Strategy.algorithm, Strategy.algorithm, ?_⟩
      simp only [aa, ah, ha, hh] at hrightleft hleftinner ⊢
      rw [max_eq_left hrightleft, max_eq_left (le_of_not_ge hleftinner)]

/-- The finite mixed welfare maximum is attained: a maximizing pure profile is
an allowed independently mixed profile with zero-one atom weights. -/
theorem exists_mixedProfileSocialWelfare_eq_finiteMixedSocialWelfareOptimum
    {n : ℕ} (M : Model n) :
    ∃ first second : MixedStrategy,
      mixedProfileSocialWelfare M first second = finiteMixedSocialWelfareOptimum M := by
  rcases exists_pureProfileSocialWelfare_eq_finitePureSocialWelfareOptimum M with
    ⟨first, second, hmax⟩
  refine ⟨pureMixedStrategy first, pureMixedStrategy second, ?_⟩
  rw [mixedProfileSocialWelfare_pureMixedStrategy, hmax]
  rfl

/-- A positive all-human pure welfare witness makes the finite mixed welfare
maximum positive as well. -/
theorem finiteMixedSocialWelfareOptimum_pos_of_human_human_pos
    {n : ℕ} (M : Model n)
    (hpositive : 0 < welfareRandomOrder M Strategy.human Strategy.human) :
    0 < finiteMixedSocialWelfareOptimum M := by
  simpa [finiteMixedSocialWelfareOptimum] using
    finitePureSocialWelfareOptimum_pos_of_human_human_pos M hpositive

/-- The signed-welfare conclusion with the equilibrium quantifier repaired to
the full independent mixed-strategy game. -/
noncomputable def HasSignedWelfareUniqueMixedEquilibrium {n : ℕ} (M : Model n) : Prop :=
  UniqueMixedNashEquilibrium M mixedAlgorithm mixedAlgorithm ∧
    welfareRandomOrder M Strategy.algorithm Strategy.algorithm < 0 ∧
      0 < finiteMixedSocialWelfareOptimum M

/-- The existing KR21 paradox certificate and signed welfare witnesses yield
the repaired mixed-equilibrium conclusion. -/
theorem hasSignedWelfareUniqueMixedEquilibrium_of_paradox_negativeAA_positiveHH
    {n : ℕ} (M : Model n) (hparadox : HasKR21MonocultureParadox M)
    (hnegativeAA : welfareRandomOrder M Strategy.algorithm Strategy.algorithm < 0)
    (hpositiveHH : 0 < welfareRandomOrder M Strategy.human Strategy.human) :
    HasSignedWelfareUniqueMixedEquilibrium M := by
  refine ⟨mixedAlgorithm_mixedAlgorithm_uniqueMixedNashEquilibrium_of_algorithmStrictlyDominant
    M hparadox.1, hnegativeAA,
    finiteMixedSocialWelfareOptimum_pos_of_human_human_pos M hpositiveHH⟩

end Model

/-- Source-model signed-welfare construction with a full independent
mixed-equilibrium conclusion.  The source ranking-law and value-translation
construction is unchanged; only the finite game-theoretic conclusion is
strengthened from pure to mixed strategies. -/
theorem fixedCenterMallows_exists_signedWelfare_uniqueMixedEquilibrium
    {n : ℕ} (center : Ranking n) (value : ValueProfile n)
    (hvalue : StrictlyOrderedBy center value) (hn : 0 < n)
    (thetaH : ℝ) (hthetaH : 0 < thetaH) :
    ∃ thetaA, thetaH < thetaA ∧ ∃ shift,
      let M := (fixedCenterMallowsPointFamily center value).modelAt thetaA thetaH
      Model.HasSignedWelfareUniqueMixedEquilibrium (M.translateValues shift) := by
  rcases fixedCenterMallows_exists_unbounded_relative_welfare_loss
      center value hvalue hn thetaH hthetaH 1 zero_lt_one with
    ⟨thetaA, hthetaA, shift, hparadox, hnegativeAA, hpositiveHH, _⟩
  exact ⟨thetaA, hthetaA, shift,
    Model.hasSignedWelfareUniqueMixedEquilibrium_of_paradox_negativeAA_positiveHH
      _ hparadox hnegativeAA hpositiveHH⟩

end KR21Monoculture
