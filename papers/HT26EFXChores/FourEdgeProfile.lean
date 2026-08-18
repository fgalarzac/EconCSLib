import HT26EFXChores.B1DirectAllocation

/-!
# Four-edge multigraph profiles

The small-agent sets of M₂ chores form a loop-free multigraph on the four
agents.  The source's B.2.2(b) `|M₂|=4` classification is the elementary fact
that a two-regular multigraph on four vertices is either two doubled disjoint
edges or a four-cycle.

Source: `EFXadditivechores.tex`, lines 2526--2535.
-/

namespace HT26EFXChores

/-- The six multiplicities of a loop-free two-regular multigraph on four
labelled vertices have one of the three doubled-matching or three four-cycle
profiles.  The three named degree equations are exactly the incidence count
used in source Case B.2.2(b). -/
theorem four_edge_profile_classification
    (e01 e02 e03 e12 e13 e23 : ℕ)
    (h0 : e01 + e02 + e03 = 2)
    (h1 : e01 + e12 + e13 = 2)
    (h2 : e02 + e12 + e23 = 2)
    (h3 : e03 + e13 + e23 = 2) :
    (e01 = 2 ∧ e23 = 2) ∨
    (e02 = 2 ∧ e13 = 2) ∨
    (e03 = 2 ∧ e12 = 2) ∨
    (e01 = 1 ∧ e12 = 1 ∧ e23 = 1 ∧ e03 = 1) ∨
    (e01 = 1 ∧ e13 = 1 ∧ e23 = 1 ∧ e02 = 1) ∨
    (e02 = 1 ∧ e12 = 1 ∧ e13 = 1 ∧ e03 = 1) := by
  by_cases h01two : e01 = 2
  · left
    constructor <;> omega
  by_cases h02two : e02 = 2
  · right; left
    constructor <;> omega
  by_cases h03two : e03 = 2
  · right; right; left
    constructor <;> omega
  have h01le : e01 ≤ 1 := by omega
  have h02le : e02 ≤ 1 := by omega
  have h03le : e03 ≤ 1 := by omega
  interval_cases e01
  · right; right; right; right; right
    omega
  · interval_cases e02
    · right; right; right; left
      omega
    · right; right; right; right; left
      omega

end HT26EFXChores
