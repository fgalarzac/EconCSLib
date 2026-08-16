import PKG25NoFreeLunch.MainTheorems

/-!
# PKG25 source-audit bridges

This module records two source-facing distinctions that should not be hidden in
the main implementation.

* The paper defines reliability over all calibrated collaboration settings. Its
  impossibility proof only needs the finite calibrated settings it explicitly
  constructs. `ReliableFinite` is the proof-facing finite restriction. The
  abstract `SourceReliabilityDomain` bridge is retained as a reusable auxiliary
  theorem, not as a source-facing endpoint.
* The proof section accidentally restates the one-way main theorem as an `iff`.
  Definition 4 leaves boundary profiles unconstrained, so the converse is
  false.  `boundaryFlipStrategy_counterexample_to_iff_converse` gives an
  explicit finite calibrated counterexample while leaving Theorem 1's forward
  implication untouched.
-/

namespace PKG25NoFreeLunch

/-! ## Accuracy/loss display -/

/-- Conditional expected 0--1 loss at a point with label-one probability `eta`. -/
def pointZeroOneLoss (prediction : Label) (eta : ℝ) : ℝ :=
  if prediction then 1 - eta else eta

/-- The source's opening absolute-difference display is loss, not accuracy. -/
theorem pointAccuracy_eq_one_sub_pointZeroOneLoss
    (prediction : Label) (eta : ℝ) :
    pointAccuracy prediction eta = 1 - pointZeroOneLoss prediction eta := by
  cases prediction <;> simp [pointAccuracy, pointZeroOneLoss]

/-- Equivalently, conditional expected correctness plus 0--1 loss is one. -/
theorem pointAccuracy_add_pointZeroOneLoss
    (prediction : Label) (eta : ℝ) :
    pointAccuracy prediction eta + pointZeroOneLoss prediction eta = 1 := by
  rw [pointAccuracy_eq_one_sub_pointZeroOneLoss]
  ring

/--
The proof preliminaries' strict-dominance sentence needs a non-tie condition.
At conditional label probability `1/2`, the paper's rounding convention calls
`true` correct and `false` incorrect, but both labels have accuracy `1/2`.
The later adversarial witnesses use conditional probabilities `0` and `1`, so
this local omission is not used by the main proof.
-/
theorem halfTie_correct_incorrect_same_accuracy :
    roundProb ((1 : ℝ) / 2) = true ∧
      false ≠ roundProb ((1 : ℝ) / 2) ∧
      pointAccuracy true ((1 : ℝ) / 2) =
        pointAccuracy false ((1 : ℝ) / 2) := by
  norm_num [roundProb, pointAccuracy]

/-- The strict correctness gap is valid once the omitted non-tie condition is restored. -/
theorem pointAccuracy_lt_of_correct_incorrect_of_ne_half
    {good bad : Label} {eta : ℝ}
    (hgood : good = roundProb eta) (hbad : bad ≠ roundProb eta)
    (hne : eta ≠ (1 : ℝ) / 2) :
    pointAccuracy bad eta < pointAccuracy good eta := by
  by_cases hr : roundProb eta = true
  · rw [hr] at hgood hbad
    subst good
    have hb : bad = false := by
      cases bad <;> simp_all
    subst bad
    have hhalf : (1 : ℝ) / 2 ≤ eta := roundProb_eq_true_iff.mp hr
    have hstrict : (1 : ℝ) / 2 < eta := lt_of_le_of_ne hhalf (Ne.symm hne)
    simp [pointAccuracy]
    linarith
  · have hr0 : roundProb eta = false := by
      cases h : roundProb eta
      · rfl
      · exact (hr h).elim
    rw [hr0] at hgood hbad
    subst good
    have hb : bad = true := by
      cases bad <;> simp_all
    subst bad
    have hhalf : eta < (1 : ℝ) / 2 := roundProb_eq_false_iff.mp hr0
    simp [pointAccuracy]
    linarith

/-! ## Auxiliary abstract-domain bridge -/

/--
An abstract source-level setting universe equipped with the actual accuracy
functionals and an accuracy-preserving inclusion of every finite calibrated
setting used by the paper's proof.

This abstraction is auxiliary only. It remains useful for setting universes
whose finite-witness inclusion preserves accuracy, but it is not the source
model used by the paper-facing interface.
-/
structure SourceReliabilityDomain (n : ℕ) where
  Setting : Type
  strategyAccuracy : Setting → CollaborationStrategy n → ℝ
  agentAccuracy : Setting → Fin n → ℝ
  includeFinite : FiniteCollaborationSetting n → Setting
  includeFinite_strategyAccuracy :
    ∀ (S : FiniteCollaborationSetting n) (C : CollaborationStrategy n),
      strategyAccuracy (includeFinite S) C = S.strategyAccuracy C
  includeFinite_agentAccuracy :
    ∀ (S : FiniteCollaborationSetting n) (i : Fin n),
      agentAccuracy (includeFinite S) i = S.agentAccuracy i

/-- Source-style reliability over a chosen universe of collaboration settings. -/
def SourceReliableIn {n : ℕ} (D : SourceReliabilityDomain n)
    (C : CollaborationStrategy n) : Prop :=
  ∀ S : D.Setting, ∃ i : Fin n,
    D.agentAccuracy S i ≤ D.strategyAccuracy S C

/-- Reliability on a source domain containing the finite witnesses implies finite reliability. -/
theorem reliableFinite_of_sourceReliableIn {n : ℕ}
    (D : SourceReliabilityDomain n) {C : CollaborationStrategy n}
    (hrel : SourceReliableIn D C) : ReliableFinite C := by
  intro S
  rcases hrel (D.includeFinite S) with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  simpa [D.includeFinite_agentAccuracy, D.includeFinite_strategyAccuracy] using hi

/--
The source-general forward theorem: any reliability universe that contains all
finite calibrated witness settings inherits the paper's no-free-lunch result.
-/
theorem main_no_free_lunch_in_source_domain {n : ℕ} [Nonempty (Fin n)]
    (D : SourceReliabilityDomain n) (C : CollaborationStrategy n) :
    SourceReliableIn D C → NonCollaborative C := by
  intro hrel
  exact main_no_free_lunch_finite C (reliableFinite_of_sourceReliableIn D hrel)

/-! ## Explicit counterexample to the proof section's accidental converse -/

/--
This one-agent strategy follows the agent on every interior profile, including
the half tie, but deliberately outputs `0` at the boundary prediction `1`.
-/
noncomputable def boundaryFlipStrategy : CollaborationStrategy 1 := fun p =>
  if p 0 = 1 then false else roundProb (p 0)

theorem boundaryFlipStrategy_nonCollaborative :
    NonCollaborative boundaryFlipStrategy := by
  refine ⟨0, true, ?_, ?_⟩
  · intro p hp _hhalf
    have hp1 : p 0 ≠ 1 := ne_of_lt (hp 0).2
    simp [boundaryFlipStrategy, hp1]
  · intro p hp hhalf
    simp [boundaryFlipStrategy, hhalf, roundProb]

/-- A one-point calibrated setting in which the unique agent predicts `1` with certainty. -/
noncomputable def boundaryCertainSetting : FiniteCollaborationSetting 1 where
  X := Unit
  mass := fun _ => 1
  mass_nonneg := by intro x; norm_num
  mass_sum := by simp
  eta := fun _ => 1
  eta_range := by intro x; norm_num
  pred := fun _ _ => 1
  pred_range := by intro i x; norm_num
  calibrated := by
    intro i p
    dsimp
    intro hpos
    by_cases hp : p = 1
    · subst p
      simp [eventMass, eventLabelMass]
    · have hp' : (1 : ℝ) ≠ p := Ne.symm hp
      simp [eventMass, hp'] at hpos

theorem boundaryCertainSetting_agentAccuracy :
    boundaryCertainSetting.agentAccuracy 0 = 1 := by
  change (∑ _x : Unit, (1 : ℝ) * pointAccuracy (roundProb 1) 1) = 1
  norm_num [pointAccuracy, roundProb]

theorem boundaryCertainSetting_strategyAccuracy :
    boundaryCertainSetting.strategyAccuracy boundaryFlipStrategy = 0 := by
  simp [FiniteCollaborationSetting.strategyAccuracy,
    FiniteCollaborationSetting.strategyClassifier, boundaryCertainSetting,
    boundaryFlipStrategy, pointAccuracy]

theorem boundaryFlipStrategy_not_reliableFinite :
    ¬ ReliableFinite boundaryFlipStrategy := by
  intro hrel
  rcases hrel boundaryCertainSetting with ⟨i, hi⟩
  have hi0 : i = 0 := Subsingleton.elim _ _
  subst i
  change boundaryCertainSetting.agentAccuracy 0 ≤
    boundaryCertainSetting.strategyAccuracy boundaryFlipStrategy at hi
  rw [boundaryCertainSetting_agentAccuracy,
    boundaryCertainSetting_strategyAccuracy] at hi
  norm_num at hi

/--
The proof section's `if and only if` converse is false under Definition 4:
non-collaboration constrains only interior profiles, while reliability also
tests calibrated settings with boundary predictions.
-/
theorem boundaryFlipStrategy_counterexample_to_iff_converse :
    NonCollaborative boundaryFlipStrategy ∧
      ¬ ReliableFinite boundaryFlipStrategy :=
  ⟨boundaryFlipStrategy_nonCollaborative,
    boundaryFlipStrategy_not_reliableFinite⟩

end PKG25NoFreeLunch
