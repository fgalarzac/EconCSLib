import PKG25NoFreeLunch.JointSourceModel

/-!
# PKG25 Proposition 7: uniform mixture of Lemma 8 witnesses

If every agent has an interior profile on which the collaboration strategy
does not defer to that agent, Lemma 8 supplies one finite counterexample per
agent.  Proposition 7 averages those settings uniformly.  This module exposes
the finite mixture and its raw joint-law embedding before either is consumed
by a reliability contradiction.
-/

namespace PKG25NoFreeLunch

/-- The uniform weights used to average one Lemma 8 setting per agent. -/
noncomputable def proposition7UniformWeights (n : ℕ) : Fin n → ℝ :=
  fun _ => (1 : ℝ) / (n : ℝ)

theorem proposition7UniformWeights_nonneg {n : ℕ} [Nonempty (Fin n)] :
    ∀ k : Fin n, 0 ≤ proposition7UniformWeights n k := by
  have hnpos_nat : 0 < n := Fin.size_positive'
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hnpos_nat
  intro k
  exact div_nonneg zero_le_one hnpos.le

theorem proposition7UniformWeights_pos {n : ℕ} [Nonempty (Fin n)] :
    ∀ k : Fin n, 0 < proposition7UniformWeights n k := by
  have hnpos_nat : 0 < n := Fin.size_positive'
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hnpos_nat
  intro k
  exact div_pos zero_lt_one hnpos

theorem proposition7UniformWeights_sum {n : ℕ} [Nonempty (Fin n)] :
    (∑ k : Fin n, proposition7UniformWeights n k) = 1 := by
  have hnpos_nat : 0 < n := Fin.size_positive'
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hnpos_nat
  rw [show (∑ _k : Fin n, proposition7UniformWeights n _k) =
      ∑ _k : Fin n, (1 : ℝ) / (n : ℝ) by rfl]
  rw [Finset.sum_const, Finset.card_univ]
  simp
  field_simp [ne_of_gt hnpos]

/-- The per-agent finite settings supplied by the Lemma 8 construction. -/
noncomputable def proposition7CounterexampleComponents {n : ℕ}
    (C : CollaborationStrategy n) (p : Fin n → Fin n → ℝ)
    (hp : ∀ k : Fin n, Interior (p k)) :
    Fin n → FiniteCollaborationSetting n :=
  fun k => part1Setting (C (p k)) (p k) (hp k)

/-- The explicit uniform mixture of the per-agent Lemma 8 finite settings. -/
noncomputable def proposition7UniformMixture {n : ℕ} [Nonempty (Fin n)]
    (C : CollaborationStrategy n) (p : Fin n → Fin n → ℝ)
    (hp : ∀ k : Fin n, Interior (p k)) : FiniteCollaborationSetting n :=
  FiniteCollaborationSetting.mix
    (proposition7CounterexampleComponents C p hp)
    (proposition7UniformWeights n)
    proposition7UniformWeights_nonneg
    proposition7UniformWeights_sum

theorem proposition7UniformMixture_strategyAccuracy {n : ℕ} [Nonempty (Fin n)]
    (C : CollaborationStrategy n) (p : Fin n → Fin n → ℝ)
    (hp : ∀ k : Fin n, Interior (p k)) :
    (proposition7UniformMixture C p hp).strategyAccuracy C =
      ∑ k : Fin n, proposition7UniformWeights n k *
        (proposition7CounterexampleComponents C p hp k).strategyAccuracy C := by
  unfold proposition7UniformMixture
  exact FiniteCollaborationSetting.strategyAccuracy_mix _ _ _ _ C

theorem proposition7UniformMixture_agentAccuracy {n : ℕ} [Nonempty (Fin n)]
    (C : CollaborationStrategy n) (p : Fin n → Fin n → ℝ)
    (hp : ∀ k : Fin n, Interior (p k)) (i : Fin n) :
    (proposition7UniformMixture C p hp).agentAccuracy i =
      ∑ k : Fin n, proposition7UniformWeights n k *
        (proposition7CounterexampleComponents C p hp k).agentAccuracy i := by
  unfold proposition7UniformMixture
  exact FiniteCollaborationSetting.agentAccuracy_mix _ _ _ _ i

/--
The uniform mixture is strictly less accurate than every agent whenever the
chosen tuple for each agent is an interior, off-half deferral failure.
-/
theorem proposition7UniformMixture_strategyAccuracy_lt_agentAccuracy
    {n : ℕ} [Nonempty (Fin n)] {C : CollaborationStrategy n}
    (p : Fin n → Fin n → ℝ) (hp : ∀ k : Fin n, Interior (p k))
    (hhalf_ne : ∀ k : Fin n, p k k ≠ (1 : ℝ) / 2)
    (hbad : ∀ k : Fin n, C (p k) ≠ roundProb (p k k)) :
    ∀ i : Fin n,
      (proposition7UniformMixture C p hp).strategyAccuracy C <
        (proposition7UniformMixture C p hp).agentAccuracy i := by
  classical
  have hcomponent : ∀ k : Fin n,
      WeakCounterexampleFor
        (FiniteCollaborationSetting.toAccuracySurface C
          (proposition7CounterexampleComponents C p hp k)) k := by
    intro k
    simpa [proposition7CounterexampleComponents] using
      (part1Setting_weakCounterexample (C := C) (hp k) (hhalf_ne k) (hbad k))
  intro i
  rw [proposition7UniformMixture_strategyAccuracy C p hp,
    proposition7UniformMixture_agentAccuracy C p hp i]
  refine Finset.sum_lt_sum ?_ ?_
  · intro k _hk
    exact mul_le_mul_of_nonneg_left ((hcomponent k).2 i)
      (proposition7UniformWeights_nonneg k)
  · exact ⟨i, Finset.mem_univ i,
      mul_lt_mul_of_pos_left (hcomponent i).1
        (proposition7UniformWeights_pos i)⟩

/-- The finite uniform witness is a well-formed raw joint-law setting. -/
theorem proposition7UniformMixture_raw_strategyWellFormed
    {n : ℕ} [Nonempty (Fin n)] (C : CollaborationStrategy n)
    (p : Fin n → Fin n → ℝ) (hp : ∀ k : Fin n, Interior (p k)) :
    JointLawCollaborationSetting.StrategyWellFormed
      (JointLawCollaborationSetting.ofFinite (proposition7UniformMixture C p hp)) C :=
  JointLawCollaborationSetting.ofFinite_strategyWellFormed C
    (proposition7UniformMixture C p hp)

theorem proposition7UniformMixture_raw_strategyAccuracy_lt_agentAccuracy
    {n : ℕ} [Nonempty (Fin n)] {C : CollaborationStrategy n}
    (p : Fin n → Fin n → ℝ) (hp : ∀ k : Fin n, Interior (p k))
    (hhalf_ne : ∀ k : Fin n, p k k ≠ (1 : ℝ) / 2)
    (hbad : ∀ k : Fin n, C (p k) ≠ roundProb (p k k)) :
    ∀ i : Fin n,
      (JointLawCollaborationSetting.ofFinite
        (proposition7UniformMixture C p hp)).strategyAccuracy C <
        (JointLawCollaborationSetting.ofFinite
          (proposition7UniformMixture C p hp)).agentAccuracy i := by
  intro i
  simpa only [JointLawCollaborationSetting.ofFinite_strategyAccuracy,
    JointLawCollaborationSetting.ofFinite_agentAccuracy] using
    (proposition7UniformMixture_strategyAccuracy_lt_agentAccuracy
      (C := C) p hp hhalf_ne hbad i)

/--
The negation of Proposition 7's fixed-deferral conclusion supplies the exact
bad tuple family needed by the explicit raw uniform witness.
-/
theorem proposition7_raw_uniform_witness_of_no_fixed_deferral
    {n : ℕ} [Nonempty (Fin n)] (C : CollaborationStrategy n)
    (hno_fixed_deferral : ¬ ∃ k : Fin n, DefersAwayFromHalf C k) :
    ∃ S : JointLawCollaborationSetting n,
      S.StrategyWellFormed C ∧
        ∀ i : Fin n, S.strategyAccuracy C < S.agentAccuracy i := by
  classical
  have hbad_exists : ∀ k : Fin n,
      ∃ p : Fin n → ℝ,
        Interior p ∧ p k ≠ (1 : ℝ) / 2 ∧ C p ≠ roundProb (p k) := by
    intro k
    have hk : ¬ DefersAwayFromHalf C k := by
      intro hk
      exact hno_fixed_deferral ⟨k, hk⟩
    simpa [DefersAwayFromHalf] using hk
  choose p hprops using hbad_exists
  let T : FiniteCollaborationSetting n :=
    proposition7UniformMixture C p (fun k => (hprops k).1)
  refine ⟨JointLawCollaborationSetting.ofFinite T,
    JointLawCollaborationSetting.ofFinite_strategyWellFormed C T, ?_⟩
  intro i
  have hstrict := proposition7UniformMixture_strategyAccuracy_lt_agentAccuracy
    (C := C) p (fun k => (hprops k).1)
      (fun k => (hprops k).2.1) (fun k => (hprops k).2.2) i
  simpa [T, JointLawCollaborationSetting.ofFinite_strategyAccuracy,
    JointLawCollaborationSetting.ofFinite_agentAccuracy] using hstrict

end PKG25NoFreeLunch
