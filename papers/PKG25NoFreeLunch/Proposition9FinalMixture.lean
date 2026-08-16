import PKG25NoFreeLunch.MainTheorems

/-!
# PKG25 Proposition 9: explicit final mixture

The source closes Proposition 9 by taking a mixture with a parameter
``lambda`` sufficiently close to one.  The finite proof uses the concrete
checked choice `7 / 8` for the first auxiliary setting and `1 / 8` for the
second.  This module exposes that witness independently of the reliability
contradiction that consumes it.
-/

namespace PKG25NoFreeLunch

/-- The two auxiliary settings used in the final Proposition 9 mixture. -/
noncomputable def proposition9FinalComponents {n : ℕ} (k : Fin n)
    (p q : Fin n → ℝ) (hp : Interior p) (hq : Interior q) :
    Fin 2 → FiniteCollaborationSetting n :=
  fun r =>
    if r = 0 then part2S1Setting k else part2S2Setting k p q hp hq

/-- The concrete source-mixture weights checked by the finite proof. -/
noncomputable def proposition9FinalWeights : Fin 2 → ℝ :=
  fun r => if r = 0 then (7 : ℝ) / 8 else (1 : ℝ) / 8

theorem proposition9FinalWeights_nonneg :
    ∀ r : Fin 2, 0 ≤ proposition9FinalWeights r := by
  intro r
  fin_cases r <;> norm_num [proposition9FinalWeights]

theorem proposition9FinalWeights_sum :
    (∑ r : Fin 2, proposition9FinalWeights r) = 1 := by
  norm_num [proposition9FinalWeights]

/-- The concrete `7 / 8`--`1 / 8` finite collaboration setting. -/
noncomputable def proposition9FinalMixture {n : ℕ} (k : Fin n)
    (p q : Fin n → ℝ) (hp : Interior p) (hq : Interior q) :
    FiniteCollaborationSetting n :=
  FiniteCollaborationSetting.mix
    (proposition9FinalComponents k p q hp hq)
    proposition9FinalWeights
    proposition9FinalWeights_nonneg
    proposition9FinalWeights_sum

theorem proposition9FinalMixture_strategyAccuracy {n : ℕ}
    (C : CollaborationStrategy n) (k : Fin n) (p q : Fin n → ℝ)
    (hp : Interior p) (hq : Interior q) :
    (proposition9FinalMixture k p q hp hq).strategyAccuracy C =
      (7 : ℝ) / 8 * (part2S1Setting k).strategyAccuracy C +
        (1 : ℝ) / 8 * (part2S2Setting k p q hp hq).strategyAccuracy C := by
  unfold proposition9FinalMixture
  rw [FiniteCollaborationSetting.strategyAccuracy_mix]
  norm_num [proposition9FinalComponents, proposition9FinalWeights]

theorem proposition9FinalMixture_agentAccuracy {n : ℕ}
    (i : Fin n) (k : Fin n) (p q : Fin n → ℝ)
    (hp : Interior p) (hq : Interior q) :
    (proposition9FinalMixture k p q hp hq).agentAccuracy i =
      (7 : ℝ) / 8 * (part2S1Setting k).agentAccuracy i +
        (1 : ℝ) / 8 * (part2S2Setting k p q hp hq).agentAccuracy i := by
  unfold proposition9FinalMixture
  rw [FiniteCollaborationSetting.agentAccuracy_mix]
  norm_num [proposition9FinalComponents, proposition9FinalWeights]

/--
The concrete final mixture is strictly less accurate than every individual
agent whenever the two tie-slice profiles witness different strategy labels.
-/
theorem proposition9FinalMixture_strategyAccuracy_lt_agentAccuracy {n : ℕ}
    [Nonempty (Fin n)] {C : CollaborationStrategy n} {k : Fin n}
    {p q : Fin n → ℝ} (hk : DefersAwayFromHalf C k)
    (hp : Interior p) (hq : Interior q)
    (hpk : p k = (1 : ℝ) / 2) (hqk : q k = (1 : ℝ) / 2)
    (hCp : C p = true) (hCq : C q = false) :
    ∀ i : Fin n,
      (proposition9FinalMixture k p q hp hq).strategyAccuracy C <
        (proposition9FinalMixture k p q hp hq).agentAccuracy i := by
  intro i
  rw [proposition9FinalMixture_strategyAccuracy C k p q hp hq,
    proposition9FinalMixture_agentAccuracy i k p q hp hq]
  by_cases hik : i = k
  · subst i
    have hS1s : (part2S1Setting k).strategyAccuracy C = (7 : ℝ) / 12 :=
      part2S1_strategyAccuracy (C := C) (k := k) hk
    have hS1a : (part2S1Setting k).agentAccuracy k = (7 : ℝ) / 12 :=
      part2S1_agentAccuracy_k k
    have hS2 : (part2S2Setting k p q hp hq).strategyAccuracy C <
        (part2S2Setting k p q hp hq).agentAccuracy k :=
      part2S2_strategyAccuracy_lt_agentK hp hq hpk hqk hCp hCq
    norm_num [hS1s, hS1a]
    nlinarith
  · have hS1s : (part2S1Setting k).strategyAccuracy C = (7 : ℝ) / 12 :=
      part2S1_strategyAccuracy (C := C) (k := k) hk
    have hS1a : (part2S1Setting k).agentAccuracy i = (3 : ℝ) / 4 :=
      part2S1_agentAccuracy_ne hik
    have hS2s_le : (part2S2Setting k p q hp hq).strategyAccuracy C ≤ 1 :=
      (FiniteCollaborationSetting.strategyAccuracy_range
        (part2S2Setting k p q hp hq) C).2
    have hS2a_nonneg : 0 ≤ (part2S2Setting k p q hp hq).agentAccuracy i :=
      (FiniteCollaborationSetting.agentAccuracy_range
        (part2S2Setting k p q hp hq) i).1
    norm_num [hS1s, hS1a]
    nlinarith

end PKG25NoFreeLunch
