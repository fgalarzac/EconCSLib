import PKG25NoFreeLunch.PartitionCalibration

/-!
# PKG25 Proposition 9: the full first-setting family

The paper introduces the first auxiliary setting of Proposition 9 for an
arbitrary parameter `0 < ε < 1/2`.  The original development used only the
single sufficient choice `ε = 1/4`.  This file formalizes the complete family,
including calibration, the induced classifiers, both accuracy formulas, and
the strict gap used in the proof.

The lower bound `0 < ε` is implicit in the source's assertion that every
prediction profile lies in `(0,1)^n`; it is recorded explicitly here.
-/

namespace PKG25NoFreeLunch

abbrev Part2S1ParamPoint := Bool

/-- The source's fixed masses `Pr[X=0]=1/3` and `Pr[X=1]=2/3`. -/
noncomputable def part2S1ParamMass : Part2S1ParamPoint → ℝ
  | false => (1 : ℝ) / 3
  | true => (2 : ℝ) / 3

/-- The conditional label probabilities `ε` and `1-ε`. -/
noncomputable def part2S1ParamEta (ε : ℝ) : Part2S1ParamPoint → ℝ
  | false => ε
  | true => 1 - ε

/-- The pooled prediction of the distinguished agent `k`. -/
noncomputable def part2S1ParamKPred (ε : ℝ) : ℝ :=
  (2 : ℝ) / 3 - ε / 3

/-- Agent `k` pools the two points; every other agent uses the two singleton cells. -/
noncomputable def part2S1ParamPred {n : ℕ} (ε : ℝ)
    (k i : Fin n) (x : Part2S1ParamPoint) : ℝ :=
  if i = k then part2S1ParamKPred ε else part2S1ParamEta ε x

theorem part2S1ParamMass_nonneg (x : Part2S1ParamPoint) :
    0 ≤ part2S1ParamMass x := by
  cases x <;> norm_num [part2S1ParamMass]

theorem part2S1ParamMass_sum :
    (∑ x : Part2S1ParamPoint, part2S1ParamMass x) = 1 := by
  norm_num [part2S1ParamMass]

theorem part2S1ParamEta_range {ε : ℝ} (hε0 : 0 < ε)
    (hεhalf : ε < (1 : ℝ) / 2) (x : Part2S1ParamPoint) :
    0 ≤ part2S1ParamEta ε x ∧ part2S1ParamEta ε x ≤ 1 := by
  cases x <;> simp [part2S1ParamEta] <;> constructor <;> linarith

theorem part2S1ParamKPred_range {ε : ℝ} (hε0 : 0 < ε)
    (hεhalf : ε < (1 : ℝ) / 2) :
    0 < part2S1ParamKPred ε ∧ part2S1ParamKPred ε < 1 := by
  dsimp [part2S1ParamKPred]
  constructor <;> linarith

theorem part2S1ParamKPred_gt_half {ε : ℝ}
    (hεhalf : ε < (1 : ℝ) / 2) :
    (1 : ℝ) / 2 < part2S1ParamKPred ε := by
  dsimp [part2S1ParamKPred]
  linarith

theorem part2S1ParamPred_range {n : ℕ} {ε : ℝ}
    (hε0 : 0 < ε) (hεhalf : ε < (1 : ℝ) / 2)
    (k i : Fin n) (x : Part2S1ParamPoint) :
    0 ≤ part2S1ParamPred ε k i x ∧ part2S1ParamPred ε k i x ≤ 1 := by
  by_cases hik : i = k
  · rw [part2S1ParamPred, if_pos hik]
    exact ⟨(part2S1ParamKPred_range hε0 hεhalf).1.le,
      (part2S1ParamKPred_range hε0 hεhalf).2.le⟩
  · rw [part2S1ParamPred, if_neg hik]
    exact part2S1ParamEta_range hε0 hεhalf x

/-- Every predictor obtained from the source's two-cell partition is calibrated. -/
theorem part2S1Param_calibrated {n : ℕ} {ε : ℝ}
    (hεhalf : ε < (1 : ℝ) / 2) (k : Fin n) :
    ∀ i : Fin n, ∀ r : ℝ,
      eventMass part2S1ParamMass
          (fun x : Part2S1ParamPoint => part2S1ParamPred ε k i x = r) > 0 →
        eventLabelMass part2S1ParamMass (part2S1ParamEta ε)
            (fun x : Part2S1ParamPoint => part2S1ParamPred ε k i x = r) =
          r * eventMass part2S1ParamMass
            (fun x : Part2S1ParamPoint => part2S1ParamPred ε k i x = r) := by
  intro i r _hpos
  have hηne : ε ≠ 1 - ε := by linarith
  by_cases hik : i = k
  · by_cases hr : r = part2S1ParamKPred ε
    · subst r
      simp [eventMass, eventLabelMass, part2S1ParamPred, hik,
        part2S1ParamMass, part2S1ParamEta, part2S1ParamKPred]
      ring
    · have hr' : part2S1ParamKPred ε ≠ r := Ne.symm hr
      simp [eventMass, eventLabelMass, part2S1ParamPred, hik, hr']
  · by_cases hr0 : r = ε
    · subst r
      have hηne' : 1 - ε ≠ ε := Ne.symm hηne
      simp [eventMass, eventLabelMass, part2S1ParamPred, hik,
        part2S1ParamMass, part2S1ParamEta, hηne']
      ring
    · by_cases hr1 : r = 1 - ε
      · subst r
        simp [eventMass, eventLabelMass, part2S1ParamPred, hik,
          part2S1ParamMass, part2S1ParamEta, hηne]
        ring
      · have hr0' : ε ≠ r := Ne.symm hr0
        have hr1' : 1 - ε ≠ r := Ne.symm hr1
        simp [eventMass, eventLabelMass, part2S1ParamPred, hik,
          part2S1ParamMass, part2S1ParamEta, hr0', hr1']

/-- The complete parameterized first auxiliary collaboration setting. -/
noncomputable def part2S1ParamSetting {n : ℕ} (ε : ℝ)
    (hε0 : 0 < ε) (hεhalf : ε < (1 : ℝ) / 2) (k : Fin n) :
    FiniteCollaborationSetting n where
  X := Part2S1ParamPoint
  mass := part2S1ParamMass
  mass_nonneg := part2S1ParamMass_nonneg
  mass_sum := part2S1ParamMass_sum
  eta := part2S1ParamEta ε
  eta_range := part2S1ParamEta_range hε0 hεhalf
  pred := part2S1ParamPred ε k
  pred_range := part2S1ParamPred_range hε0 hεhalf k
  calibrated := part2S1Param_calibrated hεhalf k

theorem part2S1Param_profile_interior {n : ℕ} {ε : ℝ}
    (hε0 : 0 < ε) (hεhalf : ε < (1 : ℝ) / 2)
    (k : Fin n) (x : Part2S1ParamPoint) :
    Interior (fun i : Fin n => part2S1ParamPred ε k i x) := by
  intro i
  by_cases hik : i = k
  · simpa [part2S1ParamPred, hik] using
      part2S1ParamKPred_range hε0 hεhalf
  · cases x <;> simp [part2S1ParamPred, hik, part2S1ParamEta]
    · constructor <;> linarith
    · constructor <;> linarith

theorem part2S1Param_k_pred_ne_half {n : ℕ} {ε : ℝ}
    (hεhalf : ε < (1 : ℝ) / 2) (k : Fin n)
    (x : Part2S1ParamPoint) :
    part2S1ParamPred ε k k x ≠ (1 : ℝ) / 2 := by
  have hgt := part2S1ParamKPred_gt_half hεhalf
  simp only [part2S1ParamPred, if_pos]
  linarith

theorem part2S1Param_agentAccuracy_k {n : ℕ} {ε : ℝ}
    (hε0 : 0 < ε) (hεhalf : ε < (1 : ℝ) / 2) (k : Fin n) :
    (part2S1ParamSetting ε hε0 hεhalf k).agentAccuracy k =
      (2 : ℝ) / 3 - ε / 3 := by
  unfold FiniteCollaborationSetting.agentAccuracy
  change
    (∑ x : Part2S1ParamPoint,
      part2S1ParamMass x *
        pointAccuracy
          (roundProb (part2S1ParamPred ε k k x))
          (part2S1ParamEta ε x)) =
      (2 : ℝ) / 3 - ε / 3
  rw [Fintype.sum_bool]
  have hround : roundProb (part2S1ParamKPred ε) = true :=
    roundProb_eq_true_iff.mpr (part2S1ParamKPred_gt_half hεhalf).le
  simp only [part2S1ParamPred, if_pos]
  rw [hround]
  simp [part2S1ParamMass, part2S1ParamEta, pointAccuracy]
  ring

theorem part2S1Param_agentAccuracy_ne {n : ℕ} {ε : ℝ}
    (hε0 : 0 < ε) (hεhalf : ε < (1 : ℝ) / 2)
    {k i : Fin n} (hik : i ≠ k) :
    (part2S1ParamSetting ε hε0 hεhalf k).agentAccuracy i = 1 - ε := by
  unfold FiniteCollaborationSetting.agentAccuracy
  change
    (∑ x : Part2S1ParamPoint,
      part2S1ParamMass x *
        pointAccuracy
          (roundProb (part2S1ParamPred ε k i x))
          (part2S1ParamEta ε x)) = 1 - ε
  rw [Fintype.sum_bool]
  have hround0 : roundProb ε = false :=
    roundProb_eq_false_iff.mpr hεhalf
  have hround1 : roundProb (1 - ε) = true :=
    roundProb_eq_true_iff.mpr (by linarith)
  simp [part2S1ParamMass, part2S1ParamEta, part2S1ParamPred, hik,
    hround0, hround1, pointAccuracy]
  ring

theorem part2S1Param_strategyAccuracy {n : ℕ} {ε : ℝ}
    (hε0 : 0 < ε) (hεhalf : ε < (1 : ℝ) / 2)
    {C : CollaborationStrategy n} {k : Fin n}
    (hk : DefersAwayFromHalf C k) :
    (part2S1ParamSetting ε hε0 hεhalf k).strategyAccuracy C =
      (2 : ℝ) / 3 - ε / 3 := by
  have hCfalse :
      C (fun i : Fin n => part2S1ParamPred ε k i false) = true := by
    have h := hk (fun i : Fin n => part2S1ParamPred ε k i false)
      (part2S1Param_profile_interior hε0 hεhalf k false)
      (part2S1Param_k_pred_ne_half hεhalf k false)
    have hround : roundProb (part2S1ParamPred ε k k false) = true :=
      by
        simp only [part2S1ParamPred, if_pos]
        exact roundProb_eq_true_iff.mpr
          (part2S1ParamKPred_gt_half hεhalf).le
    simpa [hround] using h
  have hCtrue :
      C (fun i : Fin n => part2S1ParamPred ε k i true) = true := by
    have h := hk (fun i : Fin n => part2S1ParamPred ε k i true)
      (part2S1Param_profile_interior hε0 hεhalf k true)
      (part2S1Param_k_pred_ne_half hεhalf k true)
    have hround : roundProb (part2S1ParamPred ε k k true) = true :=
      by
        simp only [part2S1ParamPred, if_pos]
        exact roundProb_eq_true_iff.mpr
          (part2S1ParamKPred_gt_half hεhalf).le
    simpa [hround] using h
  unfold FiniteCollaborationSetting.strategyAccuracy
  change
    (∑ x : Part2S1ParamPoint,
      part2S1ParamMass x *
        pointAccuracy
          (C (fun i : Fin n => part2S1ParamPred ε k i x))
          (part2S1ParamEta ε x)) =
      (2 : ℝ) / 3 - ε / 3
  rw [Fintype.sum_bool]
  simp [part2S1ParamMass, part2S1ParamEta, hCfalse, hCtrue,
    pointAccuracy]
  ring

/-- The strict Proposition 9 `S₁` gap holds for every source parameter. -/
theorem part2S1Param_accuracy_gap {n : ℕ} {ε : ℝ}
    (hε0 : 0 < ε) (hεhalf : ε < (1 : ℝ) / 2)
    {C : CollaborationStrategy n} {k : Fin n}
    (hk : DefersAwayFromHalf C k) :
    (part2S1ParamSetting ε hε0 hεhalf k).strategyAccuracy C =
        (part2S1ParamSetting ε hε0 hεhalf k).agentAccuracy k ∧
      ∀ i : Fin n, i ≠ k →
        (part2S1ParamSetting ε hε0 hεhalf k).strategyAccuracy C <
          (part2S1ParamSetting ε hε0 hεhalf k).agentAccuracy i := by
  constructor
  · rw [part2S1Param_strategyAccuracy hε0 hεhalf hk,
      part2S1Param_agentAccuracy_k hε0 hεhalf k]
  · intro i hik
    rw [part2S1Param_strategyAccuracy hε0 hεhalf hk,
      part2S1Param_agentAccuracy_ne hε0 hεhalf hik]
    linarith

end PKG25NoFreeLunch
