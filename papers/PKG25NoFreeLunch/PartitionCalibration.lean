import PKG25NoFreeLunch.MainTheorems

/-!
# PKG25 finite partition predictor recipe

The source constructs calibrated predictors by partitioning the input space
and assigning every point in a cell that cell's conditional label-one
probability.  The original Lean development checked only the particular
partitions used by the two adversarial witnesses.  This module proves the
general finite recipe and packages the resulting collaboration setting.
-/

namespace PKG25NoFreeLunch

section OnePartition

variable {X Cell : Type*} [Fintype X] [DecidableEq X]
  [Fintype Cell] [DecidableEq Cell]

/-- Probability mass of one cell in a finite partition. -/
noncomputable def partitionCellMass (mass : X → ℝ) (cell : X → Cell)
    (c : Cell) : ℝ :=
  ∑ x ∈ (Finset.univ : Finset X).filter (fun x => cell x = c), mass x

/-- Label-one mass of one cell in a finite partition. -/
noncomputable def partitionCellLabelMass (mass eta : X → ℝ)
    (cell : X → Cell) (c : Cell) : ℝ :=
  ∑ x ∈ (Finset.univ : Finset X).filter (fun x => cell x = c), mass x * eta x

/-- The cell conditional mean, with the irrelevant zero-mass cell set to zero. -/
noncomputable def partitionCellPrediction (mass eta : X → ℝ)
    (cell : X → Cell) (c : Cell) : ℝ :=
  if partitionCellMass mass cell c = 0 then 0
  else partitionCellLabelMass mass eta cell c /
    partitionCellMass mass cell c

/-- The partition-induced predictor at a point. -/
noncomputable def partitionPredictor (mass eta : X → ℝ)
    (cell : X → Cell) (x : X) : ℝ :=
  partitionCellPrediction mass eta cell (cell x)

theorem partitionCellMass_nonneg (mass : X → ℝ) (cell : X → Cell)
    (hmass : ∀ x, 0 ≤ mass x) (c : Cell) :
    0 ≤ partitionCellMass mass cell c := by
  unfold partitionCellMass
  exact Finset.sum_nonneg fun x _ => hmass x

theorem partitionCellLabelMass_nonneg (mass eta : X → ℝ)
    (cell : X → Cell) (hmass : ∀ x, 0 ≤ mass x)
    (heta : ∀ x, 0 ≤ eta x) (c : Cell) :
    0 ≤ partitionCellLabelMass mass eta cell c := by
  unfold partitionCellLabelMass
  exact Finset.sum_nonneg fun x _ => mul_nonneg (hmass x) (heta x)

theorem partitionCellLabelMass_le_mass (mass eta : X → ℝ)
    (cell : X → Cell) (hmass : ∀ x, 0 ≤ mass x)
    (heta : ∀ x, eta x ≤ 1) (c : Cell) :
    partitionCellLabelMass mass eta cell c ≤ partitionCellMass mass cell c := by
  unfold partitionCellLabelMass partitionCellMass
  exact Finset.sum_le_sum fun x _ => by
    simpa using mul_le_mul_of_nonneg_left (heta x) (hmass x)

theorem partitionCellLabelMass_eq_zero_of_mass_eq_zero
    (mass eta : X → ℝ) (cell : X → Cell)
    (hmass : ∀ x, 0 ≤ mass x) (heta : ∀ x, 0 ≤ eta x)
    (c : Cell) (hzero : partitionCellMass mass cell c = 0) :
    partitionCellLabelMass mass eta cell c = 0 := by
  unfold partitionCellMass at hzero
  unfold partitionCellLabelMass
  refine Finset.sum_eq_zero ?_
  intro x hx
  have hterm_nonneg :
      ∀ y ∈ (Finset.univ : Finset X).filter (fun y => cell y = c),
        0 ≤ mass y := by
    intro y _hy
    exact hmass y
  have hxmass : mass x = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hzero x hx
  simp [hxmass]

theorem partitionCellLabelMass_eq_prediction_mul_mass
    (mass eta : X → ℝ) (cell : X → Cell)
    (hmass : ∀ x, 0 ≤ mass x) (heta : ∀ x, 0 ≤ eta x)
    (c : Cell) :
    partitionCellLabelMass mass eta cell c =
      partitionCellPrediction mass eta cell c *
        partitionCellMass mass cell c := by
  by_cases hzero : partitionCellMass mass cell c = 0
  · rw [hzero, mul_zero,
      partitionCellLabelMass_eq_zero_of_mass_eq_zero
        mass eta cell hmass heta c hzero]
  · simp [partitionCellPrediction, hzero]

theorem partitionCellPrediction_range (mass eta : X → ℝ)
    (cell : X → Cell) (hmass : ∀ x, 0 ≤ mass x)
    (heta : ∀ x, 0 ≤ eta x ∧ eta x ≤ 1) (c : Cell) :
    0 ≤ partitionCellPrediction mass eta cell c ∧
      partitionCellPrediction mass eta cell c ≤ 1 := by
  by_cases hzero : partitionCellMass mass cell c = 0
  · simp [partitionCellPrediction, hzero]
  · have hmass_pos : 0 < partitionCellMass mass cell c :=
      lt_of_le_of_ne (partitionCellMass_nonneg mass cell hmass c)
        (Ne.symm hzero)
    have hlabel_nonneg :
        0 ≤ partitionCellLabelMass mass eta cell c :=
      partitionCellLabelMass_nonneg mass eta cell hmass (fun x => (heta x).1) c
    have hlabel_le :
        partitionCellLabelMass mass eta cell c ≤ partitionCellMass mass cell c :=
      partitionCellLabelMass_le_mass mass eta cell hmass (fun x => (heta x).2) c
    simp only [partitionCellPrediction, hzero, if_false]
    constructor
    · exact div_nonneg hlabel_nonneg hmass_pos.le
    · exact (div_le_one hmass_pos).mpr hlabel_le

/--
The source's arbitrary finite partition recipe is calibrated: pooling any
collection of cells with the same conditional mean preserves that mean.
-/
theorem partitionPredictor_calibrated (mass eta : X → ℝ)
    (cell : X → Cell) (hmass : ∀ x, 0 ≤ mass x)
    (heta : ∀ x, 0 ≤ eta x) (r : ℝ) :
    eventLabelMass mass eta
        (fun x => partitionPredictor mass eta cell x = r) =
      r * eventMass mass
        (fun x => partitionPredictor mass eta cell x = r) := by
  classical
  have hlabel :
      eventLabelMass mass eta
          (fun x => partitionPredictor mass eta cell x = r) =
        ∑ c : Cell,
          if partitionCellPrediction mass eta cell c = r then
            partitionCellLabelMass mass eta cell c else 0 := by
    unfold eventLabelMass
    rw [← Finset.sum_fiberwise (κ := Cell)
      (Finset.univ : Finset X) cell
      (fun x =>
        if partitionPredictor mass eta cell x = r then mass x * eta x else 0)]
    refine Finset.sum_congr rfl ?_
    intro c _hc
    by_cases hpred : partitionCellPrediction mass eta cell c = r
    · rw [if_pos hpred]
      unfold partitionCellLabelMass
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hxc : cell x = c := (Finset.mem_filter.mp hx).2
      simp [partitionPredictor, hxc, hpred]
    · rw [if_neg hpred]
      refine Finset.sum_eq_zero ?_
      intro x hx
      have hxc : cell x = c := (Finset.mem_filter.mp hx).2
      simp [partitionPredictor, hxc, hpred]
  have hmassEvent :
      eventMass mass
          (fun x => partitionPredictor mass eta cell x = r) =
        ∑ c : Cell,
          if partitionCellPrediction mass eta cell c = r then
            partitionCellMass mass cell c else 0 := by
    unfold eventMass
    rw [← Finset.sum_fiberwise (κ := Cell)
      (Finset.univ : Finset X) cell
      (fun x => if partitionPredictor mass eta cell x = r then mass x else 0)]
    refine Finset.sum_congr rfl ?_
    intro c _hc
    by_cases hpred : partitionCellPrediction mass eta cell c = r
    · rw [if_pos hpred]
      unfold partitionCellMass
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hxc : cell x = c := (Finset.mem_filter.mp hx).2
      simp [partitionPredictor, hxc, hpred]
    · rw [if_neg hpred]
      refine Finset.sum_eq_zero ?_
      intro x hx
      have hxc : cell x = c := (Finset.mem_filter.mp hx).2
      simp [partitionPredictor, hxc, hpred]
  rw [hlabel, hmassEvent, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro c _hc
  by_cases hpred : partitionCellPrediction mass eta cell c = r
  · rw [if_pos hpred, if_pos hpred,
      partitionCellLabelMass_eq_prediction_mul_mass
        mass eta cell hmass heta c, hpred]
  · simp [hpred]

end OnePartition

section CollaborationSetting

variable {n : ℕ} {X Cell : Type} [Fintype X] [DecidableEq X]
  [Fintype Cell] [DecidableEq Cell]

/--
Build a finite calibrated collaboration setting from one finite input law and
one partition map per agent.
-/
noncomputable def finitePartitionCollaborationSetting
    (mass eta : X → ℝ) (cell : Fin n → X → Cell)
    (hmass : ∀ x, 0 ≤ mass x) (hmass_sum : ∑ x, mass x = 1)
    (heta : ∀ x, 0 ≤ eta x ∧ eta x ≤ 1) :
    FiniteCollaborationSetting n where
  X := X
  mass := mass
  mass_nonneg := hmass
  mass_sum := hmass_sum
  eta := eta
  eta_range := heta
  pred := fun i => partitionPredictor mass eta (cell i)
  pred_range := fun i x =>
    partitionCellPrediction_range mass eta (cell i) hmass heta (cell i x)
  calibrated := fun i r _hpos =>
    partitionPredictor_calibrated mass eta (cell i) hmass
      (fun x => (heta x).1) r

theorem finitePartitionCollaborationSetting_pred
    (mass eta : X → ℝ) (cell : Fin n → X → Cell)
    (hmass : ∀ x, 0 ≤ mass x) (hmass_sum : ∑ x, mass x = 1)
    (heta : ∀ x, 0 ≤ eta x ∧ eta x ≤ 1)
    (i : Fin n) (x : X) :
    (finitePartitionCollaborationSetting mass eta cell hmass hmass_sum heta).pred i x =
      partitionCellPrediction mass eta (cell i) (cell i x) := rfl

theorem finitePartitionCollaborationSetting_calibrated
    (mass eta : X → ℝ) (cell : Fin n → X → Cell)
    (hmass : ∀ x, 0 ≤ mass x) (hmass_sum : ∑ x, mass x = 1)
    (heta : ∀ x, 0 ≤ eta x ∧ eta x ≤ 1)
    (i : Fin n) (r : ℝ) :
    eventLabelMass mass eta
        (fun x =>
          (finitePartitionCollaborationSetting mass eta cell hmass hmass_sum heta).pred i x = r) =
      r * eventMass mass
        (fun x =>
          (finitePartitionCollaborationSetting mass eta cell hmass hmass_sum heta).pred i x = r) :=
  FiniteCollaborationSetting.calibrated_unconditional
    (finitePartitionCollaborationSetting mass eta cell hmass hmass_sum heta) i r

end CollaborationSetting

end PKG25NoFreeLunch
