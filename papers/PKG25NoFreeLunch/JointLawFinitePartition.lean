import PKG25NoFreeLunch.JointSourceModel

/-!
# PKG25 finite partition calibration for raw joint laws

This module formalizes the finite version of the source paper's partition
construction directly from a joint probability mass function on `X × {0,1}`.
For a cell, the prediction is its true-label mass divided by its total joint
mass, with the value zero on null cells.  No conditional-probability function
on `X` is an input to the construction.
-/

open MeasureTheory

namespace PKG25NoFreeLunch

section RawJointPartition

variable {X Cell : Type} [Fintype X] [DecidableEq X]
  [Fintype Cell] [DecidableEq Cell]

/-- Total raw joint mass assigned to one input point. -/
noncomputable def jointInputMass (joint : PMF (X × Label)) (x : X) : ℝ :=
  (joint (x, true)).toReal + (joint (x, false)).toReal

/-- Raw joint mass of label `true` at one input point. -/
noncomputable def jointTrueInputMass (joint : PMF (X × Label)) (x : X) : ℝ :=
  (joint (x, true)).toReal

/-- The conditional label-one probability reconstructed from a raw joint law. -/
noncomputable def jointInputConditionalProbability (joint : PMF (X × Label))
    (x : X) : ℝ :=
  if jointInputMass joint x = 0 then 0
  else jointTrueInputMass joint x / jointInputMass joint x

/-- Total raw joint mass of one partition cell. -/
noncomputable def jointPartitionCellMass (joint : PMF (X × Label))
    (cell : X → Cell) (c : Cell) : ℝ :=
  ∑ x ∈ (Finset.univ : Finset X).filter (fun x => cell x = c),
    jointInputMass joint x

/-- Raw `true`-label mass of one partition cell. -/
noncomputable def jointPartitionCellTrueMass (joint : PMF (X × Label))
    (cell : X → Cell) (c : Cell) : ℝ :=
  ∑ x ∈ (Finset.univ : Finset X).filter (fun x => cell x = c),
    jointTrueInputMass joint x

/-- The direct conditional label-one probability of a partition cell. -/
noncomputable def jointPartitionCellPrediction (joint : PMF (X × Label))
    (cell : X → Cell) (c : Cell) : ℝ :=
  if jointPartitionCellMass joint cell c = 0 then 0
  else jointPartitionCellTrueMass joint cell c /
    jointPartitionCellMass joint cell c

/-- The raw-joint-law predictor induced by a finite partition. -/
noncomputable def jointPartitionPredictor (joint : PMF (X × Label))
    (cell : X → Cell) (x : X) : ℝ :=
  jointPartitionCellPrediction joint cell (cell x)

theorem jointInputMass_nonneg (joint : PMF (X × Label)) (x : X) :
    0 ≤ jointInputMass joint x := by
  unfold jointInputMass
  positivity

theorem jointTrueInputMass_nonneg (joint : PMF (X × Label)) (x : X) :
    0 ≤ jointTrueInputMass joint x := by
  unfold jointTrueInputMass
  exact ENNReal.toReal_nonneg

theorem jointTrueInputMass_le_inputMass (joint : PMF (X × Label)) (x : X) :
    jointTrueInputMass joint x ≤ jointInputMass joint x := by
  unfold jointTrueInputMass jointInputMass
  linarith [ENNReal.toReal_nonneg (a := joint (x, false))]

theorem jointInputConditionalProbability_range (joint : PMF (X × Label))
    (x : X) :
    0 ≤ jointInputConditionalProbability joint x ∧
      jointInputConditionalProbability joint x ≤ 1 := by
  by_cases hzero : jointInputMass joint x = 0
  · simp [jointInputConditionalProbability, hzero]
  · have hmass_pos : 0 < jointInputMass joint x :=
      lt_of_le_of_ne (jointInputMass_nonneg joint x) (Ne.symm hzero)
    have htrue_nonneg : 0 ≤ jointTrueInputMass joint x :=
      jointTrueInputMass_nonneg joint x
    have htrue_le : jointTrueInputMass joint x ≤ jointInputMass joint x :=
      jointTrueInputMass_le_inputMass joint x
    simp only [jointInputConditionalProbability, hzero, if_false]
    constructor
    · exact div_nonneg htrue_nonneg hmass_pos.le
    · exact (div_le_one hmass_pos).mpr htrue_le

theorem jointTrueInputMass_eq_conditional_mul_inputMass
    (joint : PMF (X × Label)) (x : X) :
    jointTrueInputMass joint x =
      jointInputConditionalProbability joint x * jointInputMass joint x := by
  by_cases hzero : jointInputMass joint x = 0
  · rw [hzero, mul_zero]
    have htrue_nonneg : 0 ≤ jointTrueInputMass joint x :=
      jointTrueInputMass_nonneg joint x
    have htrue_le : jointTrueInputMass joint x ≤ jointInputMass joint x :=
      jointTrueInputMass_le_inputMass joint x
    linarith
  · rw [jointInputConditionalProbability, if_neg hzero, div_mul_cancel₀ _ hzero]

theorem jointInputMass_sum (joint : PMF (X × Label)) :
    ∑ x : X, jointInputMass joint x = 1 := by
  have hsum : (∑ z : X × Label, joint z) = 1 := by
    rw [← tsum_fintype (L := SummationFilter.unconditional (X × Label))]
    exact joint.tsum_coe
  calc
    (∑ x : X, jointInputMass joint x) =
        ∑ z : X × Label, (joint z).toReal := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl ?_
      intro x _hx
      rw [Fintype.sum_bool]
      simp [jointInputMass, add_comm]
    _ = (∑ z : X × Label, joint z).toReal := by
      rw [ENNReal.toReal_sum (fun z _ => joint.apply_ne_top z)]
    _ = 1 := by rw [hsum]; norm_num

theorem jointPartitionCellMass_nonneg (joint : PMF (X × Label))
    (cell : X → Cell) (c : Cell) :
    0 ≤ jointPartitionCellMass joint cell c := by
  unfold jointPartitionCellMass
  exact Finset.sum_nonneg fun x _ => jointInputMass_nonneg joint x

theorem jointPartitionCellTrueMass_nonneg (joint : PMF (X × Label))
    (cell : X → Cell) (c : Cell) :
    0 ≤ jointPartitionCellTrueMass joint cell c := by
  unfold jointPartitionCellTrueMass
  exact Finset.sum_nonneg fun x _ => jointTrueInputMass_nonneg joint x

theorem jointPartitionCellTrueMass_le_mass (joint : PMF (X × Label))
    (cell : X → Cell) (c : Cell) :
    jointPartitionCellTrueMass joint cell c ≤ jointPartitionCellMass joint cell c := by
  unfold jointPartitionCellTrueMass jointPartitionCellMass
  exact Finset.sum_le_sum fun x _ => jointTrueInputMass_le_inputMass joint x

theorem jointPartitionCellTrueMass_eq_zero_of_mass_eq_zero
    (joint : PMF (X × Label)) (cell : X → Cell) (c : Cell)
    (hzero : jointPartitionCellMass joint cell c = 0) :
    jointPartitionCellTrueMass joint cell c = 0 := by
  unfold jointPartitionCellMass at hzero
  unfold jointPartitionCellTrueMass
  refine Finset.sum_eq_zero ?_
  intro x hx
  have hterm_nonneg :
      ∀ y ∈ (Finset.univ : Finset X).filter (fun y => cell y = c),
        0 ≤ jointInputMass joint y := by
    intro y _hy
    exact jointInputMass_nonneg joint y
  have hxmass : jointInputMass joint x = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hzero x hx
  have htrue_nonneg := jointTrueInputMass_nonneg joint x
  have htrue_le := jointTrueInputMass_le_inputMass joint x
  linarith

theorem jointPartitionCellTrueMass_eq_prediction_mul_mass
    (joint : PMF (X × Label)) (cell : X → Cell) (c : Cell) :
    jointPartitionCellTrueMass joint cell c =
      jointPartitionCellPrediction joint cell c *
        jointPartitionCellMass joint cell c := by
  by_cases hzero : jointPartitionCellMass joint cell c = 0
  · rw [hzero, mul_zero,
      jointPartitionCellTrueMass_eq_zero_of_mass_eq_zero joint cell c hzero]
  · simp [jointPartitionCellPrediction, hzero]

theorem jointPartitionCellPrediction_range (joint : PMF (X × Label))
    (cell : X → Cell) (c : Cell) :
    0 ≤ jointPartitionCellPrediction joint cell c ∧
      jointPartitionCellPrediction joint cell c ≤ 1 := by
  by_cases hzero : jointPartitionCellMass joint cell c = 0
  · simp [jointPartitionCellPrediction, hzero]
  · have hmass_pos : 0 < jointPartitionCellMass joint cell c :=
      lt_of_le_of_ne (jointPartitionCellMass_nonneg joint cell c) (Ne.symm hzero)
    have hlabel_nonneg : 0 ≤ jointPartitionCellTrueMass joint cell c :=
      jointPartitionCellTrueMass_nonneg joint cell c
    have hlabel_le : jointPartitionCellTrueMass joint cell c ≤
        jointPartitionCellMass joint cell c :=
      jointPartitionCellTrueMass_le_mass joint cell c
    simp only [jointPartitionCellPrediction, hzero, if_false]
    constructor
    · exact div_nonneg hlabel_nonneg hmass_pos.le
    · exact (div_le_one hmass_pos).mpr hlabel_le

theorem jointPMF_true_event_sum (joint : PMF (X × Label))
    (A : X → Prop) [DecidablePred A] :
    (∑ z : X × Label,
      (joint z).toReal * (if A z.1 ∧ z.2 = true then 1 else 0)) =
      ∑ x : X, if A x then jointTrueInputMass joint x else 0 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  rw [Fintype.sum_bool]
  by_cases hA : A x
  · simp [hA, jointTrueInputMass]
  · simp [hA]

theorem jointPMF_event_sum (joint : PMF (X × Label))
    (A : X → Prop) [DecidablePred A] (f : X → ℝ) :
    (∑ z : X × Label,
      (joint z).toReal * (if A z.1 then f z.1 else 0)) =
      ∑ x : X, if A x then jointInputMass joint x * f x else 0 := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  rw [Fintype.sum_bool]
  by_cases hA : A x
  · simp [hA, jointInputMass]
    ring
  · simp [hA]

/--
The finite partition predictor is calibrated directly under the input-label
joint PMF.  This is the finite raw-joint version of the source partition
construction, stated for every set of reported probability values.
-/
theorem jointPartitionPredictor_calibrated_events
    (joint : PMF (X × Label)) (cell : X → Cell) (A : Set ℝ)
    [DecidablePred fun x : X => jointPartitionPredictor joint cell x ∈ A] :
    (∑ z : X × Label,
      (joint z).toReal *
        (if jointPartitionPredictor joint cell z.1 ∈ A ∧ z.2 = true then 1 else 0)) =
      ∑ z : X × Label,
        (joint z).toReal *
          (if jointPartitionPredictor joint cell z.1 ∈ A then
            jointPartitionPredictor joint cell z.1 else 0) := by
  classical
  have hfiber (f : X → ℝ) :
      (∑ x : X, f x) =
        ∑ c ∈ (Finset.univ : Finset X).image cell,
          ∑ x ∈ (Finset.univ : Finset X) with cell x = c, f x := by
    symm
    exact Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ) (t := (Finset.univ : Finset X).image cell)
      (g := cell)
      (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩) f
  have hcell_true (c : Cell) :
      (∑ x ∈ (Finset.univ : Finset X) with cell x = c,
        if jointPartitionPredictor joint cell x ∈ A then
          jointTrueInputMass joint x else 0) =
        if jointPartitionCellPrediction joint cell c ∈ A then
          jointPartitionCellTrueMass joint cell c else 0 := by
    by_cases hA : jointPartitionCellPrediction joint cell c ∈ A
    · rw [if_pos hA]
      unfold jointPartitionCellTrueMass
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hxc : cell x = c := (Finset.mem_filter.mp hx).2
      simp [jointPartitionPredictor, hxc, hA]
    · rw [if_neg hA]
      refine Finset.sum_eq_zero ?_
      intro x hx
      have hxc : cell x = c := (Finset.mem_filter.mp hx).2
      simp [jointPartitionPredictor, hxc, hA]
  have hcell_mass (c : Cell) :
      (∑ x ∈ (Finset.univ : Finset X) with cell x = c,
        if jointPartitionPredictor joint cell x ∈ A then
          jointInputMass joint x * jointPartitionPredictor joint cell x else 0) =
        if jointPartitionCellPrediction joint cell c ∈ A then
          jointPartitionCellMass joint cell c *
            jointPartitionCellPrediction joint cell c else 0 := by
    by_cases hA : jointPartitionCellPrediction joint cell c ∈ A
    · rw [if_pos hA]
      unfold jointPartitionCellMass
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hxc : cell x = c := (Finset.mem_filter.mp hx).2
      simp [jointPartitionPredictor, hxc, hA]
    · rw [if_neg hA]
      refine Finset.sum_eq_zero ?_
      intro x hx
      have hxc : cell x = c := (Finset.mem_filter.mp hx).2
      simp [jointPartitionPredictor, hxc, hA]
  have hcal :
      (∑ x : X,
        if jointPartitionPredictor joint cell x ∈ A then
          jointTrueInputMass joint x else 0) =
        ∑ x : X,
          if jointPartitionPredictor joint cell x ∈ A then
            jointInputMass joint x * jointPartitionPredictor joint cell x else 0 := by
    rw [hfiber, hfiber]
    refine Finset.sum_congr rfl ?_
    intro c _hc
    rw [hcell_true c, hcell_mass c]
    by_cases hA : jointPartitionCellPrediction joint cell c ∈ A
    · rw [if_pos hA, if_pos hA,
        jointPartitionCellTrueMass_eq_prediction_mul_mass]
      ring
    · simp [hA]
  calc
    (∑ z : X × Label,
        (joint z).toReal *
          (if jointPartitionPredictor joint cell z.1 ∈ A ∧ z.2 = true then 1 else 0)) =
        ∑ x : X,
          if jointPartitionPredictor joint cell x ∈ A then
            jointTrueInputMass joint x else 0 :=
      jointPMF_true_event_sum joint
        (fun x => jointPartitionPredictor joint cell x ∈ A)
    _ = ∑ x : X,
        if jointPartitionPredictor joint cell x ∈ A then
          jointInputMass joint x * jointPartitionPredictor joint cell x else 0 := hcal
    _ = ∑ z : X × Label,
        (joint z).toReal *
          (if jointPartitionPredictor joint cell z.1 ∈ A then
            jointPartitionPredictor joint cell z.1 else 0) := by
      exact (jointPMF_event_sum joint
        (fun x => jointPartitionPredictor joint cell x ∈ A)
        (jointPartitionPredictor joint cell)).symm

/-- The pointwise range guarantee for the direct raw-joint partition predictor. -/
theorem jointPartitionPredictor_range (joint : PMF (X × Label))
    (cell : X → Cell) (x : X) :
    0 ≤ jointPartitionPredictor joint cell x ∧
      jointPartitionPredictor joint cell x ≤ 1 :=
  jointPartitionCellPrediction_range joint cell (cell x)

/--
The same calibration identity expressed as expectations under the raw PMF's
measure.  The measurability hypothesis is retained to match the source-model
interface, although every set is measurable on this finite discrete space.
-/
theorem jointPartitionPredictor_calibrated_events_measure
    (joint : PMF (X × Label)) (cell : X → Cell) (A : Set ℝ)
    [MeasurableSpace X] [MeasurableSingletonClass X]
    (_hA : MeasurableSet A) :
    (∫ z : X × Label,
      ({z | jointPartitionPredictor joint cell z.1 ∈ A ∧ z.2 = true}.indicator
        fun _ => (1 : ℝ)) z ∂joint.toMeasure) =
      ∫ z : X × Label,
        ({z | jointPartitionPredictor joint cell z.1 ∈ A}.indicator
          fun z => jointPartitionPredictor joint cell z.1) z ∂joint.toMeasure := by
  classical
  rw [PMF.integral_eq_sum, PMF.integral_eq_sum]
  simp only [smul_eq_mul, Set.indicator_apply]
  exact jointPartitionPredictor_calibrated_events joint cell A

/--
One finite partition per agent, packaged directly as a source-compatible raw
joint-law collaboration setting.  Its joint measure is exactly `joint.toMeasure`.
-/
noncomputable def finiteJointLawPartitionCollaborationSetting {n : ℕ}
    (joint : PMF (X × Label)) (cell : Fin n → X → Cell) :
    JointLawCollaborationSetting n := by
  letI : MeasurableSpace X := ⊤
  exact
    { X := X
      measurableSpaceX := inferInstance
      joint := joint.toMeasure
      isProbability := inferInstance
      pred := fun i => jointPartitionPredictor joint (cell i)
      pred_range := fun i x => jointPartitionPredictor_range joint (cell i) x
      pred_measurable := fun i => measurable_of_finite (jointPartitionPredictor joint (cell i))
      calibrated_events := by
        intro i A hA
        exact jointPartitionPredictor_calibrated_events_measure joint (cell i) A hA }

theorem finiteJointLawPartitionCollaborationSetting_pred {n : ℕ}
    (joint : PMF (X × Label)) (cell : Fin n → X → Cell)
    (i : Fin n) (x : X) :
    (finiteJointLawPartitionCollaborationSetting joint cell).pred i x =
      jointPartitionPredictor joint (cell i) x := rfl

end RawJointPartition

end PKG25NoFreeLunch
