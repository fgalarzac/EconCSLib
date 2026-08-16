import PKG25NoFreeLunch.JointSourceModel

/-!
# PKG25 finite measurable partitions for raw joint laws

The source paper constructs calibrated predictors by partitioning the input
space and assigning a cell its conditional label-one probability.  This
module performs that construction directly from a measure on `X × Label`:
the numerator is the joint mass of the cell with label `true`, and the
denominator is the joint mass of the cell with either label.  No conditional
probability function is introduced.
-/

open MeasureTheory

namespace PKG25NoFreeLunch

section OneJointLawPartition

variable {X Cell : Type*} [MeasurableSpace X]

/-- The input-label event that the input lies in a given partition cell. -/
def jointLawPartitionInputEvent (cell : X → Cell) (c : Cell) : Set (X × Label) :=
  {z | cell z.1 = c}

/-- The input-label event that the input lies in a cell and its label is true. -/
def jointLawPartitionTrueEvent (cell : X → Cell) (c : Cell) : Set (X × Label) :=
  {z | cell z.1 = c ∧ z.2 = true}

theorem jointLawPartitionInputEvent_measurable (cell : X → Cell)
    [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    (hcell : Measurable cell) (c : Cell) :
    MeasurableSet (jointLawPartitionInputEvent cell c) := by
  exact (hcell.comp measurable_fst) (measurableSet_singleton c)

theorem jointLawPartitionTrueEvent_measurable (cell : X → Cell)
    [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    (hcell : Measurable cell) (c : Cell) :
    MeasurableSet (jointLawPartitionTrueEvent cell c) := by
  exact (jointLawPartitionInputEvent_measurable cell hcell c).inter
    (measurable_snd (measurableSet_singleton true))

omit [MeasurableSpace X] in
theorem jointLawPartitionTrueEvent_subset_input (cell : X → Cell) (c : Cell) :
    jointLawPartitionTrueEvent cell c ⊆ jointLawPartitionInputEvent cell c := by
  intro z hz
  exact hz.1

/-- Total raw joint-law mass of an input partition cell. -/
noncomputable def jointLawPartitionCellMass (joint : Measure (X × Label))
    (cell : X → Cell) (c : Cell) : ℝ :=
  joint.real (jointLawPartitionInputEvent cell c)

/-- Raw joint-law mass of a cell with true label. -/
noncomputable def jointLawPartitionCellTrueMass (joint : Measure (X × Label))
    (cell : X → Cell) (c : Cell) : ℝ :=
  joint.real (jointLawPartitionTrueEvent cell c)

/-- The source cell conditional label-one probability, zero on null cells. -/
noncomputable def jointLawPartitionCellPrediction (joint : Measure (X × Label))
    (cell : X → Cell) (c : Cell) : ℝ :=
  if jointLawPartitionCellMass joint cell c = 0 then 0
  else jointLawPartitionCellTrueMass joint cell c /
    jointLawPartitionCellMass joint cell c

/-- The partition-induced prediction at an input. -/
noncomputable def jointLawPartitionPredictor (joint : Measure (X × Label))
    (cell : X → Cell) (x : X) : ℝ :=
  jointLawPartitionCellPrediction joint cell (cell x)

theorem jointLawPartitionCellMass_nonneg (joint : Measure (X × Label))
    (cell : X → Cell) (c : Cell) :
    0 ≤ jointLawPartitionCellMass joint cell c := by
  exact measureReal_nonneg

theorem jointLawPartitionCellTrueMass_nonneg (joint : Measure (X × Label))
    (cell : X → Cell) (c : Cell) :
    0 ≤ jointLawPartitionCellTrueMass joint cell c := by
  exact measureReal_nonneg

theorem jointLawPartitionCellTrueMass_le_mass (joint : Measure (X × Label))
    [IsFiniteMeasure joint] (cell : X → Cell) (c : Cell) :
    jointLawPartitionCellTrueMass joint cell c ≤
      jointLawPartitionCellMass joint cell c := by
  unfold jointLawPartitionCellTrueMass jointLawPartitionCellMass
  exact measureReal_mono (jointLawPartitionTrueEvent_subset_input cell c)

theorem jointLawPartitionCellTrueMass_eq_prediction_mul_mass
    (joint : Measure (X × Label)) [IsFiniteMeasure joint]
    (cell : X → Cell) (c : Cell) :
    jointLawPartitionCellTrueMass joint cell c =
      jointLawPartitionCellPrediction joint cell c *
        jointLawPartitionCellMass joint cell c := by
  by_cases hzero : jointLawPartitionCellMass joint cell c = 0
  · have htrue_zero : jointLawPartitionCellTrueMass joint cell c = 0 := by
      apply le_antisymm
      · simpa [hzero] using
          (jointLawPartitionCellTrueMass_le_mass joint cell c)
      · exact jointLawPartitionCellTrueMass_nonneg joint cell c
    simp [jointLawPartitionCellPrediction, hzero, htrue_zero]
  · rw [jointLawPartitionCellPrediction, if_neg hzero]
    exact (div_mul_cancel₀ _ hzero).symm

theorem jointLawPartitionCellPrediction_range
    (joint : Measure (X × Label)) [IsFiniteMeasure joint]
    (cell : X → Cell) (c : Cell) :
    0 ≤ jointLawPartitionCellPrediction joint cell c ∧
      jointLawPartitionCellPrediction joint cell c ≤ 1 := by
  by_cases hzero : jointLawPartitionCellMass joint cell c = 0
  · simp [jointLawPartitionCellPrediction, hzero]
  · have hmass_pos : 0 < jointLawPartitionCellMass joint cell c :=
      lt_of_le_of_ne (jointLawPartitionCellMass_nonneg joint cell c) (Ne.symm hzero)
    have htrue_nonneg : 0 ≤ jointLawPartitionCellTrueMass joint cell c :=
      jointLawPartitionCellTrueMass_nonneg joint cell c
    have htrue_le : jointLawPartitionCellTrueMass joint cell c ≤
        jointLawPartitionCellMass joint cell c :=
      jointLawPartitionCellTrueMass_le_mass joint cell c
    rw [jointLawPartitionCellPrediction, if_neg hzero]
    exact ⟨div_nonneg htrue_nonneg hmass_pos.le,
      (div_le_one hmass_pos).mpr htrue_le⟩

theorem jointLawPartitionPredictor_measurable (joint : Measure (X × Label))
    [Fintype Cell] [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    (cell : X → Cell) (hcell : Measurable cell) :
    Measurable (jointLawPartitionPredictor joint cell) := by
  exact (measurable_of_finite (jointLawPartitionCellPrediction joint cell)).comp hcell

/--
The arbitrary finite-partition predictor is event-calibrated under the raw
joint law.  Cells with the same reported probability are combined, so this
also covers ties among the cell conditional probabilities.
-/
theorem jointLawPartitionPredictor_calibrated_events
    (joint : Measure (X × Label)) [IsFiniteMeasure joint]
    [Fintype Cell] [MeasurableSpace Cell] [MeasurableSingletonClass Cell]
    (cell : X → Cell) (hcell : Measurable cell)
    (A : Set ℝ) (_hA : MeasurableSet A) :
    (∫ z : X × Label,
      ({z | jointLawPartitionPredictor joint cell z.1 ∈ A ∧ z.2 = true}.indicator
        (fun _ => (1 : ℝ))) z ∂joint) =
      ∫ z : X × Label,
        ({z | jointLawPartitionPredictor joint cell z.1 ∈ A}.indicator
          (fun z => jointLawPartitionPredictor joint cell z.1)) z ∂joint := by
  classical
  let q : Cell → ℝ := jointLawPartitionCellPrediction joint cell
  have hleft :
      (fun z : X × Label =>
        ({z | jointLawPartitionPredictor joint cell z.1 ∈ A ∧ z.2 = true}.indicator
          (fun _ => (1 : ℝ))) z) =
        (fun z =>
          ∑ c : Cell,
            if q c ∈ A then
              (jointLawPartitionTrueEvent cell c).indicator (fun _ => (1 : ℝ)) z
            else 0) := by
    funext z
    rw [Fintype.sum_eq_single (cell z.1)]
    · by_cases hq : q (cell z.1) ∈ A
      · by_cases htrue : z.2 = true
        · simp [jointLawPartitionPredictor, q, jointLawPartitionTrueEvent, hq, htrue]
        · simp [jointLawPartitionPredictor, q, jointLawPartitionTrueEvent, hq, htrue]
      · by_cases htrue : z.2 = true
        · simp [jointLawPartitionPredictor, q, hq, htrue]
        · simp [jointLawPartitionPredictor, q, hq, htrue]
    · intro c hne
      simp [jointLawPartitionTrueEvent, Ne.symm hne]
  have hright :
      (fun z : X × Label =>
        ({z | jointLawPartitionPredictor joint cell z.1 ∈ A}.indicator
          (fun z => jointLawPartitionPredictor joint cell z.1)) z) =
        (fun z =>
          ∑ c : Cell,
            if q c ∈ A then
              (jointLawPartitionInputEvent cell c).indicator (fun _ => q c) z
            else 0) := by
    funext z
    rw [Fintype.sum_eq_single (cell z.1)]
    · simp [jointLawPartitionPredictor, q, jointLawPartitionInputEvent,
        Set.indicator_apply]
    · intro c hne
      simp [jointLawPartitionInputEvent, Ne.symm hne]
  rw [hleft, hright, integral_finset_sum, integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro c _hc
    by_cases hcA : q c ∈ A
    · simp only [hcA, if_true]
      have htrue_integral :
          (∫ z : X × Label,
            (jointLawPartitionTrueEvent cell c).indicator (fun _ => (1 : ℝ)) z
              ∂joint) = joint.real (jointLawPartitionTrueEvent cell c) := by
        simpa using (integral_indicator_one (μ := joint)
          (jointLawPartitionTrueEvent_measurable cell hcell c))
      rw [htrue_integral,
        integral_indicator_const (q c)
          (jointLawPartitionInputEvent_measurable cell hcell c)]
      rw [← jointLawPartitionCellTrueMass,
        jointLawPartitionCellTrueMass_eq_prediction_mul_mass]
      simp [q, jointLawPartitionCellMass, smul_eq_mul, mul_comm]
    · simp [hcA]
  · intro c _hc
    by_cases hcA : q c ∈ A
    · simp [hcA]
      exact (integrable_const (q c)).indicator
        (jointLawPartitionInputEvent_measurable cell hcell c)
    · simp [hcA]
  · intro c _hc
    by_cases hcA : q c ∈ A
    · simp [hcA]
      exact (integrable_const (1 : ℝ)).indicator
        (jointLawPartitionTrueEvent_measurable cell hcell c)
    · simp [hcA]

end OneJointLawPartition

/-! ## One finite measurable partition per agent -/

section JointLawPartitionSetting

variable {n : ℕ} {Cell : Type*}
  [Fintype Cell] [MeasurableSpace Cell] [MeasurableSingletonClass Cell]

/--
Apply one finite measurable input partition per agent to a raw joint-law
setting.  The underlying joint law is unchanged; only the calibrated
predictors are replaced by the source's cell conditional probabilities.
-/
noncomputable def jointLawPartitionCollaborationSetting
    (S : JointLawCollaborationSetting n)
    (cell : Fin n → S.X → Cell) (hcell : ∀ i, Measurable (cell i)) :
    JointLawCollaborationSetting n where
  X := S.X
  measurableSpaceX := inferInstance
  joint := S.joint
  isProbability := S.isProbability
  pred := fun i => jointLawPartitionPredictor S.joint (cell i)
  pred_range := by
    intro i x
    letI : IsProbabilityMeasure S.joint := S.isProbability
    simpa [jointLawPartitionPredictor] using
      (jointLawPartitionCellPrediction_range S.joint (cell i) (cell i x))
  pred_measurable := by
    intro i
    exact jointLawPartitionPredictor_measurable S.joint (cell i) (hcell i)
  calibrated_events := by
    intro i A hA
    letI : IsProbabilityMeasure S.joint := S.isProbability
    simpa [jointLawPartitionPredictor] using
      (jointLawPartitionPredictor_calibrated_events S.joint (cell i) (hcell i) A hA)

end JointLawPartitionSetting

end PKG25NoFreeLunch
