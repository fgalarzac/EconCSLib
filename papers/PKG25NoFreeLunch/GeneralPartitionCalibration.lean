import PKG25NoFreeLunch.GeneralProbabilitySetting

/-!
# PKG25 legacy eta-based partition calibration

This historical module works over the retired `mu + eta` representation from
`GeneralProbabilitySetting.lean`.  It is not a source-facing proof of the
paper's raw-joint partition recipe because its calibration semantics inherit
the atomless exact-fiber defect of that representation.  Use
`JointLawGeneralPartition.lean` and `JointLawDependentPartition.lean` for new
paper-facing partition claims.
-/

open MeasureTheory

namespace PKG25NoFreeLunch

section OneGeneralPartition

variable {X Cell : Type*} [MeasurableSpace X]
  [Fintype Cell] [MeasurableSpace Cell] [MeasurableSingletonClass Cell]

/-- One measurable cell of a finite partition. -/
def probabilityPartitionFiber (cell : X → Cell) (c : Cell) : Set X :=
  {x | cell x = c}

theorem probabilityPartitionFiber_measurable (cell : X → Cell)
    (hcell : Measurable cell) (c : Cell) :
    MeasurableSet (probabilityPartitionFiber cell c) := by
  exact hcell (measurableSet_singleton c)

/-- Probability mass of a partition cell. -/
noncomputable def probabilityPartitionCellMass (μ : Measure X)
    (cell : X → Cell) (c : Cell) : ℝ :=
  μ.real (probabilityPartitionFiber cell c)

/-- Label-one mass of a partition cell. -/
noncomputable def probabilityPartitionCellLabelMass (μ : Measure X)
    (eta : X → ℝ) (cell : X → Cell) (c : Cell) : ℝ :=
  ∫ x in probabilityPartitionFiber cell c, eta x ∂μ

/-- Conditional label-one probability of a cell, with zero on null cells. -/
noncomputable def probabilityPartitionCellPrediction (μ : Measure X)
    (eta : X → ℝ) (cell : X → Cell) (c : Cell) : ℝ :=
  if probabilityPartitionCellMass μ cell c = 0 then 0
  else probabilityPartitionCellLabelMass μ eta cell c /
    probabilityPartitionCellMass μ cell c

/-- The partition-induced calibrated predictor. -/
noncomputable def probabilityPartitionPredictor (μ : Measure X)
    (eta : X → ℝ) (cell : X → Cell) (x : X) : ℝ :=
  probabilityPartitionCellPrediction μ eta cell (cell x)

theorem probabilityPartitionCellMass_nonneg (μ : Measure X)
    (cell : X → Cell) (c : Cell) :
    0 ≤ probabilityPartitionCellMass μ cell c := by
  exact measureReal_nonneg

theorem probabilityPartitionCellLabelMass_nonneg (μ : Measure X)
    (eta : X → ℝ) (cell : X → Cell)
    (heta : ∀ x, 0 ≤ eta x) (c : Cell) :
    0 ≤ probabilityPartitionCellLabelMass μ eta cell c := by
  unfold probabilityPartitionCellLabelMass
  exact integral_nonneg_of_ae (.of_forall fun x => heta x)

theorem probabilityPartitionCellLabelMass_le_mass (μ : Measure X)
    [IsFiniteMeasure μ] (eta : X → ℝ) (cell : X → Cell)
    (heta_int : Integrable eta μ) (heta : ∀ x, eta x ≤ 1) (c : Cell) :
    probabilityPartitionCellLabelMass μ eta cell c ≤
      probabilityPartitionCellMass μ cell c := by
  unfold probabilityPartitionCellLabelMass probabilityPartitionCellMass
  calc
    (∫ x in probabilityPartitionFiber cell c, eta x ∂μ) ≤
        ∫ _x in probabilityPartitionFiber cell c, (1 : ℝ) ∂μ := by
      exact integral_mono_ae heta_int.integrableOn (integrable_const _)
        (.of_forall fun x => heta x)
    _ = μ.real (probabilityPartitionFiber cell c) :=
      setIntegral_one_eq_measureReal

theorem probabilityPartitionCellLabelMass_eq_prediction_mul_mass
    (μ : Measure X) [IsFiniteMeasure μ]
    (eta : X → ℝ) (cell : X → Cell) (c : Cell) :
    probabilityPartitionCellLabelMass μ eta cell c =
      probabilityPartitionCellPrediction μ eta cell c *
        probabilityPartitionCellMass μ cell c := by
  by_cases hzero : probabilityPartitionCellMass μ cell c = 0
  · have hμzero : μ (probabilityPartitionFiber cell c) = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top μ _)).mp hzero
    simp [probabilityPartitionCellPrediction, hzero,
      probabilityPartitionCellLabelMass, hμzero]
  · rw [probabilityPartitionCellPrediction, if_neg hzero]
    exact (div_mul_cancel₀ _ hzero).symm

theorem probabilityPartitionCellPrediction_range
    (μ : Measure X) [IsFiniteMeasure μ]
    (eta : X → ℝ) (cell : X → Cell)
    (heta_int : Integrable eta μ)
    (heta : ∀ x, 0 ≤ eta x ∧ eta x ≤ 1) (c : Cell) :
    0 ≤ probabilityPartitionCellPrediction μ eta cell c ∧
      probabilityPartitionCellPrediction μ eta cell c ≤ 1 := by
  by_cases hzero : probabilityPartitionCellMass μ cell c = 0
  · simp [probabilityPartitionCellPrediction, hzero]
  · have hmass_pos : 0 < probabilityPartitionCellMass μ cell c :=
      lt_of_le_of_ne (probabilityPartitionCellMass_nonneg μ cell c)
        (Ne.symm hzero)
    have hlabel_nonneg :
        0 ≤ probabilityPartitionCellLabelMass μ eta cell c :=
      probabilityPartitionCellLabelMass_nonneg μ eta cell
        (fun x => (heta x).1) c
    have hlabel_le :
        probabilityPartitionCellLabelMass μ eta cell c ≤
          probabilityPartitionCellMass μ cell c :=
      probabilityPartitionCellLabelMass_le_mass μ eta cell heta_int
        (fun x => (heta x).2) c
    rw [probabilityPartitionCellPrediction, if_neg hzero]
    exact ⟨div_nonneg hlabel_nonneg hmass_pos.le,
      (div_le_one hmass_pos).mpr hlabel_le⟩

theorem probabilityPartitionPredictor_measurable
    (μ : Measure X) (eta : X → ℝ) (cell : X → Cell)
    (hcell : Measurable cell) :
    Measurable (probabilityPartitionPredictor μ eta cell) := by
  exact (measurable_of_finite
    (probabilityPartitionCellPrediction μ eta cell)).comp hcell

/--
The arbitrary-probability-space partition recipe is calibrated.  Several
partition cells may have the same conditional mean; the proof sums all such
fibers and uses the same ratio on each one.
-/
theorem probabilityPartitionPredictor_calibrated
    (μ : Measure X) [IsFiniteMeasure μ]
    (eta : X → ℝ) (cell : X → Cell)
    (hcell : Measurable cell) (heta_int : Integrable eta μ)
    (p : ℝ) :
    (∫ x, ({x | probabilityPartitionPredictor μ eta cell x = p}.indicator eta) x ∂μ) =
      p * ∫ x,
        ({x | probabilityPartitionPredictor μ eta cell x = p}.indicator
          (fun _ => (1 : ℝ))) x ∂μ := by
  classical
  let q : Cell → ℝ := probabilityPartitionCellPrediction μ eta cell
  have hdecomp (f : X → ℝ) :
      (fun x =>
          ({x | probabilityPartitionPredictor μ eta cell x = p}.indicator f) x) =
        (fun x =>
          ∑ c : Cell,
            if q c = p then
              (probabilityPartitionFiber cell c).indicator f x else 0) := by
    funext x
    rw [Fintype.sum_eq_single (cell x)]
    · simp [probabilityPartitionPredictor, q, probabilityPartitionFiber,
        Set.indicator_apply]
    · intro c hne
      simp [probabilityPartitionFiber, Ne.symm hne]
  rw [hdecomp eta, hdecomp (fun _ => (1 : ℝ))]
  rw [integral_finset_sum, integral_finset_sum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro c _hc
    by_cases hq : q c = p
    · simp only [hq, if_true]
      rw [integral_indicator
          (probabilityPartitionFiber_measurable cell hcell c),
        integral_indicator
          (probabilityPartitionFiber_measurable cell hcell c)]
      rw [← probabilityPartitionCellLabelMass,
        probabilityPartitionCellLabelMass_eq_prediction_mul_mass,
        setIntegral_one_eq_measureReal]
      change q c * μ.real (probabilityPartitionFiber cell c) =
        p * μ.real (probabilityPartitionFiber cell c)
      rw [hq]
    · simp [hq]
  · intro c _hc
    by_cases hq : q c = p
    · simp [hq]
      exact (integrable_const (1 : ℝ)).indicator
        (probabilityPartitionFiber_measurable cell hcell c)
    · simp [hq]
  · intro c _hc
    by_cases hq : q c = p
    · simp [hq]
      exact heta_int.indicator
        (probabilityPartitionFiber_measurable cell hcell c)
    · simp [hq]

/--
The partition predictor also satisfies the measure-theoretic calibration
identity on every measurable collection of reported probabilities.  This is
the non-vacuous arbitrary-space form of `E[eta | P] = P` used by the source
model.
-/
theorem probabilityPartitionPredictor_calibrated_events
    (μ : Measure X) [IsFiniteMeasure μ]
    (eta : X → ℝ) (cell : X → Cell)
    (hcell : Measurable cell) (heta_int : Integrable eta μ)
    (A : Set ℝ) (_hA : MeasurableSet A) :
    (∫ x,
        ({x | probabilityPartitionPredictor μ eta cell x ∈ A}.indicator eta) x
          ∂μ) =
      ∫ x,
        ({x | probabilityPartitionPredictor μ eta cell x ∈ A}.indicator
          (probabilityPartitionPredictor μ eta cell)) x ∂μ := by
  classical
  let q : Cell → ℝ := probabilityPartitionCellPrediction μ eta cell
  have hleft :
      (fun x =>
          ({x | probabilityPartitionPredictor μ eta cell x ∈ A}.indicator eta) x) =
        (fun x =>
          ∑ c : Cell,
            if q c ∈ A then
              (probabilityPartitionFiber cell c).indicator eta x else 0) := by
    funext x
    rw [Fintype.sum_eq_single (cell x)]
    · simp [probabilityPartitionPredictor, q, probabilityPartitionFiber,
        Set.indicator_apply]
    · intro c hne
      simp [probabilityPartitionFiber, Ne.symm hne]
  have hright :
      (fun x =>
          ({x | probabilityPartitionPredictor μ eta cell x ∈ A}.indicator
            (probabilityPartitionPredictor μ eta cell)) x) =
        (fun x =>
          ∑ c : Cell,
            if q c ∈ A then
              (probabilityPartitionFiber cell c).indicator (fun _ => q c) x
            else 0) := by
    funext x
    rw [Fintype.sum_eq_single (cell x)]
    · simp [probabilityPartitionPredictor, q, probabilityPartitionFiber,
        Set.indicator_apply]
    · intro c hne
      simp [probabilityPartitionFiber, Ne.symm hne]
  rw [hleft, hright, integral_finset_sum, integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro c _hc
    by_cases hcA : q c ∈ A
    · simp only [hcA, if_true]
      rw [integral_indicator
          (probabilityPartitionFiber_measurable cell hcell c),
        integral_indicator
          (probabilityPartitionFiber_measurable cell hcell c)]
      rw [← probabilityPartitionCellLabelMass,
        probabilityPartitionCellLabelMass_eq_prediction_mul_mass,
        setIntegral_const]
      simp [q, probabilityPartitionCellMass, smul_eq_mul, mul_comm]
    · simp [hcA]
  · intro c _hc
    by_cases hcA : q c ∈ A
    · simp [hcA]
      exact (integrable_const (q c)).indicator
        (probabilityPartitionFiber_measurable cell hcell c)
    · simp [hcA]
  · intro c _hc
    by_cases hcA : q c ∈ A
    · simp [hcA]
      exact heta_int.indicator
        (probabilityPartitionFiber_measurable cell hcell c)
    · simp [hcA]

end OneGeneralPartition

/-! ## One partition per agent -/

section GeneralPartitionSetting

variable {n : ℕ} {X : Type} {Cell : Type*} [MeasurableSpace X]
  [Fintype Cell] [MeasurableSpace Cell] [MeasurableSingletonClass Cell]

/--
Applying one finite measurable partition per agent constructs a literal
arbitrary-probability-space collaboration setting.  Strategy-specific
well-formedness is intentionally separate from the setting itself.
-/
noncomputable def probabilityPartitionCollaborationSetting
    (μ : Measure X)
    [hprob : IsProbabilityMeasure μ]
    (eta : X → ℝ) (heta_int : Integrable eta μ)
    (heta : ∀ x, 0 ≤ eta x ∧ eta x ≤ 1)
    (cell : Fin n → X → Cell) (hcell : ∀ i, Measurable (cell i)) :
    ProbabilityCollaborationSetting n where
  X := X
  measurableSpaceX := inferInstance
  μ := μ
  isProbability := hprob
  eta := eta
  eta_range := heta
  eta_integrable := heta_int
  pred := fun i => probabilityPartitionPredictor μ eta (cell i)
  pred_range := fun i x =>
    probabilityPartitionCellPrediction_range μ eta (cell i) heta_int heta (cell i x)
  pred_measurable := fun i =>
    probabilityPartitionPredictor_measurable μ eta (cell i) (hcell i)
  calibrated_positive := fun i p _hpos =>
    probabilityPartitionPredictor_calibrated μ eta (cell i) (hcell i)
      heta_int p

end GeneralPartitionSetting

end PKG25NoFreeLunch
