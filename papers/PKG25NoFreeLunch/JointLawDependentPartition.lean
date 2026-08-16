import PKG25NoFreeLunch.JointLawGeneralPartition

/-!
# PKG25 dependent finite partitions for raw joint laws

The paper allows each agent to use its own finite measurable partition.  The
common-cell construction in `JointLawGeneralPartition` already proves the
one-agent result.  This module packages those results for a dependent family
of cell types, so it does not encode agents' partitions by an artificial sum
type or assume that their cell labels share a carrier.
-/

open MeasureTheory

namespace PKG25NoFreeLunch

section DependentJointLawPartitionSetting

variable {n : ℕ} {Cell : Fin n → Type*}
  [∀ i, Fintype (Cell i)]
  [∀ i, MeasurableSpace (Cell i)]
  [∀ i, MeasurableSingletonClass (Cell i)]

/--
Construct the paper's dependent finite-partition predictors directly from an
arbitrary raw joint probability law.  Unlike
`jointLawDependentPartitionCollaborationSetting`, this does not presuppose a
calibrated predictor family: the cell conditional probabilities supply that
calibration as an output of the construction.
-/
noncomputable def jointLawDependentPartitionSetting
    {X : Type} [MeasurableSpace X]
    (joint : Measure (X × Label)) [IsProbabilityMeasure joint]
    (cell : (i : Fin n) → X → Cell i)
    (hcell : ∀ i, Measurable (cell i)) :
    JointLawCollaborationSetting n where
  X := X
  measurableSpaceX := inferInstance
  joint := joint
  isProbability := inferInstance
  pred := fun i => jointLawPartitionPredictor joint (cell i)
  pred_range := by
    intro i x
    simpa [jointLawPartitionPredictor] using
      (jointLawPartitionCellPrediction_range joint (cell i) (cell i x))
  pred_measurable := by
    intro i
    exact jointLawPartitionPredictor_measurable joint (cell i) (hcell i)
  calibrated_events := by
    intro i A hA
    simpa [jointLawPartitionPredictor] using
      (jointLawPartitionPredictor_calibrated_events joint (cell i) (hcell i) A hA)

/-- The raw construction's predictor is exactly the source cell conditional probability. -/
theorem jointLawDependentPartitionSetting_pred
    {X : Type} [MeasurableSpace X]
    (joint : Measure (X × Label)) [IsProbabilityMeasure joint]
    (cell : (i : Fin n) → X → Cell i)
    (hcell : ∀ i, Measurable (cell i))
    (i : Fin n) (x : X) :
    (jointLawDependentPartitionSetting joint cell hcell).pred i x =
      jointLawPartitionPredictor joint (cell i) x := rfl

/--
Each predictor produced directly from a raw joint law satisfies the
event-level calibration identity under that same law.
-/
theorem jointLawDependentPartitionSetting_calibrated_events
    {X : Type} [MeasurableSpace X]
    (joint : Measure (X × Label)) [IsProbabilityMeasure joint]
    (cell : (i : Fin n) → X → Cell i)
    (hcell : ∀ i, Measurable (cell i))
    (i : Fin n) (A : Set ℝ) (hA : MeasurableSet A) :
    (∫ z : X × Label,
      ({z | jointLawPartitionPredictor joint (cell i) z.1 ∈ A ∧ z.2 = true}.indicator
        (fun _ => (1 : ℝ))) z ∂joint) =
      ∫ z : X × Label,
        ({z | jointLawPartitionPredictor joint (cell i) z.1 ∈ A}.indicator
          (fun z => jointLawPartitionPredictor joint (cell i) z.1)) z ∂joint := by
  exact jointLawPartitionPredictor_calibrated_events joint (cell i) (hcell i) A hA

/--
Apply one finite measurable input partition per agent to a raw joint-law
setting, allowing the agents' finite cell types to differ.  The joint law is
unchanged and each predictor is the conditional true-label probability of its
own input cell, with value zero on a null cell.
-/
noncomputable def jointLawDependentPartitionCollaborationSetting
    (S : JointLawCollaborationSetting n)
    (cell : (i : Fin n) → S.X → Cell i)
    (hcell : ∀ i, Measurable (cell i)) :
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

/-- The dependent partition construction exposes the direct raw cell predictor. -/
theorem jointLawDependentPartitionCollaborationSetting_pred
    (S : JointLawCollaborationSetting n)
    (cell : (i : Fin n) → S.X → Cell i)
    (hcell : ∀ i, Measurable (cell i))
    (i : Fin n) (x : S.X) :
    (jointLawDependentPartitionCollaborationSetting S cell hcell).pred i x =
      jointLawPartitionPredictor S.joint (cell i) x := rfl

/--
Each dependent partition predictor is event-calibrated under the unchanged
raw joint law.
-/
theorem jointLawDependentPartitionCollaborationSetting_calibrated_events
    (S : JointLawCollaborationSetting n)
    (cell : (i : Fin n) → S.X → Cell i)
    (hcell : ∀ i, Measurable (cell i))
    (i : Fin n) (A : Set ℝ) (hA : MeasurableSet A) :
    (∫ z : S.X × Label,
      ({z | jointLawPartitionPredictor S.joint (cell i) z.1 ∈ A ∧ z.2 = true}.indicator
        (fun _ => (1 : ℝ))) z ∂S.joint) =
      ∫ z : S.X × Label,
        ({z | jointLawPartitionPredictor S.joint (cell i) z.1 ∈ A}.indicator
          (fun z => jointLawPartitionPredictor S.joint (cell i) z.1)) z ∂S.joint := by
  letI : IsProbabilityMeasure S.joint := S.isProbability
  exact jointLawPartitionPredictor_calibrated_events S.joint (cell i) (hcell i) A hA

end DependentJointLawPartitionSetting

end PKG25NoFreeLunch
