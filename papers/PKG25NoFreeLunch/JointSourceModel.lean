import Mathlib.Probability.ProbabilityMassFunction.Integrals
import PKG25NoFreeLunch.MainTheorems

/-!
# PKG25 source-compatible joint-law collaboration settings

The source paper defines a collaboration setting from a distribution over
`X × {0,1}`, not from a pointwise conditional-probability function on `X`.
This module records the paper-facing joint-law semantics directly.  The
source's point-conditioned calibration display is under-specified on null
prediction fibers.  We therefore state calibration on every measurable event
in the reported-prediction sigma algebra, which is the explicit non-vacuous
event-calibration convention used by `PaperInterface.lean`.  It is not an
assertion that an arbitrary pointwise conditional-probability version exists
or has been selected on the input space.  The finite witness settings used by
the proof embed as finite joint probability mass functions, preserving actual
classifier accuracies exactly.
-/

open MeasureTheory

namespace PKG25NoFreeLunch

/--
An event-calibrated, source-compatible joint-law collaboration setting: a
joint law of an input and a binary label, with calibrated probability
predictors.  The calibration field is the event-level identity
`E[1_{P_i(X) ∈ A, Y = 1}] = E[P_i(X) 1_{P_i(X) ∈ A}]` for every measurable
reported-probability event `A`.
-/
structure JointLawCollaborationSetting (n : ℕ) where
  X : Type
  [measurableSpaceX : MeasurableSpace X]
  joint : Measure (X × Label)
  isProbability : IsProbabilityMeasure joint
  pred : Fin n → X → ℝ
  pred_range : ∀ i x, 0 ≤ pred i x ∧ pred i x ≤ 1
  pred_measurable : ∀ i, Measurable (pred i)
  calibrated_events :
    ∀ i : Fin n, ∀ A : Set ℝ, MeasurableSet A →
      (∫ z,
        ({z | pred i z.1 ∈ A ∧ z.2 = true}.indicator fun _ => (1 : ℝ)) z
          ∂joint) =
        ∫ z, ({z | pred i z.1 ∈ A}.indicator fun z => pred i z.1) z ∂joint

namespace JointLawCollaborationSetting

attribute [instance] measurableSpaceX

/-- Accuracy of an input classifier under the source joint law. -/
noncomputable def classifierAccuracy {n : ℕ}
    (S : JointLawCollaborationSetting n) (f : S.X → Label) : ℝ :=
  ∫ z, if f z.1 = z.2 then (1 : ℝ) else 0 ∂S.joint

/-- The classifier induced by a collaboration strategy. -/
def strategyClassifier {n : ℕ} (S : JointLawCollaborationSetting n)
    (C : CollaborationStrategy n) (x : S.X) : Label :=
  C (fun i => S.pred i x)

/-- The classifier induced by one source predictor. -/
noncomputable def agentClassifier {n : ℕ} (S : JointLawCollaborationSetting n)
    (i : Fin n) (x : S.X) : Label :=
  roundProb (S.pred i x)

/-- Direct joint-law accuracy of a collaboration strategy. -/
noncomputable def strategyAccuracy {n : ℕ} (S : JointLawCollaborationSetting n)
    (C : CollaborationStrategy n) : ℝ :=
  S.classifierAccuracy (S.strategyClassifier C)

/-- Direct joint-law accuracy of an individual agent. -/
noncomputable def agentAccuracy {n : ℕ} (S : JointLawCollaborationSetting n)
    (i : Fin n) : ℝ :=
  S.classifierAccuracy (S.agentClassifier i)

/--
The source's arbitrary deterministic strategy need not be measurable solely
because each predictor is measurable.  This is the ordinary expectation
well-formedness condition required when quantifying over such strategies.
-/
def StrategyWellFormed {n : ℕ} (S : JointLawCollaborationSetting n)
    (C : CollaborationStrategy n) : Prop :=
  Integrable
    (fun z : S.X × Label =>
      if S.strategyClassifier C z.1 = z.2 then (1 : ℝ) else 0)
    S.joint

/--
Event calibration recovers the source's displayed formula for an agent's
accuracy.  The proof uses the two measurable reported-probability events
`[1/2, ∞)` and `(-∞, 1/2)`: calibration gives the true-label mass on each,
and the false-label term is its event mass minus the true-label mass.
-/
theorem agentAccuracy_eq_predictionCertainty {n : ℕ}
    (S : JointLawCollaborationSetting n) (i : Fin n) :
    S.agentAccuracy i =
      ∫ z : S.X × Label,
        max (S.pred i z.1) (1 - S.pred i z.1) ∂S.joint := by
  classical
  letI : IsProbabilityMeasure S.joint := S.isProbability
  let p : S.X × Label → ℝ := fun z => S.pred i z.1
  let Eplus : Set (S.X × Label) := {z | p z ∈ Set.Ici ((1 : ℝ) / 2)}
  let Eminus : Set (S.X × Label) := {z | p z ∈ Set.Iio ((1 : ℝ) / 2)}
  let Tplus : Set (S.X × Label) :=
    {z | p z ∈ Set.Ici ((1 : ℝ) / 2) ∧ z.2 = true}
  let Tminus : Set (S.X × Label) :=
    {z | p z ∈ Set.Iio ((1 : ℝ) / 2) ∧ z.2 = false}
  let Uminus : Set (S.X × Label) :=
    {z | p z ∈ Set.Iio ((1 : ℝ) / 2) ∧ z.2 = true}
  have hpmeas : Measurable p := by
    exact (S.pred_measurable i).comp measurable_fst
  have hpint : Integrable p S.joint := by
    refine Integrable.of_bound hpmeas.aestronglyMeasurable 1 (.of_forall ?_)
    intro z
    have hp := S.pred_range i z.1
    rw [Real.norm_eq_abs, abs_of_nonneg hp.1]
    exact hp.2
  have hEplus : MeasurableSet Eplus := by
    exact hpmeas measurableSet_Ici
  have hEminus : MeasurableSet Eminus := by
    exact hpmeas measurableSet_Iio
  have hlabelTrue : MeasurableSet {z : S.X × Label | z.2 = true} := by
    exact measurable_snd (measurableSet_singleton true)
  have hlabelFalse : MeasurableSet {z : S.X × Label | z.2 = false} := by
    exact measurable_snd (measurableSet_singleton false)
  have hTplus : MeasurableSet Tplus := by
    exact hEplus.inter hlabelTrue
  have hTminus : MeasurableSet Tminus := by
    exact hEminus.inter hlabelFalse
  have hUminus : MeasurableSet Uminus := by
    exact hEminus.inter hlabelTrue
  have hone : Integrable (fun _ : S.X × Label => (1 : ℝ)) S.joint :=
    integrable_const _
  have hTplusInt := hone.indicator hTplus
  have hTminusInt := hone.indicator hTminus
  have hUminusInt := hone.indicator hUminus
  have hEminusOne := hone.indicator hEminus
  have hEplusP := hpint.indicator hEplus
  have hEminusP := hpint.indicator hEminus
  have hcalPlus :
      (∫ z, (Tplus.indicator fun _ => (1 : ℝ)) z ∂S.joint) =
        ∫ z, (Eplus.indicator p) z ∂S.joint := by
    simpa [p, Eplus, Tplus] using
      S.calibrated_events i (Set.Ici ((1 : ℝ) / 2)) measurableSet_Ici
  have hcalMinus :
      (∫ z, (Uminus.indicator fun _ => (1 : ℝ)) z ∂S.joint) =
        ∫ z, (Eminus.indicator p) z ∂S.joint := by
    simpa [p, Eminus, Uminus] using
      S.calibrated_events i (Set.Iio ((1 : ℝ) / 2)) measurableSet_Iio
  have hcorrect :
      (fun z : S.X × Label =>
        if S.agentClassifier i z.1 = z.2 then (1 : ℝ) else 0) =
        (fun z => (Tplus.indicator fun _ => (1 : ℝ)) z +
          (Tminus.indicator fun _ => (1 : ℝ)) z) := by
    funext z
    rcases z with ⟨x, y⟩
    rw [Set.indicator_apply, Set.indicator_apply]
    cases y with
    | false =>
      by_cases hhalf : (1 : ℝ) / 2 ≤ S.pred i x
      · have hround : roundProb (S.pred i x) = true :=
          roundProb_eq_true_iff.mpr hhalf
        have hhalf' : (2 : ℝ)⁻¹ ≤ S.pred i x := by
          norm_num at hhalf ⊢
          exact hhalf
        have hnot : ¬ S.pred i x < (2 : ℝ)⁻¹ := not_lt_of_ge hhalf'
        simp [JointLawCollaborationSetting.agentClassifier, p, Tplus, Tminus,
          hround, hhalf', hnot]
      · have hlt : S.pred i x < (1 : ℝ) / 2 := lt_of_not_ge hhalf
        have hround : roundProb (S.pred i x) = false :=
          roundProb_eq_false_iff.mpr hlt
        have hlt' : S.pred i x < (2 : ℝ)⁻¹ := by
          norm_num at hlt ⊢
          exact hlt
        simp [JointLawCollaborationSetting.agentClassifier, p, Tplus, Tminus,
          hround, hlt']
    | true =>
      by_cases hhalf : (1 : ℝ) / 2 ≤ S.pred i x
      · have hround : roundProb (S.pred i x) = true :=
          roundProb_eq_true_iff.mpr hhalf
        have hhalf' : (2 : ℝ)⁻¹ ≤ S.pred i x := by
          norm_num at hhalf ⊢
          exact hhalf
        simp [JointLawCollaborationSetting.agentClassifier, p, Tplus, Tminus,
          hround, hhalf']
      · have hlt : S.pred i x < (1 : ℝ) / 2 := lt_of_not_ge hhalf
        have hround : roundProb (S.pred i x) = false :=
          roundProb_eq_false_iff.mpr hlt
        have hlt' : S.pred i x < (2 : ℝ)⁻¹ := by
          norm_num at hlt ⊢
          exact hlt
        simp [JointLawCollaborationSetting.agentClassifier, p, Tplus, Tminus,
          hround, hlt']
  have hfalse :
      (fun z : S.X × Label => (Tminus.indicator fun _ => (1 : ℝ)) z) =
        (fun z => (Eminus.indicator fun _ => (1 : ℝ)) z -
          (Uminus.indicator fun _ => (1 : ℝ)) z) := by
    funext z
    rcases z with ⟨x, y⟩
    rw [Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
    cases y with
    | false =>
      by_cases hlt : S.pred i x < (1 : ℝ) / 2
      · have hlt' : S.pred i x < (2 : ℝ)⁻¹ := by
          norm_num at hlt ⊢
          exact hlt
        simp [p, Eminus, Tminus, Uminus, hlt']
      · have hlt' : ¬ S.pred i x < (2 : ℝ)⁻¹ := by
          norm_num at hlt ⊢
          exact hlt
        simp [p, Eminus, Tminus, Uminus, hlt']
    | true =>
      by_cases hlt : S.pred i x < (1 : ℝ) / 2
      · have hlt' : S.pred i x < (2 : ℝ)⁻¹ := by
          norm_num at hlt ⊢
          exact hlt
        simp [p, Eminus, Tminus, Uminus, hlt']
      · have hlt' : ¬ S.pred i x < (2 : ℝ)⁻¹ := by
          norm_num at hlt ⊢
          exact hlt
        simp [p, Eminus, Tminus, Uminus, hlt']
  have hformula :
      (fun z : S.X × Label => (Eplus.indicator p) z +
        ((Eminus.indicator fun _ => (1 : ℝ)) z - (Eminus.indicator p) z)) =
        (fun z => max (p z) (1 - p z)) := by
    funext z
    rw [Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
    by_cases hhalf : (1 : ℝ) / 2 ≤ p z
    · have hmax : max (p z) (1 - p z) = p z := max_eq_left (by linarith)
      simp only [Eplus, Eminus, Set.mem_setOf_eq, Set.mem_Ici, Set.mem_Iio]
      rw [if_pos hhalf, if_neg (not_lt_of_ge hhalf),
        if_neg (not_lt_of_ge hhalf), hmax]
      ring
    · have hlt : p z < (1 : ℝ) / 2 := lt_of_not_ge hhalf
      have hmax : max (p z) (1 - p z) = 1 - p z := max_eq_right (by linarith)
      simp only [Eplus, Eminus, Set.mem_setOf_eq, Set.mem_Ici, Set.mem_Iio]
      rw [if_neg hhalf, if_pos hlt, if_pos hlt, hmax]
      ring
  unfold JointLawCollaborationSetting.agentAccuracy
    JointLawCollaborationSetting.classifierAccuracy
  change
    (∫ z : S.X × Label,
      if S.agentClassifier i z.1 = z.2 then (1 : ℝ) else 0 ∂S.joint) =
      ∫ z : S.X × Label, max (p z) (1 - p z) ∂S.joint
  calc
    (∫ z : S.X × Label,
        if S.agentClassifier i z.1 = z.2 then (1 : ℝ) else 0 ∂S.joint) =
        ∫ z, (Tplus.indicator fun _ => (1 : ℝ)) z +
          (Tminus.indicator fun _ => (1 : ℝ)) z ∂S.joint := by rw [hcorrect]
    _ = (∫ z, (Tplus.indicator fun _ => (1 : ℝ)) z ∂S.joint) +
        ∫ z, (Tminus.indicator fun _ => (1 : ℝ)) z ∂S.joint := by
          rw [integral_add hTplusInt hTminusInt]
    _ = (∫ z, (Tplus.indicator fun _ => (1 : ℝ)) z ∂S.joint) +
        ((∫ z, (Eminus.indicator fun _ => (1 : ℝ)) z ∂S.joint) -
          ∫ z, (Uminus.indicator fun _ => (1 : ℝ)) z ∂S.joint) := by
          rw [hfalse, integral_sub hEminusOne hUminusInt]
    _ = (∫ z, (Eplus.indicator p) z ∂S.joint) +
        ((∫ z, (Eminus.indicator fun _ => (1 : ℝ)) z ∂S.joint) -
          ∫ z, (Eminus.indicator p) z ∂S.joint) := by
          rw [hcalPlus, hcalMinus]
    _ = ∫ z, (Eplus.indicator p) z +
        ((Eminus.indicator fun _ => (1 : ℝ)) z - (Eminus.indicator p) z)
          ∂S.joint := by
          change
            (∫ z, (Eplus.indicator p) z ∂S.joint) +
                ((∫ z, (Eminus.indicator fun _ => (1 : ℝ)) z ∂S.joint) -
                  ∫ z, (Eminus.indicator p) z ∂S.joint) =
              ∫ z, ((Eplus.indicator p) +
                ((Eminus.indicator fun _ => (1 : ℝ)) - Eminus.indicator p)) z
                  ∂S.joint
          have hsub :
              (∫ z, ((Eminus.indicator fun _ => (1 : ℝ)) -
                Eminus.indicator p) z ∂S.joint) =
                (∫ z, (Eminus.indicator fun _ => (1 : ℝ)) z ∂S.joint) -
                  ∫ z, (Eminus.indicator p) z ∂S.joint := by
            exact integral_sub hEminusOne hEminusP
          exact (integral_add hEplusP (hEminusOne.sub hEminusP)).trans
            (congrArg (fun t => (∫ z, (Eplus.indicator p) z ∂S.joint) + t)
              hsub) |>.symm
    _ = ∫ z : S.X × Label, max (p z) (1 - p z) ∂S.joint := by rw [hformula]

end JointLawCollaborationSetting

/-! ## Finite calibration support -/

/--
Finite calibration summed over a measurable collection of reported prediction
values.  This is a finite algebraic consequence of the witness calibration
field and belongs with the raw-joint embedding, rather than with the retired
arbitrary `eta` model.
-/
theorem finite_calibrated_on_prediction_set {n : ℕ}
    (S : FiniteCollaborationSetting n) (i : Fin n) (A : Set ℝ)
    [DecidablePred fun x : S.X => S.pred i x ∈ A] :
    eventLabelMass S.mass S.eta (fun x : S.X => S.pred i x ∈ A) =
      ∑ x : S.X, if S.pred i x ∈ A then S.mass x * S.pred i x else 0 := by
  classical
  let values : Finset ℝ := Finset.univ.image (S.pred i)
  have hfiber (f : S.X → ℝ) :
      (∑ x : S.X, f x) =
        ∑ p ∈ values, ∑ x ∈ (Finset.univ : Finset S.X) with
          S.pred i x = p, f x := by
    symm
    exact Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ) (t := values) (g := S.pred i)
      (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩) f
  unfold eventLabelMass
  rw [hfiber, hfiber]
  refine Finset.sum_congr rfl ?_
  intro p hp
  by_cases hpA : p ∈ A
  · have hleft :
        (∑ x ∈ (Finset.univ : Finset S.X) with S.pred i x = p,
            if S.pred i x ∈ A then S.mass x * S.eta x else 0) =
          eventLabelMass S.mass S.eta (fun x : S.X => S.pred i x = p) := by
      rw [show eventLabelMass S.mass S.eta
          (fun x : S.X => S.pred i x = p) =
            ∑ x ∈ (Finset.univ : Finset S.X) with S.pred i x = p,
              S.mass x * S.eta x by
                symm
                simpa [eventLabelMass] using
                  (Finset.sum_filter (s := (Finset.univ : Finset S.X))
                    (fun x : S.X => S.pred i x = p)
                    (fun x => S.mass x * S.eta x))]
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hxp : S.pred i x = p := (Finset.mem_filter.mp hx).2
      simp [hxp, hpA]
    have hright :
        (∑ x ∈ (Finset.univ : Finset S.X) with S.pred i x = p,
            if S.pred i x ∈ A then S.mass x * S.pred i x else 0) =
          p * eventMass S.mass (fun x : S.X => S.pred i x = p) := by
      rw [show eventMass S.mass (fun x : S.X => S.pred i x = p) =
          ∑ x ∈ (Finset.univ : Finset S.X) with S.pred i x = p,
            S.mass x by
              symm
              simpa [eventMass] using
                (Finset.sum_filter (s := (Finset.univ : Finset S.X))
                  (fun x : S.X => S.pred i x = p) S.mass),
        Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hxp : S.pred i x = p := (Finset.mem_filter.mp hx).2
      simp [hxp, hpA, mul_comm]
    rw [hleft, hright, S.calibrated_unconditional i p]
  · refine Finset.sum_congr rfl ?_
    intro x hx
    have hxp : S.pred i x = p := (Finset.mem_filter.mp hx).2
    simp [hxp, hpA]

/-! ## Finite joint-law embeddings -/

/--
The joint PMF induced by a finite proof witness.  At an input `x`, it assigns
mass `mass x * eta x` to label `true` and `mass x * (1 - eta x)` to label
`false`; this is an actual distribution on `X × Bool`.
-/
noncomputable def finiteJointLawPMF {n : ℕ}
    (S : FiniteCollaborationSetting n) : PMF (S.X × Label) :=
  PMF.ofFintype
    (fun z => ENNReal.ofReal
      (S.mass z.1 * pointAccuracy z.2 (S.eta z.1))) (by
      have hnonneg :
          ∀ z ∈ (Finset.univ : Finset (S.X × Label)),
            0 ≤ S.mass z.1 * pointAccuracy z.2 (S.eta z.1) := by
        intro z _hz
        exact mul_nonneg (S.mass_nonneg z.1)
          (pointAccuracy_range (S.eta_range z.1)).1
      calc
        (∑ z : S.X × Label,
            ENNReal.ofReal (S.mass z.1 * pointAccuracy z.2 (S.eta z.1))) =
            ENNReal.ofReal
              (∑ z : S.X × Label,
                S.mass z.1 * pointAccuracy z.2 (S.eta z.1)) := by
              rw [ENNReal.ofReal_sum_of_nonneg hnonneg]
        _ = ENNReal.ofReal (∑ x : S.X, S.mass x) := by
              congr 1
              rw [Fintype.sum_prod_type]
              refine Finset.sum_congr rfl ?_
              intro x _hx
              rw [Fintype.sum_bool]
              simp [pointAccuracy]
              ring
        _ = 1 := by rw [S.mass_sum]; simp)

@[simp] theorem finiteJointLawPMF_apply_toReal {n : ℕ}
    (S : FiniteCollaborationSetting n) (z : S.X × Label) :
    (finiteJointLawPMF S z).toReal =
      S.mass z.1 * pointAccuracy z.2 (S.eta z.1) := by
  unfold finiteJointLawPMF
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (mul_nonneg (S.mass_nonneg z.1)
    (pointAccuracy_range (S.eta_range z.1)).1)

/--
Every finite calibrated witness used in the source proof is a literal finite
instance of the raw joint-law source model.
-/
noncomputable def JointLawCollaborationSetting.ofFinite {n : ℕ}
    (S : FiniteCollaborationSetting n) : JointLawCollaborationSetting n := by
  letI : MeasurableSpace S.X := ⊤
  exact
    { X := S.X
      measurableSpaceX := inferInstance
      joint := (finiteJointLawPMF S).toMeasure
      isProbability := inferInstance
      pred := S.pred
      pred_range := S.pred_range
      pred_measurable := fun i => measurable_of_finite (S.pred i)
      calibrated_events := by
        intro i A _hA
        classical
        rw [PMF.integral_eq_sum, PMF.integral_eq_sum]
        simp only [finiteJointLawPMF_apply_toReal, smul_eq_mul]
        simp_rw [Set.indicator_apply]
        calc
          (∑ z : S.X × Label,
              S.mass z.1 * pointAccuracy z.2 (S.eta z.1) *
                (if S.pred i z.1 ∈ A ∧ z.2 = true then 1 else 0)) =
              eventLabelMass S.mass S.eta (fun x : S.X => S.pred i x ∈ A) := by
                rw [Fintype.sum_prod_type]
                unfold eventLabelMass
                refine Finset.sum_congr rfl ?_
                intro x _hx
                by_cases hA : S.pred i x ∈ A
                · rw [Fintype.sum_bool]
                  simp [hA, pointAccuracy]
                · rw [Fintype.sum_bool]
                  simp [hA]
          _ = ∑ x : S.X,
              if S.pred i x ∈ A then S.mass x * S.pred i x else 0 :=
                finite_calibrated_on_prediction_set S i A
          _ = ∑ z : S.X × Label,
              S.mass z.1 * pointAccuracy z.2 (S.eta z.1) *
                (if S.pred i z.1 ∈ A then S.pred i z.1 else 0) := by
                rw [Fintype.sum_prod_type]
                refine Finset.sum_congr rfl ?_
                intro x _hx
                by_cases hA : S.pred i x ∈ A
                · rw [Fintype.sum_bool]
                  simp [hA, pointAccuracy]
                  ring
                · rw [Fintype.sum_bool]
                  simp [hA] }

/-- The finite joint-law embedding preserves the accuracy of any classifier. -/
theorem JointLawCollaborationSetting.ofFinite_classifierAccuracy {n : ℕ}
    (S : FiniteCollaborationSetting n) (f : S.X → Label) :
    (JointLawCollaborationSetting.ofFinite S).classifierAccuracy f =
      ∑ x : S.X, S.mass x * pointAccuracy (f x) (S.eta x) := by
  letI : MeasurableSpace S.X := ⊤
  unfold JointLawCollaborationSetting.classifierAccuracy
  change
    (∫ z : S.X × Label,
        if f z.1 = z.2 then (1 : ℝ) else 0 ∂(finiteJointLawPMF S).toMeasure) =
      ∑ x : S.X, S.mass x * pointAccuracy (f x) (S.eta x)
  rw [PMF.integral_eq_sum]
  simp only [finiteJointLawPMF_apply_toReal, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro x _hx
  cases h : f x <;> rw [Fintype.sum_bool] <;> simp [h, pointAccuracy]

/-- The finite joint-law embedding preserves strategy accuracy exactly. -/
theorem JointLawCollaborationSetting.ofFinite_strategyAccuracy {n : ℕ}
    (C : CollaborationStrategy n) (S : FiniteCollaborationSetting n) :
    (JointLawCollaborationSetting.ofFinite S).strategyAccuracy C =
      S.strategyAccuracy C := by
  unfold JointLawCollaborationSetting.strategyAccuracy
    JointLawCollaborationSetting.strategyClassifier
    FiniteCollaborationSetting.strategyAccuracy
    FiniteCollaborationSetting.strategyClassifier
  simpa using JointLawCollaborationSetting.ofFinite_classifierAccuracy S
    (fun x => C (fun i => S.pred i x))

/-- The finite joint-law embedding preserves every agent accuracy exactly. -/
theorem JointLawCollaborationSetting.ofFinite_agentAccuracy {n : ℕ}
    (S : FiniteCollaborationSetting n) (i : Fin n) :
    (JointLawCollaborationSetting.ofFinite S).agentAccuracy i = S.agentAccuracy i := by
  unfold JointLawCollaborationSetting.agentAccuracy
    JointLawCollaborationSetting.agentClassifier
    FiniteCollaborationSetting.agentAccuracy
  simpa [FiniteCollaborationSetting.agentClassifier] using
    JointLawCollaborationSetting.ofFinite_classifierAccuracy S
      (fun x => roundProb (S.pred i x))

/-- Every deterministic strategy is expectation-well-formed on a finite joint law. -/
theorem JointLawCollaborationSetting.ofFinite_strategyWellFormed {n : ℕ}
    (C : CollaborationStrategy n) (S : FiniteCollaborationSetting n) :
    JointLawCollaborationSetting.StrategyWellFormed
      (JointLawCollaborationSetting.ofFinite S) C := by
  letI : MeasurableSpace S.X := ⊤
  unfold JointLawCollaborationSetting.StrategyWellFormed
    JointLawCollaborationSetting.strategyClassifier
  change Integrable
    (fun z : S.X × Label =>
      if C (fun i => S.pred i z.1) = z.2 then (1 : ℝ) else 0)
    (finiteJointLawPMF S).toMeasure
  exact Integrable.of_finite

/-! ## Reliability bridge -/

/--
Reliability under the paper-facing, event-calibrated joint-law convention.  The
strategy well-formedness premise is required only because an arbitrary
deterministic strategy need not preserve measurability on an arbitrary input
space.
-/
def ReliableJointLaw {n : ℕ} (C : CollaborationStrategy n) : Prop :=
  ∀ S : JointLawCollaborationSetting n,
    JointLawCollaborationSetting.StrategyWellFormed S C →
      ∃ i : Fin n, S.agentAccuracy i ≤ S.strategyAccuracy C

/--
Reliability over this source-compatible joint-law subuniverse entails
reliability on every finite adversarial witness.  This is the bridge required
by the finite proof of the source theorem.
-/
theorem reliableFinite_of_reliableJointLaw {n : ℕ}
    {C : CollaborationStrategy n} (hrel : ReliableJointLaw C) : ReliableFinite C := by
  intro S
  rcases hrel (JointLawCollaborationSetting.ofFinite S)
      (JointLawCollaborationSetting.ofFinite_strategyWellFormed C S) with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  simpa [JointLawCollaborationSetting.ofFinite_agentAccuracy,
    JointLawCollaborationSetting.ofFinite_strategyAccuracy] using hi

/--
The no-free-lunch conclusion follows from reliability under the event-
calibrated joint-law convention by restricting that universal premise to the
exact finite joint laws used by the source constructions.
-/
theorem main_no_free_lunch_jointLaw {n : ℕ} [Nonempty (Fin n)]
    (C : CollaborationStrategy n) : ReliableJointLaw C → NonCollaborative C := by
  intro hrel
  exact main_no_free_lunch_finite C (reliableFinite_of_reliableJointLaw hrel)

end PKG25NoFreeLunch
