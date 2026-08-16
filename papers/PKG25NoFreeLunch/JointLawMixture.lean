import PKG25NoFreeLunch.JointSourceModel

/-!
# PKG25 raw joint-law mixtures

This module formalizes the finite disjoint-union mixture used in source
Proposition 6 directly on the source-compatible joint-law model.  Each
component joint law on `X_r × Label` is pushed into
`(Σ r, X_r) × Label`, then weighted by the prescribed simplex weight.
The construction is independent of any collaboration strategy.  Strategy
well-formedness is needed only to state the corresponding integral identity.
-/

open MeasureTheory

namespace PKG25NoFreeLunch

/-- Each inclusion into a dependent input disjoint union is measurable. -/
theorem jointLawMixture_sigmaMk_measurable
    {α : Type*} {β : α → Type*} [∀ a, MeasurableSpace (β a)] (a : α) :
    Measurable (fun x : β a => Sigma.mk a x) :=
  Measurable.of_le_map (iInf_le _ a)

/-- A function out of a dependent input disjoint union is measurable fiberwise. -/
theorem jointLawMixture_measurable_of_fiberwise
    {α : Type*} {β : α → Type*} [∀ a, MeasurableSpace (β a)]
    {γ : Type*} [MeasurableSpace γ] {f : Sigma β → γ}
    (hf : ∀ a, Measurable (fun x : β a => f (Sigma.mk a x))) :
    Measurable f :=
  Measurable.of_comap_le <| le_iInf fun a =>
    MeasurableSpace.comap_le_iff_le_map.2 (hf a)

/-- Each inclusion into a dependent input disjoint union is a measurable embedding. -/
theorem jointLawMixture_sigmaMk_measurableEmbedding
    {α : Type*} {β : α → Type*} [DecidableEq α]
    [∀ a, MeasurableSpace (β a)] (a : α) :
    MeasurableEmbedding (fun x : β a => Sigma.mk a x) where
  injective := sigma_mk_injective
  measurable := jointLawMixture_sigmaMk_measurable a
  measurableSet_image' := by
    intro s hs
    change MeasurableSet[⨅ b,
      (inferInstance : MeasurableSpace (β b)).map (Sigma.mk b)] (Sigma.mk a '' s)
    rw [MeasurableSpace.measurableSet_iInf]
    intro b
    change MeasurableSet ((fun x : β b => Sigma.mk b x) ⁻¹' (Sigma.mk a '' s))
    by_cases hba : b = a
    · subst b
      simpa only [Set.preimage_image_eq s sigma_mk_injective]
    · have hempty :
          (fun x : β b => Sigma.mk b x) ⁻¹' (Sigma.mk a '' s) = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false,
          iff_false]
        rintro ⟨y, _hy, hxy⟩
        exact hba (Sigma.mk.inj_iff.mp hxy).1.symm
      rw [hempty]
      exact MeasurableSet.empty

/-- Embed one component's input-label pair into the disjoint-union input space. -/
def jointLawMixtureEmbedding {n ell : ℕ}
    (S : Fin ell → JointLawCollaborationSetting n) (r : Fin ell) :
    (S r).X × Label → (Sigma fun r : Fin ell => (S r).X) × Label :=
  fun z => (Sigma.mk r z.1, z.2)

/-- The component embedding into the joint disjoint union is measurable. -/
theorem jointLawMixtureEmbedding_measurable {n ell : ℕ}
    (S : Fin ell → JointLawCollaborationSetting n) (r : Fin ell) :
    Measurable (jointLawMixtureEmbedding S r) := by
  exact Measurable.prodMk
    ((jointLawMixture_sigmaMk_measurable r).comp measurable_fst) measurable_snd

/-- The component embedding into the joint disjoint union is a measurable embedding. -/
theorem jointLawMixtureEmbedding_measurableEmbedding {n ell : ℕ}
    (S : Fin ell → JointLawCollaborationSetting n) (r : Fin ell) :
    MeasurableEmbedding (jointLawMixtureEmbedding S r) := by
  simpa only [jointLawMixtureEmbedding, Prod.map_apply] using
    (jointLawMixture_sigmaMk_measurableEmbedding
      (β := fun r : Fin ell => (S r).X) r).prodMap MeasurableEmbedding.id

/--
The raw joint-law mixture measure: scale and push each component joint law
into its summand of the dependent input disjoint union.
-/
noncomputable def jointLawMixtureMeasure {n ell : ℕ}
    (S : Fin ell → JointLawCollaborationSetting n)
    (w : Fin ell → ℝ) :
    Measure ((Sigma fun r : Fin ell => (S r).X) × Label) :=
  Measure.sum fun r =>
    ENNReal.ofReal (w r) • Measure.map (jointLawMixtureEmbedding S r) (S r).joint

/-- Simplex weights make the raw joint-law mixture a probability measure. -/
theorem jointLawMixtureMeasure_univ {n ell : ℕ}
    (S : Fin ell → JointLawCollaborationSetting n)
    (w : Fin ell → ℝ) (hw_nonneg : ∀ r, 0 ≤ w r)
    (hw_sum : ∑ r, w r = 1) :
    jointLawMixtureMeasure S w Set.univ = 1 := by
  have hmap (r : Fin ell) :
      Measure.map (jointLawMixtureEmbedding S r) (S r).joint Set.univ = 1 := by
    calc
      Measure.map (jointLawMixtureEmbedding S r) (S r).joint Set.univ =
          (S r).joint Set.univ := by
        simpa only [Set.preimage_univ] using
          (Measure.map_apply (μ := (S r).joint)
            (jointLawMixtureEmbedding_measurable S r)
            (s := Set.univ) MeasurableSet.univ)
      _ = 1 := (S r).isProbability.measure_univ
  simp only [jointLawMixtureMeasure,
    Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply, hmap,
    smul_eq_mul, mul_one]
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg]
  · rw [hw_sum]
    simp
  · exact fun r _ => hw_nonneg r

/--
On every measurable component joint event, the raw mixture law is the
component law multiplied by its mixture weight.  This is the literal
joint-event form of the component-mass display in source Proposition 6.
-/
theorem jointLawMixtureMeasure_component_image {n ell : ℕ}
    (S : Fin ell → JointLawCollaborationSetting n)
    (w : Fin ell → ℝ) (r : Fin ell) (A : Set ((S r).X × Label))
    (hA : MeasurableSet A) :
    jointLawMixtureMeasure S w ((jointLawMixtureEmbedding S r) '' A) =
      ENNReal.ofReal (w r) * (S r).joint A := by
  let E : Set ((Sigma fun r : Fin ell => (S r).X) × Label) :=
    (jointLawMixtureEmbedding S r) '' A
  have hE : MeasurableSet E :=
    (jointLawMixtureEmbedding_measurableEmbedding S r).measurableSet_image' hA
  change jointLawMixtureMeasure S w E = _
  rw [jointLawMixtureMeasure, Measure.sum_apply _ hE, tsum_fintype]
  rw [Finset.sum_eq_single r]
  · rw [Measure.smul_apply,
      Measure.map_apply (jointLawMixtureEmbedding_measurable S r) hE]
    change ENNReal.ofReal (w r) * (S r).joint
      ((jointLawMixtureEmbedding S r) ⁻¹' E) = _
    rw [show (jointLawMixtureEmbedding S r) ⁻¹' E = A by
      ext z
      constructor
      · rintro ⟨y, hy, hzy⟩
        exact (jointLawMixtureEmbedding_measurableEmbedding S r).injective hzy |>.symm ▸ hy
      · intro hz
        exact ⟨z, hz, rfl⟩]
  · intro k _hk hkr
    have hempty :
        (jointLawMixtureEmbedding S k) ⁻¹' E = ∅ := by
      ext z
      simp only [E, Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false,
        iff_false]
      rintro ⟨y, _hy, hzy⟩
      apply hkr
      exact (congrArg (fun q : (Sigma fun r : Fin ell => (S r).X) × Label =>
        q.1.1) hzy).symm
    rw [Measure.smul_apply,
      Measure.map_apply (jointLawMixtureEmbedding_measurable S k) hE,
      hempty, measure_empty]
    simp
  · intro hr
    exact (hr (Finset.mem_univ r)).elim

/-- Fiberwise integrability implies integrability under the finite raw mixture. -/
theorem integrable_jointLawMixtureMeasure {n ell : ℕ}
    (S : Fin ell → JointLawCollaborationSetting n)
    (w : Fin ell → ℝ)
    {f : (Sigma fun r : Fin ell => (S r).X) × Label → ℝ}
    (hf : ∀ r, Integrable
      (fun z : (S r).X × Label => f (jointLawMixtureEmbedding S r z))
      (S r).joint) :
    Integrable f (jointLawMixtureMeasure S w) := by
  apply integrable_sum_measure
  · intro r
    apply Integrable.smul_measure
    · exact (jointLawMixtureEmbedding_measurableEmbedding S r).integrable_map_iff.mpr
        (by simpa only [Function.comp_apply] using hf r)
    · exact ENNReal.ofReal_ne_top
  · exact Summable.of_finite

/-- Integrating under the raw joint-law mixture gives the weighted component sum. -/
theorem integral_jointLawMixtureMeasure {n ell : ℕ}
    (S : Fin ell → JointLawCollaborationSetting n)
    (w : Fin ell → ℝ) (hw_nonneg : ∀ r, 0 ≤ w r)
    {f : (Sigma fun r : Fin ell => (S r).X) × Label → ℝ}
    (hf : ∀ r, Integrable
      (fun z : (S r).X × Label => f (jointLawMixtureEmbedding S r z))
      (S r).joint) :
    (∫ z, f z ∂jointLawMixtureMeasure S w) =
      ∑ r, w r *
        ∫ z, f (jointLawMixtureEmbedding S r z) ∂(S r).joint := by
  unfold jointLawMixtureMeasure
  rw [integral_sum_measure (integrable_jointLawMixtureMeasure S w hf),
    tsum_fintype]
  refine Finset.sum_congr rfl ?_
  intro r _hr
  rw [integral_smul_measure]
  have hmap :
      (∫ z, f z ∂Measure.map (jointLawMixtureEmbedding S r) (S r).joint) =
        ∫ z, f (jointLawMixtureEmbedding S r z) ∂(S r).joint :=
    (jointLawMixtureEmbedding_measurableEmbedding S r).integral_map f
  rw [hmap]
  simp only [ENNReal.toReal_ofReal (hw_nonneg r), smul_eq_mul]

namespace JointLawCollaborationSetting

/-- The bounded measurable source agent-certainty integrand is integrable. -/
theorem predictionCertainty_integrable {n : ℕ}
    (S : JointLawCollaborationSetting n) (i : Fin n) :
    Integrable
      (fun z : S.X × Label =>
        max (S.pred i z.1) (1 - S.pred i z.1)) S.joint := by
  letI : IsProbabilityMeasure S.joint := S.isProbability
  have hpred : Measurable (fun z : S.X × Label => S.pred i z.1) :=
    (S.pred_measurable i).comp measurable_fst
  refine Integrable.of_bound
    (hpred.max (measurable_const.sub hpred)).aestronglyMeasurable 1
    (.of_forall ?_)
  intro z
  have hrange := S.pred_range i z.1
  have hnonneg : 0 ≤ max (S.pred i z.1) (1 - S.pred i z.1) :=
    le_trans hrange.1 (le_max_left _ _)
  have hle : max (S.pred i z.1) (1 - S.pred i z.1) ≤ 1 :=
    max_le hrange.2 (by linarith [hrange.1])
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact hle

/--
The C-independent raw joint-law mixture from source Proposition 6.  Its
input space is the dependent disjoint union, and it inherits each predictor
from its selected component while retaining the component's actual labels.
-/
noncomputable def mix {n ell : ℕ}
    (S : Fin ell → JointLawCollaborationSetting n)
    (w : Fin ell → ℝ) (hw_nonneg : ∀ r, 0 ≤ w r)
    (hw_sum : ∑ r, w r = 1) : JointLawCollaborationSetting n where
  X := Sigma fun r : Fin ell => (S r).X
  measurableSpaceX := inferInstance
  joint := jointLawMixtureMeasure S w
  isProbability := ⟨jointLawMixtureMeasure_univ S w hw_nonneg hw_sum⟩
  pred := fun i z => (S z.1).pred i z.2
  pred_range := fun i z => (S z.1).pred_range i z.2
  pred_measurable := by
    intro i
    apply jointLawMixture_measurable_of_fiberwise
    intro r
    simpa using (S r).pred_measurable i
  calibrated_events := by
    intro i A hA
    let lhs : (Sigma fun r : Fin ell => (S r).X) × Label → ℝ := fun z =>
      ({z | (S z.1.1).pred i z.1.2 ∈ A ∧ z.2 = true}.indicator
        (fun _ => (1 : ℝ))) z
    let rhs : (Sigma fun r : Fin ell => (S r).X) × Label → ℝ := fun z =>
      ({z | (S z.1.1).pred i z.1.2 ∈ A}.indicator
        (fun z => (S z.1.1).pred i z.1.2)) z
    have hlhs (r : Fin ell) : Integrable
        (fun z : (S r).X × Label => lhs (jointLawMixtureEmbedding S r z))
        (S r).joint := by
      letI : IsProbabilityMeasure (S r).joint := (S r).isProbability
      have hpredEvent : MeasurableSet
          {z : (S r).X × Label | (S r).pred i z.1 ∈ A} :=
        ((S r).pred_measurable i).comp measurable_fst hA
      have hlabel : MeasurableSet {z : (S r).X × Label | z.2 = true} :=
        measurable_snd (measurableSet_singleton true)
      change Integrable
        ({z : (S r).X × Label | (S r).pred i z.1 ∈ A ∧ z.2 = true}.indicator
          (fun _ => (1 : ℝ))) (S r).joint
      exact (integrable_const (1 : ℝ)).indicator (hpredEvent.inter hlabel)
    have hrhs (r : Fin ell) : Integrable
        (fun z : (S r).X × Label => rhs (jointLawMixtureEmbedding S r z))
        (S r).joint := by
      letI : IsProbabilityMeasure (S r).joint := (S r).isProbability
      have hpred : Measurable (fun z : (S r).X × Label => (S r).pred i z.1) :=
        ((S r).pred_measurable i).comp measurable_fst
      have hpredEvent : MeasurableSet
          {z : (S r).X × Label | (S r).pred i z.1 ∈ A} := hpred hA
      have hpint : Integrable
          (fun z : (S r).X × Label => (S r).pred i z.1) (S r).joint := by
        refine Integrable.of_bound hpred.aestronglyMeasurable 1 (.of_forall ?_)
        intro z
        have hrange := (S r).pred_range i z.1
        rw [Real.norm_eq_abs, abs_of_nonneg hrange.1]
        exact hrange.2
      change Integrable
        ({z : (S r).X × Label | (S r).pred i z.1 ∈ A}.indicator
          (fun z => (S r).pred i z.1)) (S r).joint
      exact hpint.indicator hpredEvent
    change (∫ z, lhs z ∂jointLawMixtureMeasure S w) =
      ∫ z, rhs z ∂jointLawMixtureMeasure S w
    rw [integral_jointLawMixtureMeasure S w hw_nonneg hlhs,
      integral_jointLawMixtureMeasure S w hw_nonneg hrhs]
    refine Finset.sum_congr rfl ?_
    intro r _hr
    change w r *
        (∫ z : (S r).X × Label,
          ({z | (S r).pred i z.1 ∈ A ∧ z.2 = true}.indicator
            (fun _ => (1 : ℝ))) z ∂(S r).joint) =
      w r * ∫ z : (S r).X × Label,
        ({z | (S r).pred i z.1 ∈ A}.indicator
          (fun z => (S r).pred i z.1)) z ∂(S r).joint
    rw [(S r).calibrated_events i A hA]

/-- The raw joint-law mixture preserves each agent's source accuracy exactly. -/
theorem agentAccuracy_mix {n ell : ℕ}
    (S : Fin ell → JointLawCollaborationSetting n)
    (w : Fin ell → ℝ) (hw_nonneg : ∀ r, 0 ≤ w r)
    (hw_sum : ∑ r, w r = 1) (i : Fin n) :
    (mix S w hw_nonneg hw_sum).agentAccuracy i =
      ∑ r, w r * (S r).agentAccuracy i := by
  calc
    (mix S w hw_nonneg hw_sum).agentAccuracy i =
        ∫ z : (Sigma fun r : Fin ell => (S r).X) × Label,
          max ((mix S w hw_nonneg hw_sum).pred i z.1)
            (1 - (mix S w hw_nonneg hw_sum).pred i z.1)
          ∂jointLawMixtureMeasure S w :=
      (agentAccuracy_eq_predictionCertainty (mix S w hw_nonneg hw_sum) i)
    _ = ∑ r, w r *
        ∫ z : (S r).X × Label,
          max ((S r).pred i z.1) (1 - (S r).pred i z.1) ∂(S r).joint := by
      apply integral_jointLawMixtureMeasure S w hw_nonneg
      intro r
      simpa [mix, jointLawMixtureEmbedding] using
        (S r).predictionCertainty_integrable i
    _ = ∑ r, w r * (S r).agentAccuracy i := by
      refine Finset.sum_congr rfl ?_
      intro r _hr
      rw [← (S r).agentAccuracy_eq_predictionCertainty i]

/-- Componentwise strategy well-formedness implies it for the same raw mixture. -/
theorem strategyWellFormed_mix {n ell : ℕ}
    (S : Fin ell → JointLawCollaborationSetting n)
    (w : Fin ell → ℝ) (hw_nonneg : ∀ r, 0 ≤ w r)
    (hw_sum : ∑ r, w r = 1) (C : CollaborationStrategy n)
    (hC : ∀ r, (S r).StrategyWellFormed C) :
    (mix S w hw_nonneg hw_sum).StrategyWellFormed C := by
  unfold StrategyWellFormed strategyClassifier
  apply integrable_jointLawMixtureMeasure S w
  intro r
  simpa [mix, jointLawMixtureEmbedding, StrategyWellFormed,
    strategyClassifier] using hC r

/-- The raw joint-law mixture preserves every componentwise well-formed strategy accuracy. -/
theorem strategyAccuracy_mix {n ell : ℕ}
    (S : Fin ell → JointLawCollaborationSetting n)
    (w : Fin ell → ℝ) (hw_nonneg : ∀ r, 0 ≤ w r)
    (hw_sum : ∑ r, w r = 1) (C : CollaborationStrategy n)
    (hC : ∀ r, (S r).StrategyWellFormed C) :
    (mix S w hw_nonneg hw_sum).strategyAccuracy C =
      ∑ r, w r * (S r).strategyAccuracy C := by
  unfold strategyAccuracy classifierAccuracy strategyClassifier
  apply integral_jointLawMixtureMeasure S w hw_nonneg
  intro r
  simpa [mix, jointLawMixtureEmbedding, StrategyWellFormed,
    strategyClassifier] using hC r

end JointLawCollaborationSetting

end PKG25NoFreeLunch
