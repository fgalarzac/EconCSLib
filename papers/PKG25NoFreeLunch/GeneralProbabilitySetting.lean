import Mathlib.Probability.ProbabilityMassFunction.Integrals
import PKG25NoFreeLunch.ParameterizedS1

/-!
# PKG25 legacy eta-based probability-space model

This historical module represents a joint law indirectly as an input measure
and a pointwise label-one function `eta`.  Its positive exact-fiber calibration
field is vacuous for atomless reported-prediction laws, so it is not the
paper-facing source model and must not be used to support a source statement.
`JointSourceModel.lean` instead records the raw `X x {0,1}` law and explicit
event-calibration convention used by `PaperInterface.lean`.

The definitions and finite helper proofs below are retained for historical
implementation compatibility only.  New source-facing rows must use the raw
joint-law modules rather than `ProbabilityCollaborationSetting` or
`ReliableProbability`.
-/

open MeasureTheory

namespace PKG25NoFreeLunch

namespace FiniteCollaborationSetting

/--
For a finite calibrated predictor, expected classifier correctness equals the
source display `E[max(P_i(X), 1-P_i(X))]`.  The proof groups the finite input
space by prediction value and applies calibration on each fiber.
-/
theorem agentAccuracy_eq_predictionCertainty {n : ℕ}
    (S : FiniteCollaborationSetting n) (i : Fin n) :
    S.agentAccuracy i =
      ∑ x : S.X, S.mass x * max (S.pred i x) (1 - S.pred i x) := by
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
  unfold FiniteCollaborationSetting.agentAccuracy
    FiniteCollaborationSetting.agentClassifier
  rw [hfiber, hfiber]
  refine Finset.sum_congr rfl ?_
  intro p hp
  have hleft :
      (∑ x ∈ (Finset.univ : Finset S.X) with S.pred i x = p,
          S.mass x * pointAccuracy (roundProb (S.pred i x)) (S.eta x)) =
        ∑ x ∈ (Finset.univ : Finset S.X) with S.pred i x = p,
          S.mass x * pointAccuracy (roundProb p) (S.eta x) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  have hright :
      (∑ x ∈ (Finset.univ : Finset S.X) with S.pred i x = p,
          S.mass x * max (S.pred i x) (1 - S.pred i x)) =
        ∑ x ∈ (Finset.univ : Finset S.X) with S.pred i x = p,
          S.mass x * max p (1 - p) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  rw [hleft, hright]
  have hmass :
      (∑ x ∈ (Finset.univ : Finset S.X) with S.pred i x = p, S.mass x) =
        eventMass S.mass (fun x : S.X => S.pred i x = p) := by
    simpa [eventMass] using
      (Finset.sum_filter (s := (Finset.univ : Finset S.X))
        (fun x : S.X => S.pred i x = p) S.mass)
  have hlabel :
      (∑ x ∈ (Finset.univ : Finset S.X) with S.pred i x = p,
          S.mass x * S.eta x) =
        eventLabelMass S.mass S.eta (fun x : S.X => S.pred i x = p) := by
    simpa [eventLabelMass] using
      (Finset.sum_filter (s := (Finset.univ : Finset S.X))
        (fun x : S.X => S.pred i x = p) (fun x => S.mass x * S.eta x))
  have hcal := S.calibrated_unconditional i p
  by_cases hhalf : (1 : ℝ) / 2 ≤ p
  · have hround : roundProb p = true := roundProb_eq_true_iff.mpr hhalf
    have hmax : max p (1 - p) = p := max_eq_left (by linarith)
    simp only [hround, pointAccuracy, if_true, hmax]
    rw [hlabel, hcal, ← hmass, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro x hx
    ring
  · have hplt : p < (1 : ℝ) / 2 := lt_of_not_ge hhalf
    have hround : roundProb p = false := roundProb_eq_false_iff.mpr hplt
    have hmax : max p (1 - p) = 1 - p := max_eq_right (by linarith)
    simp only [hround, pointAccuracy, hmax]
    calc
      (∑ x ∈ (Finset.univ : Finset S.X) with S.pred i x = p,
          S.mass x * (1 - S.eta x)) =
          (∑ x ∈ (Finset.univ : Finset S.X) with S.pred i x = p, S.mass x) -
            ∑ x ∈ (Finset.univ : Finset S.X) with S.pred i x = p,
              S.mass x * S.eta x := by
                rw [← Finset.sum_sub_distrib]
                refine Finset.sum_congr rfl ?_
                intro x hx
                ring
      _ = eventMass S.mass (fun x : S.X => S.pred i x = p) -
            eventLabelMass S.mass S.eta (fun x : S.X => S.pred i x = p) := by
              rw [hmass, hlabel]
      _ = eventMass S.mass (fun x : S.X => S.pred i x = p) -
            p * eventMass S.mass (fun x : S.X => S.pred i x = p) := by
              rw [hcal]
      _ = ∑ x ∈ (Finset.univ : Finset S.X) with S.pred i x = p,
            S.mass x * (1 - p) := by
              rw [← hmass]
              rw [← Finset.sum_mul]
              ring

/-- Finite calibration summed over any collection of prediction values. -/
theorem calibrated_on_prediction_set {n : ℕ}
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

end FiniteCollaborationSetting

/--
An arbitrary probability-space collaboration setting, independent of strategy.

`eta x` is the conditional probability of label one and `pred i x` is agent
`i`'s probability forecast.  Calibration is recorded on every
positive-probability exact prediction fiber, exactly as in the source
definition.  The denominator-free integral identity is then extended to null
fibers below.  Strategy-specific expectation well-formedness is recorded by
`StrategyWellFormed`, not baked into this source setting.  Event-level
calibration is proved separately for the
partition-generated predictors used by the source constructions; requiring it
here would silently restrict the paper's stated collaboration-setting
universe.
-/
structure ProbabilityCollaborationSetting (n : ℕ) where
  X : Type
  [measurableSpaceX : MeasurableSpace X]
  μ : Measure X
  isProbability : IsProbabilityMeasure μ
  eta : X → ℝ
  eta_range : ∀ x, 0 ≤ eta x ∧ eta x ≤ 1
  eta_integrable : Integrable eta μ
  pred : Fin n → X → ℝ
  pred_range : ∀ i x, 0 ≤ pred i x ∧ pred i x ≤ 1
  pred_measurable : ∀ i, Measurable (pred i)
  calibrated_positive :
    ∀ i : Fin n, ∀ p : ℝ, μ {x | pred i x = p} ≠ 0 →
      (∫ x, ({x | pred i x = p}.indicator eta) x ∂μ) =
        p * ∫ x,
          ({x | pred i x = p}.indicator (fun _ => (1 : ℝ))) x ∂μ

namespace ProbabilityCollaborationSetting

attribute [instance] measurableSpaceX

/--
The source's exact-prediction-fiber display, extended harmlessly to null
fibers.  On a positive-probability fiber it is the structure's source
assumption; on a null fiber both integrals vanish.
-/
theorem calibrated {n : ℕ}
    (S : ProbabilityCollaborationSetting n) (i : Fin n) (p : ℝ) :
    (∫ x, ({x | S.pred i x = p}.indicator S.eta) x ∂S.μ) =
      p * ∫ x,
        ({x | S.pred i x = p}.indicator (fun _ => (1 : ℝ))) x ∂S.μ := by
  by_cases hzero : S.μ {x | S.pred i x = p} = 0
  · have hset : MeasurableSet {x | S.pred i x = p} :=
      (S.pred_measurable i) (measurableSet_singleton p)
    rw [integral_indicator hset, integral_indicator hset]
    simp [MeasureTheory.measureReal_def, hzero]
  · exact S.calibrated_positive i p hzero

/-- The binary classifier induced by agent `i`. -/
noncomputable def agentClassifier {n : ℕ}
    (S : ProbabilityCollaborationSetting n) (i : Fin n) (x : S.X) : Label :=
  roundProb (S.pred i x)

/-- The bounded measurable source agent-accuracy integrand is integrable. -/
theorem predictionCertainty_integrable {n : ℕ}
    (S : ProbabilityCollaborationSetting n) (i : Fin n) :
    Integrable (fun x => max (S.pred i x) (1 - S.pred i x)) S.μ := by
  letI : IsProbabilityMeasure S.μ := S.isProbability
  have hPmeas : Measurable (S.pred i) := S.pred_measurable i
  refine Integrable.of_bound
    (hPmeas.max (measurable_const.sub hPmeas)).aestronglyMeasurable 1
    (.of_forall ?_)
  intro x
  have hPrange := S.pred_range i x
  have hnonneg : 0 ≤ max (S.pred i x) (1 - S.pred i x) :=
    le_trans hPrange.1 (le_max_left _ _)
  have hle : max (S.pred i x) (1 - S.pred i x) ≤ 1 :=
    max_le hPrange.2 (by linarith [hPrange.1])
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact hle

/-- The classifier induced by a chosen collaboration strategy. -/
def strategyClassifier {n : ℕ}
    (S : ProbabilityCollaborationSetting n)
    (C : CollaborationStrategy n) (x : S.X) : Label :=
  C (fun i => S.pred i x)

/--
The ordinary implicit well-formedness premise for the source expectation
defining a strategy's accuracy in a particular setting.
-/
def StrategyWellFormed {n : ℕ} (S : ProbabilityCollaborationSetting n)
    (C : CollaborationStrategy n) : Prop :=
  Integrable (fun x => pointAccuracy (S.strategyClassifier C x) (S.eta x)) S.μ

/-- Source expected correctness of an individual agent. -/
noncomputable def agentAccuracy {n : ℕ}
    (S : ProbabilityCollaborationSetting n) (i : Fin n) : ℝ :=
  ∫ x, max (S.pred i x) (1 - S.pred i x) ∂S.μ

/-- Source expected correctness of the collaboration strategy. -/
noncomputable def strategyAccuracy {n : ℕ}
    (S : ProbabilityCollaborationSetting n)
    (C : CollaborationStrategy n) : ℝ :=
  ∫ x, pointAccuracy (S.strategyClassifier C x) (S.eta x) ∂S.μ

end ProbabilityCollaborationSetting

/-! ## Finite weighted mixtures of arbitrary settings -/

/-- Each inclusion into a dependent disjoint union is measurable. -/
theorem probabilityMixture_sigmaMk_measurable
    {α : Type*} {β : α → Type*} [∀ a, MeasurableSpace (β a)] (a : α) :
    Measurable (fun x : β a => Sigma.mk a x) :=
  Measurable.of_le_map (iInf_le _ a)

/-- A function out of the dependent disjoint union is measurable fiberwise. -/
theorem probabilityMixture_measurable_of_fiberwise
    {α : Type*} {β : α → Type*} [∀ a, MeasurableSpace (β a)]
    {γ : Type*} [MeasurableSpace γ] {f : Sigma β → γ}
    (hf : ∀ a, Measurable (fun x : β a => f (Sigma.mk a x))) :
    Measurable f :=
  Measurable.of_comap_le <| le_iInf fun a =>
    MeasurableSpace.comap_le_iff_le_map.2 (hf a)

/-- Each inclusion into a dependent disjoint union is a measurable embedding. -/
theorem probabilityMixture_sigmaMk_measurableEmbedding
    {α : Type*} {β : α → Type*} [DecidableEq α]
    [∀ a, MeasurableSpace (β a)] (a : α) :
    MeasurableEmbedding (fun x : β a => Sigma.mk a x) where
  injective := sigma_mk_injective
  measurable := probabilityMixture_sigmaMk_measurable a
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

/--
The source Proposition 6 measure: scale each arbitrary component measure and
push it into the corresponding summand of the dependent disjoint union.
-/
noncomputable def probabilityMixtureMeasure {n ell : ℕ}
    (S : Fin ell → ProbabilityCollaborationSetting n)
    (w : Fin ell → ℝ) : Measure (Σ r, (S r).X) :=
  Measure.sum fun r =>
    ENNReal.ofReal (w r) •
      Measure.map
        (fun x : (S r).X =>
          @Sigma.mk (Fin ell) (fun r => (S r).X) r x)
        (S r).μ

/-- Simplex weights make the mixture measure a probability measure. -/
theorem probabilityMixtureMeasure_univ {n ell : ℕ}
    (S : Fin ell → ProbabilityCollaborationSetting n)
    (w : Fin ell → ℝ) (hw_nonneg : ∀ r, 0 ≤ w r)
    (hw_sum : ∑ r, w r = 1) :
    probabilityMixtureMeasure S w Set.univ = 1 := by
  have hmap (r : Fin ell) :
      Measure.map
          (fun x : (S r).X =>
            @Sigma.mk (Fin ell) (fun r => (S r).X) r x)
          (S r).μ Set.univ = 1 := by
    calc
      Measure.map
          (fun x : (S r).X =>
            @Sigma.mk (Fin ell) (fun r => (S r).X) r x)
          (S r).μ Set.univ = (S r).μ Set.univ := by
            simpa only [Set.preimage_univ] using
              (Measure.map_apply (μ := (S r).μ)
                (probabilityMixture_sigmaMk_measurable r)
                (s := Set.univ) MeasurableSet.univ)
      _ = 1 := (S r).isProbability.measure_univ
  simp only [probabilityMixtureMeasure,
    Measure.sum_apply _ MeasurableSet.univ, Measure.smul_apply, hmap,
    smul_eq_mul, mul_one]
  rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg]
  · rw [hw_sum]
    simp
  · exact fun r _ => hw_nonneg r

/--
On every measurable component event, the mixture measure is the component
measure multiplied by its weight.  This is the measure-theoretic form of the
source's point-mass display and remains valid on continuous input spaces.
-/
theorem probabilityMixtureMeasure_component_image {n ell : ℕ}
    (S : Fin ell → ProbabilityCollaborationSetting n)
    (w : Fin ell → ℝ) (r : Fin ell) (A : Set (S r).X)
    (hA : MeasurableSet A) :
    probabilityMixtureMeasure S w
        ((fun x : (S r).X =>
          @Sigma.mk (Fin ell) (fun r => (S r).X) r x) '' A) =
      ENNReal.ofReal (w r) * (S r).μ A := by
  let E : Set (Σ r, (S r).X) :=
    (fun x : (S r).X =>
      @Sigma.mk (Fin ell) (fun r => (S r).X) r x) '' A
  have hE : MeasurableSet E :=
    (probabilityMixture_sigmaMk_measurableEmbedding r).measurableSet_image' hA
  change probabilityMixtureMeasure S w E = _
  rw [probabilityMixtureMeasure, Measure.sum_apply _ hE, tsum_fintype]
  rw [Finset.sum_eq_single r]
  · rw [Measure.smul_apply,
      Measure.map_apply (probabilityMixture_sigmaMk_measurable r) hE]
    change ENNReal.ofReal (w r) * (S r).μ
      ((fun x : (S r).X =>
        @Sigma.mk (Fin ell) (fun r => (S r).X) r x) ⁻¹' E) = _
    rw [show (fun x : (S r).X =>
        @Sigma.mk (Fin ell) (fun r => (S r).X) r x) ⁻¹' E = A by
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩
        exact (sigma_mk_injective hxy).symm ▸ hy
      · intro hx
        exact ⟨x, hx, rfl⟩]
  · intro k _hk hkr
    have hempty :
        (fun x : (S k).X =>
          @Sigma.mk (Fin ell) (fun r => (S r).X) k x) ⁻¹' E = ∅ := by
      ext x
      simp only [E, Set.mem_preimage, Set.mem_image, Set.mem_empty_iff_false,
        iff_false]
      rintro ⟨y, _hy, hxy⟩
      exact hkr (Sigma.mk.inj_iff.mp hxy).1.symm
    rw [Measure.smul_apply,
      Measure.map_apply (probabilityMixture_sigmaMk_measurable k) hE,
      hempty, measure_empty]
    simp
  · intro hr
    exact (hr (Finset.mem_univ r)).elim

/-- Fiberwise integrability implies integrability under the finite mixture. -/
theorem integrable_probabilityMixtureMeasure {n ell : ℕ}
    (S : Fin ell → ProbabilityCollaborationSetting n)
    (w : Fin ell → ℝ) {f : (Σ r, (S r).X) → ℝ}
    (hf : ∀ r, Integrable
      (fun x : (S r).X =>
        f (@Sigma.mk (Fin ell) (fun r => (S r).X) r x)) (S r).μ) :
    Integrable f (probabilityMixtureMeasure S w) := by
  apply integrable_sum_measure
  · intro r
    apply Integrable.smul_measure
    · exact (probabilityMixture_sigmaMk_measurableEmbedding r).integrable_map_iff.mpr
        (by simpa only [Function.comp_apply] using hf r)
    · exact ENNReal.ofReal_ne_top
  · exact Summable.of_finite

/-- Integrating under the mixture gives the weighted sum of component integrals. -/
theorem integral_probabilityMixtureMeasure {n ell : ℕ}
    (S : Fin ell → ProbabilityCollaborationSetting n)
    (w : Fin ell → ℝ) (hw_nonneg : ∀ r, 0 ≤ w r)
    {f : (Σ r, (S r).X) → ℝ}
    (hf : ∀ r, Integrable
      (fun x : (S r).X =>
        f (@Sigma.mk (Fin ell) (fun r => (S r).X) r x)) (S r).μ) :
    (∫ z, f z ∂probabilityMixtureMeasure S w) =
      ∑ r, w r *
        ∫ x, f (@Sigma.mk (Fin ell) (fun r => (S r).X) r x) ∂(S r).μ := by
  unfold probabilityMixtureMeasure
  rw [integral_sum_measure (integrable_probabilityMixtureMeasure S w hf),
    tsum_fintype]
  refine Finset.sum_congr rfl ?_
  intro r _hr
  rw [integral_smul_measure]
  have hmap :
      (∫ z, f z ∂Measure.map
        (fun x : (S r).X =>
          @Sigma.mk (Fin ell) (fun r => (S r).X) r x) (S r).μ) =
        ∫ x, f (@Sigma.mk (Fin ell) (fun r => (S r).X) r x) ∂(S r).μ :=
    (probabilityMixture_sigmaMk_measurableEmbedding r).integral_map f
  rw [hmap]
  simp only [ENNReal.toReal_ofReal (hw_nonneg r), smul_eq_mul]

/--
The C-independent arbitrary-setting mixture from Proposition 6.  Its input
space is the dependent disjoint union, and it inherits labels and predictors
from the selected component.
-/
noncomputable def ProbabilityCollaborationSetting.mix {n ell : ℕ}
    (S : Fin ell → ProbabilityCollaborationSetting n)
    (w : Fin ell → ℝ) (hw_nonneg : ∀ r, 0 ≤ w r)
    (hw_sum : ∑ r, w r = 1) : ProbabilityCollaborationSetting n where
  X := Σ r, (S r).X
  measurableSpaceX := inferInstance
  μ := probabilityMixtureMeasure S w
  isProbability := ⟨probabilityMixtureMeasure_univ S w hw_nonneg hw_sum⟩
  eta := fun z => (S z.1).eta z.2
  eta_range := fun z => (S z.1).eta_range z.2
  eta_integrable := by
    apply integrable_probabilityMixtureMeasure S w
    intro r
    exact (S r).eta_integrable
  pred := fun i z => (S z.1).pred i z.2
  pred_range := fun i z => (S z.1).pred_range i z.2
  pred_measurable := by
    intro i
    apply probabilityMixture_measurable_of_fiberwise
    intro r
    simpa using (S r).pred_measurable i
  calibrated_positive := by
    intro i p _hpos
    let labelFiber : (Σ r, (S r).X) → ℝ := fun z =>
      ({z | (S z.1).pred i z.2 = p}.indicator
        (fun z => (S z.1).eta z.2)) z
    let massFiber : (Σ r, (S r).X) → ℝ := fun z =>
      ({z | (S z.1).pred i z.2 = p}.indicator
        (fun _ => (1 : ℝ))) z
    have hlabel (r : Fin ell) : Integrable
        (fun x : (S r).X =>
          labelFiber (@Sigma.mk (Fin ell) (fun r => (S r).X) r x)) (S r).μ := by
      change Integrable
        (fun x : (S r).X =>
          ({x | (S r).pred i x = p}.indicator (S r).eta) x) (S r).μ
      exact (S r).eta_integrable.indicator
        ((S r).pred_measurable i (measurableSet_singleton p))
    have hmass (r : Fin ell) : Integrable
        (fun x : (S r).X =>
          massFiber (@Sigma.mk (Fin ell) (fun r => (S r).X) r x)) (S r).μ := by
      letI : IsProbabilityMeasure (S r).μ := (S r).isProbability
      change Integrable
        (fun x : (S r).X =>
          ({x | (S r).pred i x = p}.indicator (fun _ => (1 : ℝ))) x) (S r).μ
      exact (integrable_const (1 : ℝ)).indicator
        ((S r).pred_measurable i (measurableSet_singleton p))
    change (∫ z, labelFiber z ∂probabilityMixtureMeasure S w) =
      p * ∫ z, massFiber z ∂probabilityMixtureMeasure S w
    rw [integral_probabilityMixtureMeasure S w hw_nonneg hlabel,
      integral_probabilityMixtureMeasure S w hw_nonneg hmass,
      Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro r _hr
    change w r *
        (∫ x, ({x | (S r).pred i x = p}.indicator (S r).eta) x ∂(S r).μ) =
      p * (w r *
        ∫ x, ({x | (S r).pred i x = p}.indicator
          (fun _ => (1 : ℝ))) x ∂(S r).μ)
    rw [(S r).calibrated i p]
    ring

/-- The arbitrary-setting mixture preserves each agent's accuracy exactly. -/
theorem ProbabilityCollaborationSetting.agentAccuracy_mix {n ell : ℕ}
    (S : Fin ell → ProbabilityCollaborationSetting n)
    (w : Fin ell → ℝ) (hw_nonneg : ∀ r, 0 ≤ w r)
    (hw_sum : ∑ r, w r = 1) (i : Fin n) :
    (ProbabilityCollaborationSetting.mix S w hw_nonneg hw_sum).agentAccuracy i =
      ∑ r, w r * (S r).agentAccuracy i := by
  unfold ProbabilityCollaborationSetting.agentAccuracy
  apply integral_probabilityMixtureMeasure S w hw_nonneg
  intro r
  exact (S r).predictionCertainty_integrable i

/--
For every strategy, component well-formedness implies well-formedness on the
same C-independent mixture setting.
-/
theorem ProbabilityCollaborationSetting.strategyWellFormed_mix {n ell : ℕ}
    (S : Fin ell → ProbabilityCollaborationSetting n)
    (w : Fin ell → ℝ) (hw_nonneg : ∀ r, 0 ≤ w r)
    (hw_sum : ∑ r, w r = 1) (C : CollaborationStrategy n)
    (hC : ∀ r, (S r).StrategyWellFormed C) :
    (ProbabilityCollaborationSetting.mix S w hw_nonneg hw_sum).StrategyWellFormed C := by
  unfold ProbabilityCollaborationSetting.StrategyWellFormed
    ProbabilityCollaborationSetting.strategyClassifier
  apply integrable_probabilityMixtureMeasure S w
  intro r
  simpa [ProbabilityCollaborationSetting.StrategyWellFormed,
    ProbabilityCollaborationSetting.strategyClassifier] using hC r

/-- The arbitrary-setting mixture preserves every well-formed strategy accuracy exactly. -/
theorem ProbabilityCollaborationSetting.strategyAccuracy_mix {n ell : ℕ}
    (S : Fin ell → ProbabilityCollaborationSetting n)
    (w : Fin ell → ℝ) (hw_nonneg : ∀ r, 0 ≤ w r)
    (hw_sum : ∑ r, w r = 1) (C : CollaborationStrategy n)
    (hC : ∀ r, (S r).StrategyWellFormed C) :
    (ProbabilityCollaborationSetting.mix S w hw_nonneg hw_sum).strategyAccuracy C =
      ∑ r, w r * (S r).strategyAccuracy C := by
  unfold ProbabilityCollaborationSetting.strategyAccuracy
    ProbabilityCollaborationSetting.strategyClassifier
  apply integral_probabilityMixtureMeasure S w hw_nonneg
  intro r
  simpa [ProbabilityCollaborationSetting.StrategyWellFormed,
    ProbabilityCollaborationSetting.strategyClassifier] using hC r

/-! ## Exact embedding of every finite witness -/

/-- The probability mass function associated with a finite collaboration setting. -/
noncomputable def finiteCollaborationPMF {n : ℕ}
    (S : FiniteCollaborationSetting n) : PMF S.X :=
  PMF.ofFintype (fun x => ENNReal.ofReal (S.mass x)) (by
    have hnonneg :
        ∀ x ∈ (Finset.univ : Finset S.X), 0 ≤ S.mass x := by
      intro x _hx
      exact S.mass_nonneg x
    calc
      (∑ x : S.X, ENNReal.ofReal (S.mass x)) =
          ENNReal.ofReal (∑ x : S.X, S.mass x) := by
            rw [ENNReal.ofReal_sum_of_nonneg hnonneg]
      _ = 1 := by rw [S.mass_sum]; simp)

@[simp] theorem finiteCollaborationPMF_apply_toReal {n : ℕ}
    (S : FiniteCollaborationSetting n) (x : S.X) :
    (finiteCollaborationPMF S x).toReal = S.mass x := by
  unfold finiteCollaborationPMF
  rw [PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal (S.mass_nonneg x)

/--
Every finite calibrated witness is an honest arbitrary probability-space
setting, using the discrete sigma algebra and its exact probability mass
function.
-/
noncomputable def ProbabilityCollaborationSetting.ofFinite {n : ℕ}
    (S : FiniteCollaborationSetting n) :
    ProbabilityCollaborationSetting n := by
  letI : MeasurableSpace S.X := ⊤
  exact
    { X := S.X
      measurableSpaceX := inferInstance
      μ := (finiteCollaborationPMF S).toMeasure
      isProbability := inferInstance
      eta := S.eta
      eta_range := S.eta_range
      eta_integrable := Integrable.of_finite
      pred := S.pred
      pred_range := S.pred_range
      pred_measurable := fun i => measurable_of_finite (S.pred i)
      calibrated_positive := by
        intro i p _hpos
        rw [PMF.integral_eq_sum, PMF.integral_eq_sum]
        simpa [Set.indicator, smul_eq_mul, eventLabelMass, eventMass] using
          S.calibrated_unconditional i p }

theorem ProbabilityCollaborationSetting.ofFinite_agentAccuracy
    {n : ℕ} (S : FiniteCollaborationSetting n)
    (i : Fin n) :
    (ProbabilityCollaborationSetting.ofFinite S).agentAccuracy i =
      S.agentAccuracy i := by
  letI : MeasurableSpace S.X := ⊤
  unfold ProbabilityCollaborationSetting.agentAccuracy
    FiniteCollaborationSetting.agentAccuracy
  change
    (∫ x : S.X, max (S.pred i x) (1 - S.pred i x)
      ∂(finiteCollaborationPMF S).toMeasure) =
      ∑ x : S.X,
        S.mass x * pointAccuracy (S.agentClassifier i x) (S.eta x)
  rw [PMF.integral_eq_sum]
  simp only [finiteCollaborationPMF_apply_toReal, smul_eq_mul]
  exact (FiniteCollaborationSetting.agentAccuracy_eq_predictionCertainty S i).symm

theorem ProbabilityCollaborationSetting.ofFinite_strategyAccuracy
    {n : ℕ} (C : CollaborationStrategy n) (S : FiniteCollaborationSetting n) :
    (ProbabilityCollaborationSetting.ofFinite S).strategyAccuracy C =
      S.strategyAccuracy C := by
  letI : MeasurableSpace S.X := ⊤
  unfold ProbabilityCollaborationSetting.strategyAccuracy
    ProbabilityCollaborationSetting.strategyClassifier
    FiniteCollaborationSetting.strategyAccuracy
    FiniteCollaborationSetting.strategyClassifier
  change
    (∫ x : S.X, pointAccuracy (C (fun i => S.pred i x)) (S.eta x)
      ∂(finiteCollaborationPMF S).toMeasure) =
      ∑ x : S.X, S.mass x * pointAccuracy (C (fun i => S.pred i x)) (S.eta x)
  rw [PMF.integral_eq_sum]
  simp [smul_eq_mul]

/-- Every strategy is well formed on an embedded finite setting. -/
theorem ProbabilityCollaborationSetting.ofFinite_strategyWellFormed
    {n : ℕ} (C : CollaborationStrategy n) (S : FiniteCollaborationSetting n) :
    ProbabilityCollaborationSetting.StrategyWellFormed
      (ProbabilityCollaborationSetting.ofFinite S) C := by
  letI : MeasurableSpace S.X := ⊤
  unfold ProbabilityCollaborationSetting.StrategyWellFormed
    ProbabilityCollaborationSetting.strategyClassifier
  change Integrable
    (fun x : S.X => pointAccuracy (C (fun i => S.pred i x)) (S.eta x))
    (finiteCollaborationPMF S).toMeasure
  exact Integrable.of_finite

/-! ## Source reliability and the full probability-space theorem -/

/--
The source Definition 3: in every well-formed arbitrary probability-space
setting, the strategy is at least as accurate as some agent (equivalently, at
least as accurate as the least accurate agent).
-/
def ReliableProbability {n : ℕ} (C : CollaborationStrategy n) : Prop :=
  ∀ S : ProbabilityCollaborationSetting n,
    ProbabilityCollaborationSetting.StrategyWellFormed S C →
    ∃ i : Fin n, S.agentAccuracy i ≤ S.strategyAccuracy C

/-- General source reliability specializes to every finite calibrated witness. -/
theorem reliableFinite_of_reliableProbability {n : ℕ}
    {C : CollaborationStrategy n} (hrel : ReliableProbability C) :
    ReliableFinite C := by
  intro S
  rcases hrel (ProbabilityCollaborationSetting.ofFinite S)
      (ProbabilityCollaborationSetting.ofFinite_strategyWellFormed C S) with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  simpa [ProbabilityCollaborationSetting.ofFinite_agentAccuracy,
    ProbabilityCollaborationSetting.ofFinite_strategyAccuracy] using hi

/--
The paper's forward no-free-lunch theorem over its literal arbitrary
probability-space universe.
-/
theorem main_no_free_lunch_probability {n : ℕ} [Nonempty (Fin n)]
    (C : CollaborationStrategy n) :
    ReliableProbability C → NonCollaborative C := by
  intro hrel
  exact main_no_free_lunch_finite C
    (reliableFinite_of_reliableProbability hrel)

end PKG25NoFreeLunch
