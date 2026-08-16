import LG21TestOptionalPolicies.ObservedAccessContinuous
import Mathlib.Probability.Kernel.CompProdEqIff

/-!
# Conditional kernels after a measurable selection event

This is source-neutral infrastructure for the LG21 selected-action bridge.
For a raw joint law written as `μ ⊗ₘ κ`, it constructs the law obtained by
restricting to a measurable event in the observed/latent pair.  The selected
kernel is exactly the normalized restriction of the raw fibre kernel.

The final factorization deliberately requires every selected fibre to have
positive mass.  It does not manufacture a value on zero-mass fibres, and it
does not identify this kernel with a Gaussian formula, a PBO, or an action
payoff.  A paper-level application must either prove that hypothesis on its
claimed domain or add a separate almost-everywhere/zero-fibre argument.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The latent fibre selected by a joint observed/latent event. -/
def selectedFiber (event : Set (α × β)) (a : α) : Set β :=
  Prod.mk a ⁻¹' event

/-- The indicator density of a joint selection event. -/
def selectedIndicator (event : Set (α × β)) : α → β → ℝ≥0∞ :=
  fun a b => event.indicator 1 (a, b)

/-- Restrict each raw fibre to the corresponding joint-event fibre. -/
def selectedRestrictionKernel (κ : Kernel α β) [IsSFiniteKernel κ]
    (event : Set (α × β)) : Kernel α β :=
  κ.withDensity (selectedIndicator event)

theorem selectedIndicator_measurable {event : Set (α × β)}
    (hevent : MeasurableSet event) :
    Measurable (Function.uncurry (selectedIndicator event)) := by
  change Measurable (event.indicator (1 : α × β → ℝ≥0∞))
  exact measurable_one.indicator hevent

theorem selectedRestrictionKernel_apply {κ : Kernel α β} [IsSFiniteKernel κ]
    {event : Set (α × β)} (hevent : MeasurableSet event) (a : α) :
    selectedRestrictionKernel κ event a = (κ a).restrict (selectedFiber event a) := by
  rw [selectedRestrictionKernel, Kernel.withDensity_apply _
    (selectedIndicator_measurable hevent)]
  change (κ a).withDensity ((selectedFiber event a).indicator 1) = _
  rw [withDensity_indicator_one]
  exact (measurable_const.prodMk measurable_id) hevent

theorem selectedRestrictionKernel_isFinite {κ : Kernel α β} [IsFiniteKernel κ]
    (event : Set (α × β)) :
    IsFiniteKernel (selectedRestrictionKernel κ event) := by
  unfold selectedRestrictionKernel
  apply Kernel.isFiniteKernel_withDensity_of_bounded κ ENNReal.one_ne_top
  intro a b
  classical
  by_cases hab : (a, b) ∈ event <;> simp [selectedIndicator, hab]

/-- Restricting a joint law is the composition product with its restricted raw kernel. -/
theorem compProd_selectedRestrictionKernel {μ : Measure α} [SFinite μ]
    {κ : Kernel α β} [IsFiniteKernel κ] {event : Set (α × β)}
    (hevent : MeasurableSet event) :
    μ ⊗ₘ selectedRestrictionKernel κ event = (μ ⊗ₘ κ).restrict event := by
  have hfinite : IsFiniteKernel (κ.withDensity (selectedIndicator event)) := by
    simpa only [selectedRestrictionKernel] using
      (selectedRestrictionKernel_isFinite (κ := κ) event)
  letI : IsFiniteKernel (κ.withDensity (selectedIndicator event)) := hfinite
  change μ ⊗ₘ (κ.withDensity (selectedIndicator event)) = (μ ⊗ₘ κ).restrict event
  rw [Measure.compProd_withDensity (selectedIndicator_measurable hevent)]
  change (μ ⊗ₘ κ).withDensity (event.indicator 1) = (μ ⊗ₘ κ).restrict event
  rw [withDensity_indicator_one hevent]

/-- Raw probability of selection in each observed fibre. -/
def selectionMass (κ : Kernel α β) (event : Set (α × β)) (a : α) : ℝ≥0∞ :=
  κ a (selectedFiber event a)

theorem selectionMass_measurable {κ : Kernel α β} [IsSFiniteKernel κ]
    {event : Set (α × β)} (hevent : MeasurableSet event) :
    Measurable (selectionMass κ event) := by
  exact Kernel.measurable_kernel_prodMk_left hevent

/-- The raw selected-fibre density divided by its selected mass. -/
def selectedNormalizedDensity (κ : Kernel α β) (event : Set (α × β)) : α → β → ℝ≥0∞ :=
  fun a b => selectedIndicator event a b * (selectionMass κ event a)⁻¹

theorem selectedNormalizedDensity_measurable {κ : Kernel α β} [IsSFiniteKernel κ]
    {event : Set (α × β)} (hevent : MeasurableSet event) :
    Measurable (Function.uncurry (selectedNormalizedDensity κ event)) := by
  change Measurable (fun p : α × β =>
    event.indicator 1 p * (selectionMass κ event p.1)⁻¹)
  exact (measurable_one.indicator hevent).mul
    ((selectionMass_measurable hevent).inv.comp measurable_fst)

/-- The candidate conditional kernel after joint selection. -/
def selectedNormalizedKernel (κ : Kernel α β) [IsSFiniteKernel κ]
    (event : Set (α × β)) : Kernel α β :=
  κ.withDensity (selectedNormalizedDensity κ event)

/-- Each selected fibre is the literal normalized restriction of its raw kernel. -/
theorem selectedNormalizedKernel_apply {κ : Kernel α β} [IsSFiniteKernel κ]
    {event : Set (α × β)} (hevent : MeasurableSet event) (a : α) :
    selectedNormalizedKernel κ event a =
      lg21NormalizedRestriction (κ a) (selectedFiber event a) := by
  rw [selectedNormalizedKernel, Kernel.withDensity_apply _
    (selectedNormalizedDensity_measurable hevent)]
  change (κ a).withDensity
      (fun b => (selectedFiber event a).indicator 1 b *
        (κ a (selectedFiber event a))⁻¹) = _
  have hfiber : MeasurableSet (selectedFiber event a) :=
    (measurable_const.prodMk measurable_id) hevent
  rw [show (fun b => (selectedFiber event a).indicator 1 b *
      (κ a (selectedFiber event a))⁻¹) =
      (κ a (selectedFiber event a))⁻¹ •
        (selectedFiber event a).indicator 1 by
      funext b
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_comm _ _,
    withDensity_smul _ (measurable_one.indicator hfiber)]
  rw [withDensity_indicator_one hfiber]
  · rfl

theorem selectedNormalizedKernel_isSFinite {κ : Kernel α β} [IsMarkovKernel κ]
    {event : Set (α × β)}
    (hpositive : ∀ a, selectionMass κ event a ≠ 0) :
    IsSFiniteKernel (selectedNormalizedKernel κ event) := by
  unfold selectedNormalizedKernel
  apply Kernel.IsSFiniteKernel.withDensity κ
  intro a b
  apply ENNReal.mul_ne_top
  · classical
    by_cases hab : (a, b) ∈ event <;> simp [selectedIndicator, hab]
  · exact ENNReal.inv_ne_top.mpr (hpositive a)

theorem selectedNormalizedKernel_isMarkov {κ : Kernel α β} [IsMarkovKernel κ]
    {event : Set (α × β)} (hevent : MeasurableSet event)
    (hpositive : ∀ a, selectionMass κ event a ≠ 0) :
    IsMarkovKernel (selectedNormalizedKernel κ event) := by
  letI : IsSFiniteKernel (selectedNormalizedKernel κ event) :=
    selectedNormalizedKernel_isSFinite hpositive
  constructor
  intro a
  rw [selectedNormalizedKernel_apply hevent]
  apply lg21NormalizedRestriction_isProbability
  · exact hpositive a
  · exact measure_ne_top (κ a) _

/-- Reweighting the base measure is the same as a first-coordinate joint density. -/
theorem compProd_withDensity_left {μ : Measure α} [SFinite μ]
    {κ : Kernel α β} [IsSFiniteKernel κ] {density : α → ℝ≥0∞}
    (hdensity : Measurable density) :
    (μ.withDensity density) ⊗ₘ κ =
      (μ ⊗ₘ κ).withDensity (fun pair => density pair.1) := by
  ext target htarget
  rw [Measure.compProd_apply htarget]
  rw [lintegral_withDensity_eq_lintegral_mul μ hdensity
    (Kernel.measurable_kernel_prodMk_left htarget)]
  rw [withDensity_apply _ htarget, ← lintegral_indicator htarget,
    Measure.lintegral_compProd]
  · apply lintegral_congr
    intro a
    have hfiber : MeasurableSet (Prod.mk a ⁻¹' target) :=
      (measurable_const.prodMk measurable_id) htarget
    have hintegrand :
        (fun b : β => target.indicator (fun pair => density pair.1) (a, b)) =
          (Prod.mk a ⁻¹' target).indicator (fun _ => density a) := by
      funext b
      by_cases hab : (a, b) ∈ target <;> simp [hab]
    rw [hintegrand, lintegral_indicator hfiber]
    simp [Measure.restrict_apply]
  · exact (hdensity.comp measurable_fst).indicator htarget

/-- The unnormalized observed marginal after joint selection. -/
def selectedBase (μ : Measure α) (κ : Kernel α β)
    (event : Set (α × β)) : Measure α :=
  μ.withDensity (selectionMass κ event)

/-- The observed marginal of the globally normalized selected joint law. -/
def normalizedSelectedBase (μ : Measure α) (κ : Kernel α β)
    (event : Set (α × β)) : Measure α :=
  ((μ ⊗ₘ κ) event)⁻¹ • selectedBase μ κ event

/--
An a.e. property under the base marginal of a normalized selected experiment
holds at almost every original base whose selected fibre has positive mass.

This is the valid direction for transporting an action-selected conditional
law back to the raw base population.  It does not assert anything at a base
with a zero selected fibre, where conditional values are not identified by
the selected experiment.
-/
theorem ae_normalizedSelectedBase_to_ae_positiveFibres
    {μ : Measure α} [IsProbabilityMeasure μ]
    {κ : Kernel α β} [IsMarkovKernel κ]
    {event : Set (α × β)} (hevent : MeasurableSet event)
    {P : α → Prop}
    (hP : ∀ᵐ a ∂normalizedSelectedBase μ κ event, P a) :
    ∀ᵐ a ∂μ, selectionMass κ event a ≠ 0 → P a := by
  have hnormalizer_ne_zero : ((μ ⊗ₘ κ) event)⁻¹ ≠ 0 := by
    apply ENNReal.inv_ne_zero.mpr
    exact measure_ne_top _ _
  rw [normalizedSelectedBase,
    Measure.ae_ennreal_smul_measure_iff hnormalizer_ne_zero] at hP
  exact (ae_withDensity_iff (selectionMass_measurable hevent)).mp hP

/-- The unnormalized selected joint law factors through its selected base and fibre kernel. -/
theorem selectedBase_compProd_selectedNormalizedKernel
    {μ : Measure α} [SFinite μ] {κ : Kernel α β} [IsMarkovKernel κ]
    {event : Set (α × β)} (hevent : MeasurableSet event)
    (hpositive : ∀ a, selectionMass κ event a ≠ 0) :
    selectedBase μ κ event ⊗ₘ selectedNormalizedKernel κ event =
      (μ ⊗ₘ κ).restrict event := by
  have hselected :
      IsSFiniteKernel (κ.withDensity (selectedNormalizedDensity κ event)) := by
    simpa only [selectedNormalizedKernel] using
      (selectedNormalizedKernel_isSFinite (κ := κ) hpositive)
  letI : IsSFiniteKernel (κ.withDensity (selectedNormalizedDensity κ event)) := hselected
  change (μ.withDensity (selectionMass κ event)) ⊗ₘ
      (κ.withDensity (selectedNormalizedDensity κ event)) =
    (μ ⊗ₘ κ).restrict event
  rw [Measure.compProd_withDensity
    (selectedNormalizedDensity_measurable hevent),
    compProd_withDensity_left (selectionMass_measurable hevent)]
  have hmasslift : Measurable (fun pair : α × β => selectionMass κ event pair.1) :=
    (selectionMass_measurable hevent).comp measurable_fst
  have hselectedlift : Measurable (fun pair : α × β =>
      selectedNormalizedDensity κ event pair.1 pair.2) := by
    simpa only [Function.uncurry] using selectedNormalizedDensity_measurable
      (κ := κ) hevent
  rw [← withDensity_mul (μ ⊗ₘ κ) hmasslift hselectedlift]
  have hcancel :
      (fun pair : α × β => selectionMass κ event pair.1 *
        selectedNormalizedDensity κ event pair.1 pair.2) =
        event.indicator 1 := by
    funext pair
    rcases pair with ⟨a, b⟩
    change selectionMass κ event a *
        (selectedIndicator event a b * (selectionMass κ event a)⁻¹) =
      event.indicator 1 (a, b)
    rw [show selectedIndicator event a b = event.indicator 1 (a, b) by rfl]
    calc
      selectionMass κ event a *
          (event.indicator 1 (a, b) * (selectionMass κ event a)⁻¹) =
          event.indicator 1 (a, b) *
            (selectionMass κ event a * (selectionMass κ event a)⁻¹) := by
              ac_rfl
      _ = event.indicator 1 (a, b) * 1 := by
        rw [ENNReal.mul_inv_cancel (hpositive a)
          (measure_ne_top (κ a) (selectedFiber event a))]
      _ = event.indicator 1 (a, b) := mul_one _
  have hcancel' :
      (fun pair : α × β => selectionMass κ event pair.1) *
        (fun pair : α × β => selectedNormalizedDensity κ event pair.1 pair.2) =
        event.indicator 1 := by
    simpa only [Pi.mul_apply] using hcancel
  rw [hcancel', withDensity_indicator_one hevent]

/--
The normalized restriction of a raw joint law factors through its selected
observed marginal and the normalized restriction of each positive raw fibre.
-/
theorem normalizedRestriction_compProd_selectedNormalizedKernel
    {μ : Measure α} [SFinite μ] {κ : Kernel α β} [IsMarkovKernel κ]
    {event : Set (α × β)} (hevent : MeasurableSet event)
    (hpositive : ∀ a, selectionMass κ event a ≠ 0) :
    lg21NormalizedRestriction (μ ⊗ₘ κ) event =
      normalizedSelectedBase μ κ event ⊗ₘ selectedNormalizedKernel κ event := by
  letI : IsSFiniteKernel (selectedNormalizedKernel κ event) :=
    selectedNormalizedKernel_isSFinite hpositive
  letI : SFinite (selectedBase μ κ event) := by
    unfold selectedBase
    infer_instance
  rw [lg21NormalizedRestriction, normalizedSelectedBase,
    Measure.compProd_smul_left,
    selectedBase_compProd_selectedNormalizedKernel hevent hpositive]

end

end LG21TestOptionalPolicies
