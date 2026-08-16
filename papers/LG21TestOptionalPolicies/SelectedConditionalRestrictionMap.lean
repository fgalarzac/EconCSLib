import LG21TestOptionalPolicies.SelectedConditionalRestriction

/-!
# Mapping a composition product after a joint selection

This source-neutral module records the measure transport used when an
observed/latent joint law is restricted to a measurable event and then a
latent coordinate is mapped out.  It deliberately contains no candidate,
action, PBO, Gaussian, or equilibrium definitions.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set

variable {α β γ : Type*}
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

/-- Mapping the second coordinate of a composition product can equivalently
be done by mapping each fibre kernel first. -/
theorem map_compProd_eq_compProd_map
    {μ : Measure α} [SFinite μ]
    {κ : Kernel α β} [IsSFiniteKernel κ]
    {f : β -> γ} (hf : Measurable f) :
    (μ ⊗ₘ κ).map (Prod.map id f) = μ ⊗ₘ κ.map f := by
  exact (Measure.compProd_map hf).symm

/-- Restrict a joint composition-product law to a measurable event, then map
the latent coordinate.  This is equivalently the composition product of the
event-restricted fibre kernel mapped through that coordinate. -/
theorem compProd_selectedRestrictionKernel_map
    {μ : Measure α} [SFinite μ]
    {κ : Kernel α β} [IsFiniteKernel κ]
    {event : Set (α × β)} (hevent : MeasurableSet event)
    {f : β -> γ} (hf : Measurable f) :
    μ ⊗ₘ (selectedRestrictionKernel κ event).map f =
      ((μ ⊗ₘ κ).restrict event).map (Prod.map id f) := by
  letI : IsFiniteKernel (selectedRestrictionKernel κ event) :=
    selectedRestrictionKernel_isFinite event
  rw [Measure.compProd_map hf, compProd_selectedRestrictionKernel hevent]

/-- The score/skill specialization of
`compProd_selectedRestrictionKernel_map`.  It transports a selected joint
score/skill law to its base/skill marginal. -/
theorem compProd_selectedRestrictionKernel_map_snd
    {μ : Measure α} [SFinite μ]
    {κ : Kernel α (β × γ)} [IsFiniteKernel κ]
    {event : Set (α × (β × γ))} (hevent : MeasurableSet event) :
    μ ⊗ₘ (selectedRestrictionKernel κ event).map Prod.snd =
      ((μ ⊗ₘ κ).restrict event).map (Prod.map id Prod.snd) := by
  exact compProd_selectedRestrictionKernel_map hevent measurable_snd

end

end LG21TestOptionalPolicies
