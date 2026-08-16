import LG21TestOptionalPolicies.SelectedConditionalRestriction
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Regular conditional distributions after measurable selection

This source-neutral module identifies the regular conditional distribution of
the latent coordinate after restricting a joint observed/latent law to a
measurable selection event.  It uses the factorization established in
`SelectedConditionalRestriction`: the selected conditional law is the
normalized restriction of each raw latent fibre.

The theorem deliberately has two positivity hypotheses.  Fibrewise positivity
makes the displayed kernel a Markov kernel at every observed value; positive
total selected mass makes the globally normalized restriction a probability
law.  A paper-level use must prove both on its actual domain, or separately
handle the almost-everywhere and zero-fibre cases.  Nothing here asserts a
Gaussian formula, a PBO, an action rule, or an equilibrium property.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/--
After a measurable joint selection event, the conditional latent law given
the observed coordinate is almost everywhere the normalized restriction of
the raw fibre kernel.  The almost-everywhere measure is the *selected*
observed marginal, rather than the unselected base marginal.
-/
theorem condDistrib_snd_given_fst_normalizedRestriction_ae
    [StandardBorelSpace β] [Nonempty β]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {κ : Kernel α β} [IsMarkovKernel κ]
    {event : Set (α × β)} (hevent : MeasurableSet event)
    (hpositive : ∀ a, selectionMass κ event a ≠ 0)
    (hselection : (μ ⊗ₘ κ) event ≠ 0) :
    letI : IsProbabilityMeasure
        (lg21NormalizedRestriction (μ ⊗ₘ κ) event) :=
      lg21NormalizedRestriction_isProbability (μ ⊗ₘ κ) event hselection
        (measure_ne_top _ _)
    letI : IsFiniteMeasure
        (lg21NormalizedRestriction (μ ⊗ₘ κ) event) := ⟨by simp⟩
    condDistrib Prod.snd Prod.fst
        (lg21NormalizedRestriction (μ ⊗ₘ κ) event) =ᵐ[
          (lg21NormalizedRestriction (μ ⊗ₘ κ) event).map Prod.fst]
      selectedNormalizedKernel κ event := by
  let ν : Measure (α × β) := lg21NormalizedRestriction (μ ⊗ₘ κ) event
  letI : IsProbabilityMeasure ν :=
    lg21NormalizedRestriction_isProbability (μ ⊗ₘ κ) event hselection
      (measure_ne_top _ _)
  letI : IsFiniteMeasure ν := ⟨by simp⟩
  letI : IsMarkovKernel (selectedNormalizedKernel κ event) :=
    selectedNormalizedKernel_isMarkov hevent hpositive
  letI : SFinite (selectedBase μ κ event) := by
    unfold selectedBase
    infer_instance
  letI : SFinite (normalizedSelectedBase μ κ event) := by
    unfold normalizedSelectedBase
    infer_instance
  change condDistrib Prod.snd Prod.fst ν =ᵐ[ν.map Prod.fst]
    selectedNormalizedKernel κ event
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (μ := ν) (X := Prod.fst) (Y := Prod.snd)
    measurable_fst measurable_snd
  have hfactor :
      ν = normalizedSelectedBase μ κ event ⊗ₘ
        selectedNormalizedKernel κ event := by
    exact normalizedRestriction_compProd_selectedNormalizedKernel
      (μ := μ) (κ := κ) hevent hpositive
  have hfirst : ν.map Prod.fst = normalizedSelectedBase μ κ event := by
    calc
      ν.map Prod.fst =
          (normalizedSelectedBase μ κ event ⊗ₘ
            selectedNormalizedKernel κ event).map Prod.fst := by
        rw [hfactor]
      _ = (normalizedSelectedBase μ κ event ⊗ₘ
            selectedNormalizedKernel κ event).fst := rfl
      _ = normalizedSelectedBase μ κ event :=
        Measure.fst_compProd _ _
  calc
    ν.map (fun pair => (Prod.fst pair, Prod.snd pair)) = ν := by
      change ν.map id = ν
      exact Measure.map_id
    _ = normalizedSelectedBase μ κ event ⊗ₘ
        selectedNormalizedKernel κ event := hfactor
    _ = ν.map Prod.fst ⊗ₘ selectedNormalizedKernel κ event := by
      rw [hfirst]

end

end LG21TestOptionalPolicies
