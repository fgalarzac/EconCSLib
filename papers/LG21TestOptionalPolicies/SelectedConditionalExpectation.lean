import LG21TestOptionalPolicies.SelectedConditionalRCD

/-!
# Conditional expectation after measurable selection

This source-neutral module turns the selected regular-conditional-distribution
factorization into the corresponding conditional-expectation identity.  The
ambient law is the globally normalized restriction of `μ ⊗ₘ κ` to the
measurable joint event.  Consequently, the equality is almost everywhere for
that selected law; the kernel replacement itself is first established under
its selected observed marginal and then pulled back along `Prod.fst`.

The theorem needs an explicit integrability hypothesis for the latent
coordinate.  Selection may change integrability, so it is not inferred from
the raw law here.  Nothing in this file asserts a source model, a Gaussian
formula, a PBO, an action rule, or an equilibrium property.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/--
Under a positive measurable joint selection event, the mean of the selected
regular conditional distribution is the mean of the normalized selected
fibre kernel almost everywhere under the selected observed marginal.

This is the observed-space form of the result.  The next theorem pulls it
back along `Prod.fst` to identify a conditional expectation on the selected
joint law.
-/
theorem selected_condDistrib_snd_mean_given_fst_ae
    [StandardBorelSpace β] [Nonempty β]
    [NormedAddCommGroup β] [NormedSpace ℝ β] [CompleteSpace β]
    [BorelSpace β] [SecondCountableTopology β]
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
    (fun observed => ∫ latent, latent ∂condDistrib Prod.snd Prod.fst
      (lg21NormalizedRestriction (μ ⊗ₘ κ) event) observed) =ᵐ[
        (lg21NormalizedRestriction (μ ⊗ₘ κ) event).map Prod.fst]
      fun observed => ∫ latent, latent ∂selectedNormalizedKernel κ event observed := by
  let ν : Measure (α × β) := lg21NormalizedRestriction (μ ⊗ₘ κ) event
  letI : IsProbabilityMeasure ν :=
    lg21NormalizedRestriction_isProbability (μ ⊗ₘ κ) event hselection
      (measure_ne_top _ _)
  letI : IsFiniteMeasure ν := ⟨by simp⟩
  change (fun observed => ∫ latent, latent ∂condDistrib Prod.snd Prod.fst ν observed) =ᵐ[
      ν.map Prod.fst]
    fun observed => ∫ latent, latent ∂selectedNormalizedKernel κ event observed
  filter_upwards [condDistrib_snd_given_fst_normalizedRestriction_ae
    (μ := μ) (κ := κ) hevent hpositive hselection] with observed hKernel
  rw [hKernel]

/--
Under a positive measurable joint selection event, the conditional
expectation of the latent coordinate given the observed coordinate is the
mean of the normalized selected fibre kernel, almost everywhere under the
normalized selected joint law.

The regular conditional distribution equality used inside the proof is almost
everywhere under the selected observed marginal
`(lg21NormalizedRestriction (μ ⊗ₘ κ) event).map Prod.fst`; composing it with
`Prod.fst` gives the displayed conditional-expectation equality under the
selected joint law.
-/
theorem selected_condExp_snd_given_fst_ae
    [StandardBorelSpace β] [Nonempty β]
    [NormedAddCommGroup β] [NormedSpace ℝ β] [CompleteSpace β]
    [BorelSpace β] [SecondCountableTopology β]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {κ : Kernel α β} [IsMarkovKernel κ]
    {event : Set (α × β)} (hevent : MeasurableSet event)
    (hpositive : ∀ a, selectionMass κ event a ≠ 0)
    (hselection : (μ ⊗ₘ κ) event ≠ 0)
    (hintegrable : Integrable Prod.snd
      (lg21NormalizedRestriction (μ ⊗ₘ κ) event)) :
    letI : IsProbabilityMeasure
        (lg21NormalizedRestriction (μ ⊗ₘ κ) event) :=
      lg21NormalizedRestriction_isProbability (μ ⊗ₘ κ) event hselection
        (measure_ne_top _ _)
    letI : IsFiniteMeasure
        (lg21NormalizedRestriction (μ ⊗ₘ κ) event) := ⟨by simp⟩
    (lg21NormalizedRestriction (μ ⊗ₘ κ) event)[Prod.snd |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[
        lg21NormalizedRestriction (μ ⊗ₘ κ) event]
      fun pair => ∫ latent, latent ∂selectedNormalizedKernel κ event pair.1 := by
  let ν : Measure (α × β) := lg21NormalizedRestriction (μ ⊗ₘ κ) event
  letI : IsProbabilityMeasure ν :=
    lg21NormalizedRestriction_isProbability (μ ⊗ₘ κ) event hselection
      (measure_ne_top _ _)
  letI : IsFiniteMeasure ν := ⟨by simp⟩
  change ν[Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[ν]
    fun pair => ∫ latent, latent ∂selectedNormalizedKernel κ event pair.1
  have hcondExp :
      ν[Prod.snd | MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[ν]
        fun pair => ∫ latent, latent ∂condDistrib Prod.snd Prod.fst ν pair.1 :=
    condExp_ae_eq_integral_condDistrib' measurable_fst hintegrable
  have hcondDistrib_pullback :
      ∀ᵐ pair ∂ν,
        (∫ latent, latent ∂condDistrib Prod.snd Prod.fst ν pair.1) =
          ∫ latent, latent ∂selectedNormalizedKernel κ event pair.1 := by
    exact ae_of_ae_map measurable_fst.aemeasurable
      (selected_condDistrib_snd_mean_given_fst_ae
        (μ := μ) (κ := κ) hevent hpositive hselection)
  filter_upwards [hcondExp, hcondDistrib_pullback] with pair hExp hKernel
  rw [hExp, hKernel]

end

end LG21TestOptionalPolicies
