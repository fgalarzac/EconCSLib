import LG21TestOptionalPolicies.SelectedConditionalRCD

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The observed fibres that have positive mass after a joint selection event. -/
def selectedPositiveFibres {κ : Kernel α β} (event : Set (α × β)) : Set α :=
  Function.support (selectionMass κ event)

theorem selectedPositiveFibres_measurable {κ : Kernel α β} [IsSFiniteKernel κ]
    {event : Set (α × β)} (hevent : MeasurableSet event) :
    MeasurableSet (selectedPositiveFibres (κ := κ) event) := by
  change MeasurableSet (Function.support (selectionMass κ event))
  simpa only [Function.support, Set.mem_preimage, Set.mem_compl_iff,
    Set.mem_singleton_iff] using
    (selectionMass_measurable (κ := κ) hevent)
      ((measurableSet_singleton (0 : ℝ≥0∞)).compl)

/--
The selected conditional kernel where a fibre has positive selected mass,
patched by the raw kernel on zero-mass fibres.

The patch only makes this a total Markov kernel.  The theorems below use it
only under the selected observed marginal, where it agrees almost everywhere
with the literal normalized selected restriction.
-/
noncomputable def selectedNormalizedKernelAtPositiveFibres
    {κ : Kernel α β} [IsMarkovKernel κ]
    {event : Set (α × β)} (hevent : MeasurableSet event) : Kernel α β := by
  classical
  exact Kernel.piecewise
    (selectedPositiveFibres_measurable (κ := κ) hevent)
    (selectedNormalizedKernel κ event) κ

theorem selectedNormalizedKernelAtPositiveFibres_apply_pos
    {κ : Kernel α β} [IsMarkovKernel κ]
    {event : Set (α × β)} (hevent : MeasurableSet event) (a : α)
    (ha : selectionMass κ event a ≠ 0) :
    selectedNormalizedKernelAtPositiveFibres (κ := κ) hevent a =
      selectedNormalizedKernel κ event a := by
  classical
  rw [selectedNormalizedKernelAtPositiveFibres, Kernel.piecewise_apply]
  simp [selectedPositiveFibres, ha]

theorem selectedNormalizedKernelAtPositiveFibres_isMarkov
    {κ : Kernel α β} [IsMarkovKernel κ]
    {event : Set (α × β)} (hevent : MeasurableSet event) :
    IsMarkovKernel (selectedNormalizedKernelAtPositiveFibres (κ := κ) hevent) := by
  classical
  constructor
  intro a
  rw [selectedNormalizedKernelAtPositiveFibres, Kernel.piecewise_apply]
  by_cases ha : selectionMass κ event a ≠ 0
  · rw [if_pos (by simpa [selectedPositiveFibres] using ha)]
    rw [selectedNormalizedKernel_apply hevent]
    exact lg21NormalizedRestriction_isProbability (κ a) _ ha
      (measure_ne_top _ _)
  · rw [if_neg (by simpa [selectedPositiveFibres] using ha)]
    infer_instance

theorem selectedBase_compProd_selectedNormalizedKernelAtPositiveFibres
    {μ : Measure α} [SFinite μ] {κ : Kernel α β} [IsMarkovKernel κ]
    {event : Set (α × β)} (hevent : MeasurableSet event) :
    selectedBase μ κ event ⊗ₘ
        selectedNormalizedKernelAtPositiveFibres (κ := κ) hevent =
      (μ ⊗ₘ κ).restrict event := by
  classical
  let patch := selectedNormalizedKernelAtPositiveFibres (κ := κ) hevent
  letI : IsMarkovKernel patch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov (κ := κ) hevent
  letI : SFinite (selectedBase μ κ event) := by
    unfold selectedBase
    infer_instance
  ext target htarget
  rw [Measure.compProd_apply htarget]
  change ∫⁻ a, patch a (Prod.mk a ⁻¹' target) ∂
      μ.withDensity (selectionMass κ event) =
    ((μ ⊗ₘ κ).restrict event) target
  rw [Measure.restrict_apply htarget]
  rw [Measure.compProd_apply (htarget.inter hevent)]
  rw [lintegral_withDensity_eq_lintegral_mul μ
    (selectionMass_measurable hevent)
    (Kernel.measurable_kernel_prodMk_left htarget)]
  apply lintegral_congr
  intro a
  change selectionMass κ event a * patch a (Prod.mk a ⁻¹' target) =
    κ a (Prod.mk a ⁻¹' (target ∩ event))
  by_cases ha : selectionMass κ event a = 0
  · rw [ha, zero_mul]
    symm
    apply measure_mono_null
    · intro b hb
      exact hb.2
    · change κ a (selectedFiber event a) = 0
      exact ha
  · rw [show patch a = selectedNormalizedKernel κ event a by
      exact selectedNormalizedKernelAtPositiveFibres_apply_pos hevent a ha]
    rw [selectedNormalizedKernel_apply hevent]
    rw [lg21NormalizedRestriction_apply (κ a)
      (event := selectedFiber event a) (target := Prod.mk a ⁻¹' target)
      ((measurable_const.prodMk measurable_id) htarget)]
    have hinter : (Prod.mk a ⁻¹' target) ∩ selectedFiber event a =
        Prod.mk a ⁻¹' (target ∩ event) := by
      ext b
      simp [selectedFiber]
    rw [hinter]
    calc
      selectionMass κ event a *
          ((selectionMass κ event a)⁻¹ *
            κ a (Prod.mk a ⁻¹' (target ∩ event))) =
          (selectionMass κ event a * (selectionMass κ event a)⁻¹) *
            κ a (Prod.mk a ⁻¹' (target ∩ event)) := by
              ac_rfl
      _ = κ a (Prod.mk a ⁻¹' (target ∩ event)) := by
        rw [ENNReal.mul_inv_cancel ha (measure_ne_top _ _), one_mul]

theorem normalizedRestriction_compProd_selectedNormalizedKernelAtPositiveFibres
    {μ : Measure α} [SFinite μ] {κ : Kernel α β} [IsMarkovKernel κ]
    {event : Set (α × β)} (hevent : MeasurableSet event) :
    lg21NormalizedRestriction (μ ⊗ₘ κ) event =
      normalizedSelectedBase μ κ event ⊗ₘ
        selectedNormalizedKernelAtPositiveFibres (κ := κ) hevent := by
  classical
  let patch := selectedNormalizedKernelAtPositiveFibres (κ := κ) hevent
  letI : IsMarkovKernel patch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov (κ := κ) hevent
  letI : SFinite (selectedBase μ κ event) := by
    unfold selectedBase
    infer_instance
  rw [lg21NormalizedRestriction, normalizedSelectedBase,
    Measure.compProd_smul_left,
    selectedBase_compProd_selectedNormalizedKernelAtPositiveFibres
      (μ := μ) (κ := κ) hevent]

/-- The first marginal of a normalized jointly selected law is its normalized
selected observed marginal, without a positivity requirement on every fibre. -/
theorem normalizedRestriction_map_fst_eq_normalizedSelectedBase
    {μ : Measure α} [SFinite μ] {κ : Kernel α β} [IsMarkovKernel κ]
    {event : Set (α × β)} (hevent : MeasurableSet event) :
    (lg21NormalizedRestriction (μ ⊗ₘ κ) event).map Prod.fst =
      normalizedSelectedBase μ κ event := by
  classical
  let patch := selectedNormalizedKernelAtPositiveFibres (κ := κ) hevent
  letI : IsMarkovKernel patch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov (κ := κ) hevent
  letI : SFinite (selectedBase μ κ event) := by
    unfold selectedBase
    infer_instance
  letI : SFinite (normalizedSelectedBase μ κ event) := by
    unfold normalizedSelectedBase
    infer_instance
  rw [normalizedRestriction_compProd_selectedNormalizedKernelAtPositiveFibres
    (μ := μ) (κ := κ) hevent]
  exact Measure.fst_compProd _ _

theorem selectedNormalizedKernelAtPositiveFibres_ae_eq
    {μ : Measure α} [IsProbabilityMeasure μ]
    {κ : Kernel α β} [IsMarkovKernel κ]
    {event : Set (α × β)} (hevent : MeasurableSet event) :
    selectedNormalizedKernelAtPositiveFibres (κ := κ) hevent =ᵐ[
      normalizedSelectedBase μ κ event]
      selectedNormalizedKernel κ event := by
  classical
  have hnormalizer_ne_zero : ((μ ⊗ₘ κ) event)⁻¹ ≠ 0 := by
    exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
  have hpositive : ∀ᵐ a ∂normalizedSelectedBase μ κ event,
      selectionMass κ event a ≠ 0 := by
    change ∀ᵐ a ∂(((μ ⊗ₘ κ) event)⁻¹ • selectedBase μ κ event),
      selectionMass κ event a ≠ 0
    rw [Measure.ae_ennreal_smul_measure_iff hnormalizer_ne_zero]
    change ∀ᵐ a ∂μ.withDensity (selectionMass κ event),
      selectionMass κ event a ≠ 0
    rw [ae_withDensity_iff (selectionMass_measurable hevent)]
    filter_upwards with a ha
    exact ha
  filter_upwards [hpositive] with a ha
  exact selectedNormalizedKernelAtPositiveFibres_apply_pos hevent a ha

/-- The normalized selected observed marginal is supported on positive raw
selection fibres. -/
theorem ae_normalizedSelectedBase_positiveFibres
    {μ : Measure α} [IsProbabilityMeasure μ]
    {κ : Kernel α β} [IsMarkovKernel κ]
    {event : Set (α × β)} (hevent : MeasurableSet event) :
    ∀ᵐ a ∂normalizedSelectedBase μ κ event,
      selectionMass κ event a ≠ 0 := by
  have hnormalizer_ne_zero : ((μ ⊗ₘ κ) event)⁻¹ ≠ 0 := by
    exact ENNReal.inv_ne_zero.mpr (measure_ne_top _ _)
  change ∀ᵐ a ∂(((μ ⊗ₘ κ) event)⁻¹ • selectedBase μ κ event),
    selectionMass κ event a ≠ 0
  rw [Measure.ae_ennreal_smul_measure_iff hnormalizer_ne_zero]
  change ∀ᵐ a ∂μ.withDensity (selectionMass κ event),
    selectionMass κ event a ≠ 0
  rw [ae_withDensity_iff (selectionMass_measurable hevent)]
  filter_upwards with a ha
  exact ha

/--
After any measurable joint selection event of positive total mass, the latent
regular conditional distribution given the observed coordinate is almost
everywhere the literal normalized selected fibre.  Zero-mass raw fibres are
not assigned a selected law: the equality is only under the selected
observed marginal.
-/
theorem condDistrib_snd_given_fst_normalizedRestriction_ae_of_positiveFibres
    [StandardBorelSpace β] [Nonempty β]
    {μ : Measure α} [IsProbabilityMeasure μ]
    {κ : Kernel α β} [IsMarkovKernel κ]
    {event : Set (α × β)} (hevent : MeasurableSet event)
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
  classical
  let ν : Measure (α × β) := lg21NormalizedRestriction (μ ⊗ₘ κ) event
  letI : IsProbabilityMeasure ν :=
    lg21NormalizedRestriction_isProbability (μ ⊗ₘ κ) event hselection
      (measure_ne_top _ _)
  letI : IsFiniteMeasure ν := ⟨by simp⟩
  let patch := selectedNormalizedKernelAtPositiveFibres (κ := κ) hevent
  letI : IsMarkovKernel patch :=
    selectedNormalizedKernelAtPositiveFibres_isMarkov (κ := κ) hevent
  letI : SFinite (selectedBase μ κ event) := by
    unfold selectedBase
    infer_instance
  letI : SFinite (normalizedSelectedBase μ κ event) := by
    unfold normalizedSelectedBase
    infer_instance
  change condDistrib Prod.snd Prod.fst ν =ᵐ[ν.map Prod.fst]
    selectedNormalizedKernel κ event
  have hfactor :
      ν = normalizedSelectedBase μ κ event ⊗ₘ patch := by
    exact
      normalizedRestriction_compProd_selectedNormalizedKernelAtPositiveFibres
        (μ := μ) (κ := κ) hevent
  have hfirst : ν.map Prod.fst = normalizedSelectedBase μ κ event := by
    calc
      ν.map Prod.fst =
          (normalizedSelectedBase μ κ event ⊗ₘ patch).map Prod.fst := by
        rw [hfactor]
      _ = (normalizedSelectedBase μ κ event ⊗ₘ patch).fst := rfl
      _ = normalizedSelectedBase μ κ event :=
        Measure.fst_compProd _ _
  have hrcd : condDistrib Prod.snd Prod.fst ν =ᵐ[ν.map Prod.fst] patch := by
    apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
      (μ := ν) (X := Prod.fst) (Y := Prod.snd)
      measurable_fst measurable_snd
    calc
      ν.map (fun pair => (Prod.fst pair, Prod.snd pair)) = ν := by
        change ν.map id = ν
        exact Measure.map_id
      _ = normalizedSelectedBase μ κ event ⊗ₘ patch := hfactor
      _ = ν.map Prod.fst ⊗ₘ patch := by
        rw [hfirst]
  have hpatch : patch =ᵐ[ν.map Prod.fst] selectedNormalizedKernel κ event := by
    rw [hfirst]
    exact selectedNormalizedKernelAtPositiveFibres_ae_eq
      (μ := μ) (κ := κ) hevent
  exact hrcd.trans hpatch

end

end LG21TestOptionalPolicies
