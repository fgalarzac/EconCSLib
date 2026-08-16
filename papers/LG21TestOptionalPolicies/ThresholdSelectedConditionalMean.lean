import LG21TestOptionalPolicies.SelectedConditionalExpectation
import LG21TestOptionalPolicies.ReportRequiredSelectionAwarePBOBridge

/-!
# Conditional means after upper-tail selection

This module specializes the source-neutral selected-kernel infrastructure to
the event that the latent real coordinate is strictly above a cutoff.  The
observed coordinate remains an arbitrary measurable type, so an eventual LG21
application can use the full observed `(base, score)` history rather than
silently dropping base features.

The results make all four relevant boundaries explicit:

* the upper-tail event is measurable;
* every observed fibre has positive selected mass, so the displayed normalized
  fibre kernel is a genuine probability kernel everywhere;
* the selected joint event has positive total mass;
* the conditional-mean and conditional-expectation conclusions are only
  almost everywhere under the selected observation/joint law, and selected-law
  integrability is an explicit premise.

Nothing here identifies the conditional expectation with a school PBO,
derives a strategic threshold action, or asserts an equilibrium property.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

variable {Observed : Type*}

/-- The joint event selecting exactly latent values strictly above `cutoff`. -/
def lg21UpperTailSelectionEvent (cutoff : ℝ) : Set (Observed × ℝ) :=
  Set.univ ×ˢ Set.Ioi cutoff

/-- The upper-tail joint selection event is measurable. -/
theorem lg21UpperTailSelectionEvent_measurable [MeasurableSpace Observed] (cutoff : ℝ) :
    MeasurableSet (lg21UpperTailSelectionEvent (Observed := Observed) cutoff) :=
  MeasurableSet.univ.prod measurableSet_Ioi

/-- Every observed fibre of an upper-tail event is the same latent upper tail. -/
theorem lg21UpperTailSelectionEvent_selectedFiber
    (cutoff : ℝ) (observed : Observed) :
    selectedFiber (lg21UpperTailSelectionEvent (Observed := Observed) cutoff) observed =
      Set.Ioi cutoff := by
  ext latent
  simp [lg21UpperTailSelectionEvent, selectedFiber]

/-- The generic selected-fibre mass is exactly the raw posterior upper-tail mass. -/
theorem lg21UpperTailSelectionEvent_selectionMass
    [MeasurableSpace Observed] {κ : Kernel Observed ℝ} (cutoff : ℝ) (observed : Observed) :
    selectionMass κ (lg21UpperTailSelectionEvent (Observed := Observed) cutoff) observed =
      κ observed (Set.Ioi cutoff) := by
  rw [selectionMass, lg21UpperTailSelectionEvent_selectedFiber]

/--
For upper-tail selection, the generic selected kernel is exactly the normalized
restriction of the raw latent fibre to that upper tail.
-/
theorem lg21UpperTailSelectionEvent_selectedNormalizedKernel_apply
    [MeasurableSpace Observed] {κ : Kernel Observed ℝ} [IsSFiniteKernel κ]
    (cutoff : ℝ) (observed : Observed) :
    selectedNormalizedKernel κ
        (lg21UpperTailSelectionEvent (Observed := Observed) cutoff) observed =
      lg21NormalizedRestriction (κ observed) (Set.Ioi cutoff) := by
  rw [selectedNormalizedKernel_apply
    (lg21UpperTailSelectionEvent_measurable (Observed := Observed) cutoff)]
  rw [lg21UpperTailSelectionEvent_selectedFiber]

/--
The mean of every integrable selected fibre lies strictly above the selection
cutoff.  The theorem is stated almost everywhere under the selected observed
marginal: it does not choose values of a conditional law on null observation
fibres.
-/
theorem lg21_upperTail_selectedKernel_mean_gt_cutoff_ae
    [MeasurableSpace Observed] {μ : Measure Observed} [IsProbabilityMeasure μ]
    {κ : Kernel Observed ℝ} [IsMarkovKernel κ]
    (cutoff : ℝ)
    (hfibrePositive : ∀ observed, κ observed (Set.Ioi cutoff) ≠ 0)
    (hintegrable :
      ∀ᵐ observed ∂
        (lg21NormalizedRestriction (μ ⊗ₘ κ)
          (lg21UpperTailSelectionEvent (Observed := Observed) cutoff)).map Prod.fst,
        Integrable (fun latent : ℝ => latent)
          (selectedNormalizedKernel κ
            (lg21UpperTailSelectionEvent (Observed := Observed) cutoff) observed)) :
    ∀ᵐ observed ∂
      (lg21NormalizedRestriction (μ ⊗ₘ κ)
        (lg21UpperTailSelectionEvent (Observed := Observed) cutoff)).map Prod.fst,
      cutoff < ∫ latent,
        latent ∂selectedNormalizedKernel κ
          (lg21UpperTailSelectionEvent (Observed := Observed) cutoff) observed := by
  filter_upwards [hintegrable] with observed hInt
  have hInt' : Integrable (fun latent : ℝ => latent)
      (lg21NormalizedRestriction (κ observed) (Set.Ioi cutoff)) := by
    rw [← lg21UpperTailSelectionEvent_selectedNormalizedKernel_apply]
    exact hInt
  rw [lg21UpperTailSelectionEvent_selectedNormalizedKernel_apply]
  simpa [lg21ReportRequiredUpperTailSelectedPosterior] using
    (lg21_report_required_upper_tail_selected_posterior_mean_gt_cutoff
      κ cutoff observed
      (pos_iff_ne_zero.mpr (hfibrePositive observed))
      (measure_ne_top (κ observed) (Set.Ioi cutoff)) hInt')

/--
The regular conditional latent mean under the globally normalized upper-tail
selection is strictly above the cutoff almost everywhere under the selected
observed marginal.  `hselection` supplies the actual positive selected law;
the per-fibre hypothesis is retained because it is what makes the selected
kernel canonical at every observed value.
-/
theorem lg21_upperTail_selected_condDistrib_mean_gt_cutoff_ae
    [MeasurableSpace Observed] {μ : Measure Observed} [IsProbabilityMeasure μ]
    {κ : Kernel Observed ℝ} [IsMarkovKernel κ]
    (cutoff : ℝ)
    (hfibrePositive : ∀ observed, κ observed (Set.Ioi cutoff) ≠ 0)
    (hselection :
      (μ ⊗ₘ κ) (lg21UpperTailSelectionEvent (Observed := Observed) cutoff) ≠ 0)
    (hintegrable :
      ∀ᵐ observed ∂
        (lg21NormalizedRestriction (μ ⊗ₘ κ)
          (lg21UpperTailSelectionEvent (Observed := Observed) cutoff)).map Prod.fst,
        Integrable (fun latent : ℝ => latent)
          (selectedNormalizedKernel κ
            (lg21UpperTailSelectionEvent (Observed := Observed) cutoff) observed)) :
    letI : IsProbabilityMeasure
        (lg21NormalizedRestriction (μ ⊗ₘ κ)
          (lg21UpperTailSelectionEvent (Observed := Observed) cutoff)) :=
      lg21NormalizedRestriction_isProbability (μ ⊗ₘ κ)
        (lg21UpperTailSelectionEvent (Observed := Observed) cutoff) hselection
        (measure_ne_top _ _)
    letI : IsFiniteMeasure
        (lg21NormalizedRestriction (μ ⊗ₘ κ)
          (lg21UpperTailSelectionEvent (Observed := Observed) cutoff)) := ⟨by simp⟩
    ∀ᵐ observed ∂
      (lg21NormalizedRestriction (μ ⊗ₘ κ)
        (lg21UpperTailSelectionEvent (Observed := Observed) cutoff)).map Prod.fst,
      cutoff < ∫ latent,
        latent ∂condDistrib Prod.snd Prod.fst
          (lg21NormalizedRestriction (μ ⊗ₘ κ)
            (lg21UpperTailSelectionEvent (Observed := Observed) cutoff)) observed := by
  let event : Set (Observed × ℝ) :=
    lg21UpperTailSelectionEvent (Observed := Observed) cutoff
  let selectedLaw : Measure (Observed × ℝ) :=
    lg21NormalizedRestriction (μ ⊗ₘ κ) event
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability (μ ⊗ₘ κ) event hselection
      (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  have hpositive : ∀ observed, selectionMass κ event observed ≠ 0 := by
    intro observed
    change selectionMass κ
      (lg21UpperTailSelectionEvent (Observed := Observed) cutoff) observed ≠ 0
    rw [lg21UpperTailSelectionEvent_selectionMass]
    exact hfibrePositive observed
  have hkernelMean : ∀ᵐ observed ∂selectedLaw.map Prod.fst,
      cutoff < ∫ latent, latent ∂selectedNormalizedKernel κ event observed := by
    exact lg21_upperTail_selectedKernel_mean_gt_cutoff_ae
      (μ := μ) (κ := κ) cutoff hfibrePositive (by
        simpa [selectedLaw, event] using hintegrable)
  have hRCDMean :
      (fun observed => ∫ latent, latent ∂condDistrib Prod.snd Prod.fst selectedLaw observed) =ᵐ[
        selectedLaw.map Prod.fst]
      fun observed => ∫ latent, latent ∂selectedNormalizedKernel κ event observed :=
    selected_condDistrib_snd_mean_given_fst_ae
      (μ := μ) (κ := κ)
      (by simpa [event] using
        lg21UpperTailSelectionEvent_measurable (Observed := Observed) cutoff)
      hpositive hselection
  filter_upwards [hRCDMean, hkernelMean] with observed hMean hKernel
  rw [hMean]
  exact hKernel

/--
For an integrable latent coordinate, its conditional expectation given the
observed coordinate in the selected population is strictly above the cutoff
almost everywhere under the selected *joint* law.  This is the exact
measure-theoretic input a later source bridge would need before calling the
conditional expectation a PBO; it is not that bridge itself.
-/
theorem lg21_upperTail_selected_condExp_gt_cutoff_ae
    [MeasurableSpace Observed] {μ : Measure Observed} [IsProbabilityMeasure μ]
    {κ : Kernel Observed ℝ} [IsMarkovKernel κ]
    (cutoff : ℝ)
    (hfibrePositive : ∀ observed, κ observed (Set.Ioi cutoff) ≠ 0)
    (hselection :
      (μ ⊗ₘ κ) (lg21UpperTailSelectionEvent (Observed := Observed) cutoff) ≠ 0)
    (hintegrableSelected : Integrable Prod.snd
      (lg21NormalizedRestriction (μ ⊗ₘ κ)
        (lg21UpperTailSelectionEvent (Observed := Observed) cutoff)))
    (hintegrableFibres :
      ∀ᵐ observed ∂
        (lg21NormalizedRestriction (μ ⊗ₘ κ)
          (lg21UpperTailSelectionEvent (Observed := Observed) cutoff)).map Prod.fst,
        Integrable (fun latent : ℝ => latent)
          (selectedNormalizedKernel κ
            (lg21UpperTailSelectionEvent (Observed := Observed) cutoff) observed)) :
    letI : IsProbabilityMeasure
        (lg21NormalizedRestriction (μ ⊗ₘ κ)
          (lg21UpperTailSelectionEvent (Observed := Observed) cutoff)) :=
      lg21NormalizedRestriction_isProbability (μ ⊗ₘ κ)
        (lg21UpperTailSelectionEvent (Observed := Observed) cutoff) hselection
        (measure_ne_top _ _)
    letI : IsFiniteMeasure
        (lg21NormalizedRestriction (μ ⊗ₘ κ)
          (lg21UpperTailSelectionEvent (Observed := Observed) cutoff)) := ⟨by simp⟩
    ∀ᵐ pair ∂lg21NormalizedRestriction (μ ⊗ₘ κ)
      (lg21UpperTailSelectionEvent (Observed := Observed) cutoff),
      cutoff <
        (lg21NormalizedRestriction (μ ⊗ₘ κ)
          (lg21UpperTailSelectionEvent (Observed := Observed) cutoff))[Prod.snd |
            MeasurableSpace.comap Prod.fst inferInstance] pair := by
  let event : Set (Observed × ℝ) :=
    lg21UpperTailSelectionEvent (Observed := Observed) cutoff
  let selectedLaw : Measure (Observed × ℝ) :=
    lg21NormalizedRestriction (μ ⊗ₘ κ) event
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability (μ ⊗ₘ κ) event hselection
      (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  have hpositive : ∀ observed, selectionMass κ event observed ≠ 0 := by
    intro observed
    change selectionMass κ
      (lg21UpperTailSelectionEvent (Observed := Observed) cutoff) observed ≠ 0
    rw [lg21UpperTailSelectionEvent_selectionMass]
    exact hfibrePositive observed
  have hkernelMean : ∀ᵐ observed ∂selectedLaw.map Prod.fst,
      cutoff < ∫ latent, latent ∂selectedNormalizedKernel κ event observed := by
    exact lg21_upperTail_selectedKernel_mean_gt_cutoff_ae
      (μ := μ) (κ := κ) cutoff hfibrePositive (by
        simpa [selectedLaw, event] using hintegrableFibres)
  have hcondExp : selectedLaw[Prod.snd |
      MeasurableSpace.comap Prod.fst inferInstance] =ᵐ[selectedLaw]
      fun pair => ∫ latent, latent ∂selectedNormalizedKernel κ event pair.1 :=
    selected_condExp_snd_given_fst_ae
      (μ := μ) (κ := κ)
      (by simpa [event] using
        lg21UpperTailSelectionEvent_measurable (Observed := Observed) cutoff)
      hpositive hselection (by simpa [selectedLaw] using hintegrableSelected)
  have hkernelMeanPullback : ∀ᵐ pair ∂selectedLaw,
      cutoff < ∫ latent, latent ∂selectedNormalizedKernel κ event pair.1 :=
    ae_of_ae_map measurable_fst.aemeasurable hkernelMean
  filter_upwards [hcondExp, hkernelMeanPullback] with pair hPBO hMean
  rw [hPBO]
  exact hMean

end

end LG21TestOptionalPolicies
