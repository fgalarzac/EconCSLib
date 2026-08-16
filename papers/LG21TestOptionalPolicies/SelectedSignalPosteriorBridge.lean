import LG21TestOptionalPolicies.ReportRequiredPublicActionPBOBridge
import Mathlib.Probability.Kernel.Posterior

/-!
# Public selection and canonical signal posteriors

These lemmas factor a latent public selection followed by a signal kernel.
They avoid normalizing arbitrary pointwise conditional-distribution versions:
the selected posterior is Mathlib's canonical `signal†selectedLaw` kernel.
The final theorem is source-neutral; an LG21 source bridge need only establish
the literal raw `(score, skill)` factorization and tie `selected` to the
public taking rule.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

/-- Normalizing a measurable preimage before or after mapping is the same. -/
theorem lg21_normalizedRestriction_map_preimage
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    (law : Measure Alpha) (f : Alpha → Beta) (hf : Measurable f)
    (event : Set Beta) (hevent : MeasurableSet event) :
    (lg21NormalizedRestriction law (f ⁻¹' event)).map f =
      lg21NormalizedRestriction (law.map f) event := by
  unfold lg21NormalizedRestriction
  calc
    ((law (f ⁻¹' event))⁻¹ • law.restrict (f ⁻¹' event)).map f =
        (law (f ⁻¹' event))⁻¹ • (law.restrict (f ⁻¹' event)).map f := by
          rw [Measure.map_smul]
    _ = (law (f ⁻¹' event))⁻¹ • (law.map f).restrict event := by
          rw [← Measure.restrict_map hf hevent]
    _ = ((law.map f) event)⁻¹ • (law.map f).restrict event := by
          rw [Measure.map_apply hf hevent]

/--
Restricting a latent law to a selected first-coordinate event commutes with
forming its joint law with a Markov signal kernel.
-/
theorem lg21_normalizedRestriction_compProd_left
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    (latentLaw : Measure Alpha) [IsProbabilityMeasure latentLaw]
    (signal : Kernel Alpha Beta) [IsMarkovKernel signal]
    (selected : Set Alpha) (hselectedMeasurable : MeasurableSet selected) :
    lg21NormalizedRestriction (latentLaw ⊗ₘ signal) (selected ×ˢ Set.univ) =
      lg21NormalizedRestriction latentLaw selected ⊗ₘ signal := by
  have hmass : (latentLaw ⊗ₘ signal) (selected ×ˢ Set.univ) = latentLaw selected := by
    calc
      (latentLaw ⊗ₘ signal) (selected ×ˢ Set.univ) =
          ((latentLaw ⊗ₘ signal).map Prod.fst) selected := by
        rw [Measure.map_apply measurable_fst hselectedMeasurable]
        congr
        ext pair
        simp
      _ = latentLaw selected := by
        change (latentLaw ⊗ₘ signal).fst selected = latentLaw selected
        rw [Measure.fst_compProd]
  have hrestrict : (latentLaw.restrict selected) ⊗ₘ signal =
      (latentLaw ⊗ₘ signal).restrict (selected ×ˢ Set.univ) := by
    calc
      (latentLaw.restrict selected) ⊗ₘ signal =
          (latentLaw.withDensity (selected.indicator 1)) ⊗ₘ signal := by
            rw [withDensity_indicator_one hselectedMeasurable]
      _ = (latentLaw ⊗ₘ signal).withDensity
          (fun pair : Alpha × Beta => selected.indicator 1 pair.1) := by
            rw [compProd_withDensity_left
              (measurable_one.indicator hselectedMeasurable)]
      _ = (latentLaw ⊗ₘ signal).withDensity
          ((selected ×ˢ Set.univ).indicator 1) := by
            congr 2
            funext pair
            by_cases h : pair.1 ∈ selected <;> simp [Set.indicator, h]
      _ = (latentLaw ⊗ₘ signal).restrict (selected ×ˢ Set.univ) := by
            rw [withDensity_indicator_one
              (hselectedMeasurable.prod MeasurableSet.univ)]
  unfold lg21NormalizedRestriction
  rw [hmass, Measure.compProd_smul_left, hrestrict]

/--
After public latent selection, the score/skill joint law factors through the
canonical posterior of the signal kernel.  The posterior kernel exists as a
Markov kernel even on score values with zero selected probability.
-/
theorem lg21_normalizedRestriction_selectedSignalJoint_eq_posterior
    {Alpha : Type*} [MeasurableSpace Alpha] [StandardBorelSpace Alpha] [Nonempty Alpha]
    (latentLaw : Measure Alpha) [IsProbabilityMeasure latentLaw]
    (signal : Kernel Alpha ℝ) [IsFiniteKernel signal] [IsMarkovKernel signal]
    (selected : Set Alpha) (hselectedMeasurable : MeasurableSet selected)
    (hselectedPositive : 0 < latentLaw selected) :
    let selectedLaw := lg21NormalizedRestriction latentLaw selected
    letI : IsProbabilityMeasure selectedLaw :=
      lg21NormalizedRestriction_isProbability latentLaw selected
        (ne_of_gt hselectedPositive) (measure_ne_top _ _)
    letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
    let rawScoreSkillLaw := (latentLaw ⊗ₘ signal).map Prod.swap
    let publicEvent : Set (ℝ × Alpha) := {pair | pair.2 ∈ selected}
    lg21NormalizedRestriction rawScoreSkillLaw publicEvent =
      (signal ∘ₘ selectedLaw) ⊗ₘ (signal†selectedLaw) := by
  let selectedLaw : Measure Alpha := lg21NormalizedRestriction latentLaw selected
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability latentLaw selected
      (ne_of_gt hselectedPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  let rawScoreSkillLaw : Measure (ℝ × Alpha) := (latentLaw ⊗ₘ signal).map Prod.swap
  let publicEvent : Set (ℝ × Alpha) := {pair | pair.2 ∈ selected}
  change lg21NormalizedRestriction rawScoreSkillLaw publicEvent =
    (signal ∘ₘ selectedLaw) ⊗ₘ (signal†selectedLaw)
  have hpublicEvent : MeasurableSet publicEvent := by
    change MeasurableSet (Prod.snd ⁻¹' selected)
    exact hselectedMeasurable.preimage measurable_snd
  have hpreimage : Prod.swap ⁻¹' publicEvent = selected ×ˢ Set.univ := by
    ext pair
    simp [publicEvent]
  calc
    lg21NormalizedRestriction rawScoreSkillLaw publicEvent =
        (lg21NormalizedRestriction (latentLaw ⊗ₘ signal)
          (Prod.swap ⁻¹' publicEvent)).map Prod.swap := by
      symm
      exact lg21_normalizedRestriction_map_preimage
        (latentLaw ⊗ₘ signal) Prod.swap measurable_swap publicEvent hpublicEvent
    _ = (selectedLaw ⊗ₘ signal).map Prod.swap := by
      rw [hpreimage]
      congr 1
      exact lg21_normalizedRestriction_compProd_left latentLaw signal selected
        hselectedMeasurable
    _ = (signal ∘ₘ selectedLaw) ⊗ₘ (signal†selectedLaw) := by
      exact ProbabilityTheory.compProd_posterior_eq_map_swap.symm

/--
Transport the canonical selected-signal factorization through any literal raw
source law whose mapped `(score, skill)` law is supplied explicitly.  The
selection event is defined by the public taking rule itself.
-/
theorem lg21_publicAction_selectedSignalJoint_eq_posterior
    {Omega : Type*} [MeasurableSpace Omega]
    (rawLaw : Measure Omega) (score skill : Omega → ℝ)
    (hscore : Measurable score) (hskill : Measurable skill)
    (latentLaw : Measure ℝ) [IsProbabilityMeasure latentLaw]
    (signal : Kernel ℝ ℝ) [IsFiniteKernel signal] [IsMarkovKernel signal]
    (takeDecision : ℝ → Bool) (htakeDecision : Measurable takeDecision)
    (hrawJoint : rawLaw.map (fun omega => (score omega, skill omega)) =
      (latentLaw ⊗ₘ signal).map Prod.swap)
    (hselectedPositive :
      0 < latentLaw {latentSkill | takeDecision latentSkill = true}) :
    let selectedLaw := lg21NormalizedRestriction latentLaw
      {latentSkill | takeDecision latentSkill = true}
    letI : IsProbabilityMeasure selectedLaw :=
      lg21NormalizedRestriction_isProbability latentLaw
        {latentSkill | takeDecision latentSkill = true}
        (ne_of_gt hselectedPositive) (measure_ne_top _ _)
    letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
    let publicEvent := lg21ReportRequiredPublicReporterEvent takeDecision
    (lg21NormalizedRestriction rawLaw
      ((fun omega => (score omega, skill omega)) ⁻¹' publicEvent)).map
        (fun omega => (score omega, skill omega)) =
      (signal ∘ₘ selectedLaw) ⊗ₘ (signal†selectedLaw) := by
  let selected : Set ℝ := {latentSkill | takeDecision latentSkill = true}
  let selectedLaw : Measure ℝ := lg21NormalizedRestriction latentLaw selected
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability latentLaw selected
      (by simpa [selected] using ne_of_gt hselectedPositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  let scoreSkill : Omega → ℝ × ℝ := fun omega => (score omega, skill omega)
  let publicEvent : Set (ℝ × ℝ) :=
    lg21ReportRequiredPublicReporterEvent takeDecision
  have hscoreSkill : Measurable scoreSkill := hscore.prodMk hskill
  have hpublicEvent : MeasurableSet publicEvent := by
    simpa [publicEvent] using
      (lg21ReportRequiredPublicReporterEvent_measurable
        takeDecision htakeDecision)
  have hselectedMeasurable : MeasurableSet selected := by
    change MeasurableSet (takeDecision ⁻¹' ({true} : Set Bool))
    exact (measurableSet_singleton true).preimage htakeDecision
  change
    (lg21NormalizedRestriction rawLaw (scoreSkill ⁻¹' publicEvent)).map scoreSkill =
      (signal ∘ₘ selectedLaw) ⊗ₘ (signal†selectedLaw)
  calc
    (lg21NormalizedRestriction rawLaw (scoreSkill ⁻¹' publicEvent)).map scoreSkill =
        lg21NormalizedRestriction (rawLaw.map scoreSkill) publicEvent :=
      lg21_normalizedRestriction_map_preimage
        rawLaw scoreSkill hscoreSkill publicEvent hpublicEvent
    _ = lg21NormalizedRestriction ((latentLaw ⊗ₘ signal).map Prod.swap)
        publicEvent := by rw [hrawJoint]
    _ = (signal ∘ₘ selectedLaw) ⊗ₘ (signal†selectedLaw) := by
      simpa [selectedLaw, selected, publicEvent,
        lg21ReportRequiredPublicReporterEvent] using
        (lg21_normalizedRestriction_selectedSignalJoint_eq_posterior
          latentLaw signal selected hselectedMeasurable
          (by simpa [selected] using hselectedPositive))

end

end LG21TestOptionalPolicies
