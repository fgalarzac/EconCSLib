import LG21TestOptionalPolicies.ObservedAccessSourceConditionalKernel
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Conditional-support facts for a threshold-selected LG21 population

This module supplies the first literal-measure step needed by the
report-required repair.  It does not assume a Gaussian conjugacy formula or a
pointwise posterior version.  Instead it conditions the raw population on the
threshold action event and proves that the resulting regular conditional skill
law is supported above that threshold almost everywhere in the selected score
marginal.

The theorem is deliberately generic.  A source-facing LG21 bridge must still
construct the raw Gaussian population, prove that taking is the threshold
selection event, establish positive/integrable branches, and connect this RCD
to the school PBO.  Those are not hidden in this support result.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory
open ProbabilityTheory
open Set

/-- The literal population law after selecting latent skills strictly above a cutoff. -/
def lg21ThresholdSelectedPopulationLaw
    {Ω : Type*} [MeasurableSpace Ω]
    (rawLaw : Measure Ω) (skill : Ω → ℝ) (cutoff : ℝ) : Measure Ω :=
  lg21NormalizedRestriction rawLaw {ω | cutoff < skill ω}

/-- The selected population is almost surely above its threshold. -/
theorem lg21ThresholdSelectedPopulationLaw_ae_above_cutoff
    {Ω : Type*} [MeasurableSpace Ω]
    (rawLaw : Measure Ω) (skill : Ω → ℝ) (cutoff : ℝ)
    (hskill : Measurable skill)
    (hfinite : rawLaw {ω | cutoff < skill ω} ≠ ⊤) :
    ∀ᵐ ω ∂lg21ThresholdSelectedPopulationLaw rawLaw skill cutoff,
      cutoff < skill ω := by
  unfold lg21ThresholdSelectedPopulationLaw lg21NormalizedRestriction
  refine (Measure.ae_ennreal_smul_measure_iff ?_).2 ?_
  · exact ENNReal.inv_ne_zero.mpr hfinite
  · refine (ae_restrict_iff' (hskill measurableSet_Ioi)).2 ?_
    exact ae_of_all _ fun ω hω => hω

/--
An RCD of the latent skill given the score preserves an a.e. support invariant
of the raw population.  The conclusion is intentionally only a.e. in the
score marginal, which is the scope supplied by `condDistrib`.
-/
theorem lg21_condDistrib_skill_ae_above_cutoff_of_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsFiniteMeasure law]
    (score skill : Ω → ℝ) (cutoff : ℝ)
    (hscore : Measurable score) (hskill : Measurable skill)
    (habove : ∀ᵐ ω ∂law, cutoff < skill ω) :
    ∀ᵐ observedScore ∂law.map score,
      ∀ᵐ latentSkill ∂condDistrib skill score law observedScore,
        cutoff < latentSkill := by
  have hpairMem :
      ∀ᵐ pair ∂law.map (fun ω => (score ω, skill ω)),
        pair.2 ∈ Set.Ioi cutoff := by
    rw [MeasureTheory.ae_map_iff (hscore.prodMk hskill).aemeasurable
      (measurable_snd measurableSet_Ioi)]
    simpa only [Set.mem_Ioi] using habove
  have hpair :
      ∀ᵐ pair ∂law.map (fun ω => (score ω, skill ω)), cutoff < pair.2 := by
    simpa only [Set.mem_Ioi] using hpairMem
  have hcomp :
      ∀ᵐ pair ∂(law.map score) ⊗ₘ condDistrib skill score law,
        cutoff < pair.2 := by
    rw [compProd_map_condDistrib hskill.aemeasurable]
    exact hpair
  simpa using (Measure.ae_ae_of_ae_compProd hcomp)

/-- An a.e. strict inequality integrates strictly under a probability law. -/
theorem lg21_integral_lt_integral_of_ae_lt_probability
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    {f g : Outcome → ℝ}
    (hf : Integrable f law) (hg : Integrable g law)
    (hlt : ∀ᵐ outcome ∂law, f outcome < g outcome) :
    (∫ outcome, f outcome ∂law) < ∫ outcome, g outcome ∂law := by
  have hdiff_int : Integrable (fun outcome => g outcome - f outcome) law :=
    hg.sub hf
  have hdiff_nonneg : 0 ≤ᵐ[law] fun outcome => g outcome - f outcome := by
    filter_upwards [hlt] with outcome hltOutcome
    exact sub_nonneg.mpr (le_of_lt hltOutcome)
  have hsupport_ae :
      ∀ᵐ outcome ∂law,
        outcome ∈ Function.support (fun outcome => g outcome - f outcome) := by
    filter_upwards [hlt] with outcome hltOutcome
    change g outcome - f outcome ≠ 0
    exact ne_of_gt (sub_pos.mpr hltOutcome)
  have hsupport_pos : 0 < law (Function.support fun outcome => g outcome - f outcome) := by
    apply (pos_iff_ne_zero).2
    intro hzero
    have hcompl : law (Function.support (fun outcome => g outcome - f outcome))ᶜ = 0 :=
      mem_ae_iff.mp hsupport_ae
    have huniv : law Set.univ = 0 := by
      rw [← Set.union_compl_self (Function.support fun outcome => g outcome - f outcome)]
      exact measure_union_null hzero hcompl
    rw [IsProbabilityMeasure.measure_univ] at huniv
    norm_num at huniv
  have hpos : 0 < ∫ outcome, g outcome - f outcome ∂law :=
    (integral_pos_iff_support_of_nonneg_ae hdiff_nonneg hdiff_int).2 hsupport_pos
  have hsub :
      (∫ outcome, g outcome - f outcome ∂law) =
        (∫ outcome, g outcome ∂law) - ∫ outcome, f outcome ∂law :=
    integral_sub hg hf
  linarith

/--
An integrable conditional skill law inherits a strict conditional-mean bound
from an a.e. strict support invariant.  This is stated for an actual RCD,
rather than for an arbitrary pointwise posterior version.
-/
theorem lg21_condDistrib_skill_mean_gt_cutoff_of_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (law : Measure Ω) [IsFiniteMeasure law]
    (score skill : Ω → ℝ) (cutoff : ℝ)
    (hscore : Measurable score) (hskill : Measurable skill)
    (habove : ∀ᵐ ω ∂law, cutoff < skill ω)
    (hintegrable :
      ∀ᵐ observedScore ∂law.map score,
        Integrable (fun latentSkill : ℝ => latentSkill)
          (condDistrib skill score law observedScore)) :
    ∀ᵐ observedScore ∂law.map score,
      cutoff < ∫ latentSkill,
        latentSkill ∂condDistrib skill score law observedScore := by
  letI : IsMarkovKernel (condDistrib skill score law) := inferInstance
  have hsupport :=
    lg21_condDistrib_skill_ae_above_cutoff_of_ae
      law score skill cutoff hscore hskill habove
  filter_upwards [hsupport, hintegrable] with observedScore hsupportAtScore hInt
  letI : IsProbabilityMeasure
      (condDistrib skill score law observedScore) :=
    IsMarkovKernel.isProbabilityMeasure observedScore
  have hstrict :=
    lg21_integral_lt_integral_of_ae_lt_probability
      (condDistrib skill score law observedScore)
      (f := fun _latentSkill : ℝ => cutoff)
      (g := fun latentSkill : ℝ => latentSkill)
      (integrable_const cutoff) hInt hsupportAtScore
  simpa using hstrict

/--
Combining literal threshold selection with the RCD support theorem.  This is
the valid a.e. replacement for asserting `E[q | score, q > cutoff] > cutoff`
at every individual score by an arbitrary conditional-version choice.
-/
theorem lg21_threshold_selected_condDistrib_skill_ae_above_cutoff
    {Ω : Type*} [MeasurableSpace Ω]
    (rawLaw : Measure Ω) [IsFiniteMeasure rawLaw]
    (score skill : Ω → ℝ) (cutoff : ℝ)
    (hscore : Measurable score) (hskill : Measurable skill)
    (hpositive : 0 < rawLaw {ω | cutoff < skill ω})
    (hfinite : rawLaw {ω | cutoff < skill ω} ≠ ⊤) :
    letI : IsProbabilityMeasure
        (lg21ThresholdSelectedPopulationLaw rawLaw skill cutoff) :=
      lg21NormalizedRestriction_isProbability rawLaw {ω | cutoff < skill ω}
        (ne_of_gt hpositive) hfinite
    letI : IsFiniteMeasure
        (lg21ThresholdSelectedPopulationLaw rawLaw skill cutoff) :=
      ⟨by simp⟩
    ∀ᵐ observedScore ∂
      (lg21ThresholdSelectedPopulationLaw rawLaw skill cutoff).map score,
      ∀ᵐ latentSkill ∂condDistrib skill score
        (lg21ThresholdSelectedPopulationLaw rawLaw skill cutoff) observedScore,
        cutoff < latentSkill := by
  letI : IsProbabilityMeasure
      (lg21ThresholdSelectedPopulationLaw rawLaw skill cutoff) :=
    lg21NormalizedRestriction_isProbability rawLaw {ω | cutoff < skill ω}
      (ne_of_gt hpositive) hfinite
  letI : IsFiniteMeasure
      (lg21ThresholdSelectedPopulationLaw rawLaw skill cutoff) :=
    ⟨by simp⟩
  apply lg21_condDistrib_skill_ae_above_cutoff_of_ae
    (lg21ThresholdSelectedPopulationLaw rawLaw skill cutoff) score skill cutoff hscore hskill
  simpa using
    (lg21ThresholdSelectedPopulationLaw_ae_above_cutoff
      rawLaw skill cutoff hskill hfinite)

end

end LG21TestOptionalPolicies
