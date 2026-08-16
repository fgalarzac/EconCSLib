import LG21TestOptionalPolicies.SelectedConditionalRestriction

/-!
# Base-mass promotion for observed-access optional reporting

These lemmas retain the full observed base profile when lifting a
score-selected optional-reporting event. They do not infer positive report
mass at every base from a global event, and they do not inspect a strategy's
implementation beyond its measurable public action event.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- The full public action event on which an observed-access student reports
their realized score. The latent coordinate is retained in the carrier but
does not determine this public action. -/
def lg21OptionalFullPublicReportSet
    {Base : Type*} (report : Base -> ℝ -> Bool) : Set (Base × (ℝ × ℝ)) :=
  {profile | report profile.1 profile.2.1 = true}

/-- The full public action event on which an observed-access student does not
report their realized score. -/
def lg21OptionalFullPublicNoReportSet
    {Base : Type*} (report : Base -> ℝ -> Bool) : Set (Base × (ℝ × ℝ)) :=
  {profile | report profile.1 profile.2.1 = false}

theorem lg21OptionalFullPublicReportSet_measurable
    {Base : Type*} [MeasurableSpace Base]
    (report : Base -> ℝ -> Bool)
    (hreport : Measurable (fun profile : Base × ℝ => report profile.1 profile.2)) :
    MeasurableSet (lg21OptionalFullPublicReportSet report) := by
  change MeasurableSet
    ((fun profile : Base × (ℝ × ℝ) => report profile.1 profile.2.1) ⁻¹'
      ({true} : Set Bool))
  exact (measurableSet_singleton true).preimage
    (hreport.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))

theorem lg21OptionalFullPublicNoReportSet_measurable
    {Base : Type*} [MeasurableSpace Base]
    (report : Base -> ℝ -> Bool)
    (hreport : Measurable (fun profile : Base × ℝ => report profile.1 profile.2)) :
    MeasurableSet (lg21OptionalFullPublicNoReportSet report) := by
  change MeasurableSet
    ((fun profile : Base × (ℝ × ℝ) => report profile.1 profile.2.1) ⁻¹'
      ({false} : Set Bool))
  exact (measurableSet_singleton false).preimage
    (hreport.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))

/-- A positive global no-report event has a positive-mass set of observed-base
fibres with positive no-report mass. -/
theorem lg21_optional_positive_noReport_mass_has_positive_baseFibres
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (scoreSkillKernel : Kernel Base (ℝ × ℝ)) [IsMarkovKernel scoreSkillKernel]
    (report : Base -> ℝ -> Bool)
    (hreport : Measurable (fun profile : Base × ℝ => report profile.1 profile.2))
    (hpositive : 0 < (baseLaw ⊗ₘ scoreSkillKernel)
      (lg21OptionalFullPublicNoReportSet report)) :
    0 < baseLaw (Function.support
      (selectionMass scoreSkillKernel (lg21OptionalFullPublicNoReportSet report))) := by
  let event : Set (Base × (ℝ × ℝ)) := lg21OptionalFullPublicNoReportSet report
  have hevent : MeasurableSet event := by
    simpa [event] using lg21OptionalFullPublicNoReportSet_measurable report hreport
  have hmassMeasurable : Measurable (selectionMass scoreSkillKernel event) :=
    selectionMass_measurable hevent
  change 0 < (baseLaw ⊗ₘ scoreSkillKernel) event at hpositive
  rw [Measure.compProd_apply hevent] at hpositive
  exact (lintegral_pos_iff_support hmassMeasurable).mp hpositive

/-- A positive global no-report event has positive base mass either where both
public actions occur, or where the report action has zero conditional mass.
The latter branch must be handled by a recalibrated positive-mass entry; an
on-path reporter PBO has no information there. -/
theorem lg21_optional_positive_noReport_mass_split_reporterFibres
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (scoreSkillKernel : Kernel Base (ℝ × ℝ)) [IsMarkovKernel scoreSkillKernel]
    (report : Base -> ℝ -> Bool)
    (hreport : Measurable (fun profile : Base × ℝ => report profile.1 profile.2))
    (hpositive : 0 < (baseLaw ⊗ₘ scoreSkillKernel)
      (lg21OptionalFullPublicNoReportSet report)) :
    (0 < baseLaw
      (Function.support
        (selectionMass scoreSkillKernel (lg21OptionalFullPublicNoReportSet report)) ∩
        Function.support
          (selectionMass scoreSkillKernel (lg21OptionalFullPublicReportSet report)))) ∨
      (0 < baseLaw
        (Function.support
          (selectionMass scoreSkillKernel (lg21OptionalFullPublicNoReportSet report)) ∩
        {base | selectionMass scoreSkillKernel
          (lg21OptionalFullPublicReportSet report) base = 0})) := by
  let noReportEvent : Set (Base × (ℝ × ℝ)) :=
    lg21OptionalFullPublicNoReportSet report
  let reportEvent : Set (Base × (ℝ × ℝ)) :=
    lg21OptionalFullPublicReportSet report
  let noReportMass : Base -> ℝ≥0∞ := selectionMass scoreSkillKernel noReportEvent
  let reportMass : Base -> ℝ≥0∞ := selectionMass scoreSkillKernel reportEvent
  have hnoReportPositive : 0 < baseLaw (Function.support noReportMass) := by
    simpa [noReportEvent, noReportMass] using
      (lg21_optional_positive_noReport_mass_has_positive_baseFibres
        baseLaw scoreSkillKernel report hreport hpositive)
  by_cases hcoexist : 0 < baseLaw
      (Function.support noReportMass ∩ Function.support reportMass)
  · exact Or.inl (by
      simpa [noReportEvent, reportEvent, noReportMass, reportMass] using hcoexist)
  · right
    apply pos_iff_ne_zero.mpr
    intro hzero
    have hcoexistZero : baseLaw
        (Function.support noReportMass ∩ Function.support reportMass) = 0 := by
      exact le_antisymm (not_lt.mp hcoexist) (zero_le _)
    have hpartition : Function.support noReportMass =
        (Function.support noReportMass ∩ Function.support reportMass) ∪
          (Function.support noReportMass ∩ {base | reportMass base = 0}) := by
      ext base
      simp only [Function.mem_support, Set.mem_union, Set.mem_inter_iff,
        Set.mem_setOf_eq]
      constructor
      · intro hnoReport
        by_cases hreportMass : reportMass base = 0
        · exact Or.inr ⟨hnoReport, hreportMass⟩
        · exact Or.inl ⟨hnoReport, hreportMass⟩
      · intro h
        exact h.elim (fun hleft => hleft.1) (fun hright => hright.1)
    have hnoReportZero : baseLaw (Function.support noReportMass) = 0 := by
      rw [hpartition]
      exact measure_union_null hcoexistZero hzero
    exact (ne_of_gt hnoReportPositive) hnoReportZero

end

end LG21TestOptionalPolicies
