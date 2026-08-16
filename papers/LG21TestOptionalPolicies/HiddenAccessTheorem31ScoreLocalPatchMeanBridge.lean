import LG21TestOptionalPolicies.HiddenAccessTheorem31ScoreLocalPatchResponseBridge

/-!
# Score-local patch mean bridge for LG21 Theorem 3.1

The source-local patch promotes only the access component of a current
no-report score set.  The no-access component stays in the candidate's
`X = 0` population.  This file records the elementary mixture calculation
needed by that patch: deleting access mass whose displayed score value is
strictly above the incumbent mixture mean cannot increase the recalibrated
mixture mean.

The lemma is deliberately source-neutral.  Its caller must prove that the
displayed score value is the literal conditional skill mean on the relevant
public score law; this module does not infer that fact from an action name.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

/-- The access scores retained in the candidate's no-report branch after a
score-local promotion above the incumbent mixture mean. -/
def lg21ScoreLocalPatchRetained
    {Omega : Type*}
    (currentNoReport : Set Omega) (scoreValue : Omega -> ℝ) (incumbentMean : ℝ) :
    Set Omega :=
  currentNoReport ∩ {omega | scoreValue omega ≤ incumbentMean}

/-- The promoted access scores in a score-local patch. -/
def lg21ScoreLocalPatchPromoted
    {Omega : Type*}
    (currentNoReport : Set Omega) (scoreValue : Omega -> ℝ) (incumbentMean : ℝ) :
    Set Omega :=
  currentNoReport ∩ {omega | incumbentMean < scoreValue omega}

theorem lg21ScoreLocalPatch_current_eq_retained_union_promoted
    {Omega : Type*}
    (currentNoReport : Set Omega) (scoreValue : Omega -> ℝ) (incumbentMean : ℝ) :
    currentNoReport =
      lg21ScoreLocalPatchRetained currentNoReport scoreValue incumbentMean ∪
        lg21ScoreLocalPatchPromoted currentNoReport scoreValue incumbentMean := by
  ext omega
  simp only [lg21ScoreLocalPatchRetained, lg21ScoreLocalPatchPromoted,
    mem_inter_iff, mem_union, mem_setOf_eq]
  constructor
  · rintro hcurrent
    by_cases hle : scoreValue omega ≤ incumbentMean
    · exact Or.inl ⟨hcurrent, hle⟩
    · exact Or.inr ⟨hcurrent, lt_of_not_ge hle⟩
  · rintro (hretained | hpromoted)
    · exact hretained.1
    · exact hpromoted.1

theorem lg21ScoreLocalPatch_retained_disjoint_promoted
    {Omega : Type*}
    (currentNoReport : Set Omega) (scoreValue : Omega -> ℝ) (incumbentMean : ℝ) :
    Disjoint
      (lg21ScoreLocalPatchRetained currentNoReport scoreValue incumbentMean)
      (lg21ScoreLocalPatchPromoted currentNoReport scoreValue incumbentMean) := by
  apply Set.disjoint_left.2
  intro omega hretained hpromoted
  change omega ∈ currentNoReport ∩ {omega | scoreValue omega ≤ incumbentMean} at hretained
  change omega ∈ currentNoReport ∩ {omega | incumbentMean < scoreValue omega} at hpromoted
  have hretainedValue : scoreValue omega ≤ incumbentMean := by
    simpa using hretained.2
  have hpromotedValue : incumbentMean < scoreValue omega := by
    simpa using hpromoted.2
  exact (not_lt_of_ge hretainedValue) hpromotedValue

theorem lg21ScoreLocalPatchRetained_measurable
    {Omega : Type*} [MeasurableSpace Omega]
    (currentNoReport : Set Omega) (scoreValue : Omega -> ℝ) (incumbentMean : ℝ)
    (hcurrent : MeasurableSet currentNoReport) (hscoreValue : Measurable scoreValue) :
    MeasurableSet
      (lg21ScoreLocalPatchRetained currentNoReport scoreValue incumbentMean) := by
  exact hcurrent.inter (measurableSet_le hscoreValue measurable_const)

theorem lg21ScoreLocalPatchPromoted_measurable
    {Omega : Type*} [MeasurableSpace Omega]
    (currentNoReport : Set Omega) (scoreValue : Omega -> ℝ) (incumbentMean : ℝ)
    (hcurrent : MeasurableSet currentNoReport) (hscoreValue : Measurable scoreValue) :
    MeasurableSet
      (lg21ScoreLocalPatchPromoted currentNoReport scoreValue incumbentMean) := by
  exact hcurrent.inter (measurableSet_lt measurable_const hscoreValue)

/-- The public score-local promotion rule used by the hidden-access patch.
It compares only the public base, realized score, and incumbent base-only
value. -/
def lg21ScoreLocalPromotion
    {Base : Type*}
    (incumbentNoReport : Base -> ℝ) (scoreValue : Base -> ℝ -> ℝ) :
    Base -> ℝ -> Bool :=
  fun publicBase score => decide (incumbentNoReport publicBase < scoreValue publicBase score)

@[simp] theorem lg21ScoreLocalPromotion_eq_true_iff
    {Base : Type*}
    (incumbentNoReport : Base -> ℝ) (scoreValue : Base -> ℝ -> ℝ)
    (publicBase : Base) (score : ℝ) :
    lg21ScoreLocalPromotion incumbentNoReport scoreValue publicBase score = true ↔
      incumbentNoReport publicBase < scoreValue publicBase score := by
  simp [lg21ScoreLocalPromotion]

@[simp] theorem lg21ScoreLocalPromotion_eq_false_iff
    {Base : Type*}
    (incumbentNoReport : Base -> ℝ) (scoreValue : Base -> ℝ -> ℝ)
    (publicBase : Base) (score : ℝ) :
    lg21ScoreLocalPromotion incumbentNoReport scoreValue publicBase score = false ↔
      scoreValue publicBase score ≤ incumbentNoReport publicBase := by
  simp [lg21ScoreLocalPromotion, not_lt]

theorem lg21ScoreLocalPromotion_measurable
    {Base : Type*} [MeasurableSpace Base]
    (incumbentNoReport : Base -> ℝ) (scoreValue : Base -> ℝ -> ℝ)
    (hincumbent : Measurable incumbentNoReport)
    (hscoreValue : Measurable (fun pair : Base × ℝ => scoreValue pair.1 pair.2)) :
    Measurable (fun pair : Base × ℝ =>
      lg21ScoreLocalPromotion incumbentNoReport scoreValue pair.1 pair.2) := by
  apply measurable_to_bool
  have hset : MeasurableSet {pair : Base × ℝ |
      incumbentNoReport pair.1 < scoreValue pair.1 pair.2} := by
    exact measurableSet_lt (hincumbent.comp measurable_fst) hscoreValue
  convert hset using 1
  ext pair
  simp [lg21ScoreLocalPromotion]

/-- The score-local patch leaves an access student unreported exactly when
the predecessor leaves them unreported and their score value is no larger
than the incumbent base-only value. -/
theorem lg21HiddenAccessScoreLocalReportPatch_eq_false_iff
    {Base : Type*}
    (currentReport : Base -> ℝ -> Bool)
    (incumbentNoReport : Base -> ℝ) (scoreValue : Base -> ℝ -> ℝ)
    (publicBase : Base) (score : ℝ) :
    lg21HiddenAccessScoreLocalReportPatch currentReport
      (lg21ScoreLocalPromotion incumbentNoReport scoreValue)
      publicBase score = false ↔
      currentReport publicBase score = false ∧
        scoreValue publicBase score ≤ incumbentNoReport publicBase := by
  constructor
  · intro hpatch
    have hcurrent : currentReport publicBase score = false := by
      cases hdecision : currentReport publicBase score <;>
        simp [lg21HiddenAccessScoreLocalReportPatch, hdecision] at hpatch ⊢
    refine ⟨hcurrent, ?_⟩
    have hpromotion : lg21ScoreLocalPromotion incumbentNoReport scoreValue
        publicBase score = false := by
      cases hdecision : lg21ScoreLocalPromotion incumbentNoReport scoreValue
          publicBase score <;>
        simp [lg21HiddenAccessScoreLocalReportPatch, hcurrent, hdecision] at hpatch ⊢
    exact (lg21ScoreLocalPromotion_eq_false_iff
      incumbentNoReport scoreValue publicBase score).1 hpromotion
  · rintro ⟨hcurrent, hvalue⟩
    have hpromotion : lg21ScoreLocalPromotion incumbentNoReport scoreValue
        publicBase score = false :=
      (lg21ScoreLocalPromotion_eq_false_iff
        incumbentNoReport scoreValue publicBase score).2 hvalue
    simp [lg21HiddenAccessScoreLocalReportPatch, hcurrent, hpromotion]

/--
Removing the access component of scores strictly above an incumbent mixture
mean cannot raise the normalized mixture mean.

`noAccessWeight` multiplies the full score population, whereas
`accessWeight` multiplies only the current no-report score set.  This is the
literal hidden-access `X = 0` geometry: no-access students remain in the
branch even when some access students are promoted to reporting.
-/
theorem lg21_scoreLocalPatch_mixtureMean_le_incumbent
    {Omega : Type*} [MeasurableSpace Omega]
    (scoreLaw : Measure Omega) [IsProbabilityMeasure scoreLaw]
    (scoreValue : Omega -> ℝ) (hscoreValue : Measurable scoreValue)
    (hscoreIntegrable : Integrable scoreValue scoreLaw)
    (currentNoReport : Set Omega) (hcurrent : MeasurableSet currentNoReport)
    (noAccessWeight accessWeight incumbentMean : ℝ)
    (hnoAccess : 0 < noAccessWeight) (haccess : 0 ≤ accessWeight)
    (hincumbent :
      incumbentMean =
        (noAccessWeight * (∫ omega, scoreValue omega ∂scoreLaw) +
          accessWeight * (∫ omega in currentNoReport, scoreValue omega ∂scoreLaw)) /
          (noAccessWeight + accessWeight * (scoreLaw currentNoReport).toReal)) :
    let retained := lg21ScoreLocalPatchRetained
      currentNoReport scoreValue incumbentMean
    (noAccessWeight * (∫ omega, scoreValue omega ∂scoreLaw) +
      accessWeight * (∫ omega in retained, scoreValue omega ∂scoreLaw)) /
        (noAccessWeight + accessWeight * (scoreLaw retained).toReal) ≤
      incumbentMean := by
  intro retained
  let promoted := lg21ScoreLocalPatchPromoted
    currentNoReport scoreValue incumbentMean
  have hretained : MeasurableSet retained := by
    simpa [retained] using
      (lg21ScoreLocalPatchRetained_measurable currentNoReport scoreValue
        incumbentMean hcurrent hscoreValue)
  have hpromoted : MeasurableSet promoted := by
    simpa [promoted] using
      (lg21ScoreLocalPatchPromoted_measurable currentNoReport scoreValue
        incumbentMean hcurrent hscoreValue)
  have hpartition : currentNoReport = retained ∪ promoted := by
    simpa [retained, promoted] using
      (lg21ScoreLocalPatch_current_eq_retained_union_promoted
        currentNoReport scoreValue incumbentMean)
  have hdisjoint : Disjoint retained promoted := by
    simpa [retained, promoted] using
      (lg21ScoreLocalPatch_retained_disjoint_promoted
        currentNoReport scoreValue incumbentMean)
  have hvalueRetained : IntegrableOn scoreValue retained scoreLaw :=
    hscoreIntegrable.integrableOn
  have hvaluePromoted : IntegrableOn scoreValue promoted scoreLaw :=
    hscoreIntegrable.integrableOn
  have hvalueCurrent : IntegrableOn scoreValue currentNoReport scoreLaw :=
    hscoreIntegrable.integrableOn
  have hintegralSplit :
      (∫ omega in currentNoReport, scoreValue omega ∂scoreLaw) =
        (∫ omega in retained, scoreValue omega ∂scoreLaw) +
          (∫ omega in promoted, scoreValue omega ∂scoreLaw) := by
    rw [hpartition]
    exact setIntegral_union hdisjoint hpromoted hvalueRetained hvaluePromoted
  have hmeasureSplit :
      (scoreLaw currentNoReport).toReal =
        (scoreLaw retained).toReal + (scoreLaw promoted).toReal := by
    rw [hpartition, measure_union hdisjoint hpromoted]
    exact ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)
  have hpromotedMean :
      incumbentMean * (scoreLaw promoted).toReal ≤
        ∫ omega in promoted, scoreValue omega ∂scoreLaw := by
    simpa [mul_comm] using
      (setIntegral_ge_of_const_le_real hpromoted (measure_ne_top _ _)
        (fun omega homega => le_of_lt homega.2) hvaluePromoted)
  have hdenominatorPos :
      0 < noAccessWeight + accessWeight * (scoreLaw retained).toReal := by
    have hmeasureNonneg : 0 ≤ (scoreLaw retained).toReal := ENNReal.toReal_nonneg
    nlinarith
  have hdenominatorNe :
      noAccessWeight + accessWeight * (scoreLaw retained).toReal ≠ 0 :=
    ne_of_gt hdenominatorPos
  have hincumbentDenominator :
      noAccessWeight + accessWeight * (scoreLaw currentNoReport).toReal ≠ 0 := by
    have hmeasureNonneg : 0 ≤ (scoreLaw currentNoReport).toReal := ENNReal.toReal_nonneg
    nlinarith
  have hincumbentMul :
      incumbentMean *
        (noAccessWeight + accessWeight * (scoreLaw currentNoReport).toReal) =
        noAccessWeight * (∫ omega, scoreValue omega ∂scoreLaw) +
          accessWeight * (∫ omega in currentNoReport, scoreValue omega ∂scoreLaw) := by
    rw [hincumbent]
    exact div_mul_cancel₀ _ hincumbentDenominator
  have hremovalNonneg :
      accessWeight *
        ((∫ omega in promoted, scoreValue omega ∂scoreLaw) -
          incumbentMean * (scoreLaw promoted).toReal) ≥ 0 := by
    apply mul_nonneg haccess
    linarith
  have htargetRaw :
      noAccessWeight * (∫ omega, scoreValue omega ∂scoreLaw) +
          accessWeight * (∫ omega in retained, scoreValue omega ∂scoreLaw) ≤
        incumbentMean *
          (noAccessWeight + accessWeight * (scoreLaw retained).toReal) := by
    have hrelation :
        incumbentMean *
            (noAccessWeight + accessWeight * (scoreLaw retained).toReal) -
          (noAccessWeight * (∫ omega, scoreValue omega ∂scoreLaw) +
            accessWeight * (∫ omega in retained, scoreValue omega ∂scoreLaw)) =
          accessWeight *
            ((∫ omega in promoted, scoreValue omega ∂scoreLaw) -
              incumbentMean * (scoreLaw promoted).toReal) := by
      rw [hmeasureSplit, hintegralSplit] at hincumbentMul
      nlinarith [hincumbentMul]
    linarith
  apply (div_le_iff₀ hdenominatorPos).2
  exact htargetRaw

end

end LG21TestOptionalPolicies
