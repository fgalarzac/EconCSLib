import LG21TestOptionalPolicies.OptionalFibrewisePositiveMassUnraveling
import LG21TestOptionalPolicies.PositiveMassDeviation
import LG21TestOptionalPolicies.SelectedObservationConditionalInvariance

/-!
# All-report positive-mass withdrawal diagnostics for LG21

This standalone module distinguishes the two timings hidden by an informal
"positive-mass deviation" check at an all-report profile.

* A post-score report withdrawal is selected by the public `(base, score)`
  record.  The original reported PBO remains a conditional mean after that
  public-observation selection.  If the new no-report branch is calibrated
  from the same selected population, its members cannot all weakly prefer
  withdrawal.
* A pre-score no-test withdrawal is selected using latent skill.  Its new
  no-take PBO is a conditional mean of latent skill, while the predecessor
  all-take payoff is a shrunken posterior expectation.  The averaging identity
  needed for the first conclusion is absent; bounded high-skill bands provide
  a formal diagnostic of that distinction.

Nothing here asserts that either class of candidate is a full equilibrium.
In particular, a source-faithful equilibrium refinement must separately state
how nonmembers and both candidate branches are checked.  This file only
records the semantic tests needed before an all-report witness can claim
stability against withdrawals.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory

/--
Post-score withdrawals from an all-report profile cannot be weakly preferred
by every member when all of the following are literal:

* the incumbent report and candidate no-report values are conditional means of
  the same latent skill on the selected population; and
* conditional score laws are atomless and the incumbent reported value is
  strictly increasing in score on every base fibre.

The `hreportedPBO` premise is not an arbitrary payoff identity.  For a
post-score withdrawal, it is obtained by transporting the on-path all-report
PBO through public-observation selection;
`SelectedObservationConditionalInvariance.lean` contains that transport
lemma.  It is kept explicit so this theorem cannot silently be applied to a
skill-selected pre-score withdrawal, where that identity is generally false.
-/
theorem lg21_allReport_postScoreWithdrawal_not_all_weakly_prefer
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (scoreKernel : Kernel Base ℝ) [IsMarkovKernel scoreKernel]
    (reportedValue : Base × ℝ -> ℝ) (noReportValue : Base -> ℝ)
    (hbase : Measurable base) (hscore : Measurable score)
    (hskill : Measurable skill)
    (hfactor : sourceLaw.map (fun omega => (base omega, score omega)) =
      baseLaw ⊗ₘ scoreKernel)
    (withdrawal : Set Omega)
    (hreportedValue : Measurable reportedValue)
    (hnoReportValue : Measurable noReportValue)
    (hstrict : ∀ publicBase,
      StrictMono (fun observedScore => reportedValue (publicBase, observedScore)))
    (hsingleton : ∀ publicBase observedScore,
      scoreKernel publicBase {observedScore} = 0)
    (hmemberWeakGain : ∀ᵐ omega ∂sourceLaw.restrict withdrawal,
      reportedValue (base omega, score omega) ≤ noReportValue (base omega))
    (hintegrable : 0 < sourceLaw withdrawal ->
      Integrable skill (lg21NormalizedRestriction sourceLaw withdrawal))
    (hreportedPBO : 0 < sourceLaw withdrawal ->
      (fun omega => reportedValue (base omega, score omega)) =ᵐ[
        lg21NormalizedRestriction sourceLaw withdrawal]
        (lg21NormalizedRestriction sourceLaw withdrawal)[skill |
          MeasurableSpace.comap (fun omega => (base omega, score omega))
            inferInstance])
    (hnoReportPBO : 0 < sourceLaw withdrawal ->
      (fun omega => noReportValue (base omega)) =ᵐ[
        lg21NormalizedRestriction sourceLaw withdrawal]
        (lg21NormalizedRestriction sourceLaw withdrawal)[skill |
          MeasurableSpace.comap base inferInstance]) :
    ¬ 0 < sourceLaw withdrawal := by
  apply no_positive_mass_unchosen_of_fibrewise_selected_skill_means
    sourceLaw withdrawal base score skill reportedValue noReportValue
    hbase (hbase.prodMk hscore) hmemberWeakGain hintegrable hreportedPBO
    hnoReportPBO
  · simpa using
      (measurableSet_eq_fun
        (hreportedValue.comp (hbase.prodMk hscore))
        (hnoReportValue.comp hbase))
  · let level : Set (Base × ℝ) :=
      {profile | reportedValue profile = noReportValue profile.1}
    have hlevel : MeasurableSet level := by
      simpa [level] using measurableSet_eq_fun hreportedValue
        (hnoReportValue.comp measurable_fst)
    have hproductNull : (baseLaw ⊗ₘ scoreKernel) level = 0 := by
      simpa [level] using
        (lg21_fibrewise_strictMono_graph_null baseLaw scoreKernel
          reportedValue noReportValue hreportedValue hnoReportValue hstrict hsingleton)
    have hpreimage :
        {omega | reportedValue (base omega, score omega) = noReportValue (base omega)} =
          (fun omega => (base omega, score omega)) ⁻¹' level := by
      rfl
    rw [hpreimage, ← Measure.map_apply (hbase.prodMk hscore) hlevel, hfactor]
    exact hproductNull

/--
Transport an on-path all-report PBO to a positive candidate branch chosen by
the same public `(base, score)` observation.  This is the concrete bridge
which supplies `hreportedPBO` in
`lg21_allReport_postScoreWithdrawal_not_all_weakly_prefer`; it fails for a
candidate selection that additionally depends on latent skill.
-/
theorem lg21_allReport_reportedPBO_on_publicScoreWithdrawal
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    [IsFiniteMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (reportedValue : Base × ℝ -> ℝ)
    (hbase : Measurable base) (hscore : Measurable score)
    (hskill : Measurable skill) (hreportedValue : Measurable reportedValue)
    (hrawIntegrable : Integrable skill sourceLaw)
    (hrawPBO : (fun omega => reportedValue (base omega, score omega)) =ᵐ[sourceLaw]
      sourceLaw[skill |
        MeasurableSpace.comap (fun omega => (base omega, score omega))
          inferInstance])
    (selected : Set (Base × ℝ)) (hselected : MeasurableSet selected)
    (hpositive : 0 < sourceLaw
      ((fun omega => (base omega, score omega)) ⁻¹' selected)) :
    let selectedLaw := lg21NormalizedRestriction sourceLaw
      ((fun omega => (base omega, score omega)) ⁻¹' selected)
    letI : IsProbabilityMeasure selectedLaw :=
      lg21NormalizedRestriction_isProbability sourceLaw _
        (ne_of_gt hpositive) (measure_ne_top _ _)
    letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
    (fun omega => reportedValue (base omega, score omega)) =ᵐ[selectedLaw]
      selectedLaw[skill |
        MeasurableSpace.comap (fun omega => (base omega, score omega))
          inferInstance] := by
  intro selectedLaw
  let observation : Omega -> Base × ℝ := fun omega => (base omega, score omega)
  have hobservation : Measurable observation := hbase.prodMk hscore
  letI : IsProbabilityMeasure selectedLaw :=
    lg21NormalizedRestriction_isProbability sourceLaw (observation ⁻¹' selected)
      (ne_of_gt (by simpa [observation] using hpositive)) (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  have hrawCondExp : sourceLaw[skill |
      MeasurableSpace.comap observation inferInstance] =ᵐ[sourceLaw]
      fun omega => ∫ latentSkill, latentSkill ∂
        condDistrib skill observation sourceLaw (observation omega) := by
    exact condExp_ae_eq_integral_condDistrib' hobservation hrawIntegrable
  have hrawPBO' : (fun omega => reportedValue (observation omega)) =ᵐ[sourceLaw]
      fun omega => ∫ latentSkill, latentSkill ∂
        condDistrib skill observation sourceLaw (observation omega) := by
    simpa [observation] using hrawPBO.trans hrawCondExp
  have hmeanMeasurable : Measurable (fun publicObservation : Base × ℝ =>
      ∫ latentSkill, latentSkill ∂
        condDistrib skill observation sourceLaw publicObservation) := by
    exact stronglyMeasurable_id.integral_kernel.measurable
  have hrawPBOOnObservation : ∀ᵐ publicObservation ∂sourceLaw.map observation,
      reportedValue publicObservation = ∫ latentSkill, latentSkill ∂
        condDistrib skill observation sourceLaw publicObservation := by
    rw [MeasureTheory.ae_map_iff hobservation.aemeasurable
      (measurableSet_eq_fun hreportedValue hmeanMeasurable)]
    exact hrawPBO'
  have hselectedPBO := lg21_selectedObservation_condDistribMean_eq_raw_ae
    sourceLaw observation skill reportedValue hobservation hskill
    hrawPBOOnObservation selected hselected
    (by simpa [observation] using hpositive)
  have hselectedPullback : ∀ᵐ omega ∂selectedLaw,
      reportedValue (observation omega) = ∫ latentSkill, latentSkill ∂
        condDistrib skill observation selectedLaw (observation omega) := by
    exact ae_of_ae_map hobservation.aemeasurable hselectedPBO
  have hselectedCondExp : selectedLaw[skill |
      MeasurableSpace.comap observation inferInstance] =ᵐ[selectedLaw]
      fun omega => ∫ latentSkill, latentSkill ∂
        condDistrib skill observation selectedLaw (observation omega) := by
    exact condExp_ae_eq_integral_condDistrib' hobservation
      (hrawIntegrable.restrict.smul_measure
        (ENNReal.inv_ne_top.mpr (ne_of_gt (by simpa [selectedLaw, observation]
          using hpositive))))
  filter_upwards [hselectedPullback, hselectedCondExp] with omega hpbo hmean
  rw [hpbo, hmean]

/--
Fully semantic post-score withdrawal closure for an on-path all-report PBO.
Unlike the lower-level theorem above, the incumbent selected-branch PBO is
derived here from the raw all-report PBO and the fact that the candidate event
is selected by the public record itself.  The only candidate-specific PBO
input left is the literal no-report conditional mean on its positive branch.
-/
theorem lg21_allReport_publicScoreWithdrawal_not_all_weakly_prefer
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    [IsFiniteMeasure sourceLaw]
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (scoreKernel : Kernel Base ℝ) [IsMarkovKernel scoreKernel]
    (reportedValue : Base × ℝ -> ℝ) (noReportValue : Base -> ℝ)
    (hbase : Measurable base) (hscore : Measurable score)
    (hskill : Measurable skill)
    (hfactor : sourceLaw.map (fun omega => (base omega, score omega)) =
      baseLaw ⊗ₘ scoreKernel)
    (hreportedValue : Measurable reportedValue)
    (hnoReportValue : Measurable noReportValue)
    (hstrict : ∀ publicBase,
      StrictMono (fun observedScore => reportedValue (publicBase, observedScore)))
    (hsingleton : ∀ publicBase observedScore,
      scoreKernel publicBase {observedScore} = 0)
    (hrawIntegrable : Integrable skill sourceLaw)
    (hrawPBO : (fun omega => reportedValue (base omega, score omega)) =ᵐ[sourceLaw]
      sourceLaw[skill |
        MeasurableSpace.comap (fun omega => (base omega, score omega))
          inferInstance])
    (selected : Set (Base × ℝ)) (hselected : MeasurableSet selected)
    (hpositive : 0 < sourceLaw
      ((fun omega => (base omega, score omega)) ⁻¹' selected))
    (hmemberWeakGain : ∀ᵐ omega ∂sourceLaw.restrict
      ((fun omega => (base omega, score omega)) ⁻¹' selected),
      reportedValue (base omega, score omega) ≤ noReportValue (base omega))
    (hselectedIntegrable : Integrable skill
      (lg21NormalizedRestriction sourceLaw
        ((fun omega => (base omega, score omega)) ⁻¹' selected)))
    (hnoReportPBO : (fun omega => noReportValue (base omega)) =ᵐ[
      lg21NormalizedRestriction sourceLaw
        ((fun omega => (base omega, score omega)) ⁻¹' selected)]
      (lg21NormalizedRestriction sourceLaw
        ((fun omega => (base omega, score omega)) ⁻¹' selected))[skill |
          MeasurableSpace.comap base inferInstance]) :
    False := by
  have hnot := lg21_allReport_postScoreWithdrawal_not_all_weakly_prefer
    sourceLaw base score skill baseLaw scoreKernel reportedValue noReportValue
    hbase hscore hskill hfactor
    ((fun omega => (base omega, score omega)) ⁻¹' selected)
    hreportedValue hnoReportValue hstrict hsingleton hmemberWeakGain
    (fun _ => hselectedIntegrable)
    (fun _ =>
      lg21_allReport_reportedPBO_on_publicScoreWithdrawal sourceLaw base score skill
        reportedValue hbase hscore hskill hreportedValue hrawIntegrable hrawPBO
        selected hselected hpositive)
    (fun _ => hnoReportPBO)
  exact hnot hpositive

/--
The contrasting pre-score diagnostic.  A bounded high-skill cohort can make
every one of its members strictly prefer the candidate no-take PBO to the
*predecessor* all-take expected payoff whenever that payoff has a genuine
Gaussian-posterior shrinkage factor.  This is deliberately not used to define
an equilibrium: it proves that member-only withdrawal stability is too weak
for pre-score deviations.
-/
theorem lg21_allReport_preScoreWithdrawal_highBand_predecessor_gain
    {Omega : Type*} [MeasurableSpace Omega]
    (sourceLaw : Measure Omega) [IsFiniteMeasure sourceLaw]
    (skill : Omega -> ℝ) (mean scale weight lower width : ℝ)
    (hskill : Measurable skill) (hscale : 0 < scale) (hweight : 0 < weight)
    (hband : weight * (lower + width) < lower)
    (hpositive : 0 < sourceLaw
      {omega | mean + lower * scale < skill omega ∧
        skill omega < mean + (lower + width) * scale})
    (hintegrable : Integrable skill (lg21NormalizedRestriction sourceLaw
      {omega | mean + lower * scale < skill omega ∧
        skill omega < mean + (lower + width) * scale})) :
    ∀ᵐ omega ∂lg21NormalizedRestriction sourceLaw
      {omega | mean + lower * scale < skill omega ∧
        skill omega < mean + (lower + width) * scale},
      mean + weight * (skill omega - mean) <
        ∫ candidate, skill candidate ∂lg21NormalizedRestriction sourceLaw
          {candidate | mean + lower * scale < skill candidate ∧
            skill candidate < mean + (lower + width) * scale} := by
  exact lg21_affine_high_band_strictly_benefits sourceLaw skill mean scale
    weight lower width hskill hscale hweight hband hpositive hintegrable

/-- A nonzero, nonunit posterior-shrinkage factor always has a high/narrow
band satisfying the preceding diagnostic's numerical condition. -/
theorem lg21_allReport_preScoreWithdrawal_highBand_parameters
    (weight : ℝ) (hweight : 0 < weight) (hweight_lt_one : weight < 1) :
    ∃ lower width : ℝ,
      0 < lower ∧ 0 < width ∧ weight * (lower + width) < lower :=
  lg21_affine_shrinkage_admits_high_band weight hweight hweight_lt_one

end

end LG21TestOptionalPolicies
