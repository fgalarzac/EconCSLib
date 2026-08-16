import LG21TestOptionalPolicies.OptionalPositiveMassUnraveling
import LG21TestOptionalPolicies.SelectedConditionalRestriction
import Mathlib.Probability.Kernel.Condexp

/-!
# Global fibrewise positive-mass unraveling for optional reporting

The optional report decision is observed with the full public base profile.
This module proves the corresponding global closure without treating a
continuous base profile as an atom. The no-report PBO is a conditional mean
under the normalized full joint no-report law, conditional only on the base.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-- A fibrewise strictly increasing score payoff can equal a base-only value
only on a score graph. If every conditional score law has null singletons,
that graph has zero mass under the full base-score law. -/
theorem lg21_fibrewise_strictMono_graph_null
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (scoreKernel : Kernel Base ℝ) [IsMarkovKernel scoreKernel]
    (payoff : Base × ℝ -> ℝ) (outside : Base -> ℝ)
    (hpayoff : Measurable payoff) (houtside : Measurable outside)
    (hstrict : ∀ base, StrictMono (fun score => payoff (base, score)))
    (hsingleton : ∀ base score, scoreKernel base {score} = 0) :
    (baseLaw ⊗ₘ scoreKernel)
      {profile | payoff profile = outside profile.1} = 0 := by
  let level : Set (Base × ℝ) := {profile | payoff profile = outside profile.1}
  have hlevel : MeasurableSet level := by
    simpa [level] using measurableSet_eq_fun hpayoff
      (houtside.comp measurable_fst)
  have hfiberZero : ∀ base,
      scoreKernel base (Prod.mk base ⁻¹' level) = 0 := by
    intro base
    change scoreKernel base {score | payoff (base, score) = outside base} = 0
    let fibre : Set ℝ := {score | payoff (base, score) = outside base}
    have hfibreSubsingleton : fibre.Subsingleton := by
      intro left hleft right hright
      apply (hstrict base).injective
      change payoff (base, left) = payoff (base, right)
      exact hleft.trans hright.symm
    by_cases hempty : fibre = ∅
    · simp [fibre, hempty]
    · obtain ⟨score, hscore⟩ := Set.nonempty_iff_ne_empty.mpr hempty
      apply measure_mono_null
        (fun candidate hcandidate =>
          Set.mem_singleton_iff.mpr (hfibreSubsingleton hcandidate hscore))
      exact hsingleton base score
  rw [Measure.compProd_apply hlevel]
  have hzero : (fun base => scoreKernel base (Prod.mk base ⁻¹' level)) = 0 := by
    funext base
    exact hfiberZero base
  rw [hzero]
  exact lintegral_zero

/--
Two literal PBOs on one selected population have the same integral when each
is the conditional mean of the same latent skill under that population.  The
two public observations may be different.  In particular, this is *not* an
assumption that the report payoff is a conditional expectation under the
no-report observation; it is the tower identity applied separately to the
latent skill.
-/
theorem lg21_selected_skill_conditionalMean_integrals_eq
    {Omega ReportObservation NoReportObservation : Type*}
    [MeasurableSpace Omega] [MeasurableSpace ReportObservation]
    [MeasurableSpace NoReportObservation]
    (selectedLaw : Measure Omega) [IsFiniteMeasure selectedLaw]
    (skill : Omega -> ℝ)
    (reportObservation : Omega -> ReportObservation)
    (noReportObservation : Omega -> NoReportObservation)
    (reportValue noReportValue : Omega -> ℝ)
    (hreportObservation : Measurable reportObservation)
    (hnoReportObservation : Measurable noReportObservation)
    (hintegrable : Integrable skill selectedLaw)
    (hreportPBO : reportValue =ᵐ[selectedLaw]
      selectedLaw[skill |
        MeasurableSpace.comap reportObservation inferInstance])
    (hnoReportPBO : noReportValue =ᵐ[selectedLaw]
      selectedLaw[skill |
        MeasurableSpace.comap noReportObservation inferInstance]) :
    ∫ omega, reportValue omega ∂selectedLaw =
      ∫ omega, noReportValue omega ∂selectedLaw := by
  calc
    ∫ omega, reportValue omega ∂selectedLaw =
        ∫ omega, selectedLaw[skill |
          MeasurableSpace.comap reportObservation inferInstance] omega
          ∂selectedLaw := integral_congr_ae hreportPBO
    _ = ∫ omega, skill omega ∂selectedLaw := by
      simpa using (MeasureTheory.setIntegral_condExp
        (μ := selectedLaw) (f := skill) hreportObservation.comap_le
        hintegrable (s := Set.univ) MeasurableSet.univ)
    _ = ∫ omega, selectedLaw[skill |
          MeasurableSpace.comap noReportObservation inferInstance] omega
          ∂selectedLaw := by
      symm
      simpa using (MeasureTheory.setIntegral_condExp
        (μ := selectedLaw) (f := skill) hnoReportObservation.comap_le
        hintegrable (s := Set.univ) MeasurableSet.univ)
    _ = ∫ omega, noReportValue omega ∂selectedLaw :=
      integral_congr_ae hnoReportPBO.symm

/--
Global optional-report closure with literal selected PBOs.

The report and no-report payoffs are each calibrated as a conditional mean of
the same latent skill on the normalized literal no-report population.  This
is the source-derivable form: public-observation selection invariance can
transport a structural reported-score posterior to that population, while the
no-report PBO is calibrated directly there.  No conditional expectation of
one payoff given the other action's observation is assumed.
-/
theorem no_positive_mass_unchosen_of_fibrewise_selected_skill_means
    {Omega Base : Type*} [MeasurableSpace Omega] [MeasurableSpace Base]
    (sourceLaw : Measure Omega) [IsProbabilityMeasure sourceLaw]
    (unchosen : Set Omega)
    (base : Omega -> Base) (score skill : Omega -> ℝ)
    (reportValue : Base × ℝ -> ℝ) (noReportValue : Base -> ℝ)
    (hbase : Measurable base)
    (hbaseScore : Measurable (fun omega => (base omega, score omega)))
    (hbest : ∀ᵐ omega ∂sourceLaw.restrict unchosen,
      reportValue (base omega, score omega) ≤ noReportValue (base omega))
    (hintegrable : 0 < sourceLaw unchosen ->
      Integrable skill (lg21NormalizedRestriction sourceLaw unchosen))
    (hreportPBO : 0 < sourceLaw unchosen ->
      (fun omega => reportValue (base omega, score omega)) =ᵐ[
        lg21NormalizedRestriction sourceLaw unchosen]
        (lg21NormalizedRestriction sourceLaw unchosen)[skill |
          MeasurableSpace.comap (fun omega => (base omega, score omega))
            inferInstance])
    (hnoReportPBO : 0 < sourceLaw unchosen ->
      (fun omega => noReportValue (base omega)) =ᵐ[
        lg21NormalizedRestriction sourceLaw unchosen]
        (lg21NormalizedRestriction sourceLaw unchosen)[skill |
          MeasurableSpace.comap base inferInstance])
    (hlevelMeasurable : MeasurableSet {omega |
      reportValue (base omega, score omega) = noReportValue (base omega)})
    (hlevelNull : sourceLaw {omega |
      reportValue (base omega, score omega) = noReportValue (base omega)} = 0) :
    ¬ 0 < sourceLaw unchosen := by
  intro hpositive
  let selectedLaw : Measure Omega := lg21NormalizedRestriction sourceLaw unchosen
  letI : IsFiniteMeasure sourceLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure selectedLaw := by
    dsimp [selectedLaw]
    exact lg21NormalizedRestriction_isProbability sourceLaw unchosen
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  have hskillIntegrable : Integrable skill selectedLaw := by
    simpa [selectedLaw] using hintegrable hpositive
  have hreport : (fun omega => reportValue (base omega, score omega)) =ᵐ[selectedLaw]
      selectedLaw[skill |
        MeasurableSpace.comap (fun omega => (base omega, score omega))
          inferInstance] := by
    simpa [selectedLaw] using hreportPBO hpositive
  have hnoReport : (fun omega => noReportValue (base omega)) =ᵐ[selectedLaw]
      selectedLaw[skill | MeasurableSpace.comap base inferInstance] := by
    simpa [selectedLaw] using hnoReportPBO hpositive
  have hreportIntegrable : Integrable (fun omega =>
      reportValue (base omega, score omega)) selectedLaw := by
    exact MeasureTheory.integrable_condExp.congr hreport.symm
  have hnoReportIntegrable : Integrable (fun omega =>
      noReportValue (base omega)) selectedLaw := by
    exact MeasureTheory.integrable_condExp.congr hnoReport.symm
  have hbestSelected : ∀ᵐ omega ∂selectedLaw,
      reportValue (base omega, score omega) ≤ noReportValue (base omega) := by
    change ∀ᵐ omega ∂(sourceLaw unchosen)⁻¹ • sourceLaw.restrict unchosen,
      reportValue (base omega, score omega) ≤ noReportValue (base omega)
    exact Measure.ae_smul_measure hbest _
  have hintegral : ∫ omega, reportValue (base omega, score omega) ∂selectedLaw =
      ∫ omega, noReportValue (base omega) ∂selectedLaw := by
    exact lg21_selected_skill_conditionalMean_integrals_eq selectedLaw skill
      (fun omega => (base omega, score omega)) base
      (fun omega => reportValue (base omega, score omega))
      (fun omega => noReportValue (base omega)) hbaseScore hbase
      hskillIntegrable hreport hnoReport
  have hequal : (fun omega => reportValue (base omega, score omega)) =ᵐ[selectedLaw]
      fun omega => noReportValue (base omega) := by
    exact (integral_eq_iff_of_ae_le hreportIntegrable hnoReportIntegrable
      hbestSelected).mp hintegral
  let level : Set Omega := {omega |
    reportValue (base omega, score omega) = noReportValue (base omega)}
  have hlevelRaw : sourceLaw level = 0 := by
    simpa [level] using hlevelNull
  have hlevelSelected : selectedLaw level = 0 := by
    rw [show selectedLaw = lg21NormalizedRestriction sourceLaw unchosen by rfl,
      lg21NormalizedRestriction_apply sourceLaw (event := unchosen) (target := level)
        (by simpa [level] using hlevelMeasurable)]
    rw [measure_mono_null inter_subset_left hlevelRaw]
    simp
  have hlevelAE : ∀ᵐ omega ∂selectedLaw, omega ∈ level := by
    filter_upwards [hequal] with omega homega
    simpa [level] using homega
  rw [ae_iff] at hlevelAE
  have hselectedEmpty : selectedLaw Set.univ = 0 := by
    rw [← Set.union_compl_self level]
    apply measure_union_null hlevelSelected
    simpa only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] using hlevelAE
  have honeZero : (1 : ℝ≥0∞) = 0 := by
    simpa using hselectedEmpty
  exact one_ne_zero honeZero

/--
A positive optional no-report branch cannot be calibrated to its literal
base-conditional mean when reporting is fibrewise strictly increasing and
each source score fibre is atomless.

The PBO premise is stated on the normalized full joint no-report law. Thus it
is valid exactly on an attained positive branch, and does not assign a value
to an unused report history. The conclusion is global, so it does not assume
that any individual base profile has positive mass.
-/
theorem no_positive_mass_unchosen_of_fibrewise_literal_conditional_mean
    {Base : Type*} [MeasurableSpace Base]
    (baseLaw : Measure Base) [IsProbabilityMeasure baseLaw]
    (scoreKernel : Kernel Base ℝ) [IsMarkovKernel scoreKernel]
    (unchosen : Set (Base × ℝ))
    (payoff : Base × ℝ -> ℝ) (outside : Base -> ℝ)
    (hpayoff : Measurable payoff) (houtside : Measurable outside)
    (hstrict : ∀ base, StrictMono (fun score => payoff (base, score)))
    (hsingleton : ∀ base score, scoreKernel base {score} = 0)
    (hbest : ∀ᵐ profile ∂(baseLaw ⊗ₘ scoreKernel).restrict unchosen,
      payoff profile ≤ outside profile.1)
    (hintegrable : 0 < (baseLaw ⊗ₘ scoreKernel) unchosen ->
      Integrable payoff
        (lg21NormalizedRestriction (baseLaw ⊗ₘ scoreKernel) unchosen))
    (hcalibrated : 0 < (baseLaw ⊗ₘ scoreKernel) unchosen ->
      (fun profile : Base × ℝ => outside profile.1) =ᵐ[
        lg21NormalizedRestriction (baseLaw ⊗ₘ scoreKernel) unchosen]
        (lg21NormalizedRestriction (baseLaw ⊗ₘ scoreKernel) unchosen)[payoff |
          MeasurableSpace.comap Prod.fst inferInstance]) :
    ¬ 0 < (baseLaw ⊗ₘ scoreKernel) unchosen := by
  intro hpositive
  let rawLaw : Measure (Base × ℝ) := baseLaw ⊗ₘ scoreKernel
  let selectedLaw : Measure (Base × ℝ) :=
    lg21NormalizedRestriction rawLaw unchosen
  letI : IsProbabilityMeasure rawLaw := by
    dsimp [rawLaw]
    infer_instance
  letI : IsFiniteMeasure rawLaw := ⟨by simp⟩
  letI : IsProbabilityMeasure selectedLaw := by
    dsimp [selectedLaw]
    exact lg21NormalizedRestriction_isProbability rawLaw unchosen
      (ne_of_gt (by simpa [rawLaw] using hpositive)) (measure_ne_top _ _)
  letI : IsFiniteMeasure selectedLaw := ⟨by simp⟩
  have hpIntegrable : Integrable payoff selectedLaw := by
    simpa [selectedLaw, rawLaw] using hintegrable hpositive
  have hmean : (fun profile : Base × ℝ => outside profile.1) =ᵐ[selectedLaw]
      selectedLaw[payoff | MeasurableSpace.comap Prod.fst inferInstance] := by
    simpa [selectedLaw, rawLaw] using hcalibrated hpositive
  have houtsideIntegrable : Integrable (fun profile : Base × ℝ => outside profile.1)
      selectedLaw := by
    exact MeasureTheory.integrable_condExp.congr hmean.symm
  have hbestSelected : ∀ᵐ profile ∂selectedLaw,
      payoff profile ≤ outside profile.1 := by
    change ∀ᵐ profile ∂(rawLaw unchosen)⁻¹ • rawLaw.restrict unchosen,
      payoff profile ≤ outside profile.1
    exact Measure.ae_smul_measure (by simpa [rawLaw] using hbest) _
  have hintegral : ∫ profile, payoff profile ∂selectedLaw =
      ∫ profile, outside profile.1 ∂selectedLaw := by
    calc
      ∫ profile, payoff profile ∂selectedLaw =
          ∫ profile, selectedLaw[payoff |
            MeasurableSpace.comap Prod.fst inferInstance] profile ∂selectedLaw := by
            symm
            exact MeasureTheory.integral_condExp measurable_fst.comap_le
      _ = ∫ profile, outside profile.1 ∂selectedLaw := by
            exact integral_congr_ae hmean.symm
  have hpayoffEq : payoff =ᵐ[selectedLaw] fun profile => outside profile.1 := by
    exact (integral_eq_iff_of_ae_le hpIntegrable houtsideIntegrable
      hbestSelected).mp hintegral
  let level : Set (Base × ℝ) := {profile | payoff profile = outside profile.1}
  have hlevelRaw : rawLaw level = 0 := by
    simpa [rawLaw, level] using
      (lg21_fibrewise_strictMono_graph_null baseLaw scoreKernel payoff outside
        hpayoff houtside hstrict hsingleton)
  have hlevelMeasurable : MeasurableSet level := by
    simpa [level] using measurableSet_eq_fun hpayoff
      (houtside.comp measurable_fst)
  have hlevelSelected : selectedLaw level = 0 := by
    rw [show selectedLaw = lg21NormalizedRestriction rawLaw unchosen by rfl,
      lg21NormalizedRestriction_apply rawLaw (event := unchosen) (target := level)
        hlevelMeasurable]
    rw [measure_mono_null inter_subset_left hlevelRaw]
    simp
  have hlevelAE : ∀ᵐ profile ∂selectedLaw, profile ∈ level := by
    filter_upwards [hpayoffEq] with profile hEq
    simpa [level] using hEq
  rw [ae_iff] at hlevelAE
  have hselectedEmpty : selectedLaw Set.univ = 0 := by
    rw [← Set.union_compl_self level]
    apply measure_union_null hlevelSelected
    simpa only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] using hlevelAE
  have honeZero : (1 : ℝ≥0∞) = 0 := by
    simpa using hselectedEmpty
  exact one_ne_zero honeZero

end

end LG21TestOptionalPolicies
