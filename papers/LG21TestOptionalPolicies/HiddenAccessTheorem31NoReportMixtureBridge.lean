import LG21TestOptionalPolicies.HiddenAccessTheorem31ActualActionBridge
import LG21TestOptionalPolicies.NestedCondDistribChain

/-!
# Actual hidden-access no-report mixture for LG21 Theorem 3.1

This module continues the literal Section 3 action bridge.  Once all taking
has been derived behaviorally, it turns the actual `X = 0` source population
into a normalized mixture of the two source action components:

* students without access; and
* access students whose actual post-score action withholds the score.

The mixture is first an exact measure identity on `(base, skill)`.  Its
base-conditioned form is then the regular conditional law obtained by first
weighting the literal access coordinate under that same normalized `X = 0`
law, and then conditioning skill on `(base, access)`.  The access coordinate
is used internally to expose the mixture weights; it is not placed in the
school's public information set.

No cutoff, posterior formula, or equilibrium replacement is assumed here.
-/

namespace LG21TestOptionalPolicies

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

/-! ## Literal component measures -/

/-- The `(base, skill)` observation used for the hidden-access no-report PBO. -/
def lg21HiddenAccessBaseSkillObservation
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) (student : Bool × (ℝ × (Feature → ℝ))) :
    (LG21NonTestFeature Feature testFeature → ℝ) × ℝ :=
  (lg21HiddenAccessStudentBase testFeature student.2,
    lg21ContinuousPopulationSkill student)

theorem lg21HiddenAccessBaseSkillObservation_measurable
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (testFeature : Feature) :
    Measurable (lg21HiddenAccessBaseSkillObservation (Feature := Feature) testFeature) := by
  exact
    ((lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd).prodMk
      (measurable_fst.comp measurable_snd)

/-- The actual normalized `(base, skill)` law on students with `X = 0`. -/
def lg21HiddenAccessOptionalNoReportBaseSkillLaw
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool) :
    Measure ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) :=
  (lg21HiddenAccessOptionalNoReportLaw M testFeature takeDecision reportDecision).map
    (lg21HiddenAccessBaseSkillObservation testFeature)

/-- The unnormalized no-access `(base, skill)` component of the `X = 0` law. -/
def lg21HiddenAccessNoAccessBaseSkillMeasure
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature) :
    Measure ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) :=
  ((lg21ContinuousGaussianPopulationLaw M).restrict
    (lg21HiddenAccessNoAccessEvent (Feature := Feature))).map
      (lg21HiddenAccessBaseSkillObservation testFeature)

/--
The unnormalized access-and-withhold `(base, skill)` component of the actual
`X = 0` law.  The event is stated through the source access coordinate and
the literal post-score action, rather than by an externally supplied cohort.
-/
def lg21HiddenAccessAccessNoReportBaseSkillMeasure
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool) :
    Measure ((LG21NonTestFeature Feature testFeature → ℝ) × ℝ) :=
  ((lg21ContinuousGaussianPopulationLaw M).restrict
    (lg21HiddenAccessAccessNoReportEvent testFeature reportDecision)).map
      (lg21HiddenAccessBaseSkillObservation testFeature)

/--
Exact normalized-mixture identity for the actual `X = 0` `(base, skill)`
law.  Its normalizing weight and both components are calculated from the same
literal source population and source-timed action event.
-/
theorem lg21HiddenAccessOptional_noReportBaseSkillLaw_eq_normalized_components
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (hallTake : ∀ student,
      lg21HiddenAccessStudentTake testFeature takeDecision student = true)
    (hreportDecision : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      reportDecision pair.1 pair.2)) :
    lg21HiddenAccessOptionalNoReportBaseSkillLaw M testFeature
        takeDecision reportDecision =
      (lg21ContinuousGaussianPopulationLaw M
        (lg21HiddenAccessOptionalNoReportEvent testFeature takeDecision reportDecision))⁻¹ •
        (lg21HiddenAccessNoAccessBaseSkillMeasure M testFeature +
          lg21HiddenAccessAccessNoReportBaseSkillMeasure M testFeature reportDecision) := by
  let law := lg21ContinuousGaussianPopulationLaw M
  let noReport :=
    lg21HiddenAccessOptionalNoReportEvent testFeature takeDecision reportDecision
  let noAccess := lg21HiddenAccessNoAccessEvent (Feature := Feature)
  let accessNoReport :=
    lg21HiddenAccessAccessNoReportEvent testFeature reportDecision
  let observation := lg21HiddenAccessBaseSkillObservation testFeature
  have hdisjoint : Disjoint noAccess accessNoReport := by
    apply Set.disjoint_left.2
    rintro ⟨access, primitive⟩ hfalse htrue
    change access = false at hfalse
    change access = true ∧ _ at htrue
    simp_all
  have haccessNoReportMeasurable : MeasurableSet accessNoReport := by
    change MeasurableSet
      (lg21HiddenAccessAccessNoReportEvent testFeature reportDecision)
    rw [lg21HiddenAccessAccessNoReportEvent_eq_true_rectangle]
    exact (measurableSet_singleton true).prod
      (lg21HiddenAccessStudentNoReportEvent_measurable testFeature reportDecision
        hreportDecision)
  have hevent : noReport = noAccess ∪ accessNoReport := by
    simpa [noReport, noAccess, accessNoReport] using
      (lg21HiddenAccessOptionalNoReportEvent_eq_noAccess_union_accessNoReport
        testFeature takeDecision reportDecision hallTake)
  have hcomponents : law.restrict noReport =
      law.restrict noAccess + law.restrict accessNoReport := by
    rw [hevent]
    exact Measure.restrict_union hdisjoint haccessNoReportMeasurable
  change Measure.map observation
      (lg21NormalizedRestriction law noReport) =
    (law noReport)⁻¹ •
      (Measure.map observation (law.restrict noAccess) +
        Measure.map observation (law.restrict accessNoReport))
  unfold lg21NormalizedRestriction
  rw [Measure.map_smul, hcomponents, Measure.map_add]
  exact lg21HiddenAccessBaseSkillObservation_measurable testFeature

/--
The actual normalized `X = 0` population is supported on exactly the two
source action components after all taking.  This is an a.e. statement because
the population itself has been normalized from an action event.
-/
theorem lg21HiddenAccessOptional_noReportLaw_ae_source_components
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (htakeDecision : Measurable (fun pair : ℝ ×
      (LG21NonTestFeature Feature testFeature → ℝ) =>
      takeDecision pair.1 pair.2))
    (hreportDecision : Measurable (fun pair :
      (LG21NonTestFeature Feature testFeature → ℝ) × ℝ =>
      reportDecision pair.1 pair.2))
    (hallTake : ∀ student,
      lg21HiddenAccessStudentTake testFeature takeDecision student = true)
    (hpositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalNoReportEvent testFeature takeDecision reportDecision)) :
    ∀ᵐ student ∂lg21HiddenAccessOptionalNoReportLaw M testFeature
      takeDecision reportDecision,
      student ∈ lg21HiddenAccessNoAccessEvent ∪
        lg21HiddenAccessAccessNoReportEvent testFeature reportDecision := by
  let law := lg21ContinuousGaussianPopulationLaw M
  let noReport :=
    lg21HiddenAccessOptionalNoReportEvent testFeature takeDecision reportDecision
  letI : IsProbabilityMeasure law :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure law := ⟨by simp⟩
  have hnoReportMeasurable : MeasurableSet noReport := by
    exact lg21HiddenAccessOptionalNoReportEvent_measurable testFeature
      takeDecision reportDecision htakeDecision hreportDecision
  change ∀ᵐ student ∂lg21NormalizedRestriction law noReport,
    student ∈ lg21HiddenAccessNoAccessEvent ∪
      lg21HiddenAccessAccessNoReportEvent testFeature reportDecision
  unfold lg21NormalizedRestriction
  refine (Measure.ae_ennreal_smul_measure_iff ?_).2 ?_
  · exact ENNReal.inv_ne_zero.mpr (measure_ne_top law noReport)
  · refine (ae_restrict_iff' hnoReportMeasurable).2 ?_
    exact ae_of_all _ fun student hstudent => by
      have hevent : noReport =
          lg21HiddenAccessNoAccessEvent ∪
            lg21HiddenAccessAccessNoReportEvent testFeature reportDecision := by
        simpa [noReport] using
          (lg21HiddenAccessOptionalNoReportEvent_eq_noAccess_union_accessNoReport
            testFeature takeDecision reportDecision hallTake)
      rw [hevent] at hstudent
      exact hstudent

/-! ## Base-conditioned mixture kernel -/

/--
For the actual normalized `X = 0` population, the conditional skill law given
the public base profile is a literal mixture: first draw the unobserved source
access coordinate from its conditional law given that base and `X = 0`, then
draw skill conditional on that same `(base, access)` pair.  The school does
not observe the access coordinate; it is integrated out by the kernel map.

The equality is only almost everywhere in the actual `X = 0` base marginal.
-/
theorem lg21HiddenAccessOptional_noReport_condDistrib_skill_base_mixture_ae
    {Feature : Type*} [Fintype Feature] [DecidableEq Feature]
    (M : LG21ContinuousGaussianPopulation Feature) (testFeature : Feature)
    (takeDecision : ℝ → (LG21NonTestFeature Feature testFeature → ℝ) → Bool)
    (reportDecision : (LG21NonTestFeature Feature testFeature → ℝ) → ℝ → Bool)
    (hpositive : 0 < lg21ContinuousGaussianPopulationLaw M
      (lg21HiddenAccessOptionalNoReportEvent testFeature takeDecision reportDecision)) :
    let law := lg21HiddenAccessOptionalNoReportLaw M testFeature
      takeDecision reportDecision
    let base : Bool × (ℝ × (Feature → ℝ)) →
        (LG21NonTestFeature Feature testFeature → ℝ) :=
      fun student => lg21HiddenAccessStudentBase testFeature student.2
    let access : Bool × (ℝ × (Feature → ℝ)) → Bool :=
      lg21ContinuousPopulationAccess
    let skill : Bool × (ℝ × (Feature → ℝ)) → ℝ :=
      lg21ContinuousPopulationSkill
    letI : IsProbabilityMeasure law :=
      lg21NormalizedRestriction_isProbability
        (lg21ContinuousGaussianPopulationLaw M)
        (lg21HiddenAccessOptionalNoReportEvent testFeature takeDecision reportDecision)
        (ne_of_gt hpositive) (by
          letI : IsProbabilityMeasure (lg21ContinuousGaussianPopulationLaw M) :=
            lg21ContinuousGaussianPopulationLaw_isProbability M
          letI : IsFiniteMeasure (lg21ContinuousGaussianPopulationLaw M) := ⟨by simp⟩
          exact measure_ne_top _ _)
    letI : IsFiniteMeasure law := ⟨by simp⟩
    condDistrib skill base law =ᵐ[law.map base]
      (condDistrib access base law ⊗ₖ
        condDistrib skill (fun student => (base student, access student)) law).map Prod.snd := by
  intro law base access skill
  letI : IsProbabilityMeasure (lg21ContinuousGaussianPopulationLaw M) :=
    lg21ContinuousGaussianPopulationLaw_isProbability M
  letI : IsFiniteMeasure (lg21ContinuousGaussianPopulationLaw M) := ⟨by simp⟩
  letI : IsProbabilityMeasure law :=
    lg21NormalizedRestriction_isProbability
      (lg21ContinuousGaussianPopulationLaw M)
      (lg21HiddenAccessOptionalNoReportEvent testFeature takeDecision reportDecision)
      (ne_of_gt hpositive) (measure_ne_top _ _)
  letI : IsFiniteMeasure law := ⟨by simp⟩
  have hbase : Measurable base := by
    exact (lg21HiddenAccessStudentBase_measurable testFeature).comp measurable_snd
  have haccess : Measurable access := by
    exact measurable_fst
  have hskill : Measurable skill := by
    exact measurable_fst.comp measurable_snd
  let accessSkill : Bool × (ℝ × (Feature → ℝ)) → Bool × ℝ :=
    fun student => (access student, skill student)
  have haccessSkill : Measurable accessSkill := haccess.prodMk hskill
  have hchain :
      condDistrib accessSkill base law =ᵐ[law.map base]
        condDistrib access base law ⊗ₖ
          condDistrib skill (fun student => (base student, access student)) law := by
    simpa [accessSkill] using
      (condDistrib_score_skill_chain_ae law base access skill hbase haccess hskill)
  have hmap :
      condDistrib (Prod.snd ∘ accessSkill) base law =ᵐ[law.map base]
        (condDistrib accessSkill base law).map Prod.snd := by
    exact condDistrib_comp base haccessSkill.aemeasurable measurable_snd
  filter_upwards [hmap, hchain] with observedBase hmapAt hchainAt
  change condDistrib skill base law observedBase =
    ((condDistrib access base law ⊗ₖ
      condDistrib skill (fun student => (base student, access student)) law).map Prod.snd)
        observedBase
  calc
    condDistrib skill base law observedBase =
        condDistrib (Prod.snd ∘ accessSkill) base law observedBase := by
          rfl
    _ = (condDistrib accessSkill base law).map Prod.snd observedBase := hmapAt
    _ = Measure.map Prod.snd (condDistrib accessSkill base law observedBase) := by
          rw [Kernel.map_apply _ measurable_snd]
    _ = Measure.map Prod.snd
        ((condDistrib access base law ⊗ₖ
          condDistrib skill (fun student => (base student, access student)) law)
            observedBase) := by rw [hchainAt]
    _ = ((condDistrib access base law ⊗ₖ
      condDistrib skill (fun student => (base student, access student)) law).map Prod.snd)
        observedBase := by
          rw [Kernel.map_apply _ measurable_snd]

end

end LG21TestOptionalPolicies
